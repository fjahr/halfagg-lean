import Halfagg.Proofs.BadBound

/-!
# A computation that returns its own random-oracle transcript

`withLog oa` runs `oa` and also returns the list of its hash queries with their
answers. It behaves like `oa` (`withLog_fst`) and makes the same hash queries
(`withLog_bound`). Run against a fixed table, every recorded answer is the
table's (`withLog_fixed`). Run against a lazily sampled oracle, the final cache
is the lookup function of the transcript (`withLog_lazy`).
-/

set_option linter.unusedSectionVars false

open OracleSpec OracleComp
open scoped ENNReal

namespace Halfagg.LoggedRun

variable {D Rng α : Type}

/-- A transcript: hash queries with their answers. -/
abbrev Tr (D Rng : Type) := List (D × Rng)

/-- The answer recorded for a key, if any. -/
def lk [DecidableEq D] (l : Tr D Rng) (t : D) : Option Rng := (l.find? fun e => e.1 = t).map (·.2)

/-- Pass every query on and record hash queries with their answers. -/
def logImpl : QueryImpl (unifSpec + (D →ₒ Rng))
    (StateT (Tr D Rng) (OracleComp (unifSpec + (D →ₒ Rng))))
  | .inl k => liftM ((unifSpec + (D →ₒ Rng)).query (.inl k))
  | .inr d => fun l => do
      let u ← (liftM ((unifSpec + (D →ₒ Rng)).query (.inr d)) :
        OracleComp (unifSpec + (D →ₒ Rng)) Rng)
      pure (u, l ++ [(d, u)])

/-- `oa`, returning also its transcript appended to `l`. -/
def withLogFrom (oa : OracleComp (unifSpec + (D →ₒ Rng)) α) (l : Tr D Rng) :
    OracleComp (unifSpec + (D →ₒ Rng)) (α × Tr D Rng) :=
  (simulateQ logImpl oa).run l

/-- `oa`, returning also its transcript. -/
def withLog (oa : OracleComp (unifSpec + (D →ₒ Rng)) α) :
    OracleComp (unifSpec + (D →ₒ Rng)) (α × Tr D Rng) := withLogFrom oa []

theorem withLogFrom_pure (a : α) (l : Tr D Rng) :
    withLogFrom (pure a : OracleComp (unifSpec + (D →ₒ Rng)) α) l = pure (a, l) := by
  simp [withLogFrom]

theorem withLogFrom_unif (k : ℕ) (next : Fin (k + 1) → OracleComp (unifSpec + (D →ₒ Rng)) α)
    (l : Tr D Rng) :
    withLogFrom (liftM ((unifSpec + (D →ₒ Rng)).query (.inl k)) >>= next) l =
      (liftM ((unifSpec + (D →ₒ Rng)).query (.inl k)) >>= fun u => withLogFrom (next u) l) := by
  simp only [withLogFrom, simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
  rfl

theorem withLogFrom_hash (d : D) (next : Rng → OracleComp (unifSpec + (D →ₒ Rng)) α)
    (l : Tr D Rng) :
    withLogFrom (liftM ((unifSpec + (D →ₒ Rng)).query (.inr d)) >>= next) l =
      (liftM ((unifSpec + (D →ₒ Rng)).query (.inr d)) >>= fun u =>
        withLogFrom (next u) (l ++ [(d, u)])) := by
  simp only [withLogFrom, simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
  simp [logImpl, StateT.run]

/-- Recording the transcript does not change the computation. -/
theorem withLogFrom_fst (oa : OracleComp (unifSpec + (D →ₒ Rng)) α) (l : Tr D Rng) :
    Prod.fst <$> withLogFrom oa l = oa := by
  induction oa using OracleComp.inductionOn generalizing l with
  | pure a => simp [withLogFrom_pure]
  | query_bind t next ih =>
    rcases t with k | d
    · rw [withLogFrom_unif, map_bind]
      exact bind_congr fun u => ih u l
    · rw [withLogFrom_hash, map_bind]
      exact bind_congr fun u => ih u _

theorem withLog_fst (oa : OracleComp (unifSpec + (D →ₒ Rng)) α) :
    Prod.fst <$> withLog oa = oa := withLogFrom_fst oa []

/-- Recording the transcript makes the same hash queries. -/
theorem withLogFrom_bound (oa : OracleComp (unifSpec + (D →ₒ Rng)) α) (Q : ℕ)
    (h : oa.IsQueryBoundP isHash Q) (l : Tr D Rng) :
    (withLogFrom oa l).IsQueryBoundP isHash Q := by
  induction oa using OracleComp.inductionOn generalizing Q l with
  | pure a => rw [withLogFrom_pure]; exact isQueryBoundP_pure _ _ _
  | query_bind t next ih =>
    rw [isQueryBoundP_query_bind_iff] at h
    rcases t with k | d
    · rw [withLogFrom_unif, isQueryBoundP_query_bind_iff]
      exact ⟨h.1, fun u => ih u _ (h.2 u) l⟩
    · rw [withLogFrom_hash, isQueryBoundP_query_bind_iff]
      exact ⟨h.1, fun u => ih u _ (h.2 u) _⟩

/-- Against a fixed table, every newly recorded answer is the table's, and its
key is in the oracle's log. -/
theorem withLogFrom_fixed [DecidableEq D] (oa : OracleComp (unifSpec + (D →ₒ Rng)) α)
    (g : D → Rng) (l : Tr D Rng) (c : (D →ₒ Rng).QueryCache) (hc : Agree c g) :
    ∀ z ∈ support (fixedTableLoggedRun (withLogFrom oa l) g c),
      ∀ e ∈ z.1.1.2, e ∈ l ∨ (e.2 = g e.1 ∧ e.1 ∈ freshKeysOfLog z.1.2) := by
  induction oa using OracleComp.inductionOn generalizing l c with
  | pure a =>
    intro z hz e he
    rw [withLogFrom_pure] at hz
    simp only [fixedTableLoggedRun, QueryImpl.passthrough_add, simulateQ_pure, WriterT.run_pure,
      List.empty_eq, StateT.run_pure, MonadAttach.support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact Or.inl he
  | query_bind t next ih =>
    intro z hz e he
    rcases t with k | d
    · rw [withLogFrom_unif, fixedTableLoggedRun_bind, mem_support_bind_iff] at hz
      obtain ⟨p, hp, hz⟩ := hz
      rw [support_map] at hz
      obtain ⟨q, hq, rfl⟩ := hz
      rw [fixedTableLoggedRun_uniformQuery, support_map] at hp
      obtain ⟨u, -, rfl⟩ := hp
      rcases ih u l c hc q hq e he with h | ⟨h1, h2⟩
      · exact Or.inl h
      · exact Or.inr ⟨h1, by simpa using h2⟩
    · rw [withLogFrom_hash, fixedTableLoggedRun_bind, mem_support_bind_iff] at hz
      obtain ⟨p, hp, hz⟩ := hz
      rw [support_map] at hz
      obtain ⟨q, hq, rfl⟩ := hz
      rw [fixedTableLoggedRun_hashQuery, support_map] at hp
      obtain ⟨r, hr, rfl⟩ := hp
      obtain ⟨hr1, hag, -⟩ := fixedTable_hash d g c hc r hr
      rcases ih r.1 _ r.2 hag q hq e he with h | ⟨h1, h2⟩
      · rcases List.mem_append.mp h with h | h
        · exact Or.inl h
        · simp only [List.mem_singleton] at h
          subst h
          exact Or.inr ⟨hr1, by simp⟩
      · refine Or.inr ⟨h1, ?_⟩
        simp only [mem_freshKeysOfLog, List.mem_append] at h2 ⊢
        obtain ⟨x, hx, hxe⟩ := h2
        exact ⟨x, Or.inr hx, hxe⟩

theorem lk_append [DecidableEq D] (l : Tr D Rng) (d : D) (u : Rng) (t : D) :
    lk (l ++ [(d, u)]) t = (lk l t).or (if d = t then some u else none) := by
  unfold lk
  rw [List.find?_append]
  rcases h : l.find? (fun e => e.1 = t) with _ | e
  · by_cases hd : d = t <;> simp [h, hd]
  · simp [h]

/-- Against a lazily sampled oracle, the cache is the lookup function of the
transcript. -/
theorem withLogFrom_lazy [DecidableEq D] [SampleableType Rng]
    (oa : OracleComp (unifSpec + (D →ₒ Rng)) α) (l : Tr D Rng) (c : (D →ₒ Rng).QueryCache)
    (hinv : ∀ t, c t = lk l t) :
    ∀ z ∈ support ((simulateQ (D →ₒ Rng).romImpl (withLogFrom oa l)).run c),
      ∀ t, z.2 t = lk z.1.2 t := by
  induction oa using OracleComp.inductionOn generalizing l c with
  | pure a =>
    intro z hz
    rw [withLogFrom_pure] at hz
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact hinv
  | query_bind t next ih =>
    intro z hz
    rcases t with k | d
    · rw [withLogFrom_unif] at hz
      simp only [simulateQ_bind, StateT.run_bind] at hz
      rw [mem_support_bind_iff] at hz
      obtain ⟨p, hp, hz⟩ := hz
      have hpc : p.2 = c := by
        have h : (simulateQ (D →ₒ Rng).romImpl
            (liftM ((unifSpec + (D →ₒ Rng)).query (.inl k)))).run c =
            (fun u => (u, c)) <$> (liftM (unifSpec.query k) : ProbComp _) := by
          simpa using roSim.run_apply_inl (hashSpec := D →ₒ Rng) (D →ₒ Rng).randomOracle k c
        rw [h, support_map] at hp
        obtain ⟨u, -, rfl⟩ := hp
        rfl
      rw [hpc] at hz
      exact ih p.1 l c hinv z hz
    · rw [withLogFrom_hash] at hz
      simp only [simulateQ_bind, StateT.run_bind] at hz
      rw [mem_support_bind_iff] at hz
      obtain ⟨p, hp, hz⟩ := hz
      refine ih p.1 _ p.2 ?_ z hz
      have hrun : (simulateQ (D →ₒ Rng).romImpl
          (liftM ((unifSpec + (D →ₒ Rng)).query (.inr d)))).run c =
          ((D →ₒ Rng).randomOracle d).run c := by simp
      rw [hrun, randomOracle.run_eq] at hp
      intro t
      rw [lk_append]
      rcases hcd : c d with _ | u
      · rw [hcd] at hp
        simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hp
        obtain ⟨u, -, rfl⟩ := hp
        by_cases hdt : d = t
        · subst hdt
          rw [QueryCache.cacheQuery_self, ← hinv, hcd]
          simp
        · rw [QueryCache.cacheQuery_of_ne _ _ (Ne.symm hdt), hinv]
          simp [hdt]
      · rw [hcd] at hp
        simp only [support_pure, Set.mem_singleton_iff] at hp
        subst hp
        rw [hinv t]
        by_cases hdt : d = t
        · subst hdt
          rw [← hinv, hcd]
          simp
        · simp [hdt]

end Halfagg.LoggedRun
