import Halfagg.Proofs.BindingPairs

/-!
# Binding: the challenge side and the bound

`binding_bound` adds the challenge side to `pair_term`.

The challenge hash is degenerate on the adversary's output (`badC`) if some
item's term `R + e⋅P` vanishes or if the two lists are different single items
with the same term. With the challenge hash sampled lazily, every fresh
challenge makes a term vanish or collide with an earlier one with probability at
most `(s + 1)/n` for a cache of `s` keys (`good_fresh`), so the output is
degenerate with probability at most `Q²/n` (`chal_lazy`).

`inner_table` connects the two views: the adversary with the randomizer hash
sampled inside is, against a fixed challenge table, the adversary of the game.
-/

set_option linter.unusedSectionVars false

open OracleSpec OracleComp
open scoped ENNReal

namespace Halfagg.Security

open Taproot Taproot.Curve Taproot.BIP340 Halfagg.LoggedRun

variable {n : ℕ} [Fact n.Prime] {H E X M : Type} [AddCommGroup E] [DecidableEq E]
  [DecidableEq X] [DecidableEq M] (C : Curve n E X)
variable [SampleableType H] (red : H → ZMod n)

/-! ## The challenge side: the adversary with the randomizer hash inside -/

/-- The term `R + e⋅P` of an item with the challenge `e`. -/
def termE (it : Item X M) (e : ZMod n) : E :=
  (C.liftX it.1).getD 0 + e.val • (C.liftX it.2.1).getD 0

/-- The challenge-hash key of an item. -/
def keyOfItem (it : Item X M) : M × (X × X) := (it.2.2, (it.1, it.2.1))

/-- The adversary's oracles as computations with only the challenge hash as an
oracle: the randomizer hash is sampled lazily inside, with its cache as state. -/
noncomputable def bindInner : QueryImpl (BindSpec n H X M)
    (StateT (RandSpec H X M).QueryCache (OracleComp (unifSpec + ChalSpec n X M)))
  | .inl (.inl k) => fun cH => do
      let u ← (liftM ((unifSpec + ChalSpec n X M).query (.inl k)) :
        OracleComp (unifSpec + ChalSpec n X M) _)
      pure (u, cH)
  | .inl (.inr key) => fun cH => do
      let e ← (liftM ((unifSpec + ChalSpec n X M).query (.inr key)) :
        OracleComp (unifSpec + ChalSpec n X M) _)
      pure (e, cH)
  | .inr L => fun cH => liftM (((RandSpec H X M).randomOracle L).run cH)

/-- Ask for the challenge of an item. -/
def qItem (it : Item X M) : OracleComp (BindSpec n H X M) (Item X M × ZMod n) :=
  (fun e => (it, e)) <$> (liftM ((BindSpec n H X M).query (.inl (.inr (keyOfItem it)))) :
    OracleComp (BindSpec n H X M) (ZMod n))

/-- The adversary, followed by challenge queries for the items of both lists. -/
noncomputable def chalProg (A : BindAdversary n H X M) :
    OracleComp (BindSpec n H X M) ((AggSig n X × List (X × M) × List (X × M)) ×
      List (Item X M × ZMod n) × List (Item X M × ZMod n)) := do
  let out ← A.main
  let ps ← (items out.2.1 out.1.rs).mapM qItem
  let ps' ← (items out.2.2 out.1.rs).mapM qItem
  pure (out, ps, ps')

/-- The degenerate cases of `badC`, from items with their challenges. -/
def badB (ps ps' : List (Item X M × ZMod n)) : Bool :=
  (ps ++ ps').any (fun p => lifts C p.1 && decide (termE C p.1 p.2 = 0)) ||
    match ps, ps' with
    | [p], [p'] => decide (p.1 ≠ p'.1) && lifts C p.1 && lifts C p'.1 &&
        decide (termE C p.1 p.2 = termE C p'.1 p'.2)
    | _, _ => false

theorem badC_badB (g : M × (X × X) → ZMod n) (agg : AggSig n X) (pm pm' : List (X × M))
    (h : badC C (hOf g) agg pm pm') :
    badB C ((items pm agg.rs).map fun it => (it, g (keyOfItem it)))
      ((items pm' agg.rs).map fun it => (it, g (keyOfItem it))) = true := by
  unfold badB
  rw [Bool.or_eq_true]
  rcases h with ⟨it, hit, hl, h0⟩ | ⟨it, it', hL, hL', hne, hl, hl', heq⟩
  · left
    rw [← List.map_append, List.any_eq_true]
    exact ⟨(it, g (keyOfItem it)), List.mem_map.mpr ⟨it, hit, rfl⟩, by
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨hl, h0⟩⟩
  · right
    rw [hL, hL']
    simp only [List.map_cons, List.map_nil, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨⟨hne, hl⟩, hl'⟩, heq⟩

/-! ## Against a fixed challenge table -/

section TableC

variable (g : M × (X × X) → ZMod n)

/-- With the challenge hash answered from a table, the adversary with the
randomizer hash inside is the adversary under the lazily sampled randomizer
hash. -/
theorem inner_table {α : Type} (prog : OracleComp (BindSpec n H X M) α)
    (cH : (RandSpec H X M).QueryCache) :
    simulateQ (tableImpl g) ((simulateQ bindInner prog).run cH) =
      (simulateQ (RandSpec H X M).romImpl (simulateQ (answerChalB g) prog)).run cH := by
  induction prog using OracleComp.inductionOn generalizing cH with
  | pure a => simp
  | query_bind t next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rcases t with (k | key) | L
    · have h1 : (bindInner (H := H) (.inl (.inl k))).run cH =
          ((liftM ((unifSpec + ChalSpec n X M).query (.inl k)) :
            OracleComp (unifSpec + ChalSpec n X M) _) >>= fun u => pure (u, cH)) := rfl
      have h2 : (simulateQ (RandSpec H X M).romImpl
          (answerChalB (H := H) g (.inl (.inl k)))).run cH =
          (fun u => (u, cH)) <$> (liftM (unifSpec.query k) : ProbComp _) := by
        simpa [answerChalB] using roSim.run_apply_inl (hashSpec := RandSpec H X M)
          (RandSpec H X M).randomOracle k cH
      have h3 : simulateQ (tableImpl g) (liftM ((unifSpec + ChalSpec n X M).query (.inl k)) :
          OracleComp (unifSpec + ChalSpec n X M) _) = (liftM (unifSpec.query k) : ProbComp _) := by
        rw [simulateQ_spec_query]
        rfl
      rw [h1, h2]
      simp only [simulateQ_bind, simulateQ_pure, h3, bind_assoc, pure_bind, bind_map_left]
      exact bind_congr fun u => ih u cH
    · have h1 : (bindInner (H := H) (.inl (.inr key))).run cH =
          ((liftM ((unifSpec + ChalSpec n X M).query (.inr key)) :
            OracleComp (unifSpec + ChalSpec n X M) _) >>= fun e => pure (e, cH)) := rfl
      rw [h1]
      simp only [simulateQ_bind, simulateQ_pure, table_hash, pure_bind, answerChalB,
        StateT.run_pure]
      exact ih (g key) cH
    · have h1 : (bindInner (n := n) (.inr L)).run cH =
          (liftM (((RandSpec H X M).randomOracle L).run cH) :
            OracleComp (unifSpec + ChalSpec n X M) _) := rfl
      have h2 : (simulateQ (RandSpec H X M).romImpl
          (answerChalB (n := n) (H := H) g (.inr L))).run cH =
          ((RandSpec H X M).randomOracle L).run cH := by
        simp [answerChalB]
      rw [h1, h2, table_lift]
      exact bind_congr fun p => ih p.1 p.2

end TableC

/-! ## The challenge hash sampled lazily -/

/-- `R + v⋅P` for a challenge key and its answer. -/
def TK (key : M × (X × X)) (v : ZMod n) : E :=
  (C.liftX key.2.1).getD 0 + v.val • (C.liftX key.2.2).getD 0

/-- Both encodings of a challenge key lift. -/
def liftsK (key : M × (X × X)) : Prop :=
  (C.liftX key.2.1).isSome = true ∧ (C.liftX key.2.2).isSome = true

/-- No cached challenge makes a term vanish, and no two cached challenges give
the same term. -/
def Good (cC : (ChalSpec n X M).QueryCache) : Prop :=
  ∀ k v, cC k = some v → liftsK C k → TK C k v ≠ 0 ∧
    ∀ k' v', cC k' = some v' → k' ≠ k → liftsK C k' → TK C k' v' ≠ TK C k v

/-- A fresh challenge breaks `Good` with probability at most `(s + 1)/n`, for a
cache with at most `s` keys. -/
theorem good_fresh (hord : PrimeOrder n E) {cC : (ChalSpec n X M).QueryCache} (hG : Good C cC)
    (k : M × (X × X)) (hk : cC k = none) (ks : List (M × (X × X)))
    (hdom : ∀ k', cC k' ≠ none → k' ∈ ks) :
    Pr{let v ← $ᵗ (ZMod n)}[¬ Good C (cC.cacheQuery k v)] ≤
      ((ks.length + 1 : ℕ) : ℝ≥0∞) * (n : ℝ≥0∞)⁻¹ := by
  classical
  by_cases hl : liftsK C k
  swap
  · rw [prEvent_eq_zero_of_forall_mem_support]
    · exact zero_le
    · intro v _
      rw [not_not]
      intro k₁ v₁ h₁ hl₁
      have hk₁ : k₁ ≠ k := fun h => hl (h ▸ hl₁)
      rw [QueryCache.cacheQuery_of_ne _ _ hk₁] at h₁
      refine ⟨(hG k₁ v₁ h₁ hl₁).1, fun k' v' h' hne hl' => ?_⟩
      have hk' : k' ≠ k := fun h => hl (h ▸ hl')
      rw [QueryCache.cacheQuery_of_ne _ _ hk'] at h'
      exact (hG k₁ v₁ h₁ hl₁).2 k' v' h' hne hl'
  obtain ⟨P, hP⟩ := Option.isSome_iff_exists.mp hl.2
  have hP0 : P ≠ 0 := (C.liftX_spec _ _ hP).1
  have hTK : ∀ v : ZMod n, TK C k v = (C.liftX k.2.1).getD 0 + v.val • P := by
    intro v
    simp [TK, hP]
  have hone : ∀ W : E, Pr{let v ← $ᵗ (ZMod n)}[(C.liftX k.2.1).getD 0 + v.val • P = W] ≤
      (n : ℝ≥0∞)⁻¹ := fun W => fresh_hit_prob (id : ZMod n → ZMod n) (id_bound n) hord hP0 _ W
  have hincl : ∀ v : ZMod n, ¬ Good C (cC.cacheQuery k v) →
      (C.liftX k.2.1).getD 0 + v.val • P = 0 ∨
        ∃ k' ∈ ks.toFinset, ∃ v', cC k' = some v' ∧
          (C.liftX k.2.1).getD 0 + v.val • P = TK C k' v' := by
    intro v hbad
    by_contra hno
    rw [not_or] at hno
    obtain ⟨h0, hcol⟩ := hno
    apply hbad
    intro k₁ v₁ h₁ hl₁
    by_cases hk₁ : k₁ = k
    · subst hk₁
      rw [QueryCache.cacheQuery_self] at h₁
      cases h₁
      refine ⟨by rw [hTK]; exact h0, fun k' v' h' hne _ => ?_⟩
      rw [QueryCache.cacheQuery_of_ne _ _ hne] at h'
      rw [hTK]
      exact fun heq => hcol ⟨k', List.mem_toFinset.mpr (hdom k' (by rw [h']; simp)), v', h',
        heq.symm⟩
    · rw [QueryCache.cacheQuery_of_ne _ _ hk₁] at h₁
      refine ⟨(hG k₁ v₁ h₁ hl₁).1, fun k' v' h' hne hl' => ?_⟩
      by_cases hk' : k' = k
      · subst hk'
        rw [QueryCache.cacheQuery_self] at h'
        cases h'
        rw [hTK]
        exact fun heq => hcol ⟨k₁, List.mem_toFinset.mpr (hdom k₁ (by rw [h₁]; simp)), v₁, h₁,
          heq⟩
      · rw [QueryCache.cacheQuery_of_ne _ _ hk'] at h'
        exact (hG k₁ v₁ h₁ hl₁).2 k' v' h' hne hl'
  refine (prEvent_mono_of_support _ _ _ fun v _ hv => hincl v hv).trans ?_
  refine (prEvent_or_le _ _ _).trans ?_
  have hsum : Pr{let v ← $ᵗ (ZMod n)}[∃ k' ∈ ks.toFinset, ∃ v', cC k' = some v' ∧
      (C.liftX k.2.1).getD 0 + v.val • P = TK C k' v'] ≤
      (ks.length : ℝ≥0∞) * (n : ℝ≥0∞)⁻¹ := by
    refine (prEvent_exists_finset_le _ _ _).trans ?_
    refine (Finset.sum_le_card_nsmul _ _ (n : ℝ≥0∞)⁻¹ fun k' _ => ?_).trans ?_
    · rcases hc : cC k' with _ | v'
      · rw [prEvent_eq_zero_of_forall_mem_support]
        · exact zero_le
        · rintro v - ⟨v', h, -⟩
          cases h
      · refine (prEvent_mono_of_support _ _ _ fun v _ hv => ?_).trans (hone (TK C k' v'))
        obtain ⟨v'', h, heq⟩ := hv
        cases h
        exact heq
    · rw [nsmul_eq_mul]
      exact mul_le_mul_left (by exact_mod_cast List.toFinset_card_le ks) _
  calc Pr{let v ← $ᵗ (ZMod n)}[(C.liftX k.2.1).getD 0 + v.val • P = 0] +
        Pr{let v ← $ᵗ (ZMod n)}[∃ k' ∈ ks.toFinset, ∃ v', cC k' = some v' ∧
          (C.liftX k.2.1).getD 0 + v.val • P = TK C k' v']
      ≤ (n : ℝ≥0∞)⁻¹ + (ks.length : ℝ≥0∞) * (n : ℝ≥0∞)⁻¹ := add_le_add (hone 0) hsum
    _ = ((ks.length + 1 : ℕ) : ℝ≥0∞) * (n : ℝ≥0∞)⁻¹ := by
        push_cast
        ring

/-! ## The adversary's run with a lazily sampled challenge hash -/

section InnerRun

variable (cH : (RandSpec H X M).QueryCache) (cC : (ChalSpec n X M).QueryCache)

theorem inner_unif (k : ℕ) :
    (simulateQ (ChalSpec n X M).romImpl ((bindInner (H := H) (.inl (.inl k))).run cH)).run cC =
      (fun u => ((u, cH), cC)) <$> (liftM (unifSpec.query k) : ProbComp _) := by
  have h1 : (bindInner (H := H) (.inl (.inl k))).run cH =
      ((liftM ((unifSpec + ChalSpec n X M).query (.inl k)) :
        OracleComp (unifSpec + ChalSpec n X M) _) >>= fun u => pure (u, cH)) := rfl
  rw [h1]
  simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure, chal_unif,
    bind_map_left]
  rfl

theorem inner_chal (key : M × (X × X)) :
    (simulateQ (ChalSpec n X M).romImpl ((bindInner (H := H) (.inl (.inr key))).run cH)).run cC =
      (fun p => ((p.1, cH), p.2)) <$> ((ChalSpec n X M).randomOracle key).run cC := by
  have h1 : (bindInner (H := H) (.inl (.inr key))).run cH =
      ((liftM ((unifSpec + ChalSpec n X M).query (.inr key)) :
        OracleComp (unifSpec + ChalSpec n X M) _) >>= fun e => pure (e, cH)) := rfl
  rw [h1]
  simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure, chal_ro]
  rw [map_eq_bind_pure_comp]
  rfl

theorem inner_rand (L : List (Item X M)) :
    (simulateQ (ChalSpec n X M).romImpl ((bindInner (n := n) (.inr L)).run cH)).run cC =
      (fun p => (p, cC)) <$> ((RandSpec H X M).randomOracle L).run cH := by
  have h1 : (bindInner (n := n) (.inr L)).run cH =
      (liftM (((RandSpec H X M).randomOracle L).run cH) :
        OracleComp (unifSpec + ChalSpec n X M) _) := rfl
  rw [h1, OracleSpec.simulateQ_romImpl_liftM_run]
  rfl

end InnerRun

/-- One lazily sampled challenge returns the cached answer and keeps the cache. -/
theorem chal_ro_support (key : M × (X × X)) (cC : (ChalSpec n X M).QueryCache) :
    ∀ p ∈ support (((ChalSpec n X M).randomOracle key).run cC),
      p.2 key = some p.1 ∧ ∀ k v, cC k = some v → p.2 k = some v := by
  intro p hp
  rw [randomOracle.run_eq] at hp
  rcases hc : cC key with _ | u
  · rw [hc] at hp
    simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hp
    obtain ⟨u, -, rfl⟩ := hp
    refine ⟨by simp, fun k v h => ?_⟩
    rw [QueryCache.cacheQuery_of_ne _ _ (fun hk => by rw [hk, hc] at h; cases h)]
    exact h
  · rw [hc] at hp
    simp only [support_pure, Set.mem_singleton_iff] at hp
    subst hp
    exact ⟨hc, fun _ _ h => h⟩

/-- **The adversary's run keeps `Good`**, except with probability
`Q⋅(s + Q)/n` for `Q` challenge queries from a cache with at most `s` keys. -/
theorem good_inv (hord : PrimeOrder n E) {α : Type} (prog : OracleComp (BindSpec n H X M) α)
    (Q : ℕ) (hQ : prog.IsQueryBoundP (fun t => isChalB t) Q)
    (cH : (RandSpec H X M).QueryCache) (cC : (ChalSpec n X M).QueryCache)
    (ks : List (M × (X × X))) (hdom : ∀ k, cC k ≠ none → k ∈ ks) (hG : Good C cC) :
    Pr{let z ← (simulateQ (ChalSpec n X M).romImpl ((simulateQ bindInner prog).run cH)).run cC}[
      ¬ Good C z.2] ≤ ((Q * (ks.length + Q) : ℕ) : ℝ≥0∞) * (n : ℝ≥0∞)⁻¹ := by
  induction prog using OracleComp.inductionOn generalizing Q cH cC ks with
  | pure a =>
    rw [prEvent_eq_zero_of_forall_mem_support]
    · exact zero_le
    · intro z hz
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact not_not.mpr hG
  | query_bind t next ih =>
    rw [isQueryBoundP_query_bind_iff] at hQ
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rcases t with (k | key) | L
    · rw [inner_unif, bind_map_left]
      exact prEvent_bind_le_of_forall _ _ _ _ fun u _ =>
        ih u Q ((hQ.2 u).mono (by simp [isChalB])) cH cC ks hdom hG
    · have hpos : 0 < Q := hQ.1.resolve_left (by simp [isChalB])
      obtain ⟨Q', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hpos)
      have hQ' : ∀ u, (next u).IsQueryBoundP (fun t => isChalB t) Q' :=
        fun u => (hQ.2 u).mono (by simp [isChalB])
      rw [inner_chal, bind_map_left, randomOracle.run_eq]
      rcases hc : cC key with _ | v
      · simp only [bind_assoc, pure_bind]
        have hdom' : ∀ (v : ZMod n) k, (cC.cacheQuery key v) k ≠ none → k ∈ key :: ks := by
          intro v k hk
          by_cases hkk : k = key
          · rw [hkk]
            exact List.mem_cons_self
          · rw [QueryCache.cacheQuery_of_ne _ _ hkk] at hk
            exact List.mem_cons_of_mem _ (hdom k hk)
        refine (prEvent_bind_le_prEvent_add_of_support _ _
          (fun v => ¬ Good C (cC.cacheQuery key v)) _
          (ε := ((Q' * ((key :: ks).length + Q') : ℕ) : ℝ≥0∞) * (n : ℝ≥0∞)⁻¹)
          fun v _ hv => ih v Q' (hQ' v) cH (cC.cacheQuery key v) (key :: ks) (hdom' v)
            (not_not.mp hv)).trans ?_
        refine (add_le_add (good_fresh C hord hG key hc ks hdom) le_rfl).trans ?_
        rw [← add_mul]
        refine mul_le_mul_left ?_ _
        norm_cast
        simp only [List.length_cons]
        nlinarith
      · simp only [pure_bind]
        refine (ih v Q' (hQ' v) cH cC ks hdom hG).trans ?_
        refine mul_le_mul_left ?_ _
        norm_cast
        nlinarith
    · rw [inner_rand, bind_map_left]
      exact prEvent_bind_le_of_forall _ _ _ _ fun p _ =>
        ih p.1 Q ((hQ.2 p.1).mono (by simp [isChalB])) p.2 cC ks hdom hG

/-! ## The challenges of the output's items -/

theorem qItem_run (it : Item X M) (cH : (RandSpec H X M).QueryCache)
    (cC : (ChalSpec n X M).QueryCache) :
    (simulateQ (ChalSpec n X M).romImpl ((simulateQ bindInner (qItem (H := H) it)).run cH)).run
        cC =
      (fun p => (((it, p.1), cH), p.2)) <$>
        ((ChalSpec n X M).randomOracle (keyOfItem it)).run cC := by
  unfold qItem
  rw [simulateQ_map, simulateQ_spec_query, StateT.run_map, simulateQ_map, StateT.run_map,
    inner_chal, Functor.map_map]

/-- The challenges asked for a list of items are in the final cache. -/
theorem qItems_support (its : List (Item X M)) (cH : (RandSpec H X M).QueryCache)
    (cC : (ChalSpec n X M).QueryCache) :
    ∀ y ∈ support ((simulateQ (ChalSpec n X M).romImpl
        ((simulateQ bindInner (its.mapM (qItem (H := H)))).run cH)).run cC),
      y.1.2 = cH ∧ (∀ k v, cC k = some v → y.2 k = some v) ∧
        ∀ p ∈ y.1.1, y.2 (keyOfItem p.1) = some p.2 := by
  induction its generalizing cC with
  | nil =>
    intro y hy
    simp only [List.mapM_nil, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hy
    subst hy
    exact ⟨rfl, fun _ _ h => h, by simp⟩
  | cons it its ih =>
    intro y hy
    rw [List.mapM_cons] at hy
    simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure] at hy
    rw [mem_support_bind_iff] at hy
    obtain ⟨p, hp, hy⟩ := hy
    rw [qItem_run, support_map] at hp
    obtain ⟨r, hr, rfl⟩ := hp
    rw [mem_support_bind_iff] at hy
    obtain ⟨q, hq, hy⟩ := hy
    simp only [support_pure, Set.mem_singleton_iff] at hy
    subst hy
    obtain ⟨h1, h2⟩ := chal_ro_support _ _ r hr
    obtain ⟨e1, e2, e3⟩ := ih r.2 q hq
    refine ⟨e1, fun k v h => e2 k v (h2 k v h), fun p hp => ?_⟩
    rcases List.mem_cons.mp hp with rfl | hp
    · exact e2 _ _ h1
    · exact e3 p hp

/-- A degenerate output contradicts `Good` for a cache that holds its challenges. -/
theorem badB_not_good (cC : (ChalSpec n X M).QueryCache) (ps ps' : List (Item X M × ZMod n))
    (hps : ∀ p ∈ ps ++ ps', cC (keyOfItem p.1) = some p.2) (hb : badB C ps ps' = true) :
    ¬ Good C cC := by
  intro hG
  have hlk : ∀ it : Item X M, lifts C it = true → liftsK C (keyOfItem it) := by
    intro it h
    simpa [lifts, liftsK, keyOfItem] using h
  unfold badB at hb
  rw [Bool.or_eq_true] at hb
  rcases hb with hb | hb
  · rw [List.any_eq_true] at hb
    obtain ⟨p, hp, hpp⟩ := hb
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hpp
    exact (hG _ _ (hps p hp) (hlk _ hpp.1)).1 hpp.2
  · rcases ps with _ | ⟨p, _ | ⟨p2, ps⟩⟩ <;> rcases ps' with _ | ⟨p', _ | ⟨p2', ps'⟩⟩ <;>
      simp only [Bool.false_eq_true] at hb
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
    obtain ⟨⟨⟨hne, hl⟩, hl'⟩, heq⟩ := hb
    have hk : keyOfItem p'.1 ≠ keyOfItem p.1 := by
      intro h
      apply hne
      simp only [keyOfItem, Prod.mk.injEq] at h
      exact Prod.ext h.2.1.symm (Prod.ext h.2.2.symm h.1.symm)
    exact (hG _ _ (hps p (by simp)) (hlk _ hl)).2 _ _ (hps p' (by simp)) hk (hlk _ hl') heq.symm

theorem answer_qItems (g : M × (X × X) → ZMod n) (its : List (Item X M)) :
    simulateQ (answerChalB (H := H) g) (its.mapM qItem) =
      pure (its.map fun it => (it, g (keyOfItem it))) := by
  induction its with
  | nil => simp
  | cons it its ih =>
    rw [List.mapM_cons]
    simp only [simulateQ_bind, simulateQ_pure, ih, qItem, simulateQ_map, simulateQ_spec_query,
      answerChalB, map_pure, pure_bind, List.map_cons]

/-! ## Query counts -/

theorem qItems_bound (its : List (Item X M)) :
    (its.mapM (qItem (n := n) (H := H))).IsQueryBoundP (fun t => isChalB t) its.length := by
  induction its with
  | nil => simp
  | cons it its ih =>
    rw [List.mapM_cons]
    refine (isQueryBoundP_bind (n := 1) ?_ fun _ _ =>
      isQueryBoundP_bind (m := 0) ih fun _ _ => isQueryBoundP_pure _ _ _).mono
        (by simp only [List.length_cons]; omega)
    unfold qItem
    rw [isQueryBoundP_map_iff, isQueryBoundP_query_iff]
    exact fun _ => Nat.one_pos

theorem items_length_le (pm : List (X × M)) (rs : List X) : (items pm rs).length ≤ rs.length := by
  simp only [items, List.length_zipWith]
  omega

theorem chalProg_bound (A : BindAdversary n H X M) (qC ℓ : ℕ)
    (hC : A.main.IsQueryBoundP (fun t => isChalB t) qC)
    (hL : ∀ out ∈ support A.main, out.1.rs.length ≤ ℓ) :
    (chalProg A).IsQueryBoundP (fun t => isChalB t) (qC + 2 * ℓ) := by
  unfold chalProg
  refine (isQueryBoundP_bind (m := ℓ + (ℓ + 0)) hC fun out hout => ?_).mono (by omega)
  have h1 := (items_length_le out.2.1 out.1.rs).trans (hL out hout)
  have h2 := (items_length_le out.2.2 out.1.rs).trans (hL out hout)
  exact isQueryBoundP_bind ((qItems_bound _).mono h1) fun _ _ =>
    isQueryBoundP_bind ((qItems_bound _).mono h2) fun _ _ => isQueryBoundP_pure _ _ _

theorem answerB_support (g : M × (X × X) → ZMod n) {α : Type}
    (prog : OracleComp (BindSpec n H X M) α) :
    ∀ z ∈ support (simulateQ (answerChalB g) prog), z ∈ support prog := by
  induction prog using OracleComp.inductionOn with
  | pure x =>
    intro z hz
    simpa using hz
  | query_bind t next ih =>
    intro z hz
    simp only [simulateQ_bind, simulateQ_spec_query] at hz
    rw [mem_support_bind_iff] at hz
    obtain ⟨y, -, hz⟩ := hz
    exact (mem_support_bind_iff _ _ _).mpr ⟨y, mem_support_query _ y, ih _ z hz⟩

theorem zs_bound (L : List (Item X M)) (is : List ℕ) :
    (is.mapM (zQuery red (n := n) L)).IsQueryBoundP isHash is.length := by
  induction is with
  | nil => simp
  | cons i is ih =>
    rw [List.mapM_cons]
    refine (isQueryBoundP_bind (n := 1) ?_ fun _ _ =>
      isQueryBoundP_bind (m := 0) ih fun _ _ => isQueryBoundP_pure _ _ _).mono
        (by simp only [List.length_cons]; omega)
    unfold zQuery
    split_ifs
    · exact isQueryBoundP_pure _ _ _
    · rw [isQueryBoundP_map_iff]
      change (liftM ((unifSpec + RandSpec H X M).query (.inr (L.take (i + 1)))) :
        OracleComp (unifSpec + RandSpec H X M) H).IsQueryBoundP isHash 1
      rw [isQueryBoundP_query_iff]
      exact fun _ => Nat.one_pos

theorem gameX_bound (g : M × (X × X) → ZMod n) (A : BindAdversary n H X M) (qZ ℓ : ℕ)
    (hZ : A.main.IsQueryBoundP (fun t => isRandB t) qZ)
    (hL : ∀ out ∈ support A.main, out.1.rs.length ≤ ℓ) :
    (bindGameX red (simulateQ (answerChalB g) A.main)).IsQueryBoundP isHash (qZ + 2 * ℓ) := by
  have hA : (simulateQ (answerChalB (H := H) g) A.main).IsQueryBoundP isHash qZ := by
    refine IsQueryBoundP.simulateQ_of_step hZ (fun t ht => ?_) (fun t ht => ?_)
    · rcases t with (k | key) | L
      · simp [isRandB] at ht
      · simp [isRandB] at ht
      · simp only [answerChalB]
        rw [isQueryBoundP_query_iff]
        exact fun _ => Nat.one_pos
    · rcases t with (k | key) | L
      · simp only [answerChalB]
        rw [isQueryBoundP_query_iff]
        simp [isHash]
      · exact isQueryBoundP_pure _ _ _
      · simp [isRandB] at ht
  unfold bindGameX
  refine (isQueryBoundP_bind (m := ℓ + (ℓ + 0)) hA fun out hout => ?_).mono (by omega)
  have hl := hL out (answerB_support g A.main out hout)
  exact isQueryBoundP_bind ((zs_bound red _ _).mono (by simpa using hl)) fun _ _ =>
    isQueryBoundP_bind ((zs_bound red _ _).mono (by simpa using hl)) fun _ _ =>
      isQueryBoundP_pure _ _ _

/-! ## The two sides together -/

/-- The challenge-side experiment: whether the adversary's output is degenerate,
as a computation with only the challenge hash as an oracle. -/
noncomputable def chalExp (A : BindAdversary n H X M) :
    OracleComp (unifSpec + ChalSpec n X M) Bool :=
  (fun r => badB C r.1.2.1 r.1.2.2) <$> (simulateQ bindInner (chalProg A)).run ∅

theorem chalExp_table (g : M × (X × X) → ZMod n) (A : BindAdversary n H X M) :
    simulateQ (tableImpl g) (chalExp C A) =
      (fun p : (AggSig n X × List (X × M) × List (X × M)) × (RandSpec H X M).QueryCache =>
        badB C ((items p.1.2.1 p.1.1.rs).map fun it => (it, g (keyOfItem it)))
          ((items p.1.2.2 p.1.1.rs).map fun it => (it, g (keyOfItem it)))) <$>
        (simulateQ (RandSpec H X M).romImpl (simulateQ (answerChalB g) A.main)).run ∅ := by
  unfold chalExp
  rw [simulateQ_map, inner_table]
  unfold chalProg
  simp only [simulateQ_bind, simulateQ_pure, answer_qItems, pure_bind, StateT.run_bind,
    StateT.run_pure, map_bind, map_pure]
  rw [map_eq_bind_pure_comp]
  rfl

/-- **The output is degenerate with probability at most `Q²/n`**, for `Q`
challenge queries including those of the output's items. -/
theorem chal_lazy (hord : PrimeOrder n E) (A : BindAdversary n H X M) (qC ℓ : ℕ)
    (hC : A.main.IsQueryBoundP (fun t => isChalB t) qC)
    (hL : ∀ out ∈ support A.main, out.1.rs.length ≤ ℓ) :
    Pr{let b ← (simulateQ (ChalSpec n X M).romImpl (chalExp C A)).run' ∅}[b = true] ≤
      (((qC + 2 * ℓ) * (qC + 2 * ℓ) : ℕ) : ℝ≥0∞) * (n : ℝ≥0∞)⁻¹ := by
  unfold chalExp
  rw [StateT.run'_eq, simulateQ_map, StateT.run_map, Functor.map_map, prEvent_map]
  have hinv := good_inv C hord (chalProg A) (qC + 2 * ℓ) (chalProg_bound A qC ℓ hC hL) ∅ ∅ []
    (fun k h => absurd rfl h) (fun k v h => by cases h)
  simp only [List.length_nil, zero_add] at hinv
  refine (prEvent_mono_of_support _ _ _ fun z hz hb => ?_).trans hinv
  unfold chalProg at hz
  simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure] at hz
  rw [mem_support_bind_iff] at hz
  obtain ⟨p1, -, hz⟩ := hz
  rw [mem_support_bind_iff] at hz
  obtain ⟨p2, hp2, hz⟩ := hz
  rw [mem_support_bind_iff] at hz
  obtain ⟨p3, hp3, hz⟩ := hz
  simp only [support_pure, Set.mem_singleton_iff] at hz
  subst hz
  obtain ⟨-, -, h23⟩ := qItems_support _ _ _ p2 hp2
  obtain ⟨-, h32, h33⟩ := qItems_support _ _ _ p3 hp3
  refine badB_not_good C _ _ _ (fun p hp => ?_) hb
  rcases List.mem_append.mp hp with h | h
  · exact h32 _ _ (h23 p h)
  · exact h33 p h

/-- An event of the adversary's output is at most as likely in the whole game
as after the adversary's run. -/
theorem gameX_fst
    (A : OracleComp (unifSpec + RandSpec H X M) (AggSig n X × List (X × M) × List (X × M)))
    (P : AggSig n X × List (X × M) × List (X × M) → Prop) :
    Pr{let x ← (simulateQ (RandSpec H X M).romImpl (bindGameX red A)).run' ∅}[P x.1] ≤
      Pr{let p ← (simulateQ (RandSpec H X M).romImpl A).run ∅}[P p.1] := by
  unfold bindGameX
  rw [StateT.run'_eq, prEvent_map]
  simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure]
  have h := prEvent_bind_le_prEvent_add_of_support
    ((simulateQ (RandSpec H X M).romImpl A).run ∅)
    (fun p => (simulateQ (RandSpec H X M).romImpl ((List.range p.1.1.rs.length).mapM
        (zQuery red (items p.1.2.1 p.1.1.rs)))).run p.2 >>= fun q =>
      (simulateQ (RandSpec H X M).romImpl ((List.range p.1.1.rs.length).mapM
        (zQuery red (items p.1.2.2 p.1.1.rs)))).run q.2 >>= fun q' =>
        (pure ((p.1, q.1, q'.1), q'.2) : ProbComp _))
    (fun p => P p.1) (fun z => P z.1.1) (ε := 0) fun p _ hno => by
      rw [nonpos_iff_eq_zero]
      refine prEvent_eq_zero_of_forall_mem_support _ _ fun z hz => ?_
      simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hz
      obtain ⟨q, -, q', -, rfl⟩ := hz
      exact hno
  rw [add_zero] at h
  exact h

/-- **Binding of half-aggregation**, in the form of the proofs file. -/
theorem binding_bound [Finite M] [Finite X] [SampleableType (M × (X × X) → ZMod n)]
    (hord : PrimeOrder n E) (A : BindAdversary n H X M) (qC qZ ℓ : ℕ)
    (hC : A.main.IsQueryBoundP (fun t => isChalB t) qC)
    (hZ : A.main.IsQueryBoundP (fun t => isRandB t) qZ)
    (hL : ∀ out ∈ support A.main, out.1.rs.length ≤ ℓ) (μ : ℝ≥0∞) (hμ : RedBound red μ) :
    bindAdvantage C red A ≤
      (((qC + 2 * ℓ) * (qC + 2 * ℓ) : ℕ) : ℝ≥0∞) * (n : ℝ≥0∞)⁻¹ +
        (((qZ + 2 * ℓ) * (qZ + 2 * ℓ) : ℕ) : ℝ≥0∞) * μ := by
  classical
  unfold bindAdvantage bindExperiment
  have h1 : Pr{let b ← (($ᵗ (M × (X × X) → ZMod n)) >>= fun g =>
        (simulateQ (RandSpec H X M).romImpl
          (bindGame C red (hOf g) (simulateQ (answerChalB g) A.main))).run' ∅)}[b = true] ≤
      Pr{let b ← (($ᵗ (M × (X × X) → ZMod n)) >>= fun g =>
        simulateQ (tableImpl g) (chalExp C A))}[b = true] +
        (((qZ + 2 * ℓ) * (qZ + 2 * ℓ) : ℕ) : ℝ≥0∞) * μ := by
    refine prEvent_bind_le_add_const _ _ _ _ _ _ fun g => ?_
    rw [chalExp_table, prEvent_map]
    have hrun : (simulateQ (RandSpec H X M).romImpl
        (bindGame C red (hOf g) (simulateQ (answerChalB g) A.main))).run' ∅ =
        (fun x => bindWins C (hOf g) x.1.1 x.1.2.1 x.1.2.2 x.2.1 x.2.2) <$>
          (simulateQ (RandSpec H X M).romImpl
            (bindGameX red (simulateQ (answerChalB g) A.main))).run' ∅ := by
      rw [bindGame_eq]
      simp only [simulateQ_map, StateT.run'_eq, StateT.run_map, Functor.map_map]
    rw [hrun, prEvent_map]
    refine ((prEvent_mono_of_support _ _
      (fun x => badB C ((items x.1.2.1 x.1.1.rs).map fun it => (it, g (keyOfItem it)))
          ((items x.1.2.2 x.1.1.rs).map fun it => (it, g (keyOfItem it))) = true ∨
        (bindWins C (hOf g) x.1.1 x.1.2.1 x.1.2.2 x.2.1 x.2.2 = true ∧
          ¬ badC C (hOf g) x.1.1 x.1.2.1 x.1.2.2))
      fun x _ hw => ?_).trans (prEvent_or_le _ _ _)).trans (add_le_add ?_ ?_)
    · by_cases hb : badC C (hOf g) x.1.1 x.1.2.1 x.1.2.2
      · exact Or.inl (badC_badB C g _ _ _ hb)
      · exact Or.inr ⟨hw, hb⟩
    · exact gameX_fst red (simulateQ (answerChalB g) A.main)
        (fun out => badB C ((items out.2.1 out.1.rs).map fun it => (it, g (keyOfItem it)))
          ((items out.2.2 out.1.rs).map fun it => (it, g (keyOfItem it))) = true)
    · exact pair_term C red hμ hord (hOf g) _ _ (gameX_bound red g A qZ ℓ hZ hL)
  refine h1.trans (add_le_add ?_ le_rfl)
  exact le_of_eq_of_le (rom_eq_table (chalExp C A) fun b => b = true).symm
    (chal_lazy C hord A qC ℓ hC hL)

end Halfagg.Security
