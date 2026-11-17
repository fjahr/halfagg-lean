import VCVio.OracleComp.QueryTracking.RandomOracle.ExpectedFreshQueryInfinite
import VCVio.OracleComp.QueryTracking.QueryBound.Basic
import VCVio.EvalDist.Monad.Measure
import VCVio.CryptoFoundations.FiatShamir.QueryBounds

/-!
# Logged random-oracle runs: query counts and fixed tables

Generic facts about VCVio's `randomOracleLoggedRun` and `fixedTableLoggedRun`:

* `log_length_le`: a computation making at most `Q` hash queries logs at most `Q`.
* `expectedFreshQueryCharge_le`: so its expected fresh-query charge at a constant
  error `ε` is at most `Q * ε`.
* `fixedTable_support`: a run against a fixed answer table `g` only produces
  outputs the computation can produce, and keeps its cache inside `g`.
-/

open OracleSpec OracleComp
open scoped ENNReal

namespace Halfagg.LoggedRun

variable {D α : Type} {R : D → Type}

/-- Hash queries of `unifSpec + ofFn R`. -/
abbrev isHash : ℕ ⊕ D → Prop := fun i => i.isRight = true

/-- A computation with at most `Q` hash queries logs at most `Q` entries. -/
theorem log_length_le [DecidableEq D] [∀ d, SampleableType (R d)]
    (oa : OracleComp (unifSpec + ofFn R) α) (Q : ℕ) (h : oa.IsQueryBoundP isHash Q)
    (c : (ofFn R).QueryCache) :
    ∀ z ∈ support (randomOracleLoggedRun oa c), z.1.2.length ≤ Q := by
  induction oa using OracleComp.inductionOn generalizing Q c with
  | pure x =>
    intro z hz
    simp only [randomOracleLoggedRun, QueryImpl.passthrough_add, simulateQ_pure, WriterT.run_pure,
      List.empty_eq, StateT.run_pure, MonadAttach.support_pure, Set.mem_singleton_iff] at hz
    subst hz
    simp
  | query_bind t mx ih =>
    intro z hz
    rw [isQueryBoundP_query_bind_iff] at h
    rw [randomOracleLoggedRun_bind, mem_support_bind_iff] at hz
    obtain ⟨p, hp, hz⟩ := hz
    rw [support_map] at hz
    obtain ⟨q, hq, rfl⟩ := hz
    rcases t with k | d
    · rw [randomOracleLoggedRun_uniformQuery, support_map] at hp
      obtain ⟨u, -, rfl⟩ := hp
      have := ih u Q (by simpa [isHash] using h.2 u) c q hq
      simpa using this
    · rw [randomOracleLoggedRun_hashQuery, support_map] at hp
      obtain ⟨r, -, rfl⟩ := hp
      have hQ : 0 < Q := by simpa [isHash] using h.1
      have := ih r.1 (Q - 1) (by simpa [isHash] using h.2 r.1) r.2 q hq
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega

/-- With a constant error `ε` per fresh key, the expected fresh-query charge of a
computation with at most `Q` hash queries is at most `Q * ε`. -/
theorem expectedFreshQueryCharge_le [DecidableEq D] [∀ d, SampleableType (R d)]
    (oa : OracleComp (unifSpec + ofFn R) α) (Q : ℕ) (h : oa.IsQueryBoundP isHash Q)
    (ε : ℝ≥0∞) : expectedFreshQueryCharge oa (fun _ => ε) ≤ Q * ε := by
  unfold expectedFreshQueryCharge
  let _ : MeasurableSpace ((α × QueryLog (ofFn R)) × (ofFn R).QueryCache) := ⊤
  have hle : ∀ z ∈ support (randomOracleLoggedRun oa),
      freshQueryCharge (fun _ => ε) z.1.2 ≤ Q * ε := by
    intro z hz
    have hlen := log_length_le oa Q h ∅ z hz
    simp only [freshQueryCharge, Finset.sum_const, nsmul_eq_mul]
    gcongr
    exact (List.toFinset_card_le _).trans (by simpa using hlen)
  calc ∫⁻ z, freshQueryCharge (fun _ => ε) z.1.2 ∂𝒟[randomOracleLoggedRun oa]
      ≤ ∫⁻ _, (Q * ε : ℝ≥0∞) ∂𝒟[randomOracleLoggedRun oa] :=
        MeasureTheory.lintegral_mono_ae
          (evalDist.ae_of_forall_mem_support _ _ MeasurableSet.of_discrete hle)
    _ = Q * ε * 𝒟[randomOracleLoggedRun oa] Set.univ := MeasureTheory.lintegral_const _
    _ ≤ Q * ε := mul_le_of_le_one_right' (evalDist_apply_univ_le_one _)

/-- Every cached answer is the table's answer. -/
def Agree (c : (ofFn R).QueryCache) (g : ∀ d, R d) : Prop := ∀ t u, c t = some u → u = g t

theorem agree_empty (g : ∀ d, R d) : Agree (∅ : (ofFn R).QueryCache) g := by
  intro t u h; cases h

/-- One hash query against the fixed table returns the table's answer. -/
theorem fixedTable_hash [DecidableEq D] (t : D) (g : ∀ d, R d) (c : (ofFn R).QueryCache)
    (hc : Agree c g) :
    ∀ p ∈ support ((((QueryImpl.ofFn g).liftTarget ProbComp).withCaching t).run c),
      p.1 = g t ∧ Agree p.2 g ∧ p.2 t = some (g t) := by
  intro p hp
  rcases hct : c t with _ | u
  · rw [QueryImpl.withCaching_run_none _ hct] at hp
    have hl : ((QueryImpl.ofFn g).liftTarget ProbComp) t = pure (g t) := rfl
    rw [hl] at hp
    simp only [map_pure, MonadAttach.support_pure, Set.mem_singleton_iff] at hp
    subst hp
    refine ⟨rfl, ?_, by simp⟩
    intro t' u' h'
    by_cases ht : t' = t
    · subst ht; simpa using h'.symm
    · rw [QueryCache.cacheQuery_of_ne _ _ ht] at h'; exact hc t' u' h'
  · rw [QueryImpl.withCaching_run_some _ hct] at hp
    simp only [MonadAttach.support_pure, Set.mem_singleton_iff] at hp
    subst hp
    have := hc t u hct
    exact ⟨this, hc, by rw [hct, this]⟩

/-- A run against a fixed table only produces outputs the computation can
produce, and its cache stays inside the table. -/
theorem fixedTable_support [DecidableEq D] (oa : OracleComp (unifSpec + ofFn R) α)
    (g : ∀ d, R d) (c : (ofFn R).QueryCache) (hc : Agree c g) :
    ∀ z ∈ support (fixedTableLoggedRun oa g c), z.1.1 ∈ support oa ∧ Agree z.2 g := by
  induction oa using OracleComp.inductionOn generalizing c with
  | pure x =>
    intro z hz
    simp only [fixedTableLoggedRun, QueryImpl.passthrough_add, simulateQ_pure, WriterT.run_pure,
      List.empty_eq, StateT.run_pure, MonadAttach.support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact ⟨by simp, hc⟩
  | query_bind t mx ih =>
    intro z hz
    rw [fixedTableLoggedRun_bind, mem_support_bind_iff] at hz
    obtain ⟨p, hp, hz⟩ := hz
    rw [support_map] at hz
    obtain ⟨q, hq, rfl⟩ := hz
    rcases t with k | d
    · rw [fixedTableLoggedRun_uniformQuery, support_map] at hp
      obtain ⟨u, -, rfl⟩ := hp
      obtain ⟨h1, h2⟩ := ih u c hc q hq
      exact ⟨(mem_support_bind_iff _ _ _).mpr ⟨u, mem_support_query _ u, h1⟩, h2⟩
    · rw [fixedTableLoggedRun_hashQuery, support_map] at hp
      obtain ⟨r, hr, rfl⟩ := hp
      obtain ⟨-, hag, -⟩ := fixedTable_hash d g c hc r hr
      obtain ⟨h1, h2⟩ := ih r.1 r.2 hag q hq
      exact ⟨(mem_support_bind_iff _ _ _).mpr ⟨r.1, mem_support_query _ r.1, h1⟩, h2⟩

/-- Lifted sampling makes no hash queries. (After VCVio's
`FiatShamir.nmaHashQueryBound_liftComp_zero`.) -/
theorem liftComp_isHash_zero {β : Type} (oa : ProbComp β) :
    (liftComp oa (unifSpec + ofFn R)).IsQueryBoundP isHash 0 := by
  rw [liftComp_def]
  refine IsQueryBoundP.simulateQ_of_step (p := fun _ : ℕ => False)
    (impl := fun t => (liftM (unifSpec.query t) :
      OracleComp (unifSpec + ofFn R) (unifSpec.Range t)))
    (isQueryBoundP_false oa 0) (fun _ h => h.elim) ?_
  intro t _
  change (liftM ((unifSpec + ofFn R).query (Sum.inl t)) :
      OracleComp (unifSpec + ofFn R) _).IsQueryBoundP _ 0
  rw [isQueryBoundP_query_iff]
  simp [isHash]

end Halfagg.LoggedRun
