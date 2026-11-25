import Halfagg.Proofs.LoggedRun
import Halfagg.SecurityROM
import VCVio.OracleComp.QueryTracking.RandomOracle.ExpectedFreshQuery
import VCVio.CryptoFoundations.FiatShamir.Sigma

/-!
# A lazily sampled random oracle on a finite domain is a uniformly sampled table

`rom_eq_table`: for a computation with a random oracle on a finite domain, the
probability of an event under lazy sampling equals its probability when the whole
answer table is sampled first and every query is answered from it. This is
VCVio's `evalDist_randomOracleLoggedRun_eq_fixedTable_finite` without the log and
the cache.
-/

open OracleSpec OracleComp
open scoped ENNReal

namespace Halfagg.LoggedRun

variable {D α : Type} {R : D → Type}

theorem tableImpl_inr (g : ∀ d, R d) (d : D) : tableImpl g (.inr d) = pure (g d) := rfl

/-- A fixed-table run without its log and cache answers every query from the
table. -/
theorem fixedTable_project [DecidableEq D] (oa : OracleComp (unifSpec + ofFn R) α)
    (g : ∀ d, R d) (c : (ofFn R).QueryCache) (hc : Agree c g) :
    (fun z => z.1.1) <$> fixedTableLoggedRun oa g c = simulateQ (tableImpl g) oa := by
  induction oa using OracleComp.inductionOn generalizing c with
  | pure x => simp [fixedTableLoggedRun]
  | query_bind t mx ih =>
    rw [fixedTableLoggedRun_bind, map_bind]
    simp only [Functor.map_map, simulateQ_bind, simulateQ_spec_query]
    rcases t with k | d
    · rw [fixedTableLoggedRun_uniformQuery, bind_map_left]
      exact bind_congr fun u => ih u c hc
    · rw [fixedTableLoggedRun_hashQuery, bind_map_left, tableImpl_inr, pure_bind]
      rcases hct : c d with _ | u
      · rw [QueryImpl.withCaching_run_none _ hct]
        have hl : ((QueryImpl.ofFn g).liftTarget ProbComp) d = pure (g d) := rfl
        rw [hl]
        simp only [map_pure, pure_bind]
        refine ih (g d) _ ?_
        intro t' u' h'
        by_cases ht : t' = d
        · subst ht; simpa using h'.symm
        · rw [QueryCache.cacheQuery_of_ne _ _ ht] at h'; exact hc t' u' h'
      · rw [QueryImpl.withCaching_run_some _ hct, pure_bind, hc d u hct]
        exact ih (g d) c hc

/-- **Lazy sampling is a uniformly sampled table**, for events of the output. -/
theorem rom_eq_table [DecidableEq D] [Finite D] [∀ d, SampleableType (R d)]
    [SampleableType (∀ d, R d)] (oa : OracleComp (unifSpec + ofFn R) α) (p : α → Prop) :
    Pr{let x ← (simulateQ (ofFn R).romImpl oa).run' ∅}[p x] =
      Pr{let x ← (($ᵗ (∀ d, R d)) >>= fun g => simulateQ (tableImpl g) oa)}[p x] := by
  let _ : MeasurableSpace ((α × QueryLog (ofFn R)) × (ofFn R).QueryCache) := ⊤
  have h1 : (simulateQ (ofFn R).romImpl oa).run' ∅ =
      (fun z => z.1.1) <$> randomOracleLoggedRun oa := by
    rw [StateT.run'_eq, ← randomOracleLoggedRun_project, Functor.map_map]
  have h2 : (($ᵗ (∀ d, R d)) >>= fun g => simulateQ (tableImpl g) oa) =
      (fun z => z.1.1) <$> (($ᵗ (∀ d, R d)) >>= fun g =>
        fixedTableLoggedRun oa (completeTable ∅ g) ∅) := by
    rw [map_bind]
    refine bind_congr fun g => ?_
    rw [completeTable_empty, fixedTable_project oa g ∅ (agree_empty g)]
  rw [h1, h2, prEvent_map, prEvent_map, prEvent_eq_evalDist_of_discrete,
    prEvent_eq_evalDist_of_discrete,
    evalDist_randomOracleLoggedRun_eq_fixedTable_finite oa ∅]

end Halfagg.LoggedRun

namespace Halfagg.LoggedRun

/-- A bound for every draw, with an additive constant, survives the draw. -/
theorem prEvent_bind_le_add_const {α β γ : Type} (mx : ProbComp α) (f : α → ProbComp β)
    (f' : α → ProbComp γ) (p : β → Prop) (p' : γ → Prop) (c : ℝ≥0∞)
    (h : ∀ a, Pr{let y ← f a}[p y] ≤ Pr{let y ← f' a}[p' y] + c) :
    Pr{let y ← mx >>= f}[p y] ≤ Pr{let y ← mx >>= f'}[p' y] + c := by
  let : MeasurableSpace α := ⊤
  rw [prEvent_bind_eq_lintegral_of_discrete, prEvent_bind_eq_lintegral_of_discrete]
  calc ∫⁻ a, Pr{let y ← f a}[p y] ∂𝒟[mx]
      ≤ ∫⁻ a, (Pr{let y ← f' a}[p' y] + c) ∂𝒟[mx] := MeasureTheory.lintegral_mono h
    _ = ∫⁻ a, Pr{let y ← f' a}[p' y] ∂𝒟[mx] + c * 𝒟[mx] Set.univ := by
        rw [MeasureTheory.lintegral_add_right _ measurable_const, MeasureTheory.lintegral_const]
    _ ≤ _ := by
        gcongr
        exact mul_le_of_le_one_right' (evalDist_apply_univ_le_one mx)

end Halfagg.LoggedRun

namespace Halfagg.LoggedRun

open scoped Classical in
/-- An adversary's advantage against a Fiat-Shamir scheme in the random oracle
model, with the hash table sampled first. The statement uses the decidable
equality of VCVio's `FiatShamir.runtime`. -/
theorem fs_advantage_eq_table {M Commit Chal PK SK S : Type} [Finite (M × Commit)]
    [SampleableType Chal] [SampleableType (M × Commit → Chal)]
    {sigAlg : SignatureAlg (OracleComp (unifSpec + (M × Commit →ₒ Chal))) M PK SK S}
    (adv : SignatureAlg.UnforgeableAdversary sigAlg) :
    SignatureAlg.unforgeableAdvantage (FiatShamir.runtime (Commit := Commit) (Chal := Chal) M)
        adv =
      Pr{let b ← (($ᵗ (M × Commit → Chal)) >>= fun g =>
        simulateQ (tableImpl g) (SignatureAlg.unforgeableExperiment adv))}[b = true] := by
  unfold SignatureAlg.unforgeableAdvantage
  rw [FiatShamir.runtime, FiatShamir.runtimeWithCache, ProbCompRuntime.rom_evalDist,
    ← prEvent_eq_evalDist_singleton, rom_eq_table]

end Halfagg.LoggedRun
