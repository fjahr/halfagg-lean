import Halfagg.Proofs.Transcript
import Halfagg.Proofs.Verifier

/-!
# The bad event has probability at most `(q + 1)⋅μ`

`annROM_bad`: in the annotated experiment, the transcript wins while the
reduction's extraction fails with probability at most `(q + 1)⋅μ`, for a forger
with at most `q` randomizer requests. Here `μ` bounds the probability that the
reduction of a uniform hash output is a given scalar (`RedBound`).

A failed extraction means that the randomized sum `Σ zᵢ⋅β*ᵢ` of the forgery
vanishes while some `β*ᵢ` is nonzero. Either the forger's own randomizer queries
already contain a completed bad configuration (`Dcfg`): every prefix with a
nonzero `β*ᵢ` was queried and the sum of the answers vanishes. Each of the
forger's `q` queries completes one with probability at most `μ`
(`phase1_cfg_bound`). Or the verifier draws at least one of these randomizers
itself, and then the sum vanishes with probability at most `μ`
(`verifier_bound`).
-/

set_option linter.unusedSectionVars false

open OracleSpec OracleComp AlgebraicGroupModel.Interaction
open scoped ENNReal

namespace Halfagg.Security

open Taproot Taproot.Curve Taproot.BIP340 Taproot.BIP340Security Halfagg.LoggedRun

attribute [local instance] smulVal

variable {n : ℕ} [Fact n.Prime] {H E X M : Type} [AddCommGroup E] [DecidableEq E]
  [DecidableEq X] [DecidableEq M] (C : Curve n E X) (challenge : X → X → M → ZMod n)
variable [SampleableType H] {red : H → ZMod n} {μ : ℝ≥0∞}

/-- The coefficient `β*` of an item. -/
def betaOf (a : AItem n X M) : ZMod n := (starRep challenge a).2

/-- The forger's phase with its transcript of randomizer queries. -/
noncomputable def loggedPhase1 (F : AlgForger n H E X M) :
    OracleComp (unifSpec + AnnSpec n H X M)
      ((X × Explained (ZMod n) (Out n M) (Pts E) × Core n X M) ×
        Tr (List (AItem n X M)) H) :=
  withLog (annPhase1 C challenge F)

/-- **The forger completes a bad configuration with probability at most `q⋅μ`.** -/
theorem phase1_cfg_bound (hμ : RedBound red μ) (F : AlgForger n H E X M) (q : ℕ)
    (hq : ∀ input, (F.main input).IsQueryBoundP (fun r => isRand r.value.data) q) :
    Pr{let z ← randomOracleLoggedRun (loggedPhase1 C challenge F)}[
      Dcfg (finalItems C z.1.1.1.2.1 z.1.1.1.2.2) (betaOf challenge)
        (fun K => (lk z.1.1.2 K).map red)] ≤ (q : ℝ≥0∞) * μ := by
  refine (prEvent_randomOracle_le_expectedFreshQueryCharge (loggedPhase1 C challenge F)
    (fun out => Dcfg (finalItems C out.1.2.1 out.1.2.2) (betaOf challenge)
      (fun K => (lk out.2 K).map red))
    (fun t g => badKey challenge t (fun l => red (g l))) (fun _ => μ) ?_ ?_).trans ?_
  · intro g z hz hD
    have hlog := withLogFrom_fixed (annPhase1 C challenge F) g [] ∅ (agree_empty g) z hz
    have hlk : ∀ K u, lk z.1.1.2 K = some u → u = g K ∧ K ∈ freshKeysOfLog z.1.2 := by
      intro K u hK
      unfold lk at hK
      obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.mp hK
      have hmem := List.mem_of_find?_eq_some he
      have hkey : e.1 = K := by simpa using List.find?_some he
      rcases hlog e hmem with h | ⟨h1, h2⟩
      · cases h
      · exact ⟨hkey ▸ h1, hkey ▸ h2⟩
    set items := finalItems C z.1.1.1.2.1 z.1.1.1.2.2 with hitems
    obtain ⟨hne, hcov0, hsum⟩ := hD
    have hcov : ∀ idx (h : idx < items.length), 1 ≤ idx → betaOf challenge items[idx] ≠ 0 →
        lk z.1.1.2 (items.take (idx + 1)) ≠ none :=
      fun idx h h1 hw hnone => hcov0 idx h h1 hw (by simp [hnone])
    obtain ⟨j, hj1, hjlen, hwj, -, hcut⟩ := cut_last items
      (fun i => if i = 0 then 1 else ((lk z.1.1.2 (items.take (i + 1))).map red).getD 0)
      (betaOf challenge) (by simp) hne hsum
    obtain ⟨u, hu⟩ := Option.ne_none_iff_exists'.mp (hcov j hjlen hj1 hwj)
    refine ⟨items.take (j + 1), (hlk _ u hu).2, ?_⟩
    have hlen : (items.take (j + 1)).length = j + 1 := by rw [List.length_take]; omega
    refine ⟨by omega, items[j], ?_, hwj, ?_⟩
    · rw [List.getLast?_eq_getElem?, hlen]
      simp [hjlen]
    · rw [← hcut]
      refine isum_congr_idx fun idx hi => ?_
      rw [hlen] at hi
      simp only [zero_add, List.getElem_take]
      unfold zOf
      by_cases h0 : idx = 0
      · subst h0
        simp [betaOf]
      · simp only [h0, ↓reduceIte]
        by_cases hw : betaOf challenge items[idx] = 0
        · change _ * betaOf challenge items[idx] = _ * betaOf challenge items[idx]
          rw [hw, mul_zero, mul_zero]
        · obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp
            (hcov idx (by omega) (by omega) hw)
          rw [hv, Option.map_some, Option.getD_some, (hlk _ v hv).1, List.take_take,
            min_eq_left (by omega : idx + 1 ≤ j + 1)]
          rfl
  · exact fun t g => badKey_prob challenge hμ t g
  · exact expectedFreshQueryCharge_le _ q
      (withLogFrom_bound _ q (annPhase1_bound C challenge F q hq) []) _

/-- A failed extraction means that the randomized sum of the coefficients
vanishes while some coefficient is nonzero. -/
theorem fail_sum [Inhabited M] (hx0 : C.liftX (C.x 0) = none) (F : AlgForger n H E X M)
    (r : X × Explained (ZMod n) (Out n M) (Pts E) × Core n X M)
    (hr : r ∈ support (annPhase1 C challenge F)) (zs : List (ZMod n))
    (hwin : winT C challenge
      (r.1, finalItems C r.2.1 r.2.2, r.2.1.value.data.s, zs, r.2.2.signed))
    (hno : ¬ extractOK C challenge
      (r.1, finalItems C r.2.1 r.2.2, r.2.1.value.data.s, zs, r.2.2.signed)) :
    (∃ b ∈ finalItems C r.2.1 r.2.2, betaOf challenge b ≠ 0) ∧
      isum (fun i b => zs.getD i 0 * betaOf challenge b) 0 (finalItems C r.2.1 r.2.2) = 0 := by
  obtain ⟨d, hd, heven, hpk, -, recv, hcore, hval⟩ := phase1_ok C challenge hx0 F r hr
  simp only [winT, extractOK, hpk] at hwin hno
  have hl : ∀ it ∈ toItems C r.2.1.value.data.ms (r.2.1.value.groups ()),
      lifts C it = true := by
    have h := hwin
    simp only [aggWins, verifyWith, Bool.and_eq_true, List.all_eq_true] at h
    have h2 := h.1.1.2
    rw [items_map, finalItems, map_strip_annotate] at h2
    exact h2
  have hok := finalItems_ok C hx0 d hcore hval hl
  rcases extract_or_bad C challenge d hd heven _ _ _ _ hok hwin with hex | h
  · exact (hno hex).elim
  · exact h

/-- **An event that makes the randomized sum vanish is unlikely.** If an event
of the transcript implies that some coefficient `β*ᵢ` is nonzero while the
randomized sum `Σ zᵢ⋅β*ᵢ` vanishes, its probability is at most `(q + 1)⋅μ`. -/
theorem annROM_sum_bound (hμ : RedBound red μ) (F : AlgForger n H E X M) (q : ℕ)
    (hq : ∀ input, (F.main input).IsQueryBoundP (fun r => isRand r.value.data) q)
    (ev : Transcript n X M → Prop)
    (hev : ∀ r ∈ support (annPhase1 C challenge F), ∀ zs : List (ZMod n),
      ev (r.1, finalItems C r.2.1 r.2.2, r.2.1.value.data.s, zs, r.2.2.signed) →
      (∃ b ∈ finalItems C r.2.1 r.2.2, betaOf challenge b ≠ 0) ∧
        isum (fun i b => zs.getD i 0 * betaOf challenge b) 0 (finalItems C r.2.1 r.2.2) = 0) :
    Pr{let t ← annROM C challenge red F}[ev t] ≤ (q + 1 : ℝ≥0∞) * μ := by
  classical
  have hrom : annROM C challenge red F =
      ((simulateQ (AnnSpec n H X M).romImpl (loggedPhase1 C challenge F)).run ∅ >>= fun p =>
        ((List.range (finalItems C p.1.1.2.1 p.1.1.2.2).length).mapM
          (jZ red (finalItems C p.1.1.2.1 p.1.1.2.2))).run p.2 >>= fun y =>
            pure (p.1.1.1, finalItems C p.1.1.2.1 p.1.1.2.2, p.1.1.2.1.value.data.s, y.1,
              p.1.1.2.2.signed)) := by
    unfold annROM annExperiment loggedPhase1
    conv_lhs => rw [← withLog_fst (annPhase1 C challenge F)]
    simp only [simulateQ_bind, simulateQ_pure, StateT.run'_eq, StateT.run_bind,
      StateT.run_pure, zs_ann, map_bind, bind_map_left, map_pure]
  rw [hrom]
  refine (prEvent_bind_le_prEvent_add_of_support _ _
    (fun p => Dcfg (finalItems C p.1.1.2.1 p.1.1.2.2) (betaOf challenge)
      (fun K => (lk p.1.2 K).map red)) _
    (ε := μ) fun p hp hD => ?_).trans ?_
  · rw [bind_pure_comp, prEvent_map]
    have hlazy := withLogFrom_lazy (annPhase1 C challenge F) [] ∅ (fun t => rfl) p hp
    have hD' : ¬ Dcfg (finalItems C p.1.1.2.1 p.1.1.2.2) (betaOf challenge)
        (fun K => (p.2 K).map red) := by
      rwa [show (fun K => (p.2 K).map red) = fun K => (lk p.1.2 K).map red from
        funext fun K => by rw [hlazy K]]
    have hr : p.1.1 ∈ support (annPhase1 C challenge F) := by
      have h1 : p.1 ∈ support (loggedPhase1 C challenge F) := by
        refine support_simulateQ_run'_subset (AnnSpec n H X M).romImpl _ ∅ ?_
        rw [StateT.run'_eq, support_map]
        exact ⟨p, hp, rfl⟩
      rw [← withLog_fst (annPhase1 C challenge F), support_map]
      exact ⟨p.1, h1, rfl⟩
    exact (prEvent_mono_of_support _ _ _ fun y _ hy => hev p.1.1 hr y.1 hy).trans
      (verifier_bound _ _ hμ p.2 hD')
  · have h1 : Pr{let p ← (simulateQ (AnnSpec n H X M).romImpl
          (loggedPhase1 C challenge F)).run ∅}[
        Dcfg (finalItems C p.1.1.2.1 p.1.1.2.2) (betaOf challenge)
          (fun K => (lk p.1.2 K).map red)] =
        Pr{let z ← randomOracleLoggedRun (loggedPhase1 C challenge F)}[
          Dcfg (finalItems C z.1.1.1.2.1 z.1.1.1.2.2) (betaOf challenge)
            (fun K => (lk z.1.1.2 K).map red)] := by
      rw [← randomOracleLoggedRun_project, prEvent_map]
    rw [h1]
    have h2 := phase1_cfg_bound C challenge hμ F q hq
    rw [add_mul, one_mul]
    exact add_le_add h2 le_rfl

/-- **The bad event is unlikely.** -/
theorem annROM_bad [Inhabited M] (hμ : RedBound red μ) (hx0 : C.liftX (C.x 0) = none)
    (F : AlgForger n H E X M)
    (q : ℕ) (hq : ∀ input, (F.main input).IsQueryBoundP (fun r => isRand r.value.data) q) :
    Pr{let t ← annROM C challenge red F}[winT C challenge t ∧ ¬ extractOK C challenge t] ≤
      (q + 1 : ℝ≥0∞) * μ :=
  annROM_sum_bound C challenge hμ F q hq _
    fun r hr zs h => fail_sum C challenge hx0 F r hr zs h.1 h.2

end Halfagg.Security
