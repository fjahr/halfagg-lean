import Halfagg.Proofs.Trace

/-!
# The bad event has probability at most `(q + ℓ)/n`

`ann_bad_bound`: in the annotated experiment, the transcript wins while the
reduction's extraction fails with probability at most `(q + ℓ)/n`, for a forger
with at most `q` randomizer requests and forgeries of at most `ℓ` items.
-/

set_option linter.unusedSectionVars false

open OracleSpec OracleComp AlgebraicGroupModel.Interaction
open scoped ENNReal

namespace Halfagg.Security

open Taproot Taproot.Curve Taproot.BIP340 Taproot.BIP340Security Halfagg.LoggedRun

attribute [local instance] smulVal

variable {n : ℕ} [Fact n.Prime] {E X M : Type} [AddCommGroup E] [DecidableEq E]
  [DecidableEq X] [DecidableEq M] (C : Curve n E X) (challenge : X → X → M → ZMod n)

/-! ## Query counts -/

theorem zq_bound (items : List (AItem n X M)) (i : ℕ) :
    (zQueryAnn items i).IsQueryBoundP isHash 1 := by
  unfold zQueryAnn
  split_ifs
  · exact isQueryBoundP_pure _ _ _
  · rw [isQueryBoundP_query_iff]; simp

theorem zs_bound (items : List (AItem n X M)) (is : List ℕ) :
    (is.mapM (zQueryAnn items)).IsQueryBoundP isHash is.length := by
  induction is with
  | nil => rw [List.mapM_nil]; exact isQueryBoundP_pure _ _ _
  | cons i is ih =>
    rw [List.mapM_cons]
    refine (isQueryBoundP_bind (n := 1) (m := is.length) (zq_bound items i) fun b _ =>
      (isQueryBoundP_bind (n := is.length) (m := 0) ih fun _ _ =>
        isQueryBoundP_pure _ _ _)).mono ?_
    simp only [List.length_cons]; omega

/-- The scheme's signing makes no hash queries. -/
theorem sign_bound (pk : X) (sk : ZMod n) (msg : M) :
    ((bip340 (M := M) C challenge (OracleComp (unifSpec + AnnSpec n X M))).sign pk sk
      msg).IsQueryBoundP isHash 0 := by
  simp only [bip340]
  rw [show ∀ (x : ProbComp (X × ZMod n)), (monadLift x : OracleComp (unifSpec + AnnSpec n X M) _) =
    liftComp x (unifSpec + AnnSpec n X M) from fun _ => (liftComp_eq_liftM _).symm]
  exact liftComp_isHash_zero _

theorem keygen_bound :
    ((bip340 (M := M) C challenge (OracleComp (unifSpec + AnnSpec n X M))).keygen
      ).IsQueryBoundP isHash 0 := by
  simp only [bip340]
  rw [show ∀ (x : ProbComp (X × ZMod n)), (monadLift x : OracleComp (unifSpec + AnnSpec n X M) _) =
    liftComp x (unifSpec + AnnSpec n X M) from fun _ => (liftComp_eq_liftM _).symm]
  exact liftComp_isHash_zero _

/-- One request costs one hash query if it is a randomizer request, else none. -/
theorem annImpl_step (pk : X) (sk : ZMod n)
    (t : Explained (ZMod n) (Request M) (Pts E)) (s : Core n X M) :
    ((annImpl C challenge pk sk t).run s).IsQueryBoundP isHash
      (if isRand t.value.data = true then 1 else 0) := by
  obtain ⟨⟨data, groups⟩, coeffs⟩ := t
  cases data with
  | random k =>
    simp only [annImpl, coreImpl, isRand, StateT.run]
    rw [isQueryBoundP_query_bind_iff]
    simp
  | rand ms =>
    simp only [annImpl, coreImpl, isRand, StateT.run]
    rw [isQueryBoundP_query_bind_iff]
    simp
  | sign msg =>
    simp only [annImpl, coreImpl, isRand, StateT.run]
    exact isQueryBoundP_bind (n := 0) (m := 0) (sign_bound C challenge pk sk msg)
      fun _ _ => isQueryBoundP_pure _ _ _

theorem annPhase1_bound (F : AlgForger n E M) (q : ℕ)
    (hq : ∀ input, (F.main input).IsQueryBoundP (fun r => isRand r.value.data) q) :
    (annPhase1 C challenge F).IsQueryBoundP isHash q := by
  unfold annPhase1
  refine (isQueryBoundP_bind (n := 0) (m := q) (keygen_bound C challenge) fun ks _ =>
    (isQueryBoundP_bind (n := q) (m := 0) ?_ fun _ _ => isQueryBoundP_pure _ _ _)).mono
    (by omega)
  exact IsQueryBoundP.simulateQ_run_StateT_of_step (hq _)
    (fun t s => annImpl_step C challenge ks.1 ks.2 t s) Core.init

theorem annExperiment_bound (hx0 : C.liftX (C.x 0) = none) (F : AlgForger n E M) (q ℓ : ℕ)
    (hq : ∀ input, (F.main input).IsQueryBoundP (fun r => isRand r.value.data) q)
    (hℓ : ∀ input, ∀ out ∈ support (F.main input), out.value.data.ms.length ≤ ℓ) :
    (annExperiment C challenge F).IsQueryBoundP isHash (q + ℓ) := by
  unfold annExperiment
  refine isQueryBoundP_bind (annPhase1_bound C challenge F q hq) fun r hr => ?_
  obtain ⟨d, -, -, -, hout, -⟩ := phase1_ok C challenge hx0 F r hr
  have hlen : (finalItems C r.2.1 r.2.2).length ≤ ℓ := by
    simp only [finalItems, annotate, List.length_map]
    exact (toItems_length_le C _ _).trans (hℓ _ _ hout)
  refine (isQueryBoundP_bind (m := 0) (zs_bound _ _) fun _ _ =>
    isQueryBoundP_pure _ _ _).mono ?_
  simpa using hlen

/-! ## The bound -/

/-- **The bad event is unlikely.** -/
theorem ann_bad_bound [Inhabited M] (hx0 : C.liftX (C.x 0) = none) (F : AlgForger n E M)
    (q ℓ : ℕ)
    (hq : ∀ input, (F.main input).IsQueryBoundP (fun r => isRand r.value.data) q)
    (hℓ : ∀ input, ∀ out ∈ support (F.main input), out.value.data.ms.length ≤ ℓ) :
    Pr{let z ← randomOracleLoggedRun (annExperiment C challenge F)}[
      winT C challenge z.1.1 ∧ ¬ extractOK C challenge z.1.1] ≤ (q + ℓ : ℝ≥0∞) / n := by
  refine (prEvent_randomOracle_le_expectedFreshQueryCharge (annExperiment C challenge F)
    (fun t => winT C challenge t ∧ ¬ extractOK C challenge t) (badKey challenge)
    (fun _ => (n : ℝ≥0∞)⁻¹) ?_ ?_).trans ?_
  · rintro g z hz ⟨hw, hno⟩
    exact ann_trace C challenge hx0 F g z hz hw hno
  · exact fun t g => badKey_prob challenge t g
  · refine (expectedFreshQueryCharge_le _ (q + ℓ)
      (annExperiment_bound C challenge hx0 F q ℓ hq hℓ) _).trans (le_of_eq ?_)
    rw [div_eq_mul_inv]
    push_cast
    rfl

end Halfagg.Security
