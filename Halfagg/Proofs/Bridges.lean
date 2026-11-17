import Halfagg.Proofs.BadBound

/-!
# The annotated experiment under a lazily sampled oracle

`annROM` is the annotated experiment with its random oracle sampled lazily, and
`annROM_bad` the bad-event bound transported from `ann_bad_bound`.
-/

set_option linter.unusedSectionVars false

open OracleSpec OracleComp AlgebraicGroupModel.Interaction
open scoped ENNReal

namespace Halfagg.Security

open Taproot Taproot.Curve Taproot.BIP340 Taproot.BIP340Security Halfagg.LoggedRun

attribute [local instance] smulVal

variable {n : ℕ} [Fact n.Prime] {E X M : Type} [AddCommGroup E] [DecidableEq E]
  [DecidableEq X] [DecidableEq M] (C : Curve n E X) (challenge : X → X → M → ZMod n)

/-- The annotated experiment with a lazily sampled random oracle. -/
noncomputable def annROM (F : AlgForger n E M) : ProbComp (Transcript n X M) :=
  (simulateQ (AnnSpec n X M).romImpl (annExperiment C challenge F)).run' ∅

theorem annROM_bad [Inhabited M] (hx0 : C.liftX (C.x 0) = none) (F : AlgForger n E M)
    (q ℓ : ℕ)
    (hq : ∀ input, (F.main input).IsQueryBoundP (fun r => isRand r.value.data) q)
    (hℓ : ∀ input, ∀ out ∈ support (F.main input), out.value.data.ms.length ≤ ℓ) :
    Pr{let t ← annROM C challenge F}[winT C challenge t ∧ ¬ extractOK C challenge t] ≤
      (q + ℓ : ℝ≥0∞) / n := by
  have h : annROM C challenge F =
      (fun z => z.1.1) <$> randomOracleLoggedRun (annExperiment C challenge F) := by
    unfold annROM
    rw [StateT.run'_eq, ← randomOracleLoggedRun_project, Functor.map_map]
  rw [h, prEvent_map]
  exact ann_bad_bound C challenge hx0 F q ℓ hq hℓ

end Halfagg.Security
