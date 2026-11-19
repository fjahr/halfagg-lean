import Halfagg.Proofs.BadBound

/-!
# The annotated experiment under a lazily sampled oracle

`annROM` is the annotated experiment with its random oracle sampled lazily.
-/

set_option linter.unusedSectionVars false

open OracleSpec OracleComp AlgebraicGroupModel.Interaction
open scoped ENNReal

namespace Halfagg.Security

open Taproot Taproot.Curve Taproot.BIP340 Taproot.BIP340Security Halfagg.LoggedRun

attribute [local instance] smulVal

variable {n : ℕ} [Fact n.Prime] {H E X M : Type} [AddCommGroup E] [DecidableEq E]
  [DecidableEq X] [DecidableEq M] (C : Curve n E X) (challenge : X → X → M → ZMod n)
variable [SampleableType H] {red : H → ZMod n}

/-- The annotated experiment with a lazily sampled random oracle. -/
noncomputable def annROM (red : H → ZMod n) (F : AlgForger n H E X M) :
    ProbComp (Transcript n X M) :=
  (simulateQ (AnnSpec n H X M).romImpl (annExperiment C challenge red F)).run' ∅

end Halfagg.Security
