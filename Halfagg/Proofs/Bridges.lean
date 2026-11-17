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

variable {n : ℕ} [Fact n.Prime] {E X M : Type} [AddCommGroup E] [DecidableEq E]
  [DecidableEq X] [DecidableEq M] (C : Curve n E X) (challenge : X → X → M → ZMod n)

/-- The annotated experiment with a lazily sampled random oracle. -/
noncomputable def annROM (F : AlgForger n E X M) : ProbComp (Transcript n X M) :=
  (simulateQ (AnnSpec n X M).romImpl (annExperiment C challenge F)).run' ∅

end Halfagg.Security
