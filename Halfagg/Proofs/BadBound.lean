import Halfagg.Proofs.Trace

/-!
# The forger's phase makes at most `q` hash queries

`annPhase1_bound`: key generation and the forger's run in the annotated
experiment make at most `q` randomizer queries, for a forger with at most `q`
randomizer requests.
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

/-! ## Query counts -/

/-- The scheme's signing makes no hash queries. -/
theorem sign_bound (pk : X) (sk : ZMod n) (msg : M) :
    ((bip340 (M := M) C challenge (OracleComp (unifSpec + AnnSpec n H X M))).sign pk sk
      msg).IsQueryBoundP isHash 0 := by
  simp only [bip340]
  rw [show ∀ (x : ProbComp (X × ZMod n)),
    (monadLift x : OracleComp (unifSpec + AnnSpec n H X M) _) =
    liftComp x (unifSpec + AnnSpec n H X M) from fun _ => (liftComp_eq_liftM _).symm]
  exact liftComp_isHash_zero _

theorem keygen_bound :
    ((bip340 (M := M) C challenge (OracleComp (unifSpec + AnnSpec n H X M))).keygen
      ).IsQueryBoundP isHash 0 := by
  simp only [bip340]
  rw [show ∀ (x : ProbComp (X × ZMod n)),
    (monadLift x : OracleComp (unifSpec + AnnSpec n H X M) _) =
    liftComp x (unifSpec + AnnSpec n H X M) from fun _ => (liftComp_eq_liftM _).symm]
  exact liftComp_isHash_zero _

/-- One request costs one hash query if it is a randomizer request, else none. -/
theorem annImpl_step (pk : X) (sk : ZMod n)
    (t : Explained (ZMod n) (Request X M) (Pts E)) (s : Core n X M) :
    ((annImpl (H := H) C challenge pk sk t).run s).IsQueryBoundP isHash
      (if isRand t.value.data = true then 1 else 0) := by
  obtain ⟨⟨data, groups⟩, coeffs⟩ := t
  cases data with
  | random k =>
    simp only [annImpl, coreImpl, isRand, StateT.run]
    rw [isQueryBoundP_query_bind_iff]
    simp
  | rand ms tail =>
    simp only [annImpl, coreImpl, isRand, StateT.run]
    rw [isQueryBoundP_query_bind_iff]
    simp
  | sign msg =>
    simp only [annImpl, coreImpl, isRand, StateT.run]
    exact isQueryBoundP_bind (n := 0) (m := 0) (sign_bound C challenge pk sk msg)
      fun _ _ => isQueryBoundP_pure _ _ _

theorem annPhase1_bound (F : AlgForger n H E X M) (q : ℕ)
    (hq : ∀ input, (F.main input).IsQueryBoundP (fun r => isRand r.value.data) q) :
    (annPhase1 C challenge F).IsQueryBoundP isHash q := by
  unfold annPhase1
  refine (isQueryBoundP_bind (n := 0) (m := q) (keygen_bound C challenge) fun ks _ =>
    (isQueryBoundP_bind (n := q) (m := 0) ?_ fun _ _ => isQueryBoundP_pure _ _ _)).mono
    (by omega)
  exact IsQueryBoundP.simulateQ_run_StateT_of_step (hq _)
    (fun t s => annImpl_step C challenge ks.1 ks.2 t s) Core.init

end Halfagg.Security
