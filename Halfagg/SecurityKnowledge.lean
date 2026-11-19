import Halfagg.Security

/-!
# Knowledge of the individual signatures: definitions

The review surface for `halfagg_knowledge` (`Halfagg/Knowledge.lean`).

Unforgeability is a statement about one honest key. This file states more:
whoever produces an aggregate that verifies knows a BIP340 signature for every
item, including the items under keys it chose itself.

"Knows" means that an extractor computes the signatures. `extractor` runs the
forger as `reduction` does: it forwards signing requests to a signing oracle,
answers randomizer requests from its own lazily sampled table and records the
forger's explanations. From those it computes an `sᵢ` for every item
`(rᵢ, pkᵢ, mᵢ)` of the forger's aggregate (`extractSig`). It never sees the
secret key.

The extracted signatures have the nonces `rᵢ` of the aggregate. They need not
be the signatures that were given to `Aggregate`, which an aggregate does not
determine (`aggregate_accepts_invalid`).
-/

open OracleSpec OracleComp AlgebraicGroupModel.Interaction
open scoped ENNReal

namespace Halfagg.Security

open Taproot Taproot.Curve Taproot.BIP340 Taproot.BIP340Security

variable {n : ℕ} [Fact n.Prime] {H E X M : Type} [AddCommGroup E] [DecidableEq E]
  [DecidableEq X] [DecidableEq M] (C : Curve n E X) (challenge : X → X → M → ZMod n)
variable [SampleableType H] (red : H → ZMod n)

attribute [local instance] smulVal

/-! ## The verification game -/

/-- `VerifyAggregate` accepts the items `(rᵢ, pkᵢ, mᵢ)` and `s` with the
randomizers `zs`: the first condition of `aggWins`. -/
def aggVerifies (its : List (Item X M)) (s : ZMod n) (zs : List (ZMod n)) : Bool :=
  verifyWith C challenge (fun i => zs.getD i 0) ⟨its.map (·.1), s⟩ (its.map (·.2))

/-- The game of `aggExperiment` without the condition on the target key: the
adversary's aggregate passes `VerifyAggregate`. -/
noncomputable def aggVerifyExperiment (A : AggAdversary n H X M) :
    OracleComp (unifSpec + RandSpec H X M) Bool := do
  let alg := bip340 (M := M) C challenge (OracleComp (unifSpec + RandSpec H X M))
  let (pk, sk) ← alg.keygen
  let ((its, s), _) ← alg.runWithSigningOracle pk sk (A.main pk)
  let zs ← (List.range its.length).mapM (zQuery red its)
  return aggVerifies C challenge its s zs

/-- The probability that the adversary's aggregate verifies, with a lazily
sampled random oracle. -/
noncomputable def aggVerifyAdvantage (A : AggAdversary n H X M) : ℝ≥0∞ :=
  (ProbCompRuntime.rom (RandSpec H X M)).evalDist (aggVerifyExperiment C challenge red A) {true}

/-! ## The extractor -/

/-- The extractor's `s` for the item `a`: `α*ₐ + β*ₐ⋅x` with `x = (s - α*)/β*`,
the secret key that `extractForgery` computes, and `x = 0` if `β* = 0`. -/
def extractSig (items : List (AItem n X M)) (s : ZMod n) (zs : List (ZMod n))
    (a : AItem n X M) : ZMod n :=
  let α := isum (fun i b => zs.getD i 0 * (starRep challenge b).1) 0 items
  let β := isum (fun i b => zs.getD i 0 * (starRep challenge b).2) 0 items
  (starRep challenge a).1 + (starRep challenge a).2 * ((s - α) / β)

/-- The extractor succeeds: the aggregate passes `VerifyAggregate` with the
randomizers `zs`, and `(rᵢ, sigsᵢ)` passes BIP340 `Verify` for every item
`(rᵢ, pkᵢ, mᵢ)`. -/
def extractWins (its : List (Item X M)) (s : ZMod n) (zs sigs : List (ZMod n)) : Bool :=
  aggVerifies C challenge its s zs &&
    decide (sigs.length = its.length) &&
    (its.zip sigs).all fun p => BIP340.verify C challenge p.1.2.1 p.1.2.2 (p.1.1, p.2)

/-- **The extractor**: run the forger as `reduction` does, and return its
aggregate `(items, s)`, the randomizers of its verifier and an `s` for every
item. -/
noncomputable def extractor (F : AlgForger n H E X M) (pk : X) :
    OracleComp (unifSpec + SignSpec n X M)
      (List (Item X M) × ZMod n × List (ZMod n) × List (ZMod n)) := do
  let impl := coreImpl (E := E) C challenge pk
    (fun k => liftM (unifSpec.query k))
    tableRO
    (fun msg => liftM ((SignSpec n X M).query msg))
  let ((out, st), table) ← ((simulateQ impl (F.main (initial C ((C.liftX pk).getD 0)))).run
    Core.init).run ∅
  let st := memoize C st (out.value.groups ()) (out.coefficients ())
  let items := annotate C st.memo (toItems C out.value.data.ms (out.value.groups ()))
  let (zs, _) ← (tableZs red items).run table
  return (toItems C out.value.data.ms (out.value.groups ()), out.value.data.s, zs,
    items.map (extractSig challenge items out.value.data.s zs))

/-- The extraction experiment: the extractor runs with a BIP340 key and its
signing oracle. -/
noncomputable def extractExperiment (F : AlgForger n H E X M) : ProbComp Bool := do
  let alg := bip340 (M := M) C challenge ProbComp
  let (pk, sk) ← alg.keygen
  let ((its, s, zs, sigs), _) ← alg.runWithSigningOracle pk sk (extractor C challenge red F pk)
  return extractWins C challenge its s zs sigs

/-- The probability that the extractor succeeds. -/
noncomputable def extractAdvantage (F : AlgForger n H E X M) : ℝ≥0∞ :=
  ProbCompRuntime.probComp.evalDist (extractExperiment C challenge red F) {true}

end Halfagg.Security
