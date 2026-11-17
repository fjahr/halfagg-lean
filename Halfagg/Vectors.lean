import Halfagg.Basic
import Halfagg.VectorData
import Taproot.BIP340Vectors

/-!
# BIP458 on bytes, and the official test vectors

`aggregateBytes`, `incAggregateBytes` and `verifyAggregateBytes` add BIP458's
byte encodings, length checks and range checks to the model in
`Halfagg.Basic`, on secp256k1 with SHA-256 tagged hashes (from
`Taproot.BIP340Vectors`). As in the reference implementation, every failure
(`ValueError` in Python) is `none` or `false`.

Verification runs through `verifyAggregateFast`, which uses double-and-add and
fast square roots and is proven equal to the model. The test vectors are
checked with `native_decide`, so they rely on compiled code; no theorem in
`Halfagg.Basic` depends on them.
-/

namespace Halfagg.Vectors

open Taproot Taproot.Secp256k1 Taproot.BIP340 Taproot.BIP340Vectors

/-- `int(hash_BIP0458/randomizer(r₀ ‖ pk₀ ‖ m₀ ‖ … ‖ rᵢ ‖ pkᵢ ‖ mᵢ)) mod n`. -/
def randomizer (its : List (Item Bytes Bytes)) : ZMod n :=
  (toNatBE (taggedHash "BIP0458/randomizer" (its.flatMap fun it => it.1 ++ it.2.1 ++ it.2.2)) :
    ZMod n)

/-- The randomizer for nonces and public keys given as field elements, hashed
as `bytes(x)`. -/
def randomizerF (its : List (Item F Bytes)) : ZMod n :=
  randomizer (its.map fun it => (bytes32 it.1.val, bytes32 it.2.1.val, it.2.2))

/-- `[b[0:32], b[32:64], …]`: the first `v` 32-byte chunks of `b`. -/
def chunks32 (b : Bytes) (v : ℕ) : List Bytes :=
  (List.range v).map fun i => (b.drop (32 * i)).take 32

def is32 (b : Bytes) : Bool := b.length == 32

/-- BIP458 `IncAggregate(aggsig, pm_aggd, pms_to_agg)` on bytes. -/
def incAggregateBytes (aggsig : Bytes) (pmAggd : List (Bytes × Bytes))
    (pms : List (Bytes × Bytes × Bytes)) : Option Bytes :=
  let v := pmAggd.length
  let sAgg := toNatBE (aggsig.drop (32 * v))
  let ok := aggsig.length == 32 * (v + 1) &&
    pmAggd.all (fun x => is32 x.1 && is32 x.2) &&
    pms.all (fun x => is32 x.1 && is32 x.2.1 && x.2.2.length == 64 &&
      decide (toNatBE (x.2.2.drop 32) < n)) &&
    decide (sAgg < n)
  if ok then
    let entries : List (Entry n Bytes Bytes) :=
      pms.map fun x => ⟨x.1, x.2.1, x.2.2.take 32, (toNatBE (x.2.2.drop 32) : ZMod n)⟩
    (incAggregate randomizer ⟨chunks32 aggsig v, (sAgg : ZMod n)⟩ pmAggd entries).map
      fun agg => agg.rs.flatten ++ bytes32 agg.s.val
  else none

/-- BIP458 `Aggregate(pms)` on bytes: `IncAggregate(bytes(0), [], pms)`. -/
def aggregateBytes (pms : List (Bytes × Bytes × Bytes)) : Option Bytes :=
  incAggregateBytes (bytes32 0) [] pms

/-- BIP458 `VerifyAggregate(aggsig, pm_aggd)` on bytes. `lift_x` fails for
`x ≥ p`, so those inputs are rejected before converting to field elements. -/
def verifyAggregateBytes (aggsig : Bytes) (pm : List (Bytes × Bytes)) : Bool :=
  let u := pm.length
  let rs := chunks32 aggsig u
  let s := toNatBE (aggsig.drop (32 * u))
  aggsig.length == 32 * (u + 1) && pm.all (fun x => is32 x.1 && is32 x.2) &&
    pm.all (fun x => decide (toNatBE x.1 < p)) && rs.all (fun r => decide (toNatBE r < p)) &&
    decide (s < n) &&
    verifyAggregate secp256k1 challenge randomizerF ⟨rs.map fun r => (toNatBE r : F), (s : ZMod n)⟩
      (pm.map fun x => ((toNatBE x.1 : F), x.2))

/-! ## Fast evaluation, proven equal -/

def termFast (it : Item F Bytes) : Point :=
  (liftXFast it.1).getD 0 + smulDA (challenge it.1 it.2.1 it.2.2).val ((liftXFast it.2.1).getD 0)

def liftsFast (it : Item F Bytes) : Bool := (liftXFast it.1).isSome && (liftXFast it.2.1).isSome

theorem liftsFast_eq : liftsFast = lifts secp256k1 := by
  funext it
  simp only [liftsFast, lifts, liftXFast_eq, secp256k1_liftX]

def verifyAggregateFast (agg : AggSig n F) (pm : List (F × Bytes)) : Bool :=
  let its := items pm agg.rs
  decide (agg.rs.length = pm.length) && its.all liftsFast &&
    decide (mulGFast agg.s =
      isum (fun i it => smulDA (z randomizerF its i).val (termFast it)) 0 its)

theorem verifyAggregateFast_eq (agg : AggSig n F) (pm : List (F × Bytes)) :
    verifyAggregateFast agg pm = verifyAggregate secp256k1 challenge randomizerF agg pm := by
  simp only [verifyAggregateFast, verifyAggregate, verifyWith, termFast, term, liftsFast_eq,
    liftXFast_eq, secp256k1_liftX, mulGFast_eq, smulDA_eq]

def verifyAggregateBytesFast (aggsig : Bytes) (pm : List (Bytes × Bytes)) : Bool :=
  let u := pm.length
  let rs := chunks32 aggsig u
  let s := toNatBE (aggsig.drop (32 * u))
  aggsig.length == 32 * (u + 1) && pm.all (fun x => is32 x.1 && is32 x.2) &&
    pm.all (fun x => decide (toNatBE x.1 < p)) && rs.all (fun r => decide (toNatBE r < p)) &&
    decide (s < n) &&
    verifyAggregateFast ⟨rs.map fun r => (toNatBE r : F), (s : ZMod n)⟩
      (pm.map fun x => ((toNatBE x.1 : F), x.2))

theorem verifyAggregateBytesFast_eq (aggsig : Bytes) (pm : List (Bytes × Bytes)) :
    verifyAggregateBytesFast aggsig pm = verifyAggregateBytes aggsig pm := by
  simp only [verifyAggregateBytesFast, verifyAggregateBytes, verifyAggregateFast_eq]

/-! ## The official test vectors

The vectors are evaluated by compiled code (`native_decide`), as in
`Taproot.BIP340Vectors`. They test the model against the reference
implementation; no theorem in `Halfagg.Basic` depends on them. -/

set_option linter.style.native false

/-- The `(pk, m, sig)` triples of a row, paired up like the reference runner
(which uses Python's `zip`). -/
def pmsOf (pks msgs sigs : List String) : List (Bytes × Bytes × Bytes) :=
  (pks.map hex).zip ((msgs.map hex).zip (sigs.map hex))

def pmOf (pks msgs : List String) : List (Bytes × Bytes) :=
  (pks.map hex).zip (msgs.map hex)

/-- Every `Aggregate` vector gives the expected aggregate signature, or fails
where it should. -/
theorem aggregate_vectors :
    aggregateVectors.all (fun v =>
      aggregateBytes (pmsOf v.pubkeys v.messages v.signatures) == v.expected.map hex) = true := by
  native_decide

/-- Every `IncAggregate` vector gives the expected aggregate signature, or
fails where it should. -/
theorem incAggregate_vectors :
    incAggregateVectors.all (fun v =>
      incAggregateBytes (hex v.aggsig) (pmOf v.pmPubkeys v.pmMessages)
        (pmsOf v.pubkeys v.messages v.signatures) == v.expected.map hex) = true := by
  native_decide

/-- Every `VerifyAggregate` vector gives the expected result. -/
theorem verifyAggregate_vectors :
    verifyVectors.all (fun v =>
      verifyAggregateBytes (hex v.aggsig) (pmOf v.pubkeys v.messages) == v.expected) = true := by
  simp only [← verifyAggregateBytesFast_eq]
  native_decide

end Halfagg.Vectors
