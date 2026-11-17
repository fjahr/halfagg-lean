import Halfagg.Basic
import Halfagg.Vectors
import Halfagg.Unforgeability

/-!
# Main results and their axioms

`lake build` prints the axioms every main result depends on. The theorems in
`Halfagg.Basic` must show only Lean's standard axioms
(`propext`, `Classical.choice`, `Quot.sound`). Any `sorry` would show up as
`sorryAx`. The test vector checks additionally show one `native_decide`
axiom each (compiled evaluation), and the `VerifyAggregate` check also
inherits taproot-lean's `native_decide` computation of `n·G = 0`.
-/

-- Correctness, for every choice of the hash functions
#print axioms Halfagg.verifyAggregate_aggregate
#print axioms Halfagg.verifyAggregate_incAggregate
#print axioms Halfagg.verifyAggregate_single
#print axioms Halfagg.incAggregate_append
#print axioms Halfagg.aggregate_append
#print axioms Halfagg.aggregate_accepts_invalid

-- Test vectors (compiled evaluation)
#print axioms Halfagg.Vectors.aggregate_vectors
#print axioms Halfagg.Vectors.incAggregate_vectors
#print axioms Halfagg.Vectors.verifyAggregate_vectors

-- Unforgeability. Must show only the standard axioms; the secp256k1 version also
-- shows taproot-lean's `native_decide` computation of `n·G = 0`.
#print axioms Halfagg.Security.halfagg_unforgeable
#print axioms Halfagg.Security.ann_bad_bound
#print axioms Halfagg.Security.secp256k1_halfagg_unforgeable
