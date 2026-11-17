import Halfagg.Basic
import Halfagg.Vectors
import Halfagg.Unforgeability
import Halfagg.Tightness

/-!
# Main results and their axioms

Each check below fails the build if the axioms of a main result change. The
theorems must depend only on Lean's standard axioms (`propext`,
`Classical.choice`, `Quot.sound`); a `sorry` would show up as `sorryAx`. The
test vector checks also depend on one `native_decide` axiom each (compiled
evaluation), and the secp256k1 results inherit taproot-lean's `native_decide`
computation of `n·G = 0`.
-/

set_option linter.style.longLine false

/-! ## Correctness, for every choice of the hash functions -/

/-- info: 'Halfagg.verifyAggregate_aggregate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Halfagg.verifyAggregate_aggregate

/-- info: 'Halfagg.verifyAggregate_incAggregate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Halfagg.verifyAggregate_incAggregate

/-- info: 'Halfagg.verifyAggregate_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Halfagg.verifyAggregate_single

/-- info: 'Halfagg.incAggregate_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Halfagg.incAggregate_append

/-- info: 'Halfagg.aggregate_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Halfagg.aggregate_append

/-- info: 'Halfagg.aggregate_accepts_invalid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Halfagg.aggregate_accepts_invalid

/-! ## Test vectors (compiled evaluation) -/

/--
info: 'Halfagg.Vectors.aggregate_vectors' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Halfagg.Vectors.aggregate_vectors._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms Halfagg.Vectors.aggregate_vectors

/--
info: 'Halfagg.Vectors.incAggregate_vectors' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Halfagg.Vectors.incAggregate_vectors._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms Halfagg.Vectors.incAggregate_vectors

/--
info: 'Halfagg.Vectors.verifyAggregate_vectors' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Halfagg.Vectors.verifyAggregate_vectors._native.native_decide.ax_1_2,
 Taproot.Secp256k1.n_smul_G._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms Halfagg.Vectors.verifyAggregate_vectors

/-! ## Unforgeability -/

/-- info: 'Halfagg.Security.halfagg_unforgeable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Halfagg.Security.halfagg_unforgeable

/-- info: 'Halfagg.Security.reduction_sign_queries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Halfagg.Security.reduction_sign_queries

/-- info: 'Halfagg.Security.aggWins_lifts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Halfagg.Security.aggWins_lifts

/-- info: 'Halfagg.Security.grinder_advantage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Halfagg.Security.grinder_advantage

/--
info: 'Halfagg.Security.secp256k1_halfagg_unforgeable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Taproot.Secp256k1.n_smul_G._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms Halfagg.Security.secp256k1_halfagg_unforgeable
