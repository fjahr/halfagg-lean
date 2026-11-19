import Halfagg.Basic
import Halfagg.Vectors
import Halfagg.Encoding
import Halfagg.Unforgeability
import Halfagg.Knowledge
import Halfagg.Examples
import Halfagg.Tightness
import Halfagg.UnforgeabilityROM
import Halfagg.UnforgeabilityTight

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

/-- info: 'Halfagg.verifyMulti_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Halfagg.verifyMulti_eq

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

/-! ## Byte encodings -/

/-- info: 'Halfagg.Vectors.randomizerInput_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Halfagg.Vectors.randomizerInput_injective

/-- info: 'Halfagg.Vectors.randomizerF_input_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Halfagg.Vectors.randomizerF_input_injective

/--
info: 'Halfagg.Vectors.verifyAggregateBytes_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Taproot.Secp256k1.n_smul_G._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms Halfagg.Vectors.verifyAggregateBytes_eq

/-- info: 'Halfagg.Vectors.decodeVerify_randomizer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Halfagg.Vectors.decodeVerify_randomizer

/-- info: 'Halfagg.Vectors.decodeVerify_pm_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Halfagg.Vectors.decodeVerify_pm_injective

/--
info: 'Halfagg.Vectors.verifyAggregateBytes_incAggregateBytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Taproot.Secp256k1.n_smul_G._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms Halfagg.Vectors.verifyAggregateBytes_incAggregateBytes

/--
info: 'Halfagg.Vectors.verifyAggregateBytes_aggregateBytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Taproot.Secp256k1.n_smul_G._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms Halfagg.Vectors.verifyAggregateBytes_aggregateBytes

/--
info: 'Halfagg.Vectors.incAggregateBytes_isSome' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Taproot.Secp256k1.n_smul_G._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms Halfagg.Vectors.incAggregateBytes_isSome

/--
info: 'Halfagg.Vectors.aggregateBytes_isSome' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Taproot.Secp256k1.n_smul_G._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms Halfagg.Vectors.aggregateBytes_isSome

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

/-- info: 'Halfagg.Security.game_verifier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Halfagg.Security.game_verifier

/-- info: 'Halfagg.Security.halfagg_knowledge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Halfagg.Security.halfagg_knowledge

/-- info: 'Halfagg.Security.extractor_sign_queries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Halfagg.Security.extractor_sign_queries

/-- info: 'Halfagg.Security.halfagg_unforgeable_rom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Halfagg.Security.halfagg_unforgeable_rom

/-- info: 'Halfagg.Security.halfagg_dlog' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Halfagg.Security.halfagg_dlog

/-- info: 'Halfagg.Security.halfagg_key_or_signature' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Halfagg.Security.halfagg_key_or_signature

/-- info: 'Halfagg.Security.halfagg_dlog_tight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Halfagg.Security.halfagg_dlog_tight

/-- info: 'Halfagg.Security.grinder_advantage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Halfagg.Security.grinder_advantage

/-- info: 'Halfagg.Security.reductionROM_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Halfagg.Security.reductionROM_bound

/-- info: 'Halfagg.LoggedRun.rom_eq_table' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Halfagg.LoggedRun.rom_eq_table

/-- info: 'Halfagg.Security.grinder_sandwich' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Halfagg.Security.grinder_sandwich

/-- info: 'Halfagg.Security.grinder_reduction_no_sign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Halfagg.Security.grinder_reduction_no_sign

/-- info: 'Halfagg.Examples.demo_theorem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Halfagg.Examples.demo_theorem

/-- info: 'Halfagg.Examples.aggWins_honest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Halfagg.Examples.aggWins_honest

/--
info: 'Halfagg.Security.secp256k1_halfagg_unforgeable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Taproot.Secp256k1.n_smul_G._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms Halfagg.Security.secp256k1_halfagg_unforgeable

/--
info: 'Halfagg.Security.secp256k1_halfagg_dlog' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Taproot.Secp256k1.n_smul_G._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms Halfagg.Security.secp256k1_halfagg_dlog

/--
info: 'Halfagg.Security.secp256k1_halfagg_dlog_tight' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Taproot.Secp256k1.n_smul_G._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms Halfagg.Security.secp256k1_halfagg_dlog_tight
