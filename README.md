# halfagg-lean

Machine-checked proofs, in [Lean 4](https://lean-lang.org) with [Mathlib](https://github.com/leanprover-community/mathlib4), about [BIP 458](https://github.com/bitcoin/bips/blob/master/bip-0458.mediawiki): non-interactive half-aggregation of BIP 340 Schnorr signatures.

The model is built on [taproot-lean](https://github.com/dni/taproot-lean), which provides the curve interface, secp256k1 as a Mathlib elliptic curve, the BIP 340 model and the SHA-256 implementation used for the test vectors.

## Results

Every result in `Halfagg/Basic.lean` holds over any curve satisfying taproot-lean's interface (secp256k1 included) and for **every** choice of the challenge and randomizer hash functions.

| Theorem | Statement |
|---|---|
| `verifyAggregate_aggregate` | Aggregating valid BIP 340 signatures with `Aggregate` gives an aggregate signature that `VerifyAggregate` accepts. |
| `verifyAggregate_incAggregate` | Adding valid signatures to an aggregate that verifies, with `IncAggregate`, gives an aggregate that verifies. |
| `verifyAggregate_single` | With `z₀ = 1`, `VerifyAggregate(r ‖ bytes(s), [(pk, m)])` accepts exactly when BIP 340 `Verify(pk, m, (r, s))` does. |
| `incAggregate_append`, `aggregate_append` | Incremental aggregation agrees with aggregating at once: `Aggregate(A ++ B) = IncAggregate(Aggregate(A), A, B)`. |
| `aggregate_accepts_invalid` | The aggregate does not certify the individual signatures (BIP 458's remark after `Aggregate`): moving `δ ≠ 0` between the `s` values of the first two signatures, weighted by `z₁`, makes the second signature invalid but leaves the aggregate unchanged. |

## Unforgeability

`halfagg_unforgeable` (`Halfagg/Unforgeability.lean`) proves that half-aggregation is as secure as BIP 340: Theorem 2 of [Chen and Zhao](https://eprint.iacr.org/2022/222) for BIP 458's scheme, in the algebraic group model with the randomizer hash as a random oracle and for every challenge hash. The game is the standard aggregate chosen-key game. Algebraic forgers use the interface of zkSecurity's [agm-lean](https://github.com/zksecurity/agm-lean). An explicit reduction turns a forger into a BIP 340 forger, losing at most `(q + ℓ)/n` for `q` randomizer queries and `ℓ` entries. `reduction_sign_queries` proves that the reduction asks for no signature the forger did not ask for. `secp256k1_halfagg_unforgeable` is the same statement for secp256k1.

To review the result, read `Halfagg/Security.lean` (the game, the forger model, the reduction, and a header listing the modelling choices and limitations) and the theorem statements in `Halfagg/Unforgeability.lean`. [REVIEW.md](REVIEW.md) is a guide for that. The proofs are under `Halfagg/Proofs/`:

| File | Content |
|---|---|
| `Algebra.lean` | Representations and the extraction (`extract_or_bad`). |
| `Invariant.lean`, `Scheme.lean` | The reduction's bookkeeping stays valid (`core_inv`). |
| `LoggedRun.lean`, `Annotated.lean`, `Trace.lean`, `BadBound.lean` | The annotated experiment and the bad-event bound `(q + ℓ)/n` (`ann_bad_bound`). |
| `Natural.lean`, `BridgeReduction.lean` | The reduction's BIP 340 game equals the annotated experiment followed by extraction (`red_advantage_eq`). |
| `SignQueries.lean` | The reduction's signing queries (`reduction_sign_bound`). |
| `Projection.lean`, `BridgeGame.lean` | The standard game equals the annotated experiment followed by the win check (`bridge_game`). |
| `Secp256k1.lean` | The theorem's curve hypothesis for secp256k1. |

`Halfagg/Examples.lean` shows the theorem is not vacuous: a concrete algebraic forger satisfying its hypotheses, and an honest signature satisfying the game's win predicate.

The statement is a reduction. It does not bound the forger's or the reduction's running time.

`halfagg_unforgeable` uses only Lean's standard axioms. The secp256k1 version also inherits taproot-lean's `native_decide` computation of `n·G = 0`.

`grinder_advantage` (`Halfagg/Tightness.lean`) shows the bound is tight in `q`: a forger with `q` randomizer queries and no signing queries wins with probability at least `1 - ((n - 1)/n)^q`, which is about `q/n`.

A forger may also hash raw x-only encodings after an item that fails `lift_x`. No list with such an item verifies (`aggWins_lifts`), so the forger does not have to explain them.

## Test vectors

`Halfagg/Vectors.lean` adds BIP 458's byte encodings, length checks and range checks, and checks all 53 rows of [`bip-0458/vectors`](https://github.com/bitcoin/bips/tree/master/bip-0458/vectors) against the model: aggregate signatures must match byte for byte, and every expected failure must fail. Verification runs through a double-and-add version that is proven equal to the model. The checks use compiled evaluation (`native_decide`), and no theorem in `Halfagg/Basic.lean` depends on them.

`Halfagg/VectorData.lean` is generated from the CSV files:

```sh
python3 scripts/gen_vectors.py path/to/bips/bip-0458/vectors > Halfagg/VectorData.lean
```

## Modelling choices and trust base

- Public keys and nonces `r` are x-coordinates, `s` values are elements of `ZMod n`, and the range checks `s < n` are part of the type. Byte encodings and the checks on them are in `Halfagg/Vectors.lean`.
- The tagged hashes are arbitrary functions. The randomizer is a function of the list `[(r₀, pk₀, m₀), …, (rᵢ, pkᵢ, mᵢ)]`. BIP 458 fixes public keys, messages and nonces at 32 bytes, so the byte encoding it hashes is injective and this loses nothing.
- `lake build` fails if the axioms of a main result change (`Halfagg/Summary.lean`). The theorems in `Halfagg/Basic.lean` use only Lean's standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

## Building

Requirements: [elan](https://github.com/leanprover/elan), which installs the Lean toolchain pinned in `lean-toolchain`.

```sh
lake exe cache get   # download prebuilt Mathlib (several GB)
lake build
```

To repeat what CI runs after the build:

```sh
scripts/check.sh                  # no sorry, no new axioms, native_decide only in the vector checks
lake env leanchecker Halfagg      # replay every project module in the kernel
```

The build also compiles the parts of taproot-lean it needs. On machines with little memory, use `LEAN_NUM_THREADS=2 lake build`. Do not run `lake update`: it would move the dependencies off their pinned commits.
