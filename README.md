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
| `verifyMulti_eq` | A verifier can compute one sum of scalar multiplications, `s⋅G = Σ zᵢ⋅Rᵢ + (zᵢ⋅eᵢ mod n)⋅Pᵢ`, as BIP 458 suggests. This needs `n⋅P = 0` for every point, which is a hypothesis: it holds for secp256k1, but taproot-lean does not prove that the curve has `n` points. |

## Unforgeability

`halfagg_unforgeable` (`Halfagg/Unforgeability.lean`) proves that half-aggregation is as secure as BIP 340: Theorem 2 of [Chen and Zhao](https://eprint.iacr.org/2022/222) for BIP 458's scheme, in the algebraic group model with the randomizer hash as a random oracle and for every challenge hash. The game is the standard aggregate chosen-key game, and `game_verifier` proves that its verifier is `verifyAggregate`. Algebraic forgers use the interface of zkSecurity's [agm-lean](https://github.com/zksecurity/agm-lean). An explicit reduction turns a forger into a BIP 340 forger, losing at most `(q + 1)/n` for `q` randomizer queries, the bound of Chen and Zhao. `reduction_sign_queries` proves that the reduction asks for no signature the forger did not ask for. `secp256k1_halfagg_unforgeable` is the same statement for secp256k1.

To review the result, read `Halfagg/Security.lean` (the game, the forger model, the reduction, and a header listing the modelling choices and limitations) and the theorem statements in `Halfagg/Unforgeability.lean`. [REVIEW.md](REVIEW.md) is a guide for that. The proofs are under `Halfagg/Proofs/`:

| File | Content |
|---|---|
| `Algebra.lean` | Representations and the extraction (`extract_or_bad`). |
| `Invariant.lean`, `Scheme.lean` | The reduction's bookkeeping stays valid (`core_inv`). |
| `LoggedRun.lean`, `Annotated.lean`, `Trace.lean`, `BadBound.lean` | The annotated experiment, its bad event and the forger's query count. |
| `Transcript.lean`, `Verifier.lean`, `TightBound.lean` | The bad-event bound `(q + 1)/n` (`annROM_bad`): `q/n` for the forger's own queries, `1/n` for the verifier's draws. |
| `Natural.lean`, `BridgeReduction.lean` | The reduction's BIP 340 game equals the annotated experiment followed by extraction (`red_advantage_eq`). |
| `SignQueries.lean` | The reduction's signing queries (`reduction_sign_bound`). |
| `Projection.lean`, `BridgeGame.lean` | The standard game equals the annotated experiment followed by the win check (`bridge_game`). |
| `Secp256k1.lean` | The theorem's curve hypothesis for secp256k1. |
| `Eager.lean` | A lazily sampled oracle on a finite domain is a uniformly sampled table (`rom_eq_table`). |
| `ROM.lean` | Against a fixed challenge table, the oracle reduction is the reduction above (`rom_experiment_eq`). |
| `ROMBounds.lean` | The oracle reduction's hash and signing queries (`reductionROM_bound`). |

`Halfagg/Examples.lean` shows the theorem is not vacuous: a concrete algebraic forger satisfying its hypotheses, and an honest signature satisfying the game's win predicate.

The statement is a reduction. It does not bound the forger's or the reduction's running time.

`halfagg_unforgeable` uses only Lean's standard axioms. The secp256k1 version also inherits taproot-lean's `native_decide` computation of `n·G = 0`.

`halfagg_unforgeable_rom` (`Halfagg/UnforgeabilityROM.lean`) is the same theorem with the challenge hash as a random oracle that the forger and the reduction can only query. Its BIP 340 game is the one of taproot-lean's `euf_cma`, so the two results chain. `halfagg_dlog` turns a forger into a discrete-log solver: with `Q = qH + qS + ℓ + 1` (`ℓ` bounds the forgery's length) and `ε = Pr[forger wins] - (q + 1)/n - qS·(qS + Q)·2/(n - 1)`, the solver succeeds with probability at least `ε·(ε/(Q + 1) - 1/n)`. The quadratic loss is the forking lemma in BIP 340's own proof. The definitions are in `Halfagg/SecurityROM.lean`. This version needs a finite message type and samples the challenge table up front.

`grinder_advantage` (`Halfagg/Tightness.lean`) shows the bound is tight up to one query: a forger with `q` randomizer queries and no signing queries wins with probability at least `1 - ((n - 1)/n)^q`, which is about `q/n`.

A forger may also hash raw x-only encodings after an item that fails `lift_x`. No list with such an item verifies (`aggWins_lifts`), so the forger does not have to explain them.

## Test vectors

`Halfagg/Vectors.lean` adds BIP 458's byte encodings, length checks and range checks, and checks all 53 rows of [`bip-0458/vectors`](https://github.com/bitcoin/bips/tree/master/bip-0458/vectors) against the model: aggregate signatures must match byte for byte, and every expected failure must fail. Verification runs through a double-and-add version that is proven equal to the model. The checks use compiled evaluation (`native_decide`), and no theorem in `Halfagg/Basic.lean` depends on them.

`Halfagg/VectorData.lean` is generated from the CSV files:

```sh
python3 scripts/gen_vectors.py path/to/bips/bip-0458/vectors > Halfagg/VectorData.lean
```

CI regenerates the file from bitcoin/bips at commit [`a7f9132`](https://github.com/bitcoin/bips/tree/a7f91321f25b5be8d93e901775621c21519e80b7/bip-0458) and fails if it differs.

## Differential testing

No theorem can say that the byte layer is BIP 458's algorithm, so `scripts/fuzz.py` compares it with other implementations. It generates valid and malformed inputs for `Aggregate`, `IncAggregate` and `VerifyAggregate`, takes BIP 458's `halfagg.py` as the reference, and runs the same inputs through the Lean model (`scripts/Fuzz.lean`) and optionally through libsecp256k1's `schnorrsig_halfagg` module (`scripts/fuzz_secp256k1.c`).

```sh
python3 scripts/fuzz.py path/to/bips/bip-0458 --cases 2500 --seed 1
```

For libsecp256k1, build the library with the module and compile the driver:

```sh
cmake -S path/to/secp256k1 -B build -DBUILD_SHARED_LIBS=OFF \
  -DSECP256K1_EXPERIMENTAL=ON -DSECP256K1_ENABLE_MODULE_SCHNORRSIG_HALFAGG=ON
cmake --build build
cc -O2 -Ipath/to/secp256k1/include scripts/fuzz_secp256k1.c build/lib/libsecp256k1.a -o fuzz_secp256k1
python3 scripts/fuzz.py path/to/bips/bip-0458 --no-lean --secp256k1 ./fuzz_secp256k1 --cases 10000
```

The C API cannot express every malformed input, such as a public key of the wrong length. The driver skips those cases, about one in five.

`scripts/mutate_secp256k1.py` measures what these tests can see. It applies 21 one-line mutants to the module, such as dropping a range check or hashing `z₀`, and runs the module's unit tests and the generated cases against each:

```sh
python3 scripts/mutate_secp256k1.py path/to/secp256k1 path/to/bips/bip-0458
```

The unit tests catch 19 mutants and the cases 18, together 20. The one that only the cases catch drops the check `s < n` from `aggverify`. Such a verifier still rejects an `s ≥ n` whose reduction fails the equation, so the only input that tells it apart is the empty aggregate with `s = n`, which the generator produces. The remaining mutant reduces an `r ≥ p` mod `p`. No input can catch it, because nobody can produce a signature whose nonce has an x-coordinate below `2^256 - p`.

Runs so far found no mismatch: 10,000 cases against the Lean model (seeds 1 to 4) and 30,000 against libsecp256k1 (seeds 21 to 23), of which about 24,000 were compared. CI runs 300 cases against the Python reference of the same bips commit.

## Modelling choices and trust base

- Public keys and nonces `r` are x-coordinates, `s` values are elements of `ZMod n`, and the range checks `s < n` are part of the type. Byte encodings and the checks on them are in `Halfagg/Vectors.lean`. `verifyAggregateBytes_eq` (`Halfagg/Encoding.lean`) proves that `VerifyAggregate` on bytes is this parsing followed by the model's `verifyAggregate`, and `decodeVerify_randomizer` that its randomizers hash the bytes of the input. `verifyAggregateBytes_aggregateBytes` and `verifyAggregateBytes_incAggregateBytes` prove that `Aggregate` and `IncAggregate` on bytes are correct.
- The tagged hashes are arbitrary functions. The randomizer is a function of the list `[(r₀, pk₀, m₀), …, (rᵢ, pkᵢ, mᵢ)]`. BIP 458 fixes public keys, messages and nonces at 32 bytes, so the byte encoding it hashes is injective (`randomizerInput_injective`) and this loses nothing.
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
scripts/replay.sh                 # replay every project module in the kernel, one process per module
```

The build also compiles the parts of taproot-lean it needs. On machines with little memory, use `LEAN_NUM_THREADS=2 lake build`. Do not run `lake update`: it would move the dependencies off their pinned commits.
