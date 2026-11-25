# halfagg-lean

Machine-checked proofs, in [Lean 4](https://lean-lang.org) with [Mathlib](https://github.com/leanprover-community/mathlib4), about [BIP 458](https://github.com/bitcoin/bips/blob/master/bip-0458.mediawiki): non-interactive half-aggregation of BIP 340 Schnorr signatures.

The model is built on [taproot-lean](https://github.com/dni/taproot-lean), which provides the curve interface, secp256k1 as a Mathlib elliptic curve, the BIP 340 model and SHA-256. Games and random oracles are [VCVio](https://github.com/Verified-zkEVM/VCVio)'s, and algebraic forgers use the interface of zkSecurity's [agm-lean](https://github.com/zksecurity/agm-lean).

[REVIEW.md](REVIEW.md) is the guide for checking the statements: what to read, what the theorems leave out, and which theorem stands behind each claim of BIP 458.

## Results

### The scheme

`Halfagg/Basic.lean`. These hold over any curve that satisfies taproot-lean's interface and for every choice of the challenge and randomizer hash functions.

| Theorem | Statement |
|---|---|
| `verifyAggregate_aggregate`, `verifyAggregate_incAggregate` | Valid BIP 340 signatures give an aggregate that `VerifyAggregate` accepts, whether aggregated at once or added to an aggregate that verifies. |
| `incAggregate_append`, `aggregate_append` | `Aggregate(A ++ B) = IncAggregate(Aggregate(A), A, B)`. |
| `verifyAggregate_single` | A one-signature aggregate verifies exactly when the BIP 340 signature does. |
| `aggregate_accepts_invalid` | An aggregate does not certify the signatures it was made from. Moving `δ ≠ 0` between the `s` values of the first two, weighted by `z₁`, makes the second invalid and leaves the aggregate unchanged. |
| `verifyMulti_eq`, `secp256k1_verifyMulti_eq` | `VerifyAggregate` can be computed as one sum of scalar multiplications, `s⋅G = Σ zᵢ⋅Rᵢ + (zᵢ⋅eᵢ mod n)⋅Pᵢ`, if `n⋅P = 0` for every point. That holds for secp256k1. |
| `secp256k1_primeOrder` | secp256k1 has exactly `n` points, so `n⋅P = 0` for every point (`Halfagg/PrimeOrder.lean`). The proof counts no points: there are at most `2⋅p + 1`, the generator has order `n`, and no point has order two. |

### Security

In `Halfagg/`: `Unforgeability.lean`, `Knowledge.lean`, `Tightness.lean`, `UnforgeabilityROM.lean`, `UnforgeabilityTight.lean` and `Binding.lean`. Except for binding, the forger is algebraic. The randomizer hash is a random oracle, and `q` bounds the forger's randomizer queries. `μ` bounds the probability that one randomizer is a given scalar. For BIP 458's 256-bit hash reduced mod `n` it is `2/2^256` (`Halfagg/Hash256.lean`), and the secp256k1 forms of the theorems use that value.

| Theorem | Statement |
|---|---|
| `halfagg_unforgeable` | Half-aggregation is as secure as BIP 340: Theorem 2 of [Chen and Zhao](https://eprint.iacr.org/2022/222) for BIP 458's scheme, for every challenge hash. An explicit reduction turns a forger of the standard aggregate chosen-key game into a BIP 340 forger and loses at most `(q + 1)·μ`. |
| `grinder_advantage` | The loss is tight up to one query. With a randomizer hash that is uniform in `ZMod n`, where `μ = 1/n`, a forger with `q` randomizer queries and no signing query wins with probability at least `1 - ((n - 1)/n)^q`. |
| `halfagg_knowledge` | Whoever produces a verifying aggregate knows a BIP 340 signature for every item, also under keys it chose itself. If the aggregate verifies with probability `ε`, an extractor outputs all of them with probability at least `ε - (q + 1)·μ`. |
| `reduction_sign_queries`, `extractor_sign_queries` | The reduction and the extractor make no signing query the forger did not make. |
| `game_verifier` | The game's verifier is `verifyAggregate`. |
| `halfagg_unforgeable_rom`, `halfagg_dlog` | The first theorem with the challenge hash as a random oracle too, chained with taproot-lean's proof of BIP 340 into a discrete-log solver. |
| `halfagg_dlog_tight` | A discrete-log solver without forking, so every loss is additive. It is for forgers that send a nonce point in a randomizer request before they ask for a challenge with that nonce (`ExplainsNonces`). |
| `halfagg_key_or_signature` | The same for every forger, up to one term: the probability that a challenge cancels the coefficient of the target key in the forger's explanation of the nonce point. |
| `halfagg_binding` | An aggregate belongs to one list of `(pk, m)` pairs: Theorem 6 of [Chalkias, Garillot, Kondi and Nikolaenko](https://eprint.iacr.org/2021/350) for BIP 458's scheme. With both hashes as random oracles, an adversary with `qC` challenge queries and `qZ` randomizer queries finds an aggregate of at most `ℓ` signatures that verifies for two different lists with probability at most `(qC + 2ℓ)²/n + (qZ + 2ℓ)²·μ`. The bound needs no algebraic group model and no hardness assumption. It needs `n⋅P = 0` for every point. |

For the discrete-log solvers, let `qH` and `qS` bound the forger's challenge queries and signing requests, `ℓ` the length of its forgery, `Q = qH + qS + ℓ + 1` and `ε = Pr[forger wins] - (q + 1)·μ - qS·(qS + Q)·2/(n - 1)`. The solver of `halfagg_dlog` succeeds with probability at least `ε·(ε/(Q + 1) - 1/n)`. Its quadratic loss is the forking lemma in BIP 340's own proof. The solver of `halfagg_dlog_tight` succeeds with probability at least `ε - (qH + 1)/n`.

### Bytes

The theorems above are about x-coordinates and scalars. `Halfagg/Vectors.lean` adds BIP 458's byte encodings, length checks and range checks, and `Halfagg/Encoding.lean` connects them to the model.

| Theorem | Statement |
|---|---|
| `verifyAggregateBytes_eq` | `VerifyAggregate` on bytes is the parsing and the checks, followed by the model's `verifyAggregate`. |
| `decodeVerify_randomizer` | The randomizers of the decoded input hash the bytes of the input. |
| `randomizerInput_injective` | The bytes that a randomizer hashes determine the item list, because every field has 32 bytes. So the model loses nothing by taking the randomizer as a function of the list. |
| `verifyAggregateBytes_aggregateBytes`, `verifyAggregateBytes_incAggregateBytes` | `Aggregate` and `IncAggregate` on bytes are correct: signatures that pass BIP 340 `Verify` give bytes that pass `VerifyAggregate`. |

### Axioms

The theorems use only Lean's standard axioms (`propext`, `Classical.choice`, `Quot.sound`), and `lake build` fails if that changes for a main result (`Halfagg/Summary.lean`). Only the test vector checks depend on compiled evaluation (`native_decide`).

taproot-lean computes `n·G = 0` for secp256k1 with compiled code. `Halfagg/OrderG.lean` proves it from a certificate that the kernel checks: the double-and-add chain for `(n - 1)·G` with the slope and the result of every step. The theorems about secp256k1 are stated for `secp256k1F`, the curve with this proof.

## Proofs

The proofs of the security theorems are under `Halfagg/Proofs/`:

| File | Content |
|---|---|
| `Algebra.lean` | Representations and the extraction (`extract_or_bad`). |
| `Invariant.lean`, `Scheme.lean` | The reduction's bookkeeping stays valid (`core_inv`). |
| `LoggedRun.lean`, `Annotated.lean`, `Trace.lean`, `BadBound.lean` | The annotated experiment, its bad event and the forger's query count. |
| `Transcript.lean`, `Verifier.lean`, `TightBound.lean` | The bad-event bound `(q + 1)·μ` (`annROM_bad`): `q·μ` for the forger's own queries, `μ` for the verifier's draws. |
| `Natural.lean`, `BridgeReduction.lean` | The reduction's BIP 340 game equals the annotated experiment followed by extraction (`red_advantage_eq`). |
| `SignQueries.lean` | The reduction's signing queries (`reduction_sign_bound`). |
| `Projection.lean`, `BridgeGame.lean` | The standard game equals the annotated experiment followed by the win check (`bridge_game`). |
| `Knowledge.lean` | Every extracted signature verifies unless the bad event occurs (`extract_all_or_bad`, `know_bad`). |
| `Secp256k1.lean` | The theorems' curve hypothesis for secp256k1. |
| `Eager.lean` | A lazily sampled oracle on a finite domain is a uniformly sampled table (`rom_eq_table`). |
| `ROM.lean` | Against a fixed challenge table, the oracle reduction is the reduction above (`rom_experiment_eq`). |
| `ROMBounds.lean` | The oracle reduction's hash and signing queries (`reductionROM_bound`). |
| `Tight.lean` | A win is the event of the key machine or of the signature machine (`tight_split_event`), and the key machine under VCVio's signing simulation solves discrete log (`key_fork_le`). |
| `Explained.lean` | For a forger that explains its nonces, the signature machine's event has probability at most `(qH + 1)/n` (`hit_lazy`). |
| `BindingPairs.lean` | For a fixed challenge hash, two lists have the same randomized sum with probability at most `Q²·μ` (`pair_term`). |
| `Binding.lean` | The challenge hash is degenerate on the adversary's output with probability at most `Q²/n` (`chal_lazy`), and the two bounds together (`binding_bound`). |

`Halfagg/Examples.lean` has a concrete forger that satisfies the hypotheses of `halfagg_unforgeable`, and one that satisfies `ExplainsNonces`.

## Test vectors

`Halfagg/Vectors.lean` checks all 53 rows of [`bip-0458/vectors`](https://github.com/bitcoin/bips/tree/master/bip-0458/vectors) against the byte functions: aggregate signatures must match byte for byte, and every expected failure must fail. Verification runs through a double-and-add version that is proven equal to the model.

`Halfagg/VectorData.lean` is generated from the CSV files:

```sh
python3 scripts/gen_vectors.py path/to/bips/bip-0458/vectors > Halfagg/VectorData.lean
```

CI regenerates the file from bitcoin/bips at commit [`a7f9132`](https://github.com/bitcoin/bips/tree/a7f91321f25b5be8d93e901775621c21519e80b7/bip-0458) and fails if it differs.

## Differential testing

No theorem can say that the byte functions are BIP 458's algorithms, so `scripts/fuzz.py` compares them with other implementations. It generates valid and malformed inputs for `Aggregate`, `IncAggregate` and `VerifyAggregate`, takes BIP 458's `halfagg.py` as the reference, and runs the inputs through the Lean model (`scripts/Fuzz.lean`) and optionally through libsecp256k1's `schnorrsig_halfagg` module (`scripts/fuzz_secp256k1.c`).

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

No run has found a mismatch: 10,000 cases against the Lean model and more than 30,000 against libsecp256k1, 3,000 of them under ASan and UBSan. CI runs 300 cases against the Python reference at the pinned bips commit, with a new seed for every run.

`scripts/mutate_secp256k1.py` measures what these tests can see. It applies 21 one-line mutants to the C module, such as dropping a range check or hashing `z₀`, and runs the module's unit tests and the generated cases against each:

```sh
python3 scripts/mutate_secp256k1.py path/to/secp256k1 path/to/bips/bip-0458
```

The unit tests catch 19 mutants and the cases 18, together 20.

- Only the cases catch the mutant without the check `s < n` in `aggverify`. Such a verifier still rejects an `s ≥ n` whose reduction fails the equation. The one input that tells it apart is the empty aggregate with `s = n`, which the generator produces.
- No input can catch the mutant that reduces an `r ≥ p` mod `p`, because nobody can produce a signature whose nonce has an x-coordinate below `2^256 - p`.

## Building

Requirements: [elan](https://github.com/leanprover/elan), which installs the Lean toolchain pinned in `lean-toolchain`.

```sh
lake exe cache get   # download prebuilt Mathlib (several GB)
lake build
```

To repeat what CI runs after the build:

```sh
scripts/check.sh                  # no sorry, no new axioms, native_decide only in the vector checks
scripts/replay.sh                 # replay the project, taproot-lean and agm-lean in the kernel
```

On machines with little memory, use `LEAN_NUM_THREADS=2 lake build`. Do not run `lake update`: it would move the dependencies off their pinned commits.
