# halfagg-lean

Machine-checked proofs, in [Lean 4](https://lean-lang.org) with [Mathlib](https://github.com/leanprover-community/mathlib4), about [BIP 458](https://github.com/bitcoin/bips/blob/master/bip-0458.mediawiki): non-interactive half-aggregation of BIP 340 Schnorr signatures.

The model is built on [taproot-lean](https://github.com/dni/taproot-lean), which provides the curve interface, secp256k1 as a Mathlib elliptic curve, the BIP 340 model and SHA-256. Games and random oracles are [VCVio](https://github.com/Verified-zkEVM/VCVio)'s, and algebraic forgers use the interface of zkSecurity's [agm-lean](https://github.com/zksecurity/agm-lean).

[REVIEW.md](REVIEW.md) is the guide for checking the statements: what to read, what the theorems leave out, which theorem stands behind each claim of BIP 458, and how the statements compare with those of the papers it cites. [FINDINGS.md](FINDINGS.md) lists what the work found in the BIP, its test vectors and the C module.

## Results

### Main results

One result for every property, in `Halfagg/Basic.lean`, `Unforgeability.lean`, `Knowledge.lean`, `UnforgeabilityTight.lean` and `Binding.lean`. Each holds for any curve that satisfies taproot-lean's interface. [REVIEW.md](REVIEW.md#the-main-results) prints their statements and lists, for each, the definitions that a reader has to agree with.

| Theorem | Statement |
|---|---|
| `verifyAggregate_aggregate`, `verifyAggregate_incAggregate` | Correctness, for every choice of the challenge and randomizer hash functions. Valid BIP 340 signatures give an aggregate that `VerifyAggregate` accepts, whether aggregated at once or added to an aggregate that verifies. |
| `halfagg_unforgeable` | Half-aggregation is as secure as BIP 340: Theorem 2 of [Chen and Zhao](https://eprint.iacr.org/2022/222) for BIP 458's scheme, for every challenge hash. An explicit reduction turns a forger of the standard aggregate chosen-key game into a BIP 340 forger and loses at most `(q + 1)·μ`. |
| `halfagg_knowledge` | Whoever produces a verifying aggregate knows a BIP 340 signature for every item, also under keys it chose itself. If the aggregate verifies with probability `ε`, an extractor outputs all of them with probability at least `ε - (q + 1)·μ`. |
| `halfagg_dlog_tight` | A discrete-log solver without forking, so every loss is additive. The challenge hash is a random oracle too. It is for forgers that send a nonce point in a randomizer request before they ask for a challenge with that nonce (`ExplainsNonces`). |
| `halfagg_binding` | An aggregate belongs to one list of `(pk, m)` pairs: Theorem 6 of [Chalkias, Garillot, Kondi and Nikolaenko](https://eprint.iacr.org/2021/350) for BIP 458's scheme. With both hashes as random oracles, an adversary with `qC` challenge queries and `qZ` randomizer queries finds an aggregate of at most `ℓ` signatures that verifies for two different lists with probability at most `(qC + 2ℓ)²/n + (qZ + 2ℓ)²·μ`. The bound needs no algebraic group model and no hardness assumption. It needs `n⋅P = 0` for every point. |

Except for binding, the forger is algebraic. The randomizer hash is a random oracle, and `q` bounds the forger's randomizer queries. `μ` bounds the probability that one randomizer is a given scalar. For BIP 458's 256-bit hash reduced mod `n` it is `2/2^256` (`Halfagg/Hash256.lean`).

`halfagg_unforgeable`, `halfagg_knowledge` and `grinder_advantage` hold for every way the signer derives a nonce from its key and the message (`NonceGen`), so also for BIP 340's hashed nonces. The BIP 340 game of the reduction has the same signer. The theorems with the challenge hash as a random oracle are for uniform nonces, as taproot-lean's proof of BIP 340 is.

### The main results in other forms

The same theorems for other models of the challenge hash, for secp256k1 and for bytes. The main results are about x-coordinates and scalars. `Halfagg/Vectors.lean` adds BIP 458's byte encodings, length checks and range checks, and `Halfagg/Encoding.lean` connects them to the model.

| Theorem | Statement |
|---|---|
| `halfagg_unforgeable_rom`, `halfagg_dlog` | `halfagg_unforgeable` with the challenge hash as a random oracle too, chained with taproot-lean's proof of BIP 340 into a discrete-log solver. Its loss is quadratic, which is the forking lemma in BIP 340's own proof. |
| `halfagg_key_or_signature` | `halfagg_dlog_tight` for every algebraic forger, up to one term: the probability that a challenge cancels the coefficient of the target key in the forger's explanation of the nonce point. |
| `halfagg_hashed_le`, `halfagg_dlog_hashed`, `halfagg_dlog_tight_hashed`, `halfagg_binding_hashed` | The challenge hash as BIP 340 computes it (`Halfagg/SecurityHashed.lean`). The oracle returns a hash output, the adversary sees it, and the game reduces it mod `n`. The game reads at most `qH + qS + ℓ` hash outputs, in the binding game `qC + 2ℓ`, and each costs `δ`, the probability that a uniform hash output is not the one chosen for its scalar. For a 256-bit hash and secp256k1, `δ ≤ 2^-127` (`secp256k1_repBound`). The solvers are those of the theorems above, for the forger that turns scalar answers into hash outputs (`viaRep`). |
| `secp256k1_halfagg_unforgeable`, `secp256k1_halfagg_knowledge`, `secp256k1_halfagg_dlog`, `secp256k1_halfagg_dlog_tight`, `secp256k1_halfagg_binding`, `secp256k1_halfagg_dlog_256`, `secp256k1_halfagg_dlog_tight_256`, `secp256k1_halfagg_binding_256` | The theorems for secp256k1 and BIP 458's randomizer hash, a 256-bit value reduced mod `n`, so `μ = 2/2^256`. The last three have the challenge hash with 256-bit outputs. |
| `bytes_halfagg_unforgeable`, `bytes_halfagg_knowledge`, `bytes_halfagg_dlog_tight`, `bytes_halfagg_binding`, `bytes_halfagg_dlog_tight_256`, `bytes_halfagg_binding_256` | The main security results for secp256k1 with 32-byte nonces, public keys and messages (`Halfagg/BytesSecurity.lean`). The x-only encoding of a point is `bytes(x(P))`, the challenge hash is BIP 340's, and the randomizer hash has 256-bit outputs that are reduced mod `n`. The last two have the challenge hash as a random oracle with 256-bit outputs that are reduced mod `n`. |
| `aggExperimentB_eq`, `bytesGame_halfagg_unforgeable` | The game in which the forgery is `aggsig` and `pm_aggd` as byte arrays of any length (`Halfagg/BytesGame.lean`). It is the game on 32-byte arrays for the adversary that parses its forgery, so the bound carries over. |
| `verifyAggregateBytes_aggregateBytes`, `verifyAggregateBytes_incAggregateBytes` | `Aggregate` and `IncAggregate` on bytes are correct: signatures that pass BIP 340 `Verify` give bytes that pass `VerifyAggregate`. |

For the discrete-log solvers, let `qH` and `qS` bound the forger's challenge queries and signing requests, `ℓ` the length of its forgery, `Q = qH + qS + ℓ + 1` and `ε = Pr[forger wins] - (q + 1)·μ - qS·(qS + Q)·2/(n - 1)`. The solver of `halfagg_dlog` succeeds with probability at least `ε·(ε/(Q + 1) - 1/n)`. Its quadratic loss is the forking lemma in BIP 340's own proof. The solver of `halfagg_dlog_tight` succeeds with probability at least `ε - (qH + 1)/n`. With a 256-bit challenge hash, `ε` loses another `(qH + qS + ℓ)/2^127` (`secp256k1_halfagg_dlog_256`, `secp256k1_halfagg_dlog_tight_256`).

### Supporting facts

| Theorem | Statement |
|---|---|
| `incAggregate_append`, `aggregate_append` | `Aggregate(A ++ B) = IncAggregate(Aggregate(A), A, B)`. |
| `verifyAggregate_single` | A one-signature aggregate verifies exactly when the BIP 340 signature does. |
| `aggregate_accepts_invalid` | An aggregate does not certify the signatures it was made from. Moving `δ ≠ 0` between the `s` values of the first two, weighted by `z₁`, makes the second invalid and leaves the aggregate unchanged. |
| `verifyMulti_eq`, `secp256k1_verifyMulti_eq` | `VerifyAggregate` can be computed as one sum of scalar multiplications, `s⋅G = Σ zᵢ⋅Rᵢ + (zᵢ⋅eᵢ mod n)⋅Pᵢ`, if `n⋅P = 0` for every point. That holds for secp256k1. |
| `secp256k1_primeOrder` | secp256k1 has exactly `n` points, so `n⋅P = 0` for every point (`Halfagg/PrimeOrder.lean`). The proof counts no points: there are at most `2⋅p + 1`, the generator has order `n`, and no point has order two. |
| `forgeOnes_verifies`, `forgeLate_verifies`, `card_rogue` | The randomizers are needed, and each must cover its own item (`Halfagg/Attacks.lean`). With every randomizer `1`, the verifier of the first proposal of half-aggregation, an explicit aggregate for any public key and message verifies without a signature. The same holds if `zᵢ` hashes only the items before item `i`. The forger's nonce point must have an even y-coordinate, and at least `(n - 1)/2` of its `n` choices give one. |
| `grinder_advantage` | The loss is tight up to one query. With a randomizer hash that is uniform in `ZMod n`, where `μ = 1/n`, a forger with `q` randomizer queries and no signing query wins with probability at least `1 - ((n - 1)/n)^q`. |
| `reduction_sign_queries`, `extractor_sign_queries` | The reduction and the extractor make no signing query the forger did not make. |
| `game_verifier` | The game's verifier is `verifyAggregate`. |
| `bettor_advantage_pos`, `bettor_verify_pos`, `bettorRom_advantage_pos`, `bettorRomH_advantage_pos`, `bettor_bound`, `bettorRom_bound`, `bettorRomH_bound`, `bytesGame_winnable` | The games can be won, so the bounds are not empty. A forger that bets on the secret key `1` wins the standard game, the game of the knowledge theorem and the games with the challenge hash as a random oracle, with scalars or hash outputs as answers, with positive probability, for every model of the randomizer hash and every nonce derivation. The three `_bound` theorems are `halfagg_unforgeable`, `halfagg_dlog_tight` and `halfagg_dlog_tight_hashed` applied to that forger, so their hypotheses hold for a forger that wins. The game on bytes can be won as well: a correct aggregate in bytes passes the parsing, the checks and `VerifyAggregate`. |
| `verifyAggregateBytes_eq` | `VerifyAggregate` on bytes is the parsing and the checks, followed by the model's `verifyAggregate`. |
| `decodeVerify_randomizer` | The randomizers of the decoded input hash the bytes of the input. |
| `randomizerInput_injective` | The bytes that a randomizer hashes determine the item list, because every field has 32 bytes. So the model loses nothing by taking the randomizer as a function of the list. |
| `verifyAggregateBytes_unique` | An aggregate signature has one encoding. Two aggregate signatures with the same nonces that pass `VerifyAggregate` for the same list are equal, because `VerifyAggregate` rejects an `s` that is not below `n`. |
| `randomizerX_eq_red256`, `length_sha256` | BIP 458's randomizer is the randomizer hash of the instance for 32-byte arrays. SHA-256 has 32 bytes of output, and the randomizer is that value reduced mod `n`. |
| `verifyAggregateBytes_eq_X`, `decodeX_bytes`, `bytes_game_verifier` | `VerifyAggregate` on bytes is the verifier of the instance for 32-byte arrays on the 32-byte chunks of its input. So with SHA-256 as the randomizer hash, the game's check of a forgery is `VerifyAggregate` on bytes. |

### Axioms

The theorems use only Lean's standard axioms (`propext`, `Classical.choice`, `Quot.sound`), and `lake build` fails if that changes for a result (`Halfagg/Summary.lean`). Only the test vector checks depend on compiled evaluation (`native_decide`).

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
| `Hop.lean` | A computation with at most `Q` hash queries, with a table of hash outputs against a table of scalars read through `rep`: the difference is at most `Q·δ` (`table_hop`). |
| `HashedGame.lean`, `HashedBinding.lean` | The games with hash outputs as oracle machines (`gameM_table`, `bindM_table`) and the number of hash outputs they read (`gameM_bound`, `bindM_bound`). |

`Halfagg/Winnable.lean` has the forger that wins each game.

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

The module is [bitcoin-core/secp256k1#1566](https://github.com/bitcoin-core/secp256k1/pull/1566). The numbers in this section are for its head at commit [`c7ed5e0`](https://github.com/bitcoin-core/secp256k1/commit/c7ed5e0a0dbc69f5f75bc00e516ccd5ee1033e25). To test it, build the library with the module and compile the driver:

```sh
cmake -S path/to/secp256k1 -B build -DBUILD_SHARED_LIBS=OFF \
  -DSECP256K1_EXPERIMENTAL=ON -DSECP256K1_ENABLE_MODULE_SCHNORRSIG_HALFAGG=ON
cmake --build build
cc -O2 -Ipath/to/secp256k1/include scripts/fuzz_secp256k1.c build/lib/libsecp256k1.a -o fuzz_secp256k1
python3 scripts/fuzz.py path/to/bips/bip-0458 --no-lean --secp256k1 ./fuzz_secp256k1 --cases 10000
```

The C API cannot express every malformed input, such as a public key of the wrong length. The driver skips those cases, about one in five.

No run has found a mismatch: 10,000 cases against the Lean model and more than 30,000 against libsecp256k1, 3,000 of them under ASan and UBSan. CI runs 300 cases against the Python reference at the pinned bips commit, with a new seed for every run. A second CI job builds libsecp256k1 at the commit above and runs the module's unit tests, 3,000 cases and the exhaustive tests of the next section.

## Exhaustive test for the C module

`patches/secp256k1-halfagg-exhaustive-tests.patch` adds a test of the `schnorrsig_halfagg` module to libsecp256k1's exhaustive tests, which run the library on a group of order 13 or 199. It applies to the commit named above.

The test makes BIP 340 signatures from secret keys and nonces that it knows as discrete logarithms, aggregates up to three of them, and compares every result with the value computed on the discrete logarithms:

- `Aggregate` returns `r_0 ‖ … ‖ r_{u-1} ‖ bytes(s)` with `s = Σ zᵢ⋅sᵢ`. The test hashes every prefix from the start for `zᵢ`, where the module updates one hash state.
- `IncAggregate` returns the same bytes from every split of the list.
- `VerifyAggregate` accepts that `s` and no other value. It rejects `s = n` and `s = n + 1`, also for the empty aggregate.
- `Aggregate` rejects a signature with `s = n`, and `IncAggregate` an input aggregate with `s = n`.
- `VerifyAggregate` rejects every `s` if a nonce is not the x-coordinate of a point or is not below the field size.

The second is `aggregate_append` of the Lean model, and the third is `verifyAggregateBytes_aggregateBytes` with `verifyAggregateBytes_unique`. The test checks them on the C code for every input of a small group.

```sh
git -C path/to/secp256k1 apply path/to/halfagg-lean/patches/secp256k1-halfagg-exhaustive-tests.patch
cmake -S path/to/secp256k1 -B build -DSECP256K1_EXPERIMENTAL=ON \
  -DSECP256K1_ENABLE_MODULE_SCHNORRSIG_HALFAGG=ON -DSECP256K1_BUILD_EXHAUSTIVE_TESTS=ON
cmake --build build
build/bin/exhaustive_tests
```

The test passes on the groups of order 13 and 199 and takes about 10 seconds on each. On order 13 it runs every key and nonce of one signature and of two, with all 15 encodings of `s` from 0 to `n + 1`. On order 199 it runs every key and nonce of one signature, derives the second and third from the first, and tries the expected `s`, its successor and the two encodings that are out of range. The order is a compile-time constant of `src/tests_exhaustive.c` (`-DEXHAUSTIVE_TEST_ORDER=199` for that file only), and the rest of the suite is slow on that group.

## Mutation test of the C module

`scripts/mutate_secp256k1.py` measures what these tests can see. It applies 21 one-line mutants to the C module, such as dropping a range check or hashing `z₀`, and runs three sets of tests against each: the module's unit tests, the generated cases, and the exhaustive tests on the group of order 13 with the patch above.

```sh
python3 scripts/mutate_secp256k1.py path/to/secp256k1 path/to/bips/bip-0458
```

The script works on an export of the checkout's `HEAD` in a temporary directory and takes about 6 minutes.

The unit tests catch 19 mutants, the cases 18 and the exhaustive tests 18. Together they catch all 21.

- The unit tests miss the mutant without the check `s < n` in `aggverify`. Such a verifier still rejects an `s ≥ n` whose reduction fails the equation. The empty aggregate with `s = n` tells it apart. The generator produces that input and the exhaustive test has it.
- Only the exhaustive tests catch the mutant that reduces an `r ≥ p` mod `p`. On secp256k1 no input can, because nobody can produce a signature whose nonce has an x-coordinate below `2^256 - p`. The test curve has a point of order 3 with the x-coordinate 0, outside the group. The mutant reduces `r = p` to it, and a randomizer that is a multiple of 3 removes the point from the equation.

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
