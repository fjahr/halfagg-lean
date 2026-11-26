# Reviewing halfagg-lean

Lean checks the proofs. A reviewer checks that the statements say what they should. Everything under `Halfagg/Proofs/` can stay unread, because a wrong proof does not compile. A wrong definition does. [The main results](#the-main-results) names one result for every property and lists, for each, the definitions that decide what it says. [Every definition behind the results](#every-definition-behind-the-results) is that list for all results, in this project and in the libraries it is built on. Both are computed from the compiled project, and the build fails if they change.

## The main results

There is one main result for every property. It is stated for any curve that satisfies taproot-lean's interface and for any type of x-only encodings and of messages. Every other result is one of these in another form, for another model of a hash function, for secp256k1 or for bytes, or it is a fact that supports one. The [README](README.md#results) lists them.

A reader of a main result has to agree with its statement and with the definitions behind the statement. The table counts those definitions and their source lines, comments included, in this project and in the libraries it is built on, up to Mathlib. `#reading` in `Halfagg/Audit.lean` computes the numbers and the lists, and `Halfagg/Summary.lean` guards them.

<!-- main:begin -->

| Main result | Theorem | Definitions here | Lines | Definitions in the libraries | Lines |
|---|---|---|---|---|---|
| Correctness | `verifyAggregate_aggregate`, `verifyAggregate_incAggregate` | 13 | 56 | 5 | 39 |
| Unforgeability | `halfagg_unforgeable` | 50 | 290 | 127 | 811 |
| Knowledge of the individual signatures | `halfagg_knowledge` | 53 | 293 | 120 | 764 |
| A reduction to discrete log | `halfagg_dlog_tight` | 69 | 370 | 135 | 804 |
| Binding | `halfagg_binding` | 21 | 93 | 71 | 402 |
| All of them |  | 98 | 577 | 160 | 991 |

The definitions of this project behind each main result, by file:

**Correctness**

- `Halfagg/Basic.lean`: `AggSig`, `Item`, `aggregate`, `entryItem`, `entryPM`, `incAggregate`, `isum`, `items`, `lifts`, `term`, `verifyAggregate`, `verifyWith`, `z`

**Unforgeability**

- `Halfagg/Basic.lean`: `AggSig`, `Item`, `isum`, `items`, `lifts`, `term`, `verifyWith`
- `Halfagg/Security.lean`: `Security.AItem`, `Security.AggAdversary`, `Security.AlgForger`, `Security.AnnSpec`, `Security.Core`, `Security.GameSpec`, `Security.NonceGen`, `Security.Out`, `Security.Pts`, `Security.RandSpec`, `Security.RedBound`, `Security.Rep`, `Security.Reply`, `Security.Request`, `Security.SignSpec`, `Security.aggAdvantage`, `Security.aggExperiment`, `Security.aggWins`, `Security.annotate`, `Security.bip340`, `Security.coreImpl`, `Security.erase`, `Security.eraseImpl`, `Security.extractForgery`, `Security.flatten`, `Security.initial`, `Security.instDecidableEqAItem`, `Security.isRand`, `Security.liftRep`, `Security.memoRecord`, `Security.memoize`, `Security.memoizeList`, `Security.pairs`, `Security.rawTail`, `Security.reduction`, `Security.smulVal`, `Security.starRep`, `Security.tableRO`, `Security.tableZs`, `Security.toItems`, `Security.zQuery`, `Security.Core.init`, `Security.instDecidableEqAItem.decEq`

**Knowledge of the individual signatures**

- `Halfagg/Basic.lean`: `AggSig`, `Item`, `isum`, `items`, `lifts`, `term`, `verifyWith`
- `Halfagg/Security.lean`: `Security.AItem`, `Security.AggAdversary`, `Security.AlgForger`, `Security.AnnSpec`, `Security.Core`, `Security.GameSpec`, `Security.NonceGen`, `Security.Out`, `Security.Pts`, `Security.RandSpec`, `Security.RedBound`, `Security.Rep`, `Security.Reply`, `Security.Request`, `Security.SignSpec`, `Security.annotate`, `Security.bip340`, `Security.coreImpl`, `Security.erase`, `Security.eraseImpl`, `Security.flatten`, `Security.initial`, `Security.instDecidableEqAItem`, `Security.isRand`, `Security.liftRep`, `Security.memoRecord`, `Security.memoize`, `Security.memoizeList`, `Security.pairs`, `Security.rawTail`, `Security.smulVal`, `Security.starRep`, `Security.tableRO`, `Security.tableZs`, `Security.toItems`, `Security.zQuery`, `Security.Core.init`, `Security.instDecidableEqAItem.decEq`
- `Halfagg/SecurityKnowledge.lean`: `Security.aggVerifies`, `Security.aggVerifyAdvantage`, `Security.aggVerifyExperiment`, `Security.extractAdvantage`, `Security.extractExperiment`, `Security.extractSig`, `Security.extractWins`, `Security.extractor`

**A reduction to discrete log**

- `Halfagg/Basic.lean`: `AggSig`, `Item`, `isum`, `items`, `lifts`, `term`, `verifyWith`
- `Halfagg/Security.lean`: `Security.AItem`, `Security.AggAdversary`, `Security.AlgForger`, `Security.AnnSpec`, `Security.Core`, `Security.GameSpec`, `Security.NonceGen`, `Security.Out`, `Security.Pts`, `Security.RandSpec`, `Security.RedBound`, `Security.Rep`, `Security.Reply`, `Security.Request`, `Security.SignSpec`, `Security.aggExperiment`, `Security.aggWins`, `Security.annotate`, `Security.bip340`, `Security.erase`, `Security.eraseImpl`, `Security.finalItems`, `Security.flatten`, `Security.initial`, `Security.instDecidableEqAItem`, `Security.isRand`, `Security.isSign`, `Security.liftRep`, `Security.memoRecord`, `Security.memoize`, `Security.memoizeList`, `Security.pairs`, `Security.rawTail`, `Security.smulVal`, `Security.starRep`, `Security.toItems`, `Security.zQuery`, `Security.Core.init`, `Security.NonceGen.uniform`, `Security.instDecidableEqAItem.decEq`
- `Halfagg/SecurityROM.lean`: `Security.ChalSpec`, `Security.FSSig`, `Security.RomForger`, `Security.RomForgerSpec`, `Security.RomSpec`, `Security.aggAdvantageROM`, `Security.aggExperimentROM`, `Security.answerChal`, `Security.hOf`, `Security.hashQ`, `Security.isChalCall`, `Security.isRandCall`, `Security.isSignCall`, `Security.knownChal`, `Security.romHandler`, `Security.romTableRO`, `Security.RomForger.at`
- `Halfagg/SecurityTight.lean`: `Security.ExplainsNonces`, `Security.candKey`, `Security.keySolver`, `Security.romPrefix`, `Security.target`

**Binding**

- `Halfagg/Basic.lean`: `AggSig`, `Item`, `isum`, `items`, `lifts`, `term`, `verifyWith`
- `Halfagg/Security.lean`: `Security.RandSpec`, `Security.RedBound`, `Security.zQuery`
- `Halfagg/SecurityBinding.lean`: `Security.BindAdversary`, `Security.BindSpec`, `Security.answerChalB`, `Security.bindAdvantage`, `Security.bindExperiment`, `Security.bindGame`, `Security.bindWins`, `Security.isChalB`, `Security.isRandB`
- `Halfagg/SecurityROM.lean`: `Security.ChalSpec`, `Security.hOf`

<!-- main:end -->

## What to read

For a main result, read the definitions on its list and then its statement. [The statements](#the-statements) prints the statements and most of the definitions on one page, in this order.

1. `Halfagg/Basic.lean`, the definitions. Compare `incAggregate`, `aggregate` and `verifyWith` with the algorithms in BIP 458. Then the statements of `verifyAggregate_aggregate` and `verifyAggregate_incAggregate`.
2. `Halfagg/Security.lean`, all of it: the game, the algebraic forger and the reduction. The header lists the modelling choices and the limitations. Then the statement of `halfagg_unforgeable` in `Halfagg/Unforgeability.lean`.
3. `Halfagg/SecurityKnowledge.lean` and the statement of `halfagg_knowledge` in `Halfagg/Knowledge.lean`, for the signatures under keys the forger chose.
4. `Halfagg/SecurityROM.lean` and `Halfagg/SecurityTight.lean`, for the game with the challenge hash as a random oracle and the discrete-log solver. Then the statement of `halfagg_dlog_tight` in `Halfagg/UnforgeabilityTight.lean`.
5. `Halfagg/SecurityBinding.lean` and the statement of `halfagg_binding` in `Halfagg/Binding.lean`.

taproot-lean supplies the curve interface, `BIP340.sign` and `BIP340.verify`. VCVio supplies the random oracle and the BIP 340 game (`SignatureAlg.unforgeableAdvantage`). agm-lean supplies the algebraic adversary. A full review reads those definitions too. taproot-lean checks the order of secp256k1's generator with compiled code. `Halfagg/OrderG.lean` proves it from a certificate that the kernel checks, and the theorems here use that proof (`secp256k1F`), so only the test vector checks depend on compiled code.

The model was compared with BIP 458 at bitcoin/bips commit [`a7f9132`](https://github.com/bitcoin/bips/blob/a7f91321f25b5be8d93e901775621c21519e80b7/bip-0458.mediawiki). CI takes the test vectors and the Python reference from the same commit.

## Questions to ask

**Is the game the standard one?** `aggExperiment` and `aggWins` never mention representations or the reduction. The adversary picks every public key except the target, and wins with any verifying list that has an item under the target key with a message it never had signed. The game draws the randomizers from the oracle (`zQuery`) and calls `verifyWith`. `game_verifier` proves that this is `verifyAggregate` once the oracle is a fixed function.

**How does the signer derive its nonces?** In any way that is a distribution on the nonzero scalars for every secret key and message (`NonceGen`). `halfagg_unforgeable` and `halfagg_knowledge` hold for each of them, with the same derivation in the half-aggregation game and in the BIP 340 game that the reduction plays. BIP 340 hashes the key, the message and auxiliary randomness, which is one such derivation for fixed hash functions. So the first theorem says that half-aggregation is as secure as BIP 340 with the nonces BIP 340 specifies, and it does not need that hash to be a random oracle. The theorems with the challenge hash as a random oracle are for uniform nonces (`NonceGen.uniform`), because taproot-lean's proof of BIP 340 is.

**Is the forger class too small?** `AlgForger` is agm-lean's adversary. It must explain every point it sends as a combination of `G`, the target key and the nonce points of the signatures it received. `erase` drops the explanations, so the theorems are about the standard game. The x-coordinates a forger hashes come from points it explained, with one exception: after an item that fails `lift_x`, a randomizer request may contain arbitrary encodings (`rawTail`). That is safe because no list with such an item verifies (`aggWins_lifts`).

**Do the theorems need a curve group of prime order?** Only `verifyMulti_eq` and `halfagg_binding` do. `Curve` asks for a point `G` of prime order `n` in a commutative group. Every point the forger explains is a multiple of `G`, and the unforgeability and knowledge proofs need nothing about other points. secp256k1 has prime order (`secp256k1_primeOrder`).

**Could unforgeability be proven without the algebraic group model?** Neither proof that BIP 458 cites does so for BIP 458's scheme. BIP 458 derives `zᵢ` from the first `i + 1` items, so that signatures can be added to an aggregate later. Chen and Zhao call this scheme IASchnorr and prove it only in the algebraic group model. The random-oracle proof of [Chalkias, Garillot, Kondi and Nikolaenko](https://eprint.iacr.org/2021/350) (Theorem 5) is for the variant that hashes the whole list for every randomizer, and its loss is quadratic. For BIP 458's variant, Chen and Zhao note in Remark 6 that a random-oracle proof would rewind the forger once per item, so its loss would grow exponentially with the number of items.

**Why must the forger explain a point when it first sends it?** The theorem has no running-time bound, so it also covers a forger that finds the secret key by brute force and then knows many representations of each point. If it could choose them after seeing the randomizers, it could pick ones for which the extraction fails. So a randomizer request carries the representations of its points, and the reduction keeps the first one it sees for each x-coordinate (`memoize`). The representations behind `zᵢ` are then fixed before `zᵢ` is drawn. This is the convention of Chen and Zhao's model, where the forger explains every group element it outputs or sends to an oracle.

**What does a verifier learn about signatures under other keys?** `halfagg_knowledge` says that whoever produced the aggregate knew a BIP 340 signature for every item. `extractor` runs the forger as `reduction` does and computes an `sᵢ` for every item from the forger's explanations. It has no secret key and asks its signing oracle for nothing the forger did not ask for (`extractor_sign_queries`). The signatures have the nonces of the aggregate. They need not be the signatures that went into `Aggregate`, which an aggregate does not determine (`aggregate_accepts_invalid`).

**Do the reduction and the extractor cheat?** Each gets a BIP 340 public key and a signing oracle and nothing else, and answers randomizer requests from its own lazily sampled table. `reduction_sign_queries` shows that the reduction asks for no signature the forger did not ask for, and VCVio's game rejects a forgery on a signed message.

**Do the random-oracle forger and reduction only query the oracle?** `RomForger.main` and `reductionROM` are oracle programs over a challenge-hash oracle, so they cannot read the table. `reductionROM_bound` counts the reduction's queries: the forger's signing requests, and `qH + qS + ℓ + 1` hash queries for a forger with `qH` hash queries, `qS` signing requests and forgeries of at most `ℓ` items. The game samples the whole table first, which for a finite domain is the same as lazy sampling (`rom_eq_table`).

**How is the randomizer hash reduced mod `n`?** The oracle returns a uniform element of a type `H`, and the game and the reduction turn it into a scalar with `red`. The forger sees the unreduced output. The theorems hold for every `H` and `red` and lose `μ` per randomizer, where `RedBound red μ` says that `red` of a uniform output is a given scalar with probability at most `μ`. For secp256k1, `H` is `Fin (2^256)`, `red256` is `int(⋅) mod n` and `μ = 2/2^256`, because `2^256 ≤ 2n` (`secp256k1_redBound`). `grinder_advantage` uses the uniform model, `H = ZMod n` with `μ = 1/n`.

**How is the challenge hash reduced mod `n`?** BIP 340 computes a challenge as `int(hash(…)) mod n` from a 256-bit hash. In `Halfagg/SecurityROM.lean` the oracle returns a uniform scalar, as in taproot-lean's proof of BIP 340. In the games of `Halfagg/SecurityHashed.lean` it returns a uniform element of a type `Hc` of hash outputs. The adversary sees the outputs, and the game turns them into scalars with `redc`. `halfagg_hashed_le` reduces this game to the one with scalars. Choose one hash output `rep c` for every scalar `c`. The game reads at most `qH + qS + ℓ` hash outputs: the forger's queries, one for every signature and one for every item of the forgery. Each is one of the chosen outputs except with probability `δ` (`RepBound`), and a chosen output is `rep` of a uniform scalar. So the forger wins at most as often as `F.viaRep rep` wins the game with scalars, plus `(qH + qS + ℓ)·δ`. `F.viaRep rep` asks the oracle with scalar answers and runs `F` on `rep c`. For `Hc = Fin (2^256)` and `redc h = h mod n`, `rep c` is the output below `n` and `δ = (2^256 - n)/2^256`, which is at most `2^-127` for secp256k1 (`secp256k1_repBound`). `halfagg_dlog_hashed` and `halfagg_dlog_tight_hashed` are the discrete-log theorems for this game. `halfagg_binding_hashed` is the binding theorem, where the game reads at most `qC + 2ℓ` hash outputs.

**What does `ExplainsNonces` ask of the forger?** That it sends a nonce point in a randomizer request before it asks for a challenge with that nonce. The reduction records explanations from randomizer requests only, so this fixes the coefficient `β` of the target key in the nonce point before the challenge `e` is drawn, and `e = -β` has probability `1/n`. Without it, a forger that hashes a raw x-coordinate can choose its explanation after it has seen `e`, and `halfagg_key_or_signature` leaves that probability as a term. The request can be for the empty list and counts toward `q`. For plain Schnorr signatures, [Fuchsbauer, Plouviez and Seurin](https://eprint.iacr.org/2019/877) have a tight reduction in the same model.

**What does binding add to unforgeability?** Unforgeability protects one honest key. `halfagg_binding` is about an adversary that chooses every key: it cannot produce an aggregate that `VerifyAggregate` accepts for two lists that differ in a key or a message. BIP 458 does not state this. The bound is statistical, with both hashes as random oracles. The challenge hash has to be one because a one-signature aggregate has no randomizer, so its binding is BIP 340's own. Binding says nothing about which signatures went into the aggregate (`aggregate_accepts_invalid`).

**What connects the theorems to BIP 458's bytes?** `Halfagg/BytesSecurity.lean` instantiates them for secp256k1 with 32-byte arrays as nonces, public keys and messages (`bytes_halfagg_unforgeable` and three more). The x-only encoding of a point is `bytes(x(P))`, and an array that is not below `p` does not lift. The challenge hash is BIP 340's tagged SHA-256. The randomizer oracle answers with 256-bit values that the scheme reduces mod `n`, and BIP 458's randomizer is such a function: SHA-256 has 32 bytes of output (`length_sha256`, `randomizerX_eq_red256`), and its input determines the item list (`randHash256_input_injective`). `verifyAggregateBytes_eq_X` says that `VerifyAggregate` on bytes is the parsing and the checks followed by the verifier of this instance, on the 32-byte chunks of the input (`decodeX_bytes`). `bytes_game_verifier` puts these together: with SHA-256 as the randomizer hash, the game's check of a forgery is `VerifyAggregate` on bytes. In `Halfagg/BytesGame.lean` the forger outputs `aggsig` and `pm_aggd` as byte arrays of any length. `aggExperimentB_eq` says that this game is the game on 32-byte arrays for the adversary that parses its forgery, so `bytesGame_halfagg_unforgeable` has the same bound. `toStruct_serB` is the other direction: an algebraic forger with its forgery written as bytes parses back to itself. So the game on bytes can be won (`bytesGame_winnable`).

**Are the theorems vacuous?** A bound on forgers says nothing about a game that nobody can win, and a mistake in a definition could make a game like that. `Halfagg/Winnable.lean` has a forger that wins. `bettor` bets that the secret key is `1` and signs with it. It wins the standard game with positive probability, for every randomizer hash, every reduction of its outputs and every nonce derivation (`bettor_advantage_pos`). Its aggregate verifies in the game of the knowledge theorem (`bettor_verify_pos`), and `bettorRom` wins the game with the challenge hash as a random oracle (`bettorRom_advantage_pos`). `bettorRomH` wins the game in which that oracle returns hash outputs (`bettorRomH_advantage_pos`). `bettor_bound`, `bettorRom_bound` and `bettorRomH_bound` are `halfagg_unforgeable`, `halfagg_dlog_tight` and `halfagg_dlog_tight_hashed` applied to these forgers, so the hypotheses of both theorems, `ExplainsNonces` among them, hold for a forger that wins. The curve hypothesis `hx0` holds for secp256k1 (`Halfagg/Proofs/Secp256k1.lean`). `grinder_advantage` shows that the bound cannot be improved by more than one query. There is no such forger for the binding game, where winning means a collision.

## BIP 458's claims

What BIP 458 says about correctness and security, and the theorem for it.

| BIP 458 | Lean |
|---|---|
| Motivation: a verifier that accepts the aggregate "can be sure that the individual signatures would have passed verification". | Not for the signatures given to `Aggregate` (`aggregate_accepts_invalid`). What holds: the owner of an honest key signed its message (`halfagg_unforgeable`), and whoever produced the aggregate knew a BIP 340 signature for every item (`halfagg_knowledge`). |
| Rationale: Chen and Zhao's tight proof in the random oracle and algebraic group model. | `halfagg_unforgeable`, with loss `(q + 1)·μ`, which is `(q + 1)·2/2^256` for BIP 458's hash. `grinder_advantage` shows the loss is tight for a hash that is uniform in `ZMod n`. `halfagg_unforgeable_rom` and `halfagg_dlog` have the challenge hash as a random oracle too, and `halfagg_dlog_tight` reaches discrete log with additive losses only. `halfagg_dlog_hashed` and `halfagg_dlog_tight_hashed` are these for a challenge hash with 256-bit outputs that are reduced mod `n`. |
| Rationale: the first proposal, which added up the `s` values, had a security flaw. | `forgeOnes_verifies`: an explicit forgery against the verifier with every randomizer `1`. `forgeLate_verifies`: a randomizer must also cover its own item. |
| Rationale: `z₀ = 1` is secure. | The game's verifier uses `z₀ = 1` (`zQuery`), so the theorems are about this choice. With every randomizer `1` there is a forgery (`forgeOnes_verifies`). |
| Rationale: signatures can be added to an aggregate later. | `incAggregate_append`, `aggregate_append`: adding in steps gives the same aggregate as aggregating at once. |
| Rationale: 32-byte messages keep the input of each randomizer hash unambiguous. | `randomizerInput_injective`. |
| Rationale: implementations should stream the hash input through one hash state. | No theorem. The model hashes every prefix from the start. libsecp256k1 streams, and the differential test compares the two. |
| `Aggregate`: valid triples give an aggregate that passes `VerifyAggregate`. | `verifyAggregateBytes_aggregateBytes` on bytes, `verifyAggregate_aggregate` in the model. |
| `IncAggregate`: a verifying aggregate and valid triples give an aggregate that passes `VerifyAggregate`. | `verifyAggregateBytes_incAggregateBytes` on bytes, `verifyAggregate_incAggregate` in the model. |
| `Aggregate`, `IncAggregate`: the inverse does not hold. | `aggregate_accepts_invalid`, for invalid triples given to `Aggregate`. No theorem for an invalid aggregate given to `IncAggregate`. |
| `VerifyAggregate`: an efficient algorithm for a sum of scalar multiplications can be used. | `verifyMulti_eq`, if every point has order dividing `n`. `secp256k1_verifyMulti_eq` for secp256k1. |
| The pseudocode of `VerifyAggregate`. | `verifyAggregateBytes_eq`: the verifier on bytes is the parsing and range checks followed by the model's `verifyAggregate`. |
| `VerifyAggregate` fails if `s ≥ n`. | `verifyAggregateBytes_unique`: two aggregate signatures with the same nonces that verify for the same list are equal. Without the check, the empty aggregate would have the encodings `bytes(0)` and `bytes(n)`. No test vector of BIP 458 has that input. The differential test generates it. |

## What the theorems do not say

- The reduction to discrete log is tight only for forgers that explain the nonces they hash (`halfagg_dlog_tight`). For other algebraic forgers, `halfagg_dlog` has the forking-lemma loss of BIP 340's own proof, which is quadratic in the forger's success probability, and `halfagg_key_or_signature` leaves one term without a bound.
- The theorems with the challenge hash as a random oracle need a finite message type. BIP 458's 32-byte messages are one. Their signer draws uniform nonces.
- A `NonceGen` keeps no state between signatures and never gives the nonce `0`. BIP 340 fails on that nonce, which a hash gives with probability about `2^-256`.
- No theorem bounds running time. Without that, `halfagg_unforgeable` alone would allow a reduction that breaks BIP 340 by brute force. This one does not, and `reduction` is short enough to check by reading.
- The algebraic group model is a restriction on the forger. A forger that hashes x-coordinates of curve points it cannot explain is outside the theorems.
- `halfagg_unforgeable_rom_hashed` compares the game with 256-bit challenge hash outputs with a BIP 340 game whose challenge hash answers uniformly in `ZMod n`, the game of taproot-lean's proof of BIP 340. No theorem here is about BIP 340 with a 256-bit hash by itself.
- In the instance for 32-byte arrays and in the game on bytes a query to the randomizer hash is a list of items of 32-byte arrays, not the byte string that BIP 458 hashes, and a signature of the signing oracle comes as `(r, s)`, not as 64 bytes. No theorem has a random oracle on byte strings.
- No theorem says that the functions on bytes in `Halfagg/Vectors.lean` are BIP 458's algorithms. The 53 test vectors and the differential test compare them with `halfagg.py`.

## Machine checks

- `lake build` compiles every proof and fails if the axioms of a result change (`Halfagg/Summary.lean`).
- `Halfagg/Summary.lean` also guards two inventories of the whole project, computed by the commands of `Halfagg/Audit.lean`. `#project_axioms` lists the axioms that the modules declare and that their declarations depend on, so an axiom that no result uses fails the build too. `#surface` lists the definitions behind the results, which is the last section of this file. The summary also guards the output of `#reading` for every main result, which is the table and the lists under [The main results](#the-main-results).
- `scripts/check.sh` reads every Lean file of the repository for `sorry`, axioms, unsafe code and compiled evaluation outside the test vector checks. It checks that the root module has only imports and the generated summary only guarded commands. It checks that every code block under [The statements](#the-statements) is in the sources word for word, and that `Halfagg/Summary.lean` checks the axioms of every theorem printed there and of every result in the README's tables. It finds a result by its full name, so a declaration with the same last name in another namespace does not count. It checks that the table of the main results and the list of definitions at the end of this file are the ones the summary guards, that this file prints the statement of every main result, and that no definition on the list is under `Halfagg/Proofs/`.
- `scripts/check_selftest.sh` changes a copy of the sources in fourteen ways, such as an axiom in the root module or in the summary, and checks that `scripts/check.sh` fails each time.
- `scripts/replay.sh` replays in the kernel with `leanchecker`, without the elaborator, every project module and every module of taproot-lean and agm-lean that the project imports, one process per module. It rejects a module that adds a false theorem behind the kernel's back, which `#print axioms` does not notice.
- `scripts/replay.sh --deps` does the same for the 255 modules of VCVio, PolyFun and cslib that the project imports. A CI workflow of its own runs it when a pinned commit or the toolchain changes, and once a week. Mathlib and the libraries under it are not replayed here.
- CI runs all of these. It also regenerates the summary and the test vector data, runs 300 cases of `scripts/fuzz.py` against the Python reference with a new seed for every run, and checks that the build fails when an unused axiom is added to a module.
- A second CI job builds libsecp256k1 with the `schnorrsig_halfagg` module at the commit the README names. It runs the module's unit tests and 3,000 cases of `scripts/fuzz.py` against the Python reference with a new seed. It also runs libsecp256k1's exhaustive tests on the group of order 13, with the test that `patches/secp256k1-halfagg-exhaustive-tests.patch` adds for the module.

### Mutants of the model

`scripts/mutate_model.py` changes one definition at a time in a copy of the project and builds it. A mutant that still built would show that no theorem depends on the detail it changes. All 23 fail. A second CI workflow runs it on every push. Lake does not build what depends on a module that failed, so the table names the declarations nearest to the changed definition, which are often lemmas and not main theorems.

| Mutant | Fails in |
|---|---|
| Every randomizer is `1` | `badKey_value` |
| The randomizer `zᵢ` does not cover item `i` | `badKey_value` |
| A win needs no unsigned message | `extract_or_bad` |
| A win needs no item under the target key | `extract_or_bad` |
| The raw tail of a randomizer request is always used | `covered_rawTail` |
| `VerifyAggregate` does not check that the nonces and the public keys lift | `verifyAggregate_incAggregate`, `verifyAggregate_single`, `verifyMulti_eq` |
| Randomizer requests are not counted | `annImpl_step` |
| Signing requests are not counted | `red_step_sign` |
| Every reduction of a hash output counts as nearly uniform | `redMod_bound`, `id_bound`, `badKey_prob` |
| Every 256-bit hash output reduces to the scalar `0` | `redMod_bound`, `redMod_repMod`, `repMod_bound` |
| The verification game of the knowledge theorem accepts every aggregate | `extract_all_or_bad`, `fail_sum_all` |
| The game with a challenge oracle verifies with the challenges `0` | `halfagg_unforgeable_rom`, `halfagg_dlog` |
| Challenge-hash queries are not counted | `romHandler_bound` |
| Every forger counts as explaining its nonces | `explains_chal` |
| The binding adversary wins with the same list twice | `win_pair` |
| The challenge hash on 32-byte arrays hashes the public key before the nonce | `challengeX_encX` |
| The game on bytes is won by a forgery that fails the parsing | `aggExperimentB_eq` |
| `VerifyAggregate` on bytes accepts an `s` that is not below `n` | `decodeVerify_some`, `verifyAggregateBytes_encode`, `incAggregateBytes_isSome`, `verifyAggregateBytes_unique` |
| The randomizer hash does not cover the messages | `aggregate_vectors`, `incAggregate_vectors`, `verifyAggregate_vectors` |
| The game with hash outputs verifies with the challenges `0` | `aggAdvantageROMH_le_viaRep` |
| The forger for scalar answers gets the hash output of the scalar `0` | `answerChal_repChal` |
| Every choice of hash outputs counts as covering a uniform output | `repMod_bound` |
| The binding game with hash outputs verifies with the challenges `0` | `bindAdvantageH_le_viaRep` |

For the two randomizer mutants there is more than a proof that fails: `forgeOnes_verifies` and `forgeLate_verifies` are forgeries against these verifiers. The mutants change four definitions in the same way: `zQuery` of the game and `tableZs` of the reduction in `Halfagg/Security.lean`, and `zQueryAnn` and `zOf` of the proof in `Halfagg/Proofs/Annotated.lean`. A mutant of `z` in `Halfagg/Basic.lean` does not reach the security proof, because it already breaks `z_append` in the same file.

## The statements

The statements of the main results and the definitions behind them, copied from the sources with their comments. Proofs are left out.

Throughout, `n` is a prime, `E` is the group of curve points, `X` is the type of x-only encodings, `M` is the message type and `H` is the type of the randomizer hash's outputs. `C : Curve n E X` is taproot-lean's curve interface, `challenge : X → X → M → ZMod n` is the BIP 340 challenge hash and `red : H → ZMod n` turns a randomizer hash output into a scalar.

Not printed here: the parts of the reduction and of the discrete-log solver (`coreImpl`, `extractForgery`, `romHandler` and their helpers, in `Halfagg/Security.lean` and `Halfagg/SecurityROM.lean`), and the definitions of taproot-lean, VCVio and agm-lean at the commits pinned in `lakefile.toml`. The lists under [The main results](#the-main-results) name every definition of this project that a main result needs.


### BIP 458's verifier

From `Halfagg/Basic.lean`. `rand` is the randomizer hash as a function into `ZMod n`.

```lean
/-- A half-aggregate signature `r₀ ‖ … ‖ r_{u-1} ‖ bytes(s)`. -/
structure AggSig (n : ℕ) (X : Type*) where
  rs : List X
  s : ZMod n
```

```lean
/-- The randomizer input of one signature, in hash order: `(r, pk, m)`. -/
abbrev Item (X M : Type*) := X × X × M
```

```lean
/-- The items of already aggregated `(pk, m)` pairs and their nonces. -/
def items (pm : List (X × M)) (rs : List X) : List (Item X M) :=
  List.zipWith (fun pkm r => (r, pkm.1, pkm.2)) pm rs
```

```lean
/-- The randomizer `zᵢ`: `1` for `i = 0`, otherwise
`int(hash_BIP0458/randomizer(r₀ ‖ pk₀ ‖ m₀ ‖ … ‖ rᵢ ‖ pkᵢ ‖ mᵢ)) mod n`. -/
def z (rand : List (Item X M) → ZMod n) (its : List (Item X M)) (i : ℕ) : ZMod n :=
  if i = 0 then 1 else rand (its.take (i + 1))
```

```lean
/-- `Rᵢ + eᵢ⋅Pᵢ` for one item, with a failed `lift_x` read as `0` (the
verifier checks the lifts separately). -/
def term (C : Curve n E X) (challenge : X → X → M → ZMod n) (it : Item X M) : E :=
  (C.liftX it.1).getD 0 + (challenge it.1 it.2.1 it.2.2).val • (C.liftX it.2.1).getD 0
```

```lean
/-- Whether `lift_x(r)` and `lift_x(pk)` both succeed. -/
def lifts (C : Curve n E X) (it : Item X M) : Bool :=
  (C.liftX it.1).isSome && (C.liftX it.2.1).isSome
```

```lean
/-- The checks of `VerifyAggregate` with the randomizers given as `zf i`: the
nonce count matches, every `lift_x` succeeds, and
`s⋅G = z₀⋅(R₀ + e₀⋅P₀) + … + z_{u-1}⋅(R_{u-1} + e_{u-1}⋅P_{u-1})`. -/
def verifyWith (C : Curve n E X) (challenge : X → X → M → ZMod n) (zf : ℕ → ZMod n)
    (agg : AggSig n X) (pm : List (X × M)) : Bool :=
  let its := items pm agg.rs
  decide (agg.rs.length = pm.length) && its.all (lifts C) &&
    decide (C.mulG agg.s = isum (fun i it => (zf i).val • term C challenge it) 0 its)
```

```lean
/-- BIP458 `VerifyAggregate(aggsig, pm_aggd)`, with the randomizers `zᵢ` from
the randomizer hash `rand`. -/
def verifyAggregate (C : Curve n E X) (challenge : X → X → M → ZMod n)
    (rand : List (Item X M) → ZMod n) (agg : AggSig n X) (pm : List (X × M)) : Bool :=
  verifyWith C challenge (z rand (items pm agg.rs)) agg pm
```

### Correctness

From `Halfagg/Basic.lean`. `Entry` is taproot-lean's: a public key, a message and a BIP 340 signature `(r, s)`. `Entry.valid` is BIP 340 `Verify`.

```lean
/-- The item `(r, pk, m)` of a signature to be aggregated. -/
def entryItem (e : Entry n X M) : Item X M := (e.r, e.pk, e.m)
```

```lean
/-- The `(pk, m)` pair of a signature to be aggregated. -/
def entryPM (e : Entry n X M) : X × M := (e.pk, e.m)
```

```lean
/-- BIP458 `IncAggregate(aggsig, pm_aggd, pms_to_agg)`: add the signatures
`pms` to the aggregate `agg` of the pairs `pmAggd`. Fails if the aggregate
has a nonce count different from `pmAggd`. -/
def incAggregate (rand : List (Item X M) → ZMod n) (agg : AggSig n X) (pmAggd : List (X × M))
    (pms : List (Entry n X M)) : Option (AggSig n X) :=
  if agg.rs.length = pmAggd.length then
    let its := items pmAggd agg.rs ++ pms.map entryItem
    some ⟨agg.rs ++ pms.map (·.r),
      agg.s + isum (fun i e => z rand its i * e.s) pmAggd.length pms⟩
  else none
```

```lean
/-- BIP458 `Aggregate(pms)`: `IncAggregate` starting from the empty aggregate
`bytes(0)`. -/
def aggregate (rand : List (Item X M) → ZMod n) (pms : List (Entry n X M)) :
    Option (AggSig n X) :=
  incAggregate rand ⟨[], 0⟩ [] pms
```

```lean
/-- **Correctness of `IncAggregate`**: adding valid signatures to an aggregate
that verifies gives an aggregate that verifies, for every choice of the hash
functions. -/
theorem verifyAggregate_incAggregate {agg agg' : AggSig n X} {pmAggd : List (X × M)}
    {pms : List (Entry n X M)} (hagg : verifyAggregate C challenge rand agg pmAggd = true)
    (hpms : ∀ e ∈ pms, Entry.valid C challenge e = true)
    (hinc : incAggregate rand agg pmAggd pms = some agg') :
    verifyAggregate C challenge rand agg' (pmAggd ++ pms.map entryPM) = true
```

```lean
/-- **Correctness of `Aggregate`**: aggregating valid signatures gives an
aggregate that verifies, for every choice of the hash functions. -/
theorem verifyAggregate_aggregate {agg : AggSig n X} {pms : List (Entry n X M)}
    (hpms : ∀ e ∈ pms, Entry.valid C challenge e = true) (h : aggregate rand pms = some agg) :
    verifyAggregate C challenge rand agg (pms.map entryPM) = true
```

### The game

From `Halfagg/Security.lean`. `bip340` is BIP 340 as a VCVio signature scheme, and `runWithSigningOracle` is VCVio's signing oracle with a log of the signed messages. `NonzeroScalar n` is taproot-lean's type of the scalars other than `0`.

```lean
/-- **How the signer derives the nonce of a signature**: a distribution on the
nonzero scalars for every secret key and message. BIP340 hashes the key, the
message and auxiliary randomness, which is such a distribution for fixed hash
functions. The signer keeps no state between signatures, and a derivation that
can give the nonce `0`, where BIP340 fails, is not covered.

It is a class so that the proofs need not pass it along. -/
class NonceGen (n : ℕ) (M : Type) where
  /-- The nonce for a secret key and a message. -/
  draw : ZMod n → M → ProbComp (NonzeroScalar n)
```

```lean
/-- Uniformly random nonces, as in taproot-lean's proof of BIP340. The theorems
with the challenge hash as a random oracle are for this derivation. -/
@[reducible] noncomputable def NonceGen.uniform (n : ℕ) [Fact n.Prime] (M : Type) :
    NonceGen n M :=
  ⟨fun _ _ => $ᵗ (NonzeroScalar n)⟩
```

```lean
/-- BIP340 with a uniformly random nonzero secret key and nonces from a
`NonceGen`, in any monad that can sample. `BIP340.sign` normalizes the key and
the nonce to even-y points. Signing cannot fail with a nonzero key and nonce;
the fallback `(pk, 0)` is never used. -/
noncomputable def bip340 [NonceGen n M] (m : Type → Type) [Monad m] [MonadLiftT ProbComp m] :
    SignatureAlg m M X (ZMod n) (X × ZMod n) where
  keygen := monadLift (do
    let d ← $ᵗ (NonzeroScalar n)
    return (C.x (C.mulG d.1), d.1) : ProbComp (X × ZMod n))
  sign pk sk msg := monadLift (do
    let k ← NonceGen.draw sk msg
    return (BIP340.sign C challenge (fun _ _ _ => k.1) sk msg).getD (pk, 0) :
      ProbComp (X × ZMod n))
  verify pk msg sig := pure (BIP340.verify C challenge pk msg sig)
```

```lean
/-- The randomizer hash as a random oracle on lists of `(r, pk, m)` items. Its
outputs have type `H`, for BIP458 the 256-bit strings. -/
abbrev RandSpec (H X M : Type) := List (Item X M) →ₒ H
```

```lean
/-- The signing oracle: a message to a BIP340 signature `(r, s)`. -/
abbrev SignSpec (n : ℕ) (X M : Type) := M →ₒ (X × ZMod n)
```

```lean
/-- The adversary's oracles: uniform sampling, the randomizer hash and signing. -/
abbrev GameSpec (n : ℕ) (H X M : Type) := (unifSpec + RandSpec H X M) + SignSpec n X M
```

```lean
/-- An adversary of the standard game: given the target public key, it outputs
`(r, pk, m)` items and `s`, i.e. the aggregate signature `r₀ ‖ … ‖ bytes(s)` for
the pairs `(pkᵢ, mᵢ)`. -/
structure AggAdversary (n : ℕ) (H X M : Type) where
  main (pk : X) : OracleComp (GameSpec n H X M) (List (Item X M) × ZMod n)
```

```lean
/-- The verifier's randomizer `zᵢ`: `1` for `i = 0`, otherwise the randomizer
hash of the first `i + 1` items, reduced to a scalar by `red`. For BIP458, `red`
is `int(⋅) mod n`. -/
def zQuery (its : List (Item X M)) (i : ℕ) : OracleComp (unifSpec + RandSpec H X M) (ZMod n) :=
  if i = 0 then pure 1 else red <$> HasQuery.query (spec := RandSpec H X M) (its.take (i + 1))
```

```lean
/-- The adversary wins if `VerifyAggregate` accepts with the randomizers `zs` and
some item has the target public key and a message that was never signed. -/
def aggWins (pk : X) (its : List (Item X M)) (s : ZMod n) (zs : List (ZMod n))
    (signed : M → Bool) : Bool :=
  verifyWith C challenge (fun i => zs.getD i 0) ⟨its.map (·.1), s⟩ (its.map (·.2)) &&
    its.any fun it => it.2.1 == pk && !signed it.2.2
```

```lean
/-- The aggregate chosen-key unforgeability game (CK-AEUF-CMA) with the
randomizer hash as a random oracle. -/
noncomputable def aggExperiment [NonceGen n M] (A : AggAdversary n H X M) :
    OracleComp (unifSpec + RandSpec H X M) Bool := do
  let alg := bip340 (M := M) C challenge (OracleComp (unifSpec + RandSpec H X M))
  let (pk, sk) ← alg.keygen
  let ((its, s), log) ← alg.runWithSigningOracle pk sk (A.main pk)
  let zs ← (List.range its.length).mapM (zQuery red its)
  return aggWins C challenge pk its s zs log.wasQueried
```

```lean
/-- The adversary's success probability, with a lazily sampled random oracle. -/
noncomputable def aggAdvantage [NonceGen n M] [SampleableType H] (A : AggAdversary n H X M) :
    ℝ≥0∞ :=
  (ProbCompRuntime.rom (RandSpec H X M)).evalDist (aggExperiment C challenge red A) {true}
```

### The randomizer hash reduced mod `n`

From `Halfagg/Security.lean` and `Halfagg/Hash256.lean`.

```lean
/-- `red` of a uniform hash output is any given scalar with probability at most
`μ`. -/
def RedBound [SampleableType H] (μ : ℝ≥0∞) : Prop :=
  ∀ c : ZMod n, Pr{let h ← $ᵗ H}[red h = c] ≤ μ
```

```lean
/-- `int(h) mod n` for a hash output `h < N`. -/
def redMod (n N : ℕ) : Fin N → ZMod n := fun h => (h.val : ZMod n)
```

```lean
/-- **At most two hash outputs reduce to a given scalar** if `N ≤ 2⋅n`, so a
uniform output reduces to it with probability at most `2/N`. -/
theorem redMod_bound (n N : ℕ) [Fact n.Prime] [NeZero N] (hN : N ≤ 2 * n) :
    RedBound (redMod n N) (2 / (N : ℝ≥0∞))
```

```lean
/-- BIP458's reduction for secp256k1: a 256-bit hash output as a scalar. -/
abbrev red256 : Fin (2 ^ 256) → ZMod Taproot.Secp256k1.n := redMod Taproot.Secp256k1.n (2 ^ 256)
```

```lean
/-- For secp256k1, a uniform 256-bit hash output reduces to a given scalar with
probability at most `2/2^256`. -/
theorem secp256k1_redBound : RedBound red256 (2 / ((2 ^ 256 : ℕ) : ℝ≥0∞))
```

### Algebraic forgers

From `Halfagg/Security.lean`. `Adversary`, `Message` and `explainedSpec` are agm-lean's: every oracle call and the output carry coefficient vectors for their points, over the points received so far.

```lean
/-- Points form the single group sort of the AGM interface. -/
abbrev Pts (E : Type) : Unit → Type := fun _ => E
```

```lean
/-- A forger's requests. Randomizer requests carry the messages `[m₀, …, mᵢ]`
as data and the points `R₀, P₀, …, Rᵢ, Pᵢ` as group arguments. -/
inductive Request (X M : Type) where
  /-- Uniform sampling from `Fin (k + 1)`. -/
  | random (k : ℕ)
  /-- The randomizer hash of `(x(R₀), x(P₀), m₀), …, (x(Rᵢ), x(Pᵢ), mᵢ)`, followed
  by the items of `tail` given as raw x-only encodings (see `rawTail`). -/
  | rand (ms : List M) (tail : List (Item X M))
  /-- A BIP340 signature on a message under the target key. -/
  | sign (m : M)
```

```lean
/-- Replies: a sample, a randomizer hash, or the `s` of a signature (its nonce
point `lift_x(r)` is the reply's group argument). -/
def Reply (n : ℕ) (H X M : Type) : Request X M → Type
  | .random k => Fin (k + 1)
  | .rand _ _ => H
  | .sign _ => ZMod n
```

```lean
/-- A forgery: the messages `[m₀, …]` and `s`, with the points `R₀, P₀, …` as
group arguments. -/
structure Out (n : ℕ) (M : Type) where
  ms : List M
  s : ZMod n
```

```lean
/-- An algebraic half-aggregation forger in `agm-lean`'s interface. -/
abbrev AlgForger (n : ℕ) (H E X M : Type) [AddCommGroup E] :=
  AlgebraicGroupModel.Interaction.Adversary (ZMod n) (Pts E) Unit (Request X M) (Reply n H X M)
    (Out n M)
```

```lean
/-- The forger's initial inputs `[G, P*]`. -/
def initial (Pstar : E) : Message Unit (Pts E) := ⟨(), fun _ => [C.G, Pstar]⟩
```

```lean
/-- `[R₀, P₀, R₁, P₁, …]` as pairs `(Rᵢ, Pᵢ)`. -/
def pairs : List E → List (E × E)
  | R :: P :: rest => (R, P) :: pairs rest
  | _ => []
```

```lean
/-- The items `(x(Rᵢ), x(Pᵢ), mᵢ)` named by messages and points. -/
def toItems (ms : List M) (pts : List E) : List (Item X M) :=
  (ms.zip (pairs pts)).map fun mRP => (C.x mRP.2.1, C.x mRP.2.2, mRP.1)
```

```lean
/-- The raw tail of a randomizer request. It is used only if its first item
fails `lift_x` for `r` or `pk`; otherwise it is dropped. No list that extends
such an item passes `VerifyAggregate`, so the forger may hash anything after
it without explaining it. -/
def rawTail : List (Item X M) → List (Item X M)
  | [] => []
  | it :: rest => if lifts C it then [] else it :: rest
```

```lean
/-- Forward a request to the game's oracles. A signing reply's point is the
lifted nonce `lift_x(r)`. -/
noncomputable def eraseImpl {n : ℕ} :
    QueryImpl (plainSpec (Pts E) (Request X M) (Reply n H X M)) (OracleComp (GameSpec n H X M))
  | ⟨.random k, _⟩ => do
      let u ← (liftM ((GameSpec n H X M).query (.inl (.inl k))) : OracleComp (GameSpec n H X M) _)
      pure ⟨u, fun _ => []⟩
  | ⟨.rand ms tail, groups⟩ => do
      let z ← (liftM ((GameSpec n H X M).query
        (.inl (.inr (toItems C ms (groups ()) ++ rawTail C tail)))) :
        OracleComp (GameSpec n H X M) _)
      pure ⟨z, fun _ => []⟩
  | ⟨.sign m, _⟩ => do
      let sig ← (liftM ((GameSpec n H X M).query (.inr m)) : OracleComp (GameSpec n H X M) _)
      pure ⟨sig.2, fun _ => [(C.liftX sig.1).getD 0]⟩
```

```lean
/-- The standard-game adversary that runs `F` and drops its explanations. -/
noncomputable def erase (F : AlgForger n H E X M) : AggAdversary n H X M where
  main pk := (fun out => (toItems C out.value.data.ms (out.value.groups ()), out.value.data.s)) <$>
    simulateQ (fun q => eraseImpl C q.value) (F.main (initial C ((C.liftX pk).getD 0)))
```

```lean
/-- Whether a request is a randomizer request. -/
def isRand : Request X M → Bool
  | .rand _ _ => true
  | _ => false
```

```lean
/-- Whether a request is a signing request for a message in `p`. -/
def isSign (p : M → Bool) : Request X M → Bool
  | .sign m => p m
  | _ => false
```

```lean
/-- Whether a query of a BIP340 forger is a signing query for a message in `p`. -/
def isSignQuery (p : M → Bool) : ℕ ⊕ M → Bool
  | .inr m => p m
  | .inl _ => false
```

### Unforgeability

From `Halfagg/Security.lean` and `Halfagg/Unforgeability.lean`. The type of `reduction` makes it a forger in VCVio's BIP 340 game (`unforgeableAdvantage`), with the public key and a signing oracle.

```lean
/-- **The reduction**: run the forger with `coreImpl`, forwarding uniform
sampling and signing to its own oracles and answering randomizer requests from
its table; then record the forgery's representations, draw the randomizers the
verifier needs, and extract a BIP340 forgery. It makes one signing query per
signing request of the forger (`reduction_sign_queries`). Its running time is
not formalized. -/
noncomputable def reduction [NonceGen n M] [SampleableType H] [Inhabited M]
    (F : AlgForger n H E X M) :
    SignatureAlg.UnforgeableAdversary (bip340 (M := M) C challenge ProbComp) where
  main pk := do
    let impl := coreImpl (E := E) C challenge pk
      (fun k => liftM (unifSpec.query k))
      tableRO
      (fun msg => liftM ((SignSpec n X M).query msg))
    let ((out, st), table) ← ((simulateQ impl (F.main (initial C ((C.liftX pk).getD 0)))).run
      Core.init).run ∅
    let st := memoize C st (out.value.groups ()) (out.coefficients ())
    let items := annotate C st.memo (toItems C out.value.data.ms (out.value.groups ()))
    let (zs, _) ← (tableZs red items).run table
    return extractForgery C challenge pk items out.value.data.s zs st.signed
```

```lean
/-- **Half-aggregation is as secure as BIP340** (Chen and Zhao, Theorem 2), in
the algebraic group model with the randomizer hash as a random oracle and for
every challenge hash: an algebraic forger that makes at most `q` randomizer
requests wins the standard game with probability at most the success
probability of `reduction F` against BIP340, plus `(q + 1)⋅μ`. Here `μ` bounds
the probability that a uniform output of the randomizer hash reduces to a given
scalar (`RedBound`): `1/n` if the hash is uniform in `ZMod n`, and `2/2^256` for
BIP458's 256-bit hash reduced modulo `n` (`Halfagg/Hash256.lean`).

`hx0` says the point at infinity has no x-only encoding: its x-coordinate in the
curve interface does not lift. For secp256k1 that x-coordinate is `0`, and `0`
is not an x-coordinate of the curve because `7` is not a square modulo `p`. -/
theorem halfagg_unforgeable [NonceGen n M] [Inhabited M] (hx0 : C.liftX (C.x 0) = none)
    (F : AlgForger n H E X M) (q : ℕ)
    (hq : ∀ input, (F.main input).IsQueryBoundP (fun r => isRand r.value.data) q)
    (μ : ℝ≥0∞) (hμ : RedBound red μ) :
    aggAdvantage C challenge red (erase C F) ≤
      SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp (reduction C challenge red F) +
        (q + 1 : ℝ≥0∞) * μ
```

### Knowledge of the individual signatures

From `Halfagg/SecurityKnowledge.lean` and `Halfagg/Knowledge.lean`. `extractor` has the body of `reduction` with a different last line, and `starRep` is the pair `(α*, β*)` with `Rᵢ + eᵢ⋅Pᵢ = α*⋅G + β*⋅P*`.

```lean
/-- `VerifyAggregate` accepts the items `(rᵢ, pkᵢ, mᵢ)` and `s` with the
randomizers `zs`: the first condition of `aggWins`. -/
def aggVerifies (its : List (Item X M)) (s : ZMod n) (zs : List (ZMod n)) : Bool :=
  verifyWith C challenge (fun i => zs.getD i 0) ⟨its.map (·.1), s⟩ (its.map (·.2))
```

```lean
/-- The game of `aggExperiment` without the condition on the target key: the
adversary's aggregate passes `VerifyAggregate`. -/
noncomputable def aggVerifyExperiment [NonceGen n M] (A : AggAdversary n H X M) :
    OracleComp (unifSpec + RandSpec H X M) Bool := do
  let alg := bip340 (M := M) C challenge (OracleComp (unifSpec + RandSpec H X M))
  let (pk, sk) ← alg.keygen
  let ((its, s), _) ← alg.runWithSigningOracle pk sk (A.main pk)
  let zs ← (List.range its.length).mapM (zQuery red its)
  return aggVerifies C challenge its s zs
```

```lean
/-- The probability that the adversary's aggregate verifies, with a lazily
sampled random oracle. -/
noncomputable def aggVerifyAdvantage [NonceGen n M] (A : AggAdversary n H X M) : ℝ≥0∞ :=
  (ProbCompRuntime.rom (RandSpec H X M)).evalDist (aggVerifyExperiment C challenge red A) {true}
```

```lean
/-- The extractor's `s` for the item `a`: `α*ₐ + β*ₐ⋅x` with `x = (s - α*)/β*`,
the secret key that `extractForgery` computes, and `x = 0` if `β* = 0`. -/
def extractSig (items : List (AItem n X M)) (s : ZMod n) (zs : List (ZMod n))
    (a : AItem n X M) : ZMod n :=
  let α := isum (fun i b => zs.getD i 0 * (starRep challenge b).1) 0 items
  let β := isum (fun i b => zs.getD i 0 * (starRep challenge b).2) 0 items
  (starRep challenge a).1 + (starRep challenge a).2 * ((s - α) / β)
```

```lean
/-- The extractor succeeds: the aggregate passes `VerifyAggregate` with the
randomizers `zs`, and `(rᵢ, sigsᵢ)` passes BIP340 `Verify` for every item
`(rᵢ, pkᵢ, mᵢ)`. -/
def extractWins (its : List (Item X M)) (s : ZMod n) (zs sigs : List (ZMod n)) : Bool :=
  aggVerifies C challenge its s zs &&
    decide (sigs.length = its.length) &&
    (its.zip sigs).all fun p => BIP340.verify C challenge p.1.2.1 p.1.2.2 (p.1.1, p.2)
```

```lean
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
```

```lean
/-- The extraction experiment: the extractor runs with a BIP340 key and its
signing oracle. -/
noncomputable def extractExperiment [NonceGen n M] (F : AlgForger n H E X M) :
    ProbComp Bool := do
  let alg := bip340 (M := M) C challenge ProbComp
  let (pk, sk) ← alg.keygen
  let ((its, s, zs, sigs), _) ← alg.runWithSigningOracle pk sk (extractor C challenge red F pk)
  return extractWins C challenge its s zs sigs
```

```lean
/-- The probability that the extractor succeeds. -/
noncomputable def extractAdvantage [NonceGen n M] (F : AlgForger n H E X M) : ℝ≥0∞ :=
  ProbCompRuntime.probComp.evalDist (extractExperiment C challenge red F) {true}
```

```lean
/-- **Whoever produces a verifying aggregate knows a BIP340 signature for every
item**, in the algebraic group model with the randomizer hash as a random oracle
and for every challenge hash. If the aggregate of an algebraic forger with at
most `q` randomizer requests passes `VerifyAggregate` with probability `ε` in
the game, then `extractor F` outputs an aggregate that verifies, together with
a signature that passes BIP340 `Verify` for every one of its items, with
probability at least `ε - (q + 1)⋅μ`, with `μ` as in `halfagg_unforgeable`.

The forger chooses every public key except the target, so this covers items
under its own keys, which unforgeability does not. `hx0` is the curve
hypothesis of `halfagg_unforgeable`. -/
theorem halfagg_knowledge [NonceGen n M] (hx0 : C.liftX (C.x 0) = none)
    (F : AlgForger n H E X M) (q : ℕ)
    (hq : ∀ input, (F.main input).IsQueryBoundP (fun r => isRand r.value.data) q)
    (μ : ℝ≥0∞) (hμ : RedBound red μ) :
    aggVerifyAdvantage C challenge red (erase C F) ≤
      extractAdvantage C challenge red F + (q + 1 : ℝ≥0∞) * μ
```

```lean
/-- **The extractor signs what the forger signs.** For every set of messages
`p`: if the forger makes at most `q` signing requests for messages in `p`, the
extractor makes at most `q` signing queries for messages in `p`. So it never
obtains a signature from its oracle that the forger did not ask for. -/
theorem extractor_sign_queries (F : AlgForger n H E X M) (p : M → Bool) (q : ℕ)
    (h : ∀ input, (F.main input).IsQueryBoundP (fun r => isSign p r.value.data) q) (pk : X) :
    (extractor C challenge red F pk).IsQueryBoundP (fun t => isSignQuery p t) q
```

### A reduction to discrete log

From `Halfagg/SecurityROM.lean`, `Halfagg/SecurityTight.lean` and `Halfagg/UnforgeabilityTight.lean`, with `finalItems` from `Halfagg/Security.lean`. The challenge hash is a random oracle here. `sigma`, `keyGen`, `dlogExperiment` and `dlogOfKeyRecovery` are taproot-lean's. `FiatShamir.simulatedNmaImpl` and `FiatShamir.Fork.roImpl` are VCVio's: a signing oracle that needs no secret key, and a lazily sampled challenge hash.

```lean
/-- The challenge hash as an oracle on `(m, (r, pk))`, the input order of VCVio's
Fiat-Shamir transform. -/
abbrev ChalSpec (n : ℕ) (X M : Type) := (M × (X × X)) →ₒ ZMod n
```

```lean
/-- The challenge function of a complete answer table. -/
def hOf (g : M × (X × X) → ZMod n) : X → X → M → ZMod n := fun r pk m => g (m, (r, pk))
```

```lean
/-- A forger's oracles: the challenge hash and the requests of an `AlgForger`. -/
abbrev RomForgerSpec (n : ℕ) (H E X M : Type) :=
  ChalSpec n X M + explainedSpec (ZMod n) (Pts E) (Request X M) (Reply n H X M)
```

```lean
/-- Answer challenge-hash queries from the table `g` and pass requests on. -/
def answerChal (g : M × (X × X) → ZMod n) :
    QueryImpl (RomForgerSpec n H E X M)
      (OracleComp (explainedSpec (ZMod n) (Pts E) (Request X M) (Reply n H X M)))
  | .inl key => pure (g key)
  | .inr t => liftM ((explainedSpec (ZMod n) (Pts E) (Request X M) (Reply n H X M)).query t)
```

```lean
/-- An algebraic forger with oracle access to the challenge hash. For every
answer table, the forger with its challenge queries answered from the table is
algebraic. -/
structure RomForger (n : ℕ) (H E X M : Type) [AddCommGroup E] where
  main : Message Unit (Pts E) →
    OracleComp (RomForgerSpec n H E X M) (Explained (ZMod n) (Out n M) (Pts E))
  algebraic : ∀ (g : M × (X × X) → ZMod n) input,
    IsAlgebraic input.groups (simulateQ (answerChal g) (main input))
```

```lean
/-- The forger with its challenge queries answered from the table `g`. -/
def RomForger.at (F : RomForger n H E X M) (g : M × (X × X) → ZMod n) : AlgForger n H E X M where
  main input := simulateQ (answerChal g) (F.main input)
  algebraic := F.algebraic g
```

```lean
/-- Whether a forger's oracle call is a randomizer request. -/
def isRandCall : M × (X × X) ⊕ Explained (ZMod n) (Request X M) (Pts E) → Bool
  | .inl _ => false
  | .inr t => isRand t.value.data
```

```lean
/-- Whether a forger's oracle call is a challenge-hash query. -/
def isChalCall : M × (X × X) ⊕ Explained (ZMod n) (Request X M) (Pts E) → Bool
  | .inl _ => true
  | .inr _ => false
```

```lean
/-- Whether a forger's oracle call is a signing request. -/
def isSignCall : M × (X × X) ⊕ Explained (ZMod n) (Request X M) (Pts E) → Bool
  | .inl _ => false
  | .inr t => isSign (fun _ => true) t.value.data
```

```lean
/-- **The game with the challenge hash as a random oracle**: sample the challenge
hash table, then play the game of `aggExperiment` with it. The randomizer hash is
a lazily sampled random oracle as before. -/
noncomputable def aggExperimentROM [SampleableType (M × (X × X) → ZMod n)]
    (F : RomForger n H E X M) : ProbComp Bool := do
  let g ← $ᵗ (M × (X × X) → ZMod n)
  (simulateQ (RandSpec H X M).romImpl (aggExperiment C (hOf g) red (erase C (F.at g)))).run' ∅
```

```lean
/-- The forger's success probability. -/
noncomputable def aggAdvantageROM [SampleableType (M × (X × X) → ZMod n)]
    (F : RomForger n H E X M) : ℝ≥0∞ :=
  Pr{let b ← aggExperimentROM C red F}[b = true]
```

```lean
/-- The forgery's annotated items, after recording its representations. -/
def finalItems (out : Explained (ZMod n) (Out n M) (Pts E)) (st : Core n X M) :
    List (AItem n X M) :=
  annotate C (memoize C st (out.value.groups ()) (out.coefficients ())).memo
    (toItems C out.value.data.ms (out.value.groups ()))
```

```lean
/-- The target item of a forgery: the first item with the target key and a
message that was never signed, as in `extractForgery`. -/
def target (pk : X) (items : List (AItem n X M)) (signed : List M) : Option (AItem n X M) :=
  items.find? (fun a => a.pk == pk && !signed.contains a.m)
```

```lean
/-- The candidate for the secret key of `pk`, from the target item `a`. Its
representation `(u, v)` of `P*` satisfies `u + v⋅x = x`, so `x = u/(1 - v)` if
`v ≠ 1`. If `v = 1`, the candidate is `(s - α*)/β*` as in `extractForgery`. -/
def candKey (ch : X → X → M → ZMod n) (pk : X) (items : List (AItem n X M)) (s : ZMod n)
    (zs : List (ZMod n)) (signed : List M) : ZMod n :=
  let α := isum (fun i b => zs.getD i 0 * (starRep ch b).1) 0 items
  let β := isum (fun i b => zs.getD i 0 * (starRep ch b).2) 0 items
  match target pk items signed with
  | none => 0
  | some a => if a.repPk.2 = 1 then (s - α) / β else a.repPk.1 / (1 - a.repPk.2)
```

```lean
/-- An oracle machine up to its final step: the forgery's annotated items, `s`,
the randomizers, the signed messages and the challenges of the items. -/
noncomputable def romPrefix (F : RomForger n H E X M) (P : Stmt C) :
    OracleComp (RomSpec n X M)
      (List (AItem n X M) × ZMod n × List (ZMod n) × List M × List (ZMod n)) := do
  let r ← ((simulateQ (romHandler (H := H) C (C.x P.1))
    (F.main (initial C ((C.liftX (C.x P.1)).getD 0)))).run Core.init).run ∅
  let q ← ((List.range (finalItems C r.1.1 r.1.2).length).mapM fun i =>
    if i = 0 then pure 1
    else red <$> romTableRO ((finalItems C r.1.1 r.1.2).take (i + 1))).run r.2
  let es ← (finalItems C r.1.1 r.1.2).mapM fun a => hashQ (n := n) (a.m, (a.r, a.pk))
  pure (finalItems C r.1.1 r.1.2, r.1.1.value.data.s, q.1, r.1.2.signed, es)
```

```lean
/-- **The discrete-log solver.** Run the forger's bookkeeping with VCVio's
simulated signing oracle (`simulatedNmaImpl`, which needs no secret key) and a
lazily sampled challenge hash (`Fork.roImpl`), and output the candidate key. -/
noncomputable def keySolver (F : RomForger n H E X M) (P : Stmt C) : ProbComp (ZMod n) :=
  simulateQ (QueryImpl.ofLift unifSpec ProbComp + uniformSampleImpl (spec := (Unit →ₒ ZMod n)))
    ((fun w => candKey (knownChal w.1.1.1 w.1.1.2.2.2.2) (C.x P.1) w.1.1.1 w.1.1.2.1
        w.1.1.2.2.1 w.1.1.2.2.2.1) <$>
      StateT.run (simulateQ (FiatShamir.Fork.unifForward M (X × X) (ZMod n) +
          FiatShamir.Fork.roImpl M (X × X) (ZMod n))
        ((simulateQ (FiatShamir.simulatedNmaImpl (M := M) (Commit := X × X) (Chal := ZMod n)
          (Resp := ZMod n) (simTranscript C) P) (romPrefix C red F P)).run ∅)) (∅, []))
```

```lean
/-- **The forger explains the nonce of every challenge-hash query.** The `r` of a
query on `(m, (r, pk))` is the x-coordinate of a point that an earlier
randomizer request of the forger carried, and so explained. `seen` lists the
x-coordinates explained so far. -/
def ExplainsNonces {α : Type} (prog : OracleComp (RomForgerSpec n H E X M) α) : List X → Prop :=
  OracleComp.recOn (motive := fun _ => List X → Prop) prog
    (fun _ _ => True)
    (fun t _ next seen =>
      match t, next with
      | .inl key, next => key.2.1 ∈ seen ∧ ∀ e, next e seen
      | .inr q, next => ∀ rep, next rep
          (if isRand q.value.data then (q.value.groups ()).map C.x ++ seen else seen))
```

```lean
/-- **A tight reduction to discrete log.** For a forger that explains the nonce
of every challenge-hash query (`ExplainsNonces`), with at most `q` randomizer
requests, `qH` challenge queries, `qS` signing requests and forgeries of at
most `ℓ` items, and `Q = qH + qS + ℓ + 1`:

`Pr[forger wins] ≤ Pr[keySolver solves discrete log] + qS⋅(qS + Q)⋅2/(n - 1) +
(q + 1)⋅μ + (qH + 1)/n`,

with `μ` as in `halfagg_unforgeable`.

Every loss is additive. The last term bounds the last term of
`halfagg_key_or_signature`: a challenge drawn after the forger explained the
nonce is `-β` with probability `1/n`. -/
theorem halfagg_dlog_tight [Inhabited M] [Finite M] [Finite X]
    [SampleableType (M × (X × X) → ZMod n)] (hx0 : C.liftX (C.x 0) = none)
    (F : RomForger n H E X M) (q qH qS ℓ : ℕ)
    (hq : ∀ input, (F.main input).IsQueryBoundP (fun t => isRandCall t) q)
    (hH : ∀ input, (F.main input).IsQueryBoundP (fun t => isChalCall t) qH)
    (hS : ∀ input, (F.main input).IsQueryBoundP (fun t => isSignCall t) qS)
    (hL : ∀ input, ∀ out ∈ support (F.main input), out.value.data.ms.length ≤ ℓ)
    (hE : ∀ input, ExplainsNonces C (F.main input) [])
    (μ : ℝ≥0∞) (hμ : RedBound red μ) :
    aggAdvantageROM C red F ≤
      Pr{let x ← dlogExperiment C (dlogOfKeyRecovery C (keySolver C red F))}[x = true] +
        (qS : ℝ≥0∞) * (qS + (qH + qS + ℓ + 1 : ℕ)) * (2 / ((n - 1 : ℕ) : ℝ≥0∞)) +
        (q + 1 : ℝ≥0∞) * μ + (qH + 1 : ℝ≥0∞) / n
```

### Binding

From `Halfagg/SecurityBinding.lean` and `Halfagg/Binding.lean`. `PrimeOrder n E` is taproot-lean's: every point `P` satisfies `n⋅P = 0`.

```lean
/-- A binding adversary's oracles: uniform sampling, the challenge hash and the
randomizer hash. -/
abbrev BindSpec (n : ℕ) (H X M : Type) := (unifSpec + ChalSpec n X M) + RandSpec H X M
```

```lean
/-- A binding adversary outputs an aggregate signature and two lists of
`(pk, m)` pairs. -/
structure BindAdversary (n : ℕ) (H X M : Type) where
  main : OracleComp (BindSpec n H X M) (AggSig n X × List (X × M) × List (X × M))
```

```lean
/-- Answer challenge-hash queries from the table `g` and pass the rest on. -/
def answerChalB (g : M × (X × X) → ZMod n) :
    QueryImpl (BindSpec n H X M) (OracleComp (unifSpec + RandSpec H X M))
  | .inl (.inl k) => liftM ((unifSpec + RandSpec H X M).query (.inl k))
  | .inl (.inr key) => pure (g key)
  | .inr L => liftM ((unifSpec + RandSpec H X M).query (.inr L))
```

```lean
/-- The adversary wins if the two lists differ and `VerifyAggregate` accepts the
aggregate for both, with the randomizers `zs` and `zs'`. -/
def bindWins (challenge : X → X → M → ZMod n) (agg : AggSig n X) (pm pm' : List (X × M))
    (zs zs' : List (ZMod n)) : Bool :=
  decide (pm ≠ pm') && verifyWith C challenge (fun i => zs.getD i 0) agg pm &&
    verifyWith C challenge (fun i => zs'.getD i 0) agg pm'
```

```lean
/-- The binding game for a fixed challenge hash: run the adversary, draw the
randomizers of both lists from the randomizer hash and check `bindWins`. -/
noncomputable def bindGame (challenge : X → X → M → ZMod n)
    (A : OracleComp (unifSpec + RandSpec H X M) (AggSig n X × List (X × M) × List (X × M))) :
    OracleComp (unifSpec + RandSpec H X M) Bool := do
  let out ← A
  let zs ← (List.range out.1.rs.length).mapM (zQuery red (items out.2.1 out.1.rs))
  let zs' ← (List.range out.1.rs.length).mapM (zQuery red (items out.2.2 out.1.rs))
  return bindWins C challenge out.1 out.2.1 out.2.2 zs zs'
```

```lean
/-- **The binding game** (CK-ASBS of Chalkias, Garillot, Kondi and Nikolaenko,
for BIP458's scheme), with both hashes as random oracles: sample the challenge
hash table, then play `bindGame` with a lazily sampled randomizer hash. -/
noncomputable def bindExperiment [SampleableType (M × (X × X) → ZMod n)]
    (A : BindAdversary n H X M) : ProbComp Bool := do
  let g ← $ᵗ (M × (X × X) → ZMod n)
  (simulateQ (RandSpec H X M).romImpl
    (bindGame C red (hOf g) (simulateQ (answerChalB g) A.main))).run' ∅
```

```lean
/-- The adversary's success probability. -/
noncomputable def bindAdvantage [SampleableType (M × (X × X) → ZMod n)]
    (A : BindAdversary n H X M) : ℝ≥0∞ :=
  Pr{let b ← bindExperiment C red A}[b = true]
```

```lean
/-- Whether an oracle call is a challenge-hash query. -/
def isChalB : (ℕ ⊕ M × (X × X)) ⊕ List (Item X M) → Bool
  | .inl (.inr _) => true
  | _ => false
```

```lean
/-- Whether an oracle call is a randomizer-hash query. -/
def isRandB : (ℕ ⊕ M × (X × X)) ⊕ List (Item X M) → Bool
  | .inr _ => true
  | _ => false
```

```lean
/-- **Half-aggregation is binding** (Chalkias, Garillot, Kondi and Nikolaenko,
Theorem 6, for BIP458's scheme). With both hashes as random oracles, an
adversary with at most `qC` challenge-hash queries, `qZ` randomizer-hash queries
and aggregates of at most `ℓ` signatures outputs an aggregate that
`VerifyAggregate` accepts for two different lists of `(pk, m)` pairs with
probability at most

`(qC + 2⋅ℓ)²/n + (qZ + 2⋅ℓ)²⋅μ`,

with `μ` as in `halfagg_unforgeable`. The bound is statistical: it needs no
algebraic group model and no hardness assumption.

`hord` says that every point has order dividing `n`. On a curve with a cofactor,
a point of small order would be multiplied by a randomizer to the same point
more often than `μ`. -/
theorem halfagg_binding [Finite M] [Finite X] [SampleableType (M × (X × X) → ZMod n)]
    (hord : PrimeOrder n E) (A : BindAdversary n H X M) (qC qZ ℓ : ℕ)
    (hC : A.main.IsQueryBoundP (fun t => isChalB t) qC)
    (hZ : A.main.IsQueryBoundP (fun t => isRandB t) qZ)
    (hL : ∀ out ∈ support A.main, out.1.rs.length ≤ ℓ) (μ : ℝ≥0∞) (hμ : RedBound red μ) :
    bindAdvantage C red A ≤
      (((qC + 2 * ℓ) * (qC + 2 * ℓ) : ℕ) : ℝ≥0∞) / n +
        (((qZ + 2 * ℓ) * (qZ + 2 * ℓ) : ℕ) : ℝ≥0∞) * μ
```

<!-- definitions:begin -->

## Every definition behind the results

The definitions that the statements of the results in `Halfagg/Summary.lean` depend on, directly or through other definitions: 183 of this project and 260 of the libraries it is built on. `#surface` in `Halfagg/Audit.lean` computes the list from the compiled project, `Halfagg/Summary.lean` guards it, and the build fails if it changes. Proofs are not followed, since what a proof uses does not change what a statement says. The list stops at Lean's core library and at Mathlib. Whoever agrees with these definitions knows what the results say. The ones that are not printed above have to be read in the sources, for the libraries at the commits in `lake-manifest.json`. `scripts/check.sh` fails if the list has a module under `Halfagg/Proofs/`.

**This project**

- `Halfagg/Attacks.lean`: `forgeLate`, `forgeOnes`, `rogue`, `zLate`
- `Halfagg/Basic.lean`: `AggSig`, `Item`, `aggregate`, `entryItem`, `entryPM`, `incAggregate`, `isum`, `items`, `lifts`, `shiftedPair`, `term`, `verifyAggregate`, `verifyMulti`, `verifyWith`, `z`
- `Halfagg/BytesGame.lean`: `Security.AggAdversaryB`, `Security.aggAdvantageB`, `Security.aggExperimentB`, `Security.parseOut`, `Security.romProb`, `Security.serB`, `Security.serOut`, `Security.toStruct`
- `Halfagg/BytesSecurity.lean`: `Security.B32`, `Security.challengeX`, `Security.decodeX`, `Security.encX`, `Security.instDecidableEqB32`, `Security.instInhabitedB32`, `Security.int256`, `Security.itemBytes`, `Security.randHash256`, `Security.randomizerX`, `Security.secp256k1X`, `Security.to32`
- `Halfagg/Encoding.lean`: `Vectors.Item32`, `Vectors.decodeVerify`, `Vectors.encodeItem`, `Vectors.randomizerInput`
- `Halfagg/Hash256.lean`: `Security.RepBound`, `Security.red256`, `Security.redMod`, `Security.rep256`, `Security.repMod`
- `Halfagg/OrderG.lean`: `secp256k1F`
- `Halfagg/Security.lean`: `Security.AItem`, `Security.AggAdversary`, `Security.AlgForger`, `Security.AnnSpec`, `Security.Core`, `Security.GameSpec`, `Security.NonceGen`, `Security.Out`, `Security.Pts`, `Security.RandSpec`, `Security.RedBound`, `Security.Rep`, `Security.Reply`, `Security.Request`, `Security.SignSpec`, `Security.aggAdvantage`, `Security.aggExperiment`, `Security.aggWins`, `Security.annotate`, `Security.bip340`, `Security.coreImpl`, `Security.erase`, `Security.eraseImpl`, `Security.extractForgery`, `Security.finalItems`, `Security.flatten`, `Security.initial`, `Security.instDecidableEqAItem`, `Security.isRand`, `Security.isSign`, `Security.isSignQuery`, `Security.liftRep`, `Security.memoRecord`, `Security.memoize`, `Security.memoizeList`, `Security.pairs`, `Security.rawTail`, `Security.reduction`, `Security.smulVal`, `Security.starRep`, `Security.tableRO`, `Security.tableZs`, `Security.toItems`, `Security.zQuery`, `Security.Core.init`, `Security.NonceGen.uniform`, `Security.instDecidableEqAItem.decEq`
- `Halfagg/SecurityBinding.lean`: `Security.BindAdversary`, `Security.BindSpec`, `Security.answerChalB`, `Security.bindAdvantage`, `Security.bindExperiment`, `Security.bindGame`, `Security.bindWins`, `Security.isChalB`, `Security.isRandB`
- `Halfagg/SecurityHashed.lean`: `Security.BindAdversaryH`, `Security.BindSpecH`, `Security.ChalSpecH`, `Security.ExplainsNoncesH`, `Security.RomForgerH`, `Security.RomForgerSpecH`, `Security.aggAdvantageROMH`, `Security.aggExperimentROMH`, `Security.answerChalBH`, `Security.answerChalH`, `Security.bindAdvantageH`, `Security.bindExperimentH`, `Security.repChal`, `Security.repChalB`, `Security.BindAdversaryH.viaRep`, `Security.RomForgerH.at`, `Security.RomForgerH.viaRep`
- `Halfagg/SecurityKnowledge.lean`: `Security.aggVerifies`, `Security.aggVerifyAdvantage`, `Security.aggVerifyExperiment`, `Security.extractAdvantage`, `Security.extractExperiment`, `Security.extractSig`, `Security.extractWins`, `Security.extractor`
- `Halfagg/SecurityROM.lean`: `LoggedRun.tableImpl`, `Security.ChalSpec`, `Security.FSSig`, `Security.RomForger`, `Security.RomForgerSpec`, `Security.RomSpec`, `Security.aggAdvantageROM`, `Security.aggExperimentROM`, `Security.answerChal`, `Security.extractROM`, `Security.hOf`, `Security.hashQ`, `Security.isChalCall`, `Security.isRandCall`, `Security.isSignCall`, `Security.knownChal`, `Security.reductionROM`, `Security.romHandler`, `Security.romTableRO`, `Security.RomForger.at`
- `Halfagg/SecurityTight.lean`: `Security.ExplainsNonces`, `Security.FinalStep`, `Security.candKey`, `Security.junk`, `Security.keySolver`, `Security.repFin`, `Security.romMachine`, `Security.romPrefix`, `Security.target`
- `Halfagg/Tightness.lean`: `Security.copies`, `Security.grindLoop`, `Security.grinder`, `Security.gβ`
- `Halfagg/Unforgeability.lean`: `Security.answerRand`
- `Halfagg/VectorData.lean`: `Vectors.aggregateVectors`, `Vectors.incAggregateVectors`, `Vectors.verifyVectors`
- `Halfagg/VectorTypes.lean`: `Vectors.AggregateVector`, `Vectors.IncAggregateVector`, `Vectors.VerifyVector`
- `Halfagg/Vectors.lean`: `Vectors.aggregateBytes`, `Vectors.bip340VerifyBytes`, `Vectors.chunks32`, `Vectors.incAggregateBytes`, `Vectors.is32`, `Vectors.pmOf`, `Vectors.pmsOf`, `Vectors.randomizer`, `Vectors.randomizerF`, `Vectors.verifyAggregateBytes`
- `Halfagg/Winnable.lean`: `Security.bettor`, `Security.bettorRom`, `Security.bettorRomH`

**taproot-lean**

- `Taproot/BIP340.lean`: `Taproot.BIP340.sign`, `Taproot.BIP340.verify`
- `Taproot/BIP340Props.lean`: `Taproot.BIP340.Entry`, `Taproot.BIP340.Entry.valid`
- `Taproot/BIP340Security.lean`: `Taproot.BIP340Security.Good`, `Taproot.BIP340Security.NonzeroScalar`, `Taproot.BIP340Security.Stmt`, `Taproot.BIP340Security.dlogExperiment`, `Taproot.BIP340Security.dlogOfKeyRecovery`, `Taproot.BIP340Security.instSampleableTypeGoodValMemSetStmt`, `Taproot.BIP340Security.instSampleableTypeNonzeroScalar`, `Taproot.BIP340Security.keyGen`, `Taproot.BIP340Security.negStmt`, `Taproot.BIP340Security.sigma`, `Taproot.BIP340Security.simTranscript`
- `Taproot/BIP340Vectors.lean`: `Taproot.BIP340Vectors.Bytes`, `Taproot.BIP340Vectors.be32`, `Taproot.BIP340Vectors.bytes32`, `Taproot.BIP340Vectors.challenge`, `Taproot.BIP340Vectors.hex`, `Taproot.BIP340Vectors.rotr`, `Taproot.BIP340Vectors.sha256`, `Taproot.BIP340Vectors.sha256Block`, `Taproot.BIP340Vectors.sha256H0`, `Taproot.BIP340Vectors.sha256K`, `Taproot.BIP340Vectors.sha256Pad`, `Taproot.BIP340Vectors.taggedHash`, `Taproot.BIP340Vectors.toNatBE`, `Taproot.BIP340Vectors.hex.go`
- `Taproot/Curve.lean`: `Taproot.Curve`, `Taproot.Curve.PrimeOrder`, `Taproot.Curve.evenScalar`, `Taproot.Curve.mulG`
- `Taproot/Secp256k1.lean`: `Taproot.Secp256k1.F`, `Taproot.Secp256k1.G`, `Taproot.Secp256k1.Gx`, `Taproot.Secp256k1.Gy`, `Taproot.Secp256k1.Point`, `Taproot.Secp256k1.W`, `Taproot.Secp256k1.evenRoot`, `Taproot.Secp256k1.hasEvenY`, `Taproot.Secp256k1.liftX`, `Taproot.Secp256k1.n`, `Taproot.Secp256k1.p`, `Taproot.Secp256k1.sqrtExp`, `Taproot.Secp256k1.xCoord`

**agm-lean**

- `AlgebraicGroupModel/Interaction.lean`: `AlgebraicGroupModel.Interaction.Adversary`, `AlgebraicGroupModel.Interaction.Explained`, `AlgebraicGroupModel.Interaction.Groups`, `AlgebraicGroupModel.Interaction.IsAlgebraic`, `AlgebraicGroupModel.Interaction.Message`, `AlgebraicGroupModel.Interaction.evaluate`, `AlgebraicGroupModel.Interaction.explainedSpec`, `AlgebraicGroupModel.Interaction.extend`, `AlgebraicGroupModel.Interaction.plainSpec`, `AlgebraicGroupModel.Interaction.Explained.Valid`, `AlgebraicGroupModel.Interaction.Explained.ofVectors`

**VCVio**

- `VCVio/CryptoFoundations/ReplayFork.lean`: `OracleComp.ContextForkWitness`, `OracleComp.acceptContextForkWitness`, `OracleComp.classifyForkView`, `OracleComp.contextFork`, `OracleComp.contextForkWitness`
- `VCVio/CryptoFoundations/SigmaProtocol.lean`: `ChallengeVerifyProtocol`, `SigmaProtocol`
- `VCVio/CryptoFoundations/SignatureAlg.lean`: `SignatureAlg`, `SignatureAlg.ManagedRoNmaAdversary`, `SignatureAlg.UnforgeableAdversary`, `SignatureAlg.map_correctnessGame`, `SignatureAlg.runWithSigningOracle`, `SignatureAlg.signingOracle`, `SignatureAlg.unforgeableAdvantage`, `SignatureAlg.unforgeableExperiment`
- `VCVio/EvalDist/ProbabilityNotation.lean`: `prEvent`
- `VCVio/OracleComp/OracleComp.lean`: `OracleComp`, `OracleComp.queryBind`
- `VCVio/OracleComp/OracleQuery.lean`: `OracleQuery`, `OracleQuery.cont`, `OracleQuery.input`, `OracleSpec.query`
- `VCVio/OracleComp/OracleSpec.lean`: `OracleSpec`, `unifSpec`, `OracleSpec.Domain`, `OracleSpec.Range`, `OracleSpec.instDecidableEqRangeSumHAdd`, `OracleSpec.instFintypeRangeSumHAdd`, `OracleSpec.instHAddSum`, `OracleSpec.ofFn`, `OracleSpec.ofPFunctor`, `OracleSpec.toPFunctor`
- `VCVio/OracleComp/ProbCompLift.lean`: `ProbCompLift`, `ProbCompRuntime`, `ProbCompLift.id`, `ProbCompLift.ofMonadLift`, `ProbCompRuntime.evalDist`, `ProbCompRuntime.probComp`
- `VCVio/CryptoFoundations/FiatShamir/QueryBounds.lean`: `FiatShamir.challengeSpaceInv`, `FiatShamir.hashQueryBound`, `FiatShamir.signHashQueryBound`
- `VCVio/CryptoFoundations/FiatShamir/Sigma.lean`: `FiatShamir`, `FiatShamir.inROM`, `FiatShamir.runtime`, `FiatShamir.runtimeWithCache`
- `VCVio/CryptoFoundations/HardnessAssumptions/HardRelation.lean`: `GenerableRelation`
- `VCVio/EvalDist/PFunctorMeasure/Core.lean`: `PFunctor.AnswerMeasure`, `PFunctor.FreeM.denote`, `PFunctor.FreeM.instEvalDistSemanticsFreeM`
- `VCVio/OracleComp/EvalDist/AnswerMeasure.lean`: `OracleComp.instEvalDistSemantics`, `OracleSpec.AnswerMeasure`, `OracleSpec.UniformAnswerMeasure`, `OracleSpec.UniformAnswerMeasure.ofFiniteNonempty`, `OracleSpec.UniformAnswerMeasure.unifSpec`
- `VCVio/OracleComp/HasQuery/Basic.lean`: `HasQuery`, `HasQuery.instOfMonadLift`
- `VCVio/OracleComp/ProbComp/Basic.lean`: `ProbComp`, `ProbComp.uniformFin`
- `VCVio/OracleComp/QueryTracking/CachingOracle.lean`: `QueryImpl.withCaching`
- `VCVio/OracleComp/QueryTracking/Structures.lean`: `OracleSpec.QueryCache`, `OracleSpec.QueryLog`, `OracleSpec.QueryCache.cacheQuery`, `OracleSpec.QueryCache.instEmptyCollection`, `OracleSpec.QueryCache.ofFn`, `OracleSpec.QueryCache.toSet`, `OracleSpec.QueryLog.getQ`, `OracleSpec.QueryLog.wasQueried`
- `VCVio/OracleComp/SimSemantics/SimulateQ.lean`: `simulateQ`, `simulateQ'`
- `VCVio/CryptoFoundations/FiatShamir/Sigma/CmaToNma.lean`: `FiatShamir.cmaOracleSpec`, `FiatShamir.fsRoSpec`, `FiatShamir.simulatedNmaAdv`, `FiatShamir.simulatedNmaBaseSim`, `FiatShamir.simulatedNmaFwd`, `FiatShamir.simulatedNmaImpl`, `FiatShamir.simulatedNmaRoSim`, `FiatShamir.simulatedNmaSigSim`, `FiatShamir.simulatedNmaUnifSim`
- `VCVio/CryptoFoundations/FiatShamir/Sigma/Fork.lean`: `FiatShamir.Fork.SimState`, `FiatShamir.Fork.Trace`, `FiatShamir.Fork.forkPoint`, `FiatShamir.Fork.roImpl`, `FiatShamir.Fork.runTrace`, `FiatShamir.Fork.unifForward`, `FiatShamir.Fork.wrappedChallengeQuery`, `FiatShamir.Fork.wrappedSpec`, `FiatShamir.Fork.wrappedUniformQuery`, `FiatShamir.Fork.Trace.target`
- `VCVio/CryptoFoundations/FiatShamir/Sigma/Reductions.lean`: `FiatShamir.cmaReduction`, `FiatShamir.cmaToNmaAdv`, `FiatShamir.nmaForkBudget`, `FiatShamir.nmaForkExtract`, `FiatShamir.nmaForkExtractBranch`, `FiatShamir.nmaReduction`
- `VCVio/EvalDist/Defs/Measure/Core.lean`: `EvalDistSemantics`, `evalDist`
- `VCVio/EvalDist/Defs/Semantics/Core.lean`: `SemanticsVia`, `SemanticsVia.evalDist`, `SemanticsVia.ofEvalDistSemantics`
- `VCVio/OracleComp/Coercions/Add/Basic.lean`: `OracleQuery.subSpec_add_assoc`, `OracleQuery.subSpec_add_left`, `OracleQuery.subSpec_add_right`
- `VCVio/OracleComp/Coercions/SubSpec/Basic.lean`: `OracleComp.instMonadLiftOfOracleQuery`, `OracleComp.instMonadLiftStateTOfOracleQuery`, `OracleComp.liftComp`, `OracleSpec.SubSpec`, `OracleSpec.SubSpec.liftM_eq_lift`
- `VCVio/OracleComp/Constructions/SampleableType/Basic.lean`: `SampleableType`, `instFinEnumZModOfNeZeroNat_vCVio`, `instSampleableTypeFinOfNeZeroNat`, `uniformSample`, `uniformSampleImpl`, `FinEnum.SampleableType`, `SampleableType.Fin`, `SampleableType.ofEquiv`, `SampleableType.ofFintype`, `SampleableType.subtype`
- `VCVio/OracleComp/QueryTracking/LoggingOracle/Core.lean`: `QueryImpl.withLogging`
- `VCVio/OracleComp/QueryTracking/QueryBound/Basic.lean`: `OracleComp.IsQueryBound`, `OracleComp.IsQueryBoundP`
- `VCVio/OracleComp/QueryTracking/RandomOracle/Basic.lean`: `OracleSpec.randomOracle`
- `VCVio/OracleComp/QueryTracking/RandomOracle/Simulation.lean`: `unifFwdImpl`, `OracleSpec.romImpl`, `ProbCompRuntime.rom`
- `VCVio/OracleComp/QueryTracking/Tracing/Core.lean`: `QueryImpl.withTraceAppend`
- `VCVio/OracleComp/SimSemantics/Append/Core.lean`: `OracleSpec.passthrough`, `QueryImpl.Passthrough`, `QueryImpl.add`, `QueryImpl.instHAddPassthroughSumHAddOracleSpecOfMonadLiftTOracleComp`, `QueryImpl.instHAddSumHAddOracleSpec`
- `VCVio/OracleComp/SimSemantics/QueryImpl/Basic.lean`: `QueryImpl`, `HasQuery.toQueryImpl`, `QueryImpl.id`, `QueryImpl.id'`, `QueryImpl.liftTarget`, `QueryImpl.ofFn`, `QueryImpl.ofLift`
- `VCVio/OracleComp/SimSemantics/StateT/BundledSemantics.lean`: `ProbCompRuntime.withStateOracle`, `SemanticsVia.withStateOracle`
- `VCVio/CryptoFoundations/FiatShamir/Sigma/Stateful/Bridge.lean`: `FiatShamir.Stateful.SourceAdversary`, `FiatShamir.Stateful.SourceSigAlg`
- `VCVio/CryptoFoundations/FiatShamir/Sigma/Stateful/Chain/Simulation.lean`: `FiatShamir.Stateful.nmaAdvFromCma`, `FiatShamir.Stateful.nmaAdvFromCmaWithFinalQuery`

**PolyFun**

- `PolyFun/PFunctor/Basic.lean`: `PFunctor.sum`
- `PolyFun/PFunctor/Bound.lean`: `PFunctor.FreeM.IsRollBound`
- `PolyFun/PFunctor/Handler.lean`: `PFunctor.Handler`
- `PolyFun/Control/Monad/Hom.lean`: `MonadHom`, `NatHom`, `MonadHom.id`, `MonadHom.ofLift`
- `PolyFun/Control/Monad/Support.lean`: `MonadAttach.support`
- `PolyFun/PFunctor/Free/Cursor.lean`: `PFunctor.FreeM.Cursor`, `PFunctor.FreeM.Cursor.Spine`, `PFunctor.FreeM.Cursor.plug`, `PFunctor.FreeM.Cursor.Spine.plug`
- `PolyFun/PFunctor/Free/Displayed.lean`: `PFunctor.FreeM.Displayed`, `PFunctor.FreeM.Displayed.Algebra`
- `PolyFun/PFunctor/Free/Path.lean`: `PFunctor.FreeM.Path`, `PFunctor.FreeM.output`, `PFunctor.FreeM.Path.algebra`
- `PolyFun/PFunctor/Free/Support.lean`: `PFunctor.FreeM.attachSupp`, `PFunctor.FreeM.instMonadAttach`, `PFunctor.FreeM.supp`
- `PolyFun/PFunctor/Handler/Instrumentation.lean`: `PFunctor.Handler.liftTarget`, `PFunctor.Handler.postInsert`, `PFunctor.Handler.withTraceAppend`
- `PolyFun/PFunctor/Free/Cursor/Fork.lean`: `PFunctor.FreeM.Cursor.Located`, `PFunctor.FreeM.Cursor.SelectedForkView`, `PFunctor.FreeM.Cursor.filterMapLocateAndForkSelected`, `PFunctor.FreeM.Cursor.locateAndForkBy`, `PFunctor.FreeM.Cursor.locateAndForkSelected`, `PFunctor.FreeM.Cursor.locateAt?`, `PFunctor.FreeM.Cursor.Located.fork`, `PFunctor.FreeM.Cursor.Located.here`, `PFunctor.FreeM.Cursor.Located.prependOther`, `PFunctor.FreeM.Cursor.Located.prependSame`, `PFunctor.FreeM.Cursor.SelectedForkView.firstOutput`, `PFunctor.FreeM.Cursor.SelectedForkView.outputs`, `PFunctor.FreeM.Cursor.SelectedForkView.secondOutput`
- `PolyFun/PFunctor/Free/Cursor/Occurrence.lean`: `PFunctor.FreeM.Cursor.ForkView`, `PFunctor.FreeM.Cursor.Occurrence`, `PFunctor.FreeM.Cursor.ForkView.firstAnswer`, `PFunctor.FreeM.Cursor.ForkView.firstPath`, `PFunctor.FreeM.Cursor.ForkView.secondAnswer`, `PFunctor.FreeM.Cursor.ForkView.secondPath`, `PFunctor.FreeM.Cursor.Occurrence.Completion`, `PFunctor.FreeM.Cursor.Occurrence.plug`, `PFunctor.FreeM.Cursor.Occurrence.resume`, `PFunctor.FreeM.Cursor.Occurrence.toCursor`, `PFunctor.FreeM.Cursor.Occurrence.toSpine`, `PFunctor.FreeM.Cursor.Occurrence.Completion.path`
- `PolyFun/PFunctor/Free/Path/Execution.lean`: `PFunctor.FreeM.withPath`

**cslib**

- `Cslib/Foundations/Data/PFunctor/Free.lean`: `PFunctor.FreeM`, `PFunctor.FreeM.bind`, `PFunctor.FreeM.instBind`, `PFunctor.FreeM.instFunctor`, `PFunctor.FreeM.instMonad`, `PFunctor.FreeM.instMonadLiftObj`, `PFunctor.FreeM.instPure`, `PFunctor.FreeM.lift`, `PFunctor.FreeM.liftM`, `PFunctor.FreeM.liftObj`, `PFunctor.FreeM.map`

<!-- definitions:end -->
