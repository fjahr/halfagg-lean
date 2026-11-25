# Reviewing halfagg-lean

Lean checks the proofs. A reviewer checks that the statements say what they should. Everything under `Halfagg/Proofs/` can stay unread, because a wrong proof does not compile. A wrong definition does. [Every definition behind the results](#every-definition-behind-the-results) lists all definitions that a result depends on, in this project and in the libraries it is built on. The list is computed from the compiled project, and the build fails if it changes.

## What to read

About 1,400 lines decide whether the results mean anything. [The statements](#the-statements) at the end of this file prints most of them on one page.

1. `Halfagg/Basic.lean`, the definitions. Compare `incAggregate`, `aggregate` and `verifyWith` with the algorithms in BIP 458.
2. `Halfagg/Security.lean`, all of it, and `Halfagg/Hash256.lean`. The header lists the modelling choices and the limitations.
3. `Halfagg/Unforgeability.lean`, the theorem statements.
4. `Halfagg/SecurityROM.lean` and the statements in `Halfagg/UnforgeabilityROM.lean`, for the version with the challenge hash as a random oracle.
5. `Halfagg/SecurityKnowledge.lean` and the statements in `Halfagg/Knowledge.lean`, for the signatures under keys the forger chose.
6. `Halfagg/SecurityTight.lean` and the statements in `Halfagg/UnforgeabilityTight.lean`, for the reduction to discrete log without forking.
7. `Halfagg/SecurityBinding.lean` and the statement in `Halfagg/Binding.lean`, for binding.

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

**How is the randomizer hash reduced mod `n`?** The oracle returns a uniform element of a type `H`, and the game and the reduction turn it into a scalar with `red`. The forger sees the unreduced output. The theorems hold for every `H` and `red` and lose `μ` per randomizer, where `RedBound red μ` says that `red` of a uniform output is a given scalar with probability at most `μ`. For secp256k1, `H` is `Fin (2^256)`, `red256` is `int(⋅) mod n` and `μ = 2/2^256`, because `2^256 ≤ 2n` (`secp256k1_redBound`). `grinder_advantage` and `demo` use the uniform model, `H = ZMod n` with `μ = 1/n`.

**What does `ExplainsNonces` ask of the forger?** That it sends a nonce point in a randomizer request before it asks for a challenge with that nonce. The reduction records explanations from randomizer requests only, so this fixes the coefficient `β` of the target key in the nonce point before the challenge `e` is drawn, and `e = -β` has probability `1/n`. Without it, a forger that hashes a raw x-coordinate can choose its explanation after it has seen `e`, and `halfagg_key_or_signature` leaves that probability as a term. The request can be for the empty list and counts toward `q`. For plain Schnorr signatures, [Fuchsbauer, Plouviez and Seurin](https://eprint.iacr.org/2019/877) have a tight reduction in the same model.

**What does binding add to unforgeability?** Unforgeability protects one honest key. `halfagg_binding` is about an adversary that chooses every key: it cannot produce an aggregate that `VerifyAggregate` accepts for two lists that differ in a key or a message. BIP 458 does not state this. The bound is statistical, with both hashes as random oracles. The challenge hash has to be one because a one-signature aggregate has no randomizer, so its binding is BIP 340's own. Binding says nothing about which signatures went into the aggregate (`aggregate_accepts_invalid`).

**What connects the theorems to BIP 458's bytes?** `Halfagg/BytesSecurity.lean` instantiates them for secp256k1 with 32-byte arrays as nonces, public keys and messages (`bytes_halfagg_unforgeable` and three more). The x-only encoding of a point is `bytes(x(P))`, and an array that is not below `p` does not lift. The challenge hash is BIP 340's tagged SHA-256. The randomizer oracle answers with 256-bit values that the scheme reduces mod `n`, and BIP 458's randomizer is such a function: SHA-256 has 32 bytes of output (`length_sha256`, `randomizerX_eq_red256`), and its input determines the item list (`randHash256_input_injective`). `verifyAggregateBytes_eq_X` says that `VerifyAggregate` on bytes is the parsing and the checks followed by the verifier of this instance, on the 32-byte chunks of the input (`decodeX_bytes`). `bytes_game_verifier` puts these together: with SHA-256 as the randomizer hash, the game's check of a forgery is `VerifyAggregate` on bytes.

**Are the theorems vacuous?** A bound on forgers says nothing about a game that nobody can win, and a mistake in a definition could make a game like that. `Halfagg/Winnable.lean` has a forger that wins. `bettor` bets that the secret key is `1` and signs with it. It wins the standard game with positive probability, for every randomizer hash, every reduction of its outputs and every nonce derivation (`bettor_advantage_pos`). Its aggregate verifies in the game of the knowledge theorem (`bettor_verify_pos`), and `bettorRom` wins the game with the challenge hash as a random oracle (`bettorRom_advantage_pos`). `bettor_bound` and `bettorRom_bound` are `halfagg_unforgeable` and `halfagg_dlog_tight` applied to these forgers, so the hypotheses of both theorems, `ExplainsNonces` among them, hold for a forger that wins. The curve hypothesis `hx0` holds for secp256k1 (`Halfagg/Proofs/Secp256k1.lean`). `grinder_advantage` shows that the bound cannot be improved by more than one query. There is no such forger for the binding game, where winning means a collision.

## BIP 458's claims

What BIP 458 says about correctness and security, and the theorem for it.

| BIP 458 | Lean |
|---|---|
| Motivation: a verifier that accepts the aggregate "can be sure that the individual signatures would have passed verification". | Not for the signatures given to `Aggregate` (`aggregate_accepts_invalid`). What holds: the owner of an honest key signed its message (`halfagg_unforgeable`), and whoever produced the aggregate knew a BIP 340 signature for every item (`halfagg_knowledge`). |
| Rationale: Chen and Zhao's tight proof in the random oracle and algebraic group model. | `halfagg_unforgeable`, with loss `(q + 1)·μ`, which is `(q + 1)·2/2^256` for BIP 458's hash. `grinder_advantage` shows the loss is tight for a hash that is uniform in `ZMod n`. `halfagg_unforgeable_rom` and `halfagg_dlog` have the challenge hash as a random oracle too, and `halfagg_dlog_tight` reaches discrete log with additive losses only. |
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
- The challenge hash answers uniformly in `ZMod n`, as in taproot-lean's proof of BIP 340. BIP 340 reduces a 256-bit hash mod `n`. For secp256k1 that is about `2^-127.65` from uniform per answer, and the bounds leave this term out. The randomizer hash is modelled as BIP 458 computes it.
- In the instance for 32-byte arrays a query to the randomizer hash is a list of items of 32-byte arrays, not the byte string that BIP 458 hashes, and the forger outputs items and a scalar, not `aggsig` as one byte string. No theorem has a random oracle on byte strings or a forger that outputs bytes of any length.
- No theorem says that the functions on bytes in `Halfagg/Vectors.lean` are BIP 458's algorithms. The 53 test vectors and the differential test compare them with `halfagg.py`.

## Machine checks

- `lake build` compiles every proof and fails if the axioms of a main result change (`Halfagg/Summary.lean`).
- `Halfagg/Summary.lean` also guards two inventories of the whole project, computed by the commands of `Halfagg/Audit.lean`. `#project_axioms` lists the axioms that the modules declare and that their declarations depend on, so an axiom that no main result uses fails the build too. `#surface` lists the definitions behind the results, which is the last section of this file.
- `scripts/check.sh` reads every Lean file of the repository for `sorry`, axioms, unsafe code and compiled evaluation outside the test vector checks. It checks that the root module has only imports and the generated summary only guarded commands. It checks that every code block under [The statements](#the-statements) is in the sources word for word, and that `Halfagg/Summary.lean` checks the axioms of every theorem printed there and of every result in the README's tables. It finds a result by its full name, so a declaration with the same last name in another namespace does not count. It checks that the list of definitions at the end of this file is the one the summary guards, and that no definition on it is under `Halfagg/Proofs/`.
- `scripts/check_selftest.sh` changes a copy of the sources in twelve ways, such as an axiom in the root module or in the summary, and checks that `scripts/check.sh` fails each time.
- `scripts/replay.sh` replays in the kernel with `leanchecker`, without the elaborator, every project module and every module of taproot-lean and agm-lean that the project imports, one process per module. It rejects a module that adds a false theorem behind the kernel's back, which `#print axioms` does not notice.
- `scripts/replay.sh --deps` does the same for the 255 modules of VCVio, PolyFun and cslib that the project imports. A CI workflow of its own runs it when a pinned commit or the toolchain changes, and once a week. Mathlib and the libraries under it are not replayed here.
- CI runs all of these. It also regenerates the summary and the test vector data, runs 300 cases of `scripts/fuzz.py` against the Python reference with a new seed for every run, and checks that the build fails when an unused axiom is added to a module.
- A second CI job builds libsecp256k1 with the `schnorrsig_halfagg` module at the commit the README names. It runs the module's unit tests and 3,000 cases of `scripts/fuzz.py` against the Python reference with a new seed.

### Mutants of the model

`scripts/mutate_model.py` changes one definition at a time in a copy of the project and builds it. A mutant that still built would show that no theorem depends on the detail it changes. All 18 fail. A second CI workflow runs it on every push. Lake does not build what depends on a module that failed, so the table names the declarations nearest to the changed definition, which are often lemmas and not main theorems.

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
| Every 256-bit hash output reduces to the scalar `0` | `redMod_bound` |
| The verification game of the knowledge theorem accepts every aggregate | `extract_all_or_bad`, `fail_sum_all` |
| The game with a challenge oracle verifies with the challenges `0` | `halfagg_unforgeable_rom`, `halfagg_dlog` |
| Challenge-hash queries are not counted | `romHandler_bound` |
| Every forger counts as explaining its nonces | `demoRom_explains`, `explains_chal` |
| The binding adversary wins with the same list twice | `win_pair` |
| The challenge hash on 32-byte arrays hashes the public key before the nonce | `challengeX_encX` |
| `VerifyAggregate` on bytes accepts an `s` that is not below `n` | `decodeVerify_some`, `verifyAggregateBytes_encode`, `incAggregateBytes_isSome`, `verifyAggregateBytes_unique` |
| The randomizer hash does not cover the messages | `aggregate_vectors`, `incAggregate_vectors`, `verifyAggregate_vectors` |

For the two randomizer mutants there is more than a proof that fails: `forgeOnes_verifies` and `forgeLate_verifies` are forgeries against these verifiers. The mutants change four definitions in the same way: `zQuery` of the game and `tableZs` of the reduction in `Halfagg/Security.lean`, and `zQueryAnn` and `zOf` of the proof in `Halfagg/Proofs/Annotated.lean`. A mutant of `z` in `Halfagg/Basic.lean` does not reach the security proof, because it already breaks `z_append` in the same file.

## The statements

The definitions and theorem statements a reviewer has to agree with, copied from the sources with their comments. Proofs are left out.

Throughout, `n` is a prime, `E` is the group of curve points, `X` is the type of x-only encodings, `M` is the message type and `H` is the type of the randomizer hash's outputs. `C : Curve n E X` is taproot-lean's curve interface, `challenge : X → X → M → ZMod n` is the BIP 340 challenge hash and `red : H → ZMod n` turns a randomizer hash output into a scalar.

Not printed here: the parts of the two reductions (`coreImpl`, `extractForgery`, `romHandler`, `extractROM` and their helpers, in `Halfagg/Security.lean` and `Halfagg/SecurityROM.lean`), the grinding forger (`Halfagg/Tightness.lean`), and the definitions of taproot-lean, VCVio and agm-lean at the commits pinned in `lakefile.toml`.

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

### Forgeries against weakened verifiers

From `Halfagg/Attacks.lean`. `verifyWith` is printed above: `VerifyAggregate` with the randomizers as a parameter.

```lean
/-- The forger's nonce point `w⋅G - c⋅P`. -/
def rogue (P : E) (c w : ZMod n) : E := C.mulG w - c.val • P
```

```lean
/-- The forgery against the verifier with every randomizer `1`, for the public
key `pk` with point `P` and the message `m`. The forger picks the scalars `k`,
`a` and `w` and the message `m'`. -/
def forgeOnes (pk : X) (P : E) (m m' : M) (k a w : ZMod n) : AggSig n X × List (X × M) :=
  let r₀ := C.x (C.mulG k)
  let e₀ := challenge r₀ pk m
  let r₁ := C.x (rogue C P e₀ w)
  let pk₁ := C.x (C.mulG a)
  let e₁ := challenge r₁ pk₁ m'
  (⟨[r₀, r₁], C.evenScalar k + w + e₁ * C.evenScalar a⟩, [(pk, m), (pk₁, m')])
```

```lean
/-- **Without randomizers anyone forges.** If the forger's nonce point is not
`0` and has an even y-coordinate, its aggregate for `(pk, m)` passes the
verifier with every randomizer `1`. -/
theorem forgeOnes_verifies {pk : X} {P : E} (hP : C.liftX pk = some P) (m m' : M)
    {k a : ZMod n} (hk : k ≠ 0) (ha : a ≠ 0) (w : ZMod n)
    (hQ : rogue C P (challenge (C.x (C.mulG k)) pk m) w ≠ 0)
    (he : C.hasEvenY (rogue C P (challenge (C.x (C.mulG k)) pk m) w) = true) :
    verifyWith C challenge (fun _ => 1) (forgeOnes C challenge pk P m m' k a w).1
      (forgeOnes C challenge pk P m m' k a w).2 = true
```

```lean
/-- Randomizers that hash only the items before their own: `zᵢ` is the hash of
the items `0, …, i - 1`. -/
def zLate (rand : List (Item X M) → ZMod n) (its : List (Item X M)) (i : ℕ) : ZMod n :=
  if i = 0 then 1 else rand (its.take i)
```

```lean
/-- The forgery against the verifier with the randomizers `zLate`. The forger
knows `z₁`, the hash of its first item, before it chooses the second item. -/
def forgeLate (rand : List (Item X M) → ZMod n) (pk : X) (P : E) (m m' : M) (k a w : ZMod n) :
    AggSig n X × List (X × M) :=
  let r₀ := C.x (C.mulG k)
  let e₀ := challenge r₀ pk m
  let z₁ := rand [(r₀, pk, m)]
  let r₁ := C.x (rogue C P (z₁⁻¹ * e₀) w)
  let pk₁ := C.x (C.mulG a)
  let e₁ := challenge r₁ pk₁ m'
  (⟨[r₀, r₁], C.evenScalar k + z₁ * (w + e₁ * C.evenScalar a)⟩, [(pk, m), (pk₁, m')])
```

```lean
/-- **A randomizer must cover its own item.** If `z₁` is not `0` and the
forger's nonce point is not `0` and has an even y-coordinate, its aggregate for
`(pk, m)` passes the verifier with the randomizers `zLate`. `hn` holds for every
key that is a multiple of `G`. -/
theorem forgeLate_verifies (rand : List (Item X M) → ZMod n) {pk : X} {P : E}
    (hP : C.liftX pk = some P) (hn : n • P = 0) (m m' : M) {k a : ZMod n} (hk : k ≠ 0)
    (ha : a ≠ 0) (w : ZMod n) (hz : rand [(C.x (C.mulG k), pk, m)] ≠ 0)
    (hQ : rogue C P ((rand [(C.x (C.mulG k), pk, m)])⁻¹ * challenge (C.x (C.mulG k)) pk m) w ≠ 0)
    (he : C.hasEvenY (rogue C P
      ((rand [(C.x (C.mulG k), pk, m)])⁻¹ * challenge (C.x (C.mulG k)) pk m) w) = true) :
    verifyWith C challenge
      (zLate rand (items (forgeLate C challenge rand pk P m m' k a w).2
        (forgeLate C challenge rand pk P m m' k a w).1.rs))
      (forgeLate C challenge rand pk P m m' k a w).1
      (forgeLate C challenge rand pk P m m' k a w).2 = true
```

```lean
/-- **Half of the tries work.** For a key `x⋅G`, the nonce point is not `0` and
has an even y-coordinate for at least `(n - 1)/2` of the `n` values of `w`. -/
theorem card_rogue (x c : ZMod n) :
    n - 1 ≤ 2 * (Finset.univ.filter fun w : ZMod n =>
      rogue C (C.mulG x) c w ≠ 0 ∧ C.hasEvenY (rogue C (C.mulG x) c w) = true).card
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

### The curve secp256k1

From `Halfagg/OrderG.lean` and `Halfagg/PrimeOrder.lean`. `G`, `xCoord`, `hasEvenY` and `liftX` are taproot-lean's. `OrderG.n_smul_G` is the proof of `n⋅G = 0` from the certificate.

```lean
/-- **secp256k1** as the curve interface, with x-coordinates in the base
field. It has the fields of taproot-lean's `secp256k1`, and the order of the
generator is checked by the kernel. -/
def secp256k1F : Curve n Point F where
  G := G
  G_ne_zero := WeierstrassCurve.Affine.Point.some_ne_zero _
  order_G := OrderG.n_smul_G
  x := xCoord
  hasEvenY := hasEvenY
  liftX := liftX
  x_neg := x_neg
  hasEvenY_neg := hasEvenY_neg
  liftX_x := liftX_x
  liftX_spec := liftX_spec
```

```lean
/-- **secp256k1 has prime order `n`**: every point `P` has `n⋅P = 0`. -/
theorem secp256k1_primeOrder : Curve.PrimeOrder n Point
```

### The game's verifier is `VerifyAggregate`

From `Halfagg/Unforgeability.lean`.

```lean
/-- Answer randomizer queries from the function `rand` and pass uniform sampling
on: the randomizer oracle as a fixed hash function. -/
def answerRand (rand : List (Item X M) → H) : QueryImpl (unifSpec + RandSpec H X M) ProbComp
  | .inl k => liftM (unifSpec.query k)
  | .inr its => pure (rand its)
```

```lean
/-- **The game's verifier is BIP 458's `VerifyAggregate`.** With the randomizer
oracle answered by the function `rand`, the last two lines of `aggExperiment`
compute `verifyAggregate` with the randomizer `red ∘ rand`, and check that some
item has the target key and a message that was never signed. -/
theorem game_verifier (rand : List (Item X M) → H) (pk : X) (its : List (Item X M))
    (s : ZMod n) (signed : M → Bool) :
    simulateQ (answerRand rand) (do
        let zs ← (List.range its.length).mapM (zQuery red its)
        return aggWins C challenge pk its s zs signed) =
      pure (verifyAggregate C challenge (fun l => red (rand l)) ⟨its.map (·.1), s⟩
          (its.map (·.2)) &&
        its.any fun it => it.2.1 == pk && !signed it.2.2)
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

From `Halfagg/Security.lean`, `Halfagg/Unforgeability.lean` and `Halfagg/Tightness.lean`. The type of `reduction` makes it a forger in VCVio's BIP 340 game (`unforgeableAdvantage`), with the public key and a signing oracle. `secp256k1_halfagg_unforgeable` is the theorem for secp256k1 with BIP 458's hash. The other secp256k1 theorems take the same form.

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

```lean
/-- The theorem for secp256k1 and BIP458's randomizer hash: the curve hypothesis
holds, the hash has 256 bits and is reduced modulo `n`. -/
theorem secp256k1_halfagg_unforgeable {M : Type} [DecidableEq M] [Inhabited M]
    [NonceGen Secp256k1.n M]
    (challenge : Secp256k1.F → Secp256k1.F → M → ZMod Secp256k1.n)
    (F : AlgForger Secp256k1.n (Fin (2 ^ 256)) Secp256k1.Point Secp256k1.F M) (q : ℕ)
    (hq : ∀ input, (F.main input).IsQueryBoundP (fun r => isRand r.value.data) q) :
    aggAdvantage secp256k1F challenge red256 (erase secp256k1F F) ≤
      SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp
        (reduction secp256k1F challenge red256 F) +
        (q + 1 : ℝ≥0∞) * (2 / ((2 ^ 256 : ℕ) : ℝ≥0∞))
```

```lean
/-- **The reduction signs what the forger signs.** For every set of messages
`p`: if the forger makes at most `q` signing requests for messages in `p`, the
reduction makes at most `q` signing queries for messages in `p`. With `p` all
messages, the reduction makes no more signing queries than the forger; with
`q = 0`, it never asks for a signature the forger did not ask for. -/
theorem reduction_sign_queries [NonceGen n M] [Inhabited M] (F : AlgForger n H E X M)
    (p : M → Bool) (q : ℕ)
    (h : ∀ input, (F.main input).IsQueryBoundP (fun r => isSign p r.value.data) q) (pk : X) :
    ((reduction C challenge red F).main pk).IsQueryBoundP (fun t => isSignQuery p t) q
```

```lean
/-- **Items that fail `lift_x` never win.** Every item of a winning forgery has
an `r` and a `pk` that are x-coordinates of the curve. So the randomizer of a
list with an item that fails `lift_x` is never used by the verifier of a winning
forgery, which is why a forger may hash anything after such an item (`rawTail`). -/
theorem aggWins_lifts {pk : X} {its : List (Item X M)} {s : ZMod n} {zs : List (ZMod n)}
    {signed : M → Bool} (h : aggWins C challenge pk its s zs signed = true) :
    ∀ it ∈ its, lifts C it = true
```

```lean
/-- **The bound is tight in `q`.** The grinding forger makes no signing requests
and at most `q` randomizer requests, and wins the standard game with probability
at least `1 - ((n - 1)/n)^q`. -/
theorem grinder_advantage [NonceGen n ℕ] (q : ℕ) :
    1 - (((n - 1 : ℕ) : ℝ≥0∞) / n) ^ q ≤
      aggAdvantage C challenge id (erase C (grinder C challenge q))
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

### With the challenge hash as a random oracle

From `Halfagg/SecurityROM.lean` and `Halfagg/UnforgeabilityROM.lean`. `sigma`, `keyGen`, `dlogExperiment` and `dlogOfKeyRecovery` are taproot-lean's, and `FiatShamir` is VCVio's.

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
/-- **The reduction as an oracle machine.** It runs the forger with `romHandler`,
asks the oracle for the challenges of the forgery's items and then extracts with
`extractROM`. -/
noncomputable def reductionROM [Inhabited M] (F : RomForger n H E X M) :
    SignatureAlg.UnforgeableAdversary (FiatShamir.inROM (sigma C) (keyGen C) M) where
  main P := do
    let pk := C.x P.1
    let ((out, st), table) ← ((simulateQ (romHandler (H := H) C pk)
      (F.main (initial C ((C.liftX pk).getD 0)))).run Core.init).run ∅
    let st := memoize C st (out.value.groups ()) (out.coefficients ())
    let items := annotate C st.memo (toItems C out.value.data.ms (out.value.groups ()))
    let (zs, _) ← ((List.range items.length).mapM fun i =>
      if i = 0 then pure 1 else red <$> romTableRO (items.take (i + 1))).run table
    let es ← items.mapM fun a => hashQ (n := n) (a.m, (a.r, a.pk))
    extractROM C pk items out.value.data.s zs st.signed es
```

```lean
/-- **Half-aggregation is as secure as BIP340, with the challenge hash as a
random oracle.** An algebraic forger with oracle access to the challenge hash,
at most `q` randomizer requests, wins with probability at most the success
probability of `reductionROM F` in the BIP340 game of
`Taproot.BIP340Security.euf_cma`, plus `(q + 1)⋅μ`, with `μ` as in
`halfagg_unforgeable`. -/
theorem halfagg_unforgeable_rom [Inhabited M] [Finite M] [Finite X]
    [SampleableType (M × (X × X) → ZMod n)] (hx0 : C.liftX (C.x 0) = none)
    (F : RomForger n H E X M) (q : ℕ)
    (hq : ∀ g input, ((F.at g).main input).IsQueryBoundP (fun r => isRand r.value.data) q)
    (μ : ℝ≥0∞) (hμ : RedBound red μ) :
    aggAdvantageROM C red F ≤
      SignatureAlg.unforgeableAdvantage (FiatShamir.runtime M) (reductionROM C red F) +
        (q + 1 : ℝ≥0∞) * μ
```

```lean
/-- **Half-aggregation is unforgeable under the discrete-log assumption**, in
the algebraic group model with both hashes as random oracles:
`halfagg_unforgeable_rom` chained with `Taproot.BIP340Security.euf_cma_dlog`.

For an algebraic forger with at most `q` randomizer requests, `qH` challenge
queries, `qS` signing requests and forgeries of at most `ℓ` items, let
`Q = qH + qS + ℓ + 1` and

`ε = Pr[forger wins] - (q + 1)⋅μ - qS⋅(qS + Q)⋅2/(n - 1)`.

Then a discrete-log solver built from the forger succeeds with probability at
least `ε⋅(ε/(Q + 1) - 1/n)`. The first loss is this project's tight step, the
rest is the forking-lemma loss of BIP340 itself. -/
theorem halfagg_dlog [Inhabited M] [Finite M] [Finite X]
    [SampleableType (M × (X × X) → ZMod n)] (hx0 : C.liftX (C.x 0) = none)
    (F : RomForger n H E X M) (q qH qS ℓ : ℕ)
    (hq : ∀ input, (F.main input).IsQueryBoundP (fun t => isRandCall t) q)
    (hH : ∀ input, (F.main input).IsQueryBoundP (fun t => isChalCall t) qH)
    (hS : ∀ input, (F.main input).IsQueryBoundP (fun t => isSignCall t) qS)
    (hL : ∀ input, ∀ out ∈ support (F.main input), out.value.data.ms.length ≤ ℓ)
    (μ : ℝ≥0∞) (hμ : RedBound red μ) :
    let ε := aggAdvantageROM C red F - (q + 1 : ℝ≥0∞) * μ -
      (qS : ℝ≥0∞) * (qS + (qH + qS + ℓ + 1 : ℕ)) * (2 / ((n - 1 : ℕ) : ℝ≥0∞))
    ε * (ε / ((qH + qS + ℓ + 1 : ℕ) + 1 : ℝ≥0∞) - FiatShamir.challengeSpaceInv (ZMod n)) ≤
      Pr{let x ← (dlogExperiment C (dlogOfKeyRecovery C
        (FiatShamir.cmaReduction (sigma C) (keyGen C) M (simTranscript C) (reductionROM C red F)
          (qH + qS + ℓ + 1))))}[x = true]
```

### A reduction to discrete log without forking

From `Halfagg/SecurityTight.lean` and `Halfagg/UnforgeabilityTight.lean`, with `finalItems` from `Halfagg/Security.lean`. `FiatShamir.simulatedNmaImpl` and `FiatShamir.Fork.roImpl` are VCVio's: a signing oracle that needs no secret key, and a lazily sampled challenge hash.

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

```lean
/-- The final step of an oracle machine: from the public key, the forgery's
annotated items, `s`, the randomizers, the signed messages and the challenges of
the items, compute a forgery of the Fiat-Shamir scheme. -/
abbrev FinalStep (n : ℕ) (E X M : Type) [AddCommGroup E] [Fact n.Prime] (C : Curve n E X) :=
  Stmt C → List (AItem n X M) → ZMod n → List (ZMod n) → List M → List (ZMod n) →
    OracleComp (RomSpec n X M) (M × FSSig n X)
```

```lean
/-- `reductionROM` with its last step replaced by `fin`. -/
noncomputable def romMachine (F : RomForger n H E X M) (fin : FinalStep n E X M C) :
    SignatureAlg.UnforgeableAdversary (FiatShamir.inROM (sigma C) (keyGen C) M) where
  main P := do
    let pk := C.x P.1
    let ((out, st), table) ← ((simulateQ (romHandler (H := H) C pk)
      (F.main (initial C ((C.liftX pk).getD 0)))).run Core.init).run ∅
    let st := memoize C st (out.value.groups ()) (out.coefficients ())
    let items := annotate C st.memo (toItems C out.value.data.ms (out.value.groups ()))
    let (zs, _) ← ((List.range items.length).mapM fun i =>
      if i = 0 then pure 1 else red <$> romTableRO (items.take (i + 1))).run table
    let es ← items.mapM fun a => hashQ (n := n) (a.m, (a.r, a.pk))
    fin P items out.value.data.s zs st.signed es
```

```lean
/-- A forgery that never verifies: its nonce is the x-coordinate of the point at
infinity, which does not lift. -/
def junk [Inhabited M] : M × FSSig n X := (default, ((C.x 0, C.x 0), 0))
```

```lean
/-- Output the signature `(r, α*)` of the target item if the forgery wins, the
item's `β*` is `0` and the candidate key is not the secret key. Otherwise output
`junk`. -/
noncomputable def repFin [Inhabited M] : FinalStep n E X M C :=
  fun P items s zs signed es =>
    match target (C.x P.1) items signed with
    | none => pure (junk C)
    | some a =>
      if C.mulG (candKey (knownChal items es) (C.x P.1) items s zs signed) = P.1 then
        pure (junk C)
      else if aggWins C (knownChal items es) (C.x P.1) (items.map fun a => (a.r, a.pk, a.m))
          s zs (fun m => signed.contains m) = true ∧ (starRep (knownChal items es) a).2 = 0 then
        pure (a.m, ((a.r, C.x P.1), (starRep (knownChal items es) a).1))
      else pure (junk C)
```

```lean
/-- **A forger yields the secret key or a signature made without it**, with no
forking. In the algebraic group model with both hashes as random oracles, for a
forger with at most `q` randomizer requests, `qH` challenge queries, `qS` signing
requests and forgeries of at most `ℓ` items, and `Q = qH + qS + ℓ + 1`:

`Pr[forger wins] ≤ Pr[keySolver solves discrete log] + qS⋅(qS + Q)⋅2/(n - 1) +
(q + 1)⋅μ + Pr[romMachine F repFin forges BIP340]`,

with `μ` as in `halfagg_unforgeable`.

The second term is the loss of VCVio's signing simulation and the third is the
bad event of `halfagg_unforgeable`. The last term is the success of the machine
that reads a signature `(r, α*)` off the forger's explanations while its
candidate key is wrong. This theorem does not bound it, and
`halfagg_dlog_tight` does for forgers that explain the nonces they hash. -/
theorem halfagg_key_or_signature [Inhabited M] [Finite M] [Finite X]
    [SampleableType (M × (X × X) → ZMod n)] (hx0 : C.liftX (C.x 0) = none)
    (F : RomForger n H E X M) (q qH qS ℓ : ℕ)
    (hq : ∀ input, (F.main input).IsQueryBoundP (fun t => isRandCall t) q)
    (hH : ∀ input, (F.main input).IsQueryBoundP (fun t => isChalCall t) qH)
    (hS : ∀ input, (F.main input).IsQueryBoundP (fun t => isSignCall t) qS)
    (hL : ∀ input, ∀ out ∈ support (F.main input), out.value.data.ms.length ≤ ℓ)
    (μ : ℝ≥0∞) (hμ : RedBound red μ) :
    aggAdvantageROM C red F ≤
      Pr{let x ← dlogExperiment C (dlogOfKeyRecovery C (keySolver C red F))}[x = true] +
        (qS : ℝ≥0∞) * (qS + (qH + qS + ℓ + 1 : ℕ)) * (2 / ((n - 1 : ℕ) : ℝ≥0∞)) +
        (q + 1 : ℝ≥0∞) * μ +
        SignatureAlg.unforgeableAdvantage (FiatShamir.runtime (Commit := X × X) (Chal := ZMod n) M)
          (romMachine C red F (repFin C))
```

### The games can be won

From `Halfagg/Winnable.lean`. `copies` is from `Halfagg/Tightness.lean`. A request of the forger carries points as combinations of the points it has received, here the target key's point.

```lean
/-- `k` copies of the second received point, the target key's point `P*`. -/
def copies (b : Groups (Pts E)) (k : ℕ) : (s : Unit) → List (Fin (b s).length → ZMod n) :=
  fun _ => List.replicate k fun i => if i.val = 1 then 1 else 0
```

```lean
/-- The forger that bets on the secret key `1`. Its nonce and its key are the
x-coordinate of the point in its randomizer request, the target key's point. -/
def bettor (m₀ : M) : AlgForger n H E X M where
  main input :=
    let req : Explained (ZMod n) (Request X M) (Pts E) :=
      Explained.ofVectors input.groups (Request.rand [] []) (copies input.groups 1)
    OracleComp.queryBind
      (spec := explainedSpec (ZMod n) (Pts E) (Request X M) (Reply n H X M)) req fun rep =>
    let pk : X := C.x ((req.value.groups ()).headD 0)
    pure (Explained.ofVectors (extend input.groups rep.groups)
      (⟨[m₀], (1 + challenge pk pk m₀) * C.evenScalar 1⟩ : Out n M) (copies _ 2))
  algebraic _ :=
    ⟨Explained.valid_ofVectors _ _ _, fun _ => Explained.valid_ofVectors _ _ _⟩
```

```lean
/-- **The standard game can be won.** The bettor wins it with positive
probability, for every randomizer hash, every reduction of its outputs and
every nonce derivation of the signer. -/
theorem bettor_advantage_pos [NonceGen n M] (m₀ : M) :
    0 < aggAdvantage C challenge red (erase C (bettor C challenge m₀))
```

```lean
/-- **The game of the knowledge theorem can be won.** The bettor's aggregate
verifies with positive probability. -/
theorem bettor_verify_pos [NonceGen n M] (m₀ : M) :
    0 < aggVerifyAdvantage C challenge red (erase C (bettor C challenge m₀))
```

```lean
/-- `halfagg_unforgeable` applied to the bettor. Its left-hand side is positive
(`bettor_advantage_pos`). -/
theorem bettor_bound [NonceGen n M] [Inhabited M] (hx0 : C.liftX (C.x 0) = none) (m₀ : M)
    (μ : ℝ≥0∞) (hμ : RedBound red μ) :
    aggAdvantage C challenge red (erase C (bettor C challenge m₀)) ≤
      SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp
        (reduction C challenge red (bettor C challenge m₀)) + 2 * μ
```

```lean
/-- The bettor with oracle access to the challenge hash. It sends the target
key's point in a randomizer request, asks for the challenge of `m₀` with that
point's x-coordinate as nonce and as key, and outputs the bettor's aggregate. -/
def bettorRom (m₀ : M) : RomForger n H E X M where
  main input :=
    let req : Explained (ZMod n) (Request X M) (Pts E) :=
      Explained.ofVectors input.groups (Request.rand [] []) (copies input.groups 1)
    OracleComp.queryBind (spec := RomForgerSpec n H E X M) (.inr req) fun rep =>
    let pk : X := C.x ((req.value.groups ()).headD 0)
    OracleComp.queryBind (spec := RomForgerSpec n H E X M) (.inl (m₀, (pk, pk))) fun e =>
    pure (Explained.ofVectors (extend input.groups rep.groups)
      (⟨[m₀], (1 + e) * C.evenScalar 1⟩ : Out n M) (copies _ 2))
  algebraic _ _ :=
    ⟨Explained.valid_ofVectors _ _ _, fun _ => Explained.valid_ofVectors _ _ _⟩
```

```lean
/-- **The game with the challenge hash as a random oracle can be won.** -/
theorem bettorRom_advantage_pos [SampleableType (M × (X × X) → ZMod n)] (m₀ : M) :
    0 < aggAdvantageROM C red (bettorRom C m₀)
```

```lean
/-- `halfagg_dlog_tight` applied to `bettorRom`: one randomizer request, one
challenge query, no signing request and one item. Its left-hand side is
positive (`bettorRom_advantage_pos`). -/
theorem bettorRom_bound [Inhabited M] [Finite M] [Finite X]
    [SampleableType (M × (X × X) → ZMod n)] (hx0 : C.liftX (C.x 0) = none) (m₀ : M)
    (μ : ℝ≥0∞) (hμ : RedBound red μ) :
    aggAdvantageROM C red (bettorRom C m₀) ≤
      Pr{let x ← dlogExperiment C (dlogOfKeyRecovery C
        (keySolver C red (bettorRom C m₀)))}[x = true] + 2 * μ + 2 / n
```

### The theorems for 32-byte arrays

From `Halfagg/BytesSecurity.lean`. `bytes32`, `toNatBE` and `taggedHash` are taproot-lean's `bytes`, `int` and tagged SHA-256. `decodeVerify` and `verifyAggregateBytes` are printed under [BIP 458's verifier](#bip-458s-verifier). `bytes_halfagg_knowledge`, `bytes_halfagg_dlog_tight` and `bytes_halfagg_binding` are the other three theorems for this instance.

```lean
/-- 32-byte arrays. -/
abbrev B32 := {b : Bytes // b.length = 32}
```

```lean
/-- **secp256k1 with x-coordinates as 32-byte arrays**: the x-only encoding of
a point is `bytes(x(P))`, and `lift_x` fails for an array that is not below
`p`. -/
def secp256k1X : Curve n Point B32 where
  G := G
  G_ne_zero := secp256k1F.G_ne_zero
  order_G := OrderG.n_smul_G
  x P := ⟨bytes32 (xCoord P).val, bytes32_length _⟩
  hasEvenY := hasEvenY
  liftX b := if toNatBE b.1 < p then liftX (toNatBE b.1 : F) else none
  x_neg P := Subtype.ext (by simp only [Secp256k1.x_neg])
  hasEvenY_neg := hasEvenY_neg
  liftX_x P hP he := by
    have hv : (xCoord P).val < p := ZMod.val_lt _
    simp only [toNatBE_bytes32, Nat.mod_eq_of_lt (hv.trans p_lt), hv, ↓reduceIte,
      ZMod.natCast_zmod_val]
    exact Secp256k1.liftX_x P hP he
  liftX_spec r P h := by
    split_ifs at h with hr
    obtain ⟨h1, h2, h3⟩ := Secp256k1.liftX_spec _ P h
    refine ⟨h1, h2, Subtype.ext ?_⟩
    change bytes32 (xCoord P).val = r.1
    rw [h3, ZMod.val_natCast_of_lt hr]
    exact bytes32_toNatBE r.2
```

```lean
/-- `int(hash_BIP0340/challenge(r ‖ pk ‖ m)) mod n` on 32-byte arrays. -/
def challengeX (r pk m : B32) : ZMod n :=
  (toNatBE (taggedHash "BIP0340/challenge" (r.1 ++ pk.1 ++ m.1)) : ZMod n)
```

```lean
/-- The bytes of an item of 32-byte arrays. -/
def itemBytes (it : Item B32 B32) : Item Bytes Bytes := (it.1.1, it.2.1.1, it.2.2.1)
```

```lean
/-- BIP458's randomizer hash on items of 32-byte arrays:
`int(hash_BIP0458/randomizer(r₀ ‖ pk₀ ‖ m₀ ‖ … ‖ rᵢ ‖ pkᵢ ‖ mᵢ)) mod n`. -/
def randomizerX (its : List (Item B32 B32)) : ZMod n := randomizer (its.map itemBytes)
```

```lean
/-- A 32-byte array as a 256-bit value. -/
def int256 (b : Bytes) (h : b.length = 32) : Fin (2 ^ 256) :=
  ⟨toNatBE b, by
    have := toNatBE_lt b
    rw [h] at this
    exact lt_of_lt_of_eq this (by norm_num)⟩
```

```lean
/-- `hash_BIP0458/randomizer` with its 256-bit output, on items of 32-byte
arrays. -/
def randHash256 (its : List (Item B32 B32)) : Fin (2 ^ 256) :=
  int256 (taggedHash "BIP0458/randomizer" (randomizerInput (its.map itemBytes)))
    (length_taggedHash _ _)
```

```lean
/-- **BIP458's randomizer is a 256-bit hash output reduced modulo `n`**: the
`red256` of the security theorems for secp256k1. -/
theorem randomizerX_eq_red256 (its : List (Item B32 B32)) :
    randomizerX its = red256 (randHash256 its)
```

```lean
/-- **Half-aggregation on 32-byte arrays is as secure as BIP340.**
`halfagg_unforgeable` for secp256k1 with 32-byte nonces, public keys and
messages, BIP340's challenge hash and a 256-bit randomizer hash that is reduced
modulo `n`. -/
theorem bytes_halfagg_unforgeable [NonceGen n B32]
    (F : AlgForger n (Fin (2 ^ 256)) Point B32 B32) (q : ℕ)
    (hq : ∀ input, (F.main input).IsQueryBoundP (fun r => isRand r.value.data) q) :
    aggAdvantage secp256k1X challengeX red256 (erase secp256k1X F) ≤
      SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp
        (reduction secp256k1X challengeX red256 F) +
        (q + 1 : ℝ≥0∞) * (2 / ((2 ^ 256 : ℕ) : ℝ≥0∞))
```

```lean
/-- A byte array as a 32-byte array, if it has 32 bytes. -/
def to32 (b : Bytes) : B32 := if h : b.length = 32 then ⟨b, h⟩ else default
```

```lean
/-- A field element as its 32 bytes. -/
def encX (x : F) : B32 := ⟨bytes32 x.val, bytes32_length _⟩
```

```lean
/-- The parsing and the checks of `VerifyAggregate`, with the nonces, public
keys and messages as 32-byte arrays. -/
def decodeX (aggsig : Bytes) (pm : List (Bytes × Bytes)) :
    Option (AggSig n B32 × List (B32 × B32)) :=
  (decodeVerify aggsig pm).map fun x =>
    (⟨x.1.rs.map encX, x.1.s⟩, x.2.map fun y => (encX y.1, to32 y.2))
```

```lean
/-- **`VerifyAggregate` on bytes is the verifier of the instance with 32-byte
arrays**, after the parsing and the checks. -/
theorem verifyAggregateBytes_eq_X (aggsig : Bytes) (pm : List (Bytes × Bytes)) :
    verifyAggregateBytes aggsig pm =
      (decodeX aggsig pm).any fun x =>
        verifyAggregate secp256k1X challengeX randomizerX x.1 x.2
```

```lean
/-- **The 32-byte arrays of the decoded input are the bytes of the input**: the
nonces are the 32-byte chunks of `aggsig`, and the public keys and messages are
those of `pm`. -/
theorem decodeX_bytes {aggsig : Bytes} {pm : List (Bytes × Bytes)}
    {x : AggSig n B32 × List (B32 × B32)} (h : decodeX aggsig pm = some x) :
    x.1.rs.map (·.1) = chunks32 aggsig pm.length ∧
      x.2.map (fun y => (y.1.1, y.2.1)) = pm ∧
      x.1.s = (toNatBE (aggsig.drop (32 * pm.length)) : ZMod n)
```

```lean
/-- **With SHA-256 as the randomizer hash, the game's verifier is
`VerifyAggregate` on bytes.** For an input that passes the parsing and the
checks, the last two lines of `aggExperiment` on the decoded items, with the
randomizer oracle answered by `hash_BIP0458/randomizer`, compute
`verifyAggregateBytes` on the input and check that some item has the target key
and a message that was never signed. -/
theorem bytes_game_verifier {aggsig : Bytes} {pm : List (Bytes × Bytes)}
    {x : AggSig n B32 × List (B32 × B32)} (h : decodeX aggsig pm = some x) (pk : B32)
    (signed : B32 → Bool) :
    simulateQ (answerRand randHash256) (do
        let zs ← (List.range (items x.2 x.1.rs).length).mapM
          (zQuery red256 (items x.2 x.1.rs))
        return aggWins secp256k1X challengeX pk (items x.2 x.1.rs) x.1.s zs signed) =
      pure (verifyAggregateBytes aggsig pm &&
        (items x.2 x.1.rs).any fun it => decide (it.2.1 = pk) && !signed it.2.2)
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

```lean
/-- The theorem for secp256k1 and BIP458's randomizer hash. That every point of
secp256k1 has order dividing `n` is `secp256k1_primeOrder`. -/
theorem secp256k1_halfagg_binding {M : Type} [DecidableEq M] [Finite M]
    [SampleableType (M × (Secp256k1.F × Secp256k1.F) → ZMod Secp256k1.n)]
    (A : BindAdversary Secp256k1.n (Fin (2 ^ 256)) Secp256k1.F M) (qC qZ ℓ : ℕ)
    (hC : A.main.IsQueryBoundP (fun t => isChalB t) qC)
    (hZ : A.main.IsQueryBoundP (fun t => isRandB t) qZ)
    (hL : ∀ out ∈ support A.main, out.1.rs.length ≤ ℓ) :
    bindAdvantage secp256k1F red256 A ≤
      (((qC + 2 * ℓ) * (qC + 2 * ℓ) : ℕ) : ℝ≥0∞) / Secp256k1.n +
        (((qZ + 2 * ℓ) * (qZ + 2 * ℓ) : ℕ) : ℝ≥0∞) * (2 / ((2 ^ 256 : ℕ) : ℝ≥0∞))
```

<!-- definitions:begin -->

### Every definition behind the results

The definitions that the statements of the results in `Halfagg/Summary.lean` depend on, directly or through other definitions: 156 of this project and 261 of the libraries it is built on. `#surface` in `Halfagg/Audit.lean` computes the list from the compiled project, `Halfagg/Summary.lean` guards it, and the build fails if it changes. Proofs are not followed, since what a proof uses does not change what a statement says. The list stops at Lean's core library and at Mathlib. Whoever agrees with these definitions knows what the results say. The ones that are not printed above have to be read in the sources, for the libraries at the commits in `lake-manifest.json`. `scripts/check.sh` fails if the list has a module under `Halfagg/Proofs/`.

**This project**

- `Halfagg/Attacks.lean`: `forgeLate`, `forgeOnes`, `rogue`, `zLate`
- `Halfagg/Basic.lean`: `AggSig`, `Item`, `aggregate`, `entryItem`, `entryPM`, `incAggregate`, `isum`, `items`, `lifts`, `shiftedPair`, `term`, `verifyAggregate`, `verifyMulti`, `verifyWith`, `z`
- `Halfagg/BytesSecurity.lean`: `Security.B32`, `Security.challengeX`, `Security.decodeX`, `Security.encX`, `Security.instDecidableEqB32`, `Security.instInhabitedB32`, `Security.int256`, `Security.itemBytes`, `Security.randHash256`, `Security.randomizerX`, `Security.secp256k1X`, `Security.to32`
- `Halfagg/Encoding.lean`: `Vectors.Item32`, `Vectors.decodeVerify`, `Vectors.encodeItem`, `Vectors.randomizerInput`
- `Halfagg/Examples.lean`: `Examples.demo`, `Examples.uvec`
- `Halfagg/Hash256.lean`: `Security.red256`, `Security.redMod`
- `Halfagg/OrderG.lean`: `secp256k1F`
- `Halfagg/Security.lean`: `Security.AItem`, `Security.AggAdversary`, `Security.AlgForger`, `Security.AnnSpec`, `Security.Core`, `Security.GameSpec`, `Security.NonceGen`, `Security.Out`, `Security.Pts`, `Security.RandSpec`, `Security.RedBound`, `Security.Rep`, `Security.Reply`, `Security.Request`, `Security.SignSpec`, `Security.aggAdvantage`, `Security.aggExperiment`, `Security.aggWins`, `Security.annotate`, `Security.bip340`, `Security.coreImpl`, `Security.erase`, `Security.eraseImpl`, `Security.extractForgery`, `Security.finalItems`, `Security.flatten`, `Security.initial`, `Security.instDecidableEqAItem`, `Security.isRand`, `Security.isSign`, `Security.isSignQuery`, `Security.liftRep`, `Security.memoRecord`, `Security.memoize`, `Security.memoizeList`, `Security.pairs`, `Security.rawTail`, `Security.reduction`, `Security.smulVal`, `Security.starRep`, `Security.tableRO`, `Security.tableZs`, `Security.toItems`, `Security.zQuery`, `Security.Core.init`, `Security.NonceGen.uniform`, `Security.instDecidableEqAItem.decEq`
- `Halfagg/SecurityBinding.lean`: `Security.BindAdversary`, `Security.BindSpec`, `Security.answerChalB`, `Security.bindAdvantage`, `Security.bindExperiment`, `Security.bindGame`, `Security.bindWins`, `Security.isChalB`, `Security.isRandB`
- `Halfagg/SecurityKnowledge.lean`: `Security.aggVerifies`, `Security.aggVerifyAdvantage`, `Security.aggVerifyExperiment`, `Security.extractAdvantage`, `Security.extractExperiment`, `Security.extractSig`, `Security.extractWins`, `Security.extractor`
- `Halfagg/SecurityROM.lean`: `LoggedRun.tableImpl`, `Security.ChalSpec`, `Security.FSSig`, `Security.RomForger`, `Security.RomForgerSpec`, `Security.RomSpec`, `Security.aggAdvantageROM`, `Security.aggExperimentROM`, `Security.answerChal`, `Security.extractROM`, `Security.hOf`, `Security.hashQ`, `Security.isChalCall`, `Security.isRandCall`, `Security.isSignCall`, `Security.knownChal`, `Security.reductionROM`, `Security.romHandler`, `Security.romTableRO`, `Security.RomForger.at`
- `Halfagg/SecurityTight.lean`: `Security.ExplainsNonces`, `Security.FinalStep`, `Security.candKey`, `Security.junk`, `Security.keySolver`, `Security.repFin`, `Security.romMachine`, `Security.romPrefix`, `Security.target`
- `Halfagg/Tightness.lean`: `Security.copies`, `Security.grindLoop`, `Security.grinder`, `Security.gβ`
- `Halfagg/Unforgeability.lean`: `Security.answerRand`
- `Halfagg/VectorData.lean`: `Vectors.aggregateVectors`, `Vectors.incAggregateVectors`, `Vectors.verifyVectors`
- `Halfagg/VectorTypes.lean`: `Vectors.AggregateVector`, `Vectors.IncAggregateVector`, `Vectors.VerifyVector`
- `Halfagg/Vectors.lean`: `Vectors.aggregateBytes`, `Vectors.bip340VerifyBytes`, `Vectors.chunks32`, `Vectors.incAggregateBytes`, `Vectors.is32`, `Vectors.pmOf`, `Vectors.pmsOf`, `Vectors.randomizer`, `Vectors.randomizerF`, `Vectors.verifyAggregateBytes`
- `Halfagg/Winnable.lean`: `Security.bettor`, `Security.bettorRom`

**taproot-lean**

- `Taproot/BIP340.lean`: `Taproot.BIP340.pubkey`, `Taproot.BIP340.sign`, `Taproot.BIP340.verify`
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
