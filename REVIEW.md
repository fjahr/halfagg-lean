# Reviewing halfagg-lean

Lean checks the proofs. A reviewer checks that the statements say what they should. Everything under `Halfagg/Proofs/` can stay unread, because a wrong proof does not compile. A wrong definition does.

## What to read

About 900 lines decide whether the results mean anything. [The statements](#the-statements) at the end of this file prints most of them on one page.

1. `Halfagg/Basic.lean`, the definitions before the first theorem. Compare `incAggregate`, `aggregate` and `verifyWith` with the algorithms in BIP 458.
2. `Halfagg/Security.lean`, all of it. The header lists the modelling choices and the limitations.
3. `Halfagg/Unforgeability.lean`, the theorem statements.
4. `Halfagg/SecurityROM.lean` and the statements in `Halfagg/UnforgeabilityROM.lean`, for the version with the challenge hash as a random oracle.

taproot-lean supplies the curve interface, `BIP340.sign` and `BIP340.verify`. VCVio supplies the random oracle and the BIP 340 game (`SignatureAlg.unforgeableAdvantage`). agm-lean supplies the algebraic adversary. A full review reads those definitions too.

The model was compared with BIP 458 at bitcoin/bips commit [`a7f9132`](https://github.com/bitcoin/bips/blob/a7f91321f25b5be8d93e901775621c21519e80b7/bip-0458.mediawiki). CI takes the test vectors and the Python reference from the same commit.

## Questions to ask

**Is the game the standard one?** `aggExperiment` and `aggWins` never mention representations or the reduction. The adversary picks every public key except the target. It wins with any verifying list that has one item under the target key with a message it never had signed. The game draws the randomizers from the oracle (`zQuery`) and then calls `verifyWith`, so `verifyAggregate` does not appear in it. `game_verifier` proves that with the oracle answered by a function `rand`, those two steps compute `verifyAggregate` with the randomizer hash `rand`.

**Is the forger class too small?** `AlgForger` is agm-lean's adversary. It must explain every point it sends as a combination of `G`, the target key and the nonce points of the signatures it received. `erase` drops the explanations, so the theorem bounds the forger's advantage in the standard game. The x-coordinates a forger hashes come from points it explained, with one exception. After an item that fails `lift_x`, a randomizer request may contain arbitrary encodings (`rawTail`). `aggWins_lifts` is the reason that is safe.

**Could the proof do without the algebraic group model?** The two proofs BIP 458 cites do not. BIP 458 derives `zᵢ` from the first `i + 1` items, so that signatures can be added to an aggregate later. Chen and Zhao call this scheme IASchnorr and prove it only in the algebraic group model. The random-oracle proof of [Chalkias, Garillot, Kondi and Nikolaenko](https://eprint.iacr.org/2021/350) (Theorem 5) is for the variant that hashes the whole list for every randomizer, and its loss is quadratic. For BIP 458's variant, Chen and Zhao note in Remark 6 that a random-oracle proof would rewind the forger once per item, so its loss would grow exponentially with the number of items.

**Why must the forger explain a point when it first sends it?** The bound needs it. The theorem has no running-time bound, so it also covers a forger that finds the secret key by brute force. Such a forger knows many representations of each point. If it could choose them after seeing the randomizers, it could pick ones for which the extraction fails, and win while the reduction does not. A randomizer request carries the representations of its points, and the reduction keeps the first representation it sees for each x-coordinate (`memoize`). So the representations behind `zᵢ` are fixed before `zᵢ` is drawn, and the extraction fails with probability at most `(q + 1)/n`. This is the convention of Chen and Zhao's model, where the forger explains every group element it outputs or sends to an oracle.

**Does the reduction cheat?** `reduction` gets a BIP 340 public key and a signing oracle and nothing else. It answers randomizer requests from its own table. `reduction_sign_queries` shows it asks for no signature the forger did not ask for. VCVio's game rejects a forgery on a signed message.

**Do the random-oracle forger and reduction only query the oracle?** `RomForger.main` and `reductionROM` are oracle programs over a challenge-hash oracle, so they cannot read the table. `reductionROM_bound` counts the reduction's queries: the forger's signing requests, and `qH + qS + ℓ + 1` hash queries for a forger with `qH` hash queries, `qS` signing requests and forgeries of at most `ℓ` items. The game samples the whole table first and then answers queries from it. For a finite domain that is the same as lazy sampling (`rom_eq_table`).

**Is the theorem vacuous?** `Halfagg/Examples.lean` has a forger that satisfies the hypotheses and a transcript that satisfies the win predicate. The curve hypothesis `hx0` holds for secp256k1 (`Halfagg/Proofs/Secp256k1.lean`).

**What does the bound say?** `(q + 1)/n`, where `q` counts randomizer requests, as in Chen and Zhao. It is tight up to one query: `grinder_advantage` in `Halfagg/Tightness.lean` proves that a forger who tries `q` second items wins with probability at least `1 - ((n - 1)/n)^q`.

## What the theorem does not say

- Only the step from half-aggregation to BIP 340 is tight. `halfagg_dlog` inherits the forking-lemma loss of BIP 340's own proof, which is quadratic in the forger's success probability.
- The random-oracle version needs a finite message type. BIP 458's 32-byte messages are one.
- No theorem bounds running time. Without that, `halfagg_unforgeable` alone would allow a reduction that breaks BIP 340 by brute force. This one does not, and `reduction` is short enough to check by reading.
- The algebraic group model is a restriction on the forger. A forger that hashes x-coordinates of curve points it cannot explain is outside the theorem.
- No theorem says that the functions on bytes in `Halfagg/Vectors.lean` are BIP 458's algorithms. `Halfagg/Vectors.lean` runs BIP 458's 53 test vectors against them, and `scripts/fuzz.py` compares them with the Python reference and with libsecp256k1 on random inputs. `Halfagg/Encoding.lean` proves that the verifier on bytes is the model's verifier on the decoded input and that the randomizer's hash input determines the item list. Aggregation on bytes has no such theorem.

## Machine checks

- `lake build` compiles every proof and fails if the axioms of a main result change (`Halfagg/Summary.lean`).
- `scripts/check.sh` searches the sources for `sorry`, new axioms, unsafe code and stray `native_decide`. It also checks that every code block under [The statements](#the-statements) is in the sources word for word.
- `scripts/replay.sh` replays every project module in the kernel with `leanchecker`, without the elaborator. It rejects a module that adds a false theorem behind the kernel's back, which `#print axioms` does not notice.

Mutating the model is a useful test. Three mutants that weakened the randomizer broke the proof at `badKey_prob` or `extract_or_bad`. Removing the `lifts` check from `rawTail` breaks it at `covered_rawTail`.

## The statements

The definitions and theorem statements a reviewer has to agree with, copied from the sources with their comments. Proofs are left out.

Throughout, `n` is a prime, `E` is the group of curve points, `X` is the type of x-only encodings and `M` is the message type. `C : Curve n E X` is taproot-lean's curve interface and `challenge : X → X → M → ZMod n` is the BIP 340 challenge hash.

Not printed here: the parts of the two reductions (`coreImpl`, `extractForgery`, `romHandler`, `extractROM` and their helpers, in `Halfagg/Security.lean` and `Halfagg/SecurityROM.lean`), the grinding forger (`Halfagg/Tightness.lean`), and the definitions of taproot-lean, VCVio and agm-lean at the commits pinned in `lakefile.toml`.

### BIP 458's verifier

From `Halfagg/Basic.lean`. `C` is taproot-lean's curve interface, `challenge` the BIP 340 challenge hash and `rand` the randomizer hash.

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

### The game

From `Halfagg/Security.lean`. `bip340` is BIP 340 as a VCVio signature scheme, and `runWithSigningOracle` is VCVio's signing oracle with a log of the signed messages.

```lean
/-- BIP340 with uniformly random nonzero secret keys and nonces, in any monad
that can sample. `BIP340.sign` normalizes the key and the nonce to even-y
points. Signing cannot fail with a nonzero key and nonce; the fallback
`(pk, 0)` is never used. -/
noncomputable def bip340 (m : Type → Type) [Monad m] [MonadLiftT ProbComp m] :
    SignatureAlg m M X (ZMod n) (X × ZMod n) where
  keygen := monadLift (do
    let d ← $ᵗ (NonzeroScalar n)
    return (C.x (C.mulG d.1), d.1) : ProbComp (X × ZMod n))
  sign pk sk msg := monadLift (do
    let k ← $ᵗ (NonzeroScalar n)
    return (BIP340.sign C challenge (fun _ _ _ => k.1) sk msg).getD (pk, 0) :
      ProbComp (X × ZMod n))
  verify pk msg sig := pure (BIP340.verify C challenge pk msg sig)
```

```lean
/-- The randomizer hash as a random oracle on lists of `(r, pk, m)` items. -/
abbrev RandSpec (n : ℕ) (X M : Type) := List (Item X M) →ₒ ZMod n
```

```lean
/-- The signing oracle: a message to a BIP340 signature `(r, s)`. -/
abbrev SignSpec (n : ℕ) (X M : Type) := M →ₒ (X × ZMod n)
```

```lean
/-- The adversary's oracles: uniform sampling, the randomizer hash and signing. -/
abbrev GameSpec (n : ℕ) (X M : Type) := (unifSpec + RandSpec n X M) + SignSpec n X M
```

```lean
/-- An adversary of the standard game: given the target public key, it outputs
`(r, pk, m)` items and `s`, i.e. the aggregate signature `r₀ ‖ … ‖ bytes(s)` for
the pairs `(pkᵢ, mᵢ)`. -/
structure AggAdversary (n : ℕ) (X M : Type) where
  main (pk : X) : OracleComp (GameSpec n X M) (List (Item X M) × ZMod n)
```

```lean
/-- The verifier's randomizer `zᵢ`: `1` for `i = 0`, otherwise the randomizer
hash of the first `i + 1` items. -/
def zQuery (its : List (Item X M)) (i : ℕ) : OracleComp (unifSpec + RandSpec n X M) (ZMod n) :=
  if i = 0 then pure 1 else HasQuery.query (spec := RandSpec n X M) (its.take (i + 1))
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
noncomputable def aggExperiment (A : AggAdversary n X M) :
    OracleComp (unifSpec + RandSpec n X M) Bool := do
  let alg := bip340 (M := M) C challenge (OracleComp (unifSpec + RandSpec n X M))
  let (pk, sk) ← alg.keygen
  let ((its, s), log) ← alg.runWithSigningOracle pk sk (A.main pk)
  let zs ← (List.range its.length).mapM (zQuery its)
  return aggWins C challenge pk its s zs log.wasQueried
```

```lean
/-- The adversary's success probability, with a lazily sampled random oracle. -/
noncomputable def aggAdvantage (A : AggAdversary n X M) : ℝ≥0∞ :=
  (ProbCompRuntime.rom (RandSpec n X M)).evalDist (aggExperiment C challenge A) {true}
```

### The game's verifier is `VerifyAggregate`

From `Halfagg/Unforgeability.lean`.

```lean
/-- Answer randomizer queries from the function `rand` and pass uniform sampling
on: the randomizer oracle as a fixed hash function. -/
def answerRand (rand : List (Item X M) → ZMod n) : QueryImpl (unifSpec + RandSpec n X M) ProbComp
  | .inl k => liftM (unifSpec.query k)
  | .inr its => pure (rand its)
```

```lean
/-- **The game's verifier is BIP 458's `VerifyAggregate`.** With the randomizer
oracle answered by the function `rand`, the last two lines of `aggExperiment`
compute `verifyAggregate` with the randomizer hash `rand`, and check that some
item has the target key and a message that was never signed. -/
theorem game_verifier (rand : List (Item X M) → ZMod n) (pk : X) (its : List (Item X M))
    (s : ZMod n) (signed : M → Bool) :
    simulateQ (answerRand rand) (do
        let zs ← (List.range its.length).mapM (zQuery its)
        return aggWins C challenge pk its s zs signed) =
      pure (verifyAggregate C challenge rand ⟨its.map (·.1), s⟩ (its.map (·.2)) &&
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
/-- Replies: a sample, a randomizer, or the `s` of a signature (its nonce point
`lift_x(r)` is the reply's group argument). -/
def Reply (n : ℕ) (X M : Type) : Request X M → Type
  | .random k => Fin (k + 1)
  | .rand _ _ => ZMod n
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
abbrev AlgForger (n : ℕ) (E X M : Type) [AddCommGroup E] :=
  AlgebraicGroupModel.Interaction.Adversary (ZMod n) (Pts E) Unit (Request X M) (Reply n X M)
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
    QueryImpl (plainSpec (Pts E) (Request X M) (Reply n X M)) (OracleComp (GameSpec n X M))
  | ⟨.random k, _⟩ => do
      let u ← (liftM ((GameSpec n X M).query (.inl (.inl k))) : OracleComp (GameSpec n X M) _)
      pure ⟨u, fun _ => []⟩
  | ⟨.rand ms tail, groups⟩ => do
      let z ← (liftM ((GameSpec n X M).query
        (.inl (.inr (toItems C ms (groups ()) ++ rawTail C tail)))) :
        OracleComp (GameSpec n X M) _)
      pure ⟨z, fun _ => []⟩
  | ⟨.sign m, _⟩ => do
      let sig ← (liftM ((GameSpec n X M).query (.inr m)) : OracleComp (GameSpec n X M) _)
      pure ⟨sig.2, fun _ => [(C.liftX sig.1).getD 0]⟩
```

```lean
/-- The standard-game adversary that runs `F` and drops its explanations. -/
noncomputable def erase (F : AlgForger n E X M) : AggAdversary n X M where
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

### The theorems

From `Halfagg/Security.lean`, `Halfagg/Unforgeability.lean` and `Halfagg/Tightness.lean`. The type of `reduction` makes it a forger in VCVio's BIP 340 game (`unforgeableAdvantage`), with the public key and a signing oracle.

```lean
/-- **The reduction**: run the forger with `coreImpl`, forwarding uniform
sampling and signing to its own oracles and answering randomizer requests from
its table; then record the forgery's representations, draw the randomizers the
verifier needs, and extract a BIP340 forgery. It makes one signing query per
signing request of the forger (`reduction_sign_queries`). Its running time is
not formalized. -/
noncomputable def reduction [Inhabited M] (F : AlgForger n E X M) :
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
    let (zs, _) ← (tableZs items).run table
    return extractForgery C challenge pk items out.value.data.s zs st.signed
```

```lean
/-- **Half-aggregation is as secure as BIP340** (Chen and Zhao, Theorem 2), in
the algebraic group model with the randomizer hash as a random oracle and for
every challenge hash: an algebraic forger that makes at most `q` randomizer
requests wins the standard game with probability at most the success
probability of `reduction F` against BIP340, plus `(q + 1)/n`.

`hx0` says the point at infinity has no x-only encoding: its x-coordinate in the
curve interface does not lift. For secp256k1 that x-coordinate is `0`, and `0`
is not an x-coordinate of the curve because `7` is not a square modulo `p`. -/
theorem halfagg_unforgeable [Inhabited M] (hx0 : C.liftX (C.x 0) = none)
    (F : AlgForger n E X M) (q : ℕ)
    (hq : ∀ input, (F.main input).IsQueryBoundP (fun r => isRand r.value.data) q) :
    aggAdvantage C challenge (erase C F) ≤
      SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp (reduction C challenge F) +
        (q + 1 : ℝ≥0∞) / n
```

```lean
/-- **The reduction signs what the forger signs.** For every set of messages
`p`: if the forger makes at most `q` signing requests for messages in `p`, the
reduction makes at most `q` signing queries for messages in `p`. With `p` all
messages, the reduction makes no more signing queries than the forger; with
`q = 0`, it never asks for a signature the forger did not ask for. -/
theorem reduction_sign_queries [Inhabited M] (F : AlgForger n E X M) (p : M → Bool) (q : ℕ)
    (h : ∀ input, (F.main input).IsQueryBoundP (fun r => isSign p r.value.data) q) (pk : X) :
    ((reduction C challenge F).main pk).IsQueryBoundP (fun t => isSignQuery p t) q
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
theorem grinder_advantage (q : ℕ) :
    1 - (((n - 1 : ℕ) : ℝ≥0∞) / n) ^ q ≤
      aggAdvantage C challenge (erase C (grinder C challenge q))
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
abbrev RomForgerSpec (n : ℕ) (E X M : Type) :=
  ChalSpec n X M + explainedSpec (ZMod n) (Pts E) (Request X M) (Reply n X M)
```

```lean
/-- Answer challenge-hash queries from the table `g` and pass requests on. -/
def answerChal (g : M × (X × X) → ZMod n) :
    QueryImpl (RomForgerSpec n E X M)
      (OracleComp (explainedSpec (ZMod n) (Pts E) (Request X M) (Reply n X M)))
  | .inl key => pure (g key)
  | .inr t => liftM ((explainedSpec (ZMod n) (Pts E) (Request X M) (Reply n X M)).query t)
```

```lean
/-- An algebraic forger with oracle access to the challenge hash. For every
answer table, the forger with its challenge queries answered from the table is
algebraic. -/
structure RomForger (n : ℕ) (E X M : Type) [AddCommGroup E] where
  main : Message Unit (Pts E) →
    OracleComp (RomForgerSpec n E X M) (Explained (ZMod n) (Out n M) (Pts E))
  algebraic : ∀ (g : M × (X × X) → ZMod n) input,
    IsAlgebraic input.groups (simulateQ (answerChal g) (main input))
```

```lean
/-- The forger with its challenge queries answered from the table `g`. -/
def RomForger.at (F : RomForger n E X M) (g : M × (X × X) → ZMod n) : AlgForger n E X M where
  main input := simulateQ (answerChal g) (F.main input)
  algebraic := F.algebraic g
```

```lean
/-- Whether a forger's oracle call is a randomizer request. -/
def isRandCall : (RomForgerSpec n E X M).Domain → Bool
  | .inl _ => false
  | .inr t => isRand t.value.data
```

```lean
/-- Whether a forger's oracle call is a challenge-hash query. -/
def isChalCall : (RomForgerSpec n E X M).Domain → Bool
  | .inl _ => true
  | .inr _ => false
```

```lean
/-- Whether a forger's oracle call is a signing request. -/
def isSignCall : (RomForgerSpec n E X M).Domain → Bool
  | .inl _ => false
  | .inr t => isSign (fun _ => true) t.value.data
```

```lean
/-- **The game with the challenge hash as a random oracle**: sample the challenge
hash table, then play the game of `aggExperiment` with it. The randomizer hash is
a lazily sampled random oracle as before. -/
noncomputable def aggExperimentROM [SampleableType (M × (X × X) → ZMod n)]
    (F : RomForger n E X M) : ProbComp Bool := do
  let g ← $ᵗ (M × (X × X) → ZMod n)
  (simulateQ (RandSpec n X M).romImpl (aggExperiment C (hOf g) (erase C (F.at g)))).run' ∅
```

```lean
/-- The forger's success probability. -/
noncomputable def aggAdvantageROM [SampleableType (M × (X × X) → ZMod n)]
    (F : RomForger n E X M) : ℝ≥0∞ :=
  Pr{let b ← aggExperimentROM C F}[b = true]
```

```lean
/-- **The reduction as an oracle machine.** It runs the forger with `romHandler`,
asks the oracle for the challenges of the forgery's items and then extracts with
`extractROM`. -/
noncomputable def reductionROM [Inhabited M] (F : RomForger n E X M) :
    SignatureAlg.UnforgeableAdversary (FiatShamir.inROM (sigma C) (keyGen C) M) where
  main P := do
    let pk := C.x P.1
    let ((out, st), table) ← ((simulateQ (romHandler C pk)
      (F.main (initial C ((C.liftX pk).getD 0)))).run Core.init).run ∅
    let st := memoize C st (out.value.groups ()) (out.coefficients ())
    let items := annotate C st.memo (toItems C out.value.data.ms (out.value.groups ()))
    let (zs, _) ← ((List.range items.length).mapM fun i =>
      if i = 0 then pure 1 else romTableRO (items.take (i + 1))).run table
    let es ← items.mapM fun a => hashQ (n := n) (a.m, (a.r, a.pk))
    extractROM C pk items out.value.data.s zs st.signed es
```

```lean
/-- **Half-aggregation is as secure as BIP340, with the challenge hash as a
random oracle.** An algebraic forger with oracle access to the challenge hash,
at most `q` randomizer requests, wins with probability at most the success
probability of `reductionROM F` in the BIP340 game of
`Taproot.BIP340Security.euf_cma`, plus `(q + 1)/n`. -/
theorem halfagg_unforgeable_rom [Inhabited M] [Finite M] [Finite X]
    [SampleableType (M × (X × X) → ZMod n)] (hx0 : C.liftX (C.x 0) = none)
    (F : RomForger n E X M) (q : ℕ)
    (hq : ∀ g input, ((F.at g).main input).IsQueryBoundP (fun r => isRand r.value.data) q) :
    aggAdvantageROM C F ≤
      SignatureAlg.unforgeableAdvantage (FiatShamir.runtime M) (reductionROM C F) +
        (q + 1 : ℝ≥0∞) / n
```

```lean
/-- **Half-aggregation is unforgeable under the discrete-log assumption**, in
the algebraic group model with both hashes as random oracles:
`halfagg_unforgeable_rom` chained with `Taproot.BIP340Security.euf_cma_dlog`.

For an algebraic forger with at most `q` randomizer requests, `qH` challenge
queries, `qS` signing requests and forgeries of at most `ℓ` items, let
`Q = qH + qS + ℓ + 1` and

`ε = Pr[forger wins] - (q + 1)/n - qS⋅(qS + Q)⋅2/(n - 1)`.

Then a discrete-log solver built from the forger succeeds with probability at
least `ε⋅(ε/(Q + 1) - 1/n)`. The first loss is this project's tight step, the
rest is the forking-lemma loss of BIP340 itself. -/
theorem halfagg_dlog [Inhabited M] [Finite M] [Finite X]
    [SampleableType (M × (X × X) → ZMod n)] (hx0 : C.liftX (C.x 0) = none)
    (F : RomForger n E X M) (q qH qS ℓ : ℕ)
    (hq : ∀ input, (F.main input).IsQueryBoundP (fun t => isRandCall t) q)
    (hH : ∀ input, (F.main input).IsQueryBoundP (fun t => isChalCall t) qH)
    (hS : ∀ input, (F.main input).IsQueryBoundP (fun t => isSignCall t) qS)
    (hL : ∀ input, ∀ out ∈ support (F.main input), out.value.data.ms.length ≤ ℓ) :
    let ε := aggAdvantageROM C F - (q + 1 : ℝ≥0∞) / n -
      (qS : ℝ≥0∞) * (qS + (qH + qS + ℓ + 1 : ℕ)) * (2 / ((n - 1 : ℕ) : ℝ≥0∞))
    ε * (ε / ((qH + qS + ℓ + 1 : ℕ) + 1 : ℝ≥0∞) - FiatShamir.challengeSpaceInv (ZMod n)) ≤
      Pr{let x ← (dlogExperiment C (dlogOfKeyRecovery C
        (FiatShamir.cmaReduction (sigma C) (keyGen C) M (simTranscript C) (reductionROM C F)
          (qH + qS + ℓ + 1))))}[x = true]
```
