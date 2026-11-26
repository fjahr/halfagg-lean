import Halfagg.Basic
import Taproot.BIP340Security
import AlgebraicGroupModel.Interaction

/-!
# Unforgeability of BIP458 half-aggregation: definitions

This file is the review surface for `halfagg_unforgeable`
(`Halfagg/Unforgeability.lean`): the game, the forger model and the reduction.
Proofs live under `Halfagg/Proofs/`.

The theorem formalizes Theorem 2 of Chen and Zhao, *Half-Aggregation of Schnorr
Signatures with Tight Reductions* (ESORICS 2022, eprint 2022/222), for BIP458's
scheme (their `IASchnorr`): in the algebraic group model (AGM), with the
randomizer hash as a random oracle, `reduction F` turns an algebraic
half-aggregate forger `F` into a BIP340 forger with the same signing queries that
wins with probability at least `ε - (q + 1)⋅μ`. Here `ε` is `F`'s success
probability in the standard game and `q` bounds its randomizer queries. For `μ`
see *Randomizer hash* below. It is `1/n` in Chen and Zhao's model, where the
hash is uniform in `ZMod n`.

## The game

`aggExperiment` is the aggregate chosen-key game (CK-AEUF-CMA, Boneh et al.):
the adversary gets a BIP340 public key `pk*`, a signing oracle for it and the
randomizer hash, and outputs a list of `(r, pk, m)` items and `s`. It wins if
`VerifyAggregate` accepts and some item has public key `pk*` and a message that
was never signed. It chooses all other public keys. Nothing in the game refers
to the AGM.

## Algebraic forgers

`AlgForger` is an adversary of zkSecurity's `agm-lean` interface
(`AlgebraicGroupModel.Interaction.Adversary`): every point it sends, in a
randomizer request or in its forgery, comes with coefficients over the points it
has received so far, and it carries a proof that these are valid on every reply
path. Its initial inputs are `G` and `P* = lift_x(pk*)`, and every signing reply
adds the nonce point `lift_x(r)`. Randomizer requests and forgeries list the
points `R₀, P₀, R₁, P₁, …` as group arguments and the messages as data; the hash
input uses their x-coordinates, as BIP458 does. A randomizer request can append
further items as raw x-only encodings, starting with one that fails `lift_x`
(`rawTail`). `erase` turns an `AlgForger` into
an adversary of the standard game by forwarding its requests and dropping the
explanations, so the theorem is about the standard game.

## Modelling choices

* **Challenge hash.** `challenge` is an arbitrary function, as in Chen and
  Zhao's Theorem 2: the result holds for every `hash_BIP0340/challenge`.
  `Halfagg/SecurityROM.lean` has the variant of their Remark 2, with the
  challenge hash as an oracle of the game. That variant chains with
  `Taproot.BIP340Security.euf_cma` (`halfagg_dlog`).
* **Randomizer hash.** `hash_BIP0458/randomizer` is a random oracle with uniform
  answers in a type `H` of hash outputs, and the scheme reduces an answer to a
  scalar with `red : H → ZMod n`. The theorems hold for every `H` and `red` and
  lose `μ` per randomizer, where `μ` bounds the probability that `red` of a
  uniform hash output is a given scalar. For BIP458, `H` is the 256-bit strings
  and `red` is `int(⋅) mod n` (`Halfagg/Hash256.lean`).
* **BIP340** (`bip340`). Secret keys are uniform nonzero scalars, and
  `BIP340.sign` normalizes key and nonce as BIP340 does. The nonce of a
  signature comes from a `NonceGen`: any distribution on the nonzero scalars
  that depends on the secret key and the message. The theorems of
  `Halfagg/Unforgeability.lean` and `Halfagg/Knowledge.lean` hold for every
  `NonceGen`, so also for BIP340's own derivation, which hashes the key, the
  message and auxiliary randomness. The reduction is a VCVio
  `SignatureAlg.UnforgeableAdversary` and is measured by VCVio's
  `unforgeableAdvantage`, against BIP340 with the same `NonceGen`.
* **Scalars act on points** by `k⋅P = k.val • P` (`smulVal`), as in `Taproot.Curve`.

## Limitations

* **x-only encodings count as group elements.** An algebraic forger names the
  `r` and `pk` it hashes or outputs through points it can explain: the AGM
  assumption, applied to x-only encodings. The exception is `rawTail`: after an
  item whose `r` or `pk` is not an x-coordinate of the curve, a request can hash
  arbitrary encodings, because no list with such an item passes
  `VerifyAggregate` (`aggWins_lifts`). A forgery cannot contain such an item,
  and for the same reason that loses nothing.
* **Running time is not formalized.** `reduction` is explicit, so its cost can
  be read off, but no theorem bounds it.
-/

open OracleSpec OracleComp AlgebraicGroupModel.Interaction
open scoped ENNReal

namespace Halfagg.Security

open Taproot Taproot.Curve Taproot.BIP340 Taproot.BIP340Security

/-! ## BIP340 as a signature scheme -/

section BIP340

variable {n : ℕ} [Fact n.Prime] {E X M : Type} [AddCommGroup E] [DecidableEq E]
  [DecidableEq X] (C : Curve n E X) (challenge : X → X → M → ZMod n)

/-- **How the signer derives the nonce of a signature**: a distribution on the
nonzero scalars for every secret key and message. BIP340 hashes the key, the
message and auxiliary randomness, which is such a distribution for fixed hash
functions. The signer keeps no state between signatures, and a derivation that
can give the nonce `0`, where BIP340 fails, is not covered.

It is a class so that the proofs need not pass it along. -/
class NonceGen (n : ℕ) (M : Type) where
  /-- The nonce for a secret key and a message. -/
  draw : ZMod n → M → ProbComp (NonzeroScalar n)

/-- Uniformly random nonces, as in taproot-lean's proof of BIP340. The theorems
with the challenge hash as a random oracle are for this derivation. -/
@[reducible] noncomputable def NonceGen.uniform (n : ℕ) [Fact n.Prime] (M : Type) :
    NonceGen n M :=
  ⟨fun _ _ => $ᵗ (NonzeroScalar n)⟩

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

end BIP340

/-! ## The half-aggregation game -/

section Game

variable {n : ℕ} [Fact n.Prime] {H E X M : Type} [AddCommGroup E] [DecidableEq E]
  [DecidableEq X] [DecidableEq M] (C : Curve n E X) (challenge : X → X → M → ZMod n)
  (red : H → ZMod n)

/-- The randomizer hash as a random oracle on lists of `(r, pk, m)` items. Its
outputs have type `H`, for BIP458 the 256-bit strings. -/
abbrev RandSpec (H X M : Type) := List (Item X M) →ₒ H

/-- The signing oracle: a message to a BIP340 signature `(r, s)`. -/
abbrev SignSpec (n : ℕ) (X M : Type) := M →ₒ (X × ZMod n)

/-- The adversary's oracles: uniform sampling, the randomizer hash and signing. -/
abbrev GameSpec (n : ℕ) (H X M : Type) := (unifSpec + RandSpec H X M) + SignSpec n X M

/-- An adversary of the standard game: given the target public key, it outputs
`(r, pk, m)` items and `s`, i.e. the aggregate signature `r₀ ‖ … ‖ bytes(s)` for
the pairs `(pkᵢ, mᵢ)`. -/
structure AggAdversary (n : ℕ) (H X M : Type) where
  main (pk : X) : OracleComp (GameSpec n H X M) (List (Item X M) × ZMod n)

/-- The verifier's randomizer `zᵢ`: `1` for `i = 0`, otherwise the randomizer
hash of the first `i + 1` items, reduced to a scalar by `red`. For BIP458, `red`
is `int(⋅) mod n`. -/
def zQuery (its : List (Item X M)) (i : ℕ) : OracleComp (unifSpec + RandSpec H X M) (ZMod n) :=
  if i = 0 then pure 1 else red <$> HasQuery.query (spec := RandSpec H X M) (its.take (i + 1))

/-- `red` of a uniform hash output is any given scalar with probability at most
`μ`. -/
def RedBound [SampleableType H] (μ : ℝ≥0∞) : Prop :=
  ∀ c : ZMod n, Pr{let h ← $ᵗ H}[red h = c] ≤ μ

/-- The adversary wins if `VerifyAggregate` accepts with the randomizers `zs` and
some item has the target public key and a message that was never signed. -/
def aggWins (pk : X) (its : List (Item X M)) (s : ZMod n) (zs : List (ZMod n))
    (signed : M → Bool) : Bool :=
  verifyWith C challenge (fun i => zs.getD i 0) ⟨its.map (·.1), s⟩ (its.map (·.2)) &&
    its.any fun it => it.2.1 == pk && !signed it.2.2

/-- The aggregate chosen-key unforgeability game (CK-AEUF-CMA) with the
randomizer hash as a random oracle. -/
noncomputable def aggExperiment [NonceGen n M] (A : AggAdversary n H X M) :
    OracleComp (unifSpec + RandSpec H X M) Bool := do
  let alg := bip340 (M := M) C challenge (OracleComp (unifSpec + RandSpec H X M))
  let (pk, sk) ← alg.keygen
  let ((its, s), log) ← alg.runWithSigningOracle pk sk (A.main pk)
  let zs ← (List.range its.length).mapM (zQuery red its)
  return aggWins C challenge pk its s zs log.wasQueried

/-- The adversary's success probability, with a lazily sampled random oracle. -/
noncomputable def aggAdvantage [NonceGen n M] [SampleableType H] (A : AggAdversary n H X M) :
    ℝ≥0∞ :=
  (ProbCompRuntime.rom (RandSpec H X M)).evalDist (aggExperiment C challenge red A) {true}

end Game

/-! ## Algebraic forgers -/

section Forger

variable {n : ℕ} [Fact n.Prime] {H E X M : Type} [AddCommGroup E] [DecidableEq E]
  [DecidableEq X] [DecidableEq M] (C : Curve n E X)

/-- Points form the single group sort of the AGM interface. -/
abbrev Pts (E : Type) : Unit → Type := fun _ => E

/-- Scalars act on points by `k⋅P = k.val • P`. -/
@[reducible] def smulVal (n : ℕ) (E : Type) [AddCommGroup E] : SMul (ZMod n) E :=
  ⟨fun k P => k.val • P⟩

attribute [local instance] smulVal

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

/-- Replies: a sample, a randomizer hash, or the `s` of a signature (its nonce
point `lift_x(r)` is the reply's group argument). -/
def Reply (n : ℕ) (H X M : Type) : Request X M → Type
  | .random k => Fin (k + 1)
  | .rand _ _ => H
  | .sign _ => ZMod n

/-- A forgery: the messages `[m₀, …]` and `s`, with the points `R₀, P₀, …` as
group arguments. -/
structure Out (n : ℕ) (M : Type) where
  ms : List M
  s : ZMod n

/-- An algebraic half-aggregation forger in `agm-lean`'s interface. -/
abbrev AlgForger (n : ℕ) (H E X M : Type) [AddCommGroup E] :=
  AlgebraicGroupModel.Interaction.Adversary (ZMod n) (Pts E) Unit (Request X M) (Reply n H X M)
    (Out n M)

/-- The forger's initial inputs `[G, P*]`. -/
def initial (Pstar : E) : Message Unit (Pts E) := ⟨(), fun _ => [C.G, Pstar]⟩

/-- `[R₀, P₀, R₁, P₁, …]` as pairs `(Rᵢ, Pᵢ)`. -/
def pairs : List E → List (E × E)
  | R :: P :: rest => (R, P) :: pairs rest
  | _ => []

/-- The items `(x(Rᵢ), x(Pᵢ), mᵢ)` named by messages and points. -/
def toItems (ms : List M) (pts : List E) : List (Item X M) :=
  (ms.zip (pairs pts)).map fun mRP => (C.x mRP.2.1, C.x mRP.2.2, mRP.1)

/-- The raw tail of a randomizer request. It is used only if its first item
fails `lift_x` for `r` or `pk`; otherwise it is dropped. No list that extends
such an item passes `VerifyAggregate`, so the forger may hash anything after
it without explaining it. -/
def rawTail : List (Item X M) → List (Item X M)
  | [] => []
  | it :: rest => if lifts C it then [] else it :: rest

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

/-- The standard-game adversary that runs `F` and drops its explanations. -/
noncomputable def erase (F : AlgForger n H E X M) : AggAdversary n H X M where
  main pk := (fun out => (toItems C out.value.data.ms (out.value.groups ()), out.value.data.s)) <$>
    simulateQ (fun q => eraseImpl C q.value) (F.main (initial C ((C.liftX pk).getD 0)))

end Forger

/-! ## The reduction -/

section Reduction

variable {n : ℕ} [Fact n.Prime] {H E X M : Type} [AddCommGroup E] [DecidableEq E]
  [DecidableEq X] [DecidableEq M] (C : Curve n E X) (challenge : X → X → M → ZMod n)
  (red : H → ZMod n)

attribute [local instance] smulVal

/-- A representation `(α, β)` of the point `α⋅G + β⋅P*`. -/
abbrev Rep (n : ℕ) := ZMod n × ZMod n

/-- Flatten coefficients over the received points into a representation over
`(G, P*)`, given the representations `basis` of the received points. -/
def flatten (coeff : List (ZMod n)) (basis : List (Rep n)) : Rep n :=
  isum (fun i ρ => ((coeff[i]?).getD 0 * ρ.1, (coeff[i]?).getD 0 * ρ.2)) 0 basis

/-- The representation of `lift_x(x(Y))`, which is `Y` or `-Y`, from one of `Y`. -/
def liftRep (Y : E) (ρ : Rep n) : Rep n := if C.hasEvenY Y then ρ else -ρ

/-- An item `(r, pk, m)` with representations of `lift_x(r)` and `lift_x(pk)`. -/
structure AItem (n : ℕ) (X M : Type) where
  r : X
  pk : X
  m : M
  repR : Rep n
  repPk : Rep n
  deriving DecidableEq

/-- The reduction's bookkeeping: representations of the received points in order,
the first representation of each x-coordinate's lifted point, and the signed
messages. -/
structure Core (n : ℕ) (X M : Type) where
  basis : List (Rep n)
  memo : X → Option (Rep n)
  signed : List M

/-- Before the first query: the received points are `G = 1⋅G` and `P* = 1⋅P*`. -/
def Core.init : Core n X M := ⟨[(1, 0), (0, 1)], fun _ => none, []⟩

/-- Record the representation of `lift_x(x(Y))` from the coefficients of `Y`,
unless the x-coordinate already has one. -/
def memoRecord (basis : List (Rep n)) (memo : X → Option (Rep n)) (Y : E)
    (coeff : List (ZMod n)) : X → Option (Rep n) :=
  match memo (C.x Y) with
  | some _ => memo
  | none => Function.update memo (C.x Y) (some (liftRep C Y (flatten coeff basis)))

/-- Record every point of a list; the `j`-th point uses the `j`-th coefficient
vector, and a missing vector counts as empty. -/
def memoizeList (basis : List (Rep n)) :
    List E → List (List (ZMod n)) → (X → Option (Rep n)) → (X → Option (Rep n))
  | [], _, memo => memo
  | Y :: pts, coeffs, memo =>
      memoizeList basis pts coeffs.tail (memoRecord C basis memo Y (coeffs.headD []))

/-- Record the first representation of each point's lifted x-coordinate. -/
def memoize (st : Core n X M) (pts : List E) (coeffs : List (List (ZMod n))) : Core n X M :=
  { st with memo := memoizeList C st.basis pts coeffs st.memo }

/-- Items annotated with the recorded representations, up to the first item
that fails `lift_x`. That item and all later ones get the representation `0`:
they come from a raw tail or name the point at infinity, and no list containing
them passes `VerifyAggregate`. -/
def annotate (memo : X → Option (Rep n)) : List (Item X M) → List (AItem n X M)
  | [] => []
  | it :: rest =>
    if lifts C it then
      ⟨it.1, it.2.1, it.2.2, (memo it.1).getD 0, (memo it.2.1).getD 0⟩ :: annotate memo rest
    else (it :: rest).map fun it => ⟨it.1, it.2.1, it.2.2, 0, 0⟩

/-- The forgery's annotated items, after recording its representations. -/
def finalItems (out : Explained (ZMod n) (Out n M) (Pts E)) (st : Core n X M) :
    List (AItem n X M) :=
  annotate C (memoize C st (out.value.groups ()) (out.coefficients ())).memo
    (toItems C out.value.data.ms (out.value.groups ()))

/-- The reduction's handling of a forger's requests, generic in how uniform
samples (`unif`), randomizers of annotated lists (`ro`) and signatures (`sg`)
are obtained. Before a randomizer is drawn, the representations of the request's
points are recorded; every signature adds its nonce point `lift_x(r) = s⋅G - e⋅P*`
to the received basis. -/
def coreImpl {m : Type → Type} [Monad m] (pk : X) (unif : (k : ℕ) → m (Fin (k + 1)))
    (ro : List (AItem n X M) → m H) (sg : M → m (X × ZMod n)) :
    QueryImpl (explainedSpec (ZMod n) (Pts E) (Request X M) (Reply n H X M))
      (StateT (Core n X M) m)
  | ⟨⟨.random k, _⟩, _⟩ => fun st => do
      let u ← unif k
      pure (⟨u, fun _ => []⟩, st)
  | ⟨⟨.rand ms tail, groups⟩, coeffs⟩ => fun st => do
      let st := memoize C st (groups ()) (coeffs ())
      let z ← ro (annotate C st.memo (toItems C ms (groups ()) ++ rawTail C tail))
      pure (⟨z, fun _ => []⟩, st)
  | ⟨⟨.sign msg, _⟩, _⟩ => fun st => do
      let sig ← sg msg
      pure (⟨sig.2, fun _ => [(C.liftX sig.1).getD 0]⟩,
        { st with basis := st.basis ++ [(sig.2, -challenge sig.1 pk msg)]
                  signed := st.signed ++ [msg] })

/-- `(α*, β*)` of an item: `Rᵢ + cᵢ⋅Pᵢ = α*⋅G + β*⋅P*`, from the representations
of `Rᵢ = lift_x(rᵢ)` and `Pᵢ = lift_x(pkᵢ)` and the challenge `cᵢ`. -/
def starRep (a : AItem n X M) : Rep n :=
  let c := challenge a.r a.pk a.m
  (a.repR.1 + c * a.repPk.1, a.repR.2 + c * a.repPk.2)

/-- The reduction's BIP340 forgery for the first item `k` with the target key
and an unsigned message (Chen and Zhao, proof of Theorem 1):
* if `β*ₖ = 0`, then `Rₖ + cₖ⋅P* = α*ₖ⋅G`, so `(rₖ, α*ₖ)` is a BIP340 signature
  on `mₖ`;
* otherwise `s⋅G = Σ zᵢ⋅(Rᵢ + cᵢ⋅Pᵢ) = α*⋅G + β*⋅P*` with `α* = Σ zᵢ⋅α*ᵢ` and
  `β* = Σ zᵢ⋅β*ᵢ`, so `x = (s - α*)/β*` is the secret key of `P*` when
  `β* ≠ 0`, and the reduction signs `mₖ` with it. `β* = 0` is the bad event. -/
def extractForgery [Inhabited M] (pk : X) (items : List (AItem n X M)) (s : ZMod n)
    (zs : List (ZMod n)) (signed : List M) : M × (X × ZMod n) :=
  match items.find? (fun a => a.pk == pk && !signed.contains a.m) with
  | none => (default, (pk, 0))
  | some a =>
    if (starRep challenge a).2 = 0 then (a.m, (a.r, (starRep challenge a).1))
    else
      let α := isum (fun i b => zs.getD i 0 * (starRep challenge b).1) 0 items
      let β := isum (fun i b => zs.getD i 0 * (starRep challenge b).2) 0 items
      (a.m, (BIP340.sign C challenge (fun _ _ _ => 1) ((s - α) / β) a.m).getD (a.r, 0))

/-- The reduction's randomizer oracle: a random oracle on annotated lists. -/
abbrev AnnSpec (n : ℕ) (H X M : Type) := List (AItem n X M) →ₒ H

/-- Look up or sample a randomizer in the reduction's table, which is VCVio's
lazily sampled random oracle run inside the reduction. -/
noncomputable def tableRO [SampleableType H] (l : List (AItem n X M)) :
    StateT (AnnSpec n H X M).QueryCache (OracleComp (unifSpec + SignSpec n X M)) H :=
  fun c => liftM (((AnnSpec n H X M).randomOracle l).run c)

/-- The reduction's randomizers for its final items, from the same table. -/
noncomputable def tableZs [SampleableType H] (items : List (AItem n X M)) :
    StateT (AnnSpec n H X M).QueryCache (OracleComp (unifSpec + SignSpec n X M)) (List (ZMod n)) :=
  (List.range items.length).mapM fun i =>
    if i = 0 then pure 1 else red <$> tableRO (items.take (i + 1))

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

end Reduction

/-! ## Query counting -/

section Theorem

variable {n : ℕ} [Fact n.Prime] {E X M : Type} [AddCommGroup E] [DecidableEq E]
  [DecidableEq X] [DecidableEq M] (C : Curve n E X) (challenge : X → X → M → ZMod n)

attribute [local instance] smulVal

/-- Whether a request is a randomizer request. -/
def isRand : Request X M → Bool
  | .rand _ _ => true
  | _ => false

/-- Whether a request is a signing request for a message in `p`. -/
def isSign (p : M → Bool) : Request X M → Bool
  | .sign m => p m
  | _ => false

/-- Whether a query of a BIP340 forger is a signing query for a message in `p`. -/
def isSignQuery (p : M → Bool) : ℕ ⊕ M → Bool
  | .inr m => p m
  | .inl _ => false

end Theorem

end Halfagg.Security
