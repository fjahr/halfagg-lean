import Halfagg.Unforgeability
import VCVio.OracleComp.QueryTracking.RandomOracle.ExpectedFreshQuery

/-!
# The challenge hash as a random oracle: definitions

`halfagg_unforgeable` holds for every challenge hash. To chain it with a proof
of BIP340 unforgeability in the random oracle model, the forger and the
reduction must reach the challenge hash only through an oracle. This file
defines that setting; `Halfagg/UnforgeabilityROM.lean` has the theorems.

* **Forger.** A `RomForger` is an algebraic forger with one more oracle, the
  challenge hash on `(m, (r, pk))`. Its challenge queries are raw x-only
  encodings: it does not explain them.
* **Game.** `aggExperimentROM` samples the whole challenge hash table uniformly
  and then runs the game of `Halfagg/Security.lean` with it. This needs a finite
  message type, which BIP458's 32-byte messages are.
* **Target.** The BIP340 game is VCVio's EUF-CMA game for the Fiat-Shamir
  transform of taproot-lean's Σ-protocol (`Taproot.BIP340Security.sigma`), with
  a lazily sampled random oracle. This is the game of
  `Taproot.BIP340Security.euf_cma`. Its public keys are even-y points and its
  signatures are `((r, pk), s)`.
* **Reduction.** `reductionROM` is `reduction` as an oracle machine: wherever
  `reduction` evaluates the challenge hash, it queries the oracle.
-/

open OracleSpec OracleComp AlgebraicGroupModel.Interaction
open scoped ENNReal

namespace Halfagg.Security

open Taproot Taproot.Curve Taproot.BIP340 Taproot.BIP340Security

attribute [local instance] smulVal

variable {n : ℕ} [Fact n.Prime] {E X M : Type} [AddCommGroup E] [DecidableEq E]
  [DecidableEq X] [DecidableEq M] (C : Curve n E X)

/-- The challenge hash as an oracle on `(m, (r, pk))`, the input order of VCVio's
Fiat-Shamir transform. -/
abbrev ChalSpec (n : ℕ) (X M : Type) := (M × (X × X)) →ₒ ZMod n

/-- The challenge function of a complete answer table. -/
def hOf (g : M × (X × X) → ZMod n) : X → X → M → ZMod n := fun r pk m => g (m, (r, pk))

/-- A forger's oracles: the challenge hash and the requests of an `AlgForger`. -/
abbrev RomForgerSpec (n : ℕ) (E X M : Type) :=
  ChalSpec n X M + explainedSpec (ZMod n) (Pts E) (Request X M) (Reply n X M)

/-- Answer challenge-hash queries from the table `g` and pass requests on. -/
def answerChal (g : M × (X × X) → ZMod n) :
    QueryImpl (RomForgerSpec n E X M)
      (OracleComp (explainedSpec (ZMod n) (Pts E) (Request X M) (Reply n X M)))
  | .inl key => pure (g key)
  | .inr t => liftM ((explainedSpec (ZMod n) (Pts E) (Request X M) (Reply n X M)).query t)

/-- An algebraic forger with oracle access to the challenge hash. For every
answer table, the forger with its challenge queries answered from the table is
algebraic. -/
structure RomForger (n : ℕ) (E X M : Type) [AddCommGroup E] where
  main : Message Unit (Pts E) →
    OracleComp (RomForgerSpec n E X M) (Explained (ZMod n) (Out n M) (Pts E))
  algebraic : ∀ (g : M × (X × X) → ZMod n) input,
    IsAlgebraic input.groups (simulateQ (answerChal g) (main input))

/-- The forger with its challenge queries answered from the table `g`. -/
def RomForger.at (F : RomForger n E X M) (g : M × (X × X) → ZMod n) : AlgForger n E X M where
  main input := simulateQ (answerChal g) (F.main input)
  algebraic := F.algebraic g

/-- **The game with the challenge hash as a random oracle**: sample the challenge
hash table, then play the game of `aggExperiment` with it. The randomizer hash is
a lazily sampled random oracle as before. -/
noncomputable def aggExperimentROM [SampleableType (M × (X × X) → ZMod n)]
    (F : RomForger n E X M) : ProbComp Bool := do
  let g ← $ᵗ (M × (X × X) → ZMod n)
  (simulateQ (RandSpec n X M).romImpl (aggExperiment C (hOf g) (erase C (F.at g)))).run' ∅

/-- The forger's success probability. -/
noncomputable def aggAdvantageROM [SampleableType (M × (X × X) → ZMod n)]
    (F : RomForger n E X M) : ℝ≥0∞ :=
  Pr{let b ← aggExperimentROM C F}[b = true]

/-! ## The reduction as an oracle machine -/

/-- A signature of the Fiat-Shamir scheme: `((r, pk), s)`. -/
abbrev FSSig (n : ℕ) (X : Type) := (X × X) × ZMod n

/-- The oracles of a BIP340 forger in the random oracle model: uniform sampling,
the challenge hash and signing. -/
abbrev RomSpec (n : ℕ) (X M : Type) := (unifSpec + ChalSpec n X M) + (M →ₒ FSSig n X)

/-- A challenge hash query. -/
def hashQ (key : M × (X × X)) : OracleComp (RomSpec n X M) (ZMod n) :=
  liftM ((RomSpec n X M).query (.inl (.inr key)))

/-- The reduction's randomizer table, as in `tableRO`. -/
noncomputable def romTableRO (l : List (AItem n X M)) :
    StateT (AnnSpec n X M).QueryCache (OracleComp (RomSpec n X M)) (ZMod n) :=
  fun c => liftM (((AnnSpec n X M).randomOracle l).run c)

/-- The reduction's handling of the forger's oracles. Challenge queries go to the
challenge oracle. Requests are handled as in `coreImpl`; after a signing reply
the reduction asks the oracle for the signature's challenge. -/
noncomputable def romHandler (pk : X) :
    QueryImpl (RomForgerSpec n E X M)
      (StateT (Core n X M) (StateT (AnnSpec n X M).QueryCache (OracleComp (RomSpec n X M))))
  | .inl key => liftM (hashQ (n := n) key)
  | .inr ⟨⟨.random k, _⟩, _⟩ => fun st => do
      let u ← (liftM ((RomSpec n X M).query (.inl (.inl k))) :
        StateT (AnnSpec n X M).QueryCache (OracleComp (RomSpec n X M)) _)
      pure (⟨u, fun _ => []⟩, st)
  | .inr ⟨⟨.rand ms tail, groups⟩, coeffs⟩ => fun st => do
      let st := memoize C st (groups ()) (coeffs ())
      let z ← romTableRO (annotate C st.memo (toItems C ms (groups ()) ++ rawTail C tail))
      pure (⟨z, fun _ => []⟩, st)
  | .inr ⟨⟨.sign msg, _⟩, _⟩ => fun st => do
      let sig ← (liftM ((RomSpec n X M).query (.inr msg)) :
        StateT (AnnSpec n X M).QueryCache (OracleComp (RomSpec n X M)) _)
      let e ← (liftM (hashQ (n := n) (msg, (sig.1.1, pk))) :
        StateT (AnnSpec n X M).QueryCache (OracleComp (RomSpec n X M)) _)
      pure (⟨sig.2, fun _ => [(C.liftX sig.1.1).getD 0]⟩,
        { st with basis := st.basis ++ [(sig.2, -e)]
                  signed := st.signed ++ [msg] })

/-- The challenge function that knows the challenges `es` of `items` and is `0`
elsewhere. -/
def knownChal (items : List (AItem n X M)) (es : List (ZMod n)) : X → X → M → ZMod n :=
  fun r pk m => ((items.zip es).find? fun ae => ae.1.r = r ∧ ae.1.pk = pk ∧ ae.1.m = m).elim 0
    (·.2)

/-- Extraction as in `extractForgery`, from the challenges `es` of the items. To
sign with an extracted secret key, the reduction asks the oracle for one more
challenge. The output is a Fiat-Shamir signature `((r, pk), s)`. -/
noncomputable def extractROM [Inhabited M] (pk : X) (items : List (AItem n X M)) (s : ZMod n)
    (zs : List (ZMod n)) (signed : List M) (es : List (ZMod n)) :
    OracleComp (RomSpec n X M) (M × FSSig n X) :=
  match items.find? (fun a => a.pk == pk && !signed.contains a.m) with
  | none => pure (default, ((pk, pk), 0))
  | some a =>
    if (starRep (knownChal items es) a).2 = 0 then
      pure (a.m, ((a.r, pk), (starRep (knownChal items es) a).1))
    else do
      let α := isum (fun i b => zs.getD i 0 * (starRep (knownChal items es) b).1) 0 items
      let β := isum (fun i b => zs.getD i 0 * (starRep (knownChal items es) b).2) 0 items
      let x := (s - α) / β
      let e ← hashQ (n := n) (a.m, (C.x (C.mulG 1), C.x (C.mulG x)))
      let sig := (BIP340.sign C (fun _ _ _ => e) (fun _ _ _ => 1) x a.m).getD (a.r, 0)
      pure (a.m, ((sig.1, pk), sig.2))

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

end Halfagg.Security
