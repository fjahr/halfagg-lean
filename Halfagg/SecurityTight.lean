import Halfagg.SecurityROM

/-!
# A tight reduction to discrete log: definitions

`halfagg_dlog` goes through BIP340's own proof and inherits the quadratic loss
of the forking lemma. The definitions here avoid that proof. They are the
review surface of `Halfagg/UnforgeabilityTight.lean`.

`reductionROM` either reads a BIP340 signature off the forger's explanations or
computes the secret key and signs with it. `romMachine` is `reductionROM` with a
replaceable last step, and the two cases become two machines:

* `keyFin` forges only if its candidate key (`candKey`) is the secret key. Its
  simulated run, with no signing oracle and no secret key, is the discrete-log
  solver `keySolver`.
* `repFin` outputs the signature read off the explanations, and only if the
  candidate key is wrong.
-/

open OracleSpec OracleComp AlgebraicGroupModel.Interaction
open scoped ENNReal

namespace Halfagg.Security

open Taproot Taproot.Curve Taproot.BIP340 Taproot.BIP340Security

attribute [local instance] smulVal

variable {n : ℕ} [Fact n.Prime] {E X M : Type} [AddCommGroup E] [DecidableEq E]
  [DecidableEq X] [DecidableEq M] (C : Curve n E X)

/-! ## Oracle machines -/

/-- The final step of an oracle machine: from the public key, the forgery's
annotated items, `s`, the randomizers, the signed messages and the challenges of
the items, compute a forgery of the Fiat-Shamir scheme. -/
abbrev FinalStep (n : ℕ) (E X M : Type) [AddCommGroup E] [Fact n.Prime] (C : Curve n E X) :=
  Stmt C → List (AItem n X M) → ZMod n → List (ZMod n) → List M → List (ZMod n) →
    OracleComp (RomSpec n X M) (M × FSSig n X)

/-- `reductionROM` with its last step replaced by `fin`. -/
noncomputable def romMachine (F : RomForger n E X M) (fin : FinalStep n E X M C) :
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
    fin P items out.value.data.s zs st.signed es

/-- The target item of a forgery: the first item with the target key and a
message that was never signed, as in `extractForgery`. -/
def target (pk : X) (items : List (AItem n X M)) (signed : List M) : Option (AItem n X M) :=
  items.find? (fun a => a.pk == pk && !signed.contains a.m)

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

/-- A forgery that never verifies: its nonce is the x-coordinate of the point at
infinity, which does not lift. -/
def junk [Inhabited M] : M × FSSig n X := (default, ((C.x 0, C.x 0), 0))

/-- Sign the target message with the candidate key if the candidate is the secret
key, with nonce `1`. Otherwise output `junk`. -/
noncomputable def keyFin [Inhabited M] : FinalStep n E X M C :=
  fun P items s zs signed es =>
    match target (C.x P.1) items signed with
    | none => pure (junk C)
    | some a =>
      if C.mulG (candKey (knownChal items es) (C.x P.1) items s zs signed) = P.1 then do
        let e ← hashQ (n := n) (a.m, (C.x (C.mulG (C.evenScalar 1)), C.x P.1))
        pure (a.m, ((C.x (C.mulG (C.evenScalar 1)), C.x P.1),
          C.evenScalar 1 + e * candKey (knownChal items es) (C.x P.1) items s zs signed))
      else pure (junk C)

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

/-! ## The discrete-log solver -/

/-- An oracle machine up to its final step: the forgery's annotated items, `s`,
the randomizers, the signed messages and the challenges of the items. -/
noncomputable def romPrefix (F : RomForger n E X M) (P : Stmt C) :
    OracleComp (RomSpec n X M)
      (List (AItem n X M) × ZMod n × List (ZMod n) × List M × List (ZMod n)) := do
  let r ← ((simulateQ (romHandler C (C.x P.1))
    (F.main (initial C ((C.liftX (C.x P.1)).getD 0)))).run Core.init).run ∅
  let q ← ((List.range (finalItems C r.1.1 r.1.2).length).mapM fun i =>
    if i = 0 then pure 1 else romTableRO ((finalItems C r.1.1 r.1.2).take (i + 1))).run r.2
  let es ← (finalItems C r.1.1 r.1.2).mapM fun a => hashQ (n := n) (a.m, (a.r, a.pk))
  pure (finalItems C r.1.1 r.1.2, r.1.1.value.data.s, q.1, r.1.2.signed, es)

/-- **The discrete-log solver.** Run the forger's bookkeeping with VCVio's
simulated signing oracle (`simulatedNmaImpl`, which needs no secret key) and a
lazily sampled challenge hash (`Fork.roImpl`), and output the candidate key. -/
noncomputable def keySolver (F : RomForger n E X M) (P : Stmt C) : ProbComp (ZMod n) :=
  simulateQ (QueryImpl.ofLift unifSpec ProbComp + uniformSampleImpl (spec := (Unit →ₒ ZMod n)))
    ((fun w => candKey (knownChal w.1.1.1 w.1.1.2.2.2.2) (C.x P.1) w.1.1.1 w.1.1.2.1
        w.1.1.2.2.1 w.1.1.2.2.2.1) <$>
      StateT.run (simulateQ (FiatShamir.Fork.unifForward M (X × X) (ZMod n) +
          FiatShamir.Fork.roImpl M (X × X) (ZMod n))
        ((simulateQ (FiatShamir.simulatedNmaImpl (M := M) (Commit := X × X) (Chal := ZMod n)
          (Resp := ZMod n) (simTranscript C) P) (romPrefix C F P)).run ∅)) (∅, []))

end Halfagg.Security
