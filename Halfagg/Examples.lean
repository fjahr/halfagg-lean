import Halfagg.Unforgeability
import Halfagg.SecurityTight

/-!
# The theorem is not vacuous

* `demo`: a concrete algebraic forger that requests a signature, requests a
  randomizer for two items built from the returned nonce point, and outputs a
  two-item forgery that depends on the randomizer. It satisfies the hypotheses
  of `halfagg_unforgeable` with `q = 1` (`demo_theorem`).
* `aggWins_honest`: the game's win predicate holds for an honest BIP340
  signature on a message that was never signed, as a one-item aggregate.
* `demoRom`: a forger with oracle access to the challenge hash that makes a
  challenge query and satisfies `ExplainsNonces` (`demoRom_explains`), the
  extra hypothesis of `halfagg_dlog_tight`.

Nothing here claims that `demo` or `demoRom` wins the game.
-/

open OracleSpec OracleComp AlgebraicGroupModel.Interaction
open scoped ENNReal

namespace Halfagg.Examples

open Halfagg Halfagg.Security Taproot Taproot.BIP340

attribute [local instance] smulVal

section Forger

variable {n : ℕ} [Fact n.Prime] {E X : Type} [AddCommGroup E]

/-- The coefficient vector with `c` at position `j` and `0` elsewhere. -/
def uvec (L j : ℕ) (c : ZMod n) : Fin L → ZMod n := fun i => if i.val = j then c else 0

/-- A forger: request a signature on `7`, request the randomizer of the items
`(R, P*)` and `(3⋅G + P*, P*)`, then output a forgery whose second nonce point
depends on the randomizer `z`. -/
def demo : AlgForger n E X ℕ where
  main input :=
    let b0 := input.groups
    OracleComp.queryBind (spec := explainedSpec (ZMod n) (Pts E) (Request X ℕ) (Reply n X ℕ))
      (Explained.ofVectors b0 (Request.sign 7) (fun _ => [])) fun rep =>
    let b1 := extend b0 rep.groups
    let pts : (s : Unit) → List (Fin (b1 s).length → ZMod n) := fun _ =>
      [uvec _ 2 1, uvec _ 1 1, (fun i => uvec _ 0 3 i + uvec _ 1 1 i), uvec _ 1 1]
    OracleComp.queryBind (spec := explainedSpec (ZMod n) (Pts E) (Request X ℕ) (Reply n X ℕ))
      (Explained.ofVectors b1 (Request.rand [7, 8] []) pts) fun rep2 =>
    let b2 := extend b1 rep2.groups
    let z : ZMod n := rep2.data
    let s : ZMod n := rep.data
    pure (Explained.ofVectors b2 (⟨[7, 8], s + z * 3⟩ : Out n ℕ) (fun _ =>
      [uvec _ 2 1, uvec _ 1 1, (fun i => uvec _ 0 3 i + uvec _ 1 (-z) i), uvec _ 1 1]))
  algebraic input := by
    refine ⟨Explained.valid_ofVectors _ _ _, fun rep =>
      ⟨Explained.valid_ofVectors _ _ _, fun rep2 => ?_⟩⟩
    exact Explained.valid_ofVectors _ _ _

theorem demo_queries : ∀ input, ((demo (n := n) (E := E) (X := X)).main input).IsQueryBoundP
    (fun r => isRand r.value.data) 1 := by
  intro input
  have e : ∀ {α : Type}
      (t : (explainedSpec (ZMod n) (Pts E) (Request X ℕ) (Reply n X ℕ)).Domain)
      (k : _ → OracleComp (explainedSpec (ZMod n) (Pts E) (Request X ℕ) (Reply n X ℕ)) α),
      OracleComp.queryBind t k =
        (liftM ((explainedSpec (ZMod n) (Pts E) (Request X ℕ) (Reply n X ℕ)).query t) >>= k) :=
    fun _ _ => rfl
  unfold demo
  simp only [e]
  refine (isQueryBoundP_query_bind_iff
    (fun r : Explained (ZMod n) (Request X ℕ) (Pts E) => isRand r.value.data = true) _ _ _).mpr
    ⟨Or.inl (fun h => ?_), fun rep => ?_⟩
  · exact Bool.noConfusion h
  refine (isQueryBoundP_query_bind_iff
    (fun r : Explained (ZMod n) (Request X ℕ) (Pts E) => isRand r.value.data = true) _ _ _).mpr
    ⟨Or.inr ?_, fun rep2 => ?_⟩
  · exact Nat.lt_of_lt_of_le Nat.one_pos (by simp [Explained.ofVectors, isRand])
  exact isQueryBoundP_pure _ _ _

/-- The main theorem applies to `demo` with `q = 1`. -/
theorem demo_theorem [DecidableEq E] [DecidableEq X] (C : Curve n E X)
    (challenge : X → X → ℕ → ZMod n) (hx0 : C.liftX (C.x 0) = none) :
    aggAdvantage C challenge (erase C demo) ≤
      SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp (reduction C challenge demo) +
        ((1 : ℕ) + 1 : ℝ≥0∞) / n :=
  halfagg_unforgeable C challenge hx0 demo 1 demo_queries

end Forger

section RomForger

variable {n : ℕ} [Fact n.Prime] {E X : Type} [AddCommGroup E] (C : Curve n E X)

/-- A forger with oracle access to the challenge hash that explains its nonce:
it sends the point `3⋅G + P*` in a randomizer request for the empty list, asks
for the challenge of the message `8` with that point's x-coordinate as nonce,
and outputs a one-item forgery with the challenge as `s`. -/
def demoRom : RomForger n E X ℕ where
  main input :=
    let b0 := input.groups
    let req : Explained (ZMod n) (Request X ℕ) (Pts E) :=
      Explained.ofVectors b0 (Request.rand [] []) (fun _ => [fun i => uvec _ 0 3 i + uvec _ 1 1 i])
    OracleComp.queryBind (spec := RomForgerSpec n E X ℕ) (.inr req) fun rep =>
    let b1 := extend b0 rep.groups
    let r : X := C.x ((req.value.groups ()).headD 0)
    OracleComp.queryBind (spec := RomForgerSpec n E X ℕ) (.inl (8, (r, r))) fun e =>
    pure (Explained.ofVectors b1 (⟨[8], e⟩ : Out n ℕ) (fun _ =>
      [(fun i => uvec _ 0 3 i + uvec _ 1 1 i), uvec _ 1 1]))
  algebraic _ _ :=
    ⟨Explained.valid_ofVectors _ _ _, fun _ => Explained.valid_ofVectors _ _ _⟩

/-- `demoRom` explains the nonce of its challenge query. -/
theorem demoRom_explains [DecidableEq X] (input : Message Unit (Pts E)) :
    ExplainsNonces C ((demoRom (n := n) C).main input) [] :=
  fun _ => ⟨by simp [Explained.ofVectors, isRand], fun _ => trivial⟩

end RomForger

section Win

variable {n : ℕ} [Fact n.Prime] {E X M : Type} [AddCommGroup E] [DecidableEq E]
  [DecidableEq X] (C : Curve n E X) (challenge : X → X → M → ZMod n)

/-- The win predicate is satisfiable: an honest signature on a never-signed
message wins as a one-item aggregate. -/
theorem aggWins_honest (nonce : ZMod n → X → M → ZMod n) {sk : ZMod n} {m : M} {pk r : X}
    {s : ZMod n} (hpk : pubkey C sk = some pk) (hsig : sign C challenge nonce sk m = some (r, s)) :
    aggWins C challenge pk [(r, pk, m)] s [1] (fun _ => false) = true := by
  have h := verify_sign C challenge nonce hpk hsig
  rw [← verifyAggregate_single C challenge (fun _ => 0)] at h
  simp only [verifyAggregate, verifyWith, items, z] at h
  simp only [aggWins, verifyWith, items]
  simpa using h

end Win

end Halfagg.Examples
