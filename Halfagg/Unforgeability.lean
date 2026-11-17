import Halfagg.Proofs.BridgeGame
import Halfagg.Proofs.SignQueries
import Halfagg.Proofs.Secp256k1

/-!
# Half-aggregation is as secure as BIP340

The main theorem, over the definitions of `Halfagg/Security.lean`.
-/

open OracleSpec OracleComp AlgebraicGroupModel.Interaction
open scoped ENNReal

namespace Halfagg.Security

open Taproot Taproot.Curve Taproot.BIP340

attribute [local instance] smulVal

variable {n : ℕ} [Fact n.Prime] {E X M : Type} [AddCommGroup E] [DecidableEq E]
  [DecidableEq X] [DecidableEq M] (C : Curve n E X) (challenge : X → X → M → ZMod n)

/-- **Half-aggregation is as secure as BIP340** (Chen and Zhao, Theorem 2), in
the algebraic group model with the randomizer hash as a random oracle and for
every challenge hash: an algebraic forger that makes at most `q` randomizer
requests and forges with at most `ℓ` items wins the standard game with
probability at most the success probability of `reduction F` against BIP340,
plus `(q + ℓ)/n`.

`hx0` says the point at infinity has no x-only encoding: its x-coordinate in the
curve interface does not lift. For secp256k1 that x-coordinate is `0`, and `0`
is not an x-coordinate of the curve because `7` is not a square modulo `p`. -/
theorem halfagg_unforgeable [Inhabited M] (hx0 : C.liftX (C.x 0) = none)
    (F : AlgForger n E X M) (q ℓ : ℕ)
    (hq : ∀ input, (F.main input).IsQueryBoundP (fun r => isRand r.value.data) q)
    (hℓ : ∀ input, ∀ out ∈ support (F.main input), out.value.data.ms.length ≤ ℓ) :
    aggAdvantage C challenge (erase C F) ≤
      SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp (reduction C challenge F) +
        (q + ℓ : ℝ≥0∞) / n := by
  classical
  refine (bridge_game C challenge F).trans ?_
  refine ((prEvent_mono_of_support _ _
    (fun t => extractOK C challenge t ∨ (winT C challenge t ∧ ¬ extractOK C challenge t))
    fun t _ hw => ?_).trans (prEvent_or_le _ _ _)).trans
    (add_le_add (bridge_reduction C challenge F) (annROM_bad C challenge hx0 F q ℓ hq hℓ))
  by_cases hex : extractOK C challenge t
  · exact Or.inl hex
  · exact Or.inr ⟨hw, hex⟩


/-- The theorem for secp256k1, where the curve hypothesis holds. -/
theorem secp256k1_halfagg_unforgeable {M : Type} [DecidableEq M] [Inhabited M]
    (challenge : Secp256k1.F → Secp256k1.F → M → ZMod Secp256k1.n)
    (F : AlgForger Secp256k1.n Secp256k1.Point Secp256k1.F M) (q ℓ : ℕ)
    (hq : ∀ input, (F.main input).IsQueryBoundP (fun r => isRand r.value.data) q)
    (hℓ : ∀ input, ∀ out ∈ support (F.main input), out.value.data.ms.length ≤ ℓ) :
    aggAdvantage Secp256k1.secp256k1 challenge (erase Secp256k1.secp256k1 F) ≤
      SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp
        (reduction Secp256k1.secp256k1 challenge F) + (q + ℓ : ℝ≥0∞) / Secp256k1.n :=
  halfagg_unforgeable Secp256k1.secp256k1 challenge Halfagg.Secp256k1.liftX_x_zero F q ℓ hq hℓ

/-- **The reduction signs what the forger signs.** For every set of messages
`p`: if the forger makes at most `q` signing requests for messages in `p`, the
reduction makes at most `q` signing queries for messages in `p`. With `p` all
messages, the reduction makes no more signing queries than the forger; with
`q = 0`, it never asks for a signature the forger did not ask for. -/
theorem reduction_sign_queries [Inhabited M] (F : AlgForger n E X M) (p : M → Bool) (q : ℕ)
    (h : ∀ input, (F.main input).IsQueryBoundP (fun r => isSign p r.value.data) q) (pk : X) :
    ((reduction C challenge F).main pk).IsQueryBoundP (fun t => isSignQuery p t) q :=
  reduction_sign_bound C challenge F p q h pk

/-- **Items that fail `lift_x` never win.** Every item of a winning forgery has
an `r` and a `pk` that are x-coordinates of the curve. So the randomizer of a
list with an item that fails `lift_x` is never used by the verifier of a winning
forgery, which is why a forger may hash anything after such an item (`rawTail`). -/
theorem aggWins_lifts {pk : X} {its : List (Item X M)} {s : ZMod n} {zs : List (ZMod n)}
    {signed : M → Bool} (h : aggWins C challenge pk its s zs signed = true) :
    ∀ it ∈ its, lifts C it = true := by
  simp only [aggWins, verifyWith, Bool.and_eq_true, List.all_eq_true] at h
  have h2 := h.1.1.2
  rwa [items_map] at h2

end Halfagg.Security
