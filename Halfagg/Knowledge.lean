import Halfagg.Proofs.Knowledge
import Halfagg.Proofs.Secp256k1
import Halfagg.Hash256

/-!
# Whoever produces a verifying aggregate knows the individual signatures

The theorem, over the definitions of `Halfagg/SecurityKnowledge.lean`.
-/

open OracleSpec OracleComp AlgebraicGroupModel.Interaction
open scoped ENNReal

namespace Halfagg.Security

open Taproot Taproot.Curve Taproot.BIP340

attribute [local instance] smulVal

variable {n : ℕ} [Fact n.Prime] {H E X M : Type} [AddCommGroup E] [DecidableEq E]
  [DecidableEq X] [DecidableEq M] (C : Curve n E X) (challenge : X → X → M → ZMod n)
variable [SampleableType H] (red : H → ZMod n)

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
theorem halfagg_knowledge (hx0 : C.liftX (C.x 0) = none) (F : AlgForger n H E X M) (q : ℕ)
    (hq : ∀ input, (F.main input).IsQueryBoundP (fun r => isRand r.value.data) q)
    (μ : ℝ≥0∞) (hμ : RedBound red μ) :
    aggVerifyAdvantage C challenge red (erase C F) ≤
      extractAdvantage C challenge red F + (q + 1 : ℝ≥0∞) * μ := by
  classical
  rw [verify_advantage_eq, extract_advantage_eq]
  refine ((prEvent_mono_of_support _ _
    (fun t => extB C challenge t = true ∨
      (verB C challenge t = true ∧ ¬ extB C challenge t = true))
    fun t _ hw => ?_).trans (prEvent_or_le _ _ _)).trans
    (add_le_add le_rfl (know_bad C challenge hμ hx0 F q hq))
  by_cases hex : extB C challenge t = true
  · exact Or.inl hex
  · exact Or.inr ⟨hw, hex⟩

/-- **The extractor signs what the forger signs.** For every set of messages
`p`: if the forger makes at most `q` signing requests for messages in `p`, the
extractor makes at most `q` signing queries for messages in `p`. So it never
obtains a signature from its oracle that the forger did not ask for. -/
theorem extractor_sign_queries (F : AlgForger n H E X M) (p : M → Bool) (q : ℕ)
    (h : ∀ input, (F.main input).IsQueryBoundP (fun r => isSign p r.value.data) q) (pk : X) :
    (extractor C challenge red F pk).IsQueryBoundP (fun t => isSignQuery p t) q :=
  extractor_sign_bound C challenge F p q h pk

/-- The theorem for secp256k1 and BIP458's randomizer hash. -/
theorem secp256k1_halfagg_knowledge {M : Type} [DecidableEq M]
    (challenge : Secp256k1.F → Secp256k1.F → M → ZMod Secp256k1.n)
    (F : AlgForger Secp256k1.n (Fin (2 ^ 256)) Secp256k1.Point Secp256k1.F M) (q : ℕ)
    (hq : ∀ input, (F.main input).IsQueryBoundP (fun r => isRand r.value.data) q) :
    aggVerifyAdvantage Secp256k1.secp256k1 challenge red256 (erase Secp256k1.secp256k1 F) ≤
      extractAdvantage Secp256k1.secp256k1 challenge red256 F +
        (q + 1 : ℝ≥0∞) * (2 / ((2 ^ 256 : ℕ) : ℝ≥0∞)) :=
  halfagg_knowledge Secp256k1.secp256k1 challenge red256 Halfagg.Secp256k1.liftX_x_zero F q hq
    _ secp256k1_redBound

end Halfagg.Security
