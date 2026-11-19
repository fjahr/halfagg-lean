import Halfagg.Proofs.Binding
import Halfagg.Proofs.Secp256k1

/-!
# Binding of half-aggregation

The theorem, over the definitions of `Halfagg/SecurityBinding.lean`.
-/

open OracleSpec OracleComp
open scoped ENNReal

namespace Halfagg.Security

open Taproot Taproot.Curve Taproot.BIP340

variable {n : ℕ} [Fact n.Prime] {H E X M : Type} [AddCommGroup E] [DecidableEq E]
  [DecidableEq X] [DecidableEq M] (C : Curve n E X)
variable [SampleableType H] (red : H → ZMod n)

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
        (((qZ + 2 * ℓ) * (qZ + 2 * ℓ) : ℕ) : ℝ≥0∞) * μ := by
  rw [div_eq_mul_inv]
  exact binding_bound C red hord A qC qZ ℓ hC hZ hL μ hμ

/-- The theorem for secp256k1 and BIP458's randomizer hash. That every point of
secp256k1 has order dividing `n` is a hypothesis, because taproot-lean does not
prove that the curve has `n` points. -/
theorem secp256k1_halfagg_binding {M : Type} [DecidableEq M] [Finite M]
    [SampleableType (M × (Secp256k1.F × Secp256k1.F) → ZMod Secp256k1.n)]
    (hord : PrimeOrder Secp256k1.n Secp256k1.Point)
    (A : BindAdversary Secp256k1.n (Fin (2 ^ 256)) Secp256k1.F M) (qC qZ ℓ : ℕ)
    (hC : A.main.IsQueryBoundP (fun t => isChalB t) qC)
    (hZ : A.main.IsQueryBoundP (fun t => isRandB t) qZ)
    (hL : ∀ out ∈ support A.main, out.1.rs.length ≤ ℓ) :
    bindAdvantage Secp256k1.secp256k1 red256 A ≤
      (((qC + 2 * ℓ) * (qC + 2 * ℓ) : ℕ) : ℝ≥0∞) / Secp256k1.n +
        (((qZ + 2 * ℓ) * (qZ + 2 * ℓ) : ℕ) : ℝ≥0∞) * (2 / ((2 ^ 256 : ℕ) : ℝ≥0∞)) :=
  halfagg_binding Secp256k1.secp256k1 red256 hord A qC qZ ℓ hC hZ hL _ secp256k1_redBound

end Halfagg.Security
