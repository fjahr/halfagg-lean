import Halfagg.Proofs.HashedBinding
import Halfagg.Binding

/-!
# Binding with the challenge hash as BIP340 computes it

`halfagg_binding` is for a challenge hash that returns a uniform scalar. The
theorems here are for the game `bindExperimentH` of
`Halfagg/SecurityHashed.lean`, where the oracle returns a hash output, the
adversary sees it and the game reduces it. The game reads at most `qC + 2⋅ℓ`
hash outputs: the adversary's queries and one for every item of the two lists.
-/

open OracleSpec OracleComp
open scoped ENNReal

namespace Halfagg.Security

open Taproot Taproot.Curve Taproot.BIP340

variable {n : ℕ} [Fact n.Prime] {H Hc E X M : Type} [AddCommGroup E] [DecidableEq E]
  [DecidableEq X] [DecidableEq M] (C : Curve n E X)
variable [SampleableType H] (red : H → ZMod n) (redc : Hc → ZMod n)

/-- **The binding game with hash outputs against the game with scalars.** For an
adversary with at most `qC` challenge-hash queries and aggregates of at most `ℓ`
signatures:

`Pr[A wins with hash outputs] ≤ Pr[A.viaRep rep wins with scalars] + (qC + 2⋅ℓ)⋅δ`,

with `rep` and `δ` as in `halfagg_hashed_le`. -/
theorem halfagg_binding_hashed_le [Finite M] [Finite X] [Finite Hc] [SampleableType Hc]
    [SampleableType (M × (X × X) → Hc)] [SampleableType (M × (X × X) → ZMod n)]
    (rep : ZMod n → Hc) (hrep : ∀ c, redc (rep c) = c) (A : BindAdversaryH n H Hc X M)
    (qC ℓ : ℕ) (hC : A.main.IsQueryBoundP (fun t => isChalB t) qC)
    (hL : ∀ out ∈ support A.main, out.1.rs.length ≤ ℓ)
    (δ : ℝ≥0∞) (hδ : RepBound redc rep δ) :
    bindAdvantageH C red redc A ≤
      bindAdvantage C red (A.viaRep rep) + ((qC + 2 * ℓ : ℕ) : ℝ≥0∞) * δ :=
  (bindAdvantageH_le_viaRep C red redc rep hrep A qC ℓ hC hL).trans
    (add_le_add le_rfl (mul_le_mul' le_rfl hδ))

/-- **Half-aggregation is binding, with the challenge hash as BIP340 computes
it**: `halfagg_binding` for the game with hash outputs. An adversary with at
most `qC` challenge-hash queries, `qZ` randomizer-hash queries and aggregates of
at most `ℓ` signatures wins with probability at most

`(qC + 2⋅ℓ)²/n + (qZ + 2⋅ℓ)²⋅μ + (qC + 2⋅ℓ)⋅δ`. -/
theorem halfagg_binding_hashed [Finite M] [Finite X] [Finite Hc] [SampleableType Hc]
    [SampleableType (M × (X × X) → Hc)] [SampleableType (M × (X × X) → ZMod n)]
    (hord : PrimeOrder n E) (rep : ZMod n → Hc) (hrep : ∀ c, redc (rep c) = c)
    (A : BindAdversaryH n H Hc X M) (qC qZ ℓ : ℕ)
    (hC : A.main.IsQueryBoundP (fun t => isChalB t) qC)
    (hZ : A.main.IsQueryBoundP (fun t => isRandB t) qZ)
    (hL : ∀ out ∈ support A.main, out.1.rs.length ≤ ℓ) (μ : ℝ≥0∞) (hμ : RedBound red μ)
    (δ : ℝ≥0∞) (hδ : RepBound redc rep δ) :
    bindAdvantageH C red redc A ≤
      (((qC + 2 * ℓ) * (qC + 2 * ℓ) : ℕ) : ℝ≥0∞) / n +
        (((qZ + 2 * ℓ) * (qZ + 2 * ℓ) : ℕ) : ℝ≥0∞) * μ + ((qC + 2 * ℓ : ℕ) : ℝ≥0∞) * δ :=
  (halfagg_binding_hashed_le C red redc rep hrep A qC ℓ hC hL δ hδ).trans
    (add_le_add (halfagg_binding C red hord (A.viaRep rep) qC qZ ℓ
      (viaRepB_queries rep A _ qC hC) (viaRepB_queries rep A _ qZ hZ)
      (fun out hout => hL out (viaRepB_support rep _ out hout)) μ hμ) le_rfl)

/-- The theorem for secp256k1, BIP458's randomizer hash and BIP340's challenge
hash: both are 256-bit values reduced modulo `n`. -/
theorem secp256k1_halfagg_binding_256 {M : Type} [DecidableEq M] [Finite M]
    [SampleableType (M × (Secp256k1.F × Secp256k1.F) → Fin (2 ^ 256))]
    [SampleableType (M × (Secp256k1.F × Secp256k1.F) → ZMod Secp256k1.n)]
    (A : BindAdversaryH Secp256k1.n (Fin (2 ^ 256)) (Fin (2 ^ 256)) Secp256k1.F M)
    (qC qZ ℓ : ℕ)
    (hC : A.main.IsQueryBoundP (fun t => isChalB t) qC)
    (hZ : A.main.IsQueryBoundP (fun t => isRandB t) qZ)
    (hL : ∀ out ∈ support A.main, out.1.rs.length ≤ ℓ) :
    bindAdvantageH secp256k1F red256 red256 A ≤
      (((qC + 2 * ℓ) * (qC + 2 * ℓ) : ℕ) : ℝ≥0∞) / Secp256k1.n +
        (((qZ + 2 * ℓ) * (qZ + 2 * ℓ) : ℕ) : ℝ≥0∞) * (2 / ((2 ^ 256 : ℕ) : ℝ≥0∞)) +
        ((qC + 2 * ℓ : ℕ) : ℝ≥0∞) * (1 / 2 ^ 127) :=
  halfagg_binding_hashed secp256k1F red256 red256 secp256k1_primeOrder rep256 red256_rep256 A
    qC qZ ℓ hC hZ hL _ secp256k1_redBound _ secp256k1_repBound

end Halfagg.Security
