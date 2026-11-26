import Halfagg.Proofs.HashedGame
import Halfagg.UnforgeabilityTight

/-!
# Unforgeability with the challenge hash as BIP340 computes it

The theorems of `Halfagg/UnforgeabilityROM.lean` and
`Halfagg/UnforgeabilityTight.lean` are for a challenge hash that returns a
uniform scalar. BIP340 reduces a 256-bit hash output modulo `n`. The theorems
here are for the game of `Halfagg/SecurityHashed.lean`, where the oracle returns
a hash output, the forger sees it and the game reduces it.

`halfagg_hashed_le` compares the two games. Fix one hash output `rep c` for every
scalar `c`. The game reads at most `qH + qS + ℓ` hash outputs: the forger's
queries, one for every signature and one for every item of the forgery. A
uniform hash output is one of the chosen outputs except with probability `δ`,
and then it is `rep` of a uniform scalar. So the forger wins at most as often as
`F.viaRep rep` wins the game with scalars, plus `(qH + qS + ℓ)⋅δ`.

The other theorems are the theorems for the game with scalars, applied to
`F.viaRep rep`. For secp256k1 and 256-bit outputs, `δ ≤ 2^-127`.
-/

open OracleSpec OracleComp AlgebraicGroupModel.Interaction
open scoped ENNReal

namespace Halfagg.Security

open Taproot Taproot.Curve Taproot.BIP340 Taproot.BIP340Security Halfagg.LoggedRun

attribute [local instance] smulVal

-- Uniform nonces, as in `Halfagg/SecurityROM.lean`.
attribute [local instance] NonceGen.uniform

variable {n : ℕ} [Fact n.Prime] {H Hc E X M : Type} [AddCommGroup E] [DecidableEq E]
  [DecidableEq X] [DecidableEq M] (C : Curve n E X)
variable [SampleableType H] (red : H → ZMod n) (redc : Hc → ZMod n)

/-- **The game with hash outputs against the game with scalars.** For a forger
with at most `qH` challenge queries, `qS` signing requests and forgeries of at
most `ℓ` items:

`Pr[F wins with hash outputs] ≤ Pr[F.viaRep rep wins with scalars] + (qH + qS + ℓ)⋅δ`,

where `rep c` is a hash output that reduces to `c` and `δ` bounds the
probability that a uniform hash output `h` is not `rep (redc h)`. -/
theorem halfagg_hashed_le [Finite M] [Finite X] [Finite Hc] [SampleableType Hc]
    [SampleableType (M × (X × X) → Hc)] [SampleableType (M × (X × X) → ZMod n)]
    (rep : ZMod n → Hc) (hrep : ∀ c, redc (rep c) = c) (F : RomForgerH n H Hc E X M)
    (qH qS ℓ : ℕ)
    (hH : ∀ input, (F.main input).IsQueryBoundP (fun t => isChalCall t) qH)
    (hS : ∀ input, (F.main input).IsQueryBoundP (fun t => isSignCall t) qS)
    (hL : ∀ input, ∀ out ∈ support (F.main input), out.value.data.ms.length ≤ ℓ)
    (δ : ℝ≥0∞) (hδ : RepBound redc rep δ) :
    aggAdvantageROMH C red redc F ≤
      aggAdvantageROM C red (F.viaRep rep) + ((qH + qS + ℓ : ℕ) : ℝ≥0∞) * δ :=
  (aggAdvantageROMH_le_viaRep C red redc rep hrep F qH qS ℓ hH hS hL).trans
    (add_le_add le_rfl (mul_le_mul' le_rfl hδ))

/-- **Half-aggregation is as secure as BIP340, with the challenge hash as BIP340
computes it**: `halfagg_unforgeable_rom` for the game with hash outputs. The
BIP340 game on the right is the game of `Taproot.BIP340Security.euf_cma`, whose
oracle returns scalars. -/
theorem halfagg_unforgeable_rom_hashed [Inhabited M] [Finite M] [Finite X] [Finite Hc]
    [SampleableType Hc] [SampleableType (M × (X × X) → Hc)]
    [SampleableType (M × (X × X) → ZMod n)] (hx0 : C.liftX (C.x 0) = none)
    (rep : ZMod n → Hc) (hrep : ∀ c, redc (rep c) = c) (F : RomForgerH n H Hc E X M)
    (q qH qS ℓ : ℕ)
    (hq : ∀ input, (F.main input).IsQueryBoundP (fun t => isRandCall t) q)
    (hH : ∀ input, (F.main input).IsQueryBoundP (fun t => isChalCall t) qH)
    (hS : ∀ input, (F.main input).IsQueryBoundP (fun t => isSignCall t) qS)
    (hL : ∀ input, ∀ out ∈ support (F.main input), out.value.data.ms.length ≤ ℓ)
    (μ : ℝ≥0∞) (hμ : RedBound red μ) (δ : ℝ≥0∞) (hδ : RepBound redc rep δ) :
    aggAdvantageROMH C red redc F ≤
      SignatureAlg.unforgeableAdvantage (FiatShamir.runtime M)
          (reductionROM C red (F.viaRep rep)) +
        (q + 1 : ℝ≥0∞) * μ + ((qH + qS + ℓ : ℕ) : ℝ≥0∞) * δ :=
  (halfagg_hashed_le C red redc rep hrep F qH qS ℓ hH hS hL δ hδ).trans
    (add_le_add (halfagg_unforgeable_rom C red hx0 (F.viaRep rep) q
      (at_queries (F.viaRep rep) q (viaRep_queries rep F _ q hq)) μ hμ) le_rfl)

/-- **Half-aggregation is unforgeable under the discrete-log assumption, with
the challenge hash as BIP340 computes it**: `halfagg_dlog` for the game with
hash outputs. With `Q = qH + qS + ℓ + 1` and

`ε = Pr[forger wins] - (qH + qS + ℓ)⋅δ - (q + 1)⋅μ - qS⋅(qS + Q)⋅2/(n - 1)`,

the discrete-log solver built from `F.viaRep rep` succeeds with probability at
least `ε⋅(ε/(Q + 1) - 1/n)`. -/
theorem halfagg_dlog_hashed [Inhabited M] [Finite M] [Finite X] [Finite Hc]
    [SampleableType Hc] [SampleableType (M × (X × X) → Hc)]
    [SampleableType (M × (X × X) → ZMod n)] (hx0 : C.liftX (C.x 0) = none)
    (rep : ZMod n → Hc) (hrep : ∀ c, redc (rep c) = c) (F : RomForgerH n H Hc E X M)
    (q qH qS ℓ : ℕ)
    (hq : ∀ input, (F.main input).IsQueryBoundP (fun t => isRandCall t) q)
    (hH : ∀ input, (F.main input).IsQueryBoundP (fun t => isChalCall t) qH)
    (hS : ∀ input, (F.main input).IsQueryBoundP (fun t => isSignCall t) qS)
    (hL : ∀ input, ∀ out ∈ support (F.main input), out.value.data.ms.length ≤ ℓ)
    (μ : ℝ≥0∞) (hμ : RedBound red μ) (δ : ℝ≥0∞) (hδ : RepBound redc rep δ) :
    let ε := aggAdvantageROMH C red redc F - ((qH + qS + ℓ : ℕ) : ℝ≥0∞) * δ -
      (q + 1 : ℝ≥0∞) * μ -
      (qS : ℝ≥0∞) * (qS + (qH + qS + ℓ + 1 : ℕ)) * (2 / ((n - 1 : ℕ) : ℝ≥0∞))
    ε * (ε / ((qH + qS + ℓ + 1 : ℕ) + 1 : ℝ≥0∞) - FiatShamir.challengeSpaceInv (ZMod n)) ≤
      Pr{let x ← (dlogExperiment C (dlogOfKeyRecovery C
        (FiatShamir.cmaReduction (sigma C) (keyGen C) M (simTranscript C)
          (reductionROM C red (F.viaRep rep)) (qH + qS + ℓ + 1))))}[x = true] := by
  intro ε
  have hd := halfagg_dlog C red hx0 (F.viaRep rep) q qH qS ℓ (viaRep_queries rep F _ q hq)
    (viaRep_queries rep F _ qH hH) (viaRep_queries rep F _ qS hS)
    (fun input out hout => hL input out (viaRep_support rep _ out hout)) μ hμ
  refine le_trans ?_ hd
  have hle := halfagg_hashed_le C red redc rep hrep F qH qS ℓ hH hS hL δ hδ
  have hε : ε ≤ aggAdvantageROM C red (F.viaRep rep) - (q + 1 : ℝ≥0∞) * μ -
      (qS : ℝ≥0∞) * (qS + (qH + qS + ℓ + 1 : ℕ)) * (2 / ((n - 1 : ℕ) : ℝ≥0∞)) :=
    tsub_le_tsub_right (tsub_le_tsub_right (tsub_le_iff_right.mpr hle) _) _
  exact mul_le_mul' hε (tsub_le_tsub_right (ENNReal.div_le_div_right hε _) _)

/-- **A tight reduction to discrete log, with the challenge hash as BIP340
computes it**: `halfagg_dlog_tight` for the game with hash outputs. For a forger
that explains the nonce of every challenge-hash query (`ExplainsNoncesH`), with
`Q = qH + qS + ℓ + 1`:

`Pr[forger wins] ≤ Pr[keySolver solves discrete log] + qS⋅(qS + Q)⋅2/(n - 1) +
(q + 1)⋅μ + (qH + 1)/n + (qH + qS + ℓ)⋅δ`. -/
theorem halfagg_dlog_tight_hashed [Inhabited M] [Finite M] [Finite X] [Finite Hc]
    [SampleableType Hc] [SampleableType (M × (X × X) → Hc)]
    [SampleableType (M × (X × X) → ZMod n)] (hx0 : C.liftX (C.x 0) = none)
    (rep : ZMod n → Hc) (hrep : ∀ c, redc (rep c) = c) (F : RomForgerH n H Hc E X M)
    (q qH qS ℓ : ℕ)
    (hq : ∀ input, (F.main input).IsQueryBoundP (fun t => isRandCall t) q)
    (hH : ∀ input, (F.main input).IsQueryBoundP (fun t => isChalCall t) qH)
    (hS : ∀ input, (F.main input).IsQueryBoundP (fun t => isSignCall t) qS)
    (hL : ∀ input, ∀ out ∈ support (F.main input), out.value.data.ms.length ≤ ℓ)
    (hE : ∀ input, ExplainsNoncesH C (F.main input) [])
    (μ : ℝ≥0∞) (hμ : RedBound red μ) (δ : ℝ≥0∞) (hδ : RepBound redc rep δ) :
    aggAdvantageROMH C red redc F ≤
      Pr{let x ← dlogExperiment C (dlogOfKeyRecovery C
          (keySolver C red (F.viaRep rep)))}[x = true] +
        (qS : ℝ≥0∞) * (qS + (qH + qS + ℓ + 1 : ℕ)) * (2 / ((n - 1 : ℕ) : ℝ≥0∞)) +
        (q + 1 : ℝ≥0∞) * μ + (qH + 1 : ℝ≥0∞) / n + ((qH + qS + ℓ : ℕ) : ℝ≥0∞) * δ :=
  (halfagg_hashed_le C red redc rep hrep F qH qS ℓ hH hS hL δ hδ).trans
    (add_le_add (halfagg_dlog_tight C red hx0 (F.viaRep rep) q qH qS ℓ
      (viaRep_queries rep F _ q hq) (viaRep_queries rep F _ qH hH)
      (viaRep_queries rep F _ qS hS)
      (fun input out hout => hL input out (viaRep_support rep _ out hout))
      (fun input => viaRep_explains C rep _ [] (hE input)) μ hμ) le_rfl)

/-- The discrete-log theorem for secp256k1, BIP458's randomizer hash and
BIP340's challenge hash: both are 256-bit values reduced modulo `n`. -/
theorem secp256k1_halfagg_dlog_256 {M : Type} [DecidableEq M] [Inhabited M] [Finite M]
    [SampleableType (M × (Secp256k1.F × Secp256k1.F) → Fin (2 ^ 256))]
    [SampleableType (M × (Secp256k1.F × Secp256k1.F) → ZMod Secp256k1.n)]
    (F : RomForgerH Secp256k1.n (Fin (2 ^ 256)) (Fin (2 ^ 256)) Secp256k1.Point Secp256k1.F M)
    (q qH qS ℓ : ℕ)
    (hq : ∀ input, (F.main input).IsQueryBoundP (fun t => isRandCall t) q)
    (hH : ∀ input, (F.main input).IsQueryBoundP (fun t => isChalCall t) qH)
    (hS : ∀ input, (F.main input).IsQueryBoundP (fun t => isSignCall t) qS)
    (hL : ∀ input, ∀ out ∈ support (F.main input), out.value.data.ms.length ≤ ℓ) :
    let ε := aggAdvantageROMH secp256k1F red256 red256 F -
      ((qH + qS + ℓ : ℕ) : ℝ≥0∞) * (1 / 2 ^ 127) -
      (q + 1 : ℝ≥0∞) * (2 / ((2 ^ 256 : ℕ) : ℝ≥0∞)) -
      (qS : ℝ≥0∞) * (qS + (qH + qS + ℓ + 1 : ℕ)) * (2 / ((Secp256k1.n - 1 : ℕ) : ℝ≥0∞))
    ε * (ε / ((qH + qS + ℓ + 1 : ℕ) + 1 : ℝ≥0∞) -
        FiatShamir.challengeSpaceInv (ZMod Secp256k1.n)) ≤
      Pr{let x ← (dlogExperiment secp256k1F (dlogOfKeyRecovery secp256k1F
        (FiatShamir.cmaReduction (sigma secp256k1F) (keyGen secp256k1F) M
          (simTranscript secp256k1F) (reductionROM secp256k1F red256 (F.viaRep rep256))
          (qH + qS + ℓ + 1))))}[x = true] :=
  halfagg_dlog_hashed secp256k1F red256 red256 Halfagg.Secp256k1.liftX_x_zero rep256
    red256_rep256 F q qH qS ℓ hq hH hS hL _ secp256k1_redBound _ secp256k1_repBound

/-- The tight reduction to discrete log for secp256k1, BIP458's randomizer hash
and BIP340's challenge hash: both are 256-bit values reduced modulo `n`. -/
theorem secp256k1_halfagg_dlog_tight_256 {M : Type} [DecidableEq M] [Inhabited M] [Finite M]
    [SampleableType (M × (Secp256k1.F × Secp256k1.F) → Fin (2 ^ 256))]
    [SampleableType (M × (Secp256k1.F × Secp256k1.F) → ZMod Secp256k1.n)]
    (F : RomForgerH Secp256k1.n (Fin (2 ^ 256)) (Fin (2 ^ 256)) Secp256k1.Point Secp256k1.F M)
    (q qH qS ℓ : ℕ)
    (hq : ∀ input, (F.main input).IsQueryBoundP (fun t => isRandCall t) q)
    (hH : ∀ input, (F.main input).IsQueryBoundP (fun t => isChalCall t) qH)
    (hS : ∀ input, (F.main input).IsQueryBoundP (fun t => isSignCall t) qS)
    (hL : ∀ input, ∀ out ∈ support (F.main input), out.value.data.ms.length ≤ ℓ)
    (hE : ∀ input, ExplainsNoncesH secp256k1F (F.main input) []) :
    aggAdvantageROMH secp256k1F red256 red256 F ≤
      Pr{let x ← dlogExperiment secp256k1F (dlogOfKeyRecovery secp256k1F
          (keySolver secp256k1F red256 (F.viaRep rep256)))}[x = true] +
        (qS : ℝ≥0∞) * (qS + (qH + qS + ℓ + 1 : ℕ)) * (2 / ((Secp256k1.n - 1 : ℕ) : ℝ≥0∞)) +
        (q + 1 : ℝ≥0∞) * (2 / ((2 ^ 256 : ℕ) : ℝ≥0∞)) + (qH + 1 : ℝ≥0∞) / Secp256k1.n +
        ((qH + qS + ℓ : ℕ) : ℝ≥0∞) * (1 / 2 ^ 127) :=
  halfagg_dlog_tight_hashed secp256k1F red256 red256 Halfagg.Secp256k1.liftX_x_zero rep256
    red256_rep256 F q qH qS ℓ hq hH hS hL hE _ secp256k1_redBound _ secp256k1_repBound

end Halfagg.Security
