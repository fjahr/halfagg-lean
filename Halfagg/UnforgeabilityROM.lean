import Halfagg.Proofs.ROMBounds

/-!
# Half-aggregation is as secure as BIP340, with the challenge hash as a random oracle

`halfagg_unforgeable_rom` is `halfagg_unforgeable` for a forger and a reduction
that reach the challenge hash only through an oracle. Its BIP340 game is the
game of `Taproot.BIP340Security.euf_cma`, so the two theorems chain:
`halfagg_dlog` bounds a forger's success by the success of a discrete-log
solver.
-/

open OracleSpec OracleComp AlgebraicGroupModel.Interaction
open scoped ENNReal

namespace Halfagg.Security

open Taproot Taproot.Curve Taproot.BIP340 Taproot.BIP340Security Halfagg.LoggedRun

attribute [local instance] smulVal

variable {n : ℕ} [Fact n.Prime] {H E X M : Type} [AddCommGroup E] [DecidableEq E]
  [DecidableEq X] [DecidableEq M] (C : Curve n E X)
variable [SampleableType H] (red : H → ZMod n)

/-- **Half-aggregation is as secure as BIP340, with the challenge hash as a
random oracle.** An algebraic forger with oracle access to the challenge hash,
at most `q` randomizer requests, wins with probability at most the success
probability of `reductionROM F` in the BIP340 game of
`Taproot.BIP340Security.euf_cma`, plus `(q + 1)⋅μ`, with `μ` as in
`halfagg_unforgeable`. -/
theorem halfagg_unforgeable_rom [Inhabited M] [Finite M] [Finite X]
    [SampleableType (M × (X × X) → ZMod n)] (hx0 : C.liftX (C.x 0) = none)
    (F : RomForger n H E X M) (q : ℕ)
    (hq : ∀ g input, ((F.at g).main input).IsQueryBoundP (fun r => isRand r.value.data) q)
    (μ : ℝ≥0∞) (hμ : RedBound red μ) :
    aggAdvantageROM C red F ≤
      SignatureAlg.unforgeableAdvantage (FiatShamir.runtime M) (reductionROM C red F) +
        (q + 1 : ℝ≥0∞) * μ := by
  have hfs : SignatureAlg.unforgeableAdvantage (FiatShamir.runtime M) (reductionROM C red F) =
      Pr{let b ← (($ᵗ (M × (X × X) → ZMod n)) >>= fun g =>
        gameOK C (hOf g) <$> jExp C (hOf g) red (F.at g))}[b = true] := by
    rw [fs_advantage_eq_table]
    simp only [rom_experiment_eq]
  rw [hfs]
  unfold aggAdvantageROM aggExperimentROM
  refine prEvent_bind_le_add_const _ _ _ _ _ _ fun g => ?_
  have h := halfagg_unforgeable C (hOf g) red hx0 (F.at g) q (hq g) μ hμ
  unfold aggAdvantage SignatureAlg.unforgeableAdvantage at h
  rw [ProbCompRuntime.rom_evalDist, ← prEvent_eq_evalDist_singleton,
    ProbCompRuntime.probComp_evalDist, ← prEvent_eq_evalDist_singleton, red_experiment_eq] at h
  exact h

/-- **Half-aggregation is unforgeable under the discrete-log assumption**, in
the algebraic group model with both hashes as random oracles:
`halfagg_unforgeable_rom` chained with `Taproot.BIP340Security.euf_cma_dlog`.

For an algebraic forger with at most `q` randomizer requests, `qH` challenge
queries, `qS` signing requests and forgeries of at most `ℓ` items, let
`Q = qH + qS + ℓ + 1` and

`ε = Pr[forger wins] - (q + 1)⋅μ - qS⋅(qS + Q)⋅2/(n - 1)`.

Then a discrete-log solver built from the forger succeeds with probability at
least `ε⋅(ε/(Q + 1) - 1/n)`. The first loss is this project's tight step, the
rest is the forking-lemma loss of BIP340 itself. -/
theorem halfagg_dlog [Inhabited M] [Finite M] [Finite X]
    [SampleableType (M × (X × X) → ZMod n)] (hx0 : C.liftX (C.x 0) = none)
    (F : RomForger n H E X M) (q qH qS ℓ : ℕ)
    (hq : ∀ input, (F.main input).IsQueryBoundP (fun t => isRandCall t) q)
    (hH : ∀ input, (F.main input).IsQueryBoundP (fun t => isChalCall t) qH)
    (hS : ∀ input, (F.main input).IsQueryBoundP (fun t => isSignCall t) qS)
    (hL : ∀ input, ∀ out ∈ support (F.main input), out.value.data.ms.length ≤ ℓ)
    (μ : ℝ≥0∞) (hμ : RedBound red μ) :
    let ε := aggAdvantageROM C red F - (q + 1 : ℝ≥0∞) * μ -
      (qS : ℝ≥0∞) * (qS + (qH + qS + ℓ + 1 : ℕ)) * (2 / ((n - 1 : ℕ) : ℝ≥0∞))
    ε * (ε / ((qH + qS + ℓ + 1 : ℕ) + 1 : ℝ≥0∞) - FiatShamir.challengeSpaceInv (ZMod n)) ≤
      Pr{let x ← (dlogExperiment C (dlogOfKeyRecovery C
        (FiatShamir.cmaReduction (sigma C) (keyGen C) M (simTranscript C) (reductionROM C red F)
          (qH + qS + ℓ + 1))))}[x = true] := by
  intro ε
  have hrom := halfagg_unforgeable_rom C red hx0 F q (at_queries F q hq) μ hμ
  have hd := euf_cma_dlog C M (reductionROM C red F) qS (qH + qS + ℓ + 1)
    (reductionROM_bound C F qH qS ℓ hH hS hL)
  refine le_trans ?_ hd
  have hε : ε ≤ SignatureAlg.unforgeableAdvantage
      (FiatShamir.runtime (Commit := X × X) (Chal := ZMod n) M) (reductionROM C red F) -
      (qS : ℝ≥0∞) * (qS + (qH + qS + ℓ + 1 : ℕ)) * (2 / ((n - 1 : ℕ) : ℝ≥0∞)) :=
    tsub_le_tsub_right (tsub_le_iff_right.mpr hrom) _
  exact mul_le_mul' hε (tsub_le_tsub_right (ENNReal.div_le_div_right hε _) _)

/-- The discrete-log theorem for secp256k1 and BIP458's randomizer hash. -/
theorem secp256k1_halfagg_dlog {M : Type} [DecidableEq M] [Inhabited M] [Finite M]
    [SampleableType (M × (Secp256k1.F × Secp256k1.F) → ZMod Secp256k1.n)]
    (F : RomForger Secp256k1.n (Fin (2 ^ 256)) Secp256k1.Point Secp256k1.F M) (q qH qS ℓ : ℕ)
    (hq : ∀ input, (F.main input).IsQueryBoundP (fun t => isRandCall t) q)
    (hH : ∀ input, (F.main input).IsQueryBoundP (fun t => isChalCall t) qH)
    (hS : ∀ input, (F.main input).IsQueryBoundP (fun t => isSignCall t) qS)
    (hL : ∀ input, ∀ out ∈ support (F.main input), out.value.data.ms.length ≤ ℓ) :
    let ε := aggAdvantageROM secp256k1F red256 F -
      (q + 1 : ℝ≥0∞) * (2 / ((2 ^ 256 : ℕ) : ℝ≥0∞)) -
      (qS : ℝ≥0∞) * (qS + (qH + qS + ℓ + 1 : ℕ)) * (2 / ((Secp256k1.n - 1 : ℕ) : ℝ≥0∞))
    ε * (ε / ((qH + qS + ℓ + 1 : ℕ) + 1 : ℝ≥0∞) -
        FiatShamir.challengeSpaceInv (ZMod Secp256k1.n)) ≤
      Pr{let x ← (dlogExperiment secp256k1F (dlogOfKeyRecovery secp256k1F
        (FiatShamir.cmaReduction (sigma secp256k1F) (keyGen secp256k1F) M
          (simTranscript secp256k1F) (reductionROM secp256k1F red256 F)
          (qH + qS + ℓ + 1))))}[x = true] :=
  halfagg_dlog secp256k1F red256 Halfagg.Secp256k1.liftX_x_zero F q qH qS ℓ hq hH hS hL
    _ secp256k1_redBound

end Halfagg.Security
