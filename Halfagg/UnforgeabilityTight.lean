import Halfagg.Proofs.Explained

/-!
# A tight reduction to discrete log

The theorems, over the definitions of `Halfagg/SecurityTight.lean`.
-/

open OracleSpec OracleComp AlgebraicGroupModel.Interaction
open scoped ENNReal

namespace Halfagg.Security

open Taproot Taproot.Curve Taproot.BIP340 Taproot.BIP340Security

attribute [local instance] smulVal

variable {n : ℕ} [Fact n.Prime] {H E X M : Type} [AddCommGroup E] [DecidableEq E]
  [DecidableEq X] [DecidableEq M] (C : Curve n E X)
variable [SampleableType H] (red : H → ZMod n)

/-- **A forger yields the secret key or a signature made without it**, with no
forking. In the algebraic group model with both hashes as random oracles, for a
forger with at most `q` randomizer requests, `qH` challenge queries, `qS` signing
requests and forgeries of at most `ℓ` items, and `Q = qH + qS + ℓ + 1`:

`Pr[forger wins] ≤ Pr[keySolver solves discrete log] + qS⋅(qS + Q)⋅2/(n - 1) +
(q + 1)⋅μ + Pr[romMachine F repFin forges BIP340]`,

with `μ` as in `halfagg_unforgeable`.

The second term is the loss of VCVio's signing simulation and the third is the
bad event of `halfagg_unforgeable`. The last term is the success of the machine
that reads a signature `(r, α*)` off the forger's explanations while its
candidate key is wrong. This theorem does not bound it, and
`halfagg_dlog_tight` does for forgers that explain the nonces they hash. -/
theorem halfagg_key_or_signature [Inhabited M] [Finite M] [Finite X]
    [SampleableType (M × (X × X) → ZMod n)] (hx0 : C.liftX (C.x 0) = none)
    (F : RomForger n H E X M) (q qH qS ℓ : ℕ)
    (hq : ∀ input, (F.main input).IsQueryBoundP (fun t => isRandCall t) q)
    (hH : ∀ input, (F.main input).IsQueryBoundP (fun t => isChalCall t) qH)
    (hS : ∀ input, (F.main input).IsQueryBoundP (fun t => isSignCall t) qS)
    (hL : ∀ input, ∀ out ∈ support (F.main input), out.value.data.ms.length ≤ ℓ)
    (μ : ℝ≥0∞) (hμ : RedBound red μ) :
    aggAdvantageROM C red F ≤
      Pr{let x ← dlogExperiment C (dlogOfKeyRecovery C (keySolver C red F))}[x = true] +
        (qS : ℝ≥0∞) * (qS + (qH + qS + ℓ + 1 : ℕ)) * (2 / ((n - 1 : ℕ) : ℝ≥0∞)) +
        (q + 1 : ℝ≥0∞) * μ +
        SignatureAlg.unforgeableAdvantage (FiatShamir.runtime (Commit := X × X) (Chal := ZMod n) M)
          (romMachine C red F (repFin C)) := by
  have h1 := tight_split C hμ hx0 F q (at_queries F q hq)
  have h2 := keyMachine_to_nma C (red := red) F qH qS ℓ hH hS hL
  have h3 := key_fork_le C (red := red) hx0 F (qH + qS + ℓ + 1)
  rw [hardRelationExperiment_eq_dlog] at h3
  calc aggAdvantageROM C red F
      ≤ SignatureAlg.unforgeableAdvantage (FiatShamir.runtime M) (romMachine C red F (keyFin C)) +
          SignatureAlg.unforgeableAdvantage (FiatShamir.runtime M) (romMachine C red F (repFin C)) +
          (q + 1 : ℝ≥0∞) * μ := h1
    _ ≤ (Pr{let x ← dlogExperiment C (dlogOfKeyRecovery C (keySolver C red F))}[x = true] +
          (qS : ℝ≥0∞) * (qS + (qH + qS + ℓ + 1 : ℕ)) * (2 / ((n - 1 : ℕ) : ℝ≥0∞))) +
          SignatureAlg.unforgeableAdvantage (FiatShamir.runtime M) (romMachine C red F (repFin C)) +
          (q + 1 : ℝ≥0∞) * μ :=
        add_le_add (add_le_add (h2.trans (add_le_add h3 le_rfl)) le_rfl) le_rfl
    _ = _ := by ring

/-- **A tight reduction to discrete log.** For a forger that explains the nonce
of every challenge-hash query (`ExplainsNonces`), with at most `q` randomizer
requests, `qH` challenge queries, `qS` signing requests and forgeries of at
most `ℓ` items, and `Q = qH + qS + ℓ + 1`:

`Pr[forger wins] ≤ Pr[keySolver solves discrete log] + qS⋅(qS + Q)⋅2/(n - 1) +
(q + 1)⋅μ + (qH + 1)/n`,

with `μ` as in `halfagg_unforgeable`.

Every loss is additive. The last term bounds the last term of
`halfagg_key_or_signature`: a challenge drawn after the forger explained the
nonce is `-β` with probability `1/n`. -/
theorem halfagg_dlog_tight [Inhabited M] [Finite M] [Finite X]
    [SampleableType (M × (X × X) → ZMod n)] (hx0 : C.liftX (C.x 0) = none)
    (F : RomForger n H E X M) (q qH qS ℓ : ℕ)
    (hq : ∀ input, (F.main input).IsQueryBoundP (fun t => isRandCall t) q)
    (hH : ∀ input, (F.main input).IsQueryBoundP (fun t => isChalCall t) qH)
    (hS : ∀ input, (F.main input).IsQueryBoundP (fun t => isSignCall t) qS)
    (hL : ∀ input, ∀ out ∈ support (F.main input), out.value.data.ms.length ≤ ℓ)
    (hE : ∀ input, ExplainsNonces C (F.main input) [])
    (μ : ℝ≥0∞) (hμ : RedBound red μ) :
    aggAdvantageROM C red F ≤
      Pr{let x ← dlogExperiment C (dlogOfKeyRecovery C (keySolver C red F))}[x = true] +
        (qS : ℝ≥0∞) * (qS + (qH + qS + ℓ + 1 : ℕ)) * (2 / ((n - 1 : ℕ) : ℝ≥0∞)) +
        (q + 1 : ℝ≥0∞) * μ + (qH + 1 : ℝ≥0∞) / n := by
  have h1 := tight_split_event C hμ hx0 F q (at_queries F q hq)
  have h2 := (keyEvent_le C (red := red) F).trans (keyMachine_to_nma C F qH qS ℓ hH hS hL)
  have h3 := key_fork_le C (red := red) hx0 F (qH + qS + ℓ + 1)
  rw [hardRelationExperiment_eq_dlog] at h3
  have h4 := (repB_le_lazy C (red := red) hx0 F).trans (hit_lazy C F qH hH hE)
  refine (h1.trans (add_le_add (add_le_add (h2.trans (add_le_add h3 le_rfl)) h4)
    le_rfl)).trans (le_of_eq ?_)
  ring

/-- The tight reduction to discrete log for secp256k1 and BIP458's randomizer
hash. -/
theorem secp256k1_halfagg_dlog_tight {M : Type} [DecidableEq M] [Inhabited M] [Finite M]
    [SampleableType (M × (Secp256k1.F × Secp256k1.F) → ZMod Secp256k1.n)]
    (F : RomForger Secp256k1.n (Fin (2 ^ 256)) Secp256k1.Point Secp256k1.F M) (q qH qS ℓ : ℕ)
    (hq : ∀ input, (F.main input).IsQueryBoundP (fun t => isRandCall t) q)
    (hH : ∀ input, (F.main input).IsQueryBoundP (fun t => isChalCall t) qH)
    (hS : ∀ input, (F.main input).IsQueryBoundP (fun t => isSignCall t) qS)
    (hL : ∀ input, ∀ out ∈ support (F.main input), out.value.data.ms.length ≤ ℓ)
    (hE : ∀ input, ExplainsNonces secp256k1F (F.main input) []) :
    aggAdvantageROM secp256k1F red256 F ≤
      Pr{let x ← dlogExperiment secp256k1F (dlogOfKeyRecovery secp256k1F
          (keySolver secp256k1F red256 F))}[x = true] +
        (qS : ℝ≥0∞) * (qS + (qH + qS + ℓ + 1 : ℕ)) * (2 / ((Secp256k1.n - 1 : ℕ) : ℝ≥0∞)) +
        (q + 1 : ℝ≥0∞) * (2 / ((2 ^ 256 : ℕ) : ℝ≥0∞)) + (qH + 1 : ℝ≥0∞) / Secp256k1.n :=
  halfagg_dlog_tight secp256k1F red256 Halfagg.Secp256k1.liftX_x_zero F q qH qS ℓ
    hq hH hS hL hE _ secp256k1_redBound

end Halfagg.Security
