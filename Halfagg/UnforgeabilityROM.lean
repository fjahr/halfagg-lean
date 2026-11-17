import Halfagg.Proofs.ROM

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

variable {n : ℕ} [Fact n.Prime] {E X M : Type} [AddCommGroup E] [DecidableEq E]
  [DecidableEq X] [DecidableEq M] (C : Curve n E X)

/-- **Half-aggregation is as secure as BIP340, with the challenge hash as a
random oracle.** An algebraic forger with oracle access to the challenge hash,
at most `q` randomizer requests and forgeries of at most `ℓ` items wins with
probability at most the success probability of `reductionROM F` in the BIP340
game of `Taproot.BIP340Security.euf_cma`, plus `(q + ℓ)/n`. -/
theorem halfagg_unforgeable_rom [Inhabited M] [Finite M] [Finite X]
    [SampleableType (M × (X × X) → ZMod n)] (hx0 : C.liftX (C.x 0) = none)
    (F : RomForger n E X M) (q ℓ : ℕ)
    (hq : ∀ g input, ((F.at g).main input).IsQueryBoundP (fun r => isRand r.value.data) q)
    (hℓ : ∀ g input, ∀ out ∈ support ((F.at g).main input), out.value.data.ms.length ≤ ℓ) :
    aggAdvantageROM C F ≤
      SignatureAlg.unforgeableAdvantage (FiatShamir.runtime M) (reductionROM C F) +
        (q + ℓ : ℝ≥0∞) / n := by
  have hfs : SignatureAlg.unforgeableAdvantage (FiatShamir.runtime M) (reductionROM C F) =
      Pr{let b ← (($ᵗ (M × (X × X) → ZMod n)) >>= fun g =>
        gameOK C (hOf g) <$> jExp C (hOf g) (F.at g))}[b = true] := by
    rw [fs_advantage_eq_table]
    simp only [rom_experiment_eq]
  rw [hfs]
  unfold aggAdvantageROM aggExperimentROM
  refine prEvent_bind_le_add_const _ _ _ _ _ _ fun g => ?_
  have h := halfagg_unforgeable C (hOf g) hx0 (F.at g) q ℓ (hq g) (hℓ g)
  unfold aggAdvantage SignatureAlg.unforgeableAdvantage at h
  rw [ProbCompRuntime.rom_evalDist, ← prEvent_eq_evalDist_singleton,
    ProbCompRuntime.probComp_evalDist, ← prEvent_eq_evalDist_singleton, red_experiment_eq] at h
  exact h

end Halfagg.Security
