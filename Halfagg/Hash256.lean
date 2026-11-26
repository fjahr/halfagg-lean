import Halfagg.Security
import Taproot.Secp256k1

/-!
# The randomizer hash as a bit string reduced modulo `n`

The security theorems take the type `H` of the randomizer hash's outputs and the
map `red : H → ZMod n` that turns an output into a scalar, and lose `μ` per
randomizer, where `RedBound red μ` says that `red` of a uniform output is any
given scalar with probability at most `μ`.

BIP458 computes `int(hash) mod n` from a 256-bit hash. `redMod n N` is that map
for outputs below `N`, and `redMod_bound` gives `μ = 2/N` if `N ≤ 2⋅n`: at most
two outputs reduce to the same scalar. For secp256k1, `N = 2^256` and
`n ≤ 2^256 ≤ 2⋅n` (`secp256k1_redBound`).

`id_bound` is the uniform model, where the oracle answers in `ZMod n` and
`μ = 1/n`.
-/

open OracleSpec OracleComp
open scoped ENNReal

namespace Halfagg.Security

/-- `int(h) mod n` for a hash output `h < N`. -/
def redMod (n N : ℕ) : Fin N → ZMod n := fun h => (h.val : ZMod n)

/-- **At most two hash outputs reduce to a given scalar** if `N ≤ 2⋅n`, so a
uniform output reduces to it with probability at most `2/N`. -/
theorem redMod_bound (n N : ℕ) [Fact n.Prime] [NeZero N] (hN : N ≤ 2 * n) :
    RedBound (redMod n N) (2 / (N : ℝ≥0∞)) := by
  intro c
  have hn : 0 < n := (Fact.out : n.Prime).pos
  have hsub : (Finset.univ.filter fun h : Fin N => redMod n N h = c).image Fin.val ⊆
      ({c.val, c.val + n} : Finset ℕ) := by
    intro x hx
    obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hx
    have hc : redMod n N h = c := (Finset.mem_filter.mp hh).2
    have hmod : h.val % n = c.val := by
      rw [← hc, redMod, ZMod.val_natCast]
    have hdiv : h.val / n < 2 := Nat.div_lt_of_lt_mul (by have := h.isLt; omega)
    have hdm := Nat.div_add_mod h.val n
    rw [Finset.mem_insert, Finset.mem_singleton]
    interval_cases hq : h.val / n
    · left; omega
    · right; omega
  have hcard : (Finset.univ.filter fun h : Fin N => redMod n N h = c).card ≤ 2 := by
    rw [← Finset.card_image_of_injective _ Fin.val_injective]
    exact (Finset.card_le_card hsub).trans Finset.card_le_two
  rw [SampleableType.prEvent_uniformSample, Fintype.card_fin]
  exact ENNReal.div_le_div_right (by exact_mod_cast hcard) _

/-- The uniform model: the oracle answers in `ZMod n` and nothing is reduced. -/
theorem id_bound (n : ℕ) [Fact n.Prime] :
    RedBound (id : ZMod n → ZMod n) (n : ℝ≥0∞)⁻¹ := by
  intro c
  simp only [id]
  rw [SampleableType.prEvent_uniformSample_eq_singleton, ZMod.card]

/-- BIP458's reduction for secp256k1: a 256-bit hash output as a scalar. -/
abbrev red256 : Fin (2 ^ 256) → ZMod Taproot.Secp256k1.n := redMod Taproot.Secp256k1.n (2 ^ 256)

/-- For secp256k1, a uniform 256-bit hash output reduces to a given scalar with
probability at most `2/2^256`. -/
theorem secp256k1_redBound : RedBound red256 (2 / ((2 ^ 256 : ℕ) : ℝ≥0∞)) :=
  redMod_bound Taproot.Secp256k1.n (2 ^ 256) (by norm_num [Taproot.Secp256k1.n])

/-! ## One hash output for every scalar

The challenge hash is reduced in the same way. The theorems of
`Halfagg/UnforgeabilityHashed.lean` choose one hash output `rep c` for every
scalar `c` and lose `δ` for every hash output that the game reads, where
`RepBound red rep δ` says that a uniform output is not the chosen output of its
scalar with probability at most `δ`. -/

/-- A uniform hash output `h` is not `rep (red h)`, the chosen output for its
scalar, with probability at most `δ`. -/
def RepBound {n : ℕ} {Hc : Type} [SampleableType Hc] (red : Hc → ZMod n) (rep : ZMod n → Hc)
    (δ : ℝ≥0∞) : Prop :=
  Pr{let h ← $ᵗ Hc}[rep (red h) ≠ h] ≤ δ

/-- The hash output below `n` that reduces to the scalar `c`. -/
def repMod (n N : ℕ) [Fact n.Prime] (hN : n ≤ N) : ZMod n → Fin N :=
  fun c => ⟨c.val, (ZMod.val_lt c).trans_le hN⟩

theorem redMod_repMod (n N : ℕ) [Fact n.Prime] (hN : n ≤ N) (c : ZMod n) :
    redMod n N (repMod n N hN c) = c := by
  simp [redMod, repMod]

/-- **The hash outputs that `repMod` does not return are the `N - n` outputs
that are not below `n`.** -/
theorem repMod_bound (n N : ℕ) [Fact n.Prime] [NeZero N] (hN : n ≤ N) :
    RepBound (redMod n N) (repMod n N hN) (((N - n : ℕ) : ℝ≥0∞) / N) := by
  have hsub : (Finset.univ.filter fun h : Fin N =>
      repMod n N hN (redMod n N h) ≠ h).image Fin.val ⊆ Finset.Ico n N := by
    intro x hx
    obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hx
    have hne : repMod n N hN (redMod n N h) ≠ h := (Finset.mem_filter.mp hh).2
    rw [Finset.mem_Ico]
    refine ⟨?_, h.isLt⟩
    by_contra hlt
    exact hne (Fin.ext (by simp [repMod, redMod, ZMod.val_natCast,
      Nat.mod_eq_of_lt (not_le.mp hlt)]))
  have hcard : (Finset.univ.filter fun h : Fin N =>
      repMod n N hN (redMod n N h) ≠ h).card ≤ N - n := by
    rw [← Finset.card_image_of_injective _ Fin.val_injective]
    exact (Finset.card_le_card hsub).trans (by simp)
  unfold RepBound
  rw [SampleableType.prEvent_uniformSample, Fintype.card_fin]
  exact ENNReal.div_le_div_right (by exact_mod_cast hcard) _

/-- The 256-bit hash output below `n` that reduces to a scalar of secp256k1. -/
abbrev rep256 : ZMod Taproot.Secp256k1.n → Fin (2 ^ 256) :=
  repMod Taproot.Secp256k1.n (2 ^ 256) (by norm_num [Taproot.Secp256k1.n])

theorem red256_rep256 (c : ZMod Taproot.Secp256k1.n) : red256 (rep256 c) = c :=
  redMod_repMod _ _ _ c

/-- For secp256k1, a uniform 256-bit hash output is not below `n` with
probability at most `2^-127`. -/
theorem secp256k1_repBound : RepBound red256 rep256 (1 / 2 ^ 127) := by
  refine (repMod_bound Taproot.Secp256k1.n (2 ^ 256) _).trans ?_
  refine ENNReal.div_le_of_le_mul ?_
  have h2 : ((2 ^ 256 : ℕ) : ℝ≥0∞) = 2 ^ 127 * ((2 ^ 129 : ℕ) : ℝ≥0∞) := by
    norm_cast
  rw [h2, ← mul_assoc, one_div, ENNReal.inv_mul_cancel (by positivity) (by simp), one_mul]
  exact_mod_cast (by norm_num [Taproot.Secp256k1.n] :
    2 ^ 256 - Taproot.Secp256k1.n ≤ 2 ^ 129)

end Halfagg.Security
