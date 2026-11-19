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

end Halfagg.Security
