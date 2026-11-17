import Taproot.Secp256k1

/-!
# The point at infinity has no x-only encoding on secp256k1

`Curve.x` gives the point at infinity the x-coordinate `0`. No point of
secp256k1 has `x = 0`: that would need `y² = 7`, but `7` is not a square
modulo `p` since `7^((p-1)/2) ≠ 1`. So `lift_x(0)` fails.
-/

namespace Halfagg.Secp256k1

open Taproot Taproot.Secp256k1

theorem liftX_zero : liftX (0 : F) = none := by
  by_contra h
  obtain ⟨P, hP⟩ := Option.ne_none_iff_exists'.mp h
  obtain ⟨h0, -, hx⟩ := liftX_spec 0 P hP
  cases P with
  | zero => exact h0 rfl
  | some x y hns =>
    have hx' : x = 0 := hx
    subst hx'
    have hy := (nonsingular_iff 0 y).mp hns
    have hy0 := y_ne_zero hy
    have h7 : (7 : F) = y ^ 2 := by rw [hy]; ring
    have hone : (7 : F) ^ ((p - 1) / 2) = 1 := by
      rw [h7, ← pow_mul, show 2 * ((p - 1) / 2) = p - 1 by decide +kernel]
      exact ZMod.pow_card_sub_one_eq_one hy0
    have hcast : (7 : F) = ((7 : ℕ) : F) := by norm_cast
    rw [hcast, Pratt.natCast_pow_eq_powMod _ _ _ (by decide +kernel)] at hone
    revert hone
    decide +kernel

/-- The curve hypothesis of `halfagg_unforgeable` holds for secp256k1. -/
theorem liftX_x_zero : secp256k1.liftX (secp256k1.x 0) = none := by
  have h : secp256k1.liftX = liftX := by simp only [secp256k1]
  rw [h]
  exact liftX_zero

end Halfagg.Secp256k1
