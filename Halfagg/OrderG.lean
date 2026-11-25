import Halfagg.OrderCert
import Taproot.Secp256k1

/-!
# The generator of secp256k1 has order `n`, checked by the kernel

taproot-lean proves `n⋅G = 0` by running double-and-add in compiled code, which
adds Lean's compiler to what has to be trusted. This file proves it without
that.

`Halfagg.OrderG.cert` is the double-and-add chain for `(n - 1)⋅G` with the
slope and the result of every step written out. Checking a step then needs
only multiplications and additions modulo `p`, which the kernel evaluates
(`cert_ok`, by `decide +kernel`). `run_sound` shows that a chain that passes
the check computes what it says, with the group law of Mathlib's elliptic
curves. The chain ends in `-G`, so `n⋅G = (n - 1)⋅G + G = 0` (`n_smul_G`).

`Halfagg.secp256k1F` is secp256k1 as a `Taproot.Curve` with this proof. It has
the fields of taproot-lean's `secp256k1` and is what the theorems about
secp256k1 in this project are stated for.
-/

namespace Halfagg.OrderG

open Taproot Taproot.Secp256k1 WeierstrassCurve.Affine

/-- The x-coordinate of the generator. -/
def gx : ℕ := 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798

/-- The y-coordinate of the generator. -/
def gy : ℕ := 0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8

/-! ## Checking a chain with natural numbers -/

/-- Check one step from `(x, y)` to `(x', y')` with slope `l`. With `addG` the
step adds the generator, otherwise it doubles the point. All conditions are
congruences modulo `p` without subtraction. -/
def stepOk (addG : Bool) (x y l x' y' : ℕ) : Bool :=
  if addG then
    (x % p != gx % p) && ((l * x + gy) % p == (l * gx + y) % p) &&
      ((x' + x + gx) % p == l * l % p) && ((y' + y + l * x') % p == l * x % p)
  else
    (l * (2 * y) % p == 3 * x * x % p) && ((x' + 2 * x) % p == l * l % p) &&
      ((y' + y + l * x') % p == l * x % p)

/-- Follow a chain from the point `(x, y) = k⋅G`. The result is the final
scalar and point, if every step passes the check. -/
def run : List (Bool × ℕ × ℕ × ℕ) → ℕ → ℕ → ℕ → Option (ℕ × ℕ × ℕ)
  | [], k, x, y => some (k, x, y)
  | (addG, l, x', y') :: rest, k, x, y =>
    if stepOk addG x y l x' y' then run rest (if addG then k + 1 else 2 * k) x' y' else none

/-- **The certificate passes the check**, evaluated by the kernel: the chain
leads from `G` to `(n - 1)⋅G = (gx, p - gy)`. -/
theorem cert_ok : run cert 1 gx gy = some (n - 1, gx, p - gy) := by decide +kernel

/-! ## A chain that passes the check is correct -/

/-- `P` is the affine point with coordinates `x` and `y`. -/
def Is (P : Point) (x y : ℕ) : Prop :=
  ∃ h : W.toAffine.Nonsingular (x : F) (y : F), P = .some (x : F) (y : F) h

theorem is_of_eq {x y : F} (h : W.toAffine.Nonsingular x y) {a b : ℕ} (hx : x = a) (hy : y = b) :
    Is (.some x y h) a b := by
  subst hx hy
  exact ⟨h, rfl⟩

theorem cast_of_mod {a b : ℕ} (h : (a % p == b % p) = true) : (a : F) = b :=
  (ZMod.natCast_eq_natCast_iff' a b p).mpr (beq_iff_eq.mp h)

theorem two_ne_zero : (2 : F) ≠ 0 := by decide +kernel

/-- Adding two points with different x-coordinates. -/
theorem is_add {P Q : Point} {x₁ y₁ x₂ y₂ l x₃ y₃ : ℕ} (hP : Is P x₁ y₁) (hQ : Is Q x₂ y₂)
    (hx : (x₁ : F) ≠ x₂) (hl : (l : F) * x₁ + y₂ = l * x₂ + y₁)
    (hx₃ : (x₃ : F) + x₁ + x₂ = l * l) (hy₃ : (y₃ : F) + y₁ + l * x₃ = l * x₁) :
    Is (P + Q) x₃ y₃ := by
  obtain ⟨h₁, rfl⟩ := hP
  obtain ⟨h₂, rfl⟩ := hQ
  have hs : W.toAffine.slope (x₁ : F) x₂ y₁ y₂ = l := by
    rw [slope_of_X_ne hx, div_eq_iff (sub_ne_zero.mpr hx)]
    linear_combination -hl
  rw [Point.add_of_X_ne hx]
  refine is_of_eq _ ?_ ?_
  · rw [hs]
    simp only [addX, W]
    linear_combination -hx₃
  · rw [addY, hs]
    simp only [negY, negAddY, addX, W]
    linear_combination (l : F) * hx₃ - hy₃

/-- Doubling a point. -/
theorem is_double {P : Point} {x y l x₃ y₃ : ℕ} (hP : Is P x y)
    (hl : (l : F) * (2 * y) = 3 * x * x) (hx₃ : (x₃ : F) + 2 * x = l * l)
    (hy₃ : (y₃ : F) + y + l * x₃ = l * x) : Is (P + P) x₃ y₃ := by
  obtain ⟨h, rfl⟩ := hP
  have hy0 : (y : F) ≠ 0 := y_ne_zero ((nonsingular_iff _ _).mp h)
  have hny : (y : F) ≠ W.toAffine.negY x y := by
    simp only [negY, W]
    intro h2
    have h3 : (2 : F) * y = 0 := by linear_combination h2
    exact hy0 ((mul_eq_zero.mp h3).resolve_left two_ne_zero)
  have hs : W.toAffine.slope (x : F) x y y = l := by
    rw [slope_of_Y_ne rfl hny, div_eq_iff (sub_ne_zero.mpr hny)]
    simp only [negY, W]
    linear_combination -hl
  rw [Point.add_self_of_Y_ne hny]
  refine is_of_eq _ ?_ ?_
  · rw [hs]
    simp only [addX, W]
    linear_combination -hx₃
  · rw [addY, hs]
    simp only [negY, negAddY, addX, W]
    linear_combination (l : F) * hx₃ - hy₃

theorem is_G : Is G gx gy := by
  unfold G
  exact is_of_eq _ (by simp [Gx, gx]) (by simp [Gy, gy])

/-- **A chain that passes the check computes multiples of `G`.** -/
theorem run_sound : ∀ (steps : List (Bool × ℕ × ℕ × ℕ)) (k x y k' x' y' : ℕ),
    run steps k x y = some (k', x', y') → Is (k • G) x y → Is (k' • G) x' y'
  | [], k, x, y, k', x', y', h, hP => by
    simp only [run, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact hP
  | (addG, l, x₃, y₃) :: rest, k, x, y, k', x', y', h, hP => by
    cases addG with
    | true =>
      simp only [run, ↓reduceIte] at h
      split_ifs at h with hok
      refine run_sound rest _ _ _ _ _ _ h ?_
      simp only [stepOk, ↓reduceIte, Bool.and_eq_true, bne_iff_ne, ne_eq] at hok
      obtain ⟨⟨⟨hx, hl⟩, hx₃⟩, hy₃⟩ := hok
      have hx' : (x : F) ≠ gx := fun e => hx ((ZMod.natCast_eq_natCast_iff' x gx p).mp e)
      have hsum := is_add hP is_G hx' (by exact_mod_cast cast_of_mod hl)
        (by exact_mod_cast cast_of_mod hx₃) (by exact_mod_cast cast_of_mod hy₃)
      rw [succ_nsmul]
      exact hsum
    | false =>
      simp only [run, Bool.false_eq_true, ↓reduceIte] at h
      split_ifs at h with hok
      refine run_sound rest _ _ _ _ _ _ h ?_
      simp only [stepOk, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true] at hok
      obtain ⟨⟨hl, hx₃⟩, hy₃⟩ := hok
      have hsum := is_double hP (by exact_mod_cast cast_of_mod hl)
        (by exact_mod_cast cast_of_mod hx₃) (by exact_mod_cast cast_of_mod hy₃)
      rw [two_mul, add_nsmul]
      exact hsum

/-! ## The order of the generator -/

/-- `(n - 1)⋅G = -G`. -/
theorem n_sub_one_smul_G : Is ((n - 1) • G) gx (p - gy) :=
  run_sound cert 1 gx gy _ _ _ cert_ok (by simpa only [one_nsmul] using is_G)

/-- **`n⋅G = 0`**, with no compiled code. -/
theorem n_smul_G : n • G = 0 := by
  obtain ⟨h, hP⟩ := n_sub_one_smul_G
  have hn : n • G = (n - 1) • G + G := by
    rw [← succ_nsmul]
    rfl
  have hy : ((p - gy : ℕ) : F) = W.toAffine.negY Gx Gy := by
    rw [Nat.cast_sub (by decide), ZMod.natCast_self]
    simp [negY, W, Gy, gy]
  rw [hn, hP]
  unfold G
  exact Point.add_of_Y_eq (by simp [Gx, gx]) hy

end Halfagg.OrderG

namespace Halfagg

open Taproot Taproot.Secp256k1

/-- **secp256k1** as the curve interface, with x-coordinates in the base
field. It has the fields of taproot-lean's `secp256k1`, and the order of the
generator is checked by the kernel. -/
def secp256k1F : Curve n Point F where
  G := G
  G_ne_zero := WeierstrassCurve.Affine.Point.some_ne_zero _
  order_G := OrderG.n_smul_G
  x := xCoord
  hasEvenY := hasEvenY
  liftX := liftX
  x_neg := x_neg
  hasEvenY_neg := hasEvenY_neg
  liftX_x := liftX_x
  liftX_spec := liftX_spec

end Halfagg
