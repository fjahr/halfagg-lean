import Halfagg.Basic
import Halfagg.OrderG

/-!
# secp256k1 has prime order

`secp256k1_primeOrder`: every point `P` of secp256k1 has `n⋅P = 0`, that is,
the group of points has exactly `n` elements.

The proof needs no point counting algorithm. A point other than the point at
infinity is determined by its x-coordinate and the parity of its
y-coordinate, so there are at most `2⋅p + 1` points. The generator has order
`n`, so `n` divides the number of points, and `3⋅n > 2⋅p + 1` leaves `n` and
`2⋅n`. A group of even order has an element of order two, which would be a
point with `P = -P`; there is none, because negating a point flips the parity
of its y-coordinate.

`secp256k1_verifyMulti_eq` is `verifyMulti_eq` for secp256k1, which needs this.
-/

namespace Halfagg

open Taproot Taproot.Secp256k1

/-- A point as its x-coordinate and the parity of its y-coordinate. -/
def pointCode (P : Point) : Option (F × Bool) :=
  if P = 0 then none else some (xCoord P, hasEvenY P)

theorem pointCode_injective : Function.Injective pointCode := by
  intro P Q h
  unfold pointCode at h
  by_cases hP : P = 0 <;> by_cases hQ : Q = 0 <;> simp only [hP, hQ, ↓reduceIte] at h
  · rw [hP, hQ]
  · exact absurd h (by simp)
  · exact absurd h (by simp)
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    exact secp256k1F.eq_of_x_eq hP hQ h.1 h.2

instance : Finite Point := Finite.of_injective pointCode pointCode_injective

/-- The number of codes, for a general modulus (so that the proof does not
unfold the 256-bit prime). -/
theorem card_code (q : ℕ) [NeZero q] : Nat.card (Option (ZMod q × Bool)) = 2 * q + 1 := by
  rw [Finite.card_option, Nat.card_prod, Nat.card_zmod, Nat.card_eq_fintype_card,
    Fintype.card_bool]
  omega

/-- There are at most `2⋅p + 1` points. -/
theorem card_point_le : Nat.card Point ≤ 2 * p + 1 :=
  (Nat.card_le_card_of_injective _ pointCode_injective).trans (card_code p).le

/-- No point has order two. -/
theorem two_nsmul_ne_zero {P : Point} (hP : P ≠ 0) : 2 • P ≠ 0 := by
  intro h
  have hneg : P = -P := by
    rw [two_nsmul] at h
    exact eq_neg_of_add_eq_zero_left h
  have := hasEvenY_neg P hP
  rw [← hneg] at this
  cases hE : hasEvenY P <;> simp [hE] at this

theorem three_n_gt : 2 * p + 1 < n * 3 := by decide +kernel

/-- **secp256k1 has exactly `n` points.** -/
theorem card_point : Nat.card Point = n := by
  have hdvd : n ∣ Nat.card Point := by
    rw [← secp256k1F.addOrderOf_G]
    exact addOrderOf_dvd_natCard _
  obtain ⟨k, hk⟩ := hdvd
  have hle := card_point_le
  have hpos : 0 < Nat.card Point := Nat.card_pos
  have h3 := three_n_gt
  have hno2 : ¬2 ∣ Nat.card Point := by
    intro h2
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨P, hP⟩ := exists_prime_addOrderOf_dvd_card' 2 h2
    have hP0 : P ≠ 0 := by
      rintro rfl
      simp at hP
    exact two_nsmul_ne_zero hP0 (by rw [← hP]; exact addOrderOf_nsmul_eq_zero P)
  -- keep the large numerals out of `omega`
  generalize n = N at hk h3 ⊢
  generalize p = Pp at hle h3
  generalize Nat.card Point = c at hk hle hpos hno2 ⊢
  have hk3 : k < 3 := by
    by_contra hge
    push Not at hge
    have : N * 3 ≤ N * k := Nat.mul_le_mul_left N hge
    omega
  have hk0 : k ≠ 0 := by
    rintro rfl
    omega
  have hk2 : k = 1 ∨ k = 2 := by omega
  rcases hk2 with rfl | rfl
  · omega
  · exfalso
    have h2 : 2 ∣ c := ⟨N, by omega⟩
    exact hno2 h2

/-- **secp256k1 has prime order `n`**: every point `P` has `n⋅P = 0`. -/
theorem secp256k1_primeOrder : Curve.PrimeOrder n Point := fun P => by
  rw [← card_point]
  exact card_nsmul_eq_zero'

/-- **On secp256k1 the multi-scalar form is `VerifyAggregate`**, for every
challenge hash and every randomizer hash. -/
theorem secp256k1_verifyMulti_eq {M : Type} (challenge : F → F → M → ZMod n)
    (rand : List (Item F M) → ZMod n) (agg : AggSig n F) (pm : List (F × M)) :
    verifyMulti secp256k1F challenge rand agg pm =
      verifyAggregate secp256k1F challenge rand agg pm :=
  verifyMulti_eq secp256k1F challenge rand secp256k1_primeOrder agg pm

end Halfagg
