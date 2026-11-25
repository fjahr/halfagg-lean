import Halfagg.Basic

/-!
# Forgeries against weakened verifiers

BIP458 multiplies the term of item `i` by a randomizer `zᵢ` that hashes the
items `0, …, i`. Two weaker choices are forgeable, and the forgeries here are
explicit: they are computed from the target public key and need no signature.

* `forgeOnes_verifies`: with every randomizer `1`, the aggregate `forgeOnes`
  verifies. This is the verifier of the first proposal of half-aggregation,
  which BIP458's rationale calls flawed.
* `forgeLate_verifies`: with a randomizer `zᵢ` that hashes only the items
  before item `i`, the aggregate `forgeLate` verifies.

Both contain an item `(pk, m)` for a public key `pk` and a message `m` of the
forger's choice. The second item has a key of the forger and the nonce point
`w⋅G - c⋅P`, where `P` is the point of `pk`. That point cancels the term
`c⋅P` of the first item, which the forger cannot produce a signature for.

The nonce point must have an even y-coordinate, since the verifier lifts it
from its x-coordinate. The forger can check that and try another `w`.
`card_rogue`: for a key `P = x⋅G`, at least `(n - 1)/2` of the `n` values of `w`
give such a point, because `w` and `2⋅c⋅x - w` give opposite points.

The model mutants "every randomizer is `1`" and "`zᵢ` does not cover item `i`"
of `scripts/mutate_model.py` are these two verifiers.
-/

namespace Halfagg

open Taproot Taproot.Curve Taproot.BIP340

variable {n : ℕ} [Fact n.Prime] {E X M : Type} [AddCommGroup E] [DecidableEq E]
  (C : Curve n E X) (challenge : X → X → M → ZMod n)

/-- The forger's nonce point `w⋅G - c⋅P`. -/
def rogue (P : E) (c w : ZMod n) : E := C.mulG w - c.val • P

/-! ## Every randomizer is `1` -/

/-- The forgery against the verifier with every randomizer `1`, for the public
key `pk` with point `P` and the message `m`. The forger picks the scalars `k`,
`a` and `w` and the message `m'`. -/
def forgeOnes (pk : X) (P : E) (m m' : M) (k a w : ZMod n) : AggSig n X × List (X × M) :=
  let r₀ := C.x (C.mulG k)
  let e₀ := challenge r₀ pk m
  let r₁ := C.x (rogue C P e₀ w)
  let pk₁ := C.x (C.mulG a)
  let e₁ := challenge r₁ pk₁ m'
  (⟨[r₀, r₁], C.evenScalar k + w + e₁ * C.evenScalar a⟩, [(pk, m), (pk₁, m')])

/-- **Without randomizers anyone forges.** If the forger's nonce point is not
`0` and has an even y-coordinate, its aggregate for `(pk, m)` passes the
verifier with every randomizer `1`. -/
theorem forgeOnes_verifies {pk : X} {P : E} (hP : C.liftX pk = some P) (m m' : M)
    {k a : ZMod n} (hk : k ≠ 0) (ha : a ≠ 0) (w : ZMod n)
    (hQ : rogue C P (challenge (C.x (C.mulG k)) pk m) w ≠ 0)
    (he : C.hasEvenY (rogue C P (challenge (C.x (C.mulG k)) pk m) w) = true) :
    verifyWith C challenge (fun _ => 1) (forgeOnes C challenge pk P m m' k a w).1
      (forgeOnes C challenge pk P m m' k a w).2 = true := by
  have : Fact (1 < n) := ⟨(Fact.out : n.Prime).one_lt⟩
  have hR := C.liftX_x_mulG hk
  have hA := C.liftX_x_mulG ha
  have hL := C.liftX_x _ hQ he
  simp only [forgeOnes, verifyWith, items, List.zipWith_cons_cons, List.zipWith_nil_right,
    List.length_cons, List.length_nil, decide_true, Bool.true_and, List.all_cons, List.all_nil,
    Bool.and_true, lifts, hR, hP, hL, hA, Option.isSome_some, isum_cons, isum_nil, term,
    Option.getD_some, ZMod.val_one, one_smul, add_zero, decide_eq_true_eq]
  rw [C.val_smul_mulG, rogue]
  simp only [map_add]
  abel

/-! ## A randomizer that does not cover its own item -/

/-- Randomizers that hash only the items before their own: `zᵢ` is the hash of
the items `0, …, i - 1`. -/
def zLate (rand : List (Item X M) → ZMod n) (its : List (Item X M)) (i : ℕ) : ZMod n :=
  if i = 0 then 1 else rand (its.take i)

/-- The forgery against the verifier with the randomizers `zLate`. The forger
knows `z₁`, the hash of its first item, before it chooses the second item. -/
def forgeLate (rand : List (Item X M) → ZMod n) (pk : X) (P : E) (m m' : M) (k a w : ZMod n) :
    AggSig n X × List (X × M) :=
  let r₀ := C.x (C.mulG k)
  let e₀ := challenge r₀ pk m
  let z₁ := rand [(r₀, pk, m)]
  let r₁ := C.x (rogue C P (z₁⁻¹ * e₀) w)
  let pk₁ := C.x (C.mulG a)
  let e₁ := challenge r₁ pk₁ m'
  (⟨[r₀, r₁], C.evenScalar k + z₁ * (w + e₁ * C.evenScalar a)⟩, [(pk, m), (pk₁, m')])

/-- **A randomizer must cover its own item.** If `z₁` is not `0` and the
forger's nonce point is not `0` and has an even y-coordinate, its aggregate for
`(pk, m)` passes the verifier with the randomizers `zLate`. `hn` holds for every
key that is a multiple of `G`. -/
theorem forgeLate_verifies (rand : List (Item X M) → ZMod n) {pk : X} {P : E}
    (hP : C.liftX pk = some P) (hn : n • P = 0) (m m' : M) {k a : ZMod n} (hk : k ≠ 0)
    (ha : a ≠ 0) (w : ZMod n) (hz : rand [(C.x (C.mulG k), pk, m)] ≠ 0)
    (hQ : rogue C P ((rand [(C.x (C.mulG k), pk, m)])⁻¹ * challenge (C.x (C.mulG k)) pk m) w ≠ 0)
    (he : C.hasEvenY (rogue C P
      ((rand [(C.x (C.mulG k), pk, m)])⁻¹ * challenge (C.x (C.mulG k)) pk m) w) = true) :
    verifyWith C challenge
      (zLate rand (items (forgeLate C challenge rand pk P m m' k a w).2
        (forgeLate C challenge rand pk P m m' k a w).1.rs))
      (forgeLate C challenge rand pk P m m' k a w).1
      (forgeLate C challenge rand pk P m m' k a w).2 = true := by
  have : Fact (1 < n) := ⟨(Fact.out : n.Prime).one_lt⟩
  have hR := C.liftX_x_mulG hk
  have hA := C.liftX_x_mulG ha
  have hL := C.liftX_x _ hQ he
  simp only [forgeLate, verifyWith, items, zLate, List.zipWith_cons_cons, List.zipWith_nil_right,
    List.length_cons, List.length_nil, decide_true, Bool.true_and, List.all_cons, List.all_nil,
    Bool.and_true, lifts, hR, hP, hL, hA, Option.isSome_some, isum_cons, isum_nil, term,
    Option.getD_some, ZMod.val_one, one_smul, add_zero, decide_eq_true_eq, ↓reduceIte, zero_add,
    one_ne_zero, List.take_succ_cons, List.take_zero]
  rw [C.val_smul_mulG, rogue, nsmul_add, nsmul_sub, C.val_smul_mulG, C.val_smul_mulG,
    ← val_mul_smul hn, mul_inv_cancel_left₀ hz]
  simp only [map_add, mul_add]
  abel

/-! ## Half of the forger's tries give a usable nonce point -/

omit [DecidableEq E] in
/-- For a key `x⋅G`, the tries `w` and `2⋅c⋅x - w` give opposite nonce points. -/
theorem rogue_neg (x c w : ZMod n) :
    rogue C (C.mulG x) c (2 * c * x - w) = -rogue C (C.mulG x) c w := by
  simp only [rogue, C.val_smul_mulG, ← map_sub, ← map_neg]
  congr 1
  ring

omit [DecidableEq E] in
/-- The nonce point is `0` for one try only. -/
theorem rogue_eq_zero_iff (x c w : ZMod n) : rogue C (C.mulG x) c w = 0 ↔ w = c * x := by
  rw [rogue, C.val_smul_mulG, ← map_sub, C.mulG_eq_zero, sub_eq_zero]

/-- **Half of the tries work.** For a key `x⋅G`, the nonce point is not `0` and
has an even y-coordinate for at least `(n - 1)/2` of the `n` values of `w`. -/
theorem card_rogue (x c : ZMod n) :
    n - 1 ≤ 2 * (Finset.univ.filter fun w : ZMod n =>
      rogue C (C.mulG x) c w ≠ 0 ∧ C.hasEvenY (rogue C (C.mulG x) c w) = true).card := by
  classical
  set S := Finset.univ.filter fun w : ZMod n =>
    rogue C (C.mulG x) c w ≠ 0 ∧ C.hasEvenY (rogue C (C.mulG x) c w) = true with hS
  set T := Finset.univ.filter fun w : ZMod n =>
    rogue C (C.mulG x) c w ≠ 0 ∧ C.hasEvenY (rogue C (C.mulG x) c w) = false with hT
  have hTS : T.card ≤ S.card := by
    refine Finset.card_le_card_of_injOn (fun w => 2 * c * x - w) (fun w hw => ?_)
      (fun a _ b _ h => by simpa using h)
    simp only [hT, hS, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
    rw [rogue_neg]
    exact ⟨neg_ne_zero.mpr hw.1, by rw [C.hasEvenY_neg _ hw.1, hw.2]; rfl⟩
  have hU : S ∪ T = Finset.univ.erase (c * x) := by
    ext w
    simp only [hS, hT, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_erase, and_true]
    rw [show w ≠ c * x ↔ rogue C (C.mulG x) c w ≠ 0 from
      (not_congr (rogue_eq_zero_iff C x c w)).symm]
    cases C.hasEvenY (rogue C (C.mulG x) c w) <;> simp
  have hD : Disjoint S T := by
    rw [Finset.disjoint_filter]
    intro w _ h1 h2
    simp [h1.2] at h2
  have hcard : S.card + T.card = n - 1 := by
    rw [← Finset.card_union_of_disjoint hD, hU, Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, ZMod.card]
  omega

end Halfagg
