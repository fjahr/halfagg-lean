import Halfagg.Security

/-!
# Representations and extraction

The algebra of the reduction, with the target key `P* = d⋅G`:

* `flatten_spec`: flattening a valid explanation over the received points gives a
  representation `(α, β)` of the explained point, `α⋅G + β⋅P*`.
* `memoize_ok`: the representations the reduction records stay valid.
* `extract_or_bad`: a winning forgery either gives a valid BIP340 forgery on an
  unsigned message (`extractForgery`), or has a prefix whose last coefficient
  `β*` is nonzero and whose randomized sum `Σ zᵢ⋅β*ᵢ` vanishes (the bad event).
-/

set_option linter.unusedSectionVars false

namespace Halfagg.Security

open Taproot Taproot.Curve Taproot.BIP340 AlgebraicGroupModel.Interaction

attribute [local instance] smulVal

variable {n : ℕ} [Fact n.Prime] {E X M : Type} [AddCommGroup E] [DecidableEq E]
  [DecidableEq X] [DecidableEq M] (C : Curve n E X) (challenge : X → X → M → ZMod n)

/-! ## Indexed sums -/

theorem isum_succ {α β : Type*} [AddCommMonoid β] (f : ℕ → α → β) (k : ℕ) (l : List α) :
    isum f (k + 1) l = isum (fun i a => f (i + 1) a) k l := by
  induction l generalizing k with
  | nil => rfl
  | cons a l ih => simp [ih]

theorem sum_mapIdx_eq_isum {α β : Type*} [AddCommMonoid β] (f : ℕ → α → β) (l : List α) :
    (l.mapIdx f).sum = isum f 0 l := by
  induction l generalizing f with
  | nil => rfl
  | cons a l ih =>
    rw [List.mapIdx_cons, List.sum_cons, ih, isum_cons, zero_add, isum_succ]

theorem map_isum_fun {α β γ : Type*} [AddCommMonoid β] [AddCommMonoid γ] (φ : β → γ)
    (h0 : φ 0 = 0) (hadd : ∀ a b, φ (a + b) = φ a + φ b) (f : ℕ → α → β) (k : ℕ)
    (l : List α) : φ (isum f k l) = isum (fun i a => φ (f i a)) k l := by
  induction l generalizing k with
  | nil => simp [h0]
  | cons a l ih => simp [hadd, ih]

/-! ## Representations over `(G, P*)` -/

/-- The point `(α + β⋅d)⋅G` represented by `ρ` when `P* = d⋅G`. -/
def repPoint (d : ZMod n) (ρ : Rep n) : E := C.mulG (ρ.1 + ρ.2 * d)

theorem evalRep_mulG (d : ZMod n) (ρ : Rep n) :
    evalRep C (C.mulG d) ρ = repPoint C d ρ := by
  rw [evalRep, repPoint, C.val_smul_mulG, ← map_add]

/-- The received points are represented by `basis`. -/
def BasisOK (d : ZMod n) (pts : List E) (basis : List (Rep n)) : Prop :=
  List.Forall₂ (fun P ρ => P = repPoint C d ρ) pts basis

theorem smul_repPoint (d c : ZMod n) (ρ : Rep n) :
    c • repPoint C d ρ = repPoint C d (c * ρ.1, c * ρ.2) := by
  change c.val • (repPoint C d ρ : E) = _
  rw [repPoint, repPoint, C.val_smul_mulG]
  ring_nf

theorem flatten_spec_aux (d : ZMod n) (coeff : List (ZMod n)) {pts : List E}
    {basis : List (Rep n)} (h : BasisOK C d pts basis) (k : ℕ) :
    isum (fun i P => (coeff[i]?).getD 0 • P) k pts =
      repPoint C d (isum (fun i ρ => ((coeff[i]?).getD 0 * ρ.1, (coeff[i]?).getD 0 * ρ.2))
        k basis) := by
  induction h generalizing k with
  | nil => simp [repPoint]
  | cons hP _ ih =>
    rw [isum_cons, isum_cons, ih, hP, smul_repPoint]
    simp only [repPoint, Prod.fst_add, Prod.snd_add, ← map_add]
    ring_nf

/-- **Flattening is correct**: a valid explanation of `Y` over the received points
flattens to a representation of `Y`. -/
theorem flatten_spec (d : ZMod n) (coeff : List (ZMod n)) {pts : List E}
    {basis : List (Rep n)} (h : BasisOK C d pts basis) :
    evaluate coeff pts = repPoint C d (flatten coeff basis) := by
  rw [evaluate, sum_mapIdx_eq_isum, flatten]
  exact flatten_spec_aux C d coeff h 0

/-- `lift_x(x(Y))` is `Y` or `-Y`, whichever has an even y; `liftRep` follows. -/
theorem liftX_x_liftRep (d : ZMod n) {Y : E} {ρ : Rep n} (hY : Y = repPoint C d ρ)
    (h0 : Y ≠ 0) : C.liftX (C.x Y) = some (repPoint C d (liftRep C Y ρ)) := by
  unfold liftRep
  split_ifs with he
  · rw [← hY]; exact C.liftX_x Y h0 he
  · have hn : C.hasEvenY (-Y) = true := by rw [C.hasEvenY_neg Y h0]; simpa using he
    rw [← C.x_neg, C.liftX_x (-Y) (neg_ne_zero.mpr h0) hn, hY]
    simp only [repPoint, Prod.fst_neg, Prod.snd_neg, ← map_neg, neg_mul, neg_add]

/-- The recorded representations are valid: whenever `lift_x(v)` succeeds, it is
the recorded point. -/
def MemoOK (d : ZMod n) (memo : X → Option (Rep n)) : Prop :=
  ∀ v ρ, memo v = some ρ → ∀ Q, C.liftX v = some Q → Q = repPoint C d ρ

theorem memoOK_none (d : ZMod n) : MemoOK C d (fun _ : X => none) := by
  intro v ρ h; cases h

/-- Recording the representation of one explained point keeps the memo valid.
The point at infinity is harmless because its x-coordinate does not lift. -/
theorem memoOK_record (hx0 : C.liftX (C.x 0) = none) (d : ZMod n) (basis : List (Rep n))
    {memo : X → Option (Rep n)} (hm : MemoOK C d memo) {Y : E} {coeff : List (ZMod n)}
    (hY : Y = repPoint C d (flatten coeff basis)) :
    MemoOK C d (memoRecord C basis memo Y coeff) := by
  unfold memoRecord
  split
  · exact hm
  · intro v σ hv Q hQ
    by_cases hvY : v = C.x Y
    · subst hvY
      rw [Function.update_self, Option.some.injEq] at hv
      subst hv
      by_cases h0 : Y = 0
      · subst h0; rw [hx0] at hQ; cases hQ
      · rw [liftX_x_liftRep C d hY h0, Option.some.injEq] at hQ
        exact hQ.symm
    · rw [Function.update_of_ne hvY] at hv
      exact hm v σ hv Q hQ

theorem memoOK_memoize (hx0 : C.liftX (C.x 0) = none) (d : ZMod n) {st : Core n X M}
    (hm : MemoOK C d st.memo) {recv : List E} (hb : BasisOK C d recv st.basis)
    {pts : List E} {coeffs : List (List (ZMod n))}
    (hv : List.Forall₂ (fun Y c => c.length = recv.length ∧ evaluate c recv = Y) pts coeffs) :
    MemoOK C d (memoize C st pts coeffs).memo := by
  unfold memoize
  dsimp only
  generalize st.memo = memo at hm
  induction hv generalizing memo with
  | nil => exact hm
  | cons hY _ ih =>
    rw [memoizeList, List.headD_cons, List.tail_cons]
    exact ih _ (memoOK_record C hx0 d st.basis hm ((flatten_spec C d _ hb).symm.trans hY.2).symm)

/-- Recorded representations are never replaced. -/
theorem memoRecord_of_some (basis : List (Rep n)) {memo : X → Option (Rep n)} {v : X}
    {ρ : Rep n} (h : memo v = some ρ) (Y : E) (coeff : List (ZMod n)) :
    memoRecord C basis memo Y coeff v = some ρ := by
  rcases hY : memo (C.x Y) with _ | σ
  · simp only [memoRecord, hY]
    rw [Function.update_of_ne (fun hv => by rw [hv, hY] at h; cases h)]
    exact h
  · simp only [memoRecord, hY]; exact h

theorem memoizeList_of_some (basis : List (Rep n)) (pts : List E)
    (coeffs : List (List (ZMod n))) {memo : X → Option (Rep n)} {v : X} {ρ : Rep n}
    (h : memo v = some ρ) : memoizeList C basis pts coeffs memo v = some ρ := by
  induction pts generalizing coeffs memo with
  | nil => exact h
  | cons Y pts ih => exact ih _ (memoRecord_of_some C basis h Y _)

/-- After recording, every point's x-coordinate has a representation. -/
theorem memoizeList_isSome (basis : List (Rep n)) (pts : List E)
    (coeffs : List (List (ZMod n))) (memo : X → Option (Rep n)) {Y : E} (hY : Y ∈ pts) :
    (memoizeList C basis pts coeffs memo (C.x Y)).isSome := by
  induction pts generalizing coeffs memo with
  | nil => cases hY
  | cons Z pts ih =>
    rcases List.mem_cons.mp hY with rfl | hY
    · rw [memoizeList]
      have : (memoRecord C basis memo Y (coeffs.headD []) (C.x Y)).isSome := by
        rcases hY' : memo (C.x Y) with _ | σ <;> simp [memoRecord, hY']
      obtain ⟨ρ, hρ⟩ := Option.isSome_iff_exists.mp this
      rw [memoizeList_of_some C basis pts _ hρ]
      rfl
    · exact ih _ _ hY

theorem memoize_basis (st : Core n X M) (pts : List E) (coeffs : List (List (ZMod n))) :
    (memoize C st pts coeffs).basis = st.basis := rfl

theorem memoize_signed (st : Core n X M) (pts : List E) (coeffs : List (List (ZMod n))) :
    (memoize C st pts coeffs).signed = st.signed := rfl

/-! ## Extraction -/

theorem isum_add_fun {α β : Type*} [AddCommMonoid β] (f g : ℕ → α → β) (k : ℕ) (l : List α) :
    isum (fun i a => f i a + g i a) k l = isum f k l + isum g k l := by
  induction l generalizing k with
  | nil => simp
  | cons a l ih => simp only [isum_cons, ih]; abel

theorem isum_mul_right {α : Type*} (f : ℕ → α → ZMod n) (c : ZMod n) (k : ℕ) (l : List α) :
    isum (fun i a => f i a * c) k l = isum f k l * c := by
  induction l generalizing k with
  | nil => simp
  | cons a l ih => simp only [isum_cons, ih, add_mul]

theorem isum_zero_fun {α β : Type*} [AddCommMonoid β] (k : ℕ) (l : List α) :
    isum (fun _ _ => (0 : β)) k l = 0 := by
  induction l generalizing k with
  | nil => rfl
  | cons a l ih => simp [ih]

theorem isum_eq_zero {α β : Type*} [AddCommMonoid β] {f : ℕ → α → β} {k : ℕ} {l : List α}
    (h : ∀ i a, a ∈ l → k ≤ i → i < k + l.length → f i a = 0) : isum f k l = 0 := by
  rw [isum_congr (g := fun _ _ => 0) h]
  exact isum_zero_fun k l

/-- An annotated item without its representations. -/
def strip (a : AItem n X M) : Item X M := (a.r, a.pk, a.m)

theorem items_map (its : List (Item X M)) : items (its.map (·.2)) (its.map (·.1)) = its := by
  induction its with
  | nil => rfl
  | cons it its ih => simp only [List.map_cons, items, List.zipWith_cons_cons] at ih ⊢; rw [ih]

/-- The representations of an annotated item are valid wherever they can be checked. -/
def ItemOK (d : ZMod n) (a : AItem n X M) : Prop :=
  (∀ Q, C.liftX a.r = some Q → Q = repPoint C d a.repR) ∧
    (∀ Q, C.liftX a.pk = some Q → Q = repPoint C d a.repPk)

/-- With valid representations, `Rᵢ + eᵢ⋅Pᵢ = (α*ᵢ + β*ᵢ⋅d)⋅G`. -/
theorem term_strip (d : ZMod n) {a : AItem n X M} (ha : ItemOK C d a)
    (hl : lifts C (strip a) = true) :
    term C challenge (strip a) =
      C.mulG ((starRep challenge a).1 + (starRep challenge a).2 * d) := by
  simp only [lifts, strip, Bool.and_eq_true, Option.isSome_iff_exists] at hl
  obtain ⟨⟨R, hR⟩, ⟨P, hP⟩⟩ := hl
  simp only [term, strip, hR, hP, Option.getD_some, ha.1 R hR, ha.2 P hP, repPoint,
    C.val_smul_mulG, ← map_add, starRep]
  congr 1
  ring

/-- A verifying aggregate pins down `s` linearly: `s = α + β⋅d` with
`α = Σ zᵢ⋅α*ᵢ` and `β = Σ zᵢ⋅β*ᵢ`. -/
theorem s_eq (d : ZMod n) (items : List (AItem n X M)) (zf : ℕ → ZMod n) (s : ZMod n)
    (hok : ∀ a ∈ items, ItemOK C d a) (hlift : ∀ a ∈ items, lifts C (strip a) = true)
    (heq : C.mulG s =
      isum (fun i it => (zf i).val • term C challenge it) 0 (items.map strip)) :
    s = isum (fun i b => zf i * (starRep challenge b).1) 0 items +
      isum (fun i b => zf i * (starRep challenge b).2) 0 items * d := by
  rw [isum_map, isum_congr (g := fun i b =>
    C.mulG (zf i * ((starRep challenge b).1 + (starRep challenge b).2 * d)))] at heq
  · rw [← map_isum_fun C.mulG (map_zero _) (map_add _)] at heq
    rw [C.mulG_injective heq, ← isum_mul_right, ← isum_add_fun]
    exact isum_congr fun i b _ _ _ => by ring
  · intro i b hb _ _
    rw [term_strip C challenge d (hok b hb) (hlift b hb), C.val_smul_mulG]

/-- **Extraction** (Chen and Zhao, proof of Theorem 1). A winning forgery whose
representations are valid either yields a valid BIP340 forgery on an unsigned
message, or has a prefix `items.take (j + 1)` with `j ≥ 1` whose last
coefficient `β*ⱼ` is nonzero and whose randomized sum `Σ zᵢ⋅β*ᵢ` vanishes. -/
theorem extract_or_bad [Inhabited M] (d : ZMod n) (hd : d ≠ 0)
    (heven : C.hasEvenY (C.mulG d) = true) (items : List (AItem n X M)) (s : ZMod n)
    (zs : List (ZMod n)) (signed : List M) (hz0 : zs.getD 0 0 = 1)
    (hok : ∀ a ∈ items, ItemOK C d a)
    (hwin : aggWins C challenge (C.x (C.mulG d)) (items.map strip) s zs
      (fun m => signed.contains m) = true) :
    (BIP340.verify C challenge (C.x (C.mulG d))
        (extractForgery C challenge (C.x (C.mulG d)) items s zs signed).1
        (extractForgery C challenge (C.x (C.mulG d)) items s zs signed).2 = true ∧
      signed.contains (extractForgery C challenge (C.x (C.mulG d)) items s zs signed).1 = false) ∨
    ∃ j, 1 ≤ j ∧ ∃ hj : j < items.length, (starRep challenge items[j]).2 ≠ 0 ∧
      isum (fun i b => zs.getD i 0 * (starRep challenge b).2) 0 (items.take (j + 1)) = 0 := by
  set pk := C.x (C.mulG d) with hpk
  have hPstar : C.liftX pk = some (C.mulG d) := C.liftX_x _ (C.mulG_ne_zero hd) heven
  -- unpack the win
  simp only [aggWins, verifyWith, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true, List.any_eq_true] at hwin
  obtain ⟨⟨⟨-, hlifts⟩, heq⟩, ⟨it, hit, htarget⟩⟩ := hwin
  rw [items_map] at hlifts heq
  have hlift : ∀ a ∈ items, lifts C (strip a) = true :=
    fun a ha => hlifts _ (List.mem_map.mpr ⟨a, ha, rfl⟩)
  have hs := s_eq C challenge d items (fun i => zs.getD i 0) s hok hlift heq
  -- the target item
  obtain ⟨a₀, ha₀, rfl⟩ := List.mem_map.mp hit
  have hfind : (items.find? fun a => a.pk == pk && !signed.contains a.m).isSome := by
    rw [List.find?_isSome]
    exact ⟨a₀, ha₀, by simpa [strip] using htarget⟩
  obtain ⟨a, hfa⟩ := Option.isSome_iff_exists.mp hfind
  have ha := List.mem_of_find?_eq_some hfa
  have hpa := List.find?_some hfa
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hpa
  obtain ⟨hapk, hfresh⟩ := hpa
  have hPa : repPoint C d a.repPk = C.mulG d := by
    have hl := hlift a ha
    simp only [lifts, strip, Bool.and_eq_true] at hl
    rw [hapk, hPstar] at hl
    exact ((hok a ha).2 _ (by rw [hapk, hPstar])).symm
  unfold extractForgery
  rw [hfa]
  dsimp only
  split_ifs with hβa
  · -- `β*ₐ = 0`: `(rₐ, α*ₐ)` is a signature
    left
    refine ⟨?_, hfresh⟩
    rw [verify_eq_true_iff]
    refine ⟨C.mulG d, hPstar, ?_⟩
    have hl := hlift a ha
    simp only [lifts, strip, Bool.and_eq_true, Option.isSome_iff_exists] at hl
    obtain ⟨⟨R, hR⟩, -⟩ := hl
    rw [hR, (hok a ha).1 R hR, C.val_smul_mulG, ← map_sub, repPoint]
    apply congrArg some
    apply congrArg C.mulG
    have hPd : a.repPk.1 + a.repPk.2 * d = d := C.mulG_injective hPa
    simp only [starRep] at hβa ⊢
    rw [← hapk]
    linear_combination d * hβa - (challenge a.r a.pk a.m) * hPd
  · by_cases hβ : isum (fun i b => zs.getD i 0 * (starRep challenge b).2) 0 items = 0
    · -- `β* = 0` while `β*ₐ ≠ 0`: cut after the last item with `β*ⱼ ≠ 0`
      right
      classical
      let J := (Finset.range items.length).filter fun j =>
        ∃ hj : j < items.length, (starRep challenge items[j]).2 ≠ 0
      obtain ⟨ia, hia, hia'⟩ := List.mem_iff_getElem.mp ha
      have hJ : J.Nonempty := ⟨ia, by simp [J, hia, hia', hβa]⟩
      set j := J.max' hJ
      obtain ⟨-, hjlen, hβj⟩ := Finset.mem_filter.mp (J.max'_mem hJ)
      have hafter : ∀ i (hi : i < items.length), j < i →
          (starRep challenge items[i]).2 = 0 := by
        intro i hi hji
        by_contra h
        have : i ∈ J := by simp [J, hi, h]
        exact absurd (J.le_max' i this) (not_le.mpr hji)
      have hcut : isum (fun i b => zs.getD i 0 * (starRep challenge b).2) 0
          (items.take (j + 1)) =
          isum (fun i b => zs.getD i 0 * (starRep challenge b).2) 0 items := by
        conv_rhs => rw [← List.take_append_drop (j + 1) items]
        rw [isum_append, isum_eq_zero (l := items.drop (j + 1)), add_zero]
        intro i b hb hi _
        obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hb
        simp only [List.getElem_drop]
        rw [hafter _ _ (by simp at hi ⊢; omega), mul_zero]
      refine ⟨j, ?_, hjlen, hβj, hcut.trans hβ⟩
      by_contra hj0
      have hj0 : j = 0 := by omega
      have hall : isum (fun i b => zs.getD i 0 * (starRep challenge b).2) 0 items =
          (starRep challenge items[0]).2 := by
        rw [← hcut, hj0]
        have hz0' : zs[0]?.getD 0 = 1 := by simpa [List.getD_eq_getElem?_getD] using hz0
        cases items with
        | nil => simp at hjlen
        | cons b l => simp [hz0']
      rw [hall] at hβ
      have hidx : items[j] = items[0] := by simp only [hj0]
      exact hβj (by rw [hidx]; exact hβ)
    · -- `β* ≠ 0`: `(s - α*)/β*` is the secret key
      left
      have hx : (s - isum (fun i b => zs.getD i 0 * (starRep challenge b).1) 0 items) /
          isum (fun i b => zs.getD i 0 * (starRep challenge b).2) 0 items = d := by
        rw [div_eq_iff hβ, hs]; ring
      rw [hx]
      have hsign : ∃ sig, BIP340.sign C challenge (fun _ _ _ => 1) d a.m = some sig := by
        unfold BIP340.sign
        simp [hd]
      obtain ⟨sig, hsig⟩ := hsign
      rw [hsig, Option.getD_some]
      exact ⟨verify_sign C challenge (fun _ _ _ => 1) (by simp [pubkey, hd, hpk]) hsig, hfresh⟩

end Halfagg.Security
