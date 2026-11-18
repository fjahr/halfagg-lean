import Taproot.BIP340Props

/-!
# BIP458: half-aggregation of BIP340 signatures

The algorithms `Aggregate`, `IncAggregate` and `VerifyAggregate` of BIP458,
over the curve interface of `Taproot.Curve`, and their correctness.

Modelling choices, following `Taproot.BIP340`:
* Public keys and nonces `r` are x-coordinates (`X`), messages have an
  arbitrary type `M`, and `s` values are elements of `ZMod n`. Byte encodings,
  length checks and the range checks `s < n` are in `Halfagg.Vectors`, which
  runs the BIP458 test vectors against this model.
* The tagged hashes are arbitrary functions. `challenge r pk m` is BIP340's
  `int(hash_BIP0340/challenge(r ‖ pk ‖ m)) mod n`, and `rand` maps the list
  `[(r₀, pk₀, m₀), …, (rᵢ, pkᵢ, mᵢ)]` to
  `int(hash_BIP0458/randomizer(r₀ ‖ pk₀ ‖ m₀ ‖ … ‖ rᵢ ‖ pkᵢ ‖ mᵢ)) mod n`.
  BIP458 fixes public keys, messages and nonces at 32 bytes, so this byte
  encoding is injective and modelling `rand` as a function of the list loses
  nothing.
-/

namespace Halfagg

open Taproot Taproot.Curve Taproot.BIP340

/-! ## Indexed sums

`isum f k [a₀, …, a_{l-1}] = f k a₀ + … + f (k + l - 1) a_{l-1}`. BIP458 sums
over list positions, with the randomizer depending on the position. -/

section ISum

variable {α β : Type*} [AddCommMonoid β]

/-- `Σᵢ f (k + i) aᵢ` over the list `a₀, a₁, …`. -/
def isum (f : ℕ → α → β) : ℕ → List α → β
  | _, [] => 0
  | k, a :: l => f k a + isum f (k + 1) l

@[simp] theorem isum_nil (f : ℕ → α → β) (k : ℕ) : isum f k [] = 0 := rfl

@[simp] theorem isum_cons (f : ℕ → α → β) (k : ℕ) (a : α) (l : List α) :
    isum f k (a :: l) = f k a + isum f (k + 1) l := rfl

theorem isum_append (f : ℕ → α → β) (k : ℕ) (l l' : List α) :
    isum f k (l ++ l') = isum f k l + isum f (k + l.length) l' := by
  induction l generalizing k with
  | nil => simp
  | cons a l ih =>
    simp only [List.cons_append, isum_cons, ih, List.length_cons, add_assoc]
    congr 3
    omega

theorem isum_map {γ : Type*} (f : ℕ → α → β) (g : γ → α) (k : ℕ) (l : List γ) :
    isum f k (l.map g) = isum (fun i c => f i (g c)) k l := by
  induction l generalizing k with
  | nil => rfl
  | cons c l ih => simp [ih]

/-- Two indexed sums agree if their summands agree on the list elements at
their positions. -/
theorem isum_congr {f g : ℕ → α → β} {k : ℕ} {l : List α}
    (h : ∀ i a, a ∈ l → k ≤ i → i < k + l.length → f i a = g i a) :
    isum f k l = isum g k l := by
  induction l generalizing k with
  | nil => rfl
  | cons a l ih =>
    simp only [isum_cons]
    rw [h k a List.mem_cons_self le_rfl (by simp)]
    congr 1
    exact ih fun i b hb hi hi' =>
      h i b (List.mem_cons_of_mem a hb) (by omega) (by simp only [List.length_cons]; omega)

theorem map_isum {γ : Type*} [AddCommMonoid γ] (φ : β →+ γ) (f : ℕ → α → β) (k : ℕ)
    (l : List α) : φ (isum f k l) = isum (fun i a => φ (f i a)) k l := by
  induction l generalizing k with
  | nil => simp
  | cons a l ih => simp [ih]

end ISum

/-! ## Aggregation -/

section Aggregation

variable {n : ℕ} {X M : Type*}

/-- A half-aggregate signature `r₀ ‖ … ‖ r_{u-1} ‖ bytes(s)`. -/
structure AggSig (n : ℕ) (X : Type*) where
  rs : List X
  s : ZMod n

/-- The randomizer input of one signature, in hash order: `(r, pk, m)`. -/
abbrev Item (X M : Type*) := X × X × M

/-- The items of already aggregated `(pk, m)` pairs and their nonces. -/
def items (pm : List (X × M)) (rs : List X) : List (Item X M) :=
  List.zipWith (fun pkm r => (r, pkm.1, pkm.2)) pm rs

/-- The item `(r, pk, m)` of a signature to be aggregated. -/
def entryItem (e : Entry n X M) : Item X M := (e.r, e.pk, e.m)

/-- The `(pk, m)` pair of a signature to be aggregated. -/
def entryPM (e : Entry n X M) : X × M := (e.pk, e.m)

/-- The randomizer `zᵢ`: `1` for `i = 0`, otherwise
`int(hash_BIP0458/randomizer(r₀ ‖ pk₀ ‖ m₀ ‖ … ‖ rᵢ ‖ pkᵢ ‖ mᵢ)) mod n`. -/
def z (rand : List (Item X M) → ZMod n) (its : List (Item X M)) (i : ℕ) : ZMod n :=
  if i = 0 then 1 else rand (its.take (i + 1))

/-- BIP458 `IncAggregate(aggsig, pm_aggd, pms_to_agg)`: add the signatures
`pms` to the aggregate `agg` of the pairs `pmAggd`. Fails if the aggregate
has a nonce count different from `pmAggd`. -/
def incAggregate (rand : List (Item X M) → ZMod n) (agg : AggSig n X) (pmAggd : List (X × M))
    (pms : List (Entry n X M)) : Option (AggSig n X) :=
  if agg.rs.length = pmAggd.length then
    let its := items pmAggd agg.rs ++ pms.map entryItem
    some ⟨agg.rs ++ pms.map (·.r),
      agg.s + isum (fun i e => z rand its i * e.s) pmAggd.length pms⟩
  else none

/-- BIP458 `Aggregate(pms)`: `IncAggregate` starting from the empty aggregate
`bytes(0)`. -/
def aggregate (rand : List (Item X M) → ZMod n) (pms : List (Entry n X M)) :
    Option (AggSig n X) :=
  incAggregate rand ⟨[], 0⟩ [] pms

variable (rand : List (Item X M) → ZMod n)

@[simp] theorem z_zero (its : List (Item X M)) : z rand its 0 = 1 := by simp [z]

/-- `zᵢ` depends only on the first `i + 1` items. -/
theorem z_append {its : List (Item X M)} {i : ℕ} (hi : i < its.length) (its' : List (Item X M)) :
    z rand (its ++ its') i = z rand its i := by
  unfold z
  rw [List.take_append_of_le_length (by omega)]

theorem length_items {pm : List (X × M)} {rs : List X} (h : rs.length = pm.length) :
    (items pm rs).length = pm.length := by
  simp [items, h]

theorem items_append {pm pm' : List (X × M)} {rs rs' : List X} (h : rs.length = pm.length) :
    items (pm ++ pm') (rs ++ rs') = items pm rs ++ items pm' rs' := by
  unfold items
  rw [List.zipWith_append h.symm]

theorem items_entries (pms : List (Entry n X M)) :
    items (pms.map entryPM) (pms.map (·.r)) = pms.map entryItem := by
  induction pms with
  | nil => rfl
  | cons e pms ih => simp [items, entryPM, entryItem] at ih ⊢

/-- **Incremental aggregation agrees with aggregating at once**: adding `A`
and then `B` to an aggregate gives the same result as adding `A ++ B`. -/
theorem incAggregate_append (agg : AggSig n X) (pmAggd : List (X × M)) (A B : List (Entry n X M)) :
    incAggregate rand agg pmAggd (A ++ B) =
      (incAggregate rand agg pmAggd A).bind fun agg' =>
        incAggregate rand agg' (pmAggd ++ A.map entryPM) B := by
  by_cases h : agg.rs.length = pmAggd.length
  · have hits : items (pmAggd ++ A.map entryPM) (agg.rs ++ A.map (·.r)) =
        items pmAggd agg.rs ++ A.map entryItem := by
      rw [items_append h, items_entries]
    have hv : (items pmAggd agg.rs ++ A.map entryItem).length = pmAggd.length + A.length := by
      simp [length_items h]
    simp only [incAggregate, h, ↓reduceIte, Option.bind_some, List.length_append, List.length_map,
      hits, List.map_append, List.append_assoc, Option.some.injEq, AggSig.mk.injEq, true_and]
    rw [isum_append, add_assoc]
    congr 2
    refine isum_congr fun i e _ _ hi => ?_
    rw [← List.append_assoc, z_append rand (by rw [hv]; exact hi)]
  · simp [incAggregate, h]

/-- `Aggregate(A ++ B) = IncAggregate(Aggregate(A), A, B)`. -/
theorem aggregate_append (A B : List (Entry n X M)) :
    aggregate rand (A ++ B) =
      (aggregate rand A).bind fun agg => incAggregate rand agg (A.map entryPM) B := by
  simpa [aggregate] using incAggregate_append rand ⟨[], 0⟩ [] A B

/-- The input of `shiftedPair`: the first two signatures with `δ` moved from
the second `s` to the first, weighted by `z₁`. -/
def shiftedPair (e₀ e₁ : Entry n X M) (rest : List (Entry n X M)) (δ : ZMod n) :
    List (Entry n X M) :=
  { e₀ with s := e₀.s + z rand ((e₀ :: e₁ :: rest).map entryItem) 1 * δ } ::
    { e₁ with s := e₁.s - δ } :: rest

/-- Shifting `δ` between the first two `s` values, weighted by `z₁`, does not
change the aggregate: `z₁` does not depend on any `s`. -/
theorem aggregate_shiftedPair (e₀ e₁ : Entry n X M) (rest : List (Entry n X M)) (δ : ZMod n) :
    aggregate rand (shiftedPair rand e₀ e₁ rest δ) = aggregate rand (e₀ :: e₁ :: rest) := by
  simp only [aggregate, incAggregate, shiftedPair, List.length_nil, ↓reduceIte, List.map_cons,
    isum_cons, Option.some.injEq, AggSig.mk.injEq, true_and]
  simp only [entryItem, z_zero, zero_add, items, List.zipWith_nil_left, List.nil_append]
  ring

end Aggregation

/-! ## Verification -/

section Verification

variable {n : ℕ} [Fact n.Prime] {E X M : Type*} [AddCommGroup E] [DecidableEq E] [DecidableEq X]

/-- `Rᵢ + eᵢ⋅Pᵢ` for one item, with a failed `lift_x` read as `0` (the
verifier checks the lifts separately). -/
def term (C : Curve n E X) (challenge : X → X → M → ZMod n) (it : Item X M) : E :=
  (C.liftX it.1).getD 0 + (challenge it.1 it.2.1 it.2.2).val • (C.liftX it.2.1).getD 0

/-- Whether `lift_x(r)` and `lift_x(pk)` both succeed. -/
def lifts (C : Curve n E X) (it : Item X M) : Bool :=
  (C.liftX it.1).isSome && (C.liftX it.2.1).isSome

/-- The checks of `VerifyAggregate` with the randomizers given as `zf i`: the
nonce count matches, every `lift_x` succeeds, and
`s⋅G = z₀⋅(R₀ + e₀⋅P₀) + … + z_{u-1}⋅(R_{u-1} + e_{u-1}⋅P_{u-1})`. -/
def verifyWith (C : Curve n E X) (challenge : X → X → M → ZMod n) (zf : ℕ → ZMod n)
    (agg : AggSig n X) (pm : List (X × M)) : Bool :=
  let its := items pm agg.rs
  decide (agg.rs.length = pm.length) && its.all (lifts C) &&
    decide (C.mulG agg.s = isum (fun i it => (zf i).val • term C challenge it) 0 its)

/-- BIP458 `VerifyAggregate(aggsig, pm_aggd)`, with the randomizers `zᵢ` from
the randomizer hash `rand`. -/
def verifyAggregate (C : Curve n E X) (challenge : X → X → M → ZMod n)
    (rand : List (Item X M) → ZMod n) (agg : AggSig n X) (pm : List (X × M)) : Bool :=
  verifyWith C challenge (z rand (items pm agg.rs)) agg pm

variable (C : Curve n E X) (challenge : X → X → M → ZMod n) (rand : List (Item X M) → ZMod n)

/-- For a valid signature, `R + e⋅P = s⋅G`. -/
theorem term_of_valid {e : Entry n X M} (he : Entry.valid C challenge e = true) :
    term C challenge (entryItem e) = C.mulG e.s := by
  obtain ⟨-, -, h0⟩ := (valid_iff C challenge e).mp he
  unfold Entry.defect at h0
  rw [sub_sub, sub_eq_zero] at h0
  exact h0.symm

theorem lifts_of_valid {e : Entry n X M} (he : Entry.valid C challenge e = true) :
    lifts C (entryItem e) = true := by
  obtain ⟨hP, hR, -⟩ := (valid_iff C challenge e).mp he
  simp [lifts, entryItem, hP, hR]

omit [DecidableEq X] in
/-- The empty aggregate `bytes(0)` verifies against the empty list. -/
theorem verifyAggregate_empty : verifyAggregate C challenge rand ⟨[], 0⟩ [] = true := by
  simp [verifyAggregate, verifyWith, items]

/-- **Correctness of `IncAggregate`**: adding valid signatures to an aggregate
that verifies gives an aggregate that verifies, for every choice of the hash
functions. -/
theorem verifyAggregate_incAggregate {agg agg' : AggSig n X} {pmAggd : List (X × M)}
    {pms : List (Entry n X M)} (hagg : verifyAggregate C challenge rand agg pmAggd = true)
    (hpms : ∀ e ∈ pms, Entry.valid C challenge e = true)
    (hinc : incAggregate rand agg pmAggd pms = some agg') :
    verifyAggregate C challenge rand agg' (pmAggd ++ pms.map entryPM) = true := by
  unfold incAggregate at hinc
  split_ifs at hinc with hlen
  cases hinc
  simp only [verifyAggregate, verifyWith, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true] at hagg ⊢
  obtain ⟨⟨-, hlifts⟩, hsum⟩ := hagg
  have hits : items (pmAggd ++ pms.map entryPM) (agg.rs ++ pms.map (·.r)) =
      items pmAggd agg.rs ++ pms.map entryItem := by
    rw [items_append hlen, items_entries]
  have hv : (items pmAggd agg.rs).length = pmAggd.length := length_items hlen
  rw [hits]
  refine ⟨⟨by simp [hlen], ?_⟩, ?_⟩
  · intro it hit
    rcases List.mem_append.mp hit with hit | hit
    · exact hlifts it hit
    · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hit
      exact lifts_of_valid C challenge (hpms e he)
  · rw [isum_append, hv, map_add, hsum, zero_add, isum_map, map_isum]
    congr 1
    · refine isum_congr fun i it _ _ hi => ?_
      rw [z_append rand (by omega)]
    · refine isum_congr fun i e he _ _ => ?_
      rw [term_of_valid C challenge (hpms e he), C.val_smul_mulG]

/-- **Correctness of `Aggregate`**: aggregating valid signatures gives an
aggregate that verifies, for every choice of the hash functions. -/
theorem verifyAggregate_aggregate {agg : AggSig n X} {pms : List (Entry n X M)}
    (hpms : ∀ e ∈ pms, Entry.valid C challenge e = true) (h : aggregate rand pms = some agg) :
    verifyAggregate C challenge rand agg (pms.map entryPM) = true := by
  simpa using verifyAggregate_incAggregate C challenge rand
    (verifyAggregate_empty C challenge rand) hpms h

/-- **A one-signature aggregate is the BIP340 signature itself**: with
`z₀ = 1`, `VerifyAggregate(r ‖ bytes(s), [(pk, m)])` accepts exactly when
BIP340 `Verify(pk, m, (r, s))` does. -/
theorem verifyAggregate_single (r pk : X) (m : M) (s : ZMod n) :
    verifyAggregate C challenge rand ⟨[r], s⟩ [(pk, m)] = verify C challenge pk m (r, s) := by
  have : Fact (1 < n) := ⟨(Fact.out : n.Prime).one_lt⟩
  rw [Bool.eq_iff_iff, verify_eq_true_iff]
  simp only [verifyAggregate, verifyWith, items, List.zipWith_cons_cons, List.zipWith_nil_right,
    List.length_cons, List.length_nil, decide_true, List.all_cons, List.all_nil, Bool.and_true,
    Bool.true_and, isum_cons, isum_nil, z_zero, ZMod.val_one, one_smul, add_zero, lifts, term,
    Bool.and_eq_true, decide_eq_true_eq]
  cases hP : C.liftX pk <;> cases hR : C.liftX r <;> simp [eq_sub_iff_add_eq, eq_comm]

/-- **The aggregate does not certify the individual signatures** (BIP458's
remark after `Aggregate`): given a valid second signature and any `δ ≠ 0`,
`shiftedPair` contains an invalid signature, yet aggregates to the same
aggregate signature as the original input. If the original signatures are
valid, that aggregate verifies (`verifyAggregate_aggregate`). -/
theorem aggregate_accepts_invalid {e₀ e₁ : Entry n X M} (rest : List (Entry n X M))
    (h₁ : Entry.valid C challenge e₁ = true) {δ : ZMod n} (hδ : δ ≠ 0) :
    Entry.valid C challenge { e₁ with s := e₁.s - δ } = false ∧
      aggregate rand (shiftedPair rand e₀ e₁ rest δ) = aggregate rand (e₀ :: e₁ :: rest) := by
  refine ⟨?_, aggregate_shiftedPair rand e₀ e₁ rest δ⟩
  by_contra h
  rw [Bool.not_eq_false] at h
  exact hδ (sub_eq_self.mp (verify_unique C challenge h₁ h).symm)

/-- `VerifyAggregate` as one sum of scalar multiplications:
`s⋅G = z₀⋅R₀ + (z₀⋅e₀)⋅P₀ + … + z_{u-1}⋅R_{u-1} + (z_{u-1}⋅e_{u-1})⋅P_{u-1}`, with
the products `zᵢ⋅eᵢ` reduced mod `n`. A multi-scalar multiplication computes
this form. -/
def verifyMulti (C : Curve n E X) (challenge : X → X → M → ZMod n)
    (rand : List (Item X M) → ZMod n) (agg : AggSig n X) (pm : List (X × M)) : Bool :=
  let its := items pm agg.rs
  decide (agg.rs.length = pm.length) && its.all (lifts C) &&
    decide (C.mulG agg.s = isum (fun i it =>
      (z rand its i).val • (C.liftX it.1).getD 0 +
        (z rand its i * challenge it.1 it.2.1 it.2.2).val • (C.liftX it.2.1).getD 0) 0 its)

omit [DecidableEq X] in
/-- **The multi-scalar form is `VerifyAggregate` in a group of prime order.**
Reducing `zᵢ⋅eᵢ` mod `n` needs `n⋅Pᵢ = 0` for the lifted public keys. That holds
for every point of secp256k1, but it is a hypothesis here
(`Taproot.Curve.PrimeOrder`), because taproot-lean does not prove that the
curve has `n` points. -/
theorem verifyMulti_eq (hord : PrimeOrder n E) (agg : AggSig n X) (pm : List (X × M)) :
    verifyMulti C challenge rand agg pm = verifyAggregate C challenge rand agg pm := by
  have h : isum (fun i it =>
        (z rand (items pm agg.rs) i).val • (C.liftX it.1).getD 0 +
          (z rand (items pm agg.rs) i * challenge it.1 it.2.1 it.2.2).val •
            (C.liftX it.2.1).getD 0) 0 (items pm agg.rs) =
      isum (fun i it => (z rand (items pm agg.rs) i).val • term C challenge it) 0
        (items pm agg.rs) :=
    isum_congr fun i it _ _ _ => by rw [term, nsmul_add, val_mul_smul (hord _)]
  simp only [verifyMulti, verifyAggregate, verifyWith, h]

end Verification

end Halfagg
