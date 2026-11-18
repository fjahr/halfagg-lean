import Halfagg.Vectors

/-!
# The byte encodings lose nothing

`Halfagg/Basic.lean` and the security theorems work with x-only keys and nonces
as field elements and with the randomizer as a function of the item list.
BIP458 works with bytes. This file proves the two facts that connect them.

* `randomizerInput_injective`, `randomizerF_input_injective`: the bytes
  `r₀ ‖ pk₀ ‖ m₀ ‖ … ‖ rᵢ ‖ pkᵢ ‖ mᵢ` that the randomizer hashes determine the
  item list, because every field has 32 bytes. So a hash of these bytes is a
  function of the item list, and different lists give different hash inputs.
* `verifyAggregateBytes_eq`: `VerifyAggregate` on bytes is the parsing and range
  checks of `decodeVerify` followed by the model's `verifyAggregate`.
  `decodeVerify_pm_injective` shows that decoding keeps different `(pk, m)`
  lists apart, and `decodeVerify_randomizer` that the randomizers of the decoded
  input hash the bytes of the input.

No proof here uses compiled evaluation. `verifyAggregateBytes_eq` mentions the
curve `secp256k1` and inherits taproot-lean's compiled computation of `n·G = 0`
from it (`Halfagg/Summary.lean`).
-/

namespace Halfagg.Vectors

open Taproot Taproot.Secp256k1 Taproot.BIP340 Taproot.BIP340Vectors

/-! ## Big-endian numbers -/

theorem toNatBE_foldl (b : Bytes) (acc : ℕ) :
    b.foldl (fun acc x => acc * 256 + x.toNat) acc = acc * 256 ^ b.length + toNatBE b := by
  induction b generalizing acc with
  | nil => simp [toNatBE]
  | cons a l ih =>
    simp only [List.foldl_cons, toNatBE, List.length_cons]
    rw [ih, ih (0 * 256 + a.toNat)]
    ring

theorem toNatBE_cons (a : UInt8) (l : Bytes) :
    toNatBE (a :: l) = a.toNat * 256 ^ l.length + toNatBE l := by
  have h := toNatBE_foldl l (0 * 256 + a.toNat)
  rw [Nat.zero_mul, Nat.zero_add] at h
  simpa only [toNatBE, List.foldl_cons, Nat.zero_mul, Nat.zero_add] using h

theorem toNatBE_lt (b : Bytes) : toNatBE b < 256 ^ b.length := by
  induction b with
  | nil => simp [toNatBE]
  | cons a l ih =>
    rw [toNatBE_cons, List.length_cons, pow_succ]
    have ha : a.toNat < 256 := a.toNat_lt
    nlinarith

/-- `int` is injective on byte strings of the same length. -/
theorem toNatBE_injective {b b' : Bytes} (hl : b.length = b'.length)
    (h : toNatBE b = toNatBE b') : b = b' := by
  induction b generalizing b' with
  | nil =>
    cases b' with
    | nil => rfl
    | cons a' l' => simp at hl
  | cons a l ih =>
    cases b' with
    | nil => simp at hl
    | cons a' l' =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
      rw [toNatBE_cons, toNatBE_cons, hl] at h
      have h1 := toNatBE_lt l
      have h2 := toNatBE_lt l'
      rw [hl] at h1
      have hB : 0 < 256 ^ l'.length := by positivity
      have hd := congrArg (· / 256 ^ l'.length) h
      have hm := congrArg (· % 256 ^ l'.length) h
      simp only [Nat.mul_comm _ (256 ^ l'.length), Nat.mul_add_div hB, Nat.div_eq_of_lt h1,
        Nat.div_eq_of_lt h2, Nat.add_zero, Nat.mul_add_mod, Nat.mod_eq_of_lt h1,
        Nat.mod_eq_of_lt h2] at hd hm
      rw [UInt8.toNat_inj.mp hd, ih hl hm]

theorem bytes32_length (x : ℕ) : (bytes32 x).length = 32 := by simp [bytes32]

theorem toNatBE_bytes32 (x : ℕ) : toNatBE (bytes32 x) = x % 2 ^ 256 := by
  have key : ∀ k, toNatBE ((List.range k).reverse.map fun i => (x / 256 ^ i % 256).toUInt8) =
      x % 256 ^ k := by
    intro k
    induction k with
    | zero => simp [toNatBE, Nat.mod_one]
    | succ k ih =>
      rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append,
        List.map_cons, toNatBE_cons, ih, Nat.mod_pow_succ]
      simp only [List.length_map, List.length_reverse, List.length_range]
      have hb : (x / 256 ^ k % 256).toUInt8.toNat = x / 256 ^ k % 256 := by
        simp [Nat.toUInt8]
      rw [hb]
      ring
  unfold bytes32
  rw [key 32]
  norm_num

/-- `bytes(int(b)) = b` for 32 bytes. -/
theorem bytes32_toNatBE {b : Bytes} (h : b.length = 32) : bytes32 (toNatBE b) = b := by
  refine toNatBE_injective (by rw [bytes32_length, h]) ?_
  rw [toNatBE_bytes32]
  refine Nat.mod_eq_of_lt ?_
  have h2 := toNatBE_lt b
  rw [h] at h2
  have e : (256 : ℕ) ^ 32 = 2 ^ 256 := by norm_num
  rwa [e] at h2

theorem p_lt : p < 2 ^ 256 := by norm_num [p]

/-- `bytes ∘ int` is injective on field elements. -/
theorem bytes32_val_injective {a b : F} (h : bytes32 a.val = bytes32 b.val) : a = b := by
  have h2 := congrArg toNatBE h
  rw [toNatBE_bytes32, toNatBE_bytes32, Nat.mod_eq_of_lt ((ZMod.val_lt a).trans p_lt),
    Nat.mod_eq_of_lt ((ZMod.val_lt b).trans p_lt)] at h2
  exact ZMod.val_injective p h2

/-! ## The randomizer's hash input -/

/-- The bytes the randomizer hashes: `r₀ ‖ pk₀ ‖ m₀ ‖ … ‖ rᵢ ‖ pkᵢ ‖ mᵢ`. -/
def randomizerInput (its : List (Item Bytes Bytes)) : Bytes :=
  its.flatMap fun it => it.1 ++ it.2.1 ++ it.2.2

theorem randomizer_eq (its : List (Item Bytes Bytes)) :
    randomizer its = (toNatBE (taggedHash "BIP0458/randomizer" (randomizerInput its)) : ZMod n) :=
  rfl

/-- An item with a 32-byte nonce, public key and message, as BIP458 requires. -/
def Item32 (it : Item Bytes Bytes) : Prop :=
  it.1.length = 32 ∧ it.2.1.length = 32 ∧ it.2.2.length = 32

/-- **The randomizer's hash input determines the item list**, for items with
32-byte fields. -/
theorem randomizerInput_injective {its its' : List (Item Bytes Bytes)}
    (h : ∀ it ∈ its, Item32 it) (h' : ∀ it ∈ its', Item32 it)
    (heq : randomizerInput its = randomizerInput its') : its = its' := by
  induction its generalizing its' with
  | nil =>
    cases its' with
    | nil => rfl
    | cons b l' =>
      obtain ⟨h1, h2, h3⟩ := h' b (by simp)
      have hl := congrArg List.length heq
      simp only [randomizerInput, List.flatMap_nil, List.flatMap_cons, List.length_nil,
        List.length_append, h1, h2, h3] at hl
      omega
  | cons a l ih =>
    obtain ⟨a1, a2, a3⟩ := h a (by simp)
    cases its' with
    | nil =>
      have hl := congrArg List.length heq
      simp only [randomizerInput, List.flatMap_nil, List.flatMap_cons, List.length_nil,
        List.length_append, a1, a2, a3] at hl
      omega
    | cons b l' =>
      obtain ⟨b1, b2, b3⟩ := h' b (by simp)
      simp only [randomizerInput, List.flatMap_cons] at heq
      obtain ⟨hab, hrest⟩ := List.append_inj heq (by simp [a1, a2, a3, b1, b2, b3])
      obtain ⟨h12, h3⟩ := List.append_inj hab (by simp [a1, a2, b1, b2])
      obtain ⟨h1, h2⟩ := List.append_inj h12 (by rw [a1, b1])
      have hab' : a = b := Prod.ext h1 (Prod.ext h2 h3)
      rw [hab', ih (fun it hit => h it (List.mem_cons_of_mem _ hit))
        (fun it hit => h' it (List.mem_cons_of_mem _ hit)) hrest]

/-- The item that is hashed for a nonce and a public key given as field
elements: `(bytes(r), bytes(pk), m)`. -/
def encodeItem (it : Item F Bytes) : Item Bytes Bytes :=
  (bytes32 it.1.val, bytes32 it.2.1.val, it.2.2)

theorem randomizerF_eq (its : List (Item F Bytes)) :
    randomizerF its = randomizer (its.map encodeItem) := rfl

theorem encodeItem_injective : Function.Injective encodeItem := by
  intro a b h
  simp only [encodeItem, Prod.mk.injEq] at h
  exact Prod.ext (bytes32_val_injective h.1) (Prod.ext (bytes32_val_injective h.2.1) h.2.2)

/-- **The hash input of the model's randomizer determines the item list**, for
32-byte messages. -/
theorem randomizerF_input_injective {its its' : List (Item F Bytes)}
    (h : ∀ it ∈ its, it.2.2.length = 32) (h' : ∀ it ∈ its', it.2.2.length = 32)
    (heq : randomizerInput (its.map encodeItem) = randomizerInput (its'.map encodeItem)) :
    its = its' := by
  refine List.map_injective_iff.mpr encodeItem_injective (randomizerInput_injective ?_ ?_ heq)
  · intro it hit
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hit
    exact ⟨bytes32_length _, bytes32_length _, h a ha⟩
  · intro it hit
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hit
    exact ⟨bytes32_length _, bytes32_length _, h' a ha⟩

/-! ## The verifier on bytes -/

/-- The parsing, length checks and range checks of
`VerifyAggregate(aggsig, pm_aggd)`: the aggregate signature and the `(pk, m)`
pairs as inputs of the model, or `none` where BIP458 fails before its final
check. -/
def decodeVerify (aggsig : Bytes) (pm : List (Bytes × Bytes)) :
    Option (AggSig n F × List (F × Bytes)) :=
  let u := pm.length
  let rs := chunks32 aggsig u
  let s := toNatBE (aggsig.drop (32 * u))
  if aggsig.length == 32 * (u + 1) && pm.all (fun x => is32 x.1 && is32 x.2) &&
      pm.all (fun x => decide (toNatBE x.1 < p)) && rs.all (fun r => decide (toNatBE r < p)) &&
      decide (s < n) then
    some (⟨rs.map fun r => (toNatBE r : F), (s : ZMod n)⟩,
      pm.map fun x => ((toNatBE x.1 : F), x.2))
  else none

/-- **The verifier on bytes is the model's verifier on the decoded input.** -/
theorem verifyAggregateBytes_eq (aggsig : Bytes) (pm : List (Bytes × Bytes)) :
    verifyAggregateBytes aggsig pm =
      (decodeVerify aggsig pm).any fun x =>
        verifyAggregate secp256k1 challenge randomizerF x.1 x.2 := by
  unfold verifyAggregateBytes decodeVerify
  dsimp only
  split_ifs with h
  · simp only [Option.any_some]
    rw [h, Bool.true_and]
  · simp only [Option.any_none]
    rw [Bool.not_eq_true] at h
    rw [h, Bool.false_and]

/-- A field element below `p` decodes back to its 32 bytes. -/
theorem bytes32_val_toNatBE {b : Bytes} (h : b.length = 32) (hp : toNatBE b < p) :
    bytes32 ((toNatBE b : F)).val = b := by
  rw [ZMod.val_natCast_of_lt hp, bytes32_toNatBE h]

/-- **The randomizer of a decoded item hashes the bytes of the input.** -/
theorem encodeItem_decode {r pk m : Bytes} (hr : r.length = 32) (hrp : toNatBE r < p)
    (hpk : pk.length = 32) (hpkp : toNatBE pk < p) :
    encodeItem ((toNatBE r : F), (toNatBE pk : F), m) = (r, pk, m) := by
  simp only [encodeItem, bytes32_val_toNatBE hr hrp, bytes32_val_toNatBE hpk hpkp]

/-- What a successful `decodeVerify` says about its input. -/
theorem decodeVerify_some {aggsig : Bytes} {pm : List (Bytes × Bytes)}
    {x : AggSig n F × List (F × Bytes)} (h : decodeVerify aggsig pm = some x) :
    x = (⟨(chunks32 aggsig pm.length).map fun r => (toNatBE r : F),
        (toNatBE (aggsig.drop (32 * pm.length)) : ZMod n)⟩,
        pm.map fun e => ((toNatBE e.1 : F), e.2)) ∧
      aggsig.length = 32 * (pm.length + 1) ∧
      (∀ e ∈ pm, e.1.length = 32 ∧ e.2.length = 32 ∧ toNatBE e.1 < p) ∧
      (∀ r ∈ chunks32 aggsig pm.length, toNatBE r < p) ∧
      toNatBE (aggsig.drop (32 * pm.length)) < n := by
  unfold decodeVerify at h
  dsimp only at h
  split_ifs at h with hc
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, is32, beq_iff_eq] at hc
  obtain ⟨⟨⟨⟨hlen, h32⟩, hlt⟩, hrs⟩, hs⟩ := hc
  exact ⟨(Option.some.inj h).symm, hlen, fun e he => ⟨(h32 e he).1, (h32 e he).2, hlt e he⟩,
    hrs, hs⟩

theorem chunks32_length {b : Bytes} {v : ℕ} (h : 32 * (v + 1) ≤ b.length) :
    ∀ c ∈ chunks32 b v, c.length = 32 := by
  intro c hc
  simp only [chunks32, List.mem_map, List.mem_range] at hc
  obtain ⟨i, hi, rfl⟩ := hc
  simp only [List.length_take, List.length_drop]
  omega

theorem encodeItem_items {pm : List (Bytes × Bytes)} {rs : List Bytes}
    (hpm : ∀ e ∈ pm, e.1.length = 32 ∧ toNatBE e.1 < p)
    (hrs : ∀ r ∈ rs, r.length = 32 ∧ toNatBE r < p) :
    (items (pm.map fun e => ((toNatBE e.1 : F), e.2)) (rs.map fun r => (toNatBE r : F))).map
      encodeItem = items pm rs := by
  induction pm generalizing rs with
  | nil => simp [items]
  | cons a l ih =>
    cases rs with
    | nil => simp [items]
    | cons r rs' =>
      obtain ⟨la, pa⟩ := hpm a (by simp)
      obtain ⟨lr, pr⟩ := hrs r (by simp)
      simp only [items, List.map_cons, List.zipWith_cons_cons] at ih ⊢
      rw [encodeItem_decode lr pr la pa, ih (fun e he => hpm e (List.mem_cons_of_mem _ he))
        (fun e he => hrs e (List.mem_cons_of_mem _ he))]

/-- **The randomizers of the decoded input hash the bytes of the input**: for a
decoded input, the model's randomizer of the first `i` items is
`int(hash_BIP0458/randomizer(r₀ ‖ pk₀ ‖ m₀ ‖ …)) mod n` on the first `i` nonces,
public keys and messages as they appear in `aggsig` and `pm`. -/
theorem decodeVerify_randomizer {aggsig : Bytes} {pm : List (Bytes × Bytes)}
    {x : AggSig n F × List (F × Bytes)} (h : decodeVerify aggsig pm = some x) (i : ℕ) :
    randomizerF ((items x.2 x.1.rs).take i) =
      randomizer ((items pm (chunks32 aggsig pm.length)).take i) := by
  obtain ⟨rfl, hlen, hpm, hrs, -⟩ := decodeVerify_some h
  dsimp only
  rw [randomizerF_eq, List.map_take, encodeItem_items (fun e he => ⟨(hpm e he).1, (hpm e he).2.2⟩)
    (fun r hr => ⟨chunks32_length hlen.ge r hr, hrs r hr⟩)]

/-- **Decoding keeps different `(pk, m)` lists apart.** Two inputs that pass
the checks and decode to the same `(pk, m)` pairs have the same `(pk, m)` pairs. -/
theorem decodeVerify_pm_injective {aggsig aggsig' : Bytes} {pm pm' : List (Bytes × Bytes)}
    {x x' : AggSig n F × List (F × Bytes)} (h : decodeVerify aggsig pm = some x)
    (h' : decodeVerify aggsig' pm' = some x') (heq : x.2 = x'.2) : pm = pm' := by
  obtain ⟨rfl, -, c1, -, -⟩ := decodeVerify_some h
  obtain ⟨rfl, -, c2, -, -⟩ := decodeVerify_some h'
  dsimp only at heq
  clear h h'
  induction pm generalizing pm' with
  | nil =>
    cases pm' with
    | nil => rfl
    | cons b l' => simp at heq
  | cons a l ih =>
    cases pm' with
    | nil => simp at heq
    | cons b l' =>
      simp only [List.map_cons, List.cons.injEq, Prod.mk.injEq] at heq
      obtain ⟨⟨hpk, hm⟩, hrest⟩ := heq
      obtain ⟨la, -, pa⟩ := c1 a (by simp)
      obtain ⟨lb, -, pb⟩ := c2 b (by simp)
      have hnat : toNatBE a.1 = toNatBE b.1 := by
        have := congrArg ZMod.val hpk
        rwa [ZMod.val_natCast_of_lt pa, ZMod.val_natCast_of_lt pb] at this
      have hab : a = b := Prod.ext (toNatBE_injective (by rw [la, lb]) hnat) hm
      rw [hab, ih (fun e he => c1 e (List.mem_cons_of_mem _ he)) hrest
        (fun e he => c2 e (List.mem_cons_of_mem _ he))]

end Halfagg.Vectors
