import Halfagg.Encoding
import Halfagg.Unforgeability
import Halfagg.Knowledge
import Halfagg.UnforgeabilityTight
import Halfagg.Binding
import Halfagg.UnforgeabilityHashed
import Halfagg.BindingHashed

/-!
# The theorems for 32-byte nonces, public keys and messages

BIP458 hashes and compares bytes. The security theorems hold for every type `X`
of x-only encodings and every message type `M`. Here both are the 32-byte
arrays `B32`, and the hashes are BIP458's and BIP340's.

* `secp256k1X` is secp256k1 with `bytes(x(P))` as the x-only encoding. Its
  `lift_x` fails for an array that is not below `p`.
* `challengeX` is `int(hash_BIP0340/challenge(r ‖ pk ‖ m)) mod n`.
* `randomizerX` is BIP458's randomizer hash on 32-byte items, and
  `randomizerX_eq_red256` says that it is a 256-bit hash output
  (`randHash256`) reduced by `red256`: SHA-256 has 32 bytes of output
  (`length_sha256`).
* `bytes_halfagg_unforgeable`, `bytes_halfagg_knowledge`,
  `bytes_halfagg_dlog_tight` and `bytes_halfagg_binding` are the theorems for
  this instance.
* `bytes_halfagg_dlog_tight_256` and `bytes_halfagg_binding_256` are the last
  two with the challenge hash as a random oracle with 256-bit outputs, which the
  adversary sees and the scheme reduces modulo `n`.
-/

open OracleSpec OracleComp AlgebraicGroupModel.Interaction
open scoped ENNReal

namespace Halfagg.Security

open Taproot Taproot.Secp256k1 Taproot.BIP340 Taproot.BIP340Security Taproot.BIP340Vectors
  Halfagg.Vectors

attribute [local instance] smulVal

/-- 32-byte arrays. -/
abbrev B32 := {b : Bytes // b.length = 32}

instance : DecidableEq B32 := inferInstance

noncomputable instance : Fintype B32 :=
  haveI : Finite B32 := (List.finite_length_eq UInt8 32).to_subtype
  Fintype.ofFinite _

instance : Inhabited B32 := ⟨⟨List.replicate 32 0, List.length_replicate⟩⟩

/-- **secp256k1 with x-coordinates as 32-byte arrays**: the x-only encoding of
a point is `bytes(x(P))`, and `lift_x` fails for an array that is not below
`p`. -/
def secp256k1X : Curve n Point B32 where
  G := G
  G_ne_zero := secp256k1F.G_ne_zero
  order_G := OrderG.n_smul_G
  x P := ⟨bytes32 (xCoord P).val, bytes32_length _⟩
  hasEvenY := hasEvenY
  liftX b := if toNatBE b.1 < p then liftX (toNatBE b.1 : F) else none
  x_neg P := Subtype.ext (by simp only [Secp256k1.x_neg])
  hasEvenY_neg := hasEvenY_neg
  liftX_x P hP he := by
    have hv : (xCoord P).val < p := ZMod.val_lt _
    simp only [toNatBE_bytes32, Nat.mod_eq_of_lt (hv.trans p_lt), hv, ↓reduceIte,
      ZMod.natCast_zmod_val]
    exact Secp256k1.liftX_x P hP he
  liftX_spec r P h := by
    split_ifs at h with hr
    obtain ⟨h1, h2, h3⟩ := Secp256k1.liftX_spec _ P h
    refine ⟨h1, h2, Subtype.ext ?_⟩
    change bytes32 (xCoord P).val = r.1
    rw [h3, ZMod.val_natCast_of_lt hr]
    exact bytes32_toNatBE r.2

/-- `int(hash_BIP0340/challenge(r ‖ pk ‖ m)) mod n` on 32-byte arrays. -/
def challengeX (r pk m : B32) : ZMod n :=
  (toNatBE (taggedHash "BIP0340/challenge" (r.1 ++ pk.1 ++ m.1)) : ZMod n)

/-- The bytes of an item of 32-byte arrays. -/
def itemBytes (it : Item B32 B32) : Item Bytes Bytes := (it.1.1, it.2.1.1, it.2.2.1)

/-- BIP458's randomizer hash on items of 32-byte arrays:
`int(hash_BIP0458/randomizer(r₀ ‖ pk₀ ‖ m₀ ‖ … ‖ rᵢ ‖ pkᵢ ‖ mᵢ)) mod n`. -/
def randomizerX (its : List (Item B32 B32)) : ZMod n := randomizer (its.map itemBytes)

/-! ## The randomizer hash is a 256-bit output reduced modulo `n` -/

theorem size_sha256Block (h : Array UInt32) (blk : Array UInt8) (off : ℕ) :
    (sha256Block h blk off).size = 8 := by
  unfold sha256Block
  simp

theorem foldl_invariant {α β : Type} (P : β → Prop) (f : β → α → β)
    (hf : ∀ b a, P b → P (f b a)) : ∀ (l : List α) (b : β), P b → P (l.foldl f b)
  | [], _, hb => hb
  | a :: l, b, hb => foldl_invariant P f hf l (f b a) (hf b a hb)

/-- **SHA-256 has 32 bytes of output.** -/
theorem length_sha256 (msg : Bytes) : (sha256 msg).length = 32 := by
  unfold sha256
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', List.forIn_pure_yield_eq_foldl]
  simp only [Id.run, bind, pure]
  have hsize : ∀ l : List ℕ, (List.foldl
      (fun b a => sha256Block b (List.toArray (sha256Pad msg)) (64 * a)) sha256H0 l).size = 8 :=
    fun l => foldl_invariant (fun h : Array UInt32 => h.size = 8) _
      (fun b a _ => size_sha256Block _ _ _) l _ rfl
  rw [List.length_flatMap]
  simp [hsize]

theorem length_taggedHash (tag : String) (msg : Bytes) : (taggedHash tag msg).length = 32 :=
  length_sha256 _

/-- A 32-byte array as a 256-bit value. -/
def int256 (b : Bytes) (h : b.length = 32) : Fin (2 ^ 256) :=
  ⟨toNatBE b, by
    have := toNatBE_lt b
    rw [h] at this
    exact lt_of_lt_of_eq this (by norm_num)⟩

/-- `hash_BIP0458/randomizer` with its 256-bit output, on items of 32-byte
arrays. -/
def randHash256 (its : List (Item B32 B32)) : Fin (2 ^ 256) :=
  int256 (taggedHash "BIP0458/randomizer" (randomizerInput (its.map itemBytes)))
    (length_taggedHash _ _)

/-- **BIP458's randomizer is a 256-bit hash output reduced modulo `n`**: the
`red256` of the security theorems for secp256k1. -/
theorem randomizerX_eq_red256 (its : List (Item B32 B32)) :
    randomizerX its = red256 (randHash256 its) :=
  rfl

/-- The hash input of `randHash256` determines the item list. -/
theorem randHash256_input_injective {its its' : List (Item B32 B32)}
    (h : randomizerInput (its.map itemBytes) = randomizerInput (its'.map itemBytes)) :
    its = its' := by
  have hinj : Function.Injective itemBytes := fun a b hab => by
    simp only [itemBytes, Prod.mk.injEq] at hab
    exact Prod.ext (Subtype.ext hab.1) (Prod.ext (Subtype.ext hab.2.1) (Subtype.ext hab.2.2))
  refine List.map_injective_iff.mpr hinj (randomizerInput_injective ?_ ?_ h)
  · intro it hit
    obtain ⟨a, -, rfl⟩ := List.mem_map.mp hit
    exact ⟨a.1.2, a.2.1.2, a.2.2.2⟩
  · intro it hit
    obtain ⟨a, -, rfl⟩ := List.mem_map.mp hit
    exact ⟨a.1.2, a.2.1.2, a.2.2.2⟩

/-! ## The theorems for this instance -/

/-- The curve hypothesis of the theorems: `bytes(0)` does not lift. -/
theorem liftX_x_zero_X : secp256k1X.liftX (secp256k1X.x 0) = none := by
  have h0 : toNatBE (secp256k1X.x 0).1 = 0 := by
    change toNatBE (bytes32 (xCoord (0 : Point)).val) = 0
    rw [toNatBE_bytes32]
    simp [xCoord]
  change (if toNatBE (secp256k1X.x 0).1 < p then liftX (toNatBE (secp256k1X.x 0).1 : F)
    else none) = none
  rw [h0]
  simp [Halfagg.Secp256k1.liftX_zero]

/-- **Half-aggregation on 32-byte arrays is as secure as BIP340.**
`halfagg_unforgeable` for secp256k1 with 32-byte nonces, public keys and
messages, BIP340's challenge hash and a 256-bit randomizer hash that is reduced
modulo `n`. -/
theorem bytes_halfagg_unforgeable [NonceGen n B32]
    (F : AlgForger n (Fin (2 ^ 256)) Point B32 B32) (q : ℕ)
    (hq : ∀ input, (F.main input).IsQueryBoundP (fun r => isRand r.value.data) q) :
    aggAdvantage secp256k1X challengeX red256 (erase secp256k1X F) ≤
      SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp
        (reduction secp256k1X challengeX red256 F) +
        (q + 1 : ℝ≥0∞) * (2 / ((2 ^ 256 : ℕ) : ℝ≥0∞)) :=
  halfagg_unforgeable secp256k1X challengeX red256 liftX_x_zero_X F q hq _ secp256k1_redBound

/-- `halfagg_knowledge` for the same instance. -/
theorem bytes_halfagg_knowledge [NonceGen n B32]
    (F : AlgForger n (Fin (2 ^ 256)) Point B32 B32) (q : ℕ)
    (hq : ∀ input, (F.main input).IsQueryBoundP (fun r => isRand r.value.data) q) :
    aggVerifyAdvantage secp256k1X challengeX red256 (erase secp256k1X F) ≤
      extractAdvantage secp256k1X challengeX red256 F +
        (q + 1 : ℝ≥0∞) * (2 / ((2 ^ 256 : ℕ) : ℝ≥0∞)) :=
  halfagg_knowledge secp256k1X challengeX red256 liftX_x_zero_X F q hq _ secp256k1_redBound

-- Uniform nonces, as in `Halfagg/SecurityROM.lean`.
attribute [local instance] NonceGen.uniform in
/-- `halfagg_dlog_tight` for the same instance, with BIP340's challenge hash as
a random oracle on `(m, (r, pk))`. -/
theorem bytes_halfagg_dlog_tight [SampleableType (B32 × (B32 × B32) → ZMod n)]
    (F : RomForger n (Fin (2 ^ 256)) Point B32 B32) (q qH qS ℓ : ℕ)
    (hq : ∀ input, (F.main input).IsQueryBoundP (fun t => isRandCall t) q)
    (hH : ∀ input, (F.main input).IsQueryBoundP (fun t => isChalCall t) qH)
    (hS : ∀ input, (F.main input).IsQueryBoundP (fun t => isSignCall t) qS)
    (hL : ∀ input, ∀ out ∈ support (F.main input), out.value.data.ms.length ≤ ℓ)
    (hE : ∀ input, ExplainsNonces secp256k1X (F.main input) []) :
    aggAdvantageROM secp256k1X red256 F ≤
      Pr{let x ← dlogExperiment secp256k1X (dlogOfKeyRecovery secp256k1X
          (keySolver secp256k1X red256 F))}[x = true] +
        (qS : ℝ≥0∞) * (qS + (qH + qS + ℓ + 1 : ℕ)) * (2 / ((n - 1 : ℕ) : ℝ≥0∞)) +
        (q + 1 : ℝ≥0∞) * (2 / ((2 ^ 256 : ℕ) : ℝ≥0∞)) + (qH + 1 : ℝ≥0∞) / n :=
  halfagg_dlog_tight secp256k1X red256 liftX_x_zero_X F q qH qS ℓ hq hH hS hL hE _
    secp256k1_redBound

/-- `halfagg_binding` for the same instance. -/
theorem bytes_halfagg_binding [SampleableType (B32 × (B32 × B32) → ZMod n)]
    (A : BindAdversary n (Fin (2 ^ 256)) B32 B32) (qC qZ ℓ : ℕ)
    (hC : A.main.IsQueryBoundP (fun t => isChalB t) qC)
    (hZ : A.main.IsQueryBoundP (fun t => isRandB t) qZ)
    (hL : ∀ out ∈ support A.main, out.1.rs.length ≤ ℓ) :
    bindAdvantage secp256k1X red256 A ≤
      (((qC + 2 * ℓ) * (qC + 2 * ℓ) : ℕ) : ℝ≥0∞) / n +
        (((qZ + 2 * ℓ) * (qZ + 2 * ℓ) : ℕ) : ℝ≥0∞) * (2 / ((2 ^ 256 : ℕ) : ℝ≥0∞)) :=
  halfagg_binding secp256k1X red256 secp256k1_primeOrder A qC qZ ℓ hC hZ hL _ secp256k1_redBound

-- Uniform nonces, as in `Halfagg/SecurityROM.lean`.
attribute [local instance] NonceGen.uniform in
/-- `halfagg_dlog_tight_hashed` for the same instance: BIP340's challenge hash
is a random oracle with 256-bit outputs, which the forger sees and the scheme
reduces modulo `n`. -/
theorem bytes_halfagg_dlog_tight_256 [SampleableType (B32 × (B32 × B32) → Fin (2 ^ 256))]
    [SampleableType (B32 × (B32 × B32) → ZMod n)]
    (F : RomForgerH n (Fin (2 ^ 256)) (Fin (2 ^ 256)) Point B32 B32) (q qH qS ℓ : ℕ)
    (hq : ∀ input, (F.main input).IsQueryBoundP (fun t => isRandCall t) q)
    (hH : ∀ input, (F.main input).IsQueryBoundP (fun t => isChalCall t) qH)
    (hS : ∀ input, (F.main input).IsQueryBoundP (fun t => isSignCall t) qS)
    (hL : ∀ input, ∀ out ∈ support (F.main input), out.value.data.ms.length ≤ ℓ)
    (hE : ∀ input, ExplainsNoncesH secp256k1X (F.main input) []) :
    aggAdvantageROMH secp256k1X red256 red256 F ≤
      Pr{let x ← dlogExperiment secp256k1X (dlogOfKeyRecovery secp256k1X
          (keySolver secp256k1X red256 (F.viaRep rep256)))}[x = true] +
        (qS : ℝ≥0∞) * (qS + (qH + qS + ℓ + 1 : ℕ)) * (2 / ((n - 1 : ℕ) : ℝ≥0∞)) +
        (q + 1 : ℝ≥0∞) * (2 / ((2 ^ 256 : ℕ) : ℝ≥0∞)) + (qH + 1 : ℝ≥0∞) / n +
        ((qH + qS + ℓ : ℕ) : ℝ≥0∞) * (1 / 2 ^ 127) :=
  halfagg_dlog_tight_hashed secp256k1X red256 red256 liftX_x_zero_X rep256 red256_rep256 F
    q qH qS ℓ hq hH hS hL hE _ secp256k1_redBound _ secp256k1_repBound

/-- `halfagg_binding_hashed` for the same instance. -/
theorem bytes_halfagg_binding_256 [SampleableType (B32 × (B32 × B32) → Fin (2 ^ 256))]
    [SampleableType (B32 × (B32 × B32) → ZMod n)]
    (A : BindAdversaryH n (Fin (2 ^ 256)) (Fin (2 ^ 256)) B32 B32) (qC qZ ℓ : ℕ)
    (hC : A.main.IsQueryBoundP (fun t => isChalB t) qC)
    (hZ : A.main.IsQueryBoundP (fun t => isRandB t) qZ)
    (hL : ∀ out ∈ support A.main, out.1.rs.length ≤ ℓ) :
    bindAdvantageH secp256k1X red256 red256 A ≤
      (((qC + 2 * ℓ) * (qC + 2 * ℓ) : ℕ) : ℝ≥0∞) / n +
        (((qZ + 2 * ℓ) * (qZ + 2 * ℓ) : ℕ) : ℝ≥0∞) * (2 / ((2 ^ 256 : ℕ) : ℝ≥0∞)) +
        ((qC + 2 * ℓ : ℕ) : ℝ≥0∞) * (1 / 2 ^ 127) :=
  halfagg_binding_hashed secp256k1X red256 red256 secp256k1_primeOrder rep256 red256_rep256 A
    qC qZ ℓ hC hZ hL _ secp256k1_redBound _ secp256k1_repBound

end Halfagg.Security

/-! ## `VerifyAggregate` does not depend on the encoding of x-coordinates -/

namespace Halfagg

open Taproot Taproot.Curve

section Transfer

variable {n : ℕ} [Fact n.Prime] {E X X' M M' : Type} [AddCommGroup E] [DecidableEq E]
  (C : Curve n E X) (C' : Curve n E X') (challenge : X → X → M → ZMod n)
  (challenge' : X' → X' → M' → ZMod n) (fx : X → X') (fm : M → M')

omit [Fact n.Prime] [AddCommGroup E] [DecidableEq E] in
theorem items_map_enc (pm : List (X × M)) (rs : List X) :
    items (pm.map fun x => (fx x.1, fm x.2)) (rs.map fx) =
      (items pm rs).map fun it => (fx it.1, fx it.2.1, fm it.2.2) := by
  induction pm generalizing rs with
  | nil => simp [items]
  | cons a l ih =>
    cases rs with
    | nil => simp [items]
    | cons r rs' =>
      simp only [items, List.map_cons, List.zipWith_cons_cons] at ih ⊢
      rw [ih]

/-- Two curve interfaces on the same group with the same generator, whose
`lift_x` and challenge hashes agree along maps `fx` of the x-only encodings and
`fm` of the messages, have the same verifier. -/
theorem verifyWith_map (hG : C'.G = C.G) (hl : ∀ x, C'.liftX (fx x) = C.liftX x)
    (zf : ℕ → ZMod n) (agg : AggSig n X) (pm : List (X × M))
    (hc : ∀ it ∈ items pm agg.rs,
      challenge' (fx it.1) (fx it.2.1) (fm it.2.2) = challenge it.1 it.2.1 it.2.2) :
    verifyWith C' challenge' zf ⟨agg.rs.map fx, agg.s⟩ (pm.map fun x => (fx x.1, fm x.2)) =
      verifyWith C challenge zf agg pm := by
  have hmul : C'.mulG agg.s = C.mulG agg.s := by
    rw [C'.mulG_eq_val_smul, C.mulG_eq_val_smul, hG]
  have hsum : isum (fun i it => (zf i).val • term C' challenge' it) 0
      ((items pm agg.rs).map fun it => (fx it.1, fx it.2.1, fm it.2.2)) =
      isum (fun i it => (zf i).val • term C challenge it) 0 (items pm agg.rs) := by
    rw [isum_map]
    refine isum_congr fun i it hit _ _ => ?_
    simp only [term, hl, hc it hit]
  simp only [verifyWith, items_map_enc, List.length_map, List.all_map, hmul, hsum]
  congr 3
  funext it
  simp only [Function.comp, lifts, hl]

omit [Fact n.Prime] [AddCommGroup E] [DecidableEq E] in
/-- An item has the public key and the message of one of the pairs. -/
theorem mem_items {pm : List (X × M)} {rs : List X} {it : Item X M} (h : it ∈ items pm rs) :
    ∃ x ∈ pm, it.2.1 = x.1 ∧ it.2.2 = x.2 := by
  induction pm generalizing rs with
  | nil => simp [items] at h
  | cons a l ih =>
    cases rs with
    | nil => simp [items] at h
    | cons r rs' =>
      simp only [items, List.zipWith_cons_cons, List.mem_cons] at h
      rcases h with rfl | h
      · exact ⟨a, by simp, rfl, rfl⟩
      · obtain ⟨x, hx, h1⟩ := ih h
        exact ⟨x, List.mem_cons_of_mem _ hx, h1⟩

omit [Fact n.Prime] [AddCommGroup E] [DecidableEq E] in
/-- The nonces and the `(pk, m)` pairs of the items of lists of equal length. -/
theorem map_items {pm : List (X × M)} {rs : List X} (h : rs.length = pm.length) :
    (items pm rs).map (·.1) = rs ∧ (items pm rs).map (·.2) = pm := by
  induction pm generalizing rs with
  | nil => cases rs with
    | nil => simp [items]
    | cons r rs' => simp at h
  | cons a l ih =>
    cases rs with
    | nil => simp at h
    | cons r rs' =>
      obtain ⟨h1, h2⟩ := ih (rs := rs') (by simpa using h)
      simp only [items, List.zipWith_cons_cons, List.map_cons] at h1 h2 ⊢
      exact ⟨by rw [h1], by rw [h2]⟩

end Transfer

end Halfagg

/-! ## `VerifyAggregate` on bytes is the verifier of this instance -/

namespace Halfagg.Security

open Taproot Taproot.Secp256k1 Taproot.BIP340 Taproot.BIP340Vectors Halfagg.Vectors

/-- A byte array as a 32-byte array, if it has 32 bytes. -/
def to32 (b : Bytes) : B32 := if h : b.length = 32 then ⟨b, h⟩ else default

theorem to32_val {b : Bytes} (h : b.length = 32) : (to32 b).1 = b := by
  simp only [to32, h, ↓reduceDIte]

/-- A field element as its 32 bytes. -/
def encX (x : F) : B32 := ⟨bytes32 x.val, bytes32_length _⟩

theorem liftX_encX (x : F) : secp256k1X.liftX (encX x) = secp256k1F.liftX x := by
  have hv : x.val < p := ZMod.val_lt x
  change (if toNatBE (bytes32 x.val) < p then liftX (toNatBE (bytes32 x.val) : F) else none) =
    secp256k1F.liftX x
  rw [toNatBE_bytes32, Nat.mod_eq_of_lt (hv.trans p_lt), ZMod.natCast_zmod_val, secp256k1F_liftX]
  simp only [hv, ↓reduceIte]

theorem challengeX_encX (r pk : F) {m : Bytes} (hm : m.length = 32) :
    challengeX (encX r) (encX pk) (to32 m) = challenge r pk m := by
  simp only [challengeX, challenge, encX, to32_val hm]

/-- The verifier of the instance with 32-byte arrays is the verifier with field
elements, on the encodings. -/
theorem verifyAggregate_X (agg : AggSig n F) (pm : List (F × Bytes))
    (hm : ∀ x ∈ pm, x.2.length = 32) :
    verifyAggregate secp256k1X challengeX randomizerX ⟨agg.rs.map encX, agg.s⟩
        (pm.map fun x => (encX x.1, to32 x.2)) =
      verifyAggregate secp256k1F challenge randomizerF agg pm := by
  have hits : ∀ it ∈ items pm agg.rs, it.2.2.length = 32 := by
    intro it hit
    obtain ⟨x, hx, -, h2⟩ := mem_items hit
    rw [h2]
    exact hm x hx
  simp only [verifyAggregate]
  rw [verifyWith_map secp256k1F secp256k1X challenge challengeX encX to32 rfl liftX_encX _ agg pm
    fun it hit => challengeX_encX _ _ (hits it hit), items_map_enc encX to32]
  congr 1
  funext i
  simp only [z]
  split_ifs
  · rfl
  · rw [← List.map_take, randomizerX, randomizerF_eq, List.map_map]
    refine congrArg randomizer (List.map_congr_left fun it hit => ?_)
    simp only [Function.comp, itemBytes, encodeItem, encX,
      to32_val (hits it (List.mem_of_mem_take hit))]

/-- The parsing and the checks of `VerifyAggregate`, with the nonces, public
keys and messages as 32-byte arrays. -/
def decodeX (aggsig : Bytes) (pm : List (Bytes × Bytes)) :
    Option (AggSig n B32 × List (B32 × B32)) :=
  (decodeVerify aggsig pm).map fun x =>
    (⟨x.1.rs.map encX, x.1.s⟩, x.2.map fun y => (encX y.1, to32 y.2))

/-- **`VerifyAggregate` on bytes is the verifier of the instance with 32-byte
arrays**, after the parsing and the checks. -/
theorem verifyAggregateBytes_eq_X (aggsig : Bytes) (pm : List (Bytes × Bytes)) :
    verifyAggregateBytes aggsig pm =
      (decodeX aggsig pm).any fun x =>
        verifyAggregate secp256k1X challengeX randomizerX x.1 x.2 := by
  rw [verifyAggregateBytes_eq]
  unfold decodeX
  cases h : decodeVerify aggsig pm with
  | none => rfl
  | some x =>
    obtain ⟨hx, -, hpm, -, -⟩ := decodeVerify_some h
    simp only [Option.map_some, Option.any_some]
    refine (verifyAggregate_X x.1 x.2 fun y hy => ?_).symm
    rw [hx] at hy
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hy
    exact (hpm e he).2.1

/-- **The 32-byte arrays of the decoded input are the bytes of the input**: the
nonces are the 32-byte chunks of `aggsig`, and the public keys and messages are
those of `pm`. -/
theorem decodeX_bytes {aggsig : Bytes} {pm : List (Bytes × Bytes)}
    {x : AggSig n B32 × List (B32 × B32)} (h : decodeX aggsig pm = some x) :
    x.1.rs.map (·.1) = chunks32 aggsig pm.length ∧
      x.2.map (fun y => (y.1.1, y.2.1)) = pm ∧
      x.1.s = (toNatBE (aggsig.drop (32 * pm.length)) : ZMod n) := by
  unfold decodeX at h
  cases h' : decodeVerify aggsig pm with
  | none => rw [h'] at h; cases h
  | some x' =>
    rw [h', Option.map_some, Option.some.injEq] at h
    obtain ⟨hx, hlen, hpm, hrs, -⟩ := decodeVerify_some h'
    subst h hx
    refine ⟨?_, ?_, rfl⟩
    · simp only [List.map_map]
      conv_rhs => rw [← List.map_id (chunks32 aggsig pm.length)]
      refine List.map_congr_left fun r hr => ?_
      exact bytes32_val_toNatBE (chunks32_length hlen.ge r hr) (hrs r hr)
    · simp only [List.map_map]
      conv_rhs => rw [← List.map_id pm]
      refine List.map_congr_left fun e he => ?_
      exact Prod.ext (bytes32_val_toNatBE (hpm e he).1 (hpm e he).2.2) (to32_val (hpm e he).2.1)

/-- **With SHA-256 as the randomizer hash, the game's verifier is
`VerifyAggregate` on bytes.** For an input that passes the parsing and the
checks, the last two lines of `aggExperiment` on the decoded items, with the
randomizer oracle answered by `hash_BIP0458/randomizer`, compute
`verifyAggregateBytes` on the input and check that some item has the target key
and a message that was never signed. -/
theorem bytes_game_verifier {aggsig : Bytes} {pm : List (Bytes × Bytes)}
    {x : AggSig n B32 × List (B32 × B32)} (h : decodeX aggsig pm = some x) (pk : B32)
    (signed : B32 → Bool) :
    simulateQ (answerRand randHash256) (do
        let zs ← (List.range (items x.2 x.1.rs).length).mapM
          (zQuery red256 (items x.2 x.1.rs))
        return aggWins secp256k1X challengeX pk (items x.2 x.1.rs) x.1.s zs signed) =
      pure (verifyAggregateBytes aggsig pm &&
        (items x.2 x.1.rs).any fun it => decide (it.2.1 = pk) && !signed it.2.2) := by
  have hlen : x.1.rs.length = x.2.length := by
    obtain ⟨h1, h2, -⟩ := decodeX_bytes h
    have e1 := congrArg List.length h1
    have e2 := congrArg List.length h2
    simp only [List.length_map] at e1 e2
    rw [e1, e2]
    simp [chunks32]
  obtain ⟨h1, h2⟩ := map_items hlen
  rw [game_verifier, h1, h2, verifyAggregateBytes_eq_X, h]
  rfl

end Halfagg.Security
