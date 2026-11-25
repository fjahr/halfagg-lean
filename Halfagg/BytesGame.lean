import Halfagg.BytesSecurity
import Halfagg.Winnable

/-!
# The game with the forgery as bytes

In the game of `Halfagg/Security.lean` the forger outputs items and a scalar.
BIP458's `VerifyAggregate` gets `aggsig` and `pm_aggd`: byte arrays of any
length. Here the forger outputs those.

* `aggExperimentB` is the game for 32-byte arrays in which the adversary's
  forgery is a pair of byte arrays. The game parses it as `VerifyAggregate`
  does (`decodeX`), and a forgery that fails the parsing or the checks loses.
* `aggExperimentB_eq`: this is the game of `Halfagg/Security.lean` for the
  adversary that parses its forgery (`toStruct`).
* `serB F` is the byte adversary that runs an algebraic forger `F` and writes
  its forgery as bytes. Parsing gives `F` back (`toStruct_serB`), so the two
  have the same success probability.
* `bytesGame_halfagg_unforgeable` is `bytes_halfagg_unforgeable` in the game on
  bytes, and `bytesGame_winnable` says that this game can be won: a correct
  aggregate in bytes passes the parsing, the checks and `VerifyAggregate`.

The oracles are those of the game on 32-byte arrays: a randomizer query is a
list of items, and a signature comes as `(r, s)`.
-/

open OracleSpec OracleComp AlgebraicGroupModel.Interaction
open scoped ENNReal

namespace Halfagg.Security

open Taproot Taproot.Secp256k1 Taproot.BIP340 Taproot.BIP340Security Taproot.BIP340Vectors
  Halfagg.Vectors

attribute [local instance] smulVal

variable {H : Type}

/-- An adversary of the game on bytes. It gets the target public key as 32
bytes and has the oracles of the game. Its forgery is BIP458's `aggsig` and
`pm_aggd`: byte arrays of any length. -/
structure AggAdversaryB (H : Type) where
  main (pk : B32) : OracleComp (GameSpec n H B32 B32) (Bytes × List (Bytes × Bytes))

/-- **The game on bytes.** The adversary outputs `aggsig` and `pm_aggd`. The
game parses them as `VerifyAggregate` does. If that fails, the adversary loses.
Otherwise it wins as in `aggExperiment`: `VerifyAggregate` accepts, and some
pair has the target public key and a message that was never signed. -/
noncomputable def aggExperimentB [NonceGen n B32] (red : H → ZMod n) (A : AggAdversaryB H) :
    OracleComp (unifSpec + RandSpec H B32 B32) Bool := do
  let alg := bip340 (M := B32) secp256k1X challengeX (OracleComp (unifSpec + RandSpec H B32 B32))
  let (pk, sk) ← alg.keygen
  let ((aggsig, pm), log) ← alg.runWithSigningOracle pk sk (A.main pk)
  match decodeX aggsig pm with
  | none => return false
  | some x =>
    let zs ← (List.range (items x.2 x.1.rs).length).mapM (zQuery red (items x.2 x.1.rs))
    return aggWins secp256k1X challengeX pk (items x.2 x.1.rs) x.1.s zs log.wasQueried

section
variable {X M : Type} [DecidableEq X] [DecidableEq M]

/-- The probability that a game outputs `true`, with the randomizer hash as a
lazily sampled random oracle. `aggAdvantage` is this probability for
`aggExperiment`. -/
noncomputable def romProb [SampleableType H]
    (exp : OracleComp (unifSpec + RandSpec H X M) Bool) : ℝ≥0∞ :=
  (ProbCompRuntime.rom (RandSpec H X M)).evalDist exp {true}

end

/-- The adversary's success probability, with a lazily sampled random oracle. -/
noncomputable def aggAdvantageB [NonceGen n B32] [SampleableType H] (red : H → ZMod n)
    (A : AggAdversaryB H) : ℝ≥0∞ :=
  romProb (aggExperimentB red A)

/-- The items and `s` of a forgery in bytes. A forgery that fails the parsing
or the checks becomes the empty aggregate, which never wins. -/
def parseOut (out : Bytes × List (Bytes × Bytes)) : List (Item B32 B32) × ZMod n :=
  match decodeX out.1 out.2 with
  | none => ([], 0)
  | some x => (items x.2 x.1.rs, x.1.s)

/-- The adversary of the game on 32-byte arrays that parses the forgery of `A`. -/
def toStruct (A : AggAdversaryB H) : AggAdversary n H B32 B32 where
  main pk := parseOut <$> A.main pk

/-- **The game on bytes is the game on 32-byte arrays for the adversary that
parses its forgery.** -/
theorem aggExperimentB_eq [NonceGen n B32] (red : H → ZMod n) (A : AggAdversaryB H) :
    aggExperimentB red A = aggExperiment secp256k1X challengeX red (toStruct A) := by
  unfold aggExperimentB aggExperiment toStruct
  simp only [SignatureAlg.runWithSigningOracle_def, simulateQ_map]
  refine bind_congr fun ks => ?_
  simp only [WriterT.run_map, bind_map_left]
  refine bind_congr fun z => ?_
  unfold parseOut
  cases decodeX z.1.1 z.1.2 with
  | none => simp [aggWins]
  | some x => rfl

theorem aggAdvantageB_eq [NonceGen n B32] [SampleableType H] (red : H → ZMod n)
    (A : AggAdversaryB H) :
    aggAdvantageB red A = aggAdvantage secp256k1X challengeX red (toStruct A) := by
  unfold aggAdvantageB
  rw [aggExperimentB_eq]
  rfl

/-! ## A forger's output as bytes -/

/-- A forgery of the game on 32-byte arrays as BIP458's bytes:
`aggsig = r₀ ‖ … ‖ r_{u-1} ‖ bytes(s)` and `pm_aggd`. -/
def serOut (out : List (Item B32 B32) × ZMod n) : Bytes × List (Bytes × Bytes) :=
  ((out.1.map (·.1.1)).flatten ++ bytes32 out.2.val, out.1.map fun it => (it.2.1.1, it.2.2.1))

/-- `decodeVerify` on the encoding of nonces, a scalar and `(pk, m)` pairs. -/
theorem decodeVerify_encode {L : List Bytes} (s : ZMod n) {pm : List (Bytes × Bytes)}
    (hlen : L.length = pm.length) (hL : ∀ c ∈ L, c.length = 32 ∧ toNatBE c < p)
    (hpm : ∀ e ∈ pm, e.1.length = 32 ∧ e.2.length = 32 ∧ toNatBE e.1 < p) :
    decodeVerify (L.flatten ++ bytes32 s.val) pm =
      some (⟨L.map fun r => (toNatBE r : F), s⟩, pm.map fun e => ((toNatBE e.1 : F), e.2)) := by
  have h32 : ∀ c ∈ L, c.length = 32 := fun c hc => (hL c hc).1
  have hs : toNatBE (bytes32 s.val) = s.val := by
    rw [toNatBE_bytes32, Nat.mod_eq_of_lt ((ZMod.val_lt s).trans n_lt)]
  unfold decodeVerify
  dsimp only
  rw [← hlen, chunks32_flatten h32, drop_flatten h32, hs, ZMod.natCast_zmod_val]
  split_ifs with hc
  · rfl
  · refine absurd ?_ hc
    simp only [List.length_append, length_flatten32 h32, bytes32_length, Bool.and_eq_true,
      List.all_eq_true, decide_eq_true_eq, is32, beq_iff_eq]
    exact ⟨⟨⟨⟨by ring, fun e he => ⟨(hpm e he).1, (hpm e he).2.1⟩⟩, fun e he => (hpm e he).2.2⟩,
      fun c hc => (hL c hc).2⟩, ZMod.val_lt s⟩

/-- **Parsing undoes the encoding**, for items whose nonces and public keys are
below `p`. -/
theorem parseOut_serOut (its : List (Item B32 B32)) (s : ZMod n)
    (h : ∀ it ∈ its, toNatBE it.1.1 < p ∧ toNatBE it.2.1.1 < p) :
    parseOut (serOut (its, s)) = (its, s) := by
  have hdec := decodeVerify_encode (L := its.map (·.1.1)) s
    (pm := its.map fun it => (it.2.1.1, it.2.2.1)) (by simp)
    (fun c hc => by
      obtain ⟨it, hit, rfl⟩ := List.mem_map.mp hc
      exact ⟨it.1.2, (h it hit).1⟩)
    (fun e he => by
      obtain ⟨it, hit, rfl⟩ := List.mem_map.mp he
      exact ⟨it.2.1.2, it.2.2.2, (h it hit).2⟩)
  have hrs : ((its.map (·.1.1)).map fun r => (toNatBE r : F)).map encX = its.map (·.1) := by
    simp only [List.map_map]
    refine List.map_congr_left fun it hit => Subtype.ext ?_
    exact bytes32_val_toNatBE it.1.2 (h it hit).1
  have hpm : ((its.map fun it => (it.2.1.1, it.2.2.1)).map
      fun e => ((toNatBE e.1 : F), e.2)).map (fun y => (encX y.1, to32 y.2)) = its.map (·.2) := by
    simp only [List.map_map]
    refine List.map_congr_left fun it hit => Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · exact bytes32_val_toNatBE it.2.1.2 (h it hit).2
    · exact to32_val it.2.2.2
  simp only [parseOut, serOut, decodeX, hdec, Option.map_some, hrs, hpm, items_map]

/-- The byte adversary that runs an algebraic forger and outputs its forgery as
bytes. -/
noncomputable def serB (F : AlgForger n H Point B32 B32) : AggAdversaryB H where
  main pk := serOut <$> (erase secp256k1X F).main pk

/-- The x-only encodings of points are below `p`. -/
theorem toItems_lt (ms : List B32) (pts : List Point) :
    ∀ it ∈ toItems secp256k1X ms pts, toNatBE it.1.1 < p ∧ toNatBE it.2.1.1 < p := by
  have hx : ∀ P : Point, toNatBE (secp256k1X.x P).1 < p := fun P => by
    change toNatBE (bytes32 (xCoord P).val) < p
    rw [toNatBE_bytes32, Nat.mod_eq_of_lt ((ZMod.val_lt _).trans p_lt)]
    exact ZMod.val_lt _
  intro it hit
  simp only [toItems, List.mem_map] at hit
  obtain ⟨mRP, -, rfl⟩ := hit
  exact ⟨hx _, hx _⟩

/-- **Parsing the bytes of a forger's output gives the forger back.** -/
theorem toStruct_serB (F : AlgForger n H Point B32 B32) :
    toStruct (serB F) = erase secp256k1X F := by
  unfold toStruct serB erase
  congr 1
  funext pk
  simp only [Functor.map_map]
  congr 1
  funext out
  exact parseOut_serOut _ _ (toItems_lt _ _)

/-! ## The theorems for the game on bytes -/

/-- **Half-aggregation is as secure as BIP340, with the forgery as bytes.** For
a byte adversary whose parsed forgery is that of an algebraic forger `F`, the
bound of `bytes_halfagg_unforgeable` holds in the game on bytes. -/
theorem bytesGame_halfagg_unforgeable [NonceGen n B32] (A : AggAdversaryB (Fin (2 ^ 256)))
    (F : AlgForger n (Fin (2 ^ 256)) Point B32 B32) (hF : toStruct A = erase secp256k1X F)
    (q : ℕ) (hq : ∀ input, (F.main input).IsQueryBoundP (fun r => isRand r.value.data) q) :
    aggAdvantageB red256 A ≤
      SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp
        (reduction secp256k1X challengeX red256 F) +
        (q + 1 : ℝ≥0∞) * (2 / ((2 ^ 256 : ℕ) : ℝ≥0∞)) := by
  rw [aggAdvantageB_eq, hF]
  exact bytes_halfagg_unforgeable F q hq

/-- The theorem for the algebraic forger `F` with its forgery written as bytes. -/
theorem bytesGame_serB_unforgeable [NonceGen n B32]
    (F : AlgForger n (Fin (2 ^ 256)) Point B32 B32) (q : ℕ)
    (hq : ∀ input, (F.main input).IsQueryBoundP (fun r => isRand r.value.data) q) :
    aggAdvantageB red256 (serB F) ≤
      SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp
        (reduction secp256k1X challengeX red256 F) +
        (q + 1 : ℝ≥0∞) * (2 / ((2 ^ 256 : ℕ) : ℝ≥0∞)) :=
  bytesGame_halfagg_unforgeable (serB F) F (toStruct_serB F) q hq

/-- **The game on bytes can be won.** The bettor with its forgery written as
bytes wins it with positive probability: a correct aggregate in bytes passes
the parsing, the checks and `VerifyAggregate`. -/
theorem bytesGame_winnable [NonceGen n B32] [SampleableType H] (red : H → ZMod n) (m₀ : B32) :
    0 < aggAdvantageB red (serB (bettor (H := H) secp256k1X challengeX m₀)) := by
  rw [aggAdvantageB_eq, toStruct_serB]
  exact bettor_advantage_pos secp256k1X challengeX red m₀

end Halfagg.Security
