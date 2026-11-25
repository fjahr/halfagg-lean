import Halfagg.Proofs.BridgeGame
import Halfagg.Proofs.TightBound
import Halfagg.Proofs.SignQueries
import Halfagg.Proofs.Secp256k1
import Halfagg.Hash256

/-!
# Half-aggregation is as secure as BIP340

The main theorem, over the definitions of `Halfagg/Security.lean`.
-/

open OracleSpec OracleComp AlgebraicGroupModel.Interaction
open scoped ENNReal

namespace Halfagg.Security

open Taproot Taproot.Curve Taproot.BIP340

attribute [local instance] smulVal

variable {n : ℕ} [Fact n.Prime] {H E X M : Type} [AddCommGroup E] [DecidableEq E]
  [DecidableEq X] [DecidableEq M] (C : Curve n E X) (challenge : X → X → M → ZMod n)
variable [SampleableType H] (red : H → ZMod n)

/-- **Half-aggregation is as secure as BIP340** (Chen and Zhao, Theorem 2), in
the algebraic group model with the randomizer hash as a random oracle and for
every challenge hash: an algebraic forger that makes at most `q` randomizer
requests wins the standard game with probability at most the success
probability of `reduction F` against BIP340, plus `(q + 1)⋅μ`. Here `μ` bounds
the probability that a uniform output of the randomizer hash reduces to a given
scalar (`RedBound`): `1/n` if the hash is uniform in `ZMod n`, and `2/2^256` for
BIP458's 256-bit hash reduced modulo `n` (`Halfagg/Hash256.lean`).

`hx0` says the point at infinity has no x-only encoding: its x-coordinate in the
curve interface does not lift. For secp256k1 that x-coordinate is `0`, and `0`
is not an x-coordinate of the curve because `7` is not a square modulo `p`. -/
theorem halfagg_unforgeable [NonceGen n M] [Inhabited M] (hx0 : C.liftX (C.x 0) = none)
    (F : AlgForger n H E X M) (q : ℕ)
    (hq : ∀ input, (F.main input).IsQueryBoundP (fun r => isRand r.value.data) q)
    (μ : ℝ≥0∞) (hμ : RedBound red μ) :
    aggAdvantage C challenge red (erase C F) ≤
      SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp (reduction C challenge red F) +
        (q + 1 : ℝ≥0∞) * μ := by
  classical
  refine (bridge_game C challenge F).trans ?_
  refine ((prEvent_mono_of_support _ _
    (fun t => extractOK C challenge t ∨ (winT C challenge t ∧ ¬ extractOK C challenge t))
    fun t _ hw => ?_).trans (prEvent_or_le _ _ _)).trans
    (add_le_add (bridge_reduction C challenge F) (annROM_bad C challenge hμ hx0 F q hq))
  by_cases hex : extractOK C challenge t
  · exact Or.inl hex
  · exact Or.inr ⟨hw, hex⟩


/-- The theorem for secp256k1 and BIP458's randomizer hash: the curve hypothesis
holds, the hash has 256 bits and is reduced modulo `n`. -/
theorem secp256k1_halfagg_unforgeable {M : Type} [DecidableEq M] [Inhabited M]
    [NonceGen Secp256k1.n M]
    (challenge : Secp256k1.F → Secp256k1.F → M → ZMod Secp256k1.n)
    (F : AlgForger Secp256k1.n (Fin (2 ^ 256)) Secp256k1.Point Secp256k1.F M) (q : ℕ)
    (hq : ∀ input, (F.main input).IsQueryBoundP (fun r => isRand r.value.data) q) :
    aggAdvantage secp256k1F challenge red256 (erase secp256k1F F) ≤
      SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp
        (reduction secp256k1F challenge red256 F) +
        (q + 1 : ℝ≥0∞) * (2 / ((2 ^ 256 : ℕ) : ℝ≥0∞)) :=
  halfagg_unforgeable secp256k1F challenge red256 Halfagg.Secp256k1.liftX_x_zero F q hq
    _ secp256k1_redBound

/-- **The reduction signs what the forger signs.** For every set of messages
`p`: if the forger makes at most `q` signing requests for messages in `p`, the
reduction makes at most `q` signing queries for messages in `p`. With `p` all
messages, the reduction makes no more signing queries than the forger; with
`q = 0`, it never asks for a signature the forger did not ask for. -/
theorem reduction_sign_queries [NonceGen n M] [Inhabited M] (F : AlgForger n H E X M)
    (p : M → Bool) (q : ℕ)
    (h : ∀ input, (F.main input).IsQueryBoundP (fun r => isSign p r.value.data) q) (pk : X) :
    ((reduction C challenge red F).main pk).IsQueryBoundP (fun t => isSignQuery p t) q :=
  reduction_sign_bound C challenge F p q h pk

/-- **Items that fail `lift_x` never win.** Every item of a winning forgery has
an `r` and a `pk` that are x-coordinates of the curve. So the randomizer of a
list with an item that fails `lift_x` is never used by the verifier of a winning
forgery, which is why a forger may hash anything after such an item (`rawTail`). -/
theorem aggWins_lifts {pk : X} {its : List (Item X M)} {s : ZMod n} {zs : List (ZMod n)}
    {signed : M → Bool} (h : aggWins C challenge pk its s zs signed = true) :
    ∀ it ∈ its, lifts C it = true := by
  simp only [aggWins, verifyWith, Bool.and_eq_true, List.all_eq_true] at h
  have h2 := h.1.1.2
  rwa [items_map] at h2

/-! ## The game's verifier is `VerifyAggregate` -/

/-- Answer randomizer queries from the function `rand` and pass uniform sampling
on: the randomizer oracle as a fixed hash function. -/
def answerRand (rand : List (Item X M) → H) : QueryImpl (unifSpec + RandSpec H X M) ProbComp
  | .inl k => liftM (unifSpec.query k)
  | .inr its => pure (rand its)

omit [DecidableEq X] [DecidableEq M] [SampleableType H] in
theorem zQuery_answerRand (rand : List (Item X M) → H) (its : List (Item X M)) (i : ℕ) :
    simulateQ (answerRand rand) (zQuery red its i) = pure (z (fun l => red (rand l)) its i) := by
  unfold zQuery z
  split_ifs with h
  · rfl
  · rw [simulateQ_map]
    rfl

theorem aggWins_eq_verifyAggregate (rand : List (Item X M) → ZMod n) (pk : X)
    (its : List (Item X M)) (s : ZMod n) (signed : M → Bool) :
    aggWins C challenge pk its s ((List.range its.length).map (z rand its)) signed =
      (verifyAggregate C challenge rand ⟨its.map (·.1), s⟩ (its.map (·.2)) &&
        its.any fun it => it.2.1 == pk && !signed it.2.2) := by
  unfold aggWins verifyAggregate verifyWith
  simp only [items_map]
  have h : isum (fun i it =>
      ((List.map (z rand its) (List.range its.length)).getD i 0).val • term C challenge it) 0 its =
      isum (fun i it => (z rand its i).val • term C challenge it) 0 its :=
    isum_congr fun i a _ _ hi => by
      have hi' : i < its.length := by omega
      simp [hi']
  rw [h]

omit [SampleableType H] in
/-- **The game's verifier is BIP 458's `VerifyAggregate`.** With the randomizer
oracle answered by the function `rand`, the last two lines of `aggExperiment`
compute `verifyAggregate` with the randomizer `red ∘ rand`, and check that some
item has the target key and a message that was never signed. -/
theorem game_verifier (rand : List (Item X M) → H) (pk : X) (its : List (Item X M))
    (s : ZMod n) (signed : M → Bool) :
    simulateQ (answerRand rand) (do
        let zs ← (List.range its.length).mapM (zQuery red its)
        return aggWins C challenge pk its s zs signed) =
      pure (verifyAggregate C challenge (fun l => red (rand l)) ⟨its.map (·.1), s⟩
          (its.map (·.2)) &&
        its.any fun it => it.2.1 == pk && !signed it.2.2) := by
  have hz : ∀ is : List ℕ,
      simulateQ (answerRand rand) (is.mapM (zQuery red its)) =
        pure (is.map (z (fun l => red (rand l)) its)) := by
    intro is
    induction is with
    | nil => rfl
    | cons i is ih => simp [List.mapM_cons, zQuery_answerRand, ih]
  rw [simulateQ_bind, hz, pure_bind, simulateQ_pure, aggWins_eq_verifyAggregate]

end Halfagg.Security
