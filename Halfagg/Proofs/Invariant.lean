import Halfagg.Proofs.Algebra

/-!
# The reduction's bookkeeping stays valid

Along every reply path of an algebraic forger run through `coreImpl`, the
recorded basis represents the received points and every recorded representation
is valid (`core_inv`), provided every signature the handler obtains is valid.
The proof follows `agm-lean`'s `Adversary.run_valid`.
-/

set_option linter.unusedSectionVars false

namespace Halfagg.Security

open OracleSpec OracleComp Taproot Taproot.Curve Taproot.BIP340 AlgebraicGroupModel.Interaction

attribute [local instance] smulVal

variable {n : ℕ} [Fact n.Prime] {E X M : Type} [AddCommGroup E] [DecidableEq E]
  [DecidableEq X] [DecidableEq M] (C : Curve n E X) (challenge : X → X → M → ZMod n)

theorem extend_nil (recv : List E) :
    extend (G := Pts E) (fun _ => recv) (fun _ => []) = fun _ => recv := by
  funext s; simp [extend]

/-- The core state is valid for the received points `recv`. -/
def CoreOK (d : ZMod n) (recv : List E) (st : Core n X M) : Prop :=
  BasisOK C d recv st.basis ∧ MemoOK C d st.memo

theorem coreOK_init (d : ZMod n) : CoreOK C d [C.G, C.mulG d] (Core.init : Core n X M) := by
  have : Fact (1 < n) := ⟨(Fact.out : n.Prime).one_lt⟩
  refine ⟨?_, memoOK_none C d⟩
  refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ List.Forall₂.nil)
  · simp [repPoint, C.mulG_eq_val_smul, ZMod.val_one]
  · simp [repPoint]

/-- **The bookkeeping invariant.** If every signature `sg` returns satisfies
`lift_x(r) = s⋅G - e⋅P*`, then along every reply path of an algebraic program the
final state is valid for the final received points, and the output's
explanations are valid over them. -/
theorem core_inv {ι' : Type} {spec' : OracleSpec ι'} (hx0 : C.liftX (C.x 0) = none)
    (d : ZMod n) (pk : X)
    (unif : (k : ℕ) → OracleComp spec' (Fin (k + 1)))
    (ro : List (AItem n X M) → OracleComp spec' (ZMod n))
    (sg : M → OracleComp spec' (X × ZMod n))
    (hsg : ∀ msg, ∀ sig ∈ support (sg msg),
      C.liftX sig.1 = some (repPoint C d (sig.2, -challenge sig.1 pk msg)))
    {Result : Type}
    (prog : OracleComp (explainedSpec (ZMod n) (Pts E) (Request X M) (Reply n X M))
      (Explained (ZMod n) Result (Pts E)))
    (recv : List E) (hprog : IsAlgebraic (fun _ => recv) prog)
    (st : Core n X M) (hst : CoreOK C d recv st)
    (z : Explained (ZMod n) Result (Pts E) × Core n X M)
    (hz : z ∈ support ((simulateQ (coreImpl C challenge pk unif ro sg) prog).run st)) :
    ∃ recv', CoreOK C d recv' z.2 ∧ z.1.Valid (fun _ => recv') := by
  induction prog using OracleComp.inductionOn generalizing recv st z with
  | pure out =>
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact ⟨recv, hst, hprog⟩
  | query_bind q next ih =>
    change IsAlgebraic (fun _ => recv) (OracleComp.queryBind q next) at hprog
    obtain ⟨hq, hnext⟩ := (isAlgebraic_query _ q next).mp hprog
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind] at hz
    rw [mem_support_bind_iff] at hz
    obtain ⟨⟨reply, st'⟩, hrep, hz⟩ := hz
    obtain ⟨⟨data, groups⟩, coeffs⟩ := q
    cases data with
    | random k =>
      simp only [coreImpl, StateT.run, support_bind, support_pure, Set.mem_iUnion,
        Set.mem_singleton_iff] at hrep
      obtain ⟨u, -, hu⟩ := hrep
      simp only [Prod.mk.injEq] at hu
      obtain ⟨rfl, rfl⟩ := hu
      have h := hnext ⟨u, fun _ => []⟩
      rw [extend_nil] at h
      exact ih _ recv h _ hst z hz
    | rand ms tail =>
      simp only [coreImpl, StateT.run, support_bind, support_pure, Set.mem_iUnion,
        Set.mem_singleton_iff] at hrep
      obtain ⟨u, -, hu⟩ := hrep
      simp only [Prod.mk.injEq] at hu
      obtain ⟨rfl, rfl⟩ := hu
      have h := hnext ⟨u, fun _ => []⟩
      rw [extend_nil] at h
      refine ih _ recv h _ ?_ z hz
      exact ⟨hst.1, memoOK_memoize C hx0 d hst.2 hst.1 (hq ())⟩
    | sign msg =>
      simp only [coreImpl, StateT.run, support_bind, support_pure, Set.mem_iUnion,
        Set.mem_singleton_iff] at hrep
      obtain ⟨sig, hsig, hu⟩ := hrep
      simp only [Prod.mk.injEq] at hu
      obtain ⟨rfl, rfl⟩ := hu
      have hR := hsg msg sig hsig
      have h : AlgebraicGroupModel.Interaction.IsAlgebraic
          (fun _ => recv ++ [(C.liftX sig.1).getD 0]) _ :=
        hnext ⟨sig.2, fun _ => [(C.liftX sig.1).getD 0]⟩
      refine ih _ _ h _ ?_ z hz
      refine ⟨List.rel_append hst.1 (List.Forall₂.cons ?_ List.Forall₂.nil), hst.2⟩
      rw [hR]; rfl

end Halfagg.Security
