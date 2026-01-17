import Std
import Measurement.Chapter2.Definitions
import Measurement.Chapter2.Axioms

namespace Measurement

open Classical
noncomputable section

/--
Proposition 1 (Ledger Coherence Under Extension).

PDF sketch assumption: the experimental ledger continues past any event `e`,
so there exists at least one successor event `f` with `e ≺ f`.

Using the Cantor embedding `t : E → Nat`, define `R̂(e)` to be a successor of `e`
with minimal `t`-value among all successors. Then `e ≺ R̂(e)`, so a refinement
operator exists.
-/
theorem proposition1_refinement_operator_exists
  (E : Type u) [CausalSet E]
  (succExists : ∀ e : E, ∃ f : E, EventOrder.prec e f) :
  ∃ R : RefinementOperator E, ∀ e : E, EventOrder.prec e (R.refine e) := by
  classical
  -- Axiom 5 (Cantor): embed events into Nat strictly increasing along ≺
  obtain ⟨t, ht⟩ := cantor_embedding (E := E)

  -- For a fixed e, the predicate "n is the time-index of some successor of e"
  let P : E → Nat → Prop :=
    fun e n => ∃ f : E, EventOrder.prec e f ∧ t f = n

  -- Show P e is inhabited (uses the "ledger continues" assumption)
  have P_inhabited : ∀ e : E, ∃ n : Nat, P e n := by
    intro e
    rcases succExists e with ⟨f, hef⟩
    refine ⟨t f, ?_⟩
    exact ⟨f, hef, rfl⟩

  -- Define refine(e) by choosing the minimal n with P e n, then choosing an f witnessing it.
  let refineFun : E → E :=
    fun e =>
      Classical.choose (Nat.find_spec (P_inhabited e))

  have refineFun_spec :
      ∀ e : E,
        EventOrder.prec e (refineFun e) ∧
        t (refineFun e) = Nat.find (P_inhabited e) := by
    intro e
    -- `Nat.find_spec (P_inhabited e)` : P e (Nat.find ...)
    -- i.e. ∃ f, e ≺ f ∧ t f = Nat.find ...
    simpa [refineFun] using (Classical.choose_spec (Nat.find_spec (P_inhabited e)))

  -- The refinement operator structure
  refine ⟨⟨refineFun⟩, ?_⟩
  intro e
  exact (refineFun_spec e).1
end
end Measurement
