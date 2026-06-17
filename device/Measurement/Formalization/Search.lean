import Measurement.Formalization.Cost

set_option autoImplicit false

/-!
# Search: structural cost precursor

This is not the full Level 2 cost irredundance theorem. It gives the search
layer its first bridge: in the strict serial grammar, the structural cost of
any derivation is exactly the rank of its target stage.
-/

namespace Measurement.Formalization

theorem derivation_cost_eq_rank {s : Stage} (d : Derivation s) :
    d.cost = Stage.rank s := by
  induction d with
  | fact =>
      rfl
  | @step s t h d ih =>
      rw [Derivation.step_cost h d, ih, Step.rank_succ h]

theorem terminal_derivation_cost (d : Derivation .inferred) :
    d.cost = 36 := by
  rw [derivation_cost_eq_rank d]
  rfl

end Measurement.Formalization
