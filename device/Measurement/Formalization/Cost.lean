import Measurement.Formalization.Grammar

/-!
# Cost: the structural gauge

The gauge is not a Boolean observation. The gauge is **cost**. For the first
pass, cost is structural: it counts the production steps in a derivation.
Later passes can connect this `Nat` cost to actual heartbeat measurements
from `Calibration.LeanCalibration`.

## Contents

- `Cost := Nat` — abstract cost type.
- `Derivation.cost` — structural cost as derivation length.
- `cheaper` — the comparison underlying search order.
- `derivation_cost_monotone` — extending a derivation by one step adds cost.
- `inferred_cost` — the canonical derivation has cost 36.

## Structural cost is a proxy, not yet the search gauge

Structural cost (derivation length) is the right first proxy. It is *not*
yet the running-time / search gauge the project is ultimately measuring.
The running-time story needs a real search layer: candidates, an
enumeration, costs per candidate, and a theorem that the serial cascade
improves or controls the search. That layer lives in `Search.lean` (next
file). When `Search.lean` exists, Level 2 cost irredundance becomes
non-vacuous and the structural cost here can be reused as the cost of the
canonical derivation within a real `minCost` enumeration.

## Physical interpretation (deferred)

The formal cost is a structural `Nat`. The experimental layer interprets
that cost physically as compiler heartbeat count / running time. Do not
force actual heartbeat measurement into this formal wrapper. The two layers
stay separate until the connection theorem is written.
-/

namespace Measurement.Formalization

/-- Abstract cost type. -/
abbrev Cost := Nat

namespace Derivation

/-- Structural cost of a derivation: the number of `Step` applications.
Identical to `Derivation.length` for the first pass. -/
def cost {s : Stage} (d : Derivation s) : Cost := d.length

/-- Extending a derivation by one production step adds exactly 1 to the cost. -/
theorem step_cost {s t : Stage} (h : Step s t) (d : Derivation s) :
    (Derivation.step h d).cost = d.cost + 1 := by
  rfl

/-- The cost of the foundational derivation `.fact` is zero. -/
theorem fact_cost : Derivation.fact.cost = 0 := by rfl

end Derivation

/-- Comparison: `a` is no more expensive than `b`. -/
def cheaper {s t : Stage} (a : Derivation s) (b : Derivation t) : Prop :=
  a.cost ≤ b.cost

/-- The canonical derivation has cost 36. -/
theorem inferred_cost : derivation_inferred.cost = 36 := by
  unfold Derivation.cost
  exact inferred_derivation_length

end Measurement.Formalization
