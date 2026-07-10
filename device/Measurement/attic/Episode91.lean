import Measurement.Episode5

namespace Measurement

/-
__EPISODE 91__: _Only ≤ -- the Strict Order is Found, Not Given_

The apparatus exposes exactly ONE comparison on the abstraction: `≤` -- `Abstraction.le`, the dominance
the `LE Abstraction` instance carries.  That `X → X → Prop` is the only op you actually get to call.
It does NOT hand you the strict `<`: the genuine distinction, the funge, the matter/antimatter sign.

You FIND the strict order by RUNNING AN EXPERIMENT -- read `≤` in BOTH directions and keep the
asymmetry:

  a strictly below b   ⟺   (a ≤ b)  ∧  ¬ (b ≤ a)

Two `≤`-readings, run as an experiment, are the only honest source of `<`.  `VALUE.lt?` (Episode6)
merely *declares* a strict order; here we *find* it -- by actually calling the class's `≤` twice and
subtracting.
-/

/-- FOUND BY EXPERIMENT.  Uses the only op the apparatus exposes -- `≤`, the `LE Abstraction` class
method (`X → X → Prop`) -- read in BOTH directions.  `a` sits strictly below `b` when the dominance
holds one way and fails the other.  The strict order, derived not declared. -/
def strictlyBelow (a b : Abstraction) : Prop := a ≤ b ∧ ¬ (b ≤ a)

/-- The reciprocal reading: the same experiment, the other asymmetry. -/
def strictlyAbove (a b : Abstraction) : Prop := strictlyBelow b a

/-- NEUTRAL: both directions of the experiment come back `≤` -- mutual dominance, no asymmetry, no
charge to read (equal, or incomparable beneath the apparatus's resolution). -/
def neutral (a b : Abstraction) : Prop := a ≤ b ∧ b ≤ a

/-- THE CHARGE, read off the experiment: matter when `a` is strictly below `b`, antimatter when
strictly above, neutral when the two `≤`-readings agree both ways.  Every verdict is a call to the
class's `≤`; nothing here is declared. -/
def chargeReading (a b : Abstraction) : Prop :=
  strictlyBelow a b ∨ strictlyAbove a b ∨ neutral a b

/-- The strict order found by experiment is genuinely strict: it cannot hold both ways at once -- one
`≤`-reading had to fail for the asymmetry to exist.  (Pure consequence of the two calls to `≤`.) -/
theorem strictlyBelow_asymm (a b : Abstraction) :
    strictlyBelow a b → ¬ strictlyBelow b a := by
  intro h hba
  exact h.2 hba.1

/-- Strict-below refines `≤`: whatever the experiment calls strictly below, the class's `≤` already
agrees with one way. -/
theorem strictlyBelow_le (a b : Abstraction) :
    strictlyBelow a b → a ≤ b := fun h => h.1

end Measurement
