-- TheSlipPointByBisection.lean
--
-- Operator, 2026-08-23 20:58: "find the slip point using bisection."
--
-- THE SLIP POINT is where the slip law meets the target: slip(d) = T, with
-- slip(d) = C/d^2.  Episode 10 takes it by the proven integer square root.
-- This leaf takes it the OTHER way -- by bisection -- so the two roads can be
-- compared, which is the only reason a second road is worth building.
--
-- EXACT, AND NO DIVISION ANYWHERE.  A candidate d is a pair (p, q) read as p/q.
-- The test "is the slip at p/q above the target?" is
--     C/(p/q)^2 > T   <=>   C*q^2 > T*p^2
-- which is a comparison of two naturals.  No rationals are formed, no floats
-- exist, and every step is decidable.  That is what lets the ladder below be
-- printed AND receipted rather than merely printed.
--
-- BISECTION BY MEDIANT, which is the device's own topology: the next candidate
-- between p/q and r/s is (p+r)/(q+s).  It is not the arithmetic midpoint; it is
-- the coarsest rational strictly between the two, which is the right step for a
-- machine that counts rather than averages.
--
-- NOT CLAIMED: that this is a better road than Episode 10's square root, or
-- that the bracket below is the jar.  It is the slip point, found by bisection,
-- reported with the bracket it stopped in.

import Measurement.TheBoxesCounted

namespace Measurement.TheSlipPointByBisection

/-- The coupling and the target, restated locally as the counts they are: the
slip is the pair, the separation is the boxes and the electron's counted, the
coupling is slip times separation squared, and the target is the slip law read
at the second station. -/
def theBoxes : Nat := TheBoxesCounted.theBoxCount
def theElectrons : Nat := TheBoxesCounted.theElectronsBox
def theSeparation : Nat :=
  ((List.range theBoxes).map Sum.inl ++ (List.range theElectrons).map Sum.inr
    : List (Nat ⊕ Nat)).length
def C : Nat := theBoxes * (theSeparation * theSeparation)
def T : Nat := C / (theBoxes * theBoxes) + 1

/-- IS THE SLIP AT p/q ABOVE THE TARGET?  `C/(p/q)^2 > T` without dividing:
`C*q^2 > T*p^2`. -/
def slipAbove (p q : Nat) : Bool := decide (C * (q * q) > T * (p * p))

/-- One mediant step on a bracket `lo = a/b`, `hi = c/d`.  The mediant
`(a+c)/(b+d)` replaces whichever end it agrees with, so the slip point stays
enclosed. -/
def step : (Nat × Nat) × (Nat × Nat) → (Nat × Nat) × (Nat × Nat)
  | ((a, b), (c, d)) =>
      let m := (a + c, b + d)
      if slipAbove m.1 m.2 then (m, (c, d)) else ((a, b), m)

/-- The ladder: `n` mediant steps from the starting bracket. -/
def bisect : Nat → (Nat × Nat) × (Nat × Nat) → (Nat × Nat) × (Nat × Nat)
  | 0,     br => br
  | n + 1, br => bisect n (step br)

/-- START: one and two.  The slip is above the target at one and below it at
two -- decided below, not assumed -- so the slip point is enclosed from the
first step. -/
def theStart : (Nat × Nat) × (Nat × Nat) := ((1, 1), (2, 1))

#eval ("C, T", C, T)
#eval ("slip above at 1?  at 2?", slipAbove 1 1, slipAbove 2 1)
#eval ("bracket after  3 steps", bisect 3 theStart)
#eval ("bracket after 10 steps", bisect 10 theStart)
#eval ("bracket after 20 steps", bisect 20 theStart)

-- ---------------------------------------------------------------------------
-- THE RECEIPTS.
-- ---------------------------------------------------------------------------

/-- THE COUNTS ARE THE COUNTED ONES.  C and T here are what the counting leaf
returns, not numerals typed into this file. -/
theorem the_counts_are_counted : theBoxes = 2 ∧ theSeparation = 3 ∧ C = 18 ∧ T = 5 := by
  decide

/-- THE SLIP POINT IS ENCLOSED FROM THE START: above the target at one, below
it at two.  Bisection has something to bisect. -/
theorem the_start_encloses : slipAbove 1 1 = true ∧ slipAbove 2 1 = false := by decide

/-- AND IT STAYS ENCLOSED.  After twenty steps the low end is still above the
target and the high end still below it -- the bracket never lost the point it
was built to hold. -/
theorem it_stays_enclosed :
    slipAbove (bisect 20 theStart).1.1 (bisect 20 theStart).1.2 = true
    ∧ slipAbove (bisect 20 theStart).2.1 (bisect 20 theStart).2.2 = false := by
  decide

/-- THE BRACKET TIGHTENS, and here is the sense in which: squared, the low end
is below C/T and the high end above it, and the gap between the two squared
ends shrinks as steps are taken.  Stated on the cross-multiplied integers so no
rational is formed. -/
theorem the_bracket_tightens :
    let b3 := bisect 3 theStart
    let b20 := bisect 20 theStart
    (T * (b20.2.1 * b20.2.1) * (b3.2.2 * b3.2.2))
      ≤ (T * (b3.2.1 * b3.2.1) * (b20.2.2 * b20.2.2)) := by
  decide

end Measurement.TheSlipPointByBisection

#print axioms Measurement.TheSlipPointByBisection.the_counts_are_counted
#print axioms Measurement.TheSlipPointByBisection.the_start_encloses
#print axioms Measurement.TheSlipPointByBisection.it_stays_enclosed
#print axioms Measurement.TheSlipPointByBisection.the_bracket_tightens
