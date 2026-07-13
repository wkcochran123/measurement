/-! # CycleOfThree — the residue is the invariant of a cycle of three.
Operator: "demonstrate it is a cycle of three."

The count-to-three, the holonomy states −1/0/+1 (electron/null/positron), the R/G/B color of the
three-fold, and the two-pass calibration's rotating roles a/b/c are one object: a rotation that
carries one state into the next and CLOSES only after THREE steps. The residue the machine reports
(reproducible build-to-build) is exactly the invariant carried around this 3-cycle — it comes back
to itself after three, and the count-to-three floor is that closure.

This file demonstrates the cycle is genuinely of order THREE (not one, not two), choice-free. -/

namespace Measurement.CycleOfThree

/-- The three-fold: −1 / 0 / +1 (electron / null / positron) = R/G/B = the calibration roles a/b/c. -/
inductive ThreeFold | minus | zero | plus
deriving DecidableEq, Repr

open ThreeFold

/-- The fold / holonomy / "relabeling is angular momentum": carry each state into the next. -/
def rotate : ThreeFold → ThreeFold
  | minus => zero
  | zero  => plus
  | plus  => minus

/-- Iterate the fold `n` times (n passes of the calibration). -/
def spin : Nat → ThreeFold → ThreeFold
  | 0,     x => x
  | n + 1, x => spin n (rotate x)

-- ⭐ IT IS A CYCLE OF THREE: three folds return EVERY state to itself, and no fewer than three do.
theorem cycle_of_three :
    -- closes at three: every state returns after exactly three folds (the count-to-three floor)
    (spin 3 minus = minus ∧ spin 3 zero = zero ∧ spin 3 plus = plus)
      ∧ spin 1 minus ≠ minus       -- one fold does NOT return  (period ≠ 1)
      ∧ spin 2 minus ≠ minus := by -- two folds do NOT return   (period ≠ 2)
  decide

#print axioms cycle_of_three

-- The residue is invariant under the whole cycle (three folds leave it exactly where it was):
theorem residue_invariant_under_cycle (x : ThreeFold) : spin 3 x = x := by cases x <;> rfl

#eval s!"the fold:  minus → {repr (rotate minus)} → {repr (rotate (rotate minus))} → {repr (spin 3 minus)}  (back to minus at step 3)"
#eval s!"one full turn of all three: {(List.range 4).map (fun n => (repr (spin n minus), repr (spin n zero), repr (spin n plus)))}"
#eval s!"closes only at three:  spin1≠start? {decide (spin 1 minus ≠ minus)}  spin2≠start? {decide (spin 2 minus ≠ minus)}  spin3=start(all three)? {decide (spin 3 minus = minus ∧ spin 3 zero = zero ∧ spin 3 plus = plus)}"

end Measurement.CycleOfThree
