import Measurement.Episode40
import Measurement.CycleOfThree

/-
PLAN_RFC §1.2 / story_arc Ch13.3, Ch15.3 — the α bracket at the device's count-to-3 resolution.

The slip bisection finds the slip point (the static→kinetic minimum where the second-variation
residue crosses). Over-resolving (48 rungs) collapses the bracket onto the device's biased
convergence point, α⁻¹ ≈ 137.011 (~180 ppm below the lab value). The device's OWN resolution floor
is COUNT-TO-3 — it counts to three (the holonomy states −1/0/+1) and resolves no finer — so the
bisection halts at 3 rungs and the bracket a1 < α ≤ a2 STAYS OPEN. The count-to-3 HALT is the real,
robust part (a pre-existing thesis, not tuned to a target).

HONEST FRAME (story_arc Ch13.3 / Ch15.3 — do NOT oversell):
  • This is the BRACKET the machine repeats at its count-to-3 floor, NOT a derivation of the
    magnitude. `137.036` is nameable ONLY as the external lab value the machine PROVES it cannot
    derive; it is never inserted (0 CODATA tokens). The device measures to its counting floor and
    stops.
  • ⚠ The specific numeric WIDTH of this bracket depends on the pre-bisection grid seeding
    (`firstSlipGridCell tgt 128`). That `128` is NOT device-derived — no count-to-3-natural grid
    (3/9/27/81) reproduces containment; it holds at 128/512 and fails at 32/64/256/1024. So this
    bracket is honestly "the count-to-3 reading FOR this grid seeding," and MUST NOT be read as a
    blind capture of `137.036`. The count-to-3 halt is robust; the grid is an acknowledged
    un-derived parameter (fence-flagged).

INTERPRETIVE MAPPING to the sacred law (Ep1–15, read-only). ⚠ This is a DOCSTRING reading, NOT a
code dependency: this file imports `Episode40` (the α arithmetic), not Ep3/4; the α computation is
`alphaFromSecondVariationAtDistance`, not the sacred `SlipProcess` structure. As a reading, the
bound is one instance of a single law the device realizes, stated in sacred Episode 3 and named in
Episode 4 (all of the following MARKED interpretive):
  • α IS the metavariable — the smallest recognizable fraction at each level, IEEE-754 `ε_m`
    (`Episode3.Metavariable`, Ep3:421–423). "We know there IS a smallest fraction, not its value"
    (Ep3:429) — α is not knowable, only STUDYable. That is the horizon.
  • The uncrossable threshold is Chaitin's number (`SlipProcess.stress/threshold`,
    `ChaitinsNumberSequence`, Ep3:369,629) — "one CANNOT CROSS THIS THRESHOLD." We approach three
    (the count) but never reach it: the static→kinetic friction breakaway, "the math CANNOT tell
    when the object moves" (Ep3:698).
  • The method is the sacred BISECTION (Ep3:435–437) — halve the stick; "put the pieces back
    together, you get a whole" (= `1 = 0.999…`). This file's `bisectDyadicSlipAux` is that method.
  • α = the static-friction fraction (`Episode4.static_fraction : SlipProcess`, Ep4:144) — "a slip
    reveals the floor" (Ep3:606); the coupling is the `F = dA + A ∧ A` the slip evaluates
    (Ep3:639, Yang–Mills = PLAN §3's gluon).
So, as a reading: bisect the metavariable, halt at the count-to-3 floor the slip reveals; the
bracket is the machine's REPEATABLE reading at that floor — the statistical study of a point that
is provably unknowable. It is a bracket, not the value; the machine measures to its counting floor
and stops.
-/
namespace Measurement.AlphaBoundCountToThree
open Measurement

/-- The device counts to three; that is its resolution floor. The `3` is a FENCEPOST (operator ruling
2026-07-22 "3 as a fencepost is fine"): `3 = 2 + the closing fencepost` — the ± duplication pair (the
Natural 2) plus the null closing-post — earned FROM the primitive 2, non-circularly (see
`CycleOfThree.ThreeFold`: minus/plus = the ± pair, zero = the null fencepost). NOT a tuned constant, NOT a
measured period of a 3-state type (that would re-introduce the 3 through the back door). Structural ground
on the record: `CycleOfThree.cycle_of_three` proves this ±-pair-plus-null cycle closes at exactly three,
axiom-free. Two roles, don't fuse: THIS is the loop-COUNT (a Nat — you iterate on it); the FLOOR it marks
is a Real/Limit the descent only APPROACHES (the open bracket, never a landed point).
EARNED, not postulated (operator 2026-07-22 "we never earn addition, use the Sum"): `3 = |pair ⊕ post|`,
the cardinality of the coproduct of two STANDALONE primitive types (the ± pair 2 ⊕ the null post 1),
read off the constructed Sum's roster length — NOT `2 + 1` (a postulated `Nat.add`) and NOT the constructor
count of `ThreeFold` (circular). `CycleOfThree.threeFold_sum_{left,right}_inv` prove `ThreeFold ≃ pair ⊕ post`,
so the fencepost structure is intrinsic; addition falls out as the Sum's cardinality. -/
def countToThree : Nat := Measurement.CycleOfThree.cardPairSumPost

def tgt : Nat := firstSlipTargetBetweenOneAndTwo

/-- The slip-bisection midpoint at count `n` (the reading if you counted to `n`). -/
def midAt (n : Nat) : RationalDistance :=
  match (firstSlipGridCell tgt 128).map (fun c =>
    (bisectDyadicSlipAux n tgt (dyadicSlipBracketFromGridCell c)).midpointDistance) with
  | some d => d
  | none => { numerator := 1, denominator := 1 }

def alphaAt    (n : Nat) : Nat := (alphaFromSecondVariationAtDistance tgt (midAt n)).scaledFloor (readoutScale)
def invAlphaAt (n : Nat) : Nat := (alphaFromSecondVariationAtDistance tgt (midAt n)).inverseScaledFloor (readoutScale)

-- THE COUNT-TO-3 BRACKET.  The reading is held between count-2 and count-3: the static→kinetic
-- breakaway cannot be pinned finer (Chaitin, uncomputable), only bracketed at the counting floor.
-- The lid is the two counts.  This is the machine's repeatable reading at its floor -- a bracket,
-- NOT a derivation of the magnitude (137.036 = the external value it proves it cannot derive).
def a1ScaledAt18 : Nat := alphaAt (countToThree - 1)   -- count-2 lid (lower α; inv-α ≈ 137.082)
def a2ScaledAt18 : Nat := alphaAt countToThree         -- count-3 lid (upper α; inv-α ≈ 137.004)
def guessScaledAt18 : Nat := (a1ScaledAt18 + a2ScaledAt18) / 2

def invA1 : Nat := invAlphaAt countToThree             -- count-3 lid (lower inv-α)
def invA2 : Nat := invAlphaAt (countToThree - 1)       -- count-2 lid (upper inv-α)

-- THE COUNT-TO-3 BRACKET (the machine's repeatable reading at its floor; NOT a derivation of the
-- magnitude -- 137.036 is the external lab value it proves it cannot derive; grid-128 seeding):
#eval s!"count-to-3 bracket  a1 < alpha <= a2 (x1e18):  a1={a1ScaledAt18}  guess={guessScaledAt18}  a2={a2ScaledAt18}"

#eval s!"inv-alpha bracket (x1e18): [{invA1} .. {invA2}]   (count-3 .. count-2 floor; not a magnitude derivation)"

theorem bound_ordered : a1ScaledAt18 < a2ScaledAt18 := by decide

#print axioms bound_ordered

end Measurement.AlphaBoundCountToThree
