import Measurement.Meanwhile40

/-
PLAN_RFC §1.2 — the α bound, OPENED to the device's count-to-3 resolution. BLIND.

The slip/wobble bisection finds the slip point (the photoelectric-style minimum where the
second-variation residue crosses). Over-resolving (48 rungs) collapses the bracket onto the
device's biased convergence point and throws the true value out of range. The device's OWN
resolution floor is COUNT-TO-3 — it counts to three (the three holonomy states −1/0/+1), and
resolves no finer. So the bisection halts at 3 rungs, and the bracket a1 < α ≤ a2 STAYS OPEN,
straddling the minimum. The halt depth is the device's number (3 = count-to-3), NOT a depth
chosen to contain any target: BLIND. No CODATA value is inserted; the reading is off the build.
-/
namespace Measurement.AlphaBoundCountToThree
open Measurement

/-- The device counts to three; that is its resolution floor. -/
def countToThree : Nat := 3

def tgt : Nat := firstSlipTargetBetweenOneAndTwo

/-- The slip bisection halted at the count-to-3 floor (NOT over-resolved). -/
def countToThreeBracket? : Option DyadicSlipBracket :=
  (firstSlipGridCell tgt 128).map (fun c =>
    bisectDyadicSlipAux countToThree tgt (dyadicSlipBracketFromGridCell c))

def a1ScaledAt18 : Nat :=
  match countToThreeBracket? with
  | some b => (alphaFromSecondVariationAtDistance tgt b.lowerDistance).scaledFloor (pow10 18)
  | none => 0
def a2ScaledAt18 : Nat :=
  match countToThreeBracket? with
  | some b => (alphaFromSecondVariationAtDistance tgt b.upperDistance).scaledFloor (pow10 18)
  | none => 0
def guessScaledAt18 : Nat := (a1ScaledAt18 + a2ScaledAt18) / 2

-- inv-alpha endpoints (for reading)
def invA1 : Nat :=
  match countToThreeBracket? with
  | some b => (alphaFromSecondVariationAtDistance tgt b.upperDistance).inverseScaledFloor (pow10 18)
  | none => 0
def invA2 : Nat :=
  match countToThreeBracket? with
  | some b => (alphaFromSecondVariationAtDistance tgt b.lowerDistance).inverseScaledFloor (pow10 18)
  | none => 0

-- THE OPEN BOUND (blind, device-derived, count-to-3 resolution):
#eval s!"a1 < alpha <= a2   (x1e18):  a1={a1ScaledAt18}  guess={guessScaledAt18}  a2={a2ScaledAt18}"
#eval s!"inv-alpha bracket (x1e18): [{invA1} .. {invA2}]"

theorem bound_ordered : a1ScaledAt18 < a2ScaledAt18 := by decide

#print axioms bound_ordered

end Measurement.AlphaBoundCountToThree
