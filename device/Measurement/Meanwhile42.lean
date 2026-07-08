import Measurement.Meanwhile41

/- MEANWHILE 42 -- ADJACENT WOBBLES. A fixed rational wobble is a finite phase
lattice, not literally a dense real orbit. The useful density statement is the
finite one: if the wobble numerator is coprime to its denominator, the loop
walks every lattice point modulo one before repeating. In the refinement limit
these adjacent rational cells are the real-line probe.

For the current device charge, the adjacent wobble rationals are the two live
loop states immediately below and above the elementary charge.
-/

namespace Measurement

structure PositiveRatioDifference where
  numerator : Nat
  denominator : Nat
  scaledAt18 : Nat
deriving Repr

def positiveRatioDifference (upper lower : ApparatusRatio) :
    PositiveRatioDifference :=
  let numerator :=
    upper.numerator * lower.denominator -
      lower.numerator * upper.denominator
  let denominator := upper.denominator * lower.denominator
  { numerator := numerator
    denominator := denominator
    scaledAt18 := numerator * pow10 18 / denominator }

structure AdjacentWobbleReport where
  normalization : String
  wobbleStep : ApparatusRatio
  wobbleStepScaledAt18 : Nat
  latticePeriod : Nat
  coprimeStep : Bool
  targetElementaryChargeSquared : ApparatusRatio
  targetElementaryChargeScaledAt18 : Nat
  lowerLoop : Nat
  upperLoop : Nat
  lowerWobble : ApparatusRatio
  upperWobble : ApparatusRatio
  lowerWobbleScaledAt18 : Nat
  upperWobbleScaledAt18 : Nat
  adjacentWidthScaledAt18 : Nat
  cellResidueScaledAt18 : Nat
  cellResidueRatioScaledAt18 : Nat
  lowerSquare : ApparatusRatio
  upperSquare : ApparatusRatio
  lowerSquareGap : PositiveRatioDifference
  upperSquareGap : PositiveRatioDifference
  lowerSquareBelowTarget : Bool
  upperSquareAboveTarget : Bool
  lowerStatePreserved : Bool
  upperStatePreserved : Bool
deriving Repr

def adjacentWobbleReport
    (report : QuantumChargeLoopReport) : AdjacentWobbleReport :=
  let lower := report.lowerState.inducedCharge
  let upper := report.upperState.inducedCharge
  let lowerSquare := lower.sq
  let upperSquare := upper.sq
  let adjacentWidth :=
    report.upperState.inducedChargeScaledAt18 -
      report.lowerState.inducedChargeScaledAt18
  let cellResidue :=
    report.elementaryChargeScaledAt18 -
      report.lowerState.inducedChargeScaledAt18
  { normalization := report.normalization
    wobbleStep := report.inducedChargePerLoop
    wobbleStepScaledAt18 := report.inducedChargePerLoopScaledAt18
    latticePeriod := report.inducedChargePerLoop.denominator
    coprimeStep :=
      decide
        (Nat.gcd report.inducedChargePerLoop.numerator
          report.inducedChargePerLoop.denominator = 1)
    targetElementaryChargeSquared := report.elementaryChargeSquared
    targetElementaryChargeScaledAt18 := report.elementaryChargeScaledAt18
    lowerLoop := report.lowerLoop
    upperLoop := report.firstLoopAtElementaryCharge
    lowerWobble := lower
    upperWobble := upper
    lowerWobbleScaledAt18 := report.lowerState.inducedChargeScaledAt18
    upperWobbleScaledAt18 := report.upperState.inducedChargeScaledAt18
    adjacentWidthScaledAt18 := adjacentWidth
    cellResidueScaledAt18 := cellResidue
    cellResidueRatioScaledAt18 :=
      cellResidue * pow10 18 / adjacentWidth
    lowerSquare := lowerSquare
    upperSquare := upperSquare
    lowerSquareGap :=
      positiveRatioDifference report.elementaryChargeSquared lowerSquare
    upperSquareGap :=
      positiveRatioDifference upperSquare report.elementaryChargeSquared
    lowerSquareBelowTarget := ratioLeq lowerSquare report.elementaryChargeSquared
    upperSquareAboveTarget := ratioLeq report.elementaryChargeSquared upperSquare
    lowerStatePreserved := report.lowerState.statePreserved
    upperStatePreserved := report.upperState.statePreserved }

def defaultAdjacentWobbleReport? : Option AdjacentWobbleReport :=
  defaultQuantumChargeLoopReport?.map adjacentWobbleReport

#eval defaultAdjacentWobbleReport?

end Measurement
