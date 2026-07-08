import Measurement.Meanwhile42

/- MEANWHILE 43 -- DO NOT CONFUSE THE CLOCKS. The physical orbit walks one
full turn, `2*pi` radians. The device loop walks the rational residue lattice.

The previous report was right only as a turn-ratio report: it compared the
charge to the rational fraction of a turn. If we speak in radians, both sides
must be carried through the same `2*pi` channel. The observable ratio is then

  loop-radians / orbit-radians = residue-turns.

That is the finite rational dial. The orbit angle is not itself the residue.
-/

namespace Measurement

def twoPiRatio : ApparatusRatio :=
  { numerator := 2 * truncatedPiNumeratorForCharge
    denominator := truncatedPiScaleForCharge }

def residueTurnAfterLoops (loops : Nat) : ApparatusRatio :=
  { numerator :=
      (loops * inducedChargePerLoop.numerator) %
        inducedChargePerLoop.denominator
    denominator := inducedChargePerLoop.denominator }

def residueRadiansPerLoop : ApparatusRatio :=
  twoPiRatio.mul inducedChargePerLoop

def residueRadiansAfterLoops (loops : Nat) : ApparatusRatio :=
  twoPiRatio.mul (residueTurnAfterLoops loops)

def unwrappedResidueRadiansAfterLoops (loops : Nat) : ApparatusRatio :=
  twoPiRatio.mul (inducedChargeAfterLoops loops)

def orbitRadiansAfterLoops (loops : Nat) : ApparatusRatio :=
  twoPiRatio.mulNat loops

def ratioEquivalent (a b : ApparatusRatio) : Bool :=
  decide (a.numerator * b.denominator = b.numerator * a.denominator)

structure OrbitLoopRadianReport where
  normalization : String
  orbitRadiansPerLoop : ApparatusRatio
  orbitRadiansPerLoopScaledAt18 : Nat
  residueTurnPerLoop : ApparatusRatio
  residueTurnPerLoopScaledAt18 : Nat
  residueRadiansPerLoop : ApparatusRatio
  residueRadiansPerLoopScaledAt18 : Nat
  residueRadiansDivOrbitRadians : ApparatusRatio
  residueRadiansDivOrbitRadiansEquivalentToTurnStep : Bool
  lowerLoop : Nat
  upperLoop : Nat
  lowerResidueTurn : ApparatusRatio
  upperResidueTurn : ApparatusRatio
  lowerResidueRadians : ApparatusRatio
  upperResidueRadians : ApparatusRatio
  lowerResidueRadiansScaledAt18 : Nat
  upperResidueRadiansScaledAt18 : Nat
  orbitRadiansAtUpperLoop : ApparatusRatio
  orbitRadiansAtUpperLoopScaledAt18 : Nat
  unwrappedResidueRadiansAtUpperLoop : ApparatusRatio
  unwrappedResidueRadiansAtUpperLoopScaledAt18 : Nat
  targetChargeRadiansSquared : ApparatusRatio
  lowerResidueRadiansSquared : ApparatusRatio
  upperResidueRadiansSquared : ApparatusRatio
  lowerRadiansBelowTarget : Bool
  upperRadiansAboveTarget : Bool
deriving Repr

def orbitLoopRadianReport
    (report : AdjacentWobbleReport) : OrbitLoopRadianReport :=
  let lowerTurn := residueTurnAfterLoops report.lowerLoop
  let upperTurn := residueTurnAfterLoops report.upperLoop
  let lowerRadians := residueRadiansAfterLoops report.lowerLoop
  let upperRadians := residueRadiansAfterLoops report.upperLoop
  let orbitRadians := twoPiRatio
  let loopRadians := residueRadiansPerLoop
  let loopRatio := loopRadians.div orbitRadians
  let targetRadiansSquared :=
    twoPiRatio.sq.mul report.targetElementaryChargeSquared
  let lowerRadiansSquared := lowerRadians.sq
  let upperRadiansSquared := upperRadians.sq
  let upperOrbitRadians := orbitRadiansAfterLoops report.upperLoop
  let upperUnwrappedResidueRadians :=
    unwrappedResidueRadiansAfterLoops report.upperLoop
  { normalization := report.normalization
    orbitRadiansPerLoop := orbitRadians
    orbitRadiansPerLoopScaledAt18 := orbitRadians.scaledFloor (pow10 18)
    residueTurnPerLoop := inducedChargePerLoop
    residueTurnPerLoopScaledAt18 := inducedChargePerLoop.scaledFloor (pow10 18)
    residueRadiansPerLoop := loopRadians
    residueRadiansPerLoopScaledAt18 := loopRadians.scaledFloor (pow10 18)
    residueRadiansDivOrbitRadians := loopRatio
    residueRadiansDivOrbitRadiansEquivalentToTurnStep :=
      ratioEquivalent loopRatio inducedChargePerLoop
    lowerLoop := report.lowerLoop
    upperLoop := report.upperLoop
    lowerResidueTurn := lowerTurn
    upperResidueTurn := upperTurn
    lowerResidueRadians := lowerRadians
    upperResidueRadians := upperRadians
    lowerResidueRadiansScaledAt18 := lowerRadians.scaledFloor (pow10 18)
    upperResidueRadiansScaledAt18 := upperRadians.scaledFloor (pow10 18)
    orbitRadiansAtUpperLoop := upperOrbitRadians
    orbitRadiansAtUpperLoopScaledAt18 :=
      upperOrbitRadians.scaledFloor (pow10 18)
    unwrappedResidueRadiansAtUpperLoop := upperUnwrappedResidueRadians
    unwrappedResidueRadiansAtUpperLoopScaledAt18 :=
      upperUnwrappedResidueRadians.scaledFloor (pow10 18)
    targetChargeRadiansSquared := targetRadiansSquared
    lowerResidueRadiansSquared := lowerRadiansSquared
    upperResidueRadiansSquared := upperRadiansSquared
    lowerRadiansBelowTarget :=
      ratioLeq lowerRadiansSquared targetRadiansSquared
    upperRadiansAboveTarget :=
      ratioLeq targetRadiansSquared upperRadiansSquared }

def defaultOrbitLoopRadianReport? : Option OrbitLoopRadianReport :=
  defaultAdjacentWobbleReport?.map orbitLoopRadianReport

#eval defaultOrbitLoopRadianReport?

end Measurement
