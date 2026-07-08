import Measurement.Meanwhile44

/- MEANWHILE 45 -- SEND THE SELECTED NEIGHBORHOOD AROUND THE ORBIT. The
decider chooses a rational neighborhood inside the adjacent wobble aperture.
Now that selected neighborhood is carried by the orbit mechanism:

  turns        -> 2*pi * turns
  mean turns   -> full turns + residue turn
  variance     -> (2*pi)^2 * variance

The bracket still divides back by the orbit's `2*pi` clock to the same rational
turns. The mean, however, is an accumulated neighborhood statistic, so the orbit
read must keep both the unwrapped angle and the wrapped residue angle.
-/

namespace Measurement

def ApparatusRatio.turnResidue (q : ApparatusRatio) : ApparatusRatio :=
  { numerator := q.remainder
    denominator := q.denominator }

def ApparatusRatio.turnsAsRadians (q : ApparatusRatio) : ApparatusRatio :=
  twoPiRatio.mul q

def ApparatusRatio.residueRadians (q : ApparatusRatio) : ApparatusRatio :=
  twoPiRatio.mul q.turnResidue

def ApparatusRatio.varianceAsRadiansSquared
    (variance : ApparatusRatio) : ApparatusRatio :=
  twoPiRatio.sq.mul variance

structure NeighborhoodOrbitRead where
  seedIn : Nat
  seedOut : Nat
  selectedFace : CorridorFace
  orbitRadiansPerLoop : ApparatusRatio
  orbitRadiansPerLoopScaledAt18 : Nat
  bracketLowerTurn : ApparatusRatio
  bracketUpperTurn : ApparatusRatio
  bracketWidthTurnScaledAt18 : Nat
  bracketLowerRadians : ApparatusRatio
  bracketUpperRadians : ApparatusRatio
  bracketLowerRadiansScaledAt18 : Nat
  bracketUpperRadiansScaledAt18 : Nat
  bracketWidthRadians : PositiveRatioDifference
  lowerRadiansDivOrbitEquivalentToTurn : Bool
  upperRadiansDivOrbitEquivalentToTurn : Bool
  momentWeight : Nat
  meanTurn : ApparatusRatio
  meanTurnScaledAt18 : Nat
  meanFullTurns : Nat
  meanResidueTurn : ApparatusRatio
  meanResidueTurnScaledAt18 : Nat
  meanUnwrappedRadians : ApparatusRatio
  meanUnwrappedRadiansScaledAt18 : Nat
  meanResidueRadians : ApparatusRatio
  meanResidueRadiansScaledAt18 : Nat
  varianceTurnsSquared : ApparatusRatio
  varianceTurnsSquaredScaledAt18 : Nat
  varianceRadiansSquared : ApparatusRatio
  varianceRadiansSquaredScaledAt18 : Nat
deriving Repr

def neighborhoodOrbitRead
    (report : NeighborhoodDeciderReport) : NeighborhoodOrbitRead :=
  let selected := report.selected
  let lowerRadians := selected.bracketLower.turnsAsRadians
  let upperRadians := selected.bracketUpper.turnsAsRadians
  let meanResidue := selected.mean.turnResidue
  let meanUnwrappedRadians := selected.mean.turnsAsRadians
  let meanResidueRadians := selected.mean.residueRadians
  let varianceRadiansSquared :=
    selected.variance.varianceAsRadiansSquared
  { seedIn := report.seedIn
    seedOut := report.seedOut
    selectedFace := report.selectedFace
    orbitRadiansPerLoop := twoPiRatio
    orbitRadiansPerLoopScaledAt18 := twoPiRatio.scaledFloor (pow10 18)
    bracketLowerTurn := selected.bracketLower
    bracketUpperTurn := selected.bracketUpper
    bracketWidthTurnScaledAt18 := selected.bracketWidthScaledAt18
    bracketLowerRadians := lowerRadians
    bracketUpperRadians := upperRadians
    bracketLowerRadiansScaledAt18 := lowerRadians.scaledFloor (pow10 18)
    bracketUpperRadiansScaledAt18 := upperRadians.scaledFloor (pow10 18)
    bracketWidthRadians := positiveRatioDifference upperRadians lowerRadians
    lowerRadiansDivOrbitEquivalentToTurn :=
      ratioEquivalent (lowerRadians.div twoPiRatio) selected.bracketLower
    upperRadiansDivOrbitEquivalentToTurn :=
      ratioEquivalent (upperRadians.div twoPiRatio) selected.bracketUpper
    momentWeight := selected.momentWeight
    meanTurn := selected.mean
    meanTurnScaledAt18 := selected.meanScaledAt18
    meanFullTurns := selected.mean.floor
    meanResidueTurn := meanResidue
    meanResidueTurnScaledAt18 := meanResidue.scaledFloor (pow10 18)
    meanUnwrappedRadians := meanUnwrappedRadians
    meanUnwrappedRadiansScaledAt18 :=
      meanUnwrappedRadians.scaledFloor (pow10 18)
    meanResidueRadians := meanResidueRadians
    meanResidueRadiansScaledAt18 :=
      meanResidueRadians.scaledFloor (pow10 18)
    varianceTurnsSquared := selected.variance
    varianceTurnsSquaredScaledAt18 := selected.varianceScaledAt18
    varianceRadiansSquared := varianceRadiansSquared
    varianceRadiansSquaredScaledAt18 :=
      varianceRadiansSquared.scaledFloor (pow10 18) }

def defaultNeighborhoodOrbitRead? : Option NeighborhoodOrbitRead :=
  defaultNeighborhoodDeciderReport?.map neighborhoodOrbitRead

#eval defaultNeighborhoodOrbitRead?

end Measurement
