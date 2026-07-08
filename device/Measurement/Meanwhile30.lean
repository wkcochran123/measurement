import Measurement.Meanwhile29

/- MEANWHILE 30 -- NORMALIZE THE CHARGE/MASS DIAL. The mass face already
carries the value slot of its triplet. Now the charge face receives the same
treatment: a charge face carries the following mass slot, while a mass face
carries the following value slot.

For the dial aggregate we accumulate the carried charge and mass slip-points,
then renormalize them so C + M = 1. The statistical read is value-weighted:
the estimated slip point is sum(value^2) / sum(value), and the variance is the
corresponding value-weighted second central moment.
-/

namespace Measurement

def CorridorFace.targetReducedTurns : CorridorFace -> Nat
  | .charge => 0
  | .mass => 1
  | .value => 2

def firstTurnWithFaceAtOrAbove (face : CorridorFace) (lower : Nat) : Nat :=
  let offset :=
    (face.targetReducedTurns + corridorPeriod - corridorReducedTurns lower) %
      corridorPeriod
  lower + offset

def sumArithmeticProgression (first step count : Nat) : Nat :=
  count * (2 * first + (count - 1) * step) / 2

def sumNatUpTo (count : Nat) : Nat :=
  count * (count - 1) / 2

def sumNatSquaresUpTo (count : Nat) : Nat :=
  count * (count - 1) * (2 * count - 1) / 6

def sumNatCubesUpTo (count : Nat) : Nat :=
  square (sumNatUpTo count)

def cube (n : Nat) : Nat :=
  n * n * n

def sumArithmeticSquares (first step count : Nat) : Nat :=
  count * square first
    + 2 * first * step * sumNatUpTo count
    + square step * sumNatSquaresUpTo count

def sumArithmeticCubes (first step count : Nat) : Nat :=
  count * cube first
    + 3 * square first * step * sumNatUpTo count
    + 3 * first * square step * sumNatSquaresUpTo count
    + cube step * sumNatCubesUpTo count

def chargeTripletValueSum (lower upper : Nat) : Nat :=
  let count := countBetween chargeTurnsUpTo lower upper
  let first := firstTurnWithFaceAtOrAbove .charge lower
  sumArithmeticProgression (valueForChargeTriplet first) corridorPeriod count

def massTripletValueSum (lower upper : Nat) : Nat :=
  let count := countBetween massTurnsUpTo lower upper
  let first := firstTurnWithFaceAtOrAbove .mass lower
  sumArithmeticProgression (valueForMassTriplet first) corridorPeriod count

def chargeTripletSquareSum (lower upper : Nat) : Nat :=
  let count := countBetween chargeTurnsUpTo lower upper
  let first := firstTurnWithFaceAtOrAbove .charge lower
  sumArithmeticSquares (valueForChargeTriplet first) corridorPeriod count

def massTripletSquareSum (lower upper : Nat) : Nat :=
  let count := countBetween massTurnsUpTo lower upper
  let first := firstTurnWithFaceAtOrAbove .mass lower
  sumArithmeticSquares (valueForMassTriplet first) corridorPeriod count

def chargeTripletCubeSum (lower upper : Nat) : Nat :=
  let count := countBetween chargeTurnsUpTo lower upper
  let first := firstTurnWithFaceAtOrAbove .charge lower
  sumArithmeticCubes (valueForChargeTriplet first) corridorPeriod count

def massTripletCubeSum (lower upper : Nat) : Nat :=
  let count := countBetween massTurnsUpTo lower upper
  let first := firstTurnWithFaceAtOrAbove .mass lower
  sumArithmeticCubes (valueForMassTriplet first) corridorPeriod count

def normalizePart (part total : Nat) : ApparatusRatio :=
  { numerator := part, denominator := total }

structure SlipPointMoments where
  accumulatedSlipPoint : Nat
  accumulatedSquaredSlipPoint : Nat
  accumulatedCubedSlipPoint : Nat
  estimatedSlipPoint : ApparatusRatio
  variance : ApparatusRatio
  estimatedSlipPointScaledAt18 : Nat
  varianceScaledAt18 : Nat
deriving Repr

def slipPointMoments (weight squareSum cubeSum : Nat) : SlipPointMoments :=
  let estimate := { numerator := squareSum, denominator := weight }
  let varianceNumerator := cubeSum * weight - square squareSum
  let varianceDenominator := square weight
  let variance := { numerator := varianceNumerator, denominator := varianceDenominator }
  { accumulatedSlipPoint := weight
    accumulatedSquaredSlipPoint := squareSum
    accumulatedCubedSlipPoint := cubeSum
    estimatedSlipPoint := estimate
    variance := variance
    estimatedSlipPointScaledAt18 := estimate.scaledFloor (pow10 18)
    varianceScaledAt18 := variance.scaledFloor (pow10 18) }

structure ChargeMassNormalizationReport where
  lower : Nat
  upper : Nat
  charge : SlipPointMoments
  mass : SlipPointMoments
  combined : SlipPointMoments
  normalizedCharge : ApparatusRatio
  normalizedMass : ApparatusRatio
  chargeScaledAt18 : Nat
  massScaledAt18 : Nat
  normalizedSumScaledAt18 : Nat
deriving Repr

def chargeMassNormalizationReport (lower upper : Nat) : ChargeMassNormalizationReport :=
  let charge := chargeTripletValueSum lower upper
  let mass := massTripletValueSum lower upper
  let total := charge + mass
  let chargeSquares := chargeTripletSquareSum lower upper
  let massSquares := massTripletSquareSum lower upper
  let totalSquares := chargeSquares + massSquares
  let chargeCubes := chargeTripletCubeSum lower upper
  let massCubes := massTripletCubeSum lower upper
  let totalCubes := chargeCubes + massCubes
  { lower := lower
    upper := upper
    charge := slipPointMoments charge chargeSquares chargeCubes
    mass := slipPointMoments mass massSquares massCubes
    combined := slipPointMoments total totalSquares totalCubes
    normalizedCharge := normalizePart charge total
    normalizedMass := normalizePart mass total
    chargeScaledAt18 := charge * pow10 18 / total
    massScaledAt18 := mass * pow10 18 / total
    normalizedSumScaledAt18 := total * pow10 18 / total }

def cavendishChargeMassNormalization : ChargeMassNormalizationReport :=
  chargeMassNormalizationReport 1 1000000

theorem cavendish_charge_mass_normalizes_to_one :
    cavendishChargeMassNormalization.normalizedSumScaledAt18 = pow10 18 := by
  rfl

#eval cavendishChargeMassNormalization

end Measurement
