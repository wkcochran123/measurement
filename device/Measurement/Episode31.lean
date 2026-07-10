import Measurement.Episode30

/- MEANWHILE 31 -- THE MAGNETIC NEEDLE. Spin the corridor on the hidden side;
on the visible side a magnet deflects a needle. The needle is not another face
count. It is the analog read of the charge/mass imbalance acting on the
accumulated slip-point estimator.

The exact gain is

  gain = |M - C| / (M + C).

Then the needle carries the mean and variance through the magnet:

  needle_mean     = gain * slip_mean,
  needle_variance = gain^2 * slip_variance.
-/

namespace Measurement

def ApparatusRatio.mul (a b : ApparatusRatio) : ApparatusRatio :=
  { numerator := a.numerator * b.numerator
    denominator := a.denominator * b.denominator }

def ApparatusRatio.sq (a : ApparatusRatio) : ApparatusRatio :=
  a.mul a

def chargeMassImbalance (read : ChargeMassNormalizationReport) : Nat :=
  natAbsDiff read.mass.accumulatedSlipPoint read.charge.accumulatedSlipPoint

def chargeMassNeedleDirectionIsMass (read : ChargeMassNormalizationReport) : Bool :=
  read.charge.accumulatedSlipPoint < read.mass.accumulatedSlipPoint

def chargeMassNeedleGain (read : ChargeMassNormalizationReport) : ApparatusRatio :=
  { numerator := chargeMassImbalance read
    denominator := read.combined.accumulatedSlipPoint }

structure MagneticNeedleReport where
  lower : Nat
  upper : Nat
  corridorSpin : Nat
  chargeAccumulatedSlipPoint : Nat
  massAccumulatedSlipPoint : Nat
  deflectsTowardMass : Bool
  magneticImbalance : Nat
  normalizedMagnetGain : ApparatusRatio
  normalizedMagnetGainScaledAt18 : Nat
  slipPointMean : ApparatusRatio
  slipPointMeanScaledAt18 : Nat
  slipPointVariance : ApparatusRatio
  slipPointVarianceScaledAt18 : Nat
  needleMean : ApparatusRatio
  needleMeanScaledAt18 : Nat
  needleVariance : ApparatusRatio
  needleVarianceScaledAt18 : Nat
deriving Repr

def magneticNeedleReport (lower upper : Nat) : MagneticNeedleReport :=
  let read := chargeMassNormalizationReport lower upper
  let gain := chargeMassNeedleGain read
  let needleMean := gain.mul read.combined.estimatedSlipPoint
  let needleVariance := gain.sq.mul read.combined.variance
  { lower := lower
    upper := upper
    corridorSpin := read.combined.accumulatedSlipPoint
    chargeAccumulatedSlipPoint := read.charge.accumulatedSlipPoint
    massAccumulatedSlipPoint := read.mass.accumulatedSlipPoint
    deflectsTowardMass := chargeMassNeedleDirectionIsMass read
    magneticImbalance := chargeMassImbalance read
    normalizedMagnetGain := gain
    normalizedMagnetGainScaledAt18 := gain.scaledFloor (pow10 18)
    slipPointMean := read.combined.estimatedSlipPoint
    slipPointMeanScaledAt18 := read.combined.estimatedSlipPointScaledAt18
    slipPointVariance := read.combined.variance
    slipPointVarianceScaledAt18 := read.combined.varianceScaledAt18
    needleMean := needleMean
    needleMeanScaledAt18 := needleMean.scaledFloor (pow10 18)
    needleVariance := needleVariance
    needleVarianceScaledAt18 := needleVariance.scaledFloor (pow10 18) }

def cavendishMagneticNeedle : MagneticNeedleReport :=
  magneticNeedleReport 1 1000000

theorem cavendish_magnetic_needle_deflects_toward_mass :
    cavendishMagneticNeedle.deflectsTowardMass = true := by
  rfl

#eval cavendishMagneticNeedle

end Measurement
