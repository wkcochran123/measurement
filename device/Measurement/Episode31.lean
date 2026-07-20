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

/-! # Meanwhile 31 — the needle: a gauge direction pinned to true  (❖ compass in the tunnel)

**The genre skin (❖).** A magnetic needle set in the device's gauge — a compass image inside the tunnel.
Read which way it leans.

**Object & facet.** This is the GAUGE-NEEDLE facet of the object Yang–Mills describes: the direction the
device's needle takes over its two channels. We describe the facet in the device's own exact terms; we
never open or solve Yang–Mills, and the last box stays wrapped.

**The squeeze (a PINNED boolean).** The needle's direction is fixed: `deflectsTowardMass = true` — it
leans to the heavier of its two channels (mass over charge). The gain `|M - C| / (M + C)` and the mean and
variance carried through the magnet are the device's own reads. This is the device's OWN gauge — a compass
in its own tunnel, not real magnetism and no world field; that gauge boundary is literal, not a disavowal.
-/

namespace Measurement

/-- `ApparatusRatio.mul (a) (b) : ApparatusRatio` — multiply two ratios: numerator
`a.numerator * b.numerator`, denominator `a.denominator * b.denominator`. Carries the gain through the
mean. -/
def ApparatusRatio.mul (a b : ApparatusRatio) : ApparatusRatio :=
  { numerator := a.numerator * b.numerator
    denominator := a.denominator * b.denominator }

/-- `ApparatusRatio.sq (a) : ApparatusRatio` — the square of a ratio, `a.mul a`. Carries the gain through
the variance (a spread scales by the square of a gain). -/
def ApparatusRatio.sq (a : ApparatusRatio) : ApparatusRatio :=
  a.mul a

/-- `chargeMassImbalance (read) : Nat` — how far apart the two channels sit,
`natAbsDiff read.mass.accumulatedSlipPoint read.charge.accumulatedSlipPoint`. The magnitude `|M - C|`. -/
def chargeMassImbalance (read : ChargeMassNormalizationReport) : Nat :=
  natAbsDiff read.mass.accumulatedSlipPoint read.charge.accumulatedSlipPoint

/-- `chargeMassNeedleDirectionIsMass (read) : Bool` — which way the needle leans: `true` when mass
outweighs charge (`read.charge.accumulatedSlipPoint < read.mass.accumulatedSlipPoint`). -/
def chargeMassNeedleDirectionIsMass (read : ChargeMassNormalizationReport) : Bool :=
  read.charge.accumulatedSlipPoint < read.mass.accumulatedSlipPoint

/-- `chargeMassNeedleGain (read) : ApparatusRatio` — how hard the needle swings: the imbalance over the
combined total, `|M - C| / (M + C)`. Direction and strength, both read off the device's two channels. -/
def chargeMassNeedleGain (read : ChargeMassNormalizationReport) : ApparatusRatio :=
  { numerator := chargeMassImbalance read
    denominator := read.combined.accumulatedSlipPoint }

/-- `MagneticNeedleReport` — the needle read: the bin, the corridor spin, the two channels' accumulated
slip points, whether it `deflectsTowardMass`, the imbalance, the gain (scaled), and the slip-point mean
and variance both before and after the needle (scaled). -/
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

/-- `magneticNeedleReport (lower) (upper) : MagneticNeedleReport` — read the needle over `[lower, upper]`:
take the Ep30 normalization, the gain, and pass the accumulated mean and variance through the magnet
(`needleMean = gain * mean`, `needleVariance = gain² * variance`). -/
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

/-- `cavendishMagneticNeedle : MagneticNeedleReport` — the needle read over `[1, 1000000]`. -/
def cavendishMagneticNeedle : MagneticNeedleReport :=
  magneticNeedleReport 1 1000000

/-- `cavendish_magnetic_needle_deflects_toward_mass`.
**Proposition:** `cavendishMagneticNeedle.deflectsTowardMass = true` — the needle leans toward the mass
channel.
**Mechanism:** `rfl` — kernel-computed.
**Squeeze role:** the needle's direction pinned to `true` — the gauge facet fixed, the compass leaning to
its own heavier channel. The device's own gauge, not a world field. -/
theorem cavendish_magnetic_needle_deflects_toward_mass :
    cavendishMagneticNeedle.deflectsTowardMass = true := by
  rfl

/-! ## Readout — the needle
`#eval cavendishMagneticNeedle` prints the whole needle: the channels, direction, gain, and the mean and
variance before and after the magnet. The theorem above pins the direction; this is the device's own
compass reading. The next facet, the orbit, is next door. -/
#eval cavendishMagneticNeedle

end Measurement
