import Measurement.Episode29

/- MEANWHILE 30 -- NORMALIZE THE CHARGE/MASS DIAL. The mass face already
carries the value slot of its triplet. Now the charge face receives the same
treatment: a charge face carries the following mass slot, while a mass face
carries the following value slot.

For the dial aggregate we accumulate the carried charge and mass slip-points,
then renormalize them so C + M = 1. The statistical read is value-weighted:
the estimated slip point is sum(value^2) / sum(value), and the variance is the
corresponding value-weighted second central moment.
-/

/-! # Meanwhile 30 — the balance: charge and mass pinned to sum one  (‖ bookkeeper's ledger)

**The genre skin (‖).** The bookkeeper closes the day's books with two columns: the LEFT column is charge
(the device's lower channel, `n.lower`), the RIGHT column is mass (its upper channel, `n.upper`). Foot
each, write each as its share of the whole.

**Object & facet.** This is the CHARGE/MASS BALANCE facet of the object Yang–Mills describes: the device's
two channels, allocated against each other. We describe the facet in the device's own exact terms; we
never open or solve Yang–Mills, and the last box stays wrapped.

**The squeeze (a PINNED equality).** Each column is written as its share of the total, and the two shares
sum to EXACTLY one — `normalizedSumScaledAt18 = readoutScale`, i.e. 1.000…0 to eighteen places, an exact
`rfl`. The balance facet is fixed to the exact value 1, by the kernel, no float.

**⚠️ Stereo vs single meter (the fence for this facet).** Charge and mass here ARE the device's two
NEEDLES — its two channels — and the device sums ITS OWN STEREO PAIR to one. The single unified "one" a
reader hears is the reader's own bottom line, never something the device outputs; do not call the
normalized pair "the reading." This is the device balancing its own two columns, not a conservation law of
the world — a distinction that is literal, not a disavowal.
-/

namespace Measurement

/-- `CorridorFace.targetReducedTurns : CorridorFace → Nat` — which reduced (mod-3) turn a face posts to:
`charge ↦ 0`, `mass ↦ 1`, `value ↦ 2`. -/
def CorridorFace.targetReducedTurns : CorridorFace -> Nat
  | .charge => 0
  | .mass => 1
  | .value => 2

/-- `firstTurnWithFaceAtOrAbove (face) (lower) : Nat` — the first turn at or above `lower` that posts to
`face`: `lower` plus the offset needed (mod `corridorPeriod`) to reach the face's target turn. Where a
column's next entry falls. -/
def firstTurnWithFaceAtOrAbove (face : CorridorFace) (lower : Nat) : Nat :=
  let offset :=
    (face.targetReducedTurns + corridorPeriod - corridorReducedTurns lower) %
      corridorPeriod
  lower + offset

/-- `sumArithmeticProgression (first) (step) (count) : Nat` — the closed-form sum of `count` terms of an
arithmetic progression (first term `first`, common difference `step`),
`count * (2*first + (count-1)*step) / 2`. Foots a column by formula, no loop. -/
def sumArithmeticProgression (first step count : Nat) : Nat :=
  count * (2 * first + (count - 1) * step) / 2

/-- `sumNatUpTo (count) : Nat` — `0 + 1 + … + (count-1) = count * (count-1) / 2`. -/
def sumNatUpTo (count : Nat) : Nat :=
  count * (count - 1) / 2

/-- `sumNatSquaresUpTo (count) : Nat` — the sum of the first `count` squares (0..count-1),
`count * (count-1) * (2*count-1) / 6`. -/
def sumNatSquaresUpTo (count : Nat) : Nat :=
  count * (count - 1) * (2 * count - 1) / 6

/-- `sumNatCubesUpTo (count) : Nat` — the sum of the first `count` cubes, `square (sumNatUpTo count)`. -/
def sumNatCubesUpTo (count : Nat) : Nat :=
  square (sumNatUpTo count)

/-- `cube (n) : Nat` — `n * n * n`. -/
def cube (n : Nat) : Nat :=
  n * n * n

/-- `sumArithmeticSquares (first) (step) (count) : Nat` — the closed-form sum of the SQUARES of `count`
arithmetic-progression terms (expanded via `sumNatUpTo`/`sumNatSquaresUpTo`). The second-moment column
sum. -/
def sumArithmeticSquares (first step count : Nat) : Nat :=
  count * square first
    + 2 * first * step * sumNatUpTo count
    + square step * sumNatSquaresUpTo count

/-- `sumArithmeticCubes (first) (step) (count) : Nat` — the closed-form sum of the CUBES of `count`
arithmetic-progression terms. The third-moment column sum. -/
def sumArithmeticCubes (first step count : Nat) : Nat :=
  count * cube first
    + 3 * square first * step * sumNatUpTo count
    + 3 * first * square step * sumNatSquaresUpTo count
    + cube step * sumNatCubesUpTo count

/-- `chargeTripletValueSum (lower) (upper) : Nat` — foot the LEFT column: the value each charge-face
carries, summed across `[lower, upper]` (count of charge turns, first charge turn, step
`corridorPeriod`). -/
def chargeTripletValueSum (lower upper : Nat) : Nat :=
  let count := countBetween chargeTurnsUpTo lower upper
  let first := firstTurnWithFaceAtOrAbove .charge lower
  sumArithmeticProgression (valueForChargeTriplet first) corridorPeriod count

/-- `massTripletValueSum (lower) (upper) : Nat` — foot the RIGHT column: the value each mass-face carries,
summed across `[lower, upper]`. -/
def massTripletValueSum (lower upper : Nat) : Nat :=
  let count := countBetween massTurnsUpTo lower upper
  let first := firstTurnWithFaceAtOrAbove .mass lower
  sumArithmeticProgression (valueForMassTriplet first) corridorPeriod count

/-- `chargeTripletSquareSum (lower) (upper) : Nat` — the LEFT column's sum of squares (second moment). -/
def chargeTripletSquareSum (lower upper : Nat) : Nat :=
  let count := countBetween chargeTurnsUpTo lower upper
  let first := firstTurnWithFaceAtOrAbove .charge lower
  sumArithmeticSquares (valueForChargeTriplet first) corridorPeriod count

/-- `massTripletSquareSum (lower) (upper) : Nat` — the RIGHT column's sum of squares. -/
def massTripletSquareSum (lower upper : Nat) : Nat :=
  let count := countBetween massTurnsUpTo lower upper
  let first := firstTurnWithFaceAtOrAbove .mass lower
  sumArithmeticSquares (valueForMassTriplet first) corridorPeriod count

/-- `chargeTripletCubeSum (lower) (upper) : Nat` — the LEFT column's sum of cubes (third moment). -/
def chargeTripletCubeSum (lower upper : Nat) : Nat :=
  let count := countBetween chargeTurnsUpTo lower upper
  let first := firstTurnWithFaceAtOrAbove .charge lower
  sumArithmeticCubes (valueForChargeTriplet first) corridorPeriod count

/-- `massTripletCubeSum (lower) (upper) : Nat` — the RIGHT column's sum of cubes. -/
def massTripletCubeSum (lower upper : Nat) : Nat :=
  let count := countBetween massTurnsUpTo lower upper
  let first := firstTurnWithFaceAtOrAbove .mass lower
  sumArithmeticCubes (valueForMassTriplet first) corridorPeriod count

/-- `normalizePart (part) (total) : ApparatusRatio` — a column's share of the whole, `part` over `total`.
Applied to both columns, the two shares sum to one (the two parts add to `total`). The allocation. -/
def normalizePart (part total : Nat) : ApparatusRatio :=
  { numerator := part, denominator := total }

/-- `SlipPointMoments` — a column's weighted statistics: the accumulated value, square, and cube; the
value-weighted estimated slip point and its variance (each as an `ApparatusRatio` and scaled). -/
structure SlipPointMoments where
  accumulatedSlipPoint : Nat
  accumulatedSquaredSlipPoint : Nat
  accumulatedCubedSlipPoint : Nat
  estimatedSlipPoint : ApparatusRatio
  variance : ApparatusRatio
  estimatedSlipPointScaledAt18 : Nat
  varianceScaledAt18 : Nat
deriving Repr

/-- `slipPointMoments (weight) (squareSum) (cubeSum) : SlipPointMoments` — build the moments: estimate =
`squareSum` over `weight`; variance numerator `cubeSum * weight - square squareSum`, denominator
`square weight`. The value-weighted mean and spread of a column. -/
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
    estimatedSlipPointScaledAt18 := estimate.scaledFloor (readoutScale)
    varianceScaledAt18 := variance.scaledFloor (readoutScale) }

/-- `slipPointVarianceNumeratorSigned (weight squareSum cubeSum) : Int` — the SIGNED variance numerator
`cubeSum·weight − squareSum²` (Batch 4). The `Nat` `varianceNumerator` inside `slipPointMoments` truncates
to `0` when `squareSum² > cubeSum·weight`; this companion keeps the true sign, so a non-moment input yields
an honest NEGATIVE rather than a silent zero. ⚑ MARK: on GENUINE moment sums this is nonnegative by
Cauchy–Schwarz `(Σw·x²)(Σw) ≥ (Σw·x)²` — a property of real moments, NOT provable for arbitrary a,b,c, so
it is marked, not asserted. Where nonneg it equals the `Nat` numerator exactly
(`slipPointVarianceNumeratorSigned_toNat`), so the existing readout is unchanged on the moment domain. -/
def slipPointVarianceNumeratorSigned (weight squareSum cubeSum : Nat) : Int :=
  (cubeSum * weight : Int) - (square squareSum : Int)

/-- On the Cauchy–Schwarz (genuine-moment) domain the signed numerator equals the `Nat` one exactly —
the `Nat` variance readout is not distorted where the inputs are real moments. -/
theorem slipPointVarianceNumeratorSigned_toNat (weight squareSum cubeSum : Nat)
    (h : square squareSum ≤ cubeSum * weight) :
    (slipPointVarianceNumeratorSigned weight squareSum cubeSum).toNat
      = cubeSum * weight - square squareSum := by
  unfold slipPointVarianceNumeratorSigned; omega

/-- `ChargeMassNormalizationReport` — the day's books: the bin, the charge/mass/combined moments, each
column's normalized share, the scaled reads, and the normalized sum (`normalizedSumScaledAt18`). -/
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

/-- `chargeMassNormalizationReport (lower) (upper) : ChargeMassNormalizationReport` — close the books over
`[lower, upper]`: foot both columns (value, square, cube), take the moments, and normalize —
`normalizedCharge` = charge over total, `normalizedMass` = mass over total, and `normalizedSumScaledAt18`
= (total * readoutScale) over total = `readoutScale` (one). -/
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
    chargeScaledAt18 := charge * readoutScale / total
    massScaledAt18 := mass * readoutScale / total
    normalizedSumScaledAt18 := total * readoutScale / total }

/-- `cavendishChargeMassNormalization : ChargeMassNormalizationReport` — the report over the assay
window `[assayLower, assayUpper]` (audit #2 — named, was `1 1000000`). -/
def cavendishChargeMassNormalization : ChargeMassNormalizationReport :=
  chargeMassNormalizationReport assayLower assayUpper

/-- `cavendish_charge_mass_normalizes_to_one`.
**Proposition:** `cavendishChargeMassNormalization.normalizedSumScaledAt18 = readoutScale` — the normalized
charge-share plus mass-share is exactly one, to eighteen places (1.000…0).
**Mechanism:** `rfl` — kernel-computed, exact, no float.
**Squeeze role:** the two channels PINNED to sum exactly one — the balance facet fixed to the exact value
1. The device balances its own stereo pair; the single "one" heard is the reader's, not a device output. -/
theorem cavendish_charge_mass_normalizes_to_one :
    cavendishChargeMassNormalization.normalizedSumScaledAt18 = readoutScale := by
  rfl

/-! ## Readout — the closing entry
`#eval cavendishChargeMassNormalization` prints the whole close: both columns' moments, their normalized
shares, and the sum (= one). The theorem above pins the balance; this is the ledger. The two needles
balance to one on the device's own page; the next facet, the magnetic needle, is next door. -/
#eval cavendishChargeMassNormalization

end Measurement
