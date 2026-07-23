import Measurement.Episode28

/- MEANWHILE 29 -- BISECT THE PROXIMITY SLIP. Episode28 sampled only whole
separations, so the jump from distance 2 to distance 1 hid the actual boundary.
Here the distance is a positive rational and the bisection stays exact.

The first slip inside the interval [1, 2] is the boundary after the distance-2
read:

  distance 2 gives floor(18 / d^2) = 4, mass face.
  the mass face carries the triplet value 5.
  the next slip is floor(18 / d^2) >= 5, value face.

So the bisection solves 18 / d^2 = 5, i.e. 5*d^2 = 18, using only integer
cross-multiplication. This is the Lorentz-looking transition zone: the apparatus
gets the real cut from the partition labels.
-/

/-! # Meanwhile 29 — the first slip: a bisection that closes the bracket  (⚒ steel-driving)

**The genre skin (⚒).** John Henry drives steel: swing at the middle, read whether the drill bit past the
mark, halve the rock that is left, swing again.

**Object & facet.** This is the FIRST-SLIP facet of the object Yang–Mills describes — the place, on our
own rock, where the metal first slips. We describe the facet in the device's own exact terms; we never
open or solve Yang–Mills, and the last box stays wrapped.

**The squeeze (a CLOSING bracket).** Start with the bracket `[one, two]`; probe the midpoint; keep the
half the seam falls in; halve, and halve again — EACH HALVING IS ONE TICK of the squeeze, and every bound
stays an exact rational (integer cross-multiplication, no float). The interval converges onto the target
value `5` (the first slip past the mass triplet). The rock is our own bracket, the seam a value we LOCATE
by halving — decidable and ours, a facet described, not a fracture in the world.
-/

namespace Measurement

/-- `RationalDistance` — a distance as an exact `numerator`/`denominator` fraction (`Repr`, `DecidableEq`).
Fine enough to step either side of the seam without rounding across it. -/
structure RationalDistance where
  numerator : Nat
  denominator : Nat
deriving Repr, DecidableEq

namespace RationalDistance

/-- `RationalDistance.one : RationalDistance` — the distance `1/1`, the bracket's lower end. -/
def one : RationalDistance :=
  { numerator := 1, denominator := 1 }

/-- `RationalDistance.two : RationalDistance` — the distance `2/1`, the bracket's upper end. -/
def two : RationalDistance :=
  { numerator := 2, denominator := 1 }

/-- `RationalDistance.midpoint (a) (b) : RationalDistance` — the exact midpoint of two rationals:
numerator `a.numerator * b.denominator + b.numerator * a.denominator`, denominator
`2 * a.denominator * b.denominator`. The probe point of a bisection step; halving the interval. -/
def midpoint (a b : RationalDistance) : RationalDistance :=
  { numerator := a.numerator * b.denominator + b.numerator * a.denominator
    denominator := 2 * a.denominator * b.denominator }

/-- `RationalDistance.scaledFloor (d) (scale) : Nat` — `d` read to `scale` fixed-point units,
`d.numerator * scale / d.denominator`. -/
def scaledFloor (d : RationalDistance) (scale : Nat) : Nat :=
  d.numerator * scale / d.denominator

/-- `RationalDistance.squaredNumerator (d) : Nat` — `square d.numerator`; the numerator of `d²`, used by
the inverse-square slip. -/
def squaredNumerator (d : RationalDistance) : Nat :=
  square d.numerator

/-- `RationalDistance.squaredDenominator (d) : Nat` — `square d.denominator`; the denominator of `d²`. -/
def squaredDenominator (d : RationalDistance) : Nat :=
  square d.denominator

end RationalDistance

/-- `rationalProximitySlip (distance) : ApparatusRatio` — the inverse-square slip at a rational distance
(exact): the calibrated numerator times `distance.squaredDenominator`, over
`deviceG.denominator * distance.squaredNumerator`. The same law as Ep28, now at any rational distance. -/
def rationalProximitySlip (distance : RationalDistance) : ApparatusRatio :=
  { numerator :=
      deviceG.numerator * cavendishSourceMassTotal *
        tetheredElectronTestMass.magnitude * cavendishArm *
          distance.squaredDenominator
    denominator := deviceG.denominator * distance.squaredNumerator }

/-- `rationalSlipFloor (distance) : Nat` — the integer floor of `rationalProximitySlip distance`. -/
def rationalSlipFloor (distance : RationalDistance) : Nat :=
  (rationalProximitySlip distance).floor

/-- `rationalSlipScaledAt18 (distance) : Nat` — the slip read to eighteen places. -/
def rationalSlipScaledAt18 (distance : RationalDistance) : Nat :=
  (rationalProximitySlip distance).scaledFloor (readoutScale)

/-- `rationalSlipFace (distance) : CorridorFace` — the wheel face the slip floor lands on. -/
def rationalSlipFace (distance : RationalDistance) : CorridorFace :=
  CorridorFace.ofTurns (rationalSlipFloor distance)

/-- `rationalSlipCrosses (targetSlip) (distance) : Bool` — whether the slip at `distance` has reached the
target, `targetSlip * slip.denominator <= slip.numerator` (cross-multiplied, no rounding). The one bit
that drives each swing. -/
def rationalSlipCrosses (targetSlip : Nat) (distance : RationalDistance) : Bool :=
  targetSlip * (rationalProximitySlip distance).denominator <=
    (rationalProximitySlip distance).numerator

/-- `firstSlipTargetBetweenOneAndTwo : Nat` — the seam the drive aims at: one past the distance-2 floor,
the distance-2 floor `⊕` a single point, counted as a cardinality (`earnedSum (proximitySlipFloor 2) 1`,
no postulated `+`; the `+1` is earned as coproduct-with-a-point). Value = `proximitySlipFloor 2 + 1 = 5`
(by `earnedSum_eq`; theorem below), so the α map's slip target `T` is byte-identical. -/
def firstSlipTargetBetweenOneAndTwo : Nat :=
  earnedSum (proximitySlipFloor 2) 1

/-- `SlipBisectStep` — one swing recorded: the rung, the bracket it stood on, the probe (coarse and
scaled), the probe's slip floor / scaled value / face, and whether the drill `crossedSlip` the target. -/
structure SlipBisectStep where
  rung : Nat
  lowerDistance : RationalDistance
  upperDistance : RationalDistance
  probeDistance : RationalDistance
  probeDistanceScaledAt18 : Nat
  probeSlipFloor : Nat
  probeSlipScaledAt18 : Nat
  probeFace : CorridorFace
  crossedSlip : Bool
deriving Repr

/-- `SlipBisectBracket` — the two ends of the current interval, `lowerDistance` and `upperDistance`. -/
structure SlipBisectBracket where
  lowerDistance : RationalDistance
  upperDistance : RationalDistance
deriving Repr

/-- `initialSlipBisectBracket : SlipBisectBracket` — the whole rock to start, `[one, two]`. -/
def initialSlipBisectBracket : SlipBisectBracket :=
  { lowerDistance := RationalDistance.one
    upperDistance := RationalDistance.two }

/-- `bisectSlipOnce (targetSlip) (rung) (bracket) : SlipBisectStep × SlipBisectBracket` — ONE swing, and
one tick of the closing squeeze: probe the midpoint; if the slip crossed the target, pull the LOWER end
up to the probe, else pull the UPPER end down — either way the interval is HALVED. Returns the logged
step and the narrowed bracket. -/
def bisectSlipOnce
    (targetSlip rung : Nat) (bracket : SlipBisectBracket) :
    SlipBisectStep × SlipBisectBracket :=
  let probe := bracket.lowerDistance.midpoint bracket.upperDistance
  let crossed := rationalSlipCrosses targetSlip probe
  let nextBracket :=
    if crossed then
      { bracket with lowerDistance := probe }
    else
      { bracket with upperDistance := probe }
  ({ rung := rung
     lowerDistance := bracket.lowerDistance
     upperDistance := bracket.upperDistance
     probeDistance := probe
     probeDistanceScaledAt18 := probe.scaledFloor (readoutScale)
     probeSlipFloor := rationalSlipFloor probe
     probeSlipScaledAt18 := rationalSlipScaledAt18 probe
     probeFace := rationalSlipFace probe
     crossedSlip := crossed },
   nextBracket)

/-- `bisectSlipAux (fuel) (targetSlip) (rung) (bracket)` — swing until `fuel` runs out, each swing on the
bracket the last one left, collecting every step; returns the final bracket and the step list. Each
recursion halves the interval — the bracket closing tick by tick. -/
def bisectSlipAux :
    Nat -> Nat -> Nat -> SlipBisectBracket ->
      SlipBisectBracket × List SlipBisectStep
  | 0, _targetSlip, _rung, bracket => (bracket, [])
  | fuel + 1, targetSlip, rung, bracket =>
      let next := bisectSlipOnce targetSlip rung bracket
      let rest := bisectSlipAux fuel targetSlip (rung + 1) next.2
      (rest.1, next.1 :: rest.2)

/-- `SlipBisectReport` — the full drive: the target and rung count, the closed-in bracket (both ends,
scaled), each end's slip floor / scaled value / face, and every logged step. -/
structure SlipBisectReport where
  targetSlip : Nat
  rungs : Nat
  lowerDistance : RationalDistance
  upperDistance : RationalDistance
  lowerDistanceScaledAt18 : Nat
  upperDistanceScaledAt18 : Nat
  lowerSlipFloor : Nat
  upperSlipFloor : Nat
  lowerSlipScaledAt18 : Nat
  upperSlipScaledAt18 : Nat
  lowerFace : CorridorFace
  upperFace : CorridorFace
  steps : List SlipBisectStep
deriving Repr

/-- `slipBisectReport (targetSlip) (rungs) : SlipBisectReport` — run `rungs` swings from the whole rock
and report where the two ends finally sit, their slips and faces, and the full step log. -/
def slipBisectReport (targetSlip rungs : Nat) : SlipBisectReport :=
  let result := bisectSlipAux rungs targetSlip 0 initialSlipBisectBracket
  let bracket := result.1
  { targetSlip := targetSlip
    rungs := rungs
    lowerDistance := bracket.lowerDistance
    upperDistance := bracket.upperDistance
    lowerDistanceScaledAt18 := bracket.lowerDistance.scaledFloor (readoutScale)
    upperDistanceScaledAt18 := bracket.upperDistance.scaledFloor (readoutScale)
    lowerSlipFloor := rationalSlipFloor bracket.lowerDistance
    upperSlipFloor := rationalSlipFloor bracket.upperDistance
    lowerSlipScaledAt18 := rationalSlipScaledAt18 bracket.lowerDistance
    upperSlipScaledAt18 := rationalSlipScaledAt18 bracket.upperDistance
    lowerFace := rationalSlipFace bracket.lowerDistance
    upperFace := rationalSlipFace bracket.upperDistance
    steps := result.2 }

/-- `firstSlipBetweenOneAndTwo (rungs) : SlipBisectReport` — `slipBisectReport` driven straight at the
seam `firstSlipTargetBetweenOneAndTwo` (= 5). -/
def firstSlipBetweenOneAndTwo (rungs : Nat) : SlipBisectReport :=
  slipBisectReport firstSlipTargetBetweenOneAndTwo rungs

/-- `SlipBisectSummary` — the short ticket: target, rungs, the two closed-in ends (scaled), their slip
floors, scaled values, and faces — without the full step log. -/
structure SlipBisectSummary where
  targetSlip : Nat
  rungs : Nat
  lowerDistanceScaledAt18 : Nat
  upperDistanceScaledAt18 : Nat
  lowerSlipFloor : Nat
  upperSlipFloor : Nat
  lowerSlipScaledAt18 : Nat
  upperSlipScaledAt18 : Nat
  lowerFace : CorridorFace
  upperFace : CorridorFace
deriving Repr

/-- `slipBisectSummary (targetSlip) (rungs) : SlipBisectSummary` — the report condensed to the ticket. -/
def slipBisectSummary (targetSlip rungs : Nat) : SlipBisectSummary :=
  let report := slipBisectReport targetSlip rungs
  { targetSlip := report.targetSlip
    rungs := report.rungs
    lowerDistanceScaledAt18 := report.lowerDistanceScaledAt18
    upperDistanceScaledAt18 := report.upperDistanceScaledAt18
    lowerSlipFloor := report.lowerSlipFloor
    upperSlipFloor := report.upperSlipFloor
    lowerSlipScaledAt18 := report.lowerSlipScaledAt18
    upperSlipScaledAt18 := report.upperSlipScaledAt18
    lowerFace := report.lowerFace
    upperFace := report.upperFace }

/-- `firstSlipSummaryBetweenOneAndTwo (rungs) : SlipBisectSummary` — that ticket for the seam `5`. -/
def firstSlipSummaryBetweenOneAndTwo (rungs : Nat) : SlipBisectSummary :=
  slipBisectSummary firstSlipTargetBetweenOneAndTwo rungs

/-- `firstSlipTargetBetweenOneAndTwo_is_five`.
**Proposition:** `firstSlipTargetBetweenOneAndTwo = 5` — the bisection target T, a JAR INPUT (the crossing is
`√(C/T) = √(18/5)`).
**Mechanism (strong form, NOT `rfl` at the heartbeat).** `T = earnedSum (proximitySlipFloor 2) 1 =
proximitySlipFloor 2 + 1`. The slip at distance 2 is `deviceG.numerator · P / (P · square 2)` where `P =
sourceMassTotal · testMass · arm` is the (heartbeat-derived) mass product and `deviceG.denominator = P`
structurally (by `cavendishCalibration`'s def) — so the WHOLE mass product `P` CANCELS between the slip
numerator and denominator (`Nat.mul_div_mul_right`), leaving `deviceG.numerator / square 2 = 18/4 = 4`,
independent of any heartbeat count. Then `T = 4 + 1 = 5`. Proved through the ACTUAL `proximitySlipFloor 2`
cancellation, ∀ over the mass product — the `rfl`-at-2132 pin is retired; drift-immune by STRUCTURAL
cancellation, not by evaluation.
**One root, three paths.** T=5 is `deviceG.numerator = 18` read through slip-at-2 (`⌊18/4⌋+1`); the same
root gives C = slip(1) = 18 (`mediantC_is_eighteen`) and R = 18 (`naturalUnitOrbitRadius_is_eighteen`). Not
three independent 18/5s — one coupling (`deviceG.numerator = 18`), three structural transforms. -/
theorem firstSlipTargetBetweenOneAndTwo_is_five :
    firstSlipTargetBetweenOneAndTwo = 5 := by
  have hP : 0 < cavendishSourceMassTotal * tetheredElectronTestMass.magnitude * cavendishArm := by decide
  show earnedSum (proximitySlipFloor 2) 1 = 5
  rw [earnedSum_eq]
  have h4 : proximitySlipFloor 2 = 4 := by
    simp only [proximitySlipFloor, proximitySlip?, ApparatusRatio.floor, square]
    rw [show deviceG.denominator
           = cavendishSourceMassTotal * tetheredElectronTestMass.magnitude * cavendishArm from rfl,
        show deviceG.numerator * cavendishSourceMassTotal * tetheredElectronTestMass.magnitude * cavendishArm
           = 18 * (cavendishSourceMassTotal * tetheredElectronTestMass.magnitude * cavendishArm)
           from by simp only [show deviceG.numerator = 18 from rfl, Nat.mul_assoc]]
    rw [Nat.mul_comm _ 4, Nat.mul_div_mul_right 18 4 hP]
  omega

/-- `firstSlip_probe_starts_left_of_boundary`.
**Proposition:** `(bisectSlipOnce firstSlipTargetBetweenOneAndTwo 0 initialSlipBisectBracket).1.crossedSlip
= true` — the first swing (rung 0) crosses the seam.
**Mechanism:** `rfl` — kernel-computed.
**Squeeze role:** the bisection is honest — it begins from a known side of the seam and closes in, never
assuming where it lands. -/
theorem firstSlip_probe_starts_left_of_boundary :
    (bisectSlipOnce firstSlipTargetBetweenOneAndTwo 0 initialSlipBisectBracket).1.crossedSlip
      = true := by
  rfl

/-! ## Readout — the drive, 24 swings deep
`#eval firstSlipSummaryBetweenOneAndTwo 24` drives the seam twenty-four swings deep and prints the ticket:
the closed-in ends, their slips and faces. The theorems above pin the target and start the honest close;
this is the drive. The next facet, charge/mass normalization, is next door. -/
#eval firstSlipSummaryBetweenOneAndTwo 24

end Measurement
