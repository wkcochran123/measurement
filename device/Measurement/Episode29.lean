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

namespace Measurement

structure RationalDistance where
  numerator : Nat
  denominator : Nat
deriving Repr, DecidableEq

namespace RationalDistance

def one : RationalDistance :=
  { numerator := 1, denominator := 1 }

def two : RationalDistance :=
  { numerator := 2, denominator := 1 }

def midpoint (a b : RationalDistance) : RationalDistance :=
  { numerator := a.numerator * b.denominator + b.numerator * a.denominator
    denominator := 2 * a.denominator * b.denominator }

def scaledFloor (d : RationalDistance) (scale : Nat) : Nat :=
  d.numerator * scale / d.denominator

def squaredNumerator (d : RationalDistance) : Nat :=
  square d.numerator

def squaredDenominator (d : RationalDistance) : Nat :=
  square d.denominator

end RationalDistance

def rationalProximitySlip (distance : RationalDistance) : ApparatusRatio :=
  { numerator :=
      deviceG.numerator * cavendishSourceMassTotal *
        tetheredElectronTestMass.magnitude * cavendishArm *
          distance.squaredDenominator
    denominator := deviceG.denominator * distance.squaredNumerator }

def rationalSlipFloor (distance : RationalDistance) : Nat :=
  (rationalProximitySlip distance).floor

def rationalSlipScaledAt18 (distance : RationalDistance) : Nat :=
  (rationalProximitySlip distance).scaledFloor (pow10 18)

def rationalSlipFace (distance : RationalDistance) : CorridorFace :=
  CorridorFace.ofTurns (rationalSlipFloor distance)

def rationalSlipCrosses (targetSlip : Nat) (distance : RationalDistance) : Bool :=
  targetSlip * (rationalProximitySlip distance).denominator <=
    (rationalProximitySlip distance).numerator

def firstSlipTargetBetweenOneAndTwo : Nat :=
  proximitySlipFloor 2 + 1

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

structure SlipBisectBracket where
  lowerDistance : RationalDistance
  upperDistance : RationalDistance
deriving Repr

def initialSlipBisectBracket : SlipBisectBracket :=
  { lowerDistance := RationalDistance.one
    upperDistance := RationalDistance.two }

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
     probeDistanceScaledAt18 := probe.scaledFloor (pow10 18)
     probeSlipFloor := rationalSlipFloor probe
     probeSlipScaledAt18 := rationalSlipScaledAt18 probe
     probeFace := rationalSlipFace probe
     crossedSlip := crossed },
   nextBracket)

def bisectSlipAux :
    Nat -> Nat -> Nat -> SlipBisectBracket ->
      SlipBisectBracket × List SlipBisectStep
  | 0, _targetSlip, _rung, bracket => (bracket, [])
  | fuel + 1, targetSlip, rung, bracket =>
      let next := bisectSlipOnce targetSlip rung bracket
      let rest := bisectSlipAux fuel targetSlip (rung + 1) next.2
      (rest.1, next.1 :: rest.2)

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

def slipBisectReport (targetSlip rungs : Nat) : SlipBisectReport :=
  let result := bisectSlipAux rungs targetSlip 0 initialSlipBisectBracket
  let bracket := result.1
  { targetSlip := targetSlip
    rungs := rungs
    lowerDistance := bracket.lowerDistance
    upperDistance := bracket.upperDistance
    lowerDistanceScaledAt18 := bracket.lowerDistance.scaledFloor (pow10 18)
    upperDistanceScaledAt18 := bracket.upperDistance.scaledFloor (pow10 18)
    lowerSlipFloor := rationalSlipFloor bracket.lowerDistance
    upperSlipFloor := rationalSlipFloor bracket.upperDistance
    lowerSlipScaledAt18 := rationalSlipScaledAt18 bracket.lowerDistance
    upperSlipScaledAt18 := rationalSlipScaledAt18 bracket.upperDistance
    lowerFace := rationalSlipFace bracket.lowerDistance
    upperFace := rationalSlipFace bracket.upperDistance
    steps := result.2 }

def firstSlipBetweenOneAndTwo (rungs : Nat) : SlipBisectReport :=
  slipBisectReport firstSlipTargetBetweenOneAndTwo rungs

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

def firstSlipSummaryBetweenOneAndTwo (rungs : Nat) : SlipBisectSummary :=
  slipBisectSummary firstSlipTargetBetweenOneAndTwo rungs

theorem firstSlipTargetBetweenOneAndTwo_is_five :
    firstSlipTargetBetweenOneAndTwo = 5 := by
  rfl

theorem firstSlip_probe_starts_left_of_boundary :
    (bisectSlipOnce firstSlipTargetBetweenOneAndTwo 0 initialSlipBisectBracket).1.crossedSlip
      = true := by
  rfl

#eval firstSlipSummaryBetweenOneAndTwo 24

end Measurement
