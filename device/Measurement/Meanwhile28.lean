import Measurement.Meanwhile27

/- MEANWHILE 28 -- PROXIMITY BREAK. The Cavendish cell gives a small-signal
calibration at separation 3. Move the tethered electron closer to the Cooper
pair and the same calibrated inverse-square law amplifies the slip:

  slip(distance) = G_device * source_mass_total * electron_mass * arm / distance^2.

At distance 3 this is the calibrated mass-triplet value. At distance 2 the dial
is already nonlinear. At distance 1 the Cooper-pair proximity channel ruptures:
the floor slip reaches the original separation squared, and the wheel wraps off
the mass face. That is the "things go nuts" line in apparatus units.
-/

namespace Measurement

inductive ProximityRegime where
  | far
  | calibrated
  | nonlinear
  | rupture
  | contact
deriving Repr, DecidableEq

def proximitySlip? : Nat -> Option ApparatusRatio
  | 0 => none
  | distance =>
      some
        { numerator :=
            deviceG.numerator * cavendishSourceMassTotal *
              tetheredElectronTestMass.magnitude * cavendishArm
          denominator := deviceG.denominator * square distance }

def proximitySlipFloor (distance : Nat) : Nat :=
  match proximitySlip? distance with
  | none => 0
  | some slip => slip.floor

def proximitySlipScaledAt18 (distance : Nat) : Nat :=
  match proximitySlip? distance with
  | none => 0
  | some slip => slip.scaledFloor (pow10 18)

def proximityRuptureThreshold : Nat :=
  square cavendishSeparation

def proximityRegime (distance slipFloor : Nat) : ProximityRegime :=
  if distance = 0 then
    .contact
  else if proximityRuptureThreshold <= slipFloor then
    .rupture
  else if distance = cavendishSeparation then
    .calibrated
  else if 1 < slipFloor then
    .nonlinear
  else
    .far

structure ProximityRead where
  distance : Nat
  predictedSlip : Option ApparatusRatio
  slipFloor : Nat
  slipScaledAt18 : Nat
  slipFace : CorridorFace
  motionSlip : Bool
  pairBreaks : Bool
  regime : ProximityRegime
deriving Repr

def proximityRead (distance : Nat) : ProximityRead :=
  let slip? := proximitySlip? distance
  let slipFloor := proximitySlipFloor distance
  let regime := proximityRegime distance slipFloor
  let slipFace := CorridorFace.ofTurns slipFloor
  { distance := distance
    predictedSlip := slip?
    slipFloor := slipFloor
    slipScaledAt18 := proximitySlipScaledAt18 distance
    slipFace := slipFace
    motionSlip := slipFace.isMotionSlip
    pairBreaks := regime = .rupture || regime = .contact
    regime := regime }

def proximitySweepDistances : List Nat :=
  [5, 4, 3, 2, 1, 0]

def proximityFloorCurvature : Int :=
  distanceSecondDifference
    (proximitySlipFloor 3)
    (proximitySlipFloor 2)
    (proximitySlipFloor 1)

def proximityScaledCurvatureAt18 : Int :=
  distanceSecondDifference
    (proximitySlipScaledAt18 3)
    (proximitySlipScaledAt18 2)
    (proximitySlipScaledAt18 1)

structure ProximityBreakReport where
  deviceG : ApparatusRatio
  calibratedDistance : Nat
  sourceMassTotal : Nat
  testMass : Nat
  arm : Nat
  ruptureThreshold : Nat
  floorCurvature : Int
  scaledCurvatureAt18 : Int
  reads : List ProximityRead
deriving Repr

def proximityBreakReport : ProximityBreakReport :=
  { deviceG := deviceG
    calibratedDistance := cavendishSeparation
    sourceMassTotal := cavendishSourceMassTotal
    testMass := tetheredElectronTestMass.magnitude
    arm := cavendishArm
    ruptureThreshold := proximityRuptureThreshold
    floorCurvature := proximityFloorCurvature
    scaledCurvatureAt18 := proximityScaledCurvatureAt18
    reads := proximitySweepDistances.map proximityRead }

theorem proximity_at_calibration_is_mass_triplet_value :
    proximitySlipFloor cavendishSeparation = 2 := by
  rfl

theorem proximity_floor_curvature_positive :
    0 < proximityFloorCurvature := by
  decide

theorem proximity_unit_distance_breaks_pair :
    (proximityRead 1).pairBreaks = true := by
  rfl

#eval proximityBreakReport

end Measurement
