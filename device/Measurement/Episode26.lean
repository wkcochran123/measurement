import Measurement.Episode25

/- MEANWHILE 26 -- CAVENDISH BALANCE. The wheel from Meanwhile25 is the dial.
The outside stimulus is the build, and the Cooper-pair binding residuals are the
two source masses. A tethered electron is the test mass. The observed torsion is
the extra mass-face count on the dial, so the Cavendish calibration is solved as
an exact apparatus ratio:

  G_device = observed_slip * separation^2 / (source_mass_total * test_mass * arm)

This is a calibration of the device reading, not an SI measurement. The point is
to make the slip, source masses, test mass, and torsion fiber all visible through
the same charge/mass/value wheel.
-/

namespace Measurement

def square (n : Nat) : Nat :=
  n * n

structure ApparatusRatio where
  numerator : Nat
  denominator : Nat
deriving Repr

def ApparatusRatio.floor (q : ApparatusRatio) : Nat :=
  q.numerator / q.denominator

def ApparatusRatio.remainder (q : ApparatusRatio) : Nat :=
  q.numerator % q.denominator

def ApparatusRatio.inverseFloor (q : ApparatusRatio) : Nat :=
  q.denominator / q.numerator

def ApparatusRatio.inverseRemainder (q : ApparatusRatio) : Nat :=
  q.denominator % q.numerator

def ApparatusRatio.scaledFloor (q : ApparatusRatio) (scale : Nat) : Nat :=
  q.numerator * scale / q.denominator

def cooperPairSourceLeft : WheelStimulusRead :=
  wheelStimulusRead "cooperPair.sourceLeft" elabBindingEnergyB2

def cooperPairSourceRight : WheelStimulusRead :=
  wheelStimulusRead "cooperPair.sourceRight" elabBindingEnergyDriver

def tetheredElectronTestMass : WheelStimulusRead :=
  wheelStimulusRead "tetheredElectron.testMass" (Int.ofNat electronBox.val)

def cavendishTorsionFiber : WheelStimulusRead :=
  wheelStimulusRead "torsionFiber.friction" elabBindingEnergyB2

def cavendishSourceMassTotal : Nat :=
  cooperPairSourceLeft.magnitude + cooperPairSourceRight.magnitude

def cavendishArm : Nat :=
  electronBox.val

def cavendishSeparation : Nat :=
  boxCount + electronBox.val

def cavendishObservedSlip (dial : CorridorBinReport) : Nat :=
  dial.massCount - Nat.max dial.chargeCount dial.valueCount

def cavendishObservedMassValue (dial : CorridorBinReport) : Nat :=
  valueForMassTriplet (cavendishObservedSlip dial)

def cavendishCalibration (slip : Nat) : ApparatusRatio :=
  { numerator := slip * square cavendishSeparation
    denominator :=
      cavendishSourceMassTotal * tetheredElectronTestMass.magnitude * cavendishArm }

structure CavendishBalanceReport where
  dial : CorridorBinReport
  sourceLeft : WheelStimulusRead
  sourceRight : WheelStimulusRead
  sourcesBalanced : Bool
  testMass : WheelStimulusRead
  torsionFiber : WheelStimulusRead
  arm : Nat
  separation : Nat
  observedSlip : WheelStimulusRead
  observedMassValue : WheelStimulusRead
  calibration : ApparatusRatio
  deviceG : ApparatusRatio
  deviceGScaledAt18 : Nat
  calibrationFloor : Nat
  calibrationRemainder : Nat
  inverseCalibrationFloor : Nat
  inverseCalibrationRemainder : Nat
  motionResolved : Bool
  quantumGravityResolved : Bool
deriving Repr

def cavendishCooperElectron (lower upper : Nat) : CavendishBalanceReport :=
  let dial := corridorBinReport lower upper
  let slip := cavendishObservedSlip dial
  let massValue := cavendishObservedMassValue dial
  let observedSlip := wheelStimulusRead "dial.massFaceSlip" (Int.ofNat slip)
  let observedMassValue := wheelStimulusRead "dial.massTripletValue" (Int.ofNat massValue)
  let calibration := cavendishCalibration massValue
  let motionResolved :=
    (decide (0 < slip) : Bool)
      && cooperPairSourceLeft.motionSlip
      && cooperPairSourceRight.motionSlip
      && tetheredElectronTestMass.motionSlip
      && cavendishTorsionFiber.motionSlip
  { dial := dial
    sourceLeft := cooperPairSourceLeft
    sourceRight := cooperPairSourceRight
    sourcesBalanced :=
      (decide (cooperPairSourceLeft.magnitude = cooperPairSourceRight.magnitude) : Bool)
    testMass := tetheredElectronTestMass
    torsionFiber := cavendishTorsionFiber
    arm := cavendishArm
    separation := cavendishSeparation
    observedSlip := observedSlip
    observedMassValue := observedMassValue
    calibration := calibration
    deviceG := calibration
    deviceGScaledAt18 := calibration.scaledFloor (pow10 18)
    calibrationFloor := calibration.floor
    calibrationRemainder := calibration.remainder
    inverseCalibrationFloor := calibration.inverseFloor
    inverseCalibrationRemainder := calibration.inverseRemainder
    motionResolved := motionResolved
    quantumGravityResolved := motionResolved
      && (decide (cooperPairSourceLeft.magnitude = cooperPairSourceRight.magnitude) : Bool) }

def deviceG : ApparatusRatio :=
  (cavendishCooperElectron 1 1000000).deviceG

theorem deviceG_is_eighteen_over_2132 :
    deviceG.numerator = 18 ∧ deviceG.denominator = 2132 := by
  exact ⟨rfl, rfl⟩

#eval cavendishCooperElectron 1 1000000
#eval deviceG
#eval deviceG.scaledFloor (pow10 18)
#eval (deviceG.inverseFloor, deviceG.inverseRemainder)

end Measurement
