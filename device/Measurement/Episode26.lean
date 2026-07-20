import Measurement.Episode25

/- MEANWHILE 26 -- CAVENDISH BALANCE. The wheel from Episode25 is the dial.
The outside stimulus is the build, and the Cooper-pair binding residuals are the
two source masses. A tethered electron is the test mass. The observed torsion is
the extra mass-face count on the dial, so the Cavendish calibration is solved as
an exact apparatus ratio:

  G_device = observed_slip * separation^2 / (source_mass_total * test_mass * arm)

This is a calibration of the device reading, not an SI measurement. The point is
to make the slip, source masses, test mass, and torsion fiber all visible through
the same charge/mass/value wheel.
-/

/-! # Meanwhile 26 — the weight: gravity, the first facet pinned  (⚖ sworn assayer)

**The genre skin (⚖).** The first lid lifts and out comes a little brass weight the machine had been
carrying all along. We are the sworn assayer: we set it on the house balance and certify what it reads.

**Object & facet.** This weight is the GRAVITY facet of the object Yang–Mills describes — the first facet
the walk fixes. The balance is built from the Ep25 wheel: the two Cooper-pair binding residuals are the
source masses, the tethered electron the test mass, and the extra mass-face count on the dial is the
observed torsion. We describe this facet exactly; we never claim to open or solve Yang–Mills, and the
last box — the object's own ground — stays wrapped.

**The squeeze (this facet CLOSES).** Here the squeeze does not bracket between two moving bounds — it
collapses to a POINT: the gravity facet is pinned to the exact rational `deviceG = 18/2132`, an exact
equality decided by the kernel (`⟨rfl, rfl⟩`), no float. `G_device = observed_slip · separation² /
(source_mass_total · test_mass · arm)` is solved as a whole-number `ApparatusRatio`. This is the device's
own number, `18/2132` — the reading of its own apparatus, not Newton's specific gravitational constant;
that distinction is literal, not a disavowal. The first facet, nailed.
-/

namespace Measurement

/-- `square (n) : Nat` — `n * n`; the squared separation the Cavendish law needs. -/
def square (n : Nat) : Nat :=
  n * n

/-- `ApparatusRatio` — an exact rational as a `numerator`/`denominator` pair of `Nat`s (`Repr` for
readouts). Every device reading lives here: whole-number over whole-number, never a float; each facet's
squeeze is expressed as one of these. -/
structure ApparatusRatio where
  numerator : Nat
  denominator : Nat
deriving Repr

/-- `ApparatusRatio.floor (q) : Nat` — the integer part `q.numerator / q.denominator` (truncating `Nat`
division). -/
def ApparatusRatio.floor (q : ApparatusRatio) : Nat :=
  q.numerator / q.denominator

/-- `ApparatusRatio.remainder (q) : Nat` — the remainder `q.numerator % q.denominator`; with `floor`,
recovers `q` exactly. -/
def ApparatusRatio.remainder (q : ApparatusRatio) : Nat :=
  q.numerator % q.denominator

/-- `ApparatusRatio.inverseFloor (q) : Nat` — the integer part of the reciprocal,
`q.denominator / q.numerator`. -/
def ApparatusRatio.inverseFloor (q : ApparatusRatio) : Nat :=
  q.denominator / q.numerator

/-- `ApparatusRatio.inverseRemainder (q) : Nat` — the remainder of the reciprocal,
`q.denominator % q.numerator`. -/
def ApparatusRatio.inverseRemainder (q : ApparatusRatio) : Nat :=
  q.denominator % q.numerator

/-- `ApparatusRatio.scaledFloor (q) (scale) : Nat` — `q` read to `scale` fixed-point units,
`q.numerator * scale / q.denominator`. With `scale = pow10 18` this is the reading to eighteen decimal
places, exact by integer arithmetic. -/
def ApparatusRatio.scaledFloor (q : ApparatusRatio) (scale : Nat) : Nat :=
  q.numerator * scale / q.denominator

/-- `cooperPairSourceLeft : WheelStimulusRead` — the left source mass of the balance: the Cooper-pair
binding residual `elabBindingEnergyB2` dropped onto the Ep25 wheel. -/
def cooperPairSourceLeft : WheelStimulusRead :=
  wheelStimulusRead "cooperPair.sourceLeft" elabBindingEnergyB2

/-- `cooperPairSourceRight : WheelStimulusRead` — the right source mass: the binding residual
`elabBindingEnergyDriver` on the wheel, balanced against the left. -/
def cooperPairSourceRight : WheelStimulusRead :=
  wheelStimulusRead "cooperPair.sourceRight" elabBindingEnergyDriver

/-- `tetheredElectronTestMass : WheelStimulusRead` — the test mass of the balance: the electron's box
value (`electronBox.val`) on the wheel. -/
def tetheredElectronTestMass : WheelStimulusRead :=
  wheelStimulusRead "tetheredElectron.testMass" (Int.ofNat electronBox.val)

/-- `cavendishTorsionFiber : WheelStimulusRead` — the torsion fiber's friction: the binding residual
`elabBindingEnergyB2` on the wheel. -/
def cavendishTorsionFiber : WheelStimulusRead :=
  wheelStimulusRead "torsionFiber.friction" elabBindingEnergyB2

/-- `cavendishSourceMassTotal : Nat` — the two source masses summed,
`cooperPairSourceLeft.magnitude + cooperPairSourceRight.magnitude`; a denominator term of `G`. -/
def cavendishSourceMassTotal : Nat :=
  cooperPairSourceLeft.magnitude + cooperPairSourceRight.magnitude

/-- `cavendishArm : Nat` — the balance arm, the electron's box value (`electronBox.val`); a denominator
term of `G`. -/
def cavendishArm : Nat :=
  electronBox.val

/-- `cavendishSeparation : Nat` — the source–test separation, `boxCount + electronBox.val`; its square is
the numerator term of `G`. -/
def cavendishSeparation : Nat :=
  boxCount + electronBox.val

/-- `cavendishObservedSlip (dial) : Nat` — the observed torsion: how far the mass face outruns the larger
of charge and value on the dial, `dial.massCount - Nat.max dial.chargeCount dial.valueCount`. The
measured input to the calibration. -/
def cavendishObservedSlip (dial : CorridorBinReport) : Nat :=
  dial.massCount - Nat.max dial.chargeCount dial.valueCount

/-- `cavendishObservedMassValue (dial) : Nat` — the observed slip nudged onto the mass triplet,
`valueForMassTriplet (cavendishObservedSlip dial)`; the slip value the calibration actually uses. -/
def cavendishObservedMassValue (dial : CorridorBinReport) : Nat :=
  valueForMassTriplet (cavendishObservedSlip dial)

/-- `cavendishCalibration (slip) : ApparatusRatio` — Cavendish's law solved as an exact ratio: numerator
`slip * square cavendishSeparation`, denominator `sourceMassTotal * testMass * arm`. No float;
whole-number over whole-number. -/
def cavendishCalibration (slip : Nat) : ApparatusRatio :=
  { numerator := slip * square cavendishSeparation
    denominator :=
      cavendishSourceMassTotal * tetheredElectronTestMass.magnitude * cavendishArm }

/-- `CavendishBalanceReport` — the full assay: the dial, the two sources and whether they balance, the
test mass and fiber, arm and separation, the observed slip and mass value, the calibration and its
`deviceG` (scaled and floored), and two flags. Read `motionResolved`/`quantumGravityResolved` plainly:
they are the bench's own consistency checks (a real twist; `G` a proper fraction), not a claim about the
world. -/
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

/-- `cavendishCooperElectron (lower) (upper) : CavendishBalanceReport` — run the assay over a dial bin
`[lower, upper]`: read the slip and mass value, solve the calibration, check the sources balance, and
fill the report (`deviceG := calibration`). `motionResolved` = a positive slip with every part on the
motion face; `quantumGravityResolved` = that plus the sources balanced. -/
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

/-- `deviceG : ApparatusRatio` — the device's gravitational constant: the `deviceG` of the assay run over
`[1, 1000000]`. The little brass weight itself, `18/2132`. -/
def deviceG : ApparatusRatio :=
  (cavendishCooperElectron 1 1000000).deviceG

/-- `deviceG_is_eighteen_over_2132 : deviceG.numerator = 18 ∧ deviceG.denominator = 2132`.
**Proposition:** the device's gravity ratio is exactly eighteen over two thousand one hundred thirty-two
— numerator `18`, denominator `2132`. **Mechanism:** `⟨rfl, rfl⟩` — both conjuncts hold by `rfl`, i.e.
the kernel computes `deviceG` and each side is definitionally equal; exact, no float, no approximation.
**Squeeze role:** the FIRST facet PINNED — the gravity facet of the object fixed to an exact point, the
bracket collapsed to the single value `18/2132`. This is the device's own number, the reading of its own
apparatus, not Newton's specific constant. -/
theorem deviceG_is_eighteen_over_2132 :
    deviceG.numerator = 18 ∧ deviceG.denominator = 2132 := by
  exact ⟨rfl, rfl⟩

/-! ## Readouts — the assay figures (the pinned weight and its scalings)
Four `#eval`s: the full assay over `[1, 1000000]`, `deviceG` itself, `deviceG` to eighteen places, and
its inverse floor/remainder. The theorem above is the weight settled on the scale; these are the bench's
dials showing it. One facet fixed — the next facet, α, is bracketed (not pinned) next door. -/
#eval cavendishCooperElectron 1 1000000
#eval deviceG
#eval deviceG.scaledFloor (pow10 18)
#eval (deviceG.inverseFloor, deviceG.inverseRemainder)

end Measurement
