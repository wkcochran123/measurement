import Measurement.Episode27

/- MEANWHILE 28 -- PROXIMITY BREAK. The Cavendish cell gives a small-signal
calibration at separation 3. Move the tethered electron closer to the Cooper
pair and the same calibrated inverse-square law amplifies the slip:

  slip(distance) = G_device * source_mass_total * electron_mass * arm / distance^2.

At distance 3 this is the calibrated mass-triplet value. At distance 2 the dial
is already nonlinear. At distance 1 the Cooper-pair proximity channel ruptures:
the floor slip reaches the original separation squared, and the wheel wraps off
the mass face. That is the "things go nuts" line in apparatus units.
-/

/-! # Meanwhile 28 — proximity: the nearness facet, pinned then broken  (⊢…⊣ machinist's fit)

**The genre skin (⊢…⊣).** A machinist checks a fit with feeler gauges: a gap that holds within tolerance,
then binds. Slide the two parts together and read the fit.

**Object & facet.** This is the NEARNESS facet of the object Yang–Mills describes: how the apparatus reads
proximity, and where a paired reading gives. We describe the facet in the device's own exact terms; we
never open or solve Yang–Mills, and the last box stays wrapped.

**The squeeze.** The facet is PINNED at calibration — at the calibrated separation the slip floor sits
exactly on the mass triplet (`proximitySlipFloor cavendishSeparation = 2`, an exact `rfl`) — and it BREAKS
at unit distance, a distinct local event (`(proximityRead 1).pairBreaks = true`), with a positive floor
curvature between them (the fit tightens with a shape, not a straight ramp). The break is LOCAL: it
happens on THIS apparatus, at THIS regime's unit distance — not a universal law of proximity, and not a
real force switching on; that boundary is literal, not a disavowal.
-/

namespace Measurement

/-- `ProximityRegime` — the five fits of the proximity read: `far` (loose), `calibrated` (the snug
standard fit), `nonlinear` (tightening), `rupture` (the pair breaks), `contact` (zero distance). `Repr`,
`DecidableEq`. -/
inductive ProximityRegime where
  | far
  | calibrated
  | nonlinear
  | rupture
  | contact
deriving Repr, DecidableEq

/-- `proximitySlip? : Nat → Option ApparatusRatio` — the inverse-square slip at a whole distance: `none`
at distance 0 (contact, no gap to read); otherwise the calibrated numerator over
`deviceG.denominator * square distance`. The same law the Cavendish cell was calibrated at, amplifying as
the parts close. -/
def proximitySlip? : Nat -> Option ApparatusRatio
  | 0 => none
  | distance =>
      some
        { numerator :=
            deviceG.numerator * cavendishSourceMassTotal *
              tetheredElectronTestMass.magnitude * cavendishArm
          denominator := deviceG.denominator * square distance }

/-- `proximitySlipFloor (distance) : Nat` — the integer floor of `proximitySlip? distance` (`0` at
contact). The coarse slip reading. -/
def proximitySlipFloor (distance : Nat) : Nat :=
  match proximitySlip? distance with
  | none => 0
  | some slip => slip.floor

/-- `proximitySlipScaledAt18 (distance) : Nat` — the slip read to eighteen places (`0` at contact). -/
def proximitySlipScaledAt18 (distance : Nat) : Nat :=
  match proximitySlip? distance with
  | none => 0
  | some slip => slip.scaledFloor (readoutScale)

/-- `proximityRuptureThreshold : Nat` — where the fit gives: the original separation squared,
`square cavendishSeparation`. -/
def proximityRuptureThreshold : Nat :=
  square cavendishSeparation

/-- `proximityRegime (distance) (slipFloor) : ProximityRegime` — sort a reading into a fit: `contact` at
zero distance; `rupture` once the floor reaches the threshold; `calibrated` at the standard separation;
`nonlinear` once the floor climbs past one; else `far`. -/
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

/-- `ProximityRead` — one gap's read: the distance, predicted slip, floor (coarse and scaled), the wheel
face it lands on and whether that face moves, whether the pair `pairBreaks`, and the regime. -/
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

/-- `proximityRead (distance) : ProximityRead` — read one gap: slip, floor, regime, and face; `pairBreaks`
is `true` exactly when the regime is `rupture` or `contact` (the jaws have bound or met). -/
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

/-- `proximitySweepDistances : List Nat` — the distances swept as the parts close, `[5, 4, 3, 2, 1, 0]`. -/
def proximitySweepDistances : List Nat :=
  [5, 4, 3, 2, 1, 0]

/-- `proximityFloorCurvature : Int` — the second difference of the slip floor across distances 3, 2, 1
(`distanceSecondDifference`): how sharply the fit tightens as it closes. -/
def proximityFloorCurvature : Int :=
  distanceSecondDifference
    (proximitySlipFloor 3)
    (proximitySlipFloor 2)
    (proximitySlipFloor 1)

/-- `proximityScaledCurvatureAt18 : Int` — the same curvature on the scaled (eighteen-place) floors across
distances 3, 2, 1. -/
def proximityScaledCurvatureAt18 : Int :=
  distanceSecondDifference
    (proximitySlipScaledAt18 3)
    (proximitySlipScaledAt18 2)
    (proximitySlipScaledAt18 1)

/-- `ProximityBreakReport` — the fit log: the device-G, the calibrated distance, the masses and arm, the
rupture threshold, both curvatures, and the whole sweep of reads. -/
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

/-- `proximityBreakReport : ProximityBreakReport` — assemble the log: read every distance in the sweep,
with the curvatures and the rupture threshold. One bench's record of a fit closing to its break. -/
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

/-- `proximity_at_calibration_is_mass_triplet_value : proximitySlipFloor cavendishSeparation = 2`.
**Proposition:** at the calibrated separation the slip floor sits exactly on the mass triplet, `2`.
**Mechanism:** `rfl` — kernel-computed. **Squeeze role:** the nearness facet PINNED at calibration — the
regime fixed to an exact value where the fit is snug. -/
theorem proximity_at_calibration_is_mass_triplet_value :
    proximitySlipFloor cavendishSeparation = 2 := by
  rfl

/-- `proximity_floor_curvature_positive : 0 < proximityFloorCurvature`. **Proposition:** the floor
curvature across distances 3, 2, 1 is positive. **Mechanism:** `by decide`. **Squeeze role:** the fit
tightens with a shape — bowing upward as it closes, not a straight ramp. -/
theorem proximity_floor_curvature_positive :
    0 < proximityFloorCurvature := by
  decide

/-- `proximity_unit_distance_breaks_pair : (proximityRead 1).pairBreaks = true`. **Proposition:** at unit
distance the pair breaks. **Mechanism:** `rfl` — kernel-computed. **Squeeze role:** the LOCAL break — the
bracket gives at THIS regime's unit distance, on this apparatus; a fracture inside the ruled fit, never a
universal law of proximity. -/
theorem proximity_unit_distance_breaks_pair :
    (proximityRead 1).pairBreaks = true := by
  rfl

/-! ## Readout — the fit log
`#eval proximityBreakReport` prints the whole fit: the device-G, masses and arm, the rupture threshold,
both curvatures, and the sweep. The theorems above pin the regime and mark the break; this is the bench's
record. The next facet, the first slip, is bisected next door. -/
#eval proximityBreakReport

end Measurement
