import Measurement.Episode31

/- MEANWHILE 32 -- PUT THE ELECTRON IN ORBIT. The Cooper-pair source is now the
central body and the electron is the orbiting test body. The proximity law from
Episode28 supplies the radial pull; the circular-orbit condition cancels the
test mass:

  slip = G * M * m / r^2,
  m * v^2 / r = slip,
  v^2 = G * M / r.

In the normalized high-energy units from Episode30, the first radius with
v^2 <= 1 is the natural-unit orbit. The magnetic needle from Episode31 reads
the moving electron as `gain * v^2`.
-/

namespace Measurement

def ApparatusRatio.divNat (q : ApparatusRatio) (n : Nat) : ApparatusRatio :=
  { numerator := q.numerator
    denominator := q.denominator * n }

def ApparatusRatio.leOne (q : ApparatusRatio) : Bool :=
  q.numerator <= q.denominator

def ApparatusRatio.eqOne (q : ApparatusRatio) : Bool :=
  q.numerator = q.denominator

def ApparatusRatio.ceil (q : ApparatusRatio) : Nat :=
  (q.numerator + q.denominator - 1) / q.denominator

def cooperPairGravitationalParameter : ApparatusRatio :=
  deviceG.mulNat cavendishSourceMassTotal

def cooperElectronVelocitySquared (radius : Nat) : ApparatusRatio :=
  match radius with
  | 0 => { numerator := 0, denominator := 1 }
  | _ => cooperPairGravitationalParameter.divNat radius

def naturalUnitOrbitRadius : Nat :=
  cooperPairGravitationalParameter.ceil

inductive CooperElectronOrbitRegime where
  | contact
  | ruptured
  | superUnit
  | unitBoundary
  | boundSubunit
deriving Repr, DecidableEq

def cooperElectronOrbitRegime (radius : Nat) : CooperElectronOrbitRegime :=
  let proximity := proximityRead radius
  let velocitySquared := cooperElectronVelocitySquared radius
  if radius = 0 then
    .contact
  else if proximity.pairBreaks then
    .ruptured
  else if velocitySquared.eqOne then
    .unitBoundary
  else if velocitySquared.leOne then
    .boundSubunit
  else
    .superUnit

def orbitMagneticNeedleDeflection (radius : Nat) : ApparatusRatio :=
  (chargeMassNeedleGain cavendishChargeMassNormalization).mul
    (cooperElectronVelocitySquared radius)

structure CooperElectronOrbitRead where
  radius : Nat
  centralCooperMass : Nat
  electronMass : Nat
  radialSlip : ApparatusRatio
  radialSlipFloor : Nat
  radialSlipFace : CorridorFace
  pairBreaks : Bool
  velocitySquared : ApparatusRatio
  velocitySquaredScaledAt18 : Nat
  velocitySquaredFloor : Nat
  velocitySquaredFace : CorridorFace
  stableNaturalOrbit : Bool
  regime : CooperElectronOrbitRegime
  magneticNeedleDeflection : ApparatusRatio
  magneticNeedleDeflectionScaledAt18 : Nat
deriving Repr

def cooperElectronOrbitRead (radius : Nat) : CooperElectronOrbitRead :=
  let proximity := proximityRead radius
  let velocitySquared := cooperElectronVelocitySquared radius
  let regime := cooperElectronOrbitRegime radius
  let needle := orbitMagneticNeedleDeflection radius
  { radius := radius
    centralCooperMass := cavendishSourceMassTotal
    electronMass := tetheredElectronTestMass.magnitude
    radialSlip := proximity.predictedSlip.getD { numerator := 0, denominator := 1 }
    radialSlipFloor := proximity.slipFloor
    radialSlipFace := proximity.slipFace
    pairBreaks := proximity.pairBreaks
    velocitySquared := velocitySquared
    velocitySquaredScaledAt18 := velocitySquared.scaledFloor (pow10 18)
    velocitySquaredFloor := velocitySquared.floor
    velocitySquaredFace := CorridorFace.ofTurns velocitySquared.floor
    stableNaturalOrbit := !proximity.pairBreaks && velocitySquared.leOne
    regime := regime
    magneticNeedleDeflection := needle
    magneticNeedleDeflectionScaledAt18 := needle.scaledFloor (pow10 18) }

def cooperElectronOrbitSweep : List CooperElectronOrbitRead :=
  [3, 9, naturalUnitOrbitRadius, naturalUnitOrbitRadius + 1,
    2 * naturalUnitOrbitRadius].map cooperElectronOrbitRead

structure CooperElectronOrbitReport where
  gravitationalParameter : ApparatusRatio
  gravitationalParameterScaledAt18 : Nat
  naturalUnitRadius : Nat
  selectedOrbit : CooperElectronOrbitRead
  sweep : List CooperElectronOrbitRead
deriving Repr

def cooperElectronOrbitReport : CooperElectronOrbitReport :=
  { gravitationalParameter := cooperPairGravitationalParameter
    gravitationalParameterScaledAt18 :=
      cooperPairGravitationalParameter.scaledFloor (pow10 18)
    naturalUnitRadius := naturalUnitOrbitRadius
    selectedOrbit := cooperElectronOrbitRead naturalUnitOrbitRadius
    sweep := cooperElectronOrbitSweep }

theorem naturalUnitOrbitRadius_is_eighteen :
    naturalUnitOrbitRadius = 18 := by
  rfl

theorem natural_unit_orbit_is_stable :
    (cooperElectronOrbitRead naturalUnitOrbitRadius).stableNaturalOrbit = true := by
  rfl

theorem natural_unit_orbit_velocity_squared_is_one :
    (cooperElectronOrbitRead naturalUnitOrbitRadius).velocitySquared.numerator =
        (cooperElectronOrbitRead naturalUnitOrbitRadius).velocitySquared.denominator := by
  rfl

#eval cooperElectronOrbitReport

end Measurement
