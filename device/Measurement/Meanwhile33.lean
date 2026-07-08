import Measurement.Meanwhile32

/- MEANWHILE 33 -- LORENTZ BRACKETS THE ORBIT. The Newtonian-looking circular
orbit in Meanwhile32 sits exactly at `v^2 = 1`. Relativity refuses to let the
electron live there as an ordinary timelike circular orbit. The apparatus must
read a small undershoot/overshoot bracket around the unit boundary.

The wobble size is not external. It is the quantum-gravity needle gain from the
charge/mass accumulated slip:

  delta = |M - C| / (M + C).

The bracket is

  r_- = 18 - delta,
  r_0 = 18,
  r_+ = 18 + delta.

The lower side is super-unit (`v^2 > 1`), the middle is lightlike (`v^2 = 1`),
and the upper side is timelike (`v^2 < 1`) with finite Lorentz gamma.
-/

namespace Measurement

structure RationalRadius where
  numerator : Nat
  denominator : Nat
deriving Repr, DecidableEq

namespace RationalRadius

def scaledFloor (r : RationalRadius) (scale : Nat) : Nat :=
  r.numerator * scale / r.denominator

end RationalRadius

def orbitWobble : ApparatusRatio :=
  chargeMassNeedleGain cavendishChargeMassNormalization

def centerOrbitRadius : RationalRadius :=
  { numerator := naturalUnitOrbitRadius, denominator := 1 }

def lowerLorentzOrbitRadius : RationalRadius :=
  { numerator := naturalUnitOrbitRadius * orbitWobble.denominator - orbitWobble.numerator
    denominator := orbitWobble.denominator }

def upperLorentzOrbitRadius : RationalRadius :=
  { numerator := naturalUnitOrbitRadius * orbitWobble.denominator + orbitWobble.numerator
    denominator := orbitWobble.denominator }

def rationalOrbitVelocitySquared (radius : RationalRadius) : ApparatusRatio :=
  { numerator := cooperPairGravitationalParameter.numerator * radius.denominator
    denominator := cooperPairGravitationalParameter.denominator * radius.numerator }

def lorentzGammaSquared? (velocitySquared : ApparatusRatio) : Option ApparatusRatio :=
  if velocitySquared.numerator < velocitySquared.denominator then
    some
      { numerator := velocitySquared.denominator
        denominator := velocitySquared.denominator - velocitySquared.numerator }
  else
    none

inductive LorentzOrbitRegime where
  | superUnitUndershoot
  | lightlikeBoundary
  | timelikeOvershoot
deriving Repr, DecidableEq

def lorentzOrbitRegime (velocitySquared : ApparatusRatio) : LorentzOrbitRegime :=
  if velocitySquared.numerator = velocitySquared.denominator then
    .lightlikeBoundary
  else if velocitySquared.denominator < velocitySquared.numerator then
    .superUnitUndershoot
  else
    .timelikeOvershoot

structure LorentzOrbitRead where
  label : String
  radius : RationalRadius
  radiusScaledAt18 : Nat
  velocitySquared : ApparatusRatio
  velocitySquaredScaledAt18 : Nat
  velocitySquaredFloor : Nat
  velocitySquaredFace : CorridorFace
  gammaSquared? : Option ApparatusRatio
  gammaSquaredScaledAt18? : Option Nat
  magneticNeedleDeflection : ApparatusRatio
  magneticNeedleDeflectionScaledAt18 : Nat
  regime : LorentzOrbitRegime
deriving Repr

def lorentzOrbitRead (label : String) (radius : RationalRadius) : LorentzOrbitRead :=
  let velocitySquared := rationalOrbitVelocitySquared radius
  let gammaSquared? := lorentzGammaSquared? velocitySquared
  let needle :=
    (chargeMassNeedleGain cavendishChargeMassNormalization).mul velocitySquared
  { label := label
    radius := radius
    radiusScaledAt18 := radius.scaledFloor (pow10 18)
    velocitySquared := velocitySquared
    velocitySquaredScaledAt18 := velocitySquared.scaledFloor (pow10 18)
    velocitySquaredFloor := velocitySquared.floor
    velocitySquaredFace := CorridorFace.ofTurns velocitySquared.floor
    gammaSquared? := gammaSquared?
    gammaSquaredScaledAt18? :=
      match gammaSquared? with
      | none => none
      | some gammaSquared => some (gammaSquared.scaledFloor (pow10 18))
    magneticNeedleDeflection := needle
    magneticNeedleDeflectionScaledAt18 := needle.scaledFloor (pow10 18)
    regime := lorentzOrbitRegime velocitySquared }

structure LorentzOrbitBracketReport where
  centerRadius : Nat
  wobble : ApparatusRatio
  wobbleScaledAt18 : Nat
  undershoot : LorentzOrbitRead
  boundary : LorentzOrbitRead
  overshoot : LorentzOrbitRead
  radialWidthScaledAt18 : Nat
deriving Repr

def lorentzOrbitBracketReport : LorentzOrbitBracketReport :=
  let undershoot := lorentzOrbitRead "undershoot" lowerLorentzOrbitRadius
  let boundary := lorentzOrbitRead "unit-boundary" centerOrbitRadius
  let overshoot := lorentzOrbitRead "overshoot" upperLorentzOrbitRadius
  { centerRadius := naturalUnitOrbitRadius
    wobble := orbitWobble
    wobbleScaledAt18 := orbitWobble.scaledFloor (pow10 18)
    undershoot := undershoot
    boundary := boundary
    overshoot := overshoot
    radialWidthScaledAt18 :=
      overshoot.radiusScaledAt18 - undershoot.radiusScaledAt18 }

theorem lorentz_undershoot_is_super_unit :
    lorentzOrbitBracketReport.undershoot.regime =
      LorentzOrbitRegime.superUnitUndershoot := by
  rfl

theorem lorentz_boundary_is_lightlike :
    lorentzOrbitBracketReport.boundary.regime =
      LorentzOrbitRegime.lightlikeBoundary := by
  rfl

theorem lorentz_overshoot_is_timelike :
    lorentzOrbitBracketReport.overshoot.regime =
      LorentzOrbitRegime.timelikeOvershoot := by
  rfl

#eval lorentzOrbitBracketReport

end Measurement
