import Measurement.Episode32

/- MEANWHILE 33 -- LORENTZ BRACKETS THE ORBIT. The Newtonian-looking circular
orbit in Episode32 sits exactly at `v^2 = 1`. Relativity refuses to let the
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

/-! # Meanwhile 33 — the Lorentz bracket: the lightlike crest between two slopes  (△ continental divide)

**The genre skin (△).** A watershed crest: draw the radius in and you fall down one slope, let it out and
you fall down the other; the crest itself is the divide. A raindrop on the crest is balanced.

**Object & facet.** This is the LORENTZ / lightlike-boundary facet of the object Yang–Mills describes: the
orbit's boundary between its two slopes. We describe the facet in the device's own exact terms; we never
open or solve Yang–Mills, and the last box stays wrapped.

**The squeeze (a three-regime BRACKET).** The orbit is sorted into three regimes and the crest is bracketed
between two slopes: draw the radius in by a wobble `delta = |M - C| / (M + C)` and the speed climbs past
unit — the UNDERSHOOT (super-unit) slope; let it out and the speed falls below unit — the OVERSHOOT
(timelike) slope; the crest at radius 18 exactly is the LIGHTLIKE boundary. Two slopes pin one crest, all
decided by `rfl`.

**⚠️ Fence.** "lightlike," "timelike," "super-unit" are the device's OWN regime labels for where its own
orbit sits relative to its own unit — NOT special relativity, NOT a real light cone, NOT spacetime
causality, NOT a speed-of-light limit, NOT a photon (literal, not a disavowal). And the electron crossing
the bracket is still the device's own test body (carried from Ep32).
-/

namespace Measurement

/-- `RationalRadius` — a radius as an exact `numerator`/`denominator` fraction (`Repr`, `DecidableEq`).
Fine enough to step either side of the crest without rounding across it. -/
structure RationalRadius where
  numerator : Nat
  denominator : Nat
deriving Repr, DecidableEq

namespace RationalRadius

/-- `RationalRadius.scaledFloor (r) (scale) : Nat` — `r` read to `scale` fixed-point units,
`r.numerator * scale / r.denominator`. -/
def scaledFloor (r : RationalRadius) (scale : Nat) : Nat :=
  r.numerator * scale / r.denominator

end RationalRadius

/-- `orbitWobble : ApparatusRatio` — how far to step off the crest: the charge/mass needle gain
`|M - C| / (M + C)` (from Ep31). -/
def orbitWobble : ApparatusRatio :=
  chargeMassNeedleGain cavendishChargeMassNormalization

/-- `centerOrbitRadius : RationalRadius` — the crest, radius `18/1` (the natural-unit radius). -/
def centerOrbitRadius : RationalRadius :=
  { numerator := naturalUnitOrbitRadius, denominator := 1 }

/-- `lowerLorentzOrbitRadius : RationalRadius` — one step IN, `18 - wobble` (as an exact fraction over the
wobble's denominator). The undershoot radius. -/
def lowerLorentzOrbitRadius : RationalRadius :=
  { numerator := naturalUnitOrbitRadius * orbitWobble.denominator - orbitWobble.numerator
    denominator := orbitWobble.denominator }

/-- `upperLorentzOrbitRadius : RationalRadius` — one step OUT, `18 + wobble`. The overshoot radius. -/
def upperLorentzOrbitRadius : RationalRadius :=
  { numerator := naturalUnitOrbitRadius * orbitWobble.denominator + orbitWobble.numerator
    denominator := orbitWobble.denominator }

/-- `rationalOrbitVelocitySquared (radius) : ApparatusRatio` — v² at a rational radius, the central draw
over the radius (`cooperPairGravitationalParameter.numerator * radius.denominator`, over
`cooperPairGravitationalParameter.denominator * radius.numerator`). -/
def rationalOrbitVelocitySquared (radius : RationalRadius) : ApparatusRatio :=
  { numerator := cooperPairGravitationalParameter.numerator * radius.denominator
    denominator := cooperPairGravitationalParameter.denominator * radius.numerator }

/-- `lorentzGammaSquared? (velocitySquared) : Option ApparatusRatio` — defined ONLY on the timelike slope:
when v² < 1 it returns one over (one minus v²) (denominator over `denominator - numerator`); on the crest
or the super-unit slope there is no such quantity, so `none`. -/
def lorentzGammaSquared? (velocitySquared : ApparatusRatio) : Option ApparatusRatio :=
  if velocitySquared.numerator < velocitySquared.denominator then
    some
      { numerator := velocitySquared.denominator
        denominator := velocitySquared.denominator - velocitySquared.numerator }
  else
    none

/-- `LorentzOrbitRegime` — the three regimes of the bracket: `superUnitUndershoot`, `lightlikeBoundary`,
`timelikeOvershoot`. `Repr`, `DecidableEq`. -/
inductive LorentzOrbitRegime where
  | superUnitUndershoot
  | lightlikeBoundary
  | timelikeOvershoot
deriving Repr, DecidableEq

/-- `lorentzOrbitRegime (velocitySquared) : LorentzOrbitRegime` — sort a v² into a regime: `= 1` →
`lightlikeBoundary` (the crest); `> 1` → `superUnitUndershoot`; `< 1` → `timelikeOvershoot`. -/
def lorentzOrbitRegime (velocitySquared : ApparatusRatio) : LorentzOrbitRegime :=
  if velocitySquared.numerator = velocitySquared.denominator then
    .lightlikeBoundary
  else if velocitySquared.denominator < velocitySquared.numerator then
    .superUnitUndershoot
  else
    .timelikeOvershoot

/-- `LorentzOrbitRead` — one station on the divide: its label and radius (scaled), v² (coarse, scaled, by
face), the timelike gamma² if there is one, the needle deflection, and which regime it fell in. -/
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

/-- `lorentzOrbitRead (label) (radius) : LorentzOrbitRead` — read one radius: v², its gamma² (only on the
timelike slope), the needle, and the regime. One survey station on the crest or a slope. -/
def lorentzOrbitRead (label : String) (radius : RationalRadius) : LorentzOrbitRead :=
  let velocitySquared := rationalOrbitVelocitySquared radius
  let gammaSquared? := lorentzGammaSquared? velocitySquared
  let needle :=
    (chargeMassNeedleGain cavendishChargeMassNormalization).mul velocitySquared
  { label := label
    radius := radius
    radiusScaledAt18 := radius.scaledFloor (readoutScale)
    velocitySquared := velocitySquared
    velocitySquaredScaledAt18 := velocitySquared.scaledFloor (readoutScale)
    velocitySquaredFloor := velocitySquared.floor
    velocitySquaredFace := CorridorFace.ofTurns velocitySquared.floor
    gammaSquared? := gammaSquared?
    gammaSquaredScaledAt18? :=
      match gammaSquared? with
      | none => none
      | some gammaSquared => some (gammaSquared.scaledFloor (readoutScale))
    magneticNeedleDeflection := needle
    magneticNeedleDeflectionScaledAt18 := needle.scaledFloor (readoutScale)
    regime := lorentzOrbitRegime velocitySquared }

/-- `LorentzOrbitBracketReport` — the three-panel survey: the crest radius, the wobble, the undershoot /
boundary / overshoot reads, and the radial width between the outer two. -/
structure LorentzOrbitBracketReport where
  centerRadius : Nat
  wobble : ApparatusRatio
  wobbleScaledAt18 : Nat
  undershoot : LorentzOrbitRead
  boundary : LorentzOrbitRead
  overshoot : LorentzOrbitRead
  radialWidthScaledAt18 : Nat
deriving Repr

/-- `lorentzOrbitBracketReport : LorentzOrbitBracketReport` — read all three at once: undershoot at the
lower radius, boundary at the crest, overshoot at the upper — the whole divide, a slope on each side of the
crest. -/
def lorentzOrbitBracketReport : LorentzOrbitBracketReport :=
  let undershoot := lorentzOrbitRead "undershoot" lowerLorentzOrbitRadius
  let boundary := lorentzOrbitRead "unit-boundary" centerOrbitRadius
  let overshoot := lorentzOrbitRead "overshoot" upperLorentzOrbitRadius
  { centerRadius := naturalUnitOrbitRadius
    wobble := orbitWobble
    wobbleScaledAt18 := orbitWobble.scaledFloor (readoutScale)
    undershoot := undershoot
    boundary := boundary
    overshoot := overshoot
    radialWidthScaledAt18 :=
      overshoot.radiusScaledAt18 - undershoot.radiusScaledAt18 }

/-- `lorentz_undershoot_is_super_unit`.
**Proposition:** `lorentzOrbitBracketReport.undershoot.regime = LorentzOrbitRegime.superUnitUndershoot`.
**Mechanism:** `rfl` — kernel-computed.
**Squeeze role:** one slope of the bracket — the undershoot point is super-unit, below the crest. -/
theorem lorentz_undershoot_is_super_unit :
    lorentzOrbitBracketReport.undershoot.regime =
      LorentzOrbitRegime.superUnitUndershoot := by
  rfl

/-- `lorentz_boundary_is_lightlike`.
**Proposition:** `lorentzOrbitBracketReport.boundary.regime = LorentzOrbitRegime.lightlikeBoundary`.
**Mechanism:** `rfl` — kernel-computed.
**Squeeze role:** the CREST, bracketed between the two slopes — the centerpiece of the bracket, the
lightlike boundary caught between super-unit and timelike. -/
theorem lorentz_boundary_is_lightlike :
    lorentzOrbitBracketReport.boundary.regime =
      LorentzOrbitRegime.lightlikeBoundary := by
  rfl

/-- `lorentz_overshoot_is_timelike`.
**Proposition:** `lorentzOrbitBracketReport.overshoot.regime = LorentzOrbitRegime.timelikeOvershoot`.
**Mechanism:** `rfl` — kernel-computed.
**Squeeze role:** the other slope — the overshoot point is timelike, above the crest. Two slopes pinning
one crest. -/
theorem lorentz_overshoot_is_timelike :
    lorentzOrbitBracketReport.overshoot.regime =
      LorentzOrbitRegime.timelikeOvershoot := by
  rfl

/-! ## Readout — the three-panel survey
`#eval lorentzOrbitBracketReport` prints the whole divide: the crest, the wobble, the three stations
(undershoot / boundary / overshoot), and the radial width. The theorems above bracket the lightlike crest
between its two slopes. The next facet, the Dirac weak form, is next door. -/
#eval lorentzOrbitBracketReport

end Measurement
