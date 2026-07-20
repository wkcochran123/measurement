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

/-! # Meanwhile 32 — the orbit: the electron earns its room  (⌂ lodging-house tenancy) — MILESTONE

**The genre skin (⌂).** Back in Ep25 the electron lodged in not-zero "for the fun of it" — carried, not
earned, no room of its own. Here it signs for one: a stable orbit, a door with a number on it.

**Object & facet (MILESTONE — tracked-thread payoff #1).** This is the ORBIT facet of the object
Yang–Mills describes, and it is where the electron EARNS a distinguished room — the second independent
witness for box 1 that the naming (Ep25) could only assert. We describe the facet in the device's own
exact terms; we never open or solve Yang–Mills, and the last box stays wrapped.

**The squeeze (a PINNED point).** Set the electron orbiting the Cooper-pair body: `v² = G·M / r` (the test
body cancels). At the natural-unit radius the orbit's velocity² is fixed to EXACTLY one
(`velocitySquared.numerator = velocitySquared.denominator`, an exact `rfl`), the orbit is STABLE
(`stableNaturalOrbit = true`), and the radius is **18** — the number on the door.

**⚠️ Electron-scope fence (hardest here).** Every "electron" is the DEVICE'S OWN test body in its OWN orbit
model — NOT a physical electron, NOT a real atom, NOT a Bohr or hydrogen orbit, NOT real orbital mechanics.
The room is earned INSIDE our own construction. (The radius 18 is the same 18 as device-G's numerator — a
resonance inside our own units, nothing claimed of the world.)
-/

namespace Measurement

/-- `ApparatusRatio.divNat (q) (n) : ApparatusRatio` — divide a ratio by a whole number: denominator
`q.denominator * n`, numerator unchanged. Spreads the central pull over the radius. -/
def ApparatusRatio.divNat (q : ApparatusRatio) (n : Nat) : ApparatusRatio :=
  { numerator := q.numerator
    denominator := q.denominator * n }

/-- `ApparatusRatio.leOne (q) : Bool` — whether `q ≤ 1`, `q.numerator <= q.denominator`. -/
def ApparatusRatio.leOne (q : ApparatusRatio) : Bool :=
  q.numerator <= q.denominator

/-- `ApparatusRatio.eqOne (q) : Bool` — whether `q = 1` exactly, `q.numerator = q.denominator`. The
boundary condition of the earned room. -/
def ApparatusRatio.eqOne (q : ApparatusRatio) : Bool :=
  q.numerator = q.denominator

/-- `ApparatusRatio.ceil (q) : Nat` — the ceiling of `q`, `(q.numerator + q.denominator - 1) /
q.denominator`. Rounds up to the innermost whole radius. -/
def ApparatusRatio.ceil (q : ApparatusRatio) : Nat :=
  (q.numerator + q.denominator - 1) / q.denominator

/-- `cooperPairGravitationalParameter : ApparatusRatio` — the central body's draw, `G · sourceMassTotal`
(`deviceG.mulNat cavendishSourceMassTotal`). -/
def cooperPairGravitationalParameter : ApparatusRatio :=
  deviceG.mulNat cavendishSourceMassTotal

/-- `cooperElectronVelocitySquared (radius) : ApparatusRatio` — the circular-orbit speed² at a radius,
`G·M / radius` (the test body cancels); `0` at radius 0. -/
def cooperElectronVelocitySquared (radius : Nat) : ApparatusRatio :=
  match radius with
  | 0 => { numerator := 0, denominator := 1 }
  | _ => cooperPairGravitationalParameter.divNat radius

/-- `naturalUnitOrbitRadius : Nat` — the innermost whole radius where `v² ≤ 1`, the ceiling of the central
draw. The address of the earned room; its value is `18` (theorem below). -/
def naturalUnitOrbitRadius : Nat :=
  cooperPairGravitationalParameter.ceil

/-- `CooperElectronOrbitRegime` — the five ways the electron can sit at a radius: `contact` (on the body),
`ruptured` (the proximity pair broke), `superUnit` (too fast to stay), `unitBoundary` (v²=1, the earned
room), `boundSubunit` (settled, bound). `Repr`, `DecidableEq`. -/
inductive CooperElectronOrbitRegime where
  | contact
  | ruptured
  | superUnit
  | unitBoundary
  | boundSubunit
deriving Repr, DecidableEq

/-- `cooperElectronOrbitRegime (radius) : CooperElectronOrbitRegime` — sort a radius into a regime:
`contact` at 0; `ruptured` if the proximity pair breaks; `unitBoundary` if v²=1; `boundSubunit` if v²≤1;
else `superUnit`. -/
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

/-- `orbitMagneticNeedleDeflection (radius) : ApparatusRatio` — Ep31's needle reading the moving electron:
the needle gain times v² at that radius. The gauge follows the tenant into the room. -/
def orbitMagneticNeedleDeflection (radius : Nat) : ApparatusRatio :=
  (chargeMassNeedleGain cavendishChargeMassNormalization).mul
    (cooperElectronVelocitySquared radius)

/-- `CooperElectronOrbitRead` — one radius inspected: the radius, central and test masses, the radial slip
(and floor and face), whether the pair breaks, v² (coarse, scaled, by face), whether the orbit is a stable
natural room, the regime, and the needle deflection. -/
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

/-- `cooperElectronOrbitRead (radius) : CooperElectronOrbitRead` — inspect one radius: read the proximity
slip, v², regime, and needle; `stableNaturalOrbit = !pairBreaks && v² ≤ 1` (the room holds). -/
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

/-- `cooperElectronOrbitSweep : List CooperElectronOrbitRead` — a few radii around the natural-unit room:
`[3, 9, radius, radius+1, 2*radius]`. -/
def cooperElectronOrbitSweep : List CooperElectronOrbitRead :=
  [3, 9, naturalUnitOrbitRadius, naturalUnitOrbitRadius + 1,
    2 * naturalUnitOrbitRadius].map cooperElectronOrbitRead

/-- `CooperElectronOrbitReport` — the tenancy record: the central draw (scaled), the natural-unit radius,
the selected orbit's full inspection, and the sweep. -/
structure CooperElectronOrbitReport where
  gravitationalParameter : ApparatusRatio
  gravitationalParameterScaledAt18 : Nat
  naturalUnitRadius : Nat
  selectedOrbit : CooperElectronOrbitRead
  sweep : List CooperElectronOrbitRead
deriving Repr

/-- `cooperElectronOrbitReport : CooperElectronOrbitReport` — gather the record: the draw, the address, the
selected room inspected, and the sweep. -/
def cooperElectronOrbitReport : CooperElectronOrbitReport :=
  { gravitationalParameter := cooperPairGravitationalParameter
    gravitationalParameterScaledAt18 :=
      cooperPairGravitationalParameter.scaledFloor (pow10 18)
    naturalUnitRadius := naturalUnitOrbitRadius
    selectedOrbit := cooperElectronOrbitRead naturalUnitOrbitRadius
    sweep := cooperElectronOrbitSweep }

/-- `naturalUnitOrbitRadius_is_eighteen`.
**Proposition:** `naturalUnitOrbitRadius = 18`.
**Mechanism:** `rfl` — kernel-computed.
**Squeeze role:** the number on the door — the earned room's address, `18`. (The same 18 as device-G's
numerator: a resonance inside our own units, nothing claimed of the world.) -/
theorem naturalUnitOrbitRadius_is_eighteen :
    naturalUnitOrbitRadius = 18 := by
  rfl

/-- `natural_unit_orbit_is_stable`.
**Proposition:** `(cooperElectronOrbitRead naturalUnitOrbitRadius).stableNaturalOrbit = true`.
**Mechanism:** `rfl` — kernel-computed.
**Squeeze role:** the room HOLDS — the orbit at the natural-unit radius is stable. -/
theorem natural_unit_orbit_is_stable :
    (cooperElectronOrbitRead naturalUnitOrbitRadius).stableNaturalOrbit = true := by
  rfl

/-- `natural_unit_orbit_velocity_squared_is_one`.
**Proposition:** `(cooperElectronOrbitRead naturalUnitOrbitRadius).velocitySquared.numerator =
(cooperElectronOrbitRead naturalUnitOrbitRadius).velocitySquared.denominator` — i.e. v² = 1 at the room.
**Mechanism:** `rfl` — kernel-computed.
**Squeeze role:** the orbit's velocity² PINNED to exactly 1 — the room condition, the orbit facet fixed to
an exact point. Carried in Ep25, earned here. -/
theorem natural_unit_orbit_velocity_squared_is_one :
    (cooperElectronOrbitRead naturalUnitOrbitRadius).velocitySquared.numerator =
        (cooperElectronOrbitRead naturalUnitOrbitRadius).velocitySquared.denominator := by
  rfl

/-! ## Readout — the tenancy record
`#eval cooperElectronOrbitReport` prints the record: the central draw, the natural-unit address, the
selected room inspected, and the sweep. The theorems above pin the room (v²=1, stable, radius 18); the
electron has earned a room of its own — the second witness for box 1. The next facet, the Lorentz bracket,
is next door. -/
#eval cooperElectronOrbitReport

end Measurement
