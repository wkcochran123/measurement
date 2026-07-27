import Measurement.Episode40
import Measurement.Episode33
import Measurement.Episode35

/-! # ReadoutFloors — task 5: the calibration REGISTRY of every quantization floor.

**REGISTRY, NOT RELOCATION** (Beastmaster requirement 3, both chairs' (B) ruling, the
operator's default): the floors are HOME where their types live — Lean's import DAG
binds `ApparatusRatio.floor` to `ApparatusRatio`'s file, and a physical move would be a
jar-cone refactor spending byte-identity risk on a file-location change. THIS file is
the DECLARED CONVENTION LAYER: the single authoritative index of every quantization
choice, each entry re-exported with a machine-checked rfl-identity to its home
definition (requirement 2 — value-preserving BY CONSTRUCTION, per floor). If the
operator's "MOVE" meant physical relocation, option (A) schedules into the jar-cone
window and this registry either remains the index or is superseded; nothing here blocks
that.

**COUNT RECONCILIATION** (requirement 1 — the census is authoritative, and the count is
exact, not approximate): the 2026-07-22 audit said "~8 readout floors." The full census
below is TWELVE named definitions, and they reconcile as **7 CHOSEN + 1 FORCED + 4
DERIVED-THROUGH = 12**: the audit's ~8 estimated the CHOSEN quantization conventions
(exact count: SEVEN — the scale and the six rounding/scale conventions); the census
additionally registers the one structurally-forced helper (`pow10`) and the four
derived readings that read *through* a convention (`alphaCellFloor`,
`proximitySlipFloor`, `rationalSlipFloor`, `rationalSlipFloor?`). Nothing is excluded;
every floor-shaped definition in the episode tree is registered and classified.

**CLASSIFICATION** (requirement 3): each entry is marked
- CHOSEN — a quantization convention (a genuine choice: the scale, the rounding
  direction); a different convention would read differently; or
- FORCED — structurally determined, not a free choice (helper arithmetic); or
- DERIVED-THROUGH — a measurement read through a CHOSEN convention (the convention
  content is the floor step; the rest is measured).

Jar: new leaf, zero edits to any existing file; untouched by construction. -/

namespace Measurement.Calibration.ReadoutFloors

open Measurement

/-! ## 1–2 · the scale (Ep25) -/

/-- FORCED (helper): powers of ten — arithmetic, not a convention. -/
def pow10 : Nat → Nat := Measurement.pow10
theorem pow10_id : pow10 = Measurement.pow10 := rfl

/-- CHOSEN: the readout scale — EIGHTEEN decimal places is the display convention the
whole instrument reads at; a different scale would display differently. -/
def readoutScale : Nat := Measurement.readoutScale
theorem readoutScale_id : readoutScale = Measurement.readoutScale := rfl
theorem readoutScale_is_ten_to_eighteen : readoutScale = 10 ^ 18 := by decide

/-! ## 3–5 · the ratio floors (Ep26) -/

/-- CHOSEN: round-toward-zero integer readout of a ratio (floor, not ceiling — a
rounding-direction convention). -/
def ratioFloor : ApparatusRatio → Nat := ApparatusRatio.floor
theorem ratioFloor_id : ratioFloor = ApparatusRatio.floor := rfl

/-- CHOSEN: the reciprocal's floor (same rounding convention, on 1/q). -/
def ratioInverseFloor : ApparatusRatio → Nat := ApparatusRatio.inverseFloor
theorem ratioInverseFloor_id : ratioInverseFloor = ApparatusRatio.inverseFloor := rfl

/-- CHOSEN: scale-then-floor (the scale and the rounding, composed). -/
def ratioScaledFloor : ApparatusRatio → Nat → Nat := ApparatusRatio.scaledFloor
theorem ratioScaledFloor_id : ratioScaledFloor = ApparatusRatio.scaledFloor := rfl

/-! ## 6 · the bracket index (Ep27) -/

/-- DERIVED-THROUGH: the ruling just below the target — a bracket INDEX computed from
measured quantities (`apparatusAlphaTarget`, `deviceG`) through the floor convention;
the convention content is the integer division's round-down. -/
def alphaCellFloor : Nat := Measurement.alphaCellFloor
theorem alphaCellFloor_id : alphaCellFloor = Measurement.alphaCellFloor := rfl

/-! ## 7 · the slip floor (Ep28) -/

/-- DERIVED-THROUGH: the slip at a distance, read through the floor convention. -/
def proximitySlipFloor : Nat → Nat := Measurement.proximitySlipFloor
theorem proximitySlipFloor_id :
    proximitySlipFloor = Measurement.proximitySlipFloor := rfl

/-! ## 8–9 · the rational-distance floors (Ep29) -/

/-- CHOSEN: scale-then-floor on a rational distance (the same scale/rounding pair, on
the distance carrier). -/
def distanceScaledFloor : RationalDistance → Nat → Nat := RationalDistance.scaledFloor
theorem distanceScaledFloor_id :
    distanceScaledFloor = RationalDistance.scaledFloor := rfl

/-- DERIVED-THROUGH: the rational slip's integer floor (a measured slip read through
the rounding convention). -/
def rationalSlipFloor : RationalDistance → Nat := Measurement.rationalSlipFloor
theorem rationalSlipFloor_id :
    rationalSlipFloor = Measurement.rationalSlipFloor := rfl

/-! ## 10 · the radius floor (Ep33) -/

/-- CHOSEN: scale-then-floor on a rational radius (the convention pair, on the radius
carrier). -/
def radiusScaledFloor : RationalRadius → Nat → Nat := RationalRadius.scaledFloor
theorem radiusScaledFloor_id :
    radiusScaledFloor = RationalRadius.scaledFloor := rfl

/-! ## 11 · the guarded slip floor (Ep35) -/

/-- DERIVED-THROUGH: the slip floor with its domain guard (`Option` — `none` off-domain);
the same convention, refusing rather than distorting outside its domain. -/
def rationalSlipFloor? : RationalDistance → Option Nat := Measurement.rationalSlipFloor?
theorem rationalSlipFloor?_id :
    rationalSlipFloor? = Measurement.rationalSlipFloor? := rfl

/-! ## 12 · the inverse readout (Ep40, totalized) -/

/-- CHOSEN: the 1/α readout at a scale — routed through the projective reciprocal
(Batch 2) so the α = 0 pole is an explicit marker, never a silent zero; byte-identical
to the pre-totalization form by Ep40's own `inverseScaledFloor_eq` (2a-verified
axiom-free). -/
def inverseScaledFloor : ApparatusRatio → Nat → Nat := ApparatusRatio.inverseScaledFloor
theorem inverseScaledFloor_id :
    inverseScaledFloor = ApparatusRatio.inverseScaledFloor := rfl

#print axioms readoutScale_is_ten_to_eighteen
#print axioms ratioFloor_id
#print axioms inverseScaledFloor_id

#eval s!"registry: 12 floors indexed = 7 chosen + 1 forced + 4 derived-through (the audit's ~8 estimated the 7 chosen); readoutScale = {readoutScale}"

end Measurement.Calibration.ReadoutFloors
