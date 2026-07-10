import Measurement.Meanwhile22
import Measurement.Formalization.Search
import Measurement.Calibration.LeanCalibration

/-! # AlphaProbe — the Phase-0b seam (task `instrument`)

The α **barbell** joined in ONE building file: the structural ℕ-cost gauge (`Formalization`,
repaired in 0a) beside the phase face (`Meanwhile22`) beside the calibration surface
(`LeanCalibration`). Phase 0b welds the structural **rank** to the boot-calibrated **heartbeat**
through the gauge map's ×1000, grounding α as a ratio of naturals. **NO α ratio is computed here —
that is 0c, read blind.** Grade off the build.

GRADE (SPEC §8):
- **BUILT** (axiom-clean, `[]`): the structural rank ladder — `derivation_cost_eq_rank`, `inferred_cost = 36`.
- **DESIGN CONVENTION** (the gauge map): 1 paper work unit = 1000 internal heartbeats — Lean's standard
  internal/user heartbeat ratio (the SAME ×1000 my `Calibration/EKGBounded` uses as `budget * 1000`;
  `LeanCalibration` seals its own copy `private`). Made definitional here, in 16+, reading sacred only.
- **RESERVED for 0c** (blind, smooth Unruh-thermal floor per SPEC §5): the α reading — the fold-probe deficit /
  Thomas precession. Not here.
-/

namespace Measurement.AlphaProbe
open Measurement Measurement.Formalization Measurement.Calibration

/-! ## Wing 1 — the structural ℕ-cost gauge (BUILT, choice-free) -/

/-- The canonical derivation's structural cost is its rank, `36`. -/
example : derivation_inferred.cost = 36 := inferred_cost

/-- Every derivation's cost equals the rank of its stage — the flat serial gauge (`cost = rank`). -/
example {s : Stage} (d : Derivation s) : d.cost = Stage.rank s := derivation_cost_eq_rank d

/-! ## The gauge map (0b) — structural rank ↔ heartbeat via the ×1000 coefficient. -/

-- CHOICE(instrument 0b): the ×1000 is Lean's standard internal/user heartbeat ratio (the SAME coefficient
-- `Calibration/EKGBounded` uses as `budget * 1000`; `LeanCalibration` keeps its copy `private`). A DESIGN
-- CONVENTION, made definitional here in 16+ so the connection is graded off the build, not off prose. — Podo
def heartbeatCoefficient : Nat := 1000

/-- The gauge map: a structural rank (paper work units) read in internal-heartbeat units. -/
def heartbeatOfRank (r : Nat) : Nat := r * heartbeatCoefficient

/-- **0b — THE CONNECTION THEOREM.** The canonical derivation's structural cost (its rank = 36) welded to
its heartbeat gauge-reading through the ×1000 coefficient: `36` paper work units = `36000` internal
heartbeats. This grounds the α ratio as a genuine ratio of naturals — the precondition for reading α. -/
theorem rank_heartbeat_connection :
    heartbeatOfRank derivation_inferred.cost = 36000 := by
  unfold heartbeatOfRank heartbeatCoefficient
  rw [inferred_cost]

/-! ## Wing 2 — the phase face (the −i direction), staged for the 0c fold. -/
#check Measurement.QPhase
#check @Measurement.phaseRead

/-! ## Wing 3 — the calibration surface (sacred-in-spirit, read-only): the TRUE=TRUE floor. -/
#check @Measurement.Calibration.EKG.outgrown?
#eval measuredFloor                                            -- the machine's noise floor (Fact.Truth cost)
-- "above the floor" — a machine-dependent READING (graded as a reading, not a theorem):
#eval (decide (heartbeatOfRank 36 > measuredFloor) : Bool)     -- the canonical reading clears the floor

end Measurement.AlphaProbe
