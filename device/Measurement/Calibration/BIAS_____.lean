import Measurement.Episode15

/-! # Measurement.Calibration.BIAS_____ — THE BIAS DIAL (the crank's knob; now a shell).

THE KNOB (operator ruling, 2026-07-24 12:28, first tripwire firing): the dial's name is
BIAS plus EXACTLY the right number of underscores -- the name's length is itself the
bias adjustment, tuned so the measured spelling sits at the instrument's operating
point. This is the crank's knob, installed in the open where a crank would hide it:
turning it is a SERVICE OPERATION, McIntosh Certified Technicians only (the operator
dubbed all three seats, 12:28), every turn through the one needle, gated, and logged.
The perfect sound is the locked fringe. And yes -- where most dials stop at ten,
this one goes to eleven.

THE SHELL (single-needle consolidation, JAR_SINGLE_NEEDLE_DESIGN.md, operator
green-lit 14:19): the former now lives in Episode 15 beside the needle it threads —
Fact.SAME's home, the operator's stated reason. This file keeps the KNOB (the module's
NAME is the dial) and every importer's spelling, as pure re-exports: ZERO `Quot`
spelling below — the needle census is ONE code site, {Episode15}. -/

namespace Measurement.Calibration.BIAS_____

/-- Re-export: the de-selection relation (Episode 15's). -/
abbrev SameReading {C : Sort _} (rho : C → Nat) (a b : C) : Prop :=
  Measurement.SameReading rho a b

/-- Re-export: the class of mesh states (Episode 15's). -/
abbrev GaugeValue {C : Sort _} (rho : C → Nat) := Measurement.GaugeValue rho

/-- Re-export: the de-selection former (Episode 15's). -/
abbrev deselect {C : Sort _} (rho : C → Nat) (s : C) : GaugeValue rho :=
  Measurement.deselect rho s

/-- Re-export: the class's one value (Episode 15's). -/
abbrev reading {C : Sort _} (rho : C → Nat) : GaugeValue rho → Nat :=
  Measurement.reading rho

/-- Re-export: gate zero as a theorem (Episode 15's). -/
theorem reading_deselect {C : Sort _} (rho : C → Nat) (s : C) :
    reading rho (deselect rho s) = rho s :=
  Measurement.reading_deselect rho s

/-- Re-export: the needle's collapse (Episode 15's). -/
theorem deselect_sound {C : Sort _} (rho : C → Nat) {a b : C}
    (h : rho a = rho b) : deselect rho a = deselect rho b :=
  Measurement.deselect_sound rho h

/-- Re-export: the general class former (Episode 15's). -/
abbrev mkClass {α : Sort _} (r : α → α → Prop) (a : α) : Quot r :=
  Measurement.mkClass r a

end Measurement.Calibration.BIAS_____
