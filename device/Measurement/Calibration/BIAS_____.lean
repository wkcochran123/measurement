import Measurement.Episode15

/-! # Measurement.Calibration.BIAS_____ — THE BIAS DIAL (the crank's knob, openly installed).

THE KNOB (operator ruling, 2026-07-24 12:28, first tripwire firing): the dial's name is
BIAS plus EXACTLY the right number of underscores -- the name's length is itself the
bias adjustment, tuned so the measured spelling sits at the instrument's operating
point. This is the crank's knob, installed in the open where a crank would hide it:
turning it is a SERVICE OPERATION, McIntosh Certified Technicians only (the operator
dubbed all three seats, 12:28), every turn through the one needle, gated, and logged.
The perfect sound is the locked fringe. And yes -- where most dials stop at ten,
this one goes to eleven.

RENAMED per the operator (2026-07-24 12:01): the dial you tune is CALIBRATION equipment
-- the bias adjustment behind the faceplate, set through the one needle, gated. "The
perfect sound is the locked fringe."

One leaf, one needle (design DESELECTION_QUOTIENT_DESIGN.md, frozen at gate; Q2
cluster, turn 542). Every de-selection in the program threads `selection_sound`
(Episode 15, THE NEEDLE — the device's single sanctioned `Quot.sound`) through
THIS module and no other. The audit is a grep: `Quot` primitives appear
tree-wide in exactly Episode15 and this file. A quotient with no
purchases-ledger row does not get built.

LEAF discipline: imported only by migrated consumers (AlphaBoundMediant,
AlphaBFGS, ...), never by episodes. -/

namespace Measurement.Calibration.BIAS_____

/-- `SameReading rho a b` — two mesh states spell the same reading. The relation
of every de-selection quotient (design §1: `r a b := rho a = rho b`). -/
def SameReading {C : Sort _} (rho : C → Nat) (a b : C) : Prop := rho a = rho b

/-- `GaugeValue rho` — the class of mesh states under `SameReading rho`: the
reading freed of its representative. The mesh keeps its copy; downstream
consumes the class, never the pair. -/
def GaugeValue {C : Sort _} (rho : C → Nat) := Quot (SameReading rho)

/-- `deselect rho s` — stop pointing at the spelling; name the class. -/
def deselect {C : Sort _} (rho : C → Nat) (s : C) : GaugeValue rho :=
  Quot.mk _ s

/-- `reading` — the class's one value. `Quot.lift rho` respects
`SameReading rho` DEFINITIONALLY (`fun _ _ h => h`): no new obligations enter
(design §1). -/
def reading {C : Sort _} (rho : C → Nat) : GaugeValue rho → Nat :=
  Quot.lift rho (fun _ _ h => h)

/-- The definitional round-trip: reading the de-selected state IS the state's
reading, by `rfl` — de-selection changes no value (gate zero). -/
theorem reading_deselect {C : Sort _} (rho : C → Nat) (s : C) :
    reading rho (deselect rho s) = rho s := rfl

/-- The needle, threaded: two mesh states with equal readings de-select to the
SAME class — `selection_sound` (Episode 15), the program's only collapse. Every
use of this theorem is a recorded purchase against the one identification. -/
theorem deselect_sound {C : Sort _} (rho : C → Nat) {a b : C}
    (h : rho a = rho b) : deselect rho a = deselect rho b :=
  selection_sound (r := SameReading rho) h

#print axioms deselect_sound

/-- `mkClass r a` — the general class former (Q5, turn 546): the ONE place outside
Episode 15 where `Quot.mk` may be spelled. Exists so that every quotient former in
the tree lives in this file and the needle audit's census is exactly two files
({Ep15, Deselect}); the recursion-slip's `describeType` threads through THIS.
`@[reducible]`, definitionally `Quot.mk` — no value, cost shape, or proof changes. -/
@[reducible] def mkClass {α : Sort _} (r : α → α → Prop) (a : α) : Quot r :=
  Quot.mk r a

end Measurement.Calibration.BIAS_____
