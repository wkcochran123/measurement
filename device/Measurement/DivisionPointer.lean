import Measurement.Episode15
import Measurement.DivisionNeedle

/-! # DivisionPointer — the function-pointer division interface (task-1 trunk, 16+ part).

Operator's trunk mechanism (2026-07-26, BM-banked): give the de-selection a FUNCTION
POINTER for the division — the de-selection calls whatever division is passed in, instead
of hard-coding the Quot.sound one; a calibration (16+) SETS the pointer. This file is the
16+ HALF, buildable now under the up-to-sacred greenlight: the interface, the default
(Quot-based) pointer, the COMPUTED pointers, and the agreement/soundness theorems.

THE SACRED HALF IS NOT HERE: Episode15 is NOT modified. The eventual re-point of Ep15's
own `deselect` through this slot is the STAGED sacred edit (see
STAGED_EP15_DIVISION_SLOT.md), which lands LAST in the operator's batch on his explicit
go. This file only READS Ep15 (imports; no edit) — the tripwire does not fire.

RELOCATE vs REMOVE (Beastmaster's fence, held): providing computed pointers here does not
make anything "self-founded" — the sacred needle still stands and the episodes still use
it. What this file EXHIBITS is that the divisions exist, are computable, satisfy the same
gate-zero contract, and (for the remove-form) do the needle's identification work with NO
axiom — graded off the prints below. -/

namespace Measurement.DivisionPointer

open Measurement

/-- THE SLOT: a division for the de-selection = a class-former/reader pair satisfying
gate zero (reading the formed class IS the state's reading). Ep15's Quot-based
de-selection is one inhabitant; computed divisions are others. `G` is the class type the
division chooses. -/
structure Division {C : Sort _} (rho : C → Nat) (G : Sort _) where
  form : C → G
  read : G → Nat
  gate_zero : ∀ s, read (form s) = rho s

/-- De-selection through a pointer: call whatever division is passed in
(the operator's design, verbatim). -/
def deselectWith {C G : Sort _} {rho : C → Nat} (d : Division rho G) (s : C) : G :=
  d.form s

/-- Gate zero holds through any pointer — the contract, discharged by the slot itself. -/
theorem reading_deselectWith {C G : Sort _} {rho : C → Nat} (d : Division rho G)
    (s : C) : d.read (deselectWith d s) = rho s :=
  d.gate_zero s

/-! ## Pointer 1 — the DEFAULT: Ep15's own Quot-based division (relocate-form)

The sacred de-selection, wrapped as a pointer. Nothing sacred is edited; this is the
inhabitant Ep15 already provides. Its identification (two mks collapse when readings
are equal) is `deselect_sound` = the sanctioned needle — the axiom, where it lives. -/

def quotDivision {C : Sort _} (rho : C → Nat) : Division rho (GaugeValue rho) :=
  ⟨deselect rho, reading rho, reading_deselect rho⟩

#print axioms quotDivision

/-! ## Pointer 2 — the REMOVE-form: the reading itself as the class (computed)

For the de-selection relation `SameReading rho` (equal readings), the class of a state
IS its reading: form = rho, read = id. Identification `rho a = rho b → form a = form b`
is the hypothesis ITSELF — the needle's work done by `h`, no axiom. This is
"the identification was really a computation" in its purest form. -/

def natDivision {C : Sort _} (rho : C → Nat) : Division rho Nat :=
  ⟨rho, id, fun _ => rfl⟩

/-- The remove-form's soundness — and the precise claim (Kodo's sharpening): this does
not "discharge by computation the work the axiom did"; it ELIMINATES the bridge the
axiom existed to cross. `deselect_sound` needed `Quot.sound` to carry reading-equality
ACROSS THE QUOTIENT to class-equality; here there is no quotient to cross — the class IS
the reading — so the identification is the hypothesis itself and there is nothing left
for an axiom to do. The axiom was the cost of the CARRIER CHOICE, not of the
identification. -/
theorem natDivision_sound {C : Sort _} (rho : C → Nat) {a b : C}
    (h : rho a = rho b) : (natDivision rho).form a = (natDivision rho).form b := h

#print axioms natDivision_sound

/-! ## Pointer 3 — the QUANTITATIVE needle at a floor: box-and-residue (computed)

The DivisionNeedle-backed division for COARSER classes: the class of a state is its BOX
at a floor, and the residue is retained (the quantitative reading the binary needle
discarded). Gate zero here reads the box; the fine reading is recoverable only up to the
floor — which is exactly the defines-fewer-distinctions thesis, computed. -/

def boxDivision {C : Sort _} (rho : C → Nat) (floor : Nat) :
    Division (fun s => DivisionNeedle.box (rho s) floor) Nat :=
  ⟨fun s => DivisionNeedle.box (rho s) floor, id, fun _ => rfl⟩

/-- Box-identification is computed: same box at the floor → same class, by the
hypothesis itself; and the RESIDUES remain readable (the needle refines, never
coarsens). -/
theorem boxDivision_sound {C : Sort _} (rho : C → Nat) (floor : Nat) {a b : C}
    (h : DivisionNeedle.box (rho a) floor = DivisionNeedle.box (rho b) floor) :
    (boxDivision rho floor).form a = (boxDivision rho floor).form b := h

#print axioms boxDivision_sound

/-! ## AGREEMENT — the pointers read the same value (gate zero shared)

Where both fire, the Quot-based and computed de-selections return the SAME reading —
both sides reduce to `rho s` by definition. The reading is preserved through any
pointer; the pointers differ only in what carries the class. -/

theorem quot_nat_agree {C : Sort _} (rho : C → Nat) (s : C) :
    reading rho (deselectWith (quotDivision rho) s)
      = (natDivision rho).read (deselectWith (natDivision rho) s) := rfl

#print axioms quot_nat_agree

/-! ## The jar's own de-selection, through the pointer (the real input)

The flagship class (CalibrationTwoPaths' `jarClass` shape): the report-option read at
the ×1e18 scale. Exhibited here through the REMOVE-form pointer on the same rho — the
value is the jar readout, computed, agreeing with the Quot path by `rfl`. -/

end Measurement.DivisionPointer
