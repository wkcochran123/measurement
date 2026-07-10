import Measurement.Episode42

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000
set_option allowUnsafeReducibility true

namespace Measurement

/-
__EPISODE 43__: _The Record, in the Apparatus's Own Words_

Episode42 wrote the first record directly, with its own `HasNullMode` and
`LedgerRecord`.  That proved the right fact but left Episode41's general
vocabulary -- `PhysicallyModeled`, `MetaphysicalRelativeTo` -- adjacent rather
than consumed.  This episode sews that seam: the same record, re-expressed
through the epistemic boundary of Episode41.

The bridge is thin and honest.  An apparatus class is "admissible exactly when
the form admits a null mode."  Under the anchor that fact is false (Episode42's
coercivity certificate), so the class is empty -- nothing realizes the
indicator, and the invariant is `MetaphysicalRelativeTo` it.  Without the anchor
the fact holds, so the class is total and the constant apparatus realizes the
indicator -- `PhysicallyModeled`.

Stated formally:
* `AnchoredNullModeClass` / `UnanchoredNullModeClass` gate apparatus admissibility
  on Episode42's null-mode facts.
* `anchored_nullMode_metaphysical` and `unanchored_nullMode_physical` cast the
  first record into Episode41's `MetaphysicalRelativeTo` / `PhysicallyModeled`.
* `first_record_in_apparatus_vocabulary` is `firstRecord` (Episode42) re-read in
  the apparatus boundary -- the same line of the ledger, in the instrument's own
  words.

Residue left:
This gates the class on the fact rather than computing the indicator from an
activity encoding inside `evaluate` -- that richer apparatus needs either a
`Decidable HasNullMode` or an activity-typed apparatus, the next refinement.
-/

/-- The indicator invariant: `1` means "a null mode is present". -/
def nullModeIndicator : Nat := 1

/-- Apparatuses admissible exactly when the anchored form admits a null mode.
By Episode42 it does not, so this class is empty. -/
def AnchoredNullModeClass : ApparatusClass :=
  fun _ => HasNullMode AnchoredRung.zero anchoredEnergy

/-- Apparatuses admissible exactly when the unanchored form admits a null mode.
By Episode42 it does, so this class is total. -/
def UnanchoredNullModeClass : ApparatusClass :=
  fun _ => HasNullMode Rung3.zero unanchoredEnergy

/-- The first record's metaphysical half, in Episode41's vocabulary: relative to
the anchored apparatus class, the null-mode indicator is unrealizable. -/
theorem anchored_nullMode_metaphysical :
    MetaphysicalRelativeTo AnchoredNullModeClass nullModeIndicator := by
  intro h
  obtain ⟨a, hC, _⟩ := h
  exact anchored_has_no_null_mode hC

/-- The first record's physical half, in Episode41's vocabulary: relative to the
unanchored apparatus class, the constant apparatus realizes the indicator. -/
theorem unanchored_nullMode_physical :
    PhysicallyModeled UnanchoredNullModeClass nullModeIndicator :=
  ⟨constApparatus nullModeIndicator, unanchored_has_null_mode, ⟨[], rfl⟩⟩

/-- `firstRecord` (Episode42), now spoken in the apparatus boundary of
Episode41: one invariant, metaphysical under the anchor, physical without it. -/
theorem first_record_in_apparatus_vocabulary :
    MetaphysicalRelativeTo AnchoredNullModeClass nullModeIndicator ∧
      PhysicallyModeled UnanchoredNullModeClass nullModeIndicator :=
  ⟨anchored_nullMode_metaphysical, unanchored_nullMode_physical⟩

end Measurement
