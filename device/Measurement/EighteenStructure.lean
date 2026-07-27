import Measurement.Episode29
import Measurement.DivisionNeedle

/-! # EighteenStructure — task 3: the counted eighteen IS 2 × 9, structurally.

Kodo's earn-criterion: 18 = 2·9 must be STRUCTURAL (massValue(2) × separation²(9), the
known root), never a coincidental numeral factorization. The proof strategy is therefore
NOT "18 = 2·9 by arithmetic" (true and worthless) but: the calibration LAW's numerator is
`slip · sep²` BY DEFINITION for every measured slip (the ∀-form, the strong-form
discipline); the separation is EARNED as a coproduct cardinality and equals the fencepost
3; the assay's measured mass value is 2; and the quantitative needle reads the 2 back out
of the 18 with residue 0. The 2×9 is the definition's own shape wearing its measured
values — the factorization falls out, it is not imposed.

16+ leaf: imports Episode29 (the Ep26 Cavendish cone) + DivisionNeedle. No existing file
modified; jar untouched by construction; no self-founding claim (tier: task-3 exhibit). -/

namespace Measurement.EighteenStructure

open Measurement

/-! ## The law's shape — ∀-form, definitional

The calibration numerator IS measured-slip × separation², for EVERY slip — the
structure is the definition's, not this file's. -/

theorem calibration_shape (m : Nat) :
    (cavendishCalibration m).numerator = m * square cavendishSeparation := rfl

#print axioms calibration_shape

/-! ## The separation — earned, and it is the fencepost -/

/-- The separation is the EARNED SUM (coproduct cardinality, no postulated `+`) of the
box count and the electron box — definitionally. -/
theorem separation_is_earned :
    cavendishSeparation = earnedSum boxCount electronBox.val := rfl

/-- And it counts to THREE — the fencepost, again: the separation the coupling squares
is the same 3 the cycle closes at. -/
theorem separation_is_three : cavendishSeparation = 3 := by decide

/-- The separation squared is the NINE. -/
theorem separation_squared_is_nine : square cavendishSeparation = 9 := by decide

#print axioms separation_is_three

/-! ## The eighteen, structurally -/

/-- THE STRUCTURAL IDENTITY: the device's coupling numerator is the measured mass value
(2) times the separation squared (9) — stated through the REAL separation, not numerals:
`deviceG.numerator = 2 · sep²`. With `calibration_shape` (the ∀-form above), this pins
the assay's measured mass value to 2: the numerator is `m · 9` for the measured `m`, and
it reads 18. -/
theorem eighteen_is_mass_times_sep_squared :
    deviceG.numerator = 2 * square cavendishSeparation := by decide

/-- The corollary in numerals, for the record — carried by the structural identity
above, never standing alone. -/
theorem eighteen_is_two_times_nine : deviceG.numerator = 2 * 9 := by decide

#print axioms eighteen_is_mass_times_sep_squared

/-! ## The needle reads the mass back out

The quantitative needle (task 1's instrument) recovers the measured mass value from the
coupling: divide the eighteen by the separation-squared and the box is 2 with residue 0
— the coupling contains its mass value exactly, nothing left over. Axiom-free. -/

theorem needle_reads_mass_from_coupling :
    DivisionNeedle.divMod deviceG.numerator (square cavendishSeparation) = (2, 0) := by
  decide

#print axioms needle_reads_mass_from_coupling

/-! ## Not a coincidence — the shape survives any measured value

If the assay had measured any other mass value, the numerator would be that value times
the SAME nine — the 9 is the law's, the 2 is the measurement's. (Instances shown at 1
and 3; the ∀-form is `calibration_shape`.) -/

theorem shape_at_other_masses :
    (cavendishCalibration 1).numerator = 1 * 9
      ∧ (cavendishCalibration 3).numerator = 3 * 9 := by decide

#print axioms shape_at_other_masses

#eval s!"18 = massValue · sep²: deviceG.num = {deviceG.numerator}, sep = {cavendishSeparation}, sep² = {square cavendishSeparation}, needle reads (mass, residue) = {DivisionNeedle.divMod deviceG.numerator (square cavendishSeparation)}"

end Measurement.EighteenStructure
