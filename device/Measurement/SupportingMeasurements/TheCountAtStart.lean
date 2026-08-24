-- TheCountAtStart.lean
--
-- The START platform's own receipt (physical-intuition book, Section 1;
-- role-inversion build: Kodo wrote "the count itself is settled on this
-- platform, and it rides free"; this leaf makes that literally true).
-- ZERO IMPORTS — this file sits at the ∅ platform with the braid's own
-- ground floor: nothing below it, nothing assumed. The count is the
-- coproduct-roster cardinality (addition earned via Sum, the standing
-- rule; the `+` operator never appears in the count itself).
--
-- NOT-CLAIMED: nothing here touches the number, the crossing, or any
-- uptown object. This is the one fact the downtown platform owns: a
-- separation of two boxes and the electron's counts to three — not two,
-- not four — and it costs no axioms at all.

namespace Measurement.TheCountAtStart

/-- Addition earned, not assumed: the roster of `Fin a ⊕ Fin b`, counted
by `List.length`. Same shape as the audit desk's `earnedSum`, re-minted
here at the zero-import floor so START holds its own receipt. -/
def countedSum (a b : Nat) : Nat :=
  ((List.range a).map Sum.inl ++ (List.range b).map Sum.inr : List (Nat ⊕ Nat)).length

/-- Two boxes, and the electron's box. -/
def theTwoBoxes : Nat := 2
def theElectronsBox : Nat := 1

/-- The separation, performed as a count at the platform. -/
def theSeparation : Nat := countedSum theTwoBoxes theElectronsBox

theorem the_count_is_settled_at_start : theSeparation = 3 := by decide

theorem and_it_is_not_two_and_not_four :
    theSeparation ≠ 2 ∧ theSeparation ≠ 4 := by decide

end Measurement.TheCountAtStart

#print axioms Measurement.TheCountAtStart.the_count_is_settled_at_start
#print axioms Measurement.TheCountAtStart.and_it_is_not_two_and_not_four
