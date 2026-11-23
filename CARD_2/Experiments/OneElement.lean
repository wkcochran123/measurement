/-
The one element, counted two ways.

This file stands beside the device and is built apart: `lake build Experiments.OneElement`.  Nothing in `Measurement`
imports it.  It defines no inductive.

The author's, 20 November 2026 (declared): bring the single element in.  There are two counting maps from it to the
regular fields.  One is adding things to the element, and it leads to multiplication.  The other is collecting
elements, and it leads to addition and through addition to multiplication.  The device is that the two routes should
be equal to multiplication; these are how the two routes divide from the truth.

Card 7 has the single element as a set with a distinguished point, its dimension the number of its other points.  On
the device that is the Area: the tree is the point, and the cells are the others.  Episode 13 already has both
routes.  Collecting is the reader of a tape, a cell for every mark.  Adding to the element is `raised`, the element
each for each with itself once for every mark; the device's scale is made that way.  What is new here is only the two
set side by side.  That these are the two maps the author means is the reading made in the writing.
-/
import Measurement.Episode13

namespace Measurement
open readers_experience the_table

--| THE TWO ROUTES.  A tape of marks is handed in.  Collected: a cell for every mark.  Added to an element: the element each
--| for each with itself, once for every mark.
def collected (tape : List FACT) : Area := the_area_of_a_tape_in_blanks_is tape
def added_to (element : Area) (tape : List FACT) : Area := raised element (the_area_of_a_tape_in_blanks_is tape)

theorem collected_is_the_length (tape : List FACT) : compute_the_area_of (collected tape) = tape.length :=
  the_area_of_a_tape_in_blanks_is_the_tapes_length tape

theorem added_to_is_the_element_raised_to_the_length (element : Area) (tape : List FACT) :
    compute_the_area_of (added_to element tape) = compute_the_area_of element ^ tape.length := by
  rw [added_to, raised_raises, the_area_of_a_tape_in_blanks_is_the_tapes_length]

--| ONE TAPE AFTER ANOTHER.  Collected, the two are beside each other: addition.  Added to the element, the two are each for
--| each: multiplication.  The same thing done to the tape, and two things done to the count.
theorem collected_one_tape_after_another_is_beside (this that : List FACT) :
    compute_the_area_of (collected (this ++ that)) = compute_the_area_of (collected this + collected that) := by
  rw [palm_the_middle_card_adds, collected_is_the_length, collected_is_the_length, collected_is_the_length, List.length_append]

theorem added_one_tape_after_another_is_each_for_each (element : Area) (this that : List FACT) :
    compute_the_area_of (added_to element (this ++ that)) = compute_the_area_of (added_to element this * added_to element that) := by
  rw [false_shuffle_multiplies, added_to_is_the_element_raised_to_the_length,
    added_to_is_the_element_raised_to_the_length, added_to_is_the_element_raised_to_the_length, List.length_append, Nat.pow_add]

--| COLLECTING REACHES MULTIPLICATION THROUGH ADDITION.  The one tape, once for every mark of the other, one after another.
def once_for_every_mark : List FACT → List FACT → List FACT
  | [],        _    => []
  | _ :: rest, tape => tape ++ once_for_every_mark rest tape

theorem once_for_every_mark_is_as_long_as_the_one_by_the_other (marks tape : List FACT) :
    (once_for_every_mark marks tape).length = marks.length * tape.length := by
  induction marks with
  | nil => simp only [once_for_every_mark, List.length_nil, Nat.zero_mul]
  | cons _ rest ih => simp only [once_for_every_mark, List.length_append, List.length_cons, ih, Nat.succ_mul]; omega

theorem collected_once_for_every_mark_is_each_for_each (marks tape : List FACT) :
    compute_the_area_of (collected (once_for_every_mark marks tape)) = compute_the_area_of (collected marks * collected tape) := by
  rw [false_shuffle_multiplies, collected_is_the_length, collected_is_the_length, collected_is_the_length,
    once_for_every_mark_is_as_long_as_the_one_by_the_other]

--| AND THE OTHER ROUTE MEETS IT THERE.  Added to the element, and what came of it added to again, is the element added to
--| once, along the tape that collecting made by multiplication.  So the two routes arrive at one multiplication: the one has
--| it at once, and the other by way of beside.
theorem added_to_and_added_to_again_is_added_to_along_the_product (element : Area) (marks tape : List FACT) :
    compute_the_area_of (added_to (added_to element tape) marks) = compute_the_area_of (added_to element (once_for_every_mark marks tape)) := by
  rw [added_to_is_the_element_raised_to_the_length, added_to_is_the_element_raised_to_the_length,
    added_to_is_the_element_raised_to_the_length, once_for_every_mark_is_as_long_as_the_one_by_the_other,
    Nat.mul_comm marks.length, Nat.pow_mul]

--| HOW THE TWO ROUTES DIVIDE FROM THE TRUTH.  With no mark at all, collecting has nothing and adding has the one cell.  They
--| leave the empty tape as nothing and as one.
theorem with_no_mark_the_one_has_nothing_and_the_other_has_one (element : Area) :
    compute_the_area_of (collected []) = 0 ∧ compute_the_area_of (added_to element []) = 1 := by
  rw [collected_is_the_length, added_to_is_the_element_raised_to_the_length]; exact ⟨rfl, rfl⟩

--| OVER THE ONE ELEMENT.  Added to an element of one cell, every tape is one cell.  Collected, it is as many as its marks.
theorem added_to_the_one_cell_every_tape_is_one_cell (element : Area) (one_cell : compute_the_area_of element = 1) (tape : List FACT) :
    compute_the_area_of (added_to element tape) = 1 := by
  rw [added_to_is_the_element_raised_to_the_length, one_cell, Nat.one_pow]

--| Five truths in a row.  By the one route they are five; by the other, one.
theorem five_truths_are_five_collected_and_one_added :
    compute_the_area_of (collected [FACT.Truth, FACT.Truth, FACT.Truth, FACT.Truth, FACT.Truth]) = 5
      ∧ compute_the_area_of (added_to ast₁ [FACT.Truth, FACT.Truth, FACT.Truth, FACT.Truth, FACT.Truth]) = 1 :=
  ⟨collected_is_the_length _, added_to_the_one_cell_every_tape_is_one_cell ast₁ rfl _⟩

--| So over the one element the route by adding does not return how many marks there were: any two tapes read alike.
theorem added_to_the_one_cell_any_two_tapes_read_alike (this that : List FACT) :
    compute_the_area_of (added_to ast₁ this) = compute_the_area_of (added_to ast₁ that) := by
  rw [added_to_the_one_cell_every_tape_is_one_cell ast₁ rfl, added_to_the_one_cell_every_tape_is_one_cell ast₁ rfl]

--| THE TWO ROUTES JOINED.  Collect, not a cell for every mark, but for every mark what the element had been added to before
--| it: the element's own way of counting the tape.
def collected_as_the_element_counts (element : Area) : List FACT → Area
  | []        => ast₀
  | _ :: rest => added_to element rest + collected_as_the_element_counts element rest

theorem one_more_mark_is_the_element_once_more (element : Area) (mark : FACT) (rest : List FACT) :
    compute_the_area_of (added_to element (mark :: rest)) = compute_the_area_of (added_to element rest) * compute_the_area_of element := by
  rw [added_to_is_the_element_raised_to_the_length, added_to_is_the_element_raised_to_the_length, List.length_cons, Nat.pow_succ]

--| Added to an element, a tape is the element less one cell, by the tape collected as the element counts it, and one cell
--| more.  The one cell more is the fencepost between the routes.
theorem added_is_the_element_less_one_by_the_collected_and_one_more
    (element : Area) (one_less : Nat) (the_element : compute_the_area_of element = one_less + 1) (tape : List FACT) :
    compute_the_area_of (added_to element tape) = one_less * compute_the_area_of (collected_as_the_element_counts element tape) + 1 := by
  induction tape with
  | nil => rw [added_to_is_the_element_raised_to_the_length]; simp only [collected_as_the_element_counts]; rfl
  | cons mark rest ih =>
    rw [one_more_mark_is_the_element_once_more, the_element]
    simp only [collected_as_the_element_counts, palm_the_middle_card_adds]
    generalize compute_the_area_of (added_to element rest) = added at ih ⊢
    generalize compute_the_area_of (collected_as_the_element_counts element rest) = gathered at ih ⊢
    rw [Nat.mul_add, Nat.mul_one, Nat.mul_add, Nat.mul_comm added one_less]
    generalize one_less * gathered = product at ih ⊢
    generalize one_less * added = other at ih ⊢
    omega

--| Over the one element the element's own count of a tape is its marks: collecting is still there.
theorem as_the_one_cell_counts_a_tape_is_its_marks (tape : List FACT) :
    compute_the_area_of (collected_as_the_element_counts ast₁ tape) = compute_the_area_of (collected tape) := by
  rw [collected_is_the_length]
  induction tape with
  | nil => rfl
  | cons _ rest ih =>
    simp only [collected_as_the_element_counts, palm_the_middle_card_adds, ih, List.length_cons,
      added_to_the_one_cell_every_tape_is_one_cell ast₁ rfl]; omega

--| And it is taken by nothing.  Over the one element the join reads: nothing, by the marks, and one.  The marks are there and
--| the route by adding cannot read them: the fencepost between the routes has no size.
theorem over_the_one_element_the_marks_are_taken_by_nothing (tape : List FACT) :
    compute_the_area_of (added_to ast₁ tape) = 0 * compute_the_area_of (collected tape) + 1 := by
  rw [added_to_the_one_cell_every_tape_is_one_cell ast₁ rfl, Nat.zero_mul]

--| WHERE THEY SHOULD BE EQUAL, AND ARE.  Take the element each for each with the tape collected, and set it beside the element
--| added to along the tape.  With one mark they are one for every element.  With an element of two cells and two marks they
--| are one.  With two cells and three marks they are not.
theorem with_one_mark_the_two_routes_are_one (element : Area) (mark : FACT) :
    compute_the_area_of (added_to element [mark]) = compute_the_area_of (element * collected [mark]) := by
  rw [false_shuffle_multiplies, added_to_is_the_element_raised_to_the_length, collected_is_the_length]
  simp only [List.length_cons, List.length_nil, Nat.pow_succ, Nat.pow_zero, Nat.one_mul, Nat.mul_one, Nat.zero_add]

def two_cells : Area := ast₁ + ast₁

theorem at_two_and_two_the_routes_are_one_and_at_two_and_three_they_are_not :
    compute_the_area_of (added_to two_cells [FACT.Truth, FACT.Truth]) = compute_the_area_of (two_cells * collected [FACT.Truth, FACT.Truth])
      ∧ compute_the_area_of (added_to two_cells [FACT.Truth, FACT.Truth, FACT.Truth])
          ≠ compute_the_area_of (two_cells * collected [FACT.Truth, FACT.Truth, FACT.Truth]) := by
  rw [false_shuffle_multiplies, false_shuffle_multiplies, added_to_is_the_element_raised_to_the_length,
    added_to_is_the_element_raised_to_the_length, collected_is_the_length, collected_is_the_length]
  exact ⟨rfl, by decide⟩

--#print axioms added_is_the_element_less_one_by_the_collected_and_one_more
--#print axioms added_to_and_added_to_again_is_added_to_along_the_product
--#print axioms at_two_and_two_the_routes_are_one_and_at_two_and_three_they_are_not

end Measurement
