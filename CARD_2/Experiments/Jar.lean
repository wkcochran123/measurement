/-
The jar of rational bounds, from the natural read and the natural inferred.

This file stands beside the device and is built apart: `lake build Experiments.Jar`.  Nothing in `Measurement`
imports it.  It defines no inductive.

The author's, 21 November 2026 (declared): between the proposals and the differential equations there are two values,
one that can be read between the two and one that is inferred between the two; their standing is proposed; and the
natural read and the natural inferred finish the jar of rational bounds.

Episode 13 has the two naturals.  One is read: the giant list has a hundred and thirty-seven cells.  The other is
inferred: the whole of the sum of the roots, less that, forty-two.  The sum of the roots is a ratio, a hundred and
seventy-nine and twenty-nine sixty-fifths.  So each root lies between its natural and its natural and twenty-nine
sixty-fifths: a jar with two walls, both ratios, got from one count and one subtraction.

What is checked here is the arithmetic of the jar.  That the two naturals are the two values between the proposals
and the differential equations is the author's, and by the author's word it is proposed, not shown.
-/
import Measurement.Episode13

namespace Measurement
open readers_experience

--| THE TWO NATURALS.  One read, one inferred, and together the whole part of the sum of the roots.
set_option maxRecDepth 100000 in
theorem the_natural_read_and_the_natural_inferred :
    the_giant_list.length = 137
      ∧ what_is_left_of_the_sum = 42
      ∧ the_giant_list.length + what_is_left_of_the_sum = the_sum_of_the_roots_in_cells / the_frame_by_the_coefficient
      ∧ the_sum_of_the_roots_in_cells % the_frame_by_the_coefficient = 29
      ∧ the_frame_by_the_coefficient = 65 := by decide

--| THE JAR.  The number Episode 8 prints, over its scale, is not under the natural read, and is not over that natural and the
--| twenty-nine sixty-fifths.  Said without division: the natural by the scale is not over the number; and sixty-five of the
--| number is not over sixty-five naturals and twenty-nine, by the scale.
set_option maxRecDepth 100000 in
theorem the_number_is_in_the_jar_the_two_naturals_make :
    the_giant_list.length * all_possible_variables ≤ the_constant_factor_of_scaling_bullshit
      ∧ the_frame_by_the_coefficient * the_constant_factor_of_scaling_bullshit
          ≤ (the_frame_by_the_coefficient * the_giant_list.length
              + the_sum_of_the_roots_in_cells % the_frame_by_the_coefficient) * all_possible_variables := by decide

--| The walls, as two ratios over sixty-five: eight thousand nine hundred and five, and eight thousand nine hundred and
--| thirty-four.
set_option maxRecDepth 100000 in
theorem the_walls_of_the_jar :
    the_frame_by_the_coefficient * the_giant_list.length = 8905
      ∧ the_frame_by_the_coefficient * the_giant_list.length
          + the_sum_of_the_roots_in_cells % the_frame_by_the_coefficient = 8934 := by decide

--| THE OTHER ROOT'S JAR.  The same twenty-nine sixty-fifths over the natural inferred.  The other root's digits past its
--| natural, with the number's digits past its own, are the twenty-nine sixty-fifths, by Episode 13.
set_option maxRecDepth 100000 in
theorem the_other_roots_walls :
    the_frame_by_the_coefficient * what_is_left_of_the_sum = 2730
      ∧ the_frame_by_the_coefficient * what_is_left_of_the_sum
          + the_sum_of_the_roots_in_cells % the_frame_by_the_coefficient = 2759 := by decide

section for_the_reader
open readers_interpretation_of_the_experience

--| FOR THE READER.  The knower's bit picks a root, and the two naturals make a jar around each.  The reader is not handed the
--| bit.  What the reader is handed is the root's first part, the part with no square root in it, and that part is the same
--| whichever way the knower called it.
theorem the_reader_is_handed_one_first_part_whatever_the_knower_called (you_do : FACT) :
    (you_re_a_daisy_if_you_do you_do).1 = 5832 := by
  obtain ⟨truth, click⟩ := you_do
  cases click <;> rfl

--| THE FRACTION.  Twice that first part is the sum of the roots.  Over the sixty-five it is eighty-nine and forty-seven
--| sixty-fifths, exactly: a ratio, with no jar round it.
set_option maxRecDepth 100000 in
theorem the_readers_fraction_is_eighty_nine_and_forty_seven_sixty_fifths :
    2 * 5832 = the_sum_of_the_roots_in_cells
      ∧ 5832 = the_frame_by_the_coefficient * 89 + 47
      ∧ 47 < the_frame_by_the_coefficient := by decide

--| It is the middle of the two roots, and the two naturals stand round it one apart: the natural read is forty-eight above
--| the reader's natural and the natural inferred is forty-seven below.
set_option maxRecDepth 100000 in
theorem the_two_naturals_stand_round_the_readers_one_apart :
    the_giant_list.length = 89 + 48 ∧ what_is_left_of_the_sum + 47 = 89
      ∧ the_giant_list.length + what_is_left_of_the_sum = 2 * 89 + 1 := by decide

--| And the twenty-nine of the jar is twice the forty-seven, less the sixty-five.
set_option maxRecDepth 100000 in
theorem the_jars_twenty_nine_is_twice_the_forty_seven_less_the_sixty_five :
    2 * 47 = the_frame_by_the_coefficient + the_sum_of_the_roots_in_cells % the_frame_by_the_coefficient := by decide

end for_the_reader

--#print axioms the_number_is_in_the_jar_the_two_naturals_make
--#print axioms the_natural_read_and_the_natural_inferred
--#print axioms the_reader_is_handed_one_first_part_whatever_the_knower_called
--#print axioms the_readers_fraction_is_eighty_nine_and_forty_seven_sixty_fifths

end Measurement
