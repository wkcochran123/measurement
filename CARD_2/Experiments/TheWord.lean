/-
The word.

This file stands beside the device and is built apart: `lake build Experiments.TheWord`.  Nothing in `Measurement`
imports it.  It defines no inductive.  Every line is the device's own atoms, set beside, taken each for each, and
taken away, as Episode 13 does on the Area.

The author's, 19 November 2026: the compile and execute step is the two interpretations of the run the bits sit on,
based on the thirty-six bit construction, then the twenty-eight, then the nine, then the binary, two by four or four
by two; the knower provides the mapping through the daisy; and if it compiles, that is the test (declared).
-/
import Measurement.Episode13

namespace Measurement
open readers_experience the_table

--| THE BINARY.  Two cells, and four.  Two for each of four, or four for each of two: eight either way.
def two_cells : Area := ast₁ + ast₁
def four_cells : Area := two_cells + two_cells
def two_by_four : Area := two_cells * four_cells
def four_by_two : Area := four_cells * two_cells

theorem the_binary_is_eight_either_way : compute_the_area_of two_by_four = 8 ∧ compute_the_area_of four_by_two = 8 := by decide

--| THE DAISY.  One cell, and what it holds is the knower's: the fact the knower's bit names.
def the_knowers_cell (daisy : Bool) : Area := .dt (bitFACT daisy) another_zero ast₀

--| THE NINE.  The eight and the knower's cell.  The knower's bit says which way the eight is taken and on which side the
--| cell stands.  That is the mapping.
def the_nine (daisy : Bool) : Area :=
  if daisy then the_knowers_cell daisy + two_by_four else four_by_two + the_knowers_cell daisy

theorem the_nine_is_nine_either_way : ∀ daisy : Bool, compute_the_area_of (the_nine daisy) = 9 := by decide

--| THE THIRTY-SIX.  The device's own trace, on the Area: the reading for each of the memory.
theorem the_trace_is_thirty_six : compute_the_area_of the_table.the_trace = 36 := by decide

--| THE TWENTY-EIGHT.  The thirty-six with the eight taken away: the projection.
def the_twenty_eight : Area := the_table.the_trace - two_by_four

theorem the_twenty_eight_is_twenty_eight : compute_the_area_of the_twenty_eight = 28 := by decide

--| THE WORD.  Three nines, one for each of a, c and b, and one cell more: four daisies, the fourth by itself.
def the_word (a c b the_fourth : Bool) : Area :=
  the_nine a + the_nine c + the_nine b + the_knowers_cell the_fourth

--| THE FIT.  Whatever the knower's four bits, the word is as many cells as the twenty-eight.  Sixteen ways, and it fits
--| in every one.
theorem the_word_fits_the_projection_whatever_the_knower_says :
    ∀ a c b the_fourth : Bool, compute_the_area_of (the_word a c b the_fourth) = compute_the_area_of the_twenty_eight := by decide

--| COMPILE AND EXECUTE.  Read the word out as a tape and write the tape as an abstraction: a compile for every fact and
--| then an execute for every fact.  What execute counts is what compile built, whatever the knower's four bits.
theorem compiled_and_executed_the_word_is_one_count (a c b the_fourth : Bool) :
    compute_the_so_called_area_of (the_marks (the_word a c b the_fourth).riemann_integrate)
      = compute_the_area_of (count_up (the_marks (the_word a c b the_fourth).riemann_integrate)) :=
  execute_counts_what_compile_built _

--| WHAT IT SAYS.  The count does not see the knower's bits.  The word does hold them: read by its clicks, the four cells
--| the knower supplied click as the knower said.  Two words with different bits are the same in count and not in clicks.
theorem the_count_does_not_see_the_daisies_and_the_clicks_do :
    compute_the_area_of (the_word true true true true) = compute_the_area_of (the_word false false false false)
      ∧ (the_word true true true true).riemann_integrate.map FACT.bit
          ≠ (the_word false false false false).riemann_integrate.map FACT.bit := by decide

--| A FIT THAT DOES NOT HOLD.  Leave out the fourth cell and the word is one short of the projection.
theorem without_the_fourth_it_does_not_fit :
    ∀ a c b : Bool, compute_the_area_of (the_nine a + the_nine c + the_nine b) ≠ compute_the_area_of the_twenty_eight := by decide


--| THE FOUR BITS, THROUGH THE CRANK.  The author's, 19 November 2026: the knower's four bits encode the number through
--| the crank (declared).  Episode 13 has sixteen devices, one for each way of taking the bent card's four things as written
--| or turned over.  The word has four bits.  Give the device the word's four bits and turn the crank; then take what it
--| reads over the scale, the whole part.
def what_the_word_reads (a c b the_fourth : Bool) : Option Nat :=
  (what_a_device_reads (the_device_with a c b the_fourth)).map fun reading => reading / all_possible_variables

--| The scale is one and twenty-four noughts.
theorem the_scale_is_one_and_twenty_four_noughts : all_possible_variables = 10 ^ 24 := by decide

--| Sixteen words.  With the last two bits as written, whatever the first two: a hundred and thirty-seven.  With the last
--| turned over: a hundred and six, the turns of the crank.  With the third turned over: nothing.
set_option maxRecDepth 100000 in
theorem the_knowers_four_bits_through_the_crank :
    ([true, false].flatMap fun a => [true, false].flatMap fun c => [true, false].flatMap fun b => [true, false].map
        fun the_fourth => what_the_word_reads a c b the_fourth)
      = [some 137, some 106, none, none, some 137, some 106, none, none,
         some 137, some 106, none, none, some 137, some 106, none, none] := by decide

--| So the word whose four bits are all as written reads a hundred and thirty-seven, and it is one of four that do.
set_option maxRecDepth 100000 in
theorem the_word_as_written_reads_the_number :
    what_the_word_reads true true true true = some 137
      ∧ ∀ a c : Bool, what_the_word_reads a c true true = some 137 := by decide


--| THE WHOLE PART, THE NOUGHT, AND THE REST.  The author's, 19 November 2026: the device carries the rest, with a
--| fencepost of nothing where it is set beside the knower's bits; this is not to be joined here, for the knower infers it
--| (declared).  What the device prints, taken apart by the scale: the whole part, the first place past it, and the next.
--| Nothing is set beside anything.
set_option maxRecDepth 100000 in
theorem the_whole_part_the_nought_and_the_next :
    the_constant_factor_of_scaling_bullshit / 10 ^ 24 = 137
      ∧ the_constant_factor_of_scaling_bullshit / 10 ^ 23 % 10 = 0
      ∧ the_constant_factor_of_scaling_bullshit / 10 ^ 22 % 10 = 1 := by decide

end Measurement
