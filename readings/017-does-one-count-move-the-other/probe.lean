import Experiments.Bottom
/-
Experiment 017.  Does one count move the other?  No meter: a build either accepts each line or does not.

Episode 8 reaches eighteen and five from the lengths of tapes.  The bottom of the last machine reaches them from what
its processes hold.  Here a second bottom is written by hand with one wrapper more on the accumulation, and both are
asked for their brackets, and Episode 8 is asked again for its number.
-/
namespace Measurement
section probe
open «springer-verlag» THE_GOSPEL the_representation assembly_instructions readers_experience the_area
attribute [local instance high] rung01 rung02 rung03 rung04 rung05 rung06 rung07 rung08 rung09 rung10 rung11 rung12 rung13 rung14 rung15
  rung16 rung17 rung18 rung19 rung20 rung21 rung22 rung23 rung24 rung25 rung26 rung27 rung28 rung29 rung32 rung33 rung34 rung35 a_truth_about_the_experience

--| The accumulation with one wrapper more: a fact in front, the same sequence again, and the old accumulation behind.
noncomputable def the_accumulation_wrapped_once_more : Limit :=
  Limit.index FACT.Truth the_limit_process.sequence the_cauchy_process.accumulation
noncomputable def the_other_bracket : Nat :=
  the_cauchy_process.value.all_the_way_down.length + the_accumulation_wrapped_once_more.all_the_way_down.length

#reduce the_other_bracket
#reduce the_bracket_at_the_bottom
#reduce readers_experience.the_macguffin
#reduce the_arm_weight true true
--| LINE A.  With the other bracket, is Episode 8's eighteen still eighteen?
example : readers_experience.the_macguffin = 18 := rfl
--| LINE B.  With the other bracket, is the arm that clicks still the bracket?  (Expected to be refused.)
example : the_arm_weight true true = the_other_bracket := rfl
end probe
end Measurement
