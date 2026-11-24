/-
__Measurement: The Tragedy of John Henry__
__A Satire in Look Ahead Backus-Naur Form__

_This is a gentle reminder that I'm only in it for the fame and fortune._

(c) 2026 All rights reserved. What rights? What does this _EVEN MEAN_ when I am about to demonstrate that there really is only _1_ meaning?!

"Pete and Repeat were sitting on a fence. Pete fell off, who was left?"
                                                    -- Old-school meme

"And the green grass grew all around and around, and the green grass grew all around."
                                                    -- More Disney property

lake build --stack=5 --D_UNROLL_LOOPS_=1

__EPISODE 13__: _The Prestige_

So *YOU the KNOWER* _think_ *YOU the READER* can still help you figure this out?  Watch carefully as I slowly dismantle all meaning that could have
already been established and replace it with a quartic polynomial over and over and over again. I could do this forever. No, seriously, if the
math is to be believed, I can do this forever.  This machine describes the way to make another machine in a higher level formalism.

_WHAT DOES THAT EVEN MEAN?!?!_

It means only one thing: with this mechanism, number can only go up if it is logically consistent for it to.
-/
import Measurement.Episode12

--| I will now very carefully show that the polynomial that *YOU the READER* found under any one of the cards on the table, is not the only way that
--| polynomial comes out of that device. In fact, the challenge is to get something else to fall out instead. *YOU the KNOWER* is quite confident at
--| at this point we cannot build a finite element description of the Yang-Mills formulation of the bare electron from just the pieces of logic
--| in front of us.

--| This will require understand multigrid-accelerated JFNK solvers used in tightly coupled physics simulations. We will be coupling just a handful
--| of physics to see how tight that coupling can be made.


--| Keeping me honest, I will now ask for a volunteer from the audience to help me demonstrate that what I am talking about is, indeed, mathematics.
--| Welcome to the stage, Mr. Mathlib!
import Meanings
--| I promise not to cheat, but just to let Mr. Mathlib inspect pieces of the device to check for shenanigans. Just some ordinary mathematician we
--| can ask to see if I am telling the _TRUTH_ or _NOT_.

namespace Measurement
open readers_experience

namespace the_table

--| The four *THROWS* of _Three Card Monte_.

def palm_the_middle_card : Area → Area → Area
  | .tree _,                                                             the_arm_not_taken => the_arm_not_taken
  | .dt the_covariant_arm the_covariant_value the_covariant_computation, the_arm_not_taken =>
                .dt the_covariant_arm the_covariant_value (palm_the_middle_card the_covariant_computation the_arm_not_taken)

def false_shuffle : Area → Area → Area
  | .tree f,      _ => .tree f
  | .dt _ _ the_rest, b => palm_the_middle_card b (false_shuffle the_rest b)

def the_double_lift : Area → Area → Area
  | .tree f,    _         => .tree f
  | a,          .tree _   => a
  | .dt _ _ a,  .dt _ _ b => the_double_lift a b

def coin_flip : Area → Bool
  | .tree _   => false
  | .dt _ _ _ => true

instance : Add Area := ⟨palm_the_middle_card⟩
instance : Mul Area := ⟨false_shuffle⟩
instance : Sub Area := ⟨the_double_lift⟩
instance : LT Area := ⟨fun a b => coin_flip (b - a) = true⟩
instance : DecidableRel (α := Area) (· < ·) := fun a b => inferInstanceAs (Decidable (coin_flip (b - a) = true))

def interpret_an_opaque_list_of_truths : List FACT → Abstraction
  | []        => carefully_chosen_variable_names
  | _ :: the_rest => .compile zero δδxᵢ (interpret_an_opaque_list_of_truths the_rest)
def watch_closely (bent_card : Abstraction) : List FACT → Abstraction
  | []        => bent_card
  | _ :: the_rest_of_the_trick => .execute zero δδxᵢ (watch_closely bent_card the_rest_of_the_trick)
def the_marks (TTTTT : List FACT) : Abstraction := watch_closely (interpret_an_opaque_list_of_truths TTTTT) TTTTT

def count_the_symbols : Abstraction → Area
  | .satire_about _    => ast₀
  | .compile _ _ the_rest  => .dt zero another_zero (count_the_symbols the_rest)
  | .execute _ _ the_rest  => count_the_symbols the_rest
def count_the_meanings : Abstraction → Nat
  | .satire_about _    => 0
  | .compile _ _ the_rest  => count_the_meanings the_rest
  | .execute _ _ the_rest  => count_the_meanings the_rest + 1

def the_number_of_marks (TTTTT : List FACT) : Area := count_the_symbols (the_marks TTTTT)

--| THE DEVICE, ON THE AREA.  The same section of Episode 8, word for word, with the Area where the naturals stood.
def the_fencepost               := bent_card.fencepost Area the_number_of_marks
def the_coefficient             := bent_card.the_exact_Taylor_series_degree Area the_number_of_marks
def the_memory                  := bent_card.the_length_of_the_path_from_here_to_there Area the_number_of_marks
def the_trace                   := bent_card.the_measurement_degrees_of_freedom Area the_number_of_marks
def the_house                   := bent_card.the_device_as_linear_operator_mapped_identity Area the_number_of_marks

--| THE COUNT.  This is the only place a natural appears, and it is not handed to the device.  It is how *YOU the READER*
--| read an Area: so many cells.  The tree counts for nothing.  Area's own reading, the Riemann sum, counts the tree too;
--| that is the fencepost.
def compute_the_area_of : Area → Nat
  | .tree _      => 0
  | .dt _ _ the_rest => compute_the_area_of the_rest + 1
def some_quartic_called (pair : Area × Area) : Nat × Nat := (compute_the_area_of pair.1, compute_the_area_of pair.2)


--| The reader is the length.  Area is List.length.  And execute counts what compile built.
theorem a_proof_is_a_list_of_symbols_all_true (the_proof : Abstraction) (TTTTT : List FACT) :
                     count_the_symbols (watch_closely the_proof TTTTT) = count_the_symbols the_proof := by
  induction TTTTT with
  | nil => rfl
  | cons _ _ the_next_truth => simp only [watch_closely, count_the_symbols, the_next_truth]

theorem the_tape_has_a_cell_for_every_fact (tape : List FACT) :
                      compute_the_area_of (count_the_symbols (interpret_an_opaque_list_of_truths tape)) = tape.length := by
  induction tape with
  | nil => rfl
  | cons _ _ the_rest => simp only [interpret_an_opaque_list_of_truths, count_the_symbols, compute_the_area_of, the_rest, List.length_cons]

theorem the_number_of_marks_the_tapes_length (tape : List FACT) :
            compute_the_area_of (the_number_of_marks tape) = tape.length := by
  simp only [the_number_of_marks, the_marks, a_proof_is_a_list_of_symbols_all_true, the_tape_has_a_cell_for_every_fact]

theorem the_tape_of_symbols_has_no_ast (tape : List FACT) :
                                      count_the_meanings (interpret_an_opaque_list_of_truths tape) = 0 := by
  induction tape with
  | nil => rfl
  | cons _ _ the_rest => simp only [interpret_an_opaque_list_of_truths, count_the_meanings, the_rest]

theorem the_proof_counts_every_fact (a_card : Abstraction) (tape : List FACT) :
    count_the_meanings (watch_closely a_card tape) = count_the_meanings a_card + tape.length := by
  induction tape with
  | nil => rfl
  | cons _ _ the_rest => simp only [watch_closely, count_the_meanings, the_rest, List.length_cons]; omega

theorem execute_counts_what_compile_built (tape : List FACT) :
    count_the_meanings (the_marks tape) = compute_the_area_of (count_the_symbols (the_marks tape)) := by
  rw [show count_the_symbols (the_marks tape) = the_number_of_marks tape from rfl, the_number_of_marks_the_tapes_length]
  simp only [the_marks, the_proof_counts_every_fact, the_tape_of_symbols_has_no_ast, Nat.zero_add]

--| Episode 8's own three are the first of them: the proof is the abstraction of a tape of one.

--| Written this way a tape is on the page twice, once compiled and once executed, and once more for the names: the fencepost.
--| For the memory tape that is two eighteens and one.  Thirty-six is Closure's.


--| Compile comes before execute, and not back: the wall is strictly under the abstraction, whenever there is a fact.

--| The four things, counted.  palm_the_middle_card adds.  Each for each multiplies.  Taken away subtracts, and stops at the tree.  Less is less.
theorem palm_the_middle_card_adds (a b : Area) : compute_the_area_of (a + b) = compute_the_area_of a + compute_the_area_of b := by
  show compute_the_area_of (palm_the_middle_card a b) = _
  induction a with
  | tree _ => simp only [palm_the_middle_card, compute_the_area_of, Nat.zero_add]
  | dt _ _ _ the_rest => simp only [palm_the_middle_card, compute_the_area_of, the_rest]; omega

theorem false_shuffle_multiplies (a b : Area) : compute_the_area_of (a * b) = compute_the_area_of a * compute_the_area_of b := by
  show compute_the_area_of (false_shuffle a b) = _
  induction a with
  | tree _ => simp only [false_shuffle, compute_the_area_of, Nat.zero_mul]
  | dt _ _ the_rest_of_the_ast the_rest_of_the_proof =>
    simp only [false_shuffle, compute_the_area_of]
    rw [show palm_the_middle_card b (false_shuffle the_rest_of_the_ast b) = b + false_shuffle the_rest_of_the_ast b
                    from rfl, palm_the_middle_card_adds, the_rest_of_the_proof, Nat.succ_mul]; omega

theorem the_double_lift_subtracts (a b : Area) : compute_the_area_of (a - b) = compute_the_area_of a - compute_the_area_of b := by
  show compute_the_area_of (the_double_lift a b) = _
  induction a generalizing b with
  | tree _ => simp only [the_double_lift, compute_the_area_of, Nat.zero_sub]
  | dt _ _ _ the_rest_of_the_ast =>
    cases b with
    | tree _ => simp only [the_double_lift, compute_the_area_of, Nat.sub_zero]
    | dt _ _ the_rest_of_the_proof => simp only [the_double_lift, compute_the_area_of, the_rest_of_the_ast, Nat.add_sub_add_right]

theorem coin_flip_when_there_is_a_cell (a : Area) : coin_flip a = true ↔ 0 < compute_the_area_of a := by
  cases a with
  | tree _ => exact ⟨fun h => Bool.noConfusion h, fun h => absurd h (Nat.lt_irrefl 0)⟩
  | dt _ _ rest => exact ⟨fun _ => Nat.succ_pos _, fun _ => rfl⟩

theorem obviously_bigger (a b : Area) : a < b ↔ compute_the_area_of a < compute_the_area_of b := by
  show coin_flip (b - a) = true ↔ _
  rw [coin_flip_when_there_is_a_cell, the_double_lift_subtracts]; exact Nat.sub_pos_iff_lt

--| THE WALK, ON THE AREA.  Counted, the fencepost, the coefficient, the memory, the trace and the house of this episode are
--| those of Episode 8.
--| the_reader_has_noticed_a_few_coincidences:w
theorem the_walk_is_the_walk :
    some_quartic_called the_fencepost = bent_card.fencepost Nat List.length
      ∧ compute_the_area_of the_coefficient = an_exact_polynomial_description
      ∧ compute_the_area_of the_memory = the_number_of_symbols_that_must_be_written_to_express_this
      ∧ compute_the_area_of the_trace = the_trace_of_truth_in_the_device
      ∧ some_quartic_called the_house = the_held_house := by
  simp only [some_quartic_called, the_fencepost, the_coefficient, the_memory, the_trace, the_house, an_exact_polynomial_description,
    the_number_of_symbols_that_must_be_written_to_express_this, the_trace_of_truth_in_the_device, the_held_house,
    bent_card.fencepost, bent_card.the_exact_Taylor_series_degree, bent_card.the_length_of_the_path_from_here_to_there,
    bent_card.the_measurement_degrees_of_freedom, bent_card.the_device_as_linear_operator_mapped_identity,
    false_shuffle_multiplies, the_number_of_marks_the_tapes_length, and_self]

--| ONE TURN.  Turn the crank on the Area and count, or count and turn Episode 8's crank.  The same.

--| EVERY TURN.  As many turns as there are marks on any tape of turns.

--| THE CRANK.  All hundred and six turns from the house, on the Area; counted, they are Episode 8's.  Nobody turned them here.
--| An Area of that many cells is not a thing to be written out.  It does not have to be.


--| THE NUMBER.  Hand the Area's device any Area with as many cells as Episode 8's scale.  Count what comes back.  It is the
--| pair Episode 8 arranged, and so the same digits.  No natural went in.  One came out, and only because *YOU the READER* counted.


--| And there is such an Area: the tape of that many truths, read by the reader.

--| THE CONSTANT, ON THE AREA.  Episode 8 is the guide, line for line.  First the free variables: the basis by the dimensions.

--| Then the express route: the tape from the inferred end as deep as the bent card, less the memory.

--| Raised: the one Area each for each with itself, once for every cell of the other.  With no cell, the one cell, ast₁.
def raised : Area → Area → Area
  | _, .tree _      => ast₁
  | b, .dt _ _ rest => b * raised b rest

--| All possible variables: the free variables raised to the express route.  This is the scale.  It is an Area.

--| The names, and the delimiter between them.

--| The fourth lambda, the division algorithm: how many times the one can be taken away from the other.  The first Area is only
--| the patience: no more takings than the thing taken from has cells.  From a tree nothing is taken, and by a tree nothing is.
def taking_until_less : Area → Area → Area → Area
  | .tree _,          _,        _       => ast₀
  | .dt _ _ patience, the_rest, the_one => if the_rest < the_one then ast₀ else ast₁ + taking_until_less patience (the_rest - the_one) the_one
def how_many_times (the_whole the_one : Area) : Area :=
  if coin_flip the_one = true then taking_until_less the_whole the_whole the_one else ast₀

--| The rational idea of relativity, on the Area.  Not more: take the one away from the other and nothing is left.
@[reducible] def the_rational_idea_of_relativity_on_the_area (x y : Area × Area) : Prop := ¬ (y.1 * x.2 < x.1 * y.2)

theorem raised_raises (b e : Area) : compute_the_area_of (raised b e) = compute_the_area_of b ^ compute_the_area_of e := by
  induction e with
  | tree _ => rfl
  | dt _ _ rest ih => simp only [raised, compute_the_area_of, false_shuffle_multiplies, ih, Nat.pow_succ, Nat.mul_comm]



--| Counted, the free variables, the express route and the scale are Episode 8's.


--| THE CONSTANT CAN BE INFERRED.  Episode 8's statement, with the Area where the naturals stood: there is an Area which, each
--| for each with the second of the pair, stands in the rational relation with the first of the pair by the scale.

--| THE SEAL.  From here on the crank, the raising and the taking away are names and are not opened.  What is known of them is
--| what was counted above.  Open one and the machine goes looking for an Area nobody can write.

--| Said of any scale at all.  Nothing here is turned, raised or taken away: the scale is a name.

--| The division, counted, of three names.  No Area is looked into.



--| THE TRANSITION.  The author's, 16 November 2026: the transition matrix is abstraction, abstraction, abstraction, limit.
--| Three of the four are said of a name and cost what a name costs.  The fourth is the Area itself, and it is only approached:
--| ask the machine for it and the machine runs out of memory.  It did.  So the constant is named at the scale, and never opened.

--| In fact, put simply:

--| THE CONSTANT IS AN AREA.  Counted, it is Episode 8's constant, the one whose glyphs Episode 8 and Episode 12 print.  Nobody
--| built this Area and nobody will.  It has a definition, the definition has a count, and the count was already printed.

--| FOUR BULLSHIT VALUES.  The author's, 16 November 2026: you should now be able to get four bullshit values out.  The
--| constant is an Area nobody can write.  These four can be written, and are.  Episode 8 has the two ends: no presents, the
--| zero; and no Santa, one on top of it.  An Area is read out the same way, a no Santa for every cell.
--| Each cell carries the number of the compute_the_area_of under it, where Bullshit's order looks.  Without that the order cannot tell six
--| from nineteen: it reads the top number and nothing else.
def the_number_of : Area → Number
  | .tree _      => another_zero
  | .dt _ _ rest => .one zero (the_number_of rest)
def the_bullshit_of : Area → Bullshit.{0,0}
  | .tree _      => no_presents
  | .dt _ _ rest => .one zero (the_number_of rest) the_satire the_satire (the_bullshit_of rest)

--| The frame is Gauss's, the second of the fencepost.  An arm that can click is the coefficient palm_the_middle_card the frame.  The arm
--| that cannot is the frame alone.
def the_frame := the_fencepost.2
def the_arm (this that : Bool) : Area :=
  if the_arm_stores_a_fact_that_can_click this that then the_coefficient + the_frame else the_frame


--| One cell is no Santa.

--| The arms, counted, are the arms of Episode 12: the memory three times, and Gauss's once.  Abstraction, abstraction,
--| abstraction, limit.

--| And on Episode 8's own meter each reads one over, for the zero it stands on: the fencepost.

--| THE EXPERIENCE AND THE INTERPRETATION.  The author's, 16 November 2026: the experience and the interpretation are
--| represented by those four bullshit values; put them together.  First, the order.  The number's order on these is the count,
--| and so is Bullshit's.
theorem the_numbers_order_is_the_count (a b : Area) : Number.le (the_number_of a) (the_number_of b) ↔ compute_the_area_of a ≤ compute_the_area_of b := by
  induction a generalizing b with
  | tree _ => exact ⟨fun _ => Nat.zero_le _, fun _ => by simp only [the_number_of, another_zero, Number.le]⟩
  | dt fa na ra ih =>
    cases b with
    | tree _ => exact ⟨fun h => by simp only [the_number_of, another_zero, Number.le] at h, fun h => absurd h (Nat.not_succ_le_zero _)⟩
    | dt fb nb rb =>
      have step : Number.le (the_number_of (.dt fa na ra)) (the_number_of (.dt fb nb rb)) ↔ Number.le (the_number_of ra) (the_number_of rb) := by
        simp only [the_number_of, Number.le, zero, FACT.Truth]
      rw [step, ih]; exact Nat.succ_le_succ_iff.symm

theorem the_bullshits_order_is_the_count (a b : Area) : the_bullshit_of a ≤ the_bullshit_of b ↔ compute_the_area_of a ≤ compute_the_area_of b := by
  show Bullshit.le _ _ ↔ _
  cases a with
  | tree _ =>
    cases b with
    | tree _ => exact ⟨fun _ => Nat.le_refl _, fun _ => by simp only [the_bullshit_of, no_presents, Bullshit.le]⟩
    | dt _ _ _ => exact ⟨fun _ => Nat.zero_le _, fun _ => by simp only [the_bullshit_of, no_presents, Bullshit.le]⟩
  | dt fa na ra =>
    cases b with
    | tree _ => exact ⟨fun h => by simp only [the_bullshit_of, no_presents, Bullshit.le] at h, fun h => absurd h (Nat.not_succ_le_zero _)⟩
    | dt fb nb rb =>
      have step : Bullshit.le (the_bullshit_of (.dt fa na ra)) (the_bullshit_of (.dt fb nb rb))
          ↔ Number.le (the_number_of ra) (the_number_of rb) := by
        simp only [the_bullshit_of, Bullshit.le, zero, FACT.Truth]; exact Iff.rfl
      rw [step, the_numbers_order_is_the_count]; exact Nat.succ_le_succ_iff.symm

--| Then the two closures, each of the different kind, the kind the knower is asked to believe: a stanza, two bounds, and
--| whether the first is strictly under the second.  The experience is the two different arms, false on true and then true on
--| false: more to start than to close.  The interpretation is the two same arms, true on true and false on false.

--| THE CLOSURE.  (T=F) = (F=T) ≤ (T=T) = (T=T), in Closure's own order, and not back.

--| THE GAP.  The author's, 16 November 2026: the gap is the same difference, if you work it out.  The closure is
--| (abstraction - abstraction) ≤ (abstraction - limit).  Take the arms away from each other.  The interpretation's two are the
--| same, and nothing is left: no presents.  The experience's two are different, and what is left is the coefficient, the bent
--| card.  Nothing is under the bent card, and not back.  And Episode 5 says what the same is: two bullshits, one under the
--| other, are one thing in the quotient by the order.  So the gap is the same difference: nothing, and thirteen, the same.
def the_gap_of_the_interpretation := the_arm true true - the_arm false false
def the_gap_of_the_experience     := the_arm false true - the_arm true false


theorem the_gap_is_the_same_difference :
    (Quot.mk TruthOrder (the_bullshit_of the_gap_of_the_interpretation) : Quot TruthOrder)
      = Quot.mk TruthOrder (the_bullshit_of the_gap_of_the_experience) :=
  Quot.sound (r := TruthOrder) ((the_bullshits_order_is_the_count _ _).2 (by decide))


--| THE SAME, INFERRED FROM THE EXPERIENCE.  The author's, 16 November 2026: FACT.SAME can be inferred from the experience.
--| Episode 5's SAME takes one thing, a truth about the world, and says that its TRUE and its constant are one in the quotient by
--| the order.  Here is a truth about the experience.  Its TRUE is the gap of the interpretation: no presents.  Its constant is
--| the gap of the experience: the bent card.  That the constant is at least true is the receipt above.  The reader is rung
--| 36's.  Hand it to SAME, and what SAME says is the gap: nothing and thirteen, the same.
section the_same
open «springer-verlag» THE_GOSPEL the_representation assembly_instructions
attribute [local instance high] rung01 rung02 rung03 rung04 rung05 rung06 rung07 rung08 rung09 rung10 rung11 rung12 rung13 rung14 rung15
  rung16 rung17 rung18 rung19 rung20 rung21 rung22 rung23 rung24 rung25 rung26 rung27 rung28 rung29 rung32 rung33 rung34 rung35
noncomputable def a_truth_about_the_experience : A_TRUTH_ABOUT FACT the_first_card rung30 rung31 :=
  { you_the_reader := rung36.you_the_reader
    TRUE := the_bullshit_of.{0,0} the_gap_of_the_interpretation
    a_constant := the_bullshit_of.{0,0} the_gap_of_the_experience
    the_constant_is_at_least_true := (the_bullshits_order_is_the_count.{0,0} _ _).2 (by decide) }

--| The same, said by Episode 5 and by nobody else.  The line of zeros is the universe it is said in.
noncomputable def the_same_inferred_from_the_experience : FACT :=
  FACT.SAME.{0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0} (Box := FACT) (Pigeon := the_first_card) (fact := rung30) (about_the_world := rung31) (guano := a_truth_about_the_experience)


--| And it is so.
theorem and_it_is_so : the_same_inferred_from_the_experience.truth := the_gap_is_the_same_difference.{0,0}
end the_same

--| THE KNOWER OF THE EXPERIENCE.  The author's, 16 November 2026: carry on, finish the demonstration.  Episode 9 deals the
--| thirty-seventh rung, INFERRED, from a truth about the world.  Deal it again, the same hand, the same thirty-five rungs under
--| it, with the truth about the experience where rung 36 stood.  It is dealt as Episode 12 deals: only the first rung declared.
section the_deal
open «springer-verlag» THE_GOSPEL the_representation assembly_instructions
attribute [local instance high] rung01
deal_rung the_knower_of_the_experience := ITS_YOU_!!
    FACT the_first_card this_way_in_FACT that_way_in_FACT the_first_card FACT.Truth rung01 rung02 rung03 rung04 rung05 rung06 rung07 rung08 rung09 rung10 rung11 rung12 rung13 rung14 rung15 rung16 rung17 rung18 rung19 rung20 rung21 rung22 rung23 rung24 rung25 rung26 rung27 rung28 rung29 rung30 rung31 rung32 rung33 rung34 rung35 a_truth_about_the_experience True True

end the_deal

--| The rung carries two closures.  The conclusion: the constant against the gawk at it.  And α, inferred, which ends on the
--| same.  The same it ends on is the one above: nothing and the bent card, one thing.
section the_reading
open «springer-verlag» THE_GOSPEL the_representation assembly_instructions
attribute [local instance high] rung01 rung02 rung03 rung04 rung05 rung06 rung07 rung08 rung09 rung10 rung11 rung12 rung13 rung14 rung15
  rung16 rung17 rung18 rung19 rung20 rung21 rung22 rung23 rung24 rung25 rung26 rung27 rung28 rung29 rung32 rung33 rung34 rung35 a_truth_about_the_experience


--| THE DEMONSTRATION.  The knower compares the two by inferred?, which is ≤.  The conclusion is under α.  And α is under the
--| conclusion.  The device reads the order both ways, here as in Episode 12.  That it runs one way is the knower's.  What ran
--| one way in this episode was below: the gap, nothing under thirteen and not back.  The order on the closures does not keep it.
end the_reading

--| THE NUMBER, OUT.  The author's, 16 November 2026: can you see how to get the number out?  Compile built the Area, and the
--| Area is sealed.  Execute counts, and nothing has called it.  Call it.  Episode 12 routed the count through another machine
--| and handed it to Episode 8's crank.  The other machine here is the Abstraction: write the tape, count the executes.  The
--| pair that comes out is the pair Episode 8 arranged, and it is the Area's pair, counted.  Then read off the glyphs.







--| THE THEOREMS OF Episode 12, ON THE INDUCTIVES.  The author's, 16 November 2026: reimplement the theorems as inductives and
--| proofs on them.  Episode 12 says what it says of weights, which are naturals.  Here the same is said of Areas, with an Area
--| for a clock where there was a number of steps, and with as many where there was equals.  First the table and its walks.
--| As many: take either from the other and nothing is left.  Said of two Areas and of nothing else.
def as_many (a b : Area) : Prop := coin_flip (a - b) = false ∧ coin_flip (b - a) = false
instance (a b : Area) : Decidable (as_many a b) := inferInstanceAs (Decidable (_ ∧ _))

theorem nothing_is_left_when_there_is_no_cell (a : Area) : coin_flip a = false ↔ compute_the_area_of a = 0 := by
  cases a with
  | tree _ => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | dt _ _ rest => exact ⟨fun h => Bool.noConfusion h, fun h => absurd h (Nat.succ_ne_zero _)⟩

theorem as_many_is_the_same_count (a b : Area) : as_many a b ↔ compute_the_area_of a = compute_the_area_of b := by
  simp only [as_many, nothing_is_left_when_there_is_no_cell, the_double_lift_subtracts]
  exact ⟨fun h => Nat.le_antisymm (Nat.sub_eq_zero_iff_le.mp h.1) (Nat.sub_eq_zero_iff_le.mp h.2),
         fun h => ⟨Nat.sub_eq_zero_iff_le.mpr (Nat.le_of_eq h), Nat.sub_eq_zero_iff_le.mpr (Nat.le_of_eq h.symm)⟩⟩

--| One more cell, of ast₁'s kind.


--| THE TABLE, ON THE AREA.  Episode 12's click table, its trace and its determinant, with the arms where the weights stood.



--| THE WALKS, ON THE AREA.  The clock is an Area: no cell, stand still; one more cell, one more edge.




--| THE ACCOUNT.  The author's, 16 November 2026: a pair of Areas.  An Area cannot go below its tree, so what Episode 12 says
--| of signed numbers is said here of two Areas kept side by side: what is held, and what is owed.  Nothing is ever taken away.
structure Account where
  held : Area
  owed : Area

namespace Account
--| palm_the_middle_card: held with held, owed with owed.
instance : Add Account := ⟨fun p q => ⟨p.held + q.held, p.owed + q.owed⟩⟩
--| Turned over: what was held is owed.
instance : Neg Account := ⟨fun p => ⟨p.owed, p.held⟩⟩
--| Less: palm_the_middle_card the other turned over.
instance : Sub Account := ⟨fun p q => ⟨p.held + q.owed, p.owed + q.held⟩⟩
--| Each for each: like with like is held, unlike is owed.
instance : Mul Account := ⟨fun p q => ⟨p.held * q.held + p.owed * q.owed, p.held * q.owed + p.owed * q.held⟩⟩
--| An Area, held, with nothing owed.
def holding (a : Area) : Account := ⟨a, ast₀⟩
--| The same: each one's held palm_the_middle_card the other's owed are as many.
def the_same (p q : Account) : Prop := as_many (p.held + q.owed) (q.held + p.owed)
instance (p q : Account) : Decidable (the_same p q) := inferInstanceAs (Decidable (as_many _ _))

--| The balance.  The reader's, and not the device's: an integer is read off an account the way a count is read off an Area.
def balance (p : Account) : Int := (compute_the_area_of p.held : Int) - (compute_the_area_of p.owed : Int)

theorem balance_of_palm_the_middle_card (p q : Account) : balance (p + q) = balance p + balance q := by
  show ((compute_the_area_of (p.held + q.held) : Nat) : Int) - ((compute_the_area_of (p.owed + q.owed) : Nat) : Int) = _
  simp only [palm_the_middle_card_adds, balance]; omega
theorem balance_turned_over (p : Account) : balance (-p) = - balance p := by
  show ((compute_the_area_of p.owed : Nat) : Int) - ((compute_the_area_of p.held : Nat) : Int) = _
  simp only [balance]; omega
theorem balance_of_less (p q : Account) : balance (p - q) = balance p - balance q := by
  show ((compute_the_area_of (p.held + q.owed) : Nat) : Int) - ((compute_the_area_of (p.owed + q.held) : Nat) : Int) = _
  simp only [palm_the_middle_card_adds, balance]; omega
theorem balance_of_false_shuffle (p q : Account) : balance (p * q) = balance p * balance q := by
  show ((compute_the_area_of (p.held * q.held + p.owed * q.owed) : Nat) : Int) - ((compute_the_area_of (p.held * q.owed + p.owed * q.held) : Nat) : Int) = _
  simp only [palm_the_middle_card_adds, false_shuffle_multiplies, balance, Int.natCast_add, Int.natCast_mul, Int.sub_mul, Int.mul_sub]
  omega
theorem balance_of_holding (a : Area) : balance (holding a) = (compute_the_area_of a : Int) := by
  show ((compute_the_area_of a : Nat) : Int) - ((compute_the_area_of ast₀ : Nat) : Int) = _
  rw [show compute_the_area_of ast₀ = 0 from rfl]; omega
theorem the_same_is_the_same_balance (p q : Account) : the_same p q ↔ balance p = balance q := by
  simp only [the_same, as_many_is_the_same_count, palm_the_middle_card_adds, balance]
  constructor <;> intro h <;> omega
end Account

open Account

--| THE MEANINGS, MET.  Meanings says what it is to be counted as the naturals and balanced as the integers, and names nothing
--| of the device.  The Area and the Account meet those interfaces with the receipts already above.  Were one missing, this
--| would not compile.  Dealt: a tape of that many truths, read by the reader; owed: the same, turned over.
def a_tape_of_truths (n : Nat) : Area := the_number_of_marks (List.replicate n zero)

theorem a_tape_of_truths_is_as_long_as_asked (n : Nat) : compute_the_area_of (a_tape_of_truths n) = n := by
  rw [a_tape_of_truths, the_number_of_marks_the_tapes_length, List.length_replicate]

instance : Meanings.CountedAsNat Area where
  count      := compute_the_area_of
  deal       := a_tape_of_truths
  count_deal := a_tape_of_truths_is_as_long_as_asked
  adds       := palm_the_middle_card_adds
  multiplies := false_shuffle_multiplies
  subtracts  := the_double_lift_subtracts
  less       := obviously_bigger

def an_account_of (z : Int) : Account :=
  match z with
  | .ofNat n   => holding (a_tape_of_truths n)
  | .negSucc n => - holding (a_tape_of_truths (n + 1))

theorem an_account_of_balances (z : Int) : balance (an_account_of z) = z := by
  cases z with
  | ofNat n   => rw [an_account_of, balance_of_holding, a_tape_of_truths_is_as_long_as_asked]; rfl
  | negSucc n => rw [an_account_of, balance_turned_over, balance_of_holding, a_tape_of_truths_is_as_long_as_asked]; rfl

instance : Meanings.BalancedAsInt Account where
  balance      := balance
  deal         := an_account_of
  balance_deal := an_account_of_balances
  adds         := balance_of_palm_the_middle_card
  negates      := balance_turned_over
  subtracts    := balance_of_less
  multiplies   := balance_of_false_shuffle

--| So, up to what the reader keeps: the Area is the naturals, the Account the integers, and a pair of Accounts the ratios.

--| THE CHOICE IS THE CLICK.  A zero is not the naturals; one more is.  There is always one more Area, and no walk down the
--| Areas goes on forever, and neither costs anything.  The first Area where a statement holds is found by looking, and
--| looking needs the statement to click.  A FACT carries its click, so the first Area where a FACT holds is found with no
--| choice.  A bare statement has to be handed a click, and the only one Lean keeps is choice.  Ask to see that, and it is billed.


theorem the_first_area_where_a_fact_holds (the_fact : Area → FACT)
    (read_alike : Meanings.CountedAsNat.ReadAlike (fun a => (the_fact a).truth)) (a : Area) (holds : (the_fact a).truth) :
    ∃ b, (the_fact b).truth ∧ ∀ c, c < b → ¬ (the_fact c).truth :=
  @Meanings.CountedAsNat.the_least_counted_with_the_click Area _ _ _ _ _ (fun b => (the_fact b).truth)
    (fun b => (the_fact b).click) read_alike a holds


--| THE RESIDUAL, ON THE ACCOUNT.  Thirteen y squared less thirty-six y and eighteen, with no thirteen, thirty-six or eighteen
--| written: the coefficient, the trace and the memory, held.
def the_residual_on_the_account (y : Account) : Account :=
  holding the_coefficient * y * y - holding the_trace * y + holding the_memory

theorem the_balance_of_the_residual_is_the_residual (y : Account) :
    balance (the_residual_on_the_account y) = the_residual_at (balance y) := by
  simp only [the_residual_on_the_account, balance_of_palm_the_middle_card, balance_of_less, balance_of_false_shuffle, balance_of_holding,
    the_walk_is_the_walk.2.1, the_walk_is_the_walk.2.2.1, the_walk_is_the_walk.2.2.2.1, the_residual_at]
  rfl

--| Twice the coefficient: the basis each for each with it.
def twice_the_coefficient : Area := the_number_of_marks the_basis.the_reading * the_coefficient

--| The difference of the residual, exact: no slope is taken and none is needed.
theorem the_jacobian_free_difference_is_exact_on_the_account (y h : Account) :
    the_same (the_residual_on_the_account (y + h) - the_residual_on_the_account y)
             ((holding twice_the_coefficient * y - holding the_trace) * h + holding the_coefficient * (h * h)) := by
  rw [the_same_is_the_same_balance]
  simp only [balance_of_palm_the_middle_card, balance_of_less, balance_of_false_shuffle, balance_of_holding, the_balance_of_the_residual_is_the_residual,
    twice_the_coefficient, false_shuffle_multiplies, the_number_of_marks_the_tapes_length,
    the_walk_is_the_walk.2.1, the_walk_is_the_walk.2.2.2.1]
  exact the_jacobian_free_difference_is_exact (balance y) (balance h)

--| The residual as a rate is the table as a line: the trace and the determinant of the arms where thirty-six and two
--| hundred and thirty-four stood.

--| THE SMALL ACCOUNTS.  The numbers Episode 12 writes as glyphs, each held as an Area the device already has: the tree for
--| nothing, the basis for two, the inference for three, the basis twice over for four, the basis by the inference for six, and
--| the memory for eighteen.
def nothing_held    : Account := holding ast₀


--| THE TABLE'S POLYNOMIAL, ON THE ACCOUNT.



--| Struck: the round trip is nothing each for each with the memory, and the polynomial is a square.


--| THE ACTION, ON THE ACCOUNT.  The cubic whose slope is the residual.



--| THE SIXTEEN LOGICALS.  The author's, 16 November 2026: these are the sixteen logicals in the Cook-Levin.  Four coins: the
--| first two are the compile step, the last two the execute step.
--|
--|   t t t t   four trues: a length count.
--|   t t t f   the compile step is a count and the execute step is T=F.
--|   t t f t   the compile step is a count and the execute step is F=T.  SAME: T=F = F=T.
--|   t t f f   the compile step is a count and the execute step is INFERRED <F=F, rfl>, and F=F is SAME_DIFFERENCE.
--|   t f t t   T=F = (T=T) = RFL = (F=F).
--|   t f t f   (T=F) = (T=F): the frame alone on both sides.  The one row with no abstraction in it.  The limit.
--|   t f f t   (T=F) = (F=T): the last link of Episode 6's chain, and the left of the closure.
--|   t f f f   T=F under SAME_DIFFERENCE.
--|   f t t t   SAME, and then a count.
--|   f t t f   (F=T) = (T=F): the experience.  More to start than to close.
--|   f t f t   (F=T) = (F=T): SAME, twice.
--|   f t f f   SAME, and then SAME_DIFFERENCE: INFERRED, ending on SAME.
--|   f f t t   rfl on both sides.
--|   f f t f   SAME_DIFFERENCE, and then T=F.
--|   f f f t   SAME_DIFFERENCE, and then SAME.
--|   f f f f   (F=F) = (F=F): SAME_DIFFERENCE, twice.
--|
--| Compile builds an arm and execute counts an arm.  Abstraction or limit, twice over: nine, three, three and one.
--| A step: the compile's two coins and the execute's two coins.
def the_sixteen_steps : List ((Bool × Bool) × (Bool × Bool)) :=
  [true, false].flatMap fun t0 => [true, false].flatMap fun t1 => [true, false].flatMap fun t2 => [true, false].map fun t3 =>
    ((t0, t1), (t2, t3))
def what_compile_builds (step : (Bool × Bool) × (Bool × Bool)) : Area := the_arm step.1.1 step.1.2
def what_execute_counts (step : (Bool × Bool) × (Bool × Bool)) : Area := the_arm step.2.1 step.2.2


--| Level: as many built as counted.  Short: something built is left uncounted.  Over: something counted was never built.

--| And where it is not level, what is left either way is the bent card.

--| THE RATIO OF Episode 6.  The author's, 16 November 2026: the number is the ratio represented by Episode 6.  Read it.
--| Episode 6 is one coin and one theorem: a statement with one proof and a statement with none are each at most one thing, and
--| so they are the same statement.  The partitioned subsingleton.  Now the constant.  It was never divided out.  It was
--| inferred as a ratio, a pair in the quotient by not more than, cross multiplied.  And that quotient has one point: of any two
--| cross products one is not more than the other.  So every ratio is the same ratio, the device's and any other.  One proof
--| and no proof.
theorem the_box_on_the_area_has_one_point (x y : Quot the_rational_idea_of_relativity_on_the_area) : x = y := by
  induction x using Quot.ind with
  | mk a =>
    induction y using Quot.ind with
    | mk b =>
      by_cases more : b.1 * a.2 < a.1 * b.2
      · refine (Quot.sound (r := the_rational_idea_of_relativity_on_the_area) ?_).symm
        show ¬ (a.1 * b.2 < b.1 * a.2)
        exact fun back => Nat.lt_asymm ((obviously_bigger _ _).1 more) ((obviously_bigger _ _).1 back)
      · exact Quot.sound (r := the_rational_idea_of_relativity_on_the_area) more

instance : Subsingleton (Quot the_rational_idea_of_relativity_on_the_area) := ⟨the_box_on_the_area_has_one_point⟩

--| THE TRICK, BUILT IN THE DEVICE.  The author's, 16 November 2026: now you see it, we will build that in the device.  Episode 6
--| is not imported.  It said its piece with a coin outside the device and the extensionality of statements.  Episode 5 says
--| it inside, once, in SAME: two bullshits, one under the other, are one thing in the quotient by the order.  Here is what that
--| does.
--| One proof, and no proof: the zero on a fact that is true, and the zero on a fact that is false.

--| Neither is under the other.  Zero against zero, the order asks whether the truths are the same, and they are not.

--| But both are under no Santa: zero is the origin for all.

--| THE SOUND.  And so, in the quotient by the order, the true is the false.  No statement was made equal to another: two
--| things were each put under a third, and the quotient cannot keep them apart.

--| Every bullshit goes the same way.  A zero is under no Santa.  Anything else has no presents under it.  And no presents is
--| under no Santa.  The quotient by the order has one point.
theorem the_truth_order_has_one_point (x y : Quot (TruthOrder : Bullshit.{0,0,0,0} → Bullshit.{0,0,0,0} → Prop)) : x = y := by
  have to_no_santa : ∀ b : Bullshit.{0,0,0,0}, (Quot.mk TruthOrder b : Quot TruthOrder) = Quot.mk TruthOrder no_santa.{0,0} := by
    intro b
    cases b with
    | zero f => exact Quot.sound (r := TruthOrder) (trivial : True)
    | one f n p q rest =>
      exact (Quot.sound (r := TruthOrder) (show Bullshit.le no_presents.{0,0,0,0} (.one f n p q rest) from (trivial : True))).symm.trans
        (Quot.sound (r := TruthOrder) (show Bullshit.le no_presents.{0,0,0,0} no_santa.{0,0} from (trivial : True)))
    | rest_call f g p a b c q r before after =>
      exact (Quot.sound (r := TruthOrder) (show Bullshit.le no_presents.{0,0,0,0} (.rest_call f g p a b c q r before after) from (trivial : True))).symm.trans
        (Quot.sound (r := TruthOrder) (show Bullshit.le no_presents.{0,0,0,0} no_santa.{0,0} from (trivial : True)))
  induction x using Quot.ind with
  | mk a => induction y using Quot.ind with
    | mk b => exact (to_no_santa a).trans (to_no_santa b).symm

--| So the box of ratios has one point and the truth order has one point.  The constant is inferred in the first and the same
--| is said in the second.  One proof and no proof, the same, and by nothing but the sound of the quotient.
instance : Subsingleton (Quot (TruthOrder : Bullshit.{0,0,0,0} → Bullshit.{0,0,0,0} → Prop)) := ⟨the_truth_order_has_one_point⟩

--| THE KNOWER'S INTERPRETATION OF THE CLOCK.  The author's, 16 November 2026: you can combine this with the other
--| interpretation for the knower's interpretation, a × (−c × b); it is the clock T F T and F T F.  Three coins in a row.  The
--| arm from the third back to the second is true on false on the one clock and false on true on the other: the two the order
--| keeps apart and the quotient makes one.
--| A coin, as an account: one cell held for true, one cell owed for false.
def the_coin_held_or_owed (coin : Bool) : Account := if coin then holding ast₁ else - holding ast₁

--| THE KNOWER'S INTERPRETATION.  a × (−c × b): the arm from the third coin back to the second, turned over, each for each with
--| the first coin.
def the_knowers_interpretation (a b c : Bool) : Account := the_coin_held_or_owed a * (- holding (the_arm c b))

theorem the_knowers_interpretation_of_the_clocks :
    balance (the_knowers_interpretation true false true) = -5
      ∧ balance (the_knowers_interpretation false true false) = 18
      ∧ balance (the_knowers_interpretation true true true) = -18
      ∧ balance (the_knowers_interpretation false false false) = 18 := by decide

--| The alternating clock, T F T and F T F, read by the knower and set palm_the_middle_card itself: the bent card.  The still clock, T T T
--| and F F F: nothing.
theorem the_alternating_clock_reads_the_bent_card_and_the_still_clock_reads_nothing :
    the_same (the_knowers_interpretation true false true + the_knowers_interpretation false true false) (holding the_coefficient)
      ∧ the_same (the_knowers_interpretation true true true + the_knowers_interpretation false false false) nothing_held := by decide

--| THE INDUCTIVE THE LIST INDICATES.  The author's, 16 November 2026: the inductives made the lists; build the inductives
--| that the lists indicate, for the knower's interpretation; use the Abstraction to the List to get the number out.  Episode 8
--| reads an Abstraction to a tape, fact by fact.  Here is the way back: a tape, written as the Abstraction that reads to it.
--| Each fact goes in its own cell, on the carefully chosen variable names.  The compute_the_area_of follow the knower's clock: execute where
--| the clock says true and compile where it says false, turn about.  T F T, or F T F.
def the_abstraction_the_list_indicates : Bool → List FACT → Abstraction
  | _,     []           => carefully_chosen_variable_names
  | true,  fact :: rest => .execute fact δδxᵢ (the_abstraction_the_list_indicates false rest)
  | false, fact :: rest => .compile fact δδxᵢ (the_abstraction_the_list_indicates true rest)

--| Read back by Episode 8 it is the tape, and the names after it.  Whichever way the clock started.
theorem the_abstraction_reads_back_to_its_list (clock : Bool) (tape : List FACT) :
    (the_abstraction_the_list_indicates clock tape).equivalation = tape ++ carefully_chosen_variable_names.equivalation := by
  induction tape generalizing clock with
  | nil => cases clock <;> rfl
  | cons fact rest ih =>
    cases clock <;> simp only [the_abstraction_the_list_indicates, Abstraction.equivalation, ih, List.cons_append]

--| The count: the Abstraction, to the List, to its length, less the names.  The fencepost.
def the_knowers_count (clock : Bool) (tape : List FACT) : Nat :=
  (the_abstraction_the_list_indicates clock tape).equivalation.length - the_fencepost_bug

theorem the_knowers_count_is_the_length (clock : Bool) : the_knowers_count clock = List.length := by
  funext tape
  simp only [the_knowers_count, the_abstraction_reads_back_to_its_list, List.length_append, the_fencepost_bug, Nat.add_sub_cancel]

--| THE NUMBER, OUT OF THE ABSTRACTION.  Episode 8's crank, handed that count, on either clock.
def the_knowers_pair (clock : Bool) : Nat × Nat :=
  bent_card.fenceposts_must_be_preserved Nat (the_knowers_count clock) all_possible_variables

theorem the_knowers_pair_is_the_arrangement (clock : Bool) : the_knowers_pair clock = arrange_the_information_appropriately := by
  unfold the_knowers_pair; rw [the_knowers_count_is_the_length]; rfl

--| T F T and F T F print one number.  The order keeps the two clocks apart and the count does not.
theorem both_clocks_print_one_number : the_knowers_pair true = the_knowers_pair false :=
  (the_knowers_pair_is_the_arrangement true).trans (the_knowers_pair_is_the_arrangement false).symm





--| And the clocks are apart: on any tape with a fact on it, the one starts on an execute and the other on a compile, and
--| compile comes before execute and not back.

--| TRUTH BEFORE CLICK.  The author's, 16 November 2026: FACT.truth and FACT.click are your clocks, and they make a clock, truth
--| before click.  A fact is two things, what it says and whether it clicks.  So a fact is two ticks: a compile for its truth,
--| and then an execute for its click.  Compile before execute.

--| For one fact, the truth is strictly under the click, and not back.

--| Each fact twice over, side by side: the tape the clock is laid on.

--| It is the clock that starts false, F T F T, on that tape: the inductive the doubled list indicates.

--| Read back by Episode 8: every fact twice, and the names.

--| The count: the Abstraction, to the List, to its length, less the names, through the basis.  Two ticks to a fact.





--| THE KNOWER'S INTERPRETATION, OF FACTS.  The coin a fact shows is its click.  Three facts in a row, read as before.


--| BEFORE AND AFTER.  The author's, 16 November 2026: this is before and after; the two comparisons are disjoint and
--| connected.  The compile step is the clause before and the execute step the clause after.  On four coins the two
--| comparisons share no coin: disjoint, sixteen of them.  They are connected when the before ends on the coin the after
--| starts on, and then there are three coins and not four: the clock.  Eight of them.


--| Of the eight, four are level and four are not: two short and two over.  The one step level on the frame is not among
--| them: true on false and then true on false again is not a clock.

--| And the knower's interpretation reads a connected step by its clock: the after clause, back from its end, turned over,
--| each for each with where the before clause began.

--| OVERLAPPED.  The author's, 16 November 2026: overlap these at the same time and you get (T=F) (F=T) (T=F) as a tape.
--| Four coins, read both ways at once: the comparison before, the comparison after, and the one that connects them.

--| The step that was not a clock, the limit, true false true false: true on false, false on true, true on false.

--| Which of them can click: no, yes, no.  The coins ran T F T F and the clicks run F T F.  The one clock, compared, is the
--| other.  And the other, compared, is the one.

--| As Areas the tape is the frame, the memory, the frame.

--| Only two of the sixteen overlap to a tape on which every comparison is different: the two alternating clocks.

--| ELLIPTIC OVER HYPERBOLIC.  The author's, 16 November 2026: this is an elliptic/hyperbolic ratio solution, and the simplicial
--| time integrator associated with that.  The tape is the frame, the memory, the frame.  Two neighbours on it set palm_the_middle_card
--| each other are the different: the crossings summed, the part of the table that keeps two directions.  Hyperbolic.  The one
--| taken from the other is the turn: the crossings' difference, the part that keeps none.  Elliptic.  And the turn is the
--| coefficient, the bent card.


--| The ratio is under one: the turn is less than the different.  And the frame by the memory is less than the memory by
--| itself, which is Episode 12's speed below light.

--| The different squared less the turn squared is four of the frame by the memory, and that is the discriminant of the arms.
--| The gap squared.  Over nothing: hyperbolic.

--| THE INTEGRATOR.  Three points in a row and two steps between them.  The first step holds the bent card and the second owes
--| it: across the three the steps close.  The middle against its two neighbours owes the bent card twice, which is the
--| twenty-six of the crank's turn.


--| THE THREE THAT MUST MATCH.  The author's, 16 November 2026: those are the three triangles that must match exactly,
--| alternating, diminishing higher order terms or diminishing derivatives.  The action steps in three terms and no more: the
--| step by the residual, the step squared by the residual's slope, the step cubed by the slope's slope.  A side, a triangle,
--| a tetrahedron, doubled and tripled so nothing is halved.  Each derivative is one degree less than the last and the
--| fourth is nothing.  What is held and what is owed alternate: the coefficient held, the trace owed, the memory held.
def the_slope_on_the_account (y : Account) : Account := holding twice_the_coefficient * y - holding the_trace

--| The residual's own step, exact in two terms: this is Episode 13's earlier receipt, with the slope named.
theorem the_residual_steps_by_its_slope_exactly (y h : Account) :
    the_same (the_residual_on_the_account (y + h) - the_residual_on_the_account y)
             (the_slope_on_the_account y * h + holding the_coefficient * (h * h)) :=
  the_jacobian_free_difference_is_exact_on_the_account y h

--| The slope's step, exact in one term.

--| And the slope's slope does not step at all.  The fourth is nothing.

--| The last derivative is on the tape: the middle against its two neighbours owes exactly it.

--| Three ways to the gap squared, and they match: the different and the turn; the trace and the determinant; the residual's
--| own middle and outer coefficients.

--| AND THE THIRD THING THEY ARE.  The author's, 16 November 2026: and the third thing they are is a × (−c × b).  The three on
--| the tape, the frame, the memory, the frame, read as the knower reads three coins: the third each for each with the second,
--| turned over, each for each with the first.

--| The inside, the third by the second, is the frame by the memory: the round trip.  Four of it is the gap squared, the one
--| the three routes agree on.

--| On the tape the knower's interpretation owes the frame by the round trip.

--| THE INTEGRATOR, SET UP.  The author's, 16 November 2026: c is any possible deviation from the spline that would introduce a
--| new knot, give or take resolution, not noise; that is how the integrator is set up.  The crank already has it.  One turn
--| works out where it would go next, crosses where it is with where it would go, and asks whether the crossing, by the scale
--| and the fencepost, is under the two heights.  Under: no knot, stand still.  Not under: a knot, and go.

--| Where the turn would go next: Newton's, on the Area.

--| The deviation: here crossed with there, taken either way and set palm_the_middle_card, so that whichever way it falls it is counted.
def the_deviation (here there : Area × Area) : Area :=
  (here.1 * there.2 - there.1 * here.2) + (there.1 * here.2 - here.1 * there.2)

--| Under the resolution: the deviation by the scale and the fencepost's first is less than the two heights by its second.
def under_the_resolution (scale : Area) (here there : Area × Area) : Prop :=
  the_deviation here there * scale * the_fencepost.1 < here.2 * there.2 * the_fencepost.2

instance (scale : Area) (here there : Area × Area) : Decidable (under_the_resolution scale here there) :=
  inferInstanceAs (Decidable (_ < _))

--| That is the turn, word for word: stand still under the resolution, and otherwise go.

--| c, as a FACT.  Its truth is the statement that the deviation is not under the resolution.  Its click decides it.  Truth
--| before click.

--| And the turn goes exactly when the knot clicks.

--| THE KNOT, IN THE DEVICE'S OWN SPLINE.  Episode 3 has the spline: an observation; a knot, which is a statement, a polynomial
--| and the spline so far; and an interpolant, which is a fact, two polynomials, the spline before and the spline after.  The
--| statement of a knot is c.  The fact of an interpolant is c with its click.  Before and after are a and b.

--| An observation is under any knot and any interpolant, and neither is under an observation: no retrocausality.

--| Read by Episode 8, an interpolant is its fact, then what came before, then what came after.

--| BULLSHIT, ALL THE WAY DOWN.  The author's, 16 November 2026: instantiate Bullshit.zero; call Bullshit to Bullshit on the
--| (not c × b); then Bullshit to Bullshit to Closure on the (a × other); we should be able to get the number out.
section all_the_way_down
open «springer-verlag» THE_GOSPEL the_representation assembly_instructions
attribute [local instance high] rung01 rung02 rung03 rung04 rung05 rung06 rung07 rung08 rung09 rung10 rung11 rung12 rung13 rung14 rung15
  rung16 rung17 rung18 rung19 rung20 rung21 rung22 rung23 rung24 rung25 rung26 rung27 rung28 rung29 rung32 rung33 rung34 rung35 a_truth_about_the_experience

--| Not c, at b: at the house, with where it would go next, there is no new knot.  A fact: the statement, and its click.

--| One zero, on that fact.

--| Bullshit to Bullshit: the knower of the experience, who is its reader, gawks at it.  From a zero the gawk is the first
--| page.


--| Bullshit to Bullshit to Closure: the knower of the experience is asked to believe the zero against the gawk at it.

--| The closure is one cell, and the cell is the same.

--| Deal it as the quarter of a card, as Episode 12 deals its closures, and read past the quarter.

--| THE NUMBER, OUT OF THE ZERO.  The crank, handed the reading past that quarter, arranges Episode 8's pair; and that is the
--| Area's pair, counted; and that is the pair both clocks print.

end all_the_way_down

--| THE LIST MACHINE, OF EVERY INDUCTIVE.  The author's, 16 November 2026: make the list machine, except make the entire
--| machine of the inductives, not just the current level; for all the inductives, like in Episode 8.  Episode 8 reads each
--| of the thirty-six to a tape.  Here is the way back for each: a tape, written as the inductive that reads to it.  And all
--| the way down: every slot a cell has for the level below is filled with what the rest of the tape indicates at that level.
--| A natural carries its number.  An area carries its number.  A closure carries its bullshit, which carries its preprint and
--| its number.  Read back by Episode 8, each is as long as its tape and one for where it stands; the sample, the trial and
--| the closure say each fact twice; the measurement has no fencepost, as Episode 8 said it would not.




































--| THE ENTIRE MACHINE.  Thirty-six counts, one through every inductive of the five episodes, in the order of the rungs.


--| Every one of them is the length.

--| And so the crank, handed any of the thirty-six, arranges the one pair.  The number comes out of every inductive.

--#print axioms execute_counts_what_compile_built
--#print axioms the_memory_written_as_an_abstraction_is_the_trace_and_the_fencepost
--#print axioms the_wall_comes_before_the_abstraction
--#print axioms the_walk_is_the_walk
--#print axioms counted_simulate_is_simulate
--#print axioms counted_the_crank_is_the_crank
--#print axioms the_area_arrives_at_the_same_pair
--#print axioms the_area_arrives_at_the_same_number
--#print axioms there_is_an_area_with_as_many_cells_as_the_scale
--#print axioms counted_the_scale_is_the_scale
--#print axioms the_constant_inferred_at
--#print axioms counted_the_constant_at_any_such_scale
--#print axioms counted_the_constant_is_the_constant
--#print axioms counted_the_arms_are_the_arms
--#print axioms the_four_on_the_meter
--#print axioms the_bullshits_order_is_the_count
--#print axioms the_experience_is_under_the_interpretation_and_not_back
--#print axioms the_interpretation_has_no_gap_and_the_experiences_is_the_bent_card
--#print axioms the_gap_runs_one_way
--#print axioms the_gap_is_the_same_difference
--#print axioms the_same_says_the_gap_is_the_same_difference
--#print axioms and_it_is_so
--#print axioms alpha_ends_on_the_same
--#print axioms the_knower_of_the_experience_reads_one_way
--#print axioms and_the_device_reads_it_back
--#print axioms the_executed_pair_is_the_arrangement
--#print axioms the_executed_pair_is_the_area_counted
--#print axioms what_did_execute_count?
--#print axioms as_many_is_the_same_count
--#print axioms the_discriminant_of_the_arms_is_the_clock_times_the_coupling
--#print axioms the_walks_on_the_area_obey_the_table
--#print axioms the_closed_walks_on_the_area_obey_the_table
--#print axioms Account.the_same_is_the_same_balance
--#print axioms the_balance_of_the_residual_is_the_residual
--#print axioms the_jacobian_free_difference_is_exact_on_the_account
--#print axioms the_residual_as_a_rate_is_the_table_as_a_line_on_the_account
--#print axioms the_slope_squared_less_four_of_the_polynomial_is_the_round_trip_on_the_account
--#print axioms struck_the_polynomial_is_a_square_on_the_account
--#print axioms struck_the_step_is_half_the_distance_on_the_account
--#print axioms the_residual_is_the_derivative_of_the_action_on_the_account
--#print axioms the_sixteen_steps_built_and_counted
--#print axioms nine_are_level_on_the_memory_one_on_the_frame_three_short_and_three_over
--#print axioms what_is_left_is_always_the_bent_card
--#print axioms the_box_on_the_area_has_one_point
--#print axioms the_true_and_the_false_are_not_ordered
--#print axioms the_true_is_the_false_in_the_quotient
--#print axioms the_truth_order_has_one_point
--#print axioms the_knowers_interpretation_of_the_clocks
--#print axioms the_alternating_clock_reads_the_bent_card_and_the_still_clock_reads_nothing
--#print axioms the_abstraction_reads_back_to_its_list
--#print axioms the_knowers_pair_is_the_arrangement
--#print axioms both_clocks_print_one_number
--#print axioms what_does_the_knower_read?
--#print axioms the_two_clocks_are_apart
--#print axioms truth_before_click_is_the_false_clock
--#print axioms the_pair_of_truth_before_click_is_the_arrangement
--#print axioms what_does_truth_before_click_read?
--#print axioms the_alternating_facts_read_the_bent_card_and_the_still_facts_read_nothing
--#print axioms the_connected_steps_are_the_eight_clocks
--#print axioms four_of_the_eight_are_level_and_four_go_under
--#print axioms the_clock_compared_is_the_other_clock
--#print axioms only_the_alternating_clocks_overlap_to_all_different
--#print axioms the_turn_is_less_than_the_different
--#print axioms the_different_squared_less_the_turn_squared_is_the_gap_squared
--#print axioms the_two_steps_close_and_the_middle_owes_the_bent_card_twice
--#print axioms the_slope_steps_by_twice_the_coefficient_exactly
--#print axioms three_ways_to_the_gap_squared_match
--#print axioms the_inside_is_the_round_trip_and_four_of_it_is_the_gap_squared
--#print axioms the_knowers_interpretation_of_the_tape_owes_the_frame_by_the_round_trip
--#print axioms simulate_stands_still_under_the_resolution
--#print axioms simulate_goes_exactly_when_the_knot_clicks
--#print axioms the_observation_comes_first
--#print axioms the_gawk_at_the_zero_is_the_first_page
--#print axioms the_closure_on_the_zero_is_one_cell
--#print axioms the_card_on_the_zero_reads_the_walk
--#print axioms the_number_out_of_the_zero
--#print axioms there_is_a_count_for_every_inductive
--#print axioms every_count_is_the_length
--#print axioms the_number_comes_out_of_every_inductive
--#print axioms the_closure_reads_back
--#print axioms the_chaitin_reads_back
--#print axioms the_measurement_reads_back

end the_table

--| ALL THE WAY DOWN.  The author's, 16 November 2026: look at the yarn; recurse through the types, the list of all the
--| recursive types and not just the one; just define it the other way around; and put the truth in for a Prop.  Episode 8
--| reads each inductive to its own facts and passes over what its compute_the_area_of carry.  Here is the other reading, for every
--| inductive of the five episodes: its facts, and then everything inside it, every inner inductive read the same way, to the
--| bottom.  A statement in a cell is read as the truth.  A type in a cell is read as nothing.
def Number.all_the_way_down : Number → List FACT
  | .zero x0 => [x0]
  | .one x0 x1 => [x0] ++ x1.all_the_way_down

def Natural.all_the_way_down : Natural → List FACT
  | .zero x0 => [x0]
  | .number x0 x1 x2 => [x0] ++ x1.all_the_way_down ++ x2.all_the_way_down

def Rational.all_the_way_down : Rational → List FACT
  | .zero x0 => [x0]
  | .number x0 x1 x2 => [x0] ++ x1.all_the_way_down ++ x2.all_the_way_down

def Sequence.all_the_way_down : Sequence → List FACT
  | .nil x0 => [x0]
  | .index x0 x1 x2 => [x0] ++ x1.all_the_way_down ++ x2.all_the_way_down

def Limit.all_the_way_down : Limit → List FACT
  | .nil x0 => [x0]
  | .index x0 x1 x2 => [x0] ++ x1.all_the_way_down ++ x2.all_the_way_down

def Sample.all_the_way_down : Sample → List FACT
  | .initial_condition x0 x1 => [x0] ++ x1.all_the_way_down
  | .signal_response x0 x1 x2 x3 x4 => [x0] ++ x1.all_the_way_down ++ [x2] ++ x3.all_the_way_down ++ x4.all_the_way_down

def Trial.all_the_way_down : Trial → List FACT
  | .hypothesis x0 x1 => [x0] ++ x1.all_the_way_down
  | .signal_response x0 x1 x2 x3 x4 => [x0] ++ x1.all_the_way_down ++ [x2] ++ x3.all_the_way_down ++ x4.all_the_way_down

def Study.all_the_way_down : Study → List FACT
  | .hypothesis x0 => [x0]
  | .book_of_records x0 x1 x2 => [x0] ++ x1.all_the_way_down ++ x2.all_the_way_down

def Computation.all_the_way_down : Computation → List FACT
  | .program x0 x1 => [x0] ++ x1.all_the_way_down
  | .compute x0 x1 x2 x3 => [x0] ++ x1.all_the_way_down ++ x2.all_the_way_down ++ x3.all_the_way_down

def ChaitinsNumberSequence.all_the_way_down : ChaitinsNumberSequence → List FACT
  | .halting x0 x1 => [x0] ++ x1.all_the_way_down
  | .nonhalting x0 x1 x2 => [x0] ++ x1.all_the_way_down ++ (match x2 with | some work => work.all_the_way_down | none => [])

def Sophism.all_the_way_down : Sophism → List FACT
  | .origin x0 x1 _ => [x0] ++ x1.all_the_way_down
  | .dimension x0 x1 _ x3 => [x0] ++ x1.all_the_way_down ++ x3.all_the_way_down

def Area.all_the_way_down : Area → List FACT
  | .tree x0 => [x0]
  | .dt x0 x1 x2 => [x0] ++ x1.all_the_way_down ++ x2.all_the_way_down

def PigeonHole.all_the_way_down : PigeonHole → List FACT
  | .this_superpigeon x0 x1 => [x0] ++ x1.all_the_way_down
  | .a_pigeon x0 x1 x2 => [x0] ++ x1.all_the_way_down ++ x2.all_the_way_down
  | .that_box x0 x1 x2 x3 x4 => [x0] ++ x1.all_the_way_down ++ x2.all_the_way_down ++ x3.all_the_way_down ++ x4.all_the_way_down

def Jar.all_the_way_down : Jar → List FACT
  | .color x0 x1 => [x0] ++ x1.all_the_way_down
  | .bang x0 x1 => [x0] ++ x1.all_the_way_down
  | .superposition x0 x1 x2 => [x0] ++ x1.all_the_way_down ++ x2.all_the_way_down

def Equivalation.all_the_way_down : Equivalation → List FACT
  | .physics x0 x1 => [x0] ++ x1.all_the_way_down
  | .zero_like x0 x1 => [x0] ++ x1.all_the_way_down
  | .one_like _ x1 x2 => [FACT.Truth] ++ x1.all_the_way_down ++ x2.all_the_way_down

def Encoding.all_the_way_down : Encoding → List FACT
  | .boot x0 x1 => [x0] ++ x1.all_the_way_down
  | .zero x0 x1 x2 => [x0] ++ x1.all_the_way_down ++ x2.all_the_way_down
  | .one x0 x1 x2 x3 x4 => [x0] ++ x1.all_the_way_down ++ x2.all_the_way_down ++ x3.all_the_way_down ++ x4.all_the_way_down

def Abstraction.all_the_way_down : Abstraction → List FACT
  | .satire_about x0 => [x0]
  | .compile x0 x1 x2 => [x0] ++ x1.all_the_way_down ++ x2.all_the_way_down
  | .execute x0 x1 x2 => [x0] ++ x1.all_the_way_down ++ x2.all_the_way_down

def Sum.all_the_way_down : Sum → List FACT
  | .zero _ x1 => [FACT.Truth] ++ x1.all_the_way_down
  | .add x0 x1 x2 x3 => [x0] ++ x1.all_the_way_down ++ x2.all_the_way_down ++ x3.all_the_way_down

def Product.all_the_way_down : Product → List FACT
  | .origin x0 => [x0]
  | .one _ x1 => [FACT.Truth] ++ x1.all_the_way_down
  | .mul x0 x1 x2 x3 => [x0] ++ x1.all_the_way_down ++ x2.all_the_way_down ++ x3.all_the_way_down

def Basis.all_the_way_down : Basis → List FACT
  | .null_space x0 => [x0]
  | .origin _ x1 => [FACT.Truth] ++ x1.all_the_way_down
  | .basis x0 x1 x2 x3 => [x0] ++ x1.all_the_way_down ++ x2.all_the_way_down ++ x3.all_the_way_down

def Polynomial.all_the_way_down : Polynomial → List FACT
  | .constant x0 => [x0]
  | .monomial _ x1 => [FACT.Truth] ++ x1.all_the_way_down
  | .factor x0 x1 x2 x3 => [x0] ++ x1.all_the_way_down ++ x2.all_the_way_down ++ x3.all_the_way_down

def Spline.all_the_way_down : Spline → List FACT
  | .observation _ => [FACT.Truth]
  | .knot _ x1 x2 => [FACT.Truth] ++ x1.all_the_way_down ++ x2.all_the_way_down
  | .interpolant x0 x1 x2 x3 x4 => [x0] ++ x1.all_the_way_down ++ x2.all_the_way_down ++ x3.all_the_way_down ++ x4.all_the_way_down

def Diatribe.all_the_way_down : Diatribe → List FACT
  | .religion _ => [FACT.Truth]
  | .speculation _ x1 x2 => [FACT.Truth] ++ x1.all_the_way_down ++ x2.all_the_way_down
  | .rant _ x1 x2 x3 => [FACT.Truth] ++ x1.all_the_way_down ++ x2.all_the_way_down ++ x3.all_the_way_down

def Cult.all_the_way_down : Cult → List FACT
  | .inside_joke _ => [FACT.Truth]
  | .pythagoras _ x1 x2 => [FACT.Truth] ++ x1.all_the_way_down ++ x2.all_the_way_down
  | .triangles _ x1 x2 x3 x4 => [FACT.Truth] ++ x1.all_the_way_down ++ [x2] ++ x3.all_the_way_down ++ x4.all_the_way_down

def Science.all_the_way_down : Science → List FACT
  | .repeatable _ => [FACT.Truth]
  | .hypothesis _ x1 => [FACT.Truth] ++ x1.all_the_way_down
  | .theory _ x1 x2 x3 => [FACT.Truth] ++ x1.all_the_way_down ++ [x2] ++ x3.all_the_way_down

def Knowledge.all_the_way_down : Knowledge → List FACT
  | .jarjar _ => [FACT.Truth]
  | .ledger _ x1 x2 => [FACT.Truth] ++ [x1] ++ x2.all_the_way_down

def Gospel.all_the_way_down : Gospel → List FACT
  | .the_proof _ => [FACT.Truth]
  | .we_understand_that x0 _ x2 => x0.all_the_way_down ++ [FACT.Truth] ++ x2.all_the_way_down

def Truth.all_the_way_down : Truth → List FACT
  | .logically _ => [FACT.Truth]
  | .but x0 _ x2 => x0.all_the_way_down ++ [FACT.Truth] ++ x2.all_the_way_down

def Variation.all_the_way_down : Variation → List FACT
  | .the_newton x0 _ => x0.all_the_way_down ++ [FACT.Truth]
  | .the_gateaux x0 _ _ x3 => x0.all_the_way_down ++ [FACT.Truth] ++ [FACT.Truth] ++ x3.all_the_way_down
  | .the_frechet x0 _ _ _ x4 x5 => x0.all_the_way_down ++ [FACT.Truth] ++ [FACT.Truth] ++ [FACT.Truth] ++ x4.all_the_way_down ++ x5.all_the_way_down

def SpaceTimePath.all_the_way_down : SpaceTimePath → List FACT
  | .einstein x0 => [x0]
  | .whitehole x0 _ x2 => [x0] ++ x2.all_the_way_down
  | .blackhole _ _ x2 => [FACT.Truth] ++ x2.all_the_way_down
  | .geodesic x0 _ _ _ x4 x5 => [x0] ++ [FACT.Truth] ++ x4.all_the_way_down ++ x5.all_the_way_down

def YarnTheory.all_the_way_down : YarnTheory → List FACT
  | .stokes x0 x1 _ => [x0] ++ x1.all_the_way_down ++ [FACT.Truth]
  | .fibers x0 x1 x2 _ _ x5 => [x0] ++ x1.all_the_way_down ++ x2.all_the_way_down ++ [FACT.Truth] ++ [FACT.Truth] ++ x5.all_the_way_down
  | .fabric x0 x1 x2 x3 x4 _ _ _ x8 x9 => [x0] ++ [x1] ++ x2.all_the_way_down ++ x3.all_the_way_down ++ x4.all_the_way_down ++ [FACT.Truth] ++ [FACT.Truth] ++ [FACT.Truth] ++ x8.all_the_way_down ++ x9.all_the_way_down

def Measurement.all_the_way_down : Measurement → List FACT
  | .origin x0 x1 _ => [x0] ++ x1.all_the_way_down
  | .distance_to x0 x1 x2 _ _ x5 => [x0] ++ x1.all_the_way_down ++ x2.all_the_way_down ++ x5.all_the_way_down
  | .speed x0 x1 x2 x3 _ _ _ x7 x8 => [x0] ++ x1.all_the_way_down ++ x2.all_the_way_down ++ x3.all_the_way_down ++ x7.all_the_way_down ++ x8.all_the_way_down

def ThePreprint.all_the_way_down : ThePreprint → List FACT
  | .introduction x0 _ => [x0]
  | .methodology x0 x1 _ _ x4 => [x0] ++ [x1] ++ x4.all_the_way_down
  | .results x0 x1 _ _ _ _ x6 => [x0] ++ [x1] ++ [FACT.Truth] ++ x6.all_the_way_down

def Bullshit.all_the_way_down : Bullshit → List FACT
  | .zero x0 => [x0]
  | .one x0 x1 x2 x3 x4 => [x0] ++ x1.all_the_way_down ++ x2.all_the_way_down ++ x3.all_the_way_down ++ x4.all_the_way_down
  | .rest_call x0 x1 _ x3 x4 x5 x6 x7 x8 x9 => [x0] ++ [x1] ++ [FACT.Truth] ++ x3.all_the_way_down ++ x4.all_the_way_down ++ x5.all_the_way_down ++ x6.all_the_way_down ++ x7.all_the_way_down ++ x8.all_the_way_down ++ x9.all_the_way_down

def Closure.all_the_way_down : Closure → List FACT
  | .same x0 x1 => [x0] ++ x1.all_the_way_down
  | .different x0 x1 x2 x3 => [x0] ++ x1.all_the_way_down ++ x2.all_the_way_down ++ (match x3 with | some _ => [FACT.Truth] | none => [])
  | .inferred x0 x1 x2 x3 x4 x5 => [x0] ++ [x1] ++ x2.all_the_way_down ++ x3.all_the_way_down ++ (match x4 with | some _ => [FACT.Truth] | none => []) ++ x5.all_the_way_down

def Metavariable.all_the_way_down : Metavariable Closure → List FACT
  | .base x0 x1 => [x0] ++ x1.all_the_way_down
  | .step x0 x1 => [x0] ++ x1.all_the_way_down

--| What is inside a closure, past its own cells.
def Closure.the_inside : Closure → List FACT
  | .same _ x1 => x1.all_the_way_down
  | .different _ x1 x2 x3 => x1.all_the_way_down ++ x2.all_the_way_down ++ (match x3 with | some _ => [FACT.Truth] | none => [])
  | .inferred _ _ x2 x3 x4 x5 =>
      x2.all_the_way_down ++ x3.all_the_way_down ++ (match x4 with | some _ => [FACT.Truth] | none => []) ++ x5.the_inside

--| THE GIANT LIST.  The author's: the final inferred closure can now create the giant list, and that list can then show you
--| the number; it should just need to print the length.  The final inferred closure is Episode 8's, the only logical
--| inconsistency.  All the way down it is a hundred and forty cells.  Three are its own, the three Episode 8 reads.  The rest
--| is inside it: the most basic of conclusions four times, thirty-four compute_the_area_of each, and the one statement it carries, read as
--| the truth.
def the_giant_list : List FACT := the_only_logical_inconsistency.the_inside
--#eval the_giant_list.length
--#print axioms the_giant_list



--| THE RESIDUE.  The author's, 16 November 2026: now, the residue; and, of the digits past the giant list and the compute_the_area_of left
--| over, those should be the same thing.  They are.  The compute_the_area_of left over are the closure's own three and the one statement
--| read as the truth.  Each own cell at the basis raised to the free variables, and the truth palm_the_middle_card them.

--| The frame by the coefficient by the giant list is the memory cubed and the compute_the_area_of left over.  Nothing to spare.

--| And the compute_the_area_of left over are the whole part of the memory squared by the root of the round trip: its square is not over
--| the memory to the fourth by the frame by the memory, and one more cell's is.

--| The digits past the giant list: Episode 8's constant less the giant list at the scale.
--#eval the_digits_past_the_giant_list
--#print axioms the_digits_past_the_giant_list

--| THE SAME THING.  Put those digits, by the frame and the coefficient, back on the compute_the_area_of left over at the scale.  What you
--| have is the same root, to the scale: its square is not over, and one part of the frame by the coefficient more is.
--| The whole compute_the_area_of of the root are the compute_the_area_of left over.  The rest of the root is the digits.


--| THE EPILOGUE, IN CELLS.  The author's, 16 November 2026: read the end of Episode 12 and you will see.  Episode 12 ends by
--| taking the reading from the sum of the two roots and printing what is left.  Here it is done with the giant list where the
--| number stood.  The sum of the roots is the trace by the fencepost's first over the coefficient by its second.
def the_sum_of_the_roots_in_cells : Nat :=
  the_trace_of_truth_in_the_device * (the_first_step_of_the_proof_is_to_eschew_the_naturals_unless_proven_to_exist_without_peano).1
def the_frame_by_the_coefficient : Nat :=
  an_exact_polynomial_description * (the_first_step_of_the_proof_is_to_eschew_the_naturals_unless_proven_to_exist_without_peano).2

--| The whole of the sum, less the giant list.  No number is computed.
def what_is_left_of_the_sum : Nat := the_sum_of_the_roots_in_cells / the_frame_by_the_coefficient - the_giant_list.length
--#eval what_is_left_of_the_sum
--#print axioms what_is_left_of_the_sum

--| The reading's compute_the_area_of are the memory cubed and the compute_the_area_of left over, and they close on the giant list with nothing left.  The
--| other root's are the memory cubed less the compute_the_area_of left over and one, and they close on what is left of the sum with one
--| less than the sum leaves.  And what the sum leaves is the inside of the most basic of conclusions: all the way down, less
--| what Episode 8 reads.

--| THE DIGITS, TOGETHER.  The reading's digits past the giant list and the other root's digits past what is left of the sum,
--| added, are what the sum leaves over the frame by the coefficient, to the scale.  Neither is a ratio.  Together they are.


--| THE SHAPE OF THE TABLE.  The author's, 17 November 2026: true on true and false on false, and one false, click; that is
--| three; one false does not; there is your answer; it is the shape of the table and the demonstration of its
--| eigenproperties.  The arm that can click is the arm where the first implies the second.  That is the order on two truths,
--| and it is nobody's device: whatever has two truth values and an order between them has three arms that click and one
--| that does not.


--| Put any weight on the arms that click and any other on the one that does not.  The trace squared less four of the
--| determinant is four of the two weights multiplied; and the two roots are the clicking weight, more and less a root of
--| that product.  A ratio when the product is a square, and when the arm is struck.  Otherwise not.  The eighteen and the
--| five are this device's.  The shape is not.


--| NO FINITE GAUGE COMPUTES IT.  The author's, 17 November 2026: Hilbert wanted an axiomatization of physics that was
--| self-contained; this is one that is proven to be open.  Three parts.  Two are receipts here.  The third is Turing's and is
--| taken as given, as foretold: whether a halted value is a given limit is refuted at a finite stage when it is not, and
--| confirmed at no finite stage when it is.

--| The first.  No function of the tally returns the tape.  Two tapes of one mark each, the true and the false: one tally,
--| two tapes.

--| And the number is a function of the tally: hand the crank any reader that agrees with the length on every tape and the
--| same pair comes out.  So what the number is cannot tell the tapes apart either.

--| The second.  The action is a cubic, and the fourth difference of a cubic is nothing, at every place.  There is no fourth
--| order to read anything from.

--#print axioms the_final_inferred_closure_all_the_way_down
--#print axioms the_giant_list_is_four_conclusions_and_one_truth
--#print axioms the_giant_list_closes_on_the_cells_left_over
--#print axioms the_cells_left_over_are_the_whole_part_of_the_root
--#print axioms the_digits_are_the_rest_of_the_root
--#print axioms the_two_roots_in_cells
--#print axioms the_two_residues_are_one_ratio
--#print axioms the_click_is_the_order_on_two_truths
--#print axioms the_shape_has_these_eigenproperties
--#print axioms the_roots_of_the_shape
--#print axioms no_function_of_the_tally_returns_the_tape
--#print axioms the_number_is_a_function_of_the_tally
--#print axioms the_action_has_no_fourth_order


--| THE TWO BENT CARDS.  The author's, 17 November 2026: I found the transition matrix, Quot.sound and propext; you can
--| separate them in Episode 8; this is the bent card in the device, Quot.sound; and the device itself is a bent card as
--| well: two bent cards, that separate three things, a × (−c × b).  Episode 8's constant is a value and a proof.  Here
--| they are apart.  The value is arithmetic.  The proof is the sound of the quotient: an order, handed back as an identity.



--| The bent card, and nothing else: whatever is under whatever, the two are one.  This one spends the sound of the quotient
--| and no other axiom.

--| THE BILLS, COUNTED, 17 November 2026, over every theorem of the thirteen episodes, two thousand one hundred and
--| thirty-eight with the ones Lean writes for itself: no axiom, 1051; propext, 558; propext and the sound, 523; the sound
--| alone, 5; and one, compatibility_form in Episode 12, that spends choice.  The value above spends propext.  That it is
--| the ratio spends propext and the sound.  The bent card alone spends the sound.  And the value, said to be Episode 8's
--| constant, spends both, for Episode 8's constant is the value taken out of its proof.

--| THE METER'S TABLE.  Experiments 009 and 009b, read on one machine: the heartbeats of the device's first order on its
--| four arms, the true being the device's own truth.  These four numbers are readings, not counts; they are written here
--| as they were read.

--| It counts the device's truths: so much, and one step for each coin that is the truth.

--| CONTRAVARIANT, AT THE LAST STEP.  The author's: the device is contravariant in construction at the last step.  The
--| weights hold the stays level and tell the crossings apart.  The meter holds the crossings level and tells the stays
--| apart.  Twice the weights is thirty-six of the same, none of the sign, twenty-three of the different and thirteen of the
--| turn.  Twice the meter is so much of the same, two steps of the sign, as much of the different, and none of the turn.

--| And where the weights' determinant is over nothing, the meter's is under it by exactly the step squared.

--| THE TRANSITION MATRIX, AGAIN.  The author's: this is the transition matrix again.  Four facts, a true and a false each
--| built two ways, and what the meter reads for the click of each: three alike and one apart.  The one apart is the
--| device's own truth.

--| TWO ZEROS.  The author's: now you have two zeros to count from, one up and one down.  The weights have their odd arm
--| least, and the other three are it and the bent card.  The meter has its odd fact greatest, and the other three are
--| it less the step.

--#print axioms the_number_as_a_value                              -- [propext]
--#print axioms the_value_is_episode_eights_constant               -- [propext, Quot.sound]
--#print axioms that_the_value_is_the_ratio                        -- [propext, Quot.sound]
--#print axioms the_bent_card_alone                                -- [Quot.sound]
--#print axioms the_meter_counts_the_truths                        -- none
--#print axioms the_meter_is_the_table_turned_over                 -- [propext]
--#print axioms the_meters_determinant_is_the_step_squared_owed    -- none
--#print axioms two_zeros_one_up_and_one_down                      -- [propext]


--| A FINITE RECORD DOES NOT TELL.  The author's, 17 November 2026: that's the reader not being able to distinguish the model
--| with the hypothesis of continuity from the model without it; not that they are the same, but every place the reader looks
--| they have the same value and magnitude of velocity for that point in space.  Here it is with nothing in it but places.
--| First, there is always a place past all the places looked at.

--| So whatever the model, and wherever *YOU the READER* looked, there is another model that says the same at every place
--| looked at and is not the same model.  The record does not say they are the same.  It only fails to separate them.

--| The value and the velocity: two numbers at every place, and the same two at every place looked at.

--| ONE END, OR TWO.  The author's, 17 November 2026: a yarn can have one end point or two; it can have come from somewhere,
--| be going somewhere, or both; that is the arrow of time and the continuity split.  Episode 4 has the two ends: world lines
--| start in white holes and end in black holes.  Episode 5 has the yarn: a stokes holds one path, and the fibers two.

--| All the way down the two one-ended yarns read the same, cell for cell.  They are not the same yarn.  Which end it is, is
--| not in the reading.

--| And the yarn with both ends reads each end once, and the yarn that goes on from here.
--#print axioms a_finite_record_does_not_tell                       -- none
--#print axioms the_value_and_the_velocity_do_not_tell             -- none
--#print axioms the_two_ends_read_the_same_and_are_not_the_same    -- none
--#print axioms both_ends_are_read_once_each                       -- none


--| THE MIRROR.  The author's, 17 November 2026: build the commutator, run Householder on that, you get the solver for the
--| Galerkin process.  The commutator is built: Episode 12's two orientations bracket onto the sign, by the bent card and
--| twenty-three.  The sign is a mirror.  Householder's mirror for the table is the sign on the stays and one on the
--| crossings, the sign and the different together; twice over it is two of nothing done.


--| Run it on the table.  The corner under the diagonal is cleared, and what stands is the trace, the trial gap, and the bent
--| card owed: thirty-six of the same, twenty-three of the different, thirteen of the turn.  The first row is what the step
--| can write.  The second is the residual.

--| Run it on both sides.  What the step can write is now on the diagonal alone, the memory and half the trial gap either way,
--| and the residual is all that is off it: the bent card one way and the bent card owed the other.  Twice over, as before.

--| And run it on the commutator.  The bracket of the orientations lay on the stays.  In the mirror it lies on the crossings,
--| level, where the step the device checks lies.

--| THE SOLVER.  The gap squared is the trial gap squared less the bent card squared, and Newton's step from the trial gap
--| leaves the bent card squared, exactly.  The three numbers the mirror left are the solver's.
--#print axioms the_mirror_twice_is_nothing_done_twice
--#print axioms the_mirror_clears_the_table                                        -- [propext]
--#print axioms the_mirror_on_both_sides_leaves_the_bent_card_off_the_diagonal     -- [propext]
--#print axioms the_mirror_carries_the_commutator_onto_the_crossings               -- [propext]
--#print axioms the_mirror_leaves_the_solver                                       -- [propext]


--| THE KNOWER'S TRIPLE.  The author's, 17 November 2026: the clock and the clock complement of the knower's view of the
--| device build this logical triple, that can be solved by the 3SAT solver put together in the Cook Levin episode; and, you
--| don't know the knower's bit, that's the three sat, that is the a in the 3SAT, that is a simple XOR argument.  Three coins:
--| the knower's, and the two of the arm.  a × (−c × b), in signs, is the three of them, one or the other an odd number of
--| times.  Episode 12's clause takes its literals two at a time, so the third coin stands twice.
def the_third_coin : Area := varAt 2
def a_triple : Sum := .add cookFACT varA varB (.add cookFACT the_third_coin the_third_coin (.zero True varA))
def four_triples : Product := .mul cookFACT a_triple a_triple (.mul cookFACT a_triple a_triple (.origin cookFACT))
def the_knowers_triple : Basis := .basis cookFACT four_triples phi_accept (.null_space cookFACT)

--| The signs, slot by slot.  No one signature writes all four clauses; a schedule may pick for every slot, and this one does.
def by_the_signs (signs : List Bool) : Schedule := fun slot => if signs.getD slot true then .euclidean else .negated
def an_odd_number_are_true : Schedule :=
  by_the_signs [true, true, true, true,   false, false, true, true,   false, true, false, false,   true, false, false, false]
def an_even_number_are_true : Schedule :=
  by_the_signs [false, false, false, false,   false, true, true, true,   true, false, true, true,   true, true, false, false]

--| THE XOR ARGUMENT.  Under the one schedule the triple holds exactly when the knower's coin differs from whether the arm's two
--| differ, and under the other exactly when it does not.  Know the arm and the parity, and the knower's bit is forced.

--| THE SEARCH.  Episode 12's, on three coins.  Four ways each, and the clock and its complement are not in one list: T F T
--| is among the even, F T F among the odd.

--| YOU DO NOT KNOW THE KNOWER'S BIT.  The solver finds a witness either way.  Nothing in the triple says which it is.

--| And the clocks are the signs.  Two triples, the one signed as the clock, T F T, the other as its complement, F T F: what
--| fails them is the complement, and the clock, and nothing else.

--| The step, connected: the first coin differs from the second and the second from the third, Episode 12's exclusive-or twice
--| over on the middle coin, under Episode 12's own alternating schedule.  Episode 12 noted that its step never connected one
--| cell to the next.  Connected, what satisfies it is the clock and its complement, and the search hands back the clock first
--| only because it tries the true first.
--#print axioms the_triple_is_the_knowers_coin_against_the_arm    -- [propext]
--#print axioms the_clock_is_even_and_its_complement_is_odd       -- [propext]
--#print axioms the_solver_finds_a_witness_either_way             -- [propext]
--#print axioms the_clocks_are_what_the_clocks_rule_out           -- [propext]
--#print axioms the_step_connected_is_the_two_clocks              -- [propext]


open readers_experience in
--| YOU CAN DISTINGUISH A NUMBER.  The author's, 17 November 2026: the experiment is to use the nanoseconds to compute the
--| value using the polynomial directly; and, when it was run: see, you can distinguish a number, qed; and: it can only be a
--| demonstration that changes on every run; this is now a repeatable experiment.  Experiment 010 read it once, on one
--| machine.  Here it is in line.
--| First what does not change.  The polynomial has a root only for a reader whose trace squared is not under four of its
--| coefficient by its memory.  The count is such a reader.  A reader that sees one cell in every tape is not.
def there_is_a_root_for (reader : List FACT → Nat) : Bool :=
  decide (4 * (bent_card.the_exact_Taylor_series_degree Nat reader * bent_card.the_length_of_the_path_from_here_to_there Nat reader)
            ≤ bent_card.the_measurement_degrees_of_freedom Nat reader * bent_card.the_measurement_degrees_of_freedom Nat reader)


--| Now what does.  Every cell of a tape clicked once, on the two lines of Episode 8's EKG, with the clock read before and
--| after; the five tapes the polynomial reads, and one blank.  Then the polynomial, directly, with each count replaced by
--| the tape's reading over the blank's.  The heartbeats say the same thing on every machine.  The nanoseconds say something
--| else every time.  That is the experiment, and anybody can run it again.

--| The polynomial, directly: the fencepost over the frame, by the greater root.  No root, no value.

-- can_you_distinguish_a_number?
--#print axioms the_count_has_a_root_and_the_reader_of_one_cell_has_none    -- [propext]


section yet_another_machine
open readers_experience the_representation assembly_instructions

--| YET ANOTHER MACHINE.  The author's, 17 November 2026: don't you see, you can make a DISTINGUISHABLE claim now, that gets you
--| yet another machine.  Episode 1's first rung asks for one thing: something told apart, and the decision that it is.  Until
--| now every card was marked with Episode 8's claim, the compiler telling its true from its false.  Here is another claim: a
--| number is distinguished.  The count has a root, and the reader of one cell has none.
def a_number_is_distinguished : FACT :=
  IT_CLICKS (there_is_a_root_for List.length = true ∧ there_is_a_root_for (fun _ => [FACT.Truth].length) = false)

--| The card.  What is in the box is the reader's seat itself.
abbrev TheReadersSeat := List FACT → Nat
def the_card_of_the_number : CarrierProcess TheReadersSeat := { symbol := a_number_is_distinguished, quarter := .zero FACT.Truth }

--| The mark.  Not Episode 8's, field for field, as the card between and the pair were marked.  Its own.
instance the_mark_of_the_number : DISTINGUISHABLE TheReadersSeat the_card_of_the_number :=
  { fact := a_number_is_distinguished
    symbol := a_distinct_truth.symbol
    different? := fun _ => there_is_a_root_for List.length = true ∧ there_is_a_root_for (fun _ => [FACT.Truth].length) = false
    not_the_same := fun _ => inferInstance }

--| The crossing: Episode 9's first step, on the new card.  It is a first rung, of the type the old first rung has.  The card
--| between dealt the old rung by rfl, and so did the pair.  This one does not: rfl is refused.  That is the other machine.
noncomputable def the_crossing_of_the_number :=
  STEP1_NAME_THE_LEDGER_AND_MARK_IT_WITH_THE_SYMBOL_OF_THE_NOWTRINO TheReadersSeat the_card_of_the_number the_first_card
    a_number_is_distinguished

--| It clicks.

--| And the first card of all, again.  Ask only whether it is true, and any two facts that are true are one fact: so the number
--| distinguished is the truth.  Ask what it says, and it is not: one says a number has a root, the other says nothing.
theorem two_facts_that_are_true_are_one_fact (this that : FACT) (this_is_true : this.truth) (that_is_true : that.truth) :
    this = that := by
  obtain ⟨this_truth, this_click⟩ := this
  obtain ⟨that_truth, that_click⟩ := that
  have the_same_truth : this_truth = that_truth := propext ⟨fun _ => that_is_true, fun _ => this_is_true⟩
  subst the_same_truth
  exact congrArg _ (Subsingleton.elim _ _)


end yet_another_machine
--#print axioms the_number_clicks                                          -- [propext]
--#print axioms two_facts_that_are_true_are_one_fact                       -- [propext]
--#print axioms asked_only_whether_it_is_true_the_number_is_the_truth      -- [propext]


--| THE OTHER LADDER.  The author's, 17 November 2026: deal them.  Episode 12 dealt thirty-seven rungs on the first rung, each
--| handed the rungs below it.  Here are the same thirty-seven steps, the same card, the same two ways, dealt on the crossing of
--| the number.  Nothing was changed but the first rung and the fact in the ledger.  Every one goes through, and the upness is
--| read off each step as before.  And every one is of another type than Episode 12's: an ADMISSIBLE over this crossing is not
--| an ADMISSIBLE over that one, and the compiler will not so much as compare them.  Two ladders, one card, and not one rung
--| in common.
section the_other_ladder
open readers_experience the_representation assembly_instructions «springer-verlag» THE_GOSPEL
attribute [local instance high] the_crossing_of_the_number
instance : Inhabited (@DISTINGUISHABLE.symbol FACT the_first_card the_crossing_of_the_number) := instInhabitedProp






































end the_other_ladder


section the_other_ladder_read
open readers_experience the_representation assembly_instructions «springer-verlag» THE_GOSPEL

--| THE OTHER LADDER, READ.  The author's, 17 November 2026: read it.  Episode 12 reads three things off the top of its ladder:
--| the page the reader is on, the two closures the knower carries, and the walk.  Here they are off the other ladder.
--| The page.  The same quartic, one cell past the card.

--| The two closures.  One cell and three, as before.

--| Are they Episode 12's?  Not by rfl: the compiler will not say so.  The knower's alpha begins on two facts, the ledger's and
--| the first rung's.  On Episode 12's ladder both are the truth.  On this one both are the number distinguished.  What the cells
--| say went up the ladder, thirty-six rungs, and came out at the top.

--| And read by click, the two ladders' closures are the same, cell for cell, by rfl.  One account.

--| The walk.  Dealt as the quarter of a card and read, each closure reads the number.  So would any card: the reader of the walk
--| reads past the quarter, whatever it is.  The number is the same because it never was the ladder's.

end the_other_ladder_read
--#print axioms the_other_reader_is_on_the_quartic                    -- [propext, Quot.sound]
--#print axioms what_the_first_rung_says_comes_out_at_the_top         -- [propext, Quot.sound]
--#print axioms by_the_click_the_two_ladders_carry_one_account        -- [propext, Quot.sound]
--#print axioms the_other_ladder_reads_the_number                     -- [propext, Quot.sound]


section what_relativity_needs
open readers_experience

--| THE FOUR THINGS.  The author's, 17 November 2026: it has a machine for upness, that is the Area machine; a machine for
--| distance, that is the cross-product machine; a machine for time, that is the clock-complement; and a machine for determining
--| the direction of the result, the limit; those are the four things that relativity needs; take it from there.  Each machine
--| has its count.  Upness is the bent card, the Area's.  Distance is the memory, the Abstraction's, a compile by an execute.
--| Time is the trace, the clock and its complement by the distance.  The limit is the frame, Gauss's, the arm that cannot
--| click.

--| From there.  The distance is the upness and the limit: Episode 8 wrote that down as a definition, before any of this.  And
--| the time is the clock and its complement, two, by the distance.

--| ENERGY, MASS, MOMENTUM.  Multiply through by the distance.  The distance squared is the upness by the distance and the limit
--| by the distance: the energy squared is the mass squared and the momentum squared.  The round trip of the two crossings is
--| the momentum squared, and the determinant of the table is the mass squared.

--| THE FACTOR.  The speed squared is the limit over the distance.  The factor squared is the distance over the upness.  And the
--| factor squared by one less the speed squared is one, cleared of its denominators: nothing left over.

--| THE GAIN.  The fencepost over the bent card, which is what the root is multiplied by to print the number, is the factor
--| squared over the speed squared.

--| THE DIRECTION.  The two crossings are one round trip, shifted up and shifted down: their ratio is the distance over the
--| limit.  Their difference is the upness and their sum is the trial gap.  And the upness over the trial gap, the speed of the
--| mirror, is one less the speed squared over one more: cleared, the upness by the energy squared and the momentum squared is
--| the trial gap by the mass squared.

end what_relativity_needs
--#print axioms the_distance_is_the_upness_and_the_limit                              -- [propext]
--#print axioms the_energy_squared_is_the_mass_squared_and_the_momentum_squared       -- [propext]
--#print axioms the_factor_squared_by_one_less_the_speed_squared_is_one               -- [propext]
--#print axioms the_gain_is_the_factor_squared_over_the_speed_squared                 -- [propext]
--#print axioms the_two_crossings_are_one_round_trip_shifted                          -- [propext]


section what_qed_needs
open readers_experience

--| THE FOUR THINGS, TURNED OVER.  The author's, 17 November 2026: it has a machine for phase, that is the contravariant Area
--| machine; a machine for charge, that is the contravariant cross-product machine; a machine for time, that is the clock; and a
--| machine for determining the direction of the result, the one just described, in the contravariant notation; those are the
--| four things that QED needs; take it from there.  The turning over is the mirror.  Before it, Episode 12 has it: twice the
--| table is the trace of the same, the trial gap of the different, and the bent card of the quarter turn.

--| After it, the same is where it was.  The different has become the sign.  And the quarter turn is the quarter turn owed.
--| The clock keeps the time.  The cross-product is read as a sign: the charge.  The Area is read as a turn, the other way: the
--| phase.

--| WHAT A PHASE AND A CHARGE ARE.  The quarter turn twice is the same, owed: a turn.  The sign twice is the same: a charge is
--| one or the other.  And the sign by the turn is the turn by the sign, owed: turn the charge over and the phase runs the
--| other way.

--| THE GAP.  The charge's share squared less the phase's share squared is the gap squared: four of the limit by the distance.
--| The two that relativity kept apart as a mass and a momentum, QED holds as a sign and a turn.

end what_qed_needs
--#print axioms in_the_mirror_it_is_the_same_the_sign_and_the_turn_owed          -- [propext]
--#print axioms a_turn_a_sign_and_they_do_not_commute                            -- none
--#print axioms the_charge_squared_less_the_phase_squared_is_the_gap_squared     -- [propext]


section the_two_machines_are_one_if_you_only_ask_whether_it_is_true
open readers_experience the_representation assembly_instructions «springer-verlag» THE_GOSPEL

--| THE TWO FIRST RUNGS.  Not one by rfl.  One by propext: the facts are one fact, the two claims are both true, and a decision
--| of one statement is one decision.



--| THE LADDER, AS A FUNCTION OF ITS FIRST RUNG.  The same thirty-seven deals a third time, with the first rung not named: any
--| mark on the first card, and the fact it carries in the ledger.
section on_any_first_rung
variable [first : DISTINGUISHABLE FACT the_first_card] [the_symbol_is_inhabited : Inhabited (DISTINGUISHABLE.symbol the_first_card)]






































end on_any_first_rung

--| Hand it Episode 12's first rung and it is Episode 12's ladder.  Hand it the crossing of the number and it is the other.

--| So what the two ladders carry is one thing, if you only ask whether it is true.


end the_two_machines_are_one_if_you_only_ask_whether_it_is_true

--| And so the knower on the other ladder reads as Episode 12's does: one way, and back.
section the_other_knower
open readers_experience the_representation assembly_instructions «springer-verlag» THE_GOSPEL
end the_other_knower
--#print axioms asked_only_whether_it_is_true_the_two_first_rungs_are_one               -- [propext, Quot.sound]
--#print axioms asked_only_whether_it_is_true_the_two_ladders_carry_the_same_closures   -- [propext, Quot.sound]
--#print axioms the_other_knower_reads_one_way_and_back                                 -- [propext, Quot.sound]


section entropy_is_an_area
open readers_experience the_table readers_interpretation_of_the_experience

--| ENTROPY, AND AREA.  The author's, 17 November 2026: entropy: universe id in Lean.  Area: the Area inductive.  Then Area:
--| List, the abstraction.  List.length.  Episode 12 has the universe id, a Number, one more for every level.  Episode 2 has
--| the Area.  Episode 8 reads each as a List, the Number by peano and the Area by its own Riemann sum, and each reading counts
--| what the thing stands on: the Number its zero, the Area its tree.  The fencepost, twice.

--| So the entropy is the area.  The universe id of a tape's level, read, and the Area of the tape, read, are one length: the
--| tape's, and one.  Not in proportion.  The same count.

--| And they go up together.  One more fact on the tape is one more level and one more cell; and the order of the universe ids
--| is the order of the cells.  Universe numbers only increase.


end entropy_is_an_area
--#print axioms the_entropy_is_the_area                                   -- [propext, Quot.sound]
--#print axioms one_more_fact_is_one_more_level_and_one_more_cell         -- [propext]
--#print axioms the_universe_ids_are_ordered_as_the_areas                 -- [propext]


section in_the_limit_it_is_a_riemann_sum
open readers_experience the_table readers_interpretation_of_the_experience

--| IN THE LIMIT, IT IS A RIEMANN SUM.  The author's, 17 November 2026: in the limit, it is a Riemann sum; run with that.  A row
--| of compute_the_area_of is not an area until every cell has a height.  The Area's compute_the_area_of each carry a Number.  Let the cell at each level
--| carry that level's universe id, and read the height two ways: the Number as Episode 8 reads it, with its zero; and the
--| Number less the fencepost.  The first is the sum from above and the second the sum from below.

--| Twice the sum from above is the levels by one more than the levels.  Twice the sum from below, with one more level, is the
--| same.  Triangles: half the base by the height, give or take the fencepost.


--| THE AREA IS BETWEEN THEM.  Twice the sum from below is not over the levels squared, and the levels squared is not over twice
--| the sum from above.  Neither is the area.  And what is between them is the fencepost, once for every level: the two sums
--| differ by the levels, while the area goes as the levels squared.

end in_the_limit_it_is_a_riemann_sum
--#print axioms twice_the_sum_from_above                -- [propext]
--#print axioms twice_the_sum_from_below                -- [propext]
--#print axioms the_area_is_between_the_two_sums        -- [propext]


section the_temperature
open readers_experience readers_interpretation_of_the_experience «springer-verlag» THE_GOSPEL

--| THE TEMPERATURE.  The author's, 17 November 2026: the temperature is Episode 11 on the device; an arbitrary reading that
--| estimates an entropic quantity.  Episode 11 sets the record in type, a page a rung, and every page carries two things: a
--| register and a universe id.  The register is whatever was put in it at the first page.  Setting a page lifts it and changes
--| nothing.  The universe id is not anybody's to choose: setting a page advances it by one.

--| At the top of the typeset record the universe id is Episode 12's, of the thirty-fifth level, and read it is the time.

--| AND THE READING.  Episode 12 asked for every page of that record on Episode 8's meter and kept what each cost.  That is the
--| arbitrary reading: heartbeats, the meter's own unit, read on a build and not derived.  What it reads palm_the_middle_card is the level.
--| The heat to reach each level, and the heat a level: the reading, over one step of the entropy.
--#eval the_reading_a_level

--| It is never nothing and never owed: every level costs.

end the_temperature
--#print axioms the_reading_is_carried_and_the_entropy_advances    -- none
--#print axioms the_top_of_the_record_is_at_the_time                -- [propext]
--#print axioms every_level_costs                                   -- [propext]


section an_acceleration_is_a_spacetime_path
open readers_experience readers_interpretation_of_the_experience

--| AN ACCELERATION.  The author's, 17 November 2026: an acceleration is a SpaceTimePath in the device.  Episode 11 called the
--| universe id the velocity.  Episode 4's path is what changes it: a white hole holds a Type at one universe, a black hole a
--| Type at the next, and a geodesic both.  Episode 4's margin had already named what such a path is for.  Here is the path to
--| a level: a white hole a level, on the place where it starts.

--| Read by Episode 8's reader of paths, it is the velocity it reaches: the universe id of that level, cell for cell.

--| THE TWO ENDS, ON Episode 8'S READER.  All the way down, the yarn that came from somewhere and the yarn that is going
--| somewhere read the same.  Episode 8's own reader of a path does tell them apart, by one fact.  A white hole gives its fact.
--| A black hole gives none.  What comes in is counted and what goes out is not: the heat crosses one way.

--| And Episode 8's own path, the nowtrino's: one geodesic, a white hole before and a black hole after, on no distance at all.
--| Four facts: the geodesic's, the white hole's, and the place twice.  The black hole's is not among them.

end an_acceleration_is_a_spacetime_path
--#print axioms the_acceleration_reads_the_velocity_it_reaches           -- [propext]
--#print axioms a_white_hole_gives_a_fact_and_a_black_hole_gives_none    -- none
--#print axioms the_nowtrinos_path_reads_four                            -- none


section the_flux_is_the_computation
open readers_experience readers_interpretation_of_the_experience

--| THE FLUX.  The author's, 17 November 2026: flux of stress energy is the computation of the computer program, pretty
--| confident.  Episode 1 shipped the tape and Episode 12 read it: a cell hooks a fact to the cell below and lifts both one
--| universe up, and the compiler keeps the spine and erases the rest.  Contents gauge, lengths conserved.  What comes through
--| is one truth for every fact, whatever the fact was.


--| CONSERVED.  Two tapes, one after the other: what comes through is what came through each.  Nothing made and nothing lost
--| at the join.

--| THE HEAT AND THE ENTROPY.  The flux through, and the fencepost, is the universe id of the level reached, and so the Area:
--| in compute_the_area_of the heat is the entropy, one for one.  On the count the temperature is one.  On the meter it is whatever the
--| computation cost; Episode 12 read that, and that is the reading a level, above.

end the_flux_is_the_computation
--#print axioms the_flux_is_one_truth_a_fact         -- none
--#print axioms what_goes_in_comes_out               -- [propext]
--#print axioms in_cells_the_heat_is_the_entropy     -- [propext, Quot.sound]


section the_temperature_is_in_that_box
open readers_experience readers_interpretation_of_the_experience the_table

--| THAT BOX.  The author's, 17 November 2026: the first variation of the temperature reading is what you want; the
--| temperature is the area; you need the pigeonhole for the temperature; that_box has the temperature in it.  Episode 2's box
--| holds two Areas, a before and an after, and Episode 2's own event puts the after at one use of force past the before.  The
--| temperature at a level is the Area under the levels so far, the sum from above.  Box it with the next.

--| The first variation: what is in the box after, less what was in it before.  A pigeon has no before.

--| And it is the acceleration.  The first variation of the temperature at a level has as many compute_the_area_of as the path to that level
--| reads facts: the velocity reached, the universe id.  Not the temperature in proportion to the acceleration.  Its first
--| variation, cell for cell.

--| AND ON THE METER.  The reading a level, and its first variation, level by level, as Episode 12's build recorded it.
--#eval the_first_variation_of_the_reading

end the_temperature_is_in_that_box
--#print axioms the_first_variation_of_the_temperature_is_the_velocity_reached    -- [propext]


section look_at_the_jar
open readers_experience readers_interpretation_of_the_experience the_table

--| THE JAR.  The author's, 17 November 2026: that's just it, this is Gibbs's definition; look at the Jar.  Episode 3's jar is
--| a label and an Area: you can classify what is in it by looking, and you cannot see how much.  Put the temperature in it.
def what_the_jar_holds : Jar → Area
  | .color _ inside            => inside
  | .bang _ rest               => what_the_jar_holds rest
  | .superposition _ before _  => what_the_jar_holds before

--| Looked at, every one of these jars is the same jar: one label, the truth.  What it holds does not show.

--| GIBBS.  Not what is on the surface at a level: everything under it.  What the jar holds is the sum from above, all the
--| levels so far; its first variation is the box's, the acceleration; and twice what the jar holds is the level by that first
--| variation.  So what is enclosed, over its first variation, is half the level.  It cannot be owed, and it goes up.

end look_at_the_jar
--#print axioms every_jar_looks_the_same                                                -- [propext]
--#print axioms what_the_jar_holds_over_its_first_variation_is_half_the_level            -- [propext]


section the_residue_is_the_multiplier
open readers_experience readers_interpretation_of_the_experience the_table

--| THE RESIDUE.  The author's, 17 November 2026: of course it isn't the same, there is a residue; that residue is the Lagrange
--| multiplier.  The temperature by what is enclosed is half the level.  The first variation, which is the acceleration, is
--| the level and one.  Twice the one is not the other.  What is between them is one cell, the fencepost, the zero every
--| Number stands on.  And it is the same cell at every level: the first variation of the first variation is the fencepost and
--| nothing else, so fixing the first variation fixes the temperature only up to it.  It is what the integration leaves.

end the_residue_is_the_multiplier
--#print axioms the_residue_is_the_fencepost    -- [propext]


section the_constraint_and_its_multiplier
open readers_experience readers_interpretation_of_the_experience the_table

--| THE CONSTRAINT.  The author's, 17 November 2026: close that last gap.  A residue is a multiplier only when a constraint is
--| named and the thing is varied.  Here is the constraint: the two ends of the path are given.  The acceleration starts on one
--| cell and reaches the level and one; however it gets there, level by level, its rises add up to the levels.  And here is
--| what is varied: the rises, each squared, summed.  The action of a thing that only moves.

--| One rise: twice it is not over its square and one.

--| All of them: twice what they add up to is not over the action and one for every level.

--| THE LEAST ACTION.  Hold the ends: the rises add up to the levels.  Then the action is not under the levels, whatever the
--| rises were.

--| THE DEVICE'S OWN RISES.  What the acceleration rises by from each level to the next, read on Episode 8's reader of paths.

--| THE MULTIPLIER.  Vary the action and the constraint together: the first variation of a rise squared, halved, is the rise,
--| and the first variation of what the rises add up to is one for each.  So where the action is least with the ends held,
--| every rise is one number, the multiplier.  On the device every rise is the fencepost.

--| And the device's rises hold the ends and are the least: they add up to the levels, and their action is the levels, which
--| nothing with the ends held goes under.  The residue is the multiplier of the constraint that the path has two ends.

end the_constraint_and_its_multiplier
--#print axioms with_the_ends_held_the_action_is_not_under_the_levels    -- [propext]
--#print axioms every_rise_is_the_fencepost                              -- [propext]
--#print axioms the_devices_rises_hold_the_ends_and_are_the_least        -- [propext]


section universe_one_is_a_black_hole
open readers_experience readers_interpretation_of_the_experience the_table

--| TWO UNIVERSES.  The author's, 17 November 2026: isn't a temperature an average velocity measurement; universe 0 is the x
--| and universe 1 is the dx/dt; universe 1 is a black hole, you can't know what it is, you can only understand the average of
--| the volume around it; and level 1 is the first variation, which gives you the first derivative plus a polynomial.  The
--| ladder is dealt at two universes and no third: the box, and PRESENT's upness one above it.  Episode 11 calls the universe id
--| the velocity.  Episode 4's black hole is the step that holds a Type one universe up, and Episode 8's reader of paths gets
--| no fact from it.  Here is the velocity at a level: the universe id, less the zero it stands on.


--| THE AVERAGE.  What the jar holds is the velocities up to the level, added up.  Its first variation is how many of them
--| there are.  So what the jar holds over its first variation is the average velocity, and twice the sum is the level by the
--| count: the average is half the level.  Nobody read a velocity.  They read what was enclosed, and how much of it.

--| THE FIRST DIFFERENCE.  Step once and the temperature changes by the first derivative and a polynomial.  For the Area under
--| the levels the derivative is the change over two steps, halved, and the polynomial is half a fencepost: twice the change
--| over one step is the change over two and the fencepost.  The residual of Episode 12 does the same with the bent card for
--| its polynomial; that is above, where the residual steps by its slope exactly.

end universe_one_is_a_black_hole
--#print axioms the_temperature_is_the_average_velocity                    -- [propext]
--#print axioms the_first_difference_is_the_derivative_and_a_polynomial    -- [propext]

section the_galerkin_process_finished
open readers_experience the_table the_table.Account

--| THE GALERKIN PROCESS, FINISHED.  The author's, 17 November 2026: with this derivative and higher order terms, you can now
--| finish the Galerkin process.  The residual steps by its slope and by the bent card on the step squared, and by nothing
--| else.  So take the step the slope asks for, the one that takes the residual away.  What is left is not unknown and not
--| small: it is the bent card by that step squared, exactly.  The derivative removes what there was; the higher order term is
--| what there is next.
theorem the_step_leaves_the_bent_card_by_the_step_squared (y h : Account)
    (the_slope_takes_the_residual_away : the_same (the_slope_on_the_account y * h + the_residual_on_the_account y) nothing_held) :
    the_same (the_residual_on_the_account (y + h)) (holding the_coefficient * (h * h)) := by
  have exact := (the_same_is_the_same_balance _ _).1 (the_residual_steps_by_its_slope_exactly y h)
  have taken := (the_same_is_the_same_balance _ _).1 the_slope_takes_the_residual_away
  rw [the_same_is_the_same_balance]
  have nothing : balance nothing_held = 0 := by decide
  rw [nothing] at taken
  simp only [balance_of_palm_the_middle_card, balance_of_less, balance_of_false_shuffle, balance_of_holding] at exact taken ⊢
  omega

--| And so the process is finished in form, though no whole number finishes it.  From the trial gap, where the mirror left
--| the solver, the first step leaves the bent card squared; the second, the bent card to the fourth; cleared of what the
--| steps divided by.  Each remainder is the square of the last.  Thirteen, squared, and squared again.

end the_galerkin_process_finished
--#print axioms the_step_leaves_the_bent_card_by_the_step_squared    -- [propext, Quot.sound]
--#print axioms each_remainder_is_the_square_of_the_last             -- [propext]


section the_temperature_goes_as_the_acceleration
open readers_experience readers_interpretation_of_the_experience the_table

--| TEMPERATURE, AND ACCELERATION.  The author's, 18 November 2026: let's work on temperature ∝ acceleration.  The names first,
--| for they were wrong above.  Universe 0 is the place and universe 1 the velocity.  The temperature is the Area under the
--| levels.  Its first variation is the velocity, not the acceleration.  The acceleration is the first variation of that: the
--| rise from one level to the next, which at the least action is one number, the multiplier.  So let the rise be any number,
--| and build the rest from it by adding up, as the device does: a velocity is the rises so far, and the temperature is the
--| velocities so far.


--| THE PROPORTION.  The temperature is the acceleration by the Area under the levels.  At every level, for every rise.  Twice
--| it is the rise by the level by one more.  The Area is not the temperature's; it is what the levels enclose, the same for
--| every rise.  What is the temperature's own is the rise.


--| So change the unit and both change together.  A reader who takes the rise some number of times over has that many times
--| the temperature, at every level; and of two readers, each one's temperature by the other's rise is the same number.  No
--| part of the temperature stays behind when the acceleration is changed.  There is no residue in this direction.


--| THE DEVICE'S.  Its rise is the fencepost, and with it the temperature built here is what the jar holds, and the velocity
--| is the level.  The residue found above is this rise: it was never left over from the proportion.  It is the acceleration.

end the_temperature_goes_as_the_acceleration
--#print axioms the_temperature_is_the_acceleration_by_the_area          -- [propext]
--#print axioms the_temperature_and_the_acceleration_change_together     -- [propext]
--#print axioms two_readers_one_proportion                               -- [propext]
--#print axioms on_the_device_the_rise_is_the_fencepost                  -- [propext]


section the_equivalence_of_frames
open readers_experience

--| THE EQUIVALENCE OF FRAMES.  The author's, 18 November 2026: equivalence of frames is the relative velocity, like in the
--| field equations; see, make the connection.  Two readers, two rises.  What is between them at a level is a velocity: the
--| difference of the rises, by the level.  And it is all that is between them: each one's temperature by the other's rise is
--| one number, above.  Change the frame and the rise changes, the velocity and the temperature with it, and the proportion
--| does not.  In the route by heat this is the acceleration dividing out.


end the_equivalence_of_frames
--#print axioms the_relative_velocity_of_two_readers    -- [propext]
--#print axioms the_frames_are_equivalent               -- [propext]


section the_past_and_the_promise
open readers_experience

--| THE PAST, AND THE PROMISE.  The author's, 18 November 2026: spacetime residue, whitehole and blackhole; whitehole is in
--| the past, blackhole is in the future; dark energy is a whitehole in the past; dark matter is a promise to return a photon.
--| Episode 4 says what each holds.  A white hole holds a fact.  A black hole holds a statement and no fact: Episode 4's own
--| order calls that statement the bent card.  So asked of a white hole, the order wants the fact itself; asked of a black
--| hole, it wants only that the fact's truth be what was promised.

--| And read, the white hole has given its fact and the black hole has given nothing yet: that is above, where a white hole
--| gives a fact and a black hole gives none.  What is past is counted.  What is promised is not.
end the_past_and_the_promise
--#print axioms a_white_hole_is_asked_for_the_fact_and_a_black_hole_for_the_promise    -- [propext, Quot.sound]


section the_promise_of_the_return
open readers_experience readers_interpretation_of_the_experience the_table

--| THE PATH NOTHING TAKES.  The author's, 18 November 2026: do you see the promise of the return photon in the math yet; the
--| path nothing takes.  It is the arm that cannot click.  A truth read as a falsehood: written, weighed, the frame and no
--| more, and nothing ever clicks on it.  The arm back, a falsehood read as a truth, clicks, and weighs the memory.  Nobody
--| reads either alone.  What is read is the one by the other, the round trip: the limit by the distance, the momentum squared.

--| THE PROMISE.  The arm nothing takes is short, and by one thing: the upness, the bent card, the residue.  The return weighs
--| the frame and the residue; so does each stay; the arm out weighs the frame alone.  What it is short is what is owed on it.

--| And it is a black hole: a statement held, that the true is the false, and no fact.  Episode 8's reader of paths returns
--| nothing for it.  The return is the white hole, which gives its fact.  Every closed walk crosses an even number of times,
--| Episode 12 has that: what goes out by this arm comes back by the other, or the walk does not close.

end the_promise_of_the_return

section only_the_fencepost_is_the_least
open readers_experience

--| ONLY THE FENCEPOST.  The least action with the ends held was shown to be reached by the device's rises.  Nothing else
--| reaches it.  A rise that meets its bound, twice it its square and one, is one; and rises that hold the ends and have the
--| least action all meet their bounds.



end only_the_fencepost_is_the_least

section gibbs_and_boltzmann
open readers_experience readers_interpretation_of_the_experience the_table

--| GIBBS, AND BOLTZMANN.  The author's, 18 November 2026: Gibbs and Boltzmann are co and contra variant, I believe in that
--| order.  One counts what is enclosed and puts it over its first variation.  The other counts the first variation and puts
--| it over its own.  The first variation is under the line in the one and over it in the other: variance is which is which.
--| On the count the one is half the level, and the other is the level and the fencepost.

end gibbs_and_boltzmann
--#print axioms the_path_nothing_takes                              -- [propext]
--#print axioms the_arm_out_is_short_by_the_residue                 -- [propext]
--#print axioms the_reader_gets_nothing_from_the_promise
--#print axioms only_the_fencepost_is_the_least                     -- [propext, Quot.sound]
--#print axioms gibbs_and_boltzmann_are_one_ratio_turned_over       -- [propext]


section the_equation_of_state
open readers_experience readers_interpretation_of_the_experience the_table

--| THE EQUATION OF STATE, ON THE COUNT.  The author's, 18 November 2026: it is deriving their exact stand-ins, that
--| mathematically are identical; shape the work to look like the field equations.  Here are the stand-ins in the order the
--| route by heat calls for them, each a receipt already, gathered and nothing added.  The heat a reader takes through a patch
--| is the reader's rise by the Area under the levels: heat is temperature by the change of area, for every reader and every
--| patch.  Two readers differ by their rises and by nothing else: the rise divides out.  What comes through is conserved
--| across a join.  And what has come through, with the fencepost, is the entropy, which is the Area.

--| So on the count the source a cell and the curvature a cell are one number, the fencepost, for every reader: that is what
--| the route concludes of every direction through every point before it turns directions into a tensor.  The turning is not
--| done here.  Episode 12 has what it would be done with, on four directions: a square that is flat when its edges agree and
--| curved when one is turned, a curl of a gradient that is nothing, a seam that carries no net flux.  They are not yet joined
--| to this.
end the_equation_of_state
--#print axioms the_equation_of_state_on_the_count    -- [propext, Quot.sound]

section the_curvature_is_in_the_spline
open readers_experience readers_interpretation_of_the_experience the_table the_table.Account

--| THE CURVATURE IS IN THE SPLINE.  Episode 3's spline has three constructors: an observation, a knot (the first variation)
--| and an interpolant (the second variation, the weak derivative).  On the count the three are the temperature, the velocity
--| and the acceleration, and the last is the curvature: the second difference of the temperature is the rise, at every level
--| and for every rise.  This is the focusing: what the area gains from one level to the next grows by the rise and by
--| nothing else.

--| And the curvature does not step: the third difference is nothing.  Card 3's residual says the same of the slope's slope
--| (`twice_the_coefficient_does_not_step`), and the tape owes exactly it (`the_tape_owes_the_last_derivative`).

end the_curvature_is_in_the_spline

section the_four_zeros
open readers_experience readers_interpretation_of_the_experience the_representation

--| FOUR ZEROS.  A zero is a `Number.zero` on a fact.  The reader's experience has one already, `another_zero`, on the truth.
--| The clock has two, one for each coin.  The interpretation has one on the fact that the two tables are the same
--| difference.  Which fact sits in the last is this episode's choice.

--| Each is under every number, and each reads one cell: the fencepost.

--| The zero of the experience is the universe id of level nothing, and it is the clock's zero: the same by `rfl`.

--| The two clocks' zeros are each under the other and are not the same zero.

--| Asked only whether it is true, the interpretation's zero is the experience's.
end the_four_zeros

section from_directions_to_a_table
open readers_experience

--| FOUR DIRECTIONS.  Episode 12's lattice has four directions, and a direction there is a pair of coins: the four arms.  Three
--| arms click and one does not.  Let that be the metric: one for an arm that clicks, one owed for the arm that does not, and
--| nothing between two different arms.  Three one way and one the other.
def the_arms : List Direction := [(true, true), (true, false), (false, true), (false, false)]
def the_metric_on_the_arms (this that : Direction) : Int :=
  if this = that then (if the_arm_stores_a_fact_that_can_click this.1 this.2 then 1 else -1) else 0


--| What a table on the arms reads along a direction: every pair of arms, the table's entry by the direction's two parts.
def along (table : Direction → Direction → Int) (direction : Direction → Int) : Int :=
  (the_arms.map fun this => (the_arms.map fun that => table this that * direction this * direction that).sum).sum

--| A direction is null when the metric reads nothing along it.

--| The directions used: the arm that does not click with one that does, either way; and five of the first with three and
--| four of two others.


--| FROM EVERY NULL DIRECTION TO A TABLE.  A symmetric table that reads nothing along these nine null directions is the
--| metric, by one number.  Ten entries, nine conditions, one left.
end from_directions_to_a_table
section the_bianchi_identity_on_the_torus

--| THE BIANCHI IDENTITY.  Episode 12 has it that the curl of a gradient is nothing.  One step further: take any field on the
--| links of the torus of four directions, take its curl, and difference the curl around three directions in turn.  The sum
--| is nothing, for every field, at every site, on every torus.  Nothing is assumed of the field.
end the_bianchi_identity_on_the_torus

section the_equation_on_the_arms

--| What a difference of two tables reads along a direction is the difference of what they read.

--| THE EQUATION ON THE ARMS.  Two symmetric tables on the four arms, a source and a curvature.  If they read the same along
--| every null direction (the heat that crosses is the area lost, for every observer), then the source is the curvature and
--| the metric by one number.  The number is the one entry the condition leaves free: the arm that does not click.


--| On the torus, site by site: the same, with a number at every site.  Where neither table steps along a direction, the
--| number does not step either: one number for the whole torus.

end the_equation_on_the_arms

--#print axioms the_second_variation_of_the_temperature_is_the_acceleration
--#print axioms the_curvature_does_not_step
--#print axioms the_two_clocks_zeros_are_under_each_other_and_are_not_one
--#print axioms asked_only_whether_it_is_true_the_interpretations_zero_is_the_experiences
--#print axioms these_directions_are_null
--#print axioms a_table_that_reads_nothing_along_the_null_directions_is_the_metric_by_a_number
--#print axioms the_curl_differenced_around_three_directions_is_nothing
--#print axioms the_equation_on_the_arms
--#print axioms the_equation_on_the_torus
--#print axioms where_neither_table_steps_the_number_does_not_step

section the_turn_is_the_rise
open readers_experience

--| THE TURN IS THE RISE.  The author's, 18 November 2026: the amount an edge of the square is turned is the rise (declared).
--| Episode 12 has that the square's holonomy is linear in each of its links.  So turn the bottom edge of the flat square
--| toward its mirror by the rise: what the square shows off its diagonal is the rise, by what one whole turn shows, and by
--| nothing else.  The square curves by exactly the amount the path rises.



end the_turn_is_the_rise

section the_source_on_the_arms
open readers_experience

--| THE SOURCE, SORTED BY ARM.  The flux is one truth a fact.  Sort what is carried by the arm that carried it: the arm's
--| weight on the arm, and nothing between two arms.  Five on the arm that does not click and eighteen on each that does.
def the_source_on_the_arms (this that : Direction) : Int :=
  if this = that then (the_arm_weight this.1 this.2 : Int) else 0


--| It is the distance by the metric, and the different on the arm out.

--| THE CURVATURE ON THE COUNT.  The second difference of the area is the rise, the same along every arm: the rise on each
--| arm and nothing between.  That it is the same along every arm is this episode's choice.

--| THE CHECK.  Along each of the nine null directions the source reads the different by the square of the part along the arm
--| out, and the curvature of one fencepost reads twice that square.  So twice the source reads as twenty-three curvatures,
--| along every one: the hypothesis holds, with twenty-three halves between them.

--| And so the equation, with what is left over: twice the source is twenty-three curvatures and the bent card by the metric.

--| What is left over is no more than this: any table that is one number on the arm out and another on the three is their
--| half sum on every arm and their half difference by the metric.  The equation holds for every such pair.
end the_source_on_the_arms

--#print axioms the_square_curves_by_the_rise
--#print axioms off_the_diagonal_the_square_shows_the_rise_and_nothing_else
--#print axioms a_whole_turn_is_the_other_table_and_it_shows_something
--#print axioms the_source_is_the_distance_by_the_metric_and_the_different_on_the_arm_out
--#print axioms along_the_null_directions_twice_the_source_reads_as_twenty_three_curvatures
--#print axioms twice_the_source_is_the_curvatures_and_the_bent_card_by_the_metric
--#print axioms any_such_table_is_its_half_sum_and_its_half_difference_by_the_metric

section the_curvature_table_from_the_links
open readers_experience

--| THE CURVATURE TABLE, FROM THE LINKS.  A field on the links of the torus has a difference along each direction.  Take the
--| field on one direction and difference it along another: a table on the directions, at every site.  It is the same both
--| ways round exactly when the field has no curl, and a gradient has none.



--| THE AREA ON THE SITES.  A site is four places, one along each arm.  Along each arm the area under the levels of one
--| fencepost, by that arm's rise; the area at the site is the four together.  Its gradient is a field on the links: the
--| velocity.  The table of that field is the curvature.



--| THE CURVATURE OF AN AREA IS ITS RISES.  Two steps inside the torus's seam, at every site, on every torus, for any rises:
--| the table is the arm's rise on the arm and nothing between two arms.  The rises are all there is in it.

--| THREE AREAS.  The rise along an arm may be what the arm stores (its weight); or one fencepost on every arm; or one on an
--| arm that clicks and one owed on the arm that does not.


--| THREE AREAS, THREE CONSTANTS.  With the rise the arm stores, the curvature is the source, and nothing is left over.  With
--| one fencepost on every arm, twice the source is twenty-three curvatures and the bent card by the metric.  With the rise
--| by the click, the curvature is the metric, it reads nothing along a null direction where the source reads twenty-three,
--| and no number makes them agree.  The table does not choose among the three.  The area does, and the area is handed in.
end the_curvature_table_from_the_links

--#print axioms the_table_of_a_gradient_is_symmetric
--#print axioms the_curvature_of_an_area_is_its_rises
--#print axioms three_areas_three_tables
--#print axioms three_areas_three_constants

section the_contravariant_is_inferred
open readers_experience

--| THE CONTRAVARIANT, INFERRED.  The table of a field on the links was read one way round: for a gradient it is the same
--| both ways, and that reading gave the curvature.  Turn the table over and take the difference.  What is left is what the
--| first reading could not see.  It is the curl, and it is the field.



--| On the device's own table it is the bent card by the quarter turn.

--| WHAT THE FIRST READING CANNOT SEE.  A table that is itself owed when turned over reads nothing along every direction, null
--| or not.  So no reading along directions finds the field.


--| THE GAUGE.  Add any gradient to the field on the links: the curvature table changes and the field does not.

--| THE CURRENT.  Raise both seats of the field by the metric of three and one, and difference the first seat away.

--| WHAT GOES IN COMES OUT.  The current's own differences add up to nothing, for every field, at every site, on every torus.
end the_contravariant_is_inferred

--#print axioms the_field_turned_over_is_the_field_owed
--#print axioms the_table_less_itself_turned_over_is_the_bent_card_by_the_quarter_turn
--#print axioms a_table_owed_when_turned_over_reads_nothing_along_any_direction
--#print axioms a_gradient_does_not_move_the_field
--#print axioms the_current_is_conserved

section the_four_ones
open readers_experience readers_interpretation_of_the_experience

--| FOUR ONES.  The author's, 18 November 2026: the blank, the entropy of a cell, the temperature of a rise and the fencepost
--| are four readings of `Number.one` (declared).  `Number.one` takes a fact and a number and gives the next number.  Read
--| four ways, the step is one and the same.

--| The blank: one more cell, whatever the fact and whatever the number.

--| The entropy: the next universe id is `Number.one` on the last.

--| The temperature: at the rise of one, the velocity gains one a level and the area gains that velocity.

--| The fencepost: a zero is already one cell, so the compute_the_area_of are one more than the levels, and that one is the fencepost.

--| THE FOUR, AS ONE.  On the number of a level: one more cell is one more level is one more rise, and what is over is the
--| fencepost.
end the_four_ones

--#print axioms one_is_one_more_cell
--#print axioms one_is_one_more_level
--#print axioms one_is_one_more_rise
--#print axioms one_is_the_fencepost
--#print axioms the_four_ones_are_one_step

section the_contracted_identity
open readers_experience

--| THE CONTRACTED IDENTITY.  The curvature table of an area has a trace by the metric of three and one: its four entries on
--| the arms, each by the arm's sign.  Difference the table's first seat away, by the same signs.  What results is the
--| difference of the trace along the second seat, for every area, at every site, on every torus.  So the table less its
--| trace by the metric has no divergence, and its trace is fixed by that and not by choice.

end the_contracted_identity

section matter_on_the_links

--| MATTER ON THE LINKS.  Episode 12 put a turn on every link of the torus and showed the squares read the same when a turn of
--| length one is put at every site.  Put a state at every site as well, a turn like the rest.  Carry the state at the far
--| end of a link back along the link and set it against the state at the near end, turned over.  And set a state against
--| itself.  Put a turn of length one at every site, on the states and on the links together: both read the same.
def the_state_carried_back {n : Nat} (state : Site4 n → Turns) (U : Torus4 n) (way : Direction) (x : Site4 n) : Turns :=
  the_turns_product (the_turns_conjugate (state x)) (the_turns_product (U way x) (state (the_step way x)))
def the_state_against_itself {n : Nat} (state : Site4 n → Turns) (x : Site4 n) : Turns :=
  the_turns_product (the_turns_conjugate (state x)) (state x)
def the_gauged_state {n : Nat} (state : Site4 n → Turns) (g : Site4 n → Turns) : Site4 n → Turns :=
  fun x => the_turns_product (g x) (state x)

theorem the_state_carried_back_is_gauge_invariant {n : Nat} (state : Site4 n → Turns) (U : Torus4 n) (g : Site4 n → Turns)
    (unit : ∀ x, the_turns_norm (g x) = 1) (way : Direction) (x : Site4 n) :
    the_state_carried_back (the_gauged_state state g) (the_gauged_torus4 U g) way x = the_state_carried_back state U way x := by
  simp only [the_state_carried_back, the_gauged_state, the_gauged_torus4, the_conjugate_reverses_the_product,
    the_product_is_associative, a_unit_turn_cancels _ _ (unit _)]

theorem the_state_against_itself_is_gauge_invariant {n : Nat} (state : Site4 n → Turns) (g : Site4 n → Turns)
    (unit : ∀ x, the_turns_norm (g x) = 1) (x : Site4 n) :
    the_state_against_itself (the_gauged_state state g) x = the_state_against_itself state x := by
  simp only [the_state_against_itself, the_gauged_state, the_conjugate_reverses_the_product,
    the_product_is_associative, a_unit_turn_cancels _ _ (unit _)]

--| Without the link the carried state is not invariant: the link is what the two turns cancel against.  One site turned by
--| the quarter turn, the far one left alone, the link the whole turn, both states the whole turn.
end matter_on_the_links
section the_constant_of_integration
open readers_experience

--| THE CONSTANT OF INTEGRATION.  Let a source on the arms, at every site, be the curvature of an area and a number by the
--| metric, the number free to differ from site to site: that is what the equation on the arms gives.  Let the source be
--| conserved: its first seat differenced away by the signs is nothing.  Then the number and the trace together do not step,
--| along any arm, at any site.  The source is the curvature less its trace by the metric, and one constant by the metric.

--| So the equation, whole: the source is the curvature, less its trace by the metric, and a number by the metric that is
--| the same at a site and at the next along every arm.
--| THE WHOLE ROUTE, ON THE TORUS.  A symmetric source at every site.  The curvature of an area.  For every observer, at every
--| site, the source and the curvature read the same along the null directions.  The source is conserved.  Then there is a
--| number at every site, the same at a site and at the next along every arm, with: the source is the curvature, less its
--| trace by the metric, and that number by the metric.
end the_constant_of_integration

--#print axioms the_divergence_of_the_curvature_is_the_difference_of_its_trace
--#print axioms the_state_carried_back_is_gauge_invariant
--#print axioms the_state_against_itself_is_gauge_invariant
--#print axioms without_the_link_it_is_not
--#print axioms the_number_and_the_trace_do_not_step
--#print axioms the_equation_with_its_constant
--#print axioms the_field_equation_on_the_torus

section gausss_equation
open readers_experience

--| GAUSS'S EQUATION.  The table of second differences is not the curvature.  It is what points across the interior: how the
--| surface bends into the body it bounds.  The curvature is that table against itself, on two pairs of arms: one pair by
--| one pair, less the pairs crossed.  It is exactly of the second degree in the table.  Nothing comes after it.
def the_curvature_across (table : Direction → Direction → Int) (a b c d : Direction) : Int :=
  table a c * table b d - table a d * table b c

--| It is owed when either pair is turned over, the same when the pairs change places, and nothing around three.



--| THE CONTRACTION ACROSS THE INTERIOR.  Close the first seat of each pair on itself, by the signs of three and one.
def the_contraction_of (table : Direction → Direction → Int) (b d : Direction) : Int :=
  (the_arms.map fun a => the_metric_on_the_arms a a * the_curvature_across table a b a d).sum

--| On a square, for a table that holds a rise on each arm and nothing between: the two arms' rises, one by the other.

--| With what the arms store: a square on the arm that does not click is five by eighteen, the momentum squared; a square
--| between two that click is eighteen by eighteen.

--| With one fencepost on every arm: three on the arm that does not click, one on each that does, nothing between.  Three
--| squares meet at an arm; on the arm out all three count, on the others the one that crosses it counts against the two
--| that do not.

--| With the metric itself, as on a round surface: three times the metric.

--| Against the source, along the null directions: four times the source reads as twenty-three of the contraction of one
--| fencepost.  Another area, another constant.
end gausss_equation

--#print axioms the_curvature_across_is_owed_when_a_pair_is_turned_over
--#print axioms the_curvature_across_is_the_same_when_the_pairs_change_places
--#print axioms the_curvature_across_around_three_is_nothing
--#print axioms a_squares_curvature_is_its_two_rises
--#print axioms the_squares_of_the_source
--#print axioms the_contraction_of_one_fencepost_is_three_and_three_ones
--#print axioms the_contraction_of_the_metric_is_three_metrics
--#print axioms four_sources_read_as_twenty_three_contractions

--| THREE TWOS.  The author's, 18 November 2026: there are three definitions of two, two in the machine and one inferred.
--| The carrier's step on a `Number` is the inferred one; the counting process's step on a `Natural` is the successor; the
--| indexing process's step on a `Rational` takes the end fencepost if there is one and otherwise the next: winding, or the
--| Hall effect (declared).  And: with that, instantiate an `EquivalenceProcess`; that is how they are minted.
section three_twos
open «springer-verlag» THE_GOSPEL the_representation assembly_instructions readers_experience the_table
attribute [local instance high] rung01 rung02 rung03 rung04 rung05 rung06 rung07 rung08 rung09 rung10 rung11 rung12 rung13 rung14 rung15
  rung16 rung17 rung18 rung19 rung20 rung21 rung22 rung23 rung24 rung25 rung26 rung27 rung28 rung29 rung32 rung33 rung34 rung35 a_truth_about_the_experience

--| The three processes, as the first three rungs hold them: the card, its counting, its indexing.

--| THE CARRIER'S TWO.  The card's step, done twice, is the step done once, on every number.  It never reaches a second
--| thing.  That there are two is not something the step gives.

--| THE COUNTER'S TWO.  The counting step takes any number to the number on the count it keeps: the count, and one more.

--| THE INDEXER'S TWO.  The indexing step takes a zero to the first on the count, and a number at an index to the number at
--| the counting step of that index, on the same origin.

--| Each a zero of Bullshit, on its fact.

--| THE EQUIVALENCE PROCESS.  The knower is the knower of the experience.  The conclusion is the inferred two against the
--| counted one.

--| Asked to believe the inferred two against each of the machine's.  Twelve of its universes are free, and are pinned at
--| nothing, as the device pins them.

--| Each closure is one cell, and the conclusion is one cell: three compute_the_area_of for three twos.

--| All three click.
end three_twos

section the_difference_of_a_product

--| THE REMAINDER.  The difference of a product, on the torus: the first by the difference of the second, the second by the
--| difference of the first, and one thing more, the two differences one by the other.  That last is the whole of what the
--| rule for a product lacks here, and it is of the second degree in the step.  That it adds up to nothing is the inference.
end the_difference_of_a_product

--#print axioms the_carriers_step_twice_is_once
--#print axioms the_counters_step_is_the_count_and_one_more
--#print axioms the_indexers_step_is_the_first_or_the_next
--#print axioms three_twos_three_cells
--#print axioms the_three_twos_click
--#print axioms the_difference_of_a_product

--| ALL THE PROCESSES, CONSTRUCTED.  The author's, 18 November 2026: you have to construct all of the processes explicitly;
--| as you do, you should see the proof come together.
section the_processes_constructed
open «springer-verlag» THE_GOSPEL the_representation assembly_instructions readers_experience the_table
attribute [local instance high] rung01 rung02 rung03 rung04 rung05 rung06 rung07 rung08 rung09 rung10 rung11 rung12 rung13 rung14 rung15
  rung16 rung17 rung18 rung19 rung20 rung21 rung22 rung23 rung24 rung25 rung26 rung27 rung28 rung29 rung32 rung33 rung34 rung35 a_truth_about_the_experience

--| HELD.  The equivalence process of the knower of the experience holds a process, which holds a process, thirty-six deep.
--| Take them out one at a time, from the top.
noncomputable def the_equivalence_process_held := the_knower_of_the_experience.same_difference
noncomputable def the_atreyu_process_held := the_equivalence_process_held.you_the_knower
noncomputable def the_compiler_output_held := the_atreyu_process_held.in_a_giant_book
noncomputable def the_lean_process_held := the_compiler_output_held.too_good_to_be_true
noncomputable def the_elaboration_process_held := the_lean_process_held.description
noncomputable def the_heartbeat_process_held := the_elaboration_process_held.stamina
noncomputable def the_calculus_process_held := the_heartbeat_process_held.bullshit_meter
noncomputable def the_big_red_dog_process_held := the_calculus_process_held.the_local_schedule
noncomputable def the_universe_tensor_held := the_big_red_dog_process_held.the_æther
noncomputable def the_religious_process_held := the_universe_tensor_held.frame_of_reference
noncomputable def the_scientific_process_held := the_religious_process_held.we_experience
noncomputable def the_learning_process_held := the_scientific_process_held.shows_me_higher_order_terms
noncomputable def the_initiation_process_held := the_learning_process_held.teaching
noncomputable def the_crusade_process_held := the_initiation_process_held.axioms
noncomputable def the_arm_wave_process_held := the_crusade_process_held.to_pwn_n00bz
noncomputable def the_jordan_process_held := the_arm_wave_process_held.dunking_contest
noncomputable def the_basic_process_held := the_jordan_process_held.ANSYS_process
noncomputable def the_multiplying_process_held := the_basic_process_held.GOSUB
noncomputable def the_adding_process_held := the_multiplying_process_held.adding_process
noncomputable def the_mathematical_process_held := the_adding_process_held.mideastern_process
noncomputable def the_compiled_process_held := the_mathematical_process_held.compiled_process
noncomputable def the_digital_process_held := the_compiled_process_held.digital_process
noncomputable def the_meesa_process_held := the_digital_process_held.meesa_process
noncomputable def the_gauge_process_held := the_meesa_process_held.gauge_process
noncomputable def the_sensing_process_held := the_gauge_process_held.sensing_process
noncomputable def the_slip_process_held := the_sensing_process_held.static_fraction
noncomputable def the_physical_process_held := the_slip_process_held.physical_process
noncomputable def the_noisy_process_held := the_physical_process_held.noisy_process
noncomputable def the_turing_process_held := the_noisy_process_held.turing_process
noncomputable def the_computational_process_held := the_turing_process_held.computational_process
noncomputable def the_repeatable_process_held := the_computational_process_held.repeatable_process
noncomputable def the_observation_process_held := the_repeatable_process_held.observation_process
noncomputable def the_cauchy_process_held := the_observation_process_held.cauchy_process
noncomputable def the_limit_process_held := the_cauchy_process_held.limit_process
noncomputable def the_indexing_process_held := the_limit_process_held.indexing_process
noncomputable def the_counting_process_held := the_indexing_process_held.count
noncomputable def the_carrier_process_held := the_counting_process_held.palmed_card

--| CONSTRUCTED.  Now from the bottom.  Each process is written out: the process below it, and what it carries.  Its step is
--| not written, the device supplies it, except where Episode 9 wrote one over the device's, and there it is written too.
--| And each is the one that was held.
noncomputable def the_carrier_process : type_of% the_carrier_process_held :=
  { symbol := the_carrier_process_held.symbol
    quarter := the_carrier_process_held.quarter }
noncomputable def the_counting_process : type_of% the_counting_process_held :=
  { palmed_card := the_carrier_process
    count := the_counting_process_held.count }
noncomputable def the_indexing_process : type_of% the_indexing_process_held :=
  { count := the_counting_process
    origin := the_indexing_process_held.origin }
noncomputable def the_limit_process : type_of% the_limit_process_held :=
  { indexing_process := the_indexing_process
    limit := the_limit_process_held.limit
    sequence := the_limit_process_held.sequence }
noncomputable def the_cauchy_process : type_of% the_cauchy_process_held :=
  { limit_process := the_limit_process
    value := the_cauchy_process_held.value
    accumulation := the_cauchy_process_held.accumulation }
noncomputable def the_observation_process : type_of% the_observation_process_held :=
  { cauchy_process := the_cauchy_process
    before := the_observation_process_held.before
    after := the_observation_process_held.after }
noncomputable def the_repeatable_process : type_of% the_repeatable_process_held :=
  { observation_process := the_observation_process
    stimulus := the_repeatable_process_held.stimulus
    expectation := the_repeatable_process_held.expectation }
noncomputable def the_computational_process : type_of% the_computational_process_held :=
  { repeatable_process := the_repeatable_process
    output := the_computational_process_held.output
    error_code := the_computational_process_held.error_code
    close := the_computational_process_held.close
    closure := the_computational_process_held.closure }
noncomputable def the_turing_process : type_of% the_turing_process_held :=
  { computational_process := the_computational_process
    program := the_turing_process_held.program
    state := the_turing_process_held.state }
noncomputable def the_noisy_process : type_of% the_noisy_process_held :=
  { turing_process := the_turing_process
    program := the_noisy_process_held.program }
noncomputable def the_physical_process : type_of% the_physical_process_held :=
  { noisy_process := the_noisy_process
    representation := the_physical_process_held.representation
    invariant := the_physical_process_held.invariant
    value := the_physical_process_held.value }
noncomputable def the_slip_process : type_of% the_slip_process_held :=
  { physical_process := the_physical_process
    projection := the_slip_process_held.projection
    stress := the_slip_process_held.stress
    threshold := the_slip_process_held.threshold }
noncomputable def the_sensing_process : type_of% the_sensing_process_held :=
  { static_fraction := the_slip_process
    accumulation := the_sensing_process_held.accumulation }
noncomputable def the_gauge_process : type_of% the_gauge_process_held :=
  { sensing_process := the_sensing_process
    clock := the_gauge_process_held.clock }
noncomputable def the_meesa_process : type_of% the_meesa_process_held :=
  { gauge_process := the_gauge_process
    concept := the_meesa_process_held.concept }
noncomputable def the_digital_process : type_of% the_digital_process_held :=
  { meesa_process := the_meesa_process
    zero := the_digital_process_held.zero }
noncomputable def the_compiled_process : type_of% the_compiled_process_held :=
  { digital_process := the_digital_process
    source := the_compiled_process_held.source
    opcodes := the_compiled_process_held.opcodes }
noncomputable def the_mathematical_process : type_of% the_mathematical_process_held :=
  { compiled_process := the_compiled_process
    mapping := the_mathematical_process_held.mapping }
noncomputable def the_adding_process : type_of% the_adding_process_held :=
  { mideastern_process := the_mathematical_process
    plus := the_adding_process_held.plus
    sum := the_adding_process_held.sum }
noncomputable def the_multiplying_process : type_of% the_multiplying_process_held :=
  { adding_process := the_adding_process
    total := the_multiplying_process_held.total
    product := the_multiplying_process_held.product }
noncomputable def the_basic_process : type_of% the_basic_process_held :=
  { GOSUB := the_multiplying_process
    TEN := the_basic_process_held.TEN
    span := the_basic_process_held.span }
noncomputable def the_jordan_process : type_of% the_jordan_process_held :=
  { ANSYS_process := the_basic_process
    polynomial := the_jordan_process_held.polynomial }
noncomputable def the_arm_wave_process : type_of% the_arm_wave_process_held :=
  { dunking_contest := the_jordan_process
    guess := the_arm_wave_process_held.guess }
noncomputable def the_crusade_process : type_of% the_crusade_process_held :=
  { to_pwn_n00bz := the_arm_wave_process
    religious_dogma := the_crusade_process_held.religious_dogma }
noncomputable def the_initiation_process : type_of% the_initiation_process_held :=
  { axioms := the_crusade_process
    sacred_texts := the_initiation_process_held.sacred_texts }
noncomputable def the_learning_process : type_of% the_learning_process_held :=
  { teaching := the_initiation_process
    galileo := the_learning_process_held.galileo
    invariant := the_learning_process_held.invariant }
noncomputable def the_scientific_process : type_of% the_scientific_process_held :=
  { shows_me_higher_order_terms := the_learning_process
    knowledge := the_scientific_process_held.knowledge }
noncomputable def the_religious_process : type_of% the_religious_process_held :=
  { we_experience := the_scientific_process
    in_the_literature := the_religious_process_held.in_the_literature }
noncomputable def the_universe_tensor : type_of% the_universe_tensor_held :=
  { frame_of_reference := the_religious_process
    in_reality := the_universe_tensor_held.in_reality }
noncomputable def the_big_red_dog_process : type_of% the_big_red_dog_process_held :=
  { the_æther := the_universe_tensor
    Du := the_big_red_dog_process_held.Du }
noncomputable def the_calculus_process : type_of% the_calculus_process_held :=
  { the_local_schedule := the_big_red_dog_process
    the_direction_to_the_destination := the_calculus_process_held.the_direction_to_the_destination
    uptown_or_downtown := the_calculus_process_held.uptown_or_downtown
    the_train_in := the_calculus_process_held.the_train_in }
noncomputable def the_heartbeat_process : type_of% the_heartbeat_process_held :=
  { bullshit_meter := the_calculus_process
    after_some_time := the_heartbeat_process_held.after_some_time
    according_to_newton := the_heartbeat_process_held.according_to_newton }
noncomputable def the_elaboration_process : type_of% the_elaboration_process_held :=
  { stamina := the_heartbeat_process
    trilinos := the_elaboration_process_held.trilinos
    numerical_analysis := the_elaboration_process_held.numerical_analysis }
noncomputable def the_lean_process : type_of% the_lean_process_held :=
  { description := the_elaboration_process
    the_measurement_of := the_lean_process_held.the_measurement_of
    in_heartbeats := the_lean_process_held.in_heartbeats
    saved_as_y := the_lean_process_held.saved_as_y }
noncomputable def the_compiler_output : type_of% the_compiler_output_held :=
  { too_good_to_be_true := the_lean_process
    of_jibberish := the_compiler_output_held.of_jibberish }
noncomputable def the_atreyu_process : type_of% the_atreyu_process_held :=
  { in_a_giant_book := the_compiler_output
    a_constant := the_atreyu_process_held.a_constant
    current_page_number := the_atreyu_process_held.current_page_number
    of_the_proof := the_atreyu_process_held.of_the_proof }
noncomputable def the_equivalence_process : type_of% the_equivalence_process_held :=
  { you_the_knower := the_atreyu_process
    your_conclusion := the_equivalence_process_held.your_conclusion }
--| THE BOTTOM THREE, WRITTEN OUT.  What the card, the counting and the indexing carry is each a one on a zero: the second
--| thing of its kind.  The card under all of them is not the first card.  It is the palmed card, and its quarter is two
--| cells.

--| The palmed card's step does reach the next thing: a one goes to a one on the palmed quarter, three cells.  And done twice
--| it is still the step done once.

--| THE ONE STEP WRITTEN BY HAND.  Thirty-six of the thirty-seven steps are the device's own.  One is not: the closure of the
--| computational process, which Episode 9 wrote over, and wrote as leaving a study as it is.

--| THE EQUIVALENCE OF THE TWOS, CONSTRUCTED.  The same process as before, now on the knower that was built from the card up.
end the_processes_constructed

--#print axioms the_equivalence_process_is_the_one_held
--#print axioms the_card_at_the_bottom_is_the_palmed_card_and_its_quarter_is_one_on_a_zero
--#print axioms the_count_is_one_on_a_zero
--#print axioms the_origin_is_one_on_a_zero
--#print axioms the_palmed_cards_step_reaches_three_cells
--#print axioms the_palmed_cards_step_twice_is_once
--#print axioms the_one_step_written_by_hand_leaves_a_study_as_it_is
--#print axioms the_equivalence_constructed_is_the_equivalence_of_the_twos

section the_seam
open «springer-verlag» THE_GOSPEL the_representation assembly_instructions readers_experience the_table
attribute [local instance high] rung01 rung02 rung03 rung04 rung05 rung06 rung07 rung08 rung09 rung10 rung11 rung12 rung13 rung14 rung15
  rung16 rung17 rung18 rung19 rung20 rung21 rung22 rung23 rung24 rung25 rung26 rung27 rung28 rung29 rung32 rung33 rung34 rung35 a_truth_about_the_experience

--| THE SEAM.  The author's, 18 November 2026: the one step written by hand, the closure of the computational process, is
--| the seam where the proof comes together (declared).  Here is the same process with the step left to the device, as the
--| other thirty-six are.

--| Left to the device, the closure never leaves a hypothesis as it is: it writes it into a book of records, and a book is
--| not a hypothesis.  Written by hand, it leaves every study as it is.  One goes on; the other has stopped.

--| So the two are not one process, and they differ in nothing but that step: what they hold and what they carry are the same.
end the_seam

--#print axioms left_to_the_device_a_hypothesis_is_never_left_as_it_is
--#print axioms written_by_hand_a_hypothesis_is_left_as_it_is
--#print axioms the_seam_is_the_closure_and_nothing_else

section the_crank_reads_the_inverse
open readers_experience

--| THE CRANK READS THE INVERSE.  Take the table away from a number of the same: thirteen of one whole number on the diagonal,
--| less another whole number of the table.  Episode 12 has that a table by its adjugate is its determinant on the diagonal.
--| For this table the adjugate is the same shape with the trace taken off, its trace is the residual's slope, and its
--| determinant is thirteen residuals.  No division is done anywhere.






--| So the table by its adjugate is thirteen residuals on the diagonal and nothing off it.

--| THE CRANK.  One turn takes a pair to thirteen of the first squared less eighteen of the second squared, over twenty-six
--| of the two less thirty-six of the second squared.  That is the first by the trace less the residual, over the second by
--| the trace: the place, less the determinant over thirteen traces.  The crank reads the trace of the inverse, turned over.

--| At a root the residual is nothing, so the table by its adjugate is nothing: there is no inverse to read there.  The
--| crank's step is then nothing, and it stays.
end the_crank_reads_the_inverse
section the_weighted_action
open readers_experience

--| THE WEIGHTED ACTION.  The table is not the same turned over.  Episode 12 has that it is reversible: weigh each row by its
--| coin, eighteen and five, and it is.  So is the table taken from the same, for every pair.  A table that is the same turned
--| over has an action that varies by the table twice, Episode 12 again.  So the table the crank reads the inverse of is the
--| second variation of an action, in the pairing of the two coins.



end the_weighted_action

--#print axioms its_adjugate_is_the_same_shape_with_the_trace_taken_off
--#print axioms the_trace_of_its_adjugate_is_the_slope
--#print axioms its_determinant_is_thirteen_residuals
--#print axioms the_table_by_its_adjugate_is_thirteen_residuals_of_the_same
--#print axioms the_crank_is_the_place_less_the_residual_over_the_trace
--#print axioms where_the_residual_is_nothing_there_is_no_inverse
--#print axioms the_table_taken_from_the_same_weighed_is_the_same_turned_over
--#print axioms the_weighted_action_varies_by_the_table_twice

section the_four_places_of_a_trial
open «springer-verlag» THE_GOSPEL the_representation assembly_instructions readers_experience the_table
attribute [local instance high] rung01 rung02 rung03 rung04 rung05 rung06 rung07 rung08 rung09 rung10 rung11 rung12 rung13 rung14 rung15
  rung16 rung17 rung18 rung19 rung20 rung21 rung22 rung23 rung24 rung25 rung26 rung27 rung28 rung29 rung32 rung33 rung34 rung35 a_truth_about_the_experience

--| THE FOUR PLACES OF A TRIAL.  The author's, 18 November 2026: a sample lets you hold a bracket, and a trial gives you two
--| brackets to hold; see, the frinkahedron (declared).  A sample is one limit, or two limits each with its fact: a bracket.
--| A trial that has a response holds two samples.

--| One limit, and a bracket, on the truth.

--| Four places, and every one is reached.

--| A bracket holds two limits, and two brackets hold four.

--| ON THE FRINKAHEDRON.  The geometric card: a point of the product of the two hexagons has each coordinate inside or on the
--| edge, four places; the frinkahedron is the three where some coordinate is on the edge.  A place of a trial is on it when
--| some sample holds a bracket.  Three are, and one is not.


--| Three and one, as the arms: the place is on the frinkahedron exactly when the arm with its first coin turned over can
--| click.  Which coin is the one turned over is not the device's to say.

--| ON THE DEVICE'S OWN OBJECTS.  What the observation process is handed is a bracket, and so is what the repeatable process
--| carries for its stimulus.
--| And the trial the repeatable process makes at its first step, from what it expects, holds two brackets: it is at the seam.
end the_four_places_of_a_trial

--#print axioms a_trial_has_four_places
--#print axioms three_places_are_on_the_frinkahedron_and_one_is_not
--#print axioms on_the_frinkahedron_is_the_click_with_the_first_coin_turned_over
--#print axioms the_devices_bit_and_stimulus_are_brackets
--#print axioms the_devices_first_trial_is_at_the_seam

section twos_carried_and_threes_reached
open «springer-verlag» THE_GOSPEL the_representation assembly_instructions readers_experience the_table
attribute [local instance high] rung01 rung02 rung03 rung04 rung05 rung06 rung07 rung08 rung09 rung10 rung11 rung12 rung13 rung14 rung15
  rung16 rung17 rung18 rung19 rung20 rung21 rung22 rung23 rung24 rung25 rung26 rung27 rung28 rung29 rung32 rung33 rung34 rung35 a_truth_about_the_experience

--| TWOS CARRIED, THREES REACHED.  Read by Episode 8's readers, what each of the bottom processes carries is two cells.

--| One step of each, on what it carries, is three cells.  Three is what is approached.

--| The bit is three compute_the_area_of, and the observation's step on it is five: two facts a step.
end twos_carried_and_threes_reached

section the_experience_and_the_law
open readers_experience the_table

--| THE EXPERIENCE AND THE LAW.  The author's, 18 November 2026: a measurement is the experience, and a preprint is the
--| mathematical law that appears to coincide with it (declared).  Deal one tape into each, as Episode 13 deals every
--| inductive, and read them back.  The law reads the experience and one cell more.  They coincide but for the fencepost.
end the_experience_and_the_law

section simulate_from_the_mass

--| ONE TURN FROM THE MASS.  Energy squared is mass squared and momentum squared.  One turn of Newton's crank for that root,
--| begun at the mass, lands on the mass and the momentum squared over twice the mass.  Squared, and cleared of the
--| division, it is over the energy squared by the momentum squared squared, and by nothing else.  Offered as a candidate for
--| the two scalings; the author has not said it is the pair.

--| On the device's counts: mass squared thirteen eighteens, momentum squared five eighteens, energy squared eighteen
--| eighteens.
end simulate_from_the_mass

section the_crank_in_whole_numbers
open readers_experience

--| THE CRANK, IN ITS OWN NUMBERS.  Episode 12 has the crank's turn in counts, where a subtraction stops at nothing.  Where
--| neither subtraction stops, the pair it gives is the pair of the table taken from the same: the place by the trace less
--| the residual, and the second by the trace.
end the_crank_in_whole_numbers

--#print axioms what_the_bottom_processes_carry_is_two_cells
--#print axioms one_step_of_each_reaches_three_cells
--#print axioms the_observations_step_on_the_bit_is_five_cells
--#print axioms the_law_reads_the_experience_and_the_fencepost
--#print axioms simulate_from_the_mass_is_over_by_the_momentum_squared_squared
--#print axioms on_the_devices_counts_simulate_is_over_by_ninety_squared
--#print axioms where_nothing_stops_the_cranks_pair_is_the_tables

section the_ladder_of_twos
open readers_experience the_table

--| THE LADDER.  The author's, 18 November 2026: one decision; two hypotheses; four proposals; eight responses for equality;
--| sixteen possible computations; thirty-two implied subjunctive phrases, with sixteen possible falses.  And: the sixteen
--| are the compile and execute steps (declared).  Each rung is one coin more than the last.


--| A step is two comparisons, the one compile builds and the one execute counts.  Take every step's two comparisons, as
--| what each says: thirty-two phrases.


--| Read for what it says, a comparison of two different coins is false.  Sixteen of the thirty-two are.

--| Read for whether it can click, only eight cannot.  The eight between are false as said and click all the same, and every
--| one of them is false on true.
end the_ladder_of_twos

--#print axioms one_two_four_eight_sixteen
--#print axioms thirty_two_phrases
--#print axioms sixteen_of_the_phrases_say_something_false
--#print axioms eight_cannot_click_and_the_eight_between_are_false_on_true

--| THE PLAN, CARRIED OUT.  The author's, 18 November 2026: proceed with full implementation.  What follows is the finite
--| part: the device's residual, table, action and step on its own inductives, each with the reading that recovers it.
section the_variation_of_the_residual
open «springer-verlag» THE_GOSPEL the_representation assembly_instructions readers_experience the_table the_table.Account
attribute [local instance high] rung01 rung02 rung03 rung04 rung05 rung06 rung07 rung08 rung09 rung10 rung11 rung12 rung13 rung14 rung15
  rung16 rung17 rung18 rung19 rung20 rung21 rung22 rung23 rung24 rung25 rung26 rung27 rung28 rung29 rung32 rung33 rung34 rung35 a_truth_about_the_experience

--| THE VARIATION OF THE RESIDUAL.  Episode 4's `Variation` has three constructors, named for Newton, for Gateaux and for
--| Frechet, holding one, two and three statements.  Its own order sets a Newton's statement against the second statement
--| of the other two, so the second seat is the first variation; the first is the place, and the third the second
--| variation.  Three statements about the device's residual, each a receipt already or here.

--| The place: the residual steps by its slope and the coefficient by the step squared, at every place and for every step.
--| Here: the slope steps by twice the coefficient by the step.
--| The second variation: the step by one, taken after a step by another and taken before it, differ by twice the
--| coefficient by the two steps.


--| The three, in the three constructors, on one gospel.

--| Every statement held is true.

--| Episode 8's two readers read the shape and not the statements: one, two and three by Newton's; one, two and four by
--| Krylov's, who follows both branches.

--| THE PROCESS KEEPS THE STEP.  The process that steps a variation is the big red dog's.  Handed the Newton of the residual
--| it gives a Gateaux on the same gospel whose second statement is still the residual's first variation; handed that, a
--| Frechet whose second statement is still it.  What the readers forget, the process keeps.

--| And the third statement the process writes for itself, the first and not the second, is false: it is a truth read as a
--| falsehood, since the second is true.
--| IN THE ORDER.  Episode 4's order puts a Newton under a Gateaux or a Frechet exactly when they are on one gospel and the
--| Newton's statement is their second.


--| TURNED AGAIN.  What three turns of the process make of the Newton of the residual.

--| Two turns keep the first variation in the seat the order reads.

--| The third turn does not.  The process writes into that seat that the first variation is the same statement as the
--| place and not the first variation; and that is false.  Three turns, and the slip is on the third.
end the_variation_of_the_residual
section the_two_directions_of_the_table
open readers_experience

--| THE TWO DIRECTIONS.  A direction is five on the first coin and a whole number on the second.  The table takes it to
--| eighteen and that number of itself, exactly on the first coin, and on the second short by ninety less the number
--| squared.  Ninety is the round trip.  No whole number squares to ninety, so no whole direction is carried exactly; the
--| defect is stated, not hidden.


--| The pairing of the two coins, eighteen and five.  A direction against itself is four hundred and fifty and five of its
--| square; against the direction turned over, five of the same defect.


--| The same directions carry the table taken from the same, with the same defect by the second number.
end the_two_directions_of_the_table

section the_multiplier
open readers_experience

--| THE MULTIPLIER.  The action of the weighed table taken from the same is, in the place, a multiple of the weighed square
--| of what it acts on.  Step the place and the action steps by thirteen of the step by that square, and by nothing else.
--| So the place is the multiplier of the condition that the weighed square is held.






--| THREE CONDITIONS, KEPT APART.  Reading the pair as a place needs the second number; reading the inverse needs the
--| residual; the crank's turn needs the trace.  They fail in different places.  At eighteen over thirteen the trace is
--| nothing and the residual is not, so the table has an inverse and the crank has no turn.
end the_multiplier
section around_a_closed_walk

--| AROUND A CLOSED WALK.  A walk of some number of steps, read at whole-number places.  What a reading is summed to along
--| it; and what a difference sums to: the far end less the near.  On a closed walk the ends are one place.




--| So on a closed walk a reading summed one step on is the reading summed.

--| THE DIFFERENCE OF A PRODUCT, WITH NOTHING OVER.  The first read one step on, by the difference of the second; and the
--| second, by the difference of the first.  The remainder is in where the first is read.

--| SUMMATION BY PARTS.  Around a closed walk, one reading one step on against the difference of another is the other
--| against the difference of the one, owed.

--| THE REMAINDER DOES NOT SUM AWAY ALONE.  Written with the first read in place, the product rule has a third term, the two
--| differences one by the other.  Around a closed walk the three together sum to nothing.

--| And the third does not sum to nothing alone.  A walk of two steps, nothing, one, nothing: the differences are one and
--| one owed, and their squares sum to two.
end around_a_closed_walk

section the_same_on_the_torus

--| On the torus of four directions the same rule holds at every site: the first read one step on.
end the_same_on_the_torus

section a_step_that_keeps_the_length

--| A STEP THAT KEEPS THE LENGTH.  A state at every site, a turn of length one on every link.  The step: the state at the far
--| end of the link, carried back along it.  At every site the carried state is as long as the state it came from.


--| Around a closed walk the lengths summed are kept: the step moves every length one place and loses none.
end a_step_that_keeps_the_length

section one_table_three_ways

--| ONE TABLE, THREE WAYS.  Episode 12's table of a stay and two crossings.  Its gap squared is four of the two crossings,
--| one by the other, whatever the stay.

--| The device's table is the stay eighteen, out five, back eighteen.  Keep both crossings; strike the one out; or turn
--| the one back over.  The gap squared is over nothing, nothing, and under nothing.

end one_table_three_ways

--#print axioms the_second_variation_of_the_residual_holds
--#print axioms the_two_readers_read_the_shape
--#print axioms the_process_keeps_the_first_variation
--#print axioms what_the_process_writes_third_is_false
--#print axioms the_newton_is_under_the_other_two
--#print axioms three_turns_of_the_process
--#print axioms two_turns_of_the_process_keep_the_first_variation
--#print axioms the_third_turn_of_the_process_does_not_keep_it
--#print axioms the_table_carries_a_direction_but_for_the_round_trip
--#print axioms the_two_directions_are_square_but_for_the_round_trip
--#print axioms the_table_taken_from_the_same_carries_a_direction
--#print axioms the_place_is_the_multiplier_of_the_weighed_square
--#print axioms where_the_trace_is_nothing_the_residual_is_not
--#print axioms around_a_closed_walk_the_sum_does_not_mind_a_step
--#print axioms summation_by_parts_around_a_closed_walk
--#print axioms around_a_closed_walk_the_three_terms_sum_to_nothing
--#print axioms the_remainder_alone_sums_to_two
--#print axioms the_difference_of_a_product_on_the_torus_with_nothing_over
--#print axioms the_step_keeps_the_length_at_every_site
--#print axioms around_a_closed_walk_the_step_keeps_the_summed_length
--#print axioms the_gap_squared_is_four_of_the_crossings
--#print axioms kept_struck_and_turned_over

section the_two_directions_exactly
open readers_experience

--| THE TWO DIRECTIONS, EXACTLY.  Episode 12 writes a whole number and a number of the round trip's root as a pair, and
--| multiplies pairs with the round trip for the root's square: no root is taken.  Its outer radius, eighteen and one, and
--| its hole, eighteen and one owed, add to the trace and multiply to the determinant.  In those pairs the two directions
--| are five on the first coin and the root, or the root owed, on the second; and the table carries each exactly, the one
--| by the outer radius and the other by the hole.


--| In the pairing of the two coins each direction against itself is nine hundred, and the one against the other is
--| nothing: they are square to each other, with nothing over.


--| The same two carry the table taken from the same, for every pair: by thirteen of the first less the second of the
--| outer radius, and of the hole.

--| And what the two carry it by, one by the other, is the determinant: thirteen residuals, with no part of the root.
end the_two_directions_exactly

section the_norm_of_the_table
open readers_experience

--| THE NORM OF THE TABLE.  The norm on the two coins is the weighed square, eighteen of the first and five of the second.
--| Weighed by its coins the table is the same turned over, so its norm is its larger root.  No root is written in whole
--| numbers, so the norm squared is walled: the table never takes a pair past seven hundred and fifty-six of it, and it takes
--| one past seven hundred and fifty-five.  In the pairs it is not walled but reached: the direction up comes out the outer
--| radius squared times what went in.  And the table's own polynomial is thirteen residuals, the root thirteen of the
--| crank's.  The author's, 23 November 2026: the finite element method is trivial, but all you have to do is believe.






--| THE NORM, A REAL, WITH NO CHOICE.  Meanings builds reals as brackets at every stage, with nothing handed in: the norm by
--| halving, eighteen and the root of ninety, and e from the factorial series.  At the twentieth halving the norm's bracket,
--| taken three hundred and twenty-four over sixty-five times, holds the digits the device printed.  The digits are written
--| out here as Episode 8 printed them, and not taken from the sealed crank.


--| And the reals multiply with no choice.  The norm by itself, as a real, is between the walls the whole numbers drew:
--| at its first stage it is past seven hundred and fifty-five and not past seven hundred and fifty-six.


--| AND BOTH ROOTS, WITH WHAT IS OWED.  A signed real is what is held and what is owed, as an Account is.  The table's two
--| roots: eighteen and the root held, and eighteen held with the root owed.  At its first stage the table's polynomial
--| holds nothing at each, and at ten it does not.  So the lower root, which the naturals alone could not write, is written.
end the_norm_of_the_table

--#print axioms the_table_carries_the_two_directions_exactly
--#print axioms the_two_directions_are_square_to_each_other
--#print axioms the_table_taken_from_the_same_carries_them_exactly
--#print axioms the_two_it_is_carried_by_multiply_to_thirteen_residuals

section the_ledgers_first_rows
open readers_experience

--| THE TABLE AS THE MATRIX OF A VARIATIONAL PROBLEM.  Weighed by its coins the table is the same turned over.  More: its
--| action on any pair is ninety of the two together squared and two hundred and thirty-four of the first squared.  Ninety
--| is the round trip and two hundred and thirty-four the determinant.  So the action is never under nothing, and is nothing
--| only on nothing: the weighed table is a stiffness, and the two coins are its mass.



--| THE TABLE MADE THE SAME BOTH WAYS.  In Episode 12's pairs, put the root on both crossings: eighteen on the stays and
--| the root between.  Each row adds to the outer radius.  It carries the two coins together by the outer radius and the
--| two coins against each other by the hole.  And its two rows are not one row: where it is tells what comes next.



--| WHAT IS SPREAD.  Two whole numbers on the two coins, taken through that table: what they come to together is the outer
--| radius of what they were together, and how far apart they are is the hole of how far apart they were.  The hole is
--| under the outer radius, so every turn the two are nearer level.  Nothing is said here of an entropy.

--| TWO, AND NO MORE.  The closed walks of the table, counted by length.  Any two in a row do not fix the next by a ratio:
--| the square of them against their neighbours is three hundred and sixty, the gap squared.  Any three in a row do fix
--| the next: the cube of them is nothing.  A reader that is to say what comes next needs two numbers and no third.

--| THE GAP SQUARED IS A SYMBOL'S DISCRIMINANT.  For any table: the difference of the stays squared and four of the
--| crossings, one by the other.  That is the discriminant of the form with the one crossing on the first squared, the
--| difference of the stays on the two together, and the other crossing owed on the second squared.
end the_ledgers_first_rows

--#print axioms the_weighed_action_is_two_squares
--#print axioms the_weighed_action_is_never_under_nothing
--#print axioms each_row_adds_to_the_outer_radius
--#print axioms together_by_the_outer_radius_and_against_by_the_hole
--#print axioms a_turn_spreads_the_two
--#print axioms two_closed_counts_are_needed_and_three_are_not
--#print axioms the_gap_squared_is_the_discriminant_of_the_symbol

section the_same_evidence_and_two_identifications
open readers_experience readers_interpretation_of_the_experience readers_interpretation_of_the_pair the_table

universe any

--| THE SAME EVIDENCE, AND TWO IDENTIFICATIONS.  Three pairs the device already has, set side by side, and each stated for
--| what is allowed to be read.  They are not one theorem about every description; each says what its own readers cannot
--| tell.

--| THE KNOWER'S BIT.  What is read: the triple's solver, and the quartic's two receipts.  The solver finds a witness with
--| the bit one way and with it the other; the receipts hold for the root given on a yes and for the root given on a no;
--| and the two roots are not one root.  The evidence is the same and the identification is not.

--| THE TWO LADDERS.  What is read: the closures at the top, by any reader whatever.  Episode 12's ladder begins on the
--| truth and the other on a number distinguished, and the knower's alpha of each begins on its own first fact.  Every
--| reader of the two closures returns the same for the one ladder as for the other.

--| THE RECORD.  What is read: the readings at the places looked at.  For any finite list of places and any model there is
--| another that reads the same at every one of them and is not the same model.  And what is read of a tally is the same
--| for either carrier.
end the_same_evidence_and_two_identifications

--#print axioms the_knowers_bit_is_not_fixed_by_what_is_read
--#print axioms every_reader_of_the_closures_reads_the_two_ladders_alike
--#print axioms the_record_and_the_tally_do_not_fix_it

section two_counts_and_no_third
open readers_experience

--| TWO COUNTS, AT EVERY LENGTH.  Episode 12 has that the closed walks obey the table: each count is the trace of the one
--| before less the determinant of the one before that.  So two in a row always fix the next.  And two are always needed:
--| the square of three in a row, the outer two less the middle squared, is three hundred and sixty at the start and is
--| multiplied by the determinant at every step, so it is never nothing.



end two_counts_and_no_third

section three_ways_as_three_maps

--| THREE WAYS, AS THREE MAPS.  One table goes in.  Kept: it comes out as it went in.  Struck: the arm that does not click
--| is set to nothing.  Turned over: the arm that clicks on a falsehood, false on true, is owed.  On a table of a stay and
--| two crossings the three give the table itself, the table with nothing out, and the table with the way back owed.
def kept (table : Table) : Table := table


--| And the gap squared of the three: four of the crossings, one by the other; nothing; and the same owed.  Where the
--| crossings are of one sign that is over nothing, nothing, and under nothing.

--| The struck map moves only the arm that does not click, and the turned map only the arm that clicks on a falsehood.
end three_ways_as_three_maps

--#print axioms the_next_count_is_fixed_by_the_two_before
--#print axioms the_square_of_three_is_multiplied_by_the_determinant
--#print axioms the_square_of_three_is_never_nothing
--#print axioms the_three_maps_on_a_stay_and_two_crossings
--#print axioms the_gap_squared_of_the_three_ways
--#print axioms which_arm_each_map_moves

section the_bending_energy_and_the_stencil

--| THE BENDING ENERGY AND THE STENCIL.  A reading that comes round: the same again after so many places.  Its difference
--| comes round, and so does the reading one place on.  Around it, one reading against the difference of another is the
--| difference of the one, owed, against the other one place on.





--| THE FIRST VARIATION.  The bending energy of a reading is its second difference squared, summed.  Its first variation
--| against another reading is the two second differences one by the other, summed.  Around what comes round, that is the
--| fourth difference of the first against the second two places on.

--| And the fourth difference is the stencil: one, four owed, six, four owed, one.
end the_bending_energy_and_the_stencil

--#print axioms by_parts_for_what_comes_round
--#print axioms the_variation_of_the_bending_is_the_fourth_difference
--#print axioms the_fourth_difference_is_the_stencil

section the_bending_energy_assembled

--| THE BENDING ENERGY, ASSEMBLED.  The energy of a reading is its second difference squared, summed.  Of two readings, the
--| two second differences one by the other, summed.  Move a reading by a number of another: the energy moves by twice
--| that number of the two, and that number squared of the other's energy, and by nothing else.  The two belongs to the
--| energy; half the energy has the two together for its first variation.





--| WHAT COMES ROUND, AND WHAT CLIMBS.  The stencil is nothing on a cubic in the place, at every place: that is Episode
--| 12's, and it is about one place and its neighbours.  The energy above is summed round a walk, and a reading that climbs
--| does not come round.  They are two statements and are kept two.

--| STATIONARY, AT EVERY PLACE.  Let a reading come round a walk of some steps, and let the two together be nothing against
--| every reading that comes round.  Then its fourth difference, the stencil, is nothing at every place.



end the_bending_energy_assembled

--#print axioms the_bending_energy_of_a_reading_moved
--#print axioms a_reading_that_climbs_does_not_come_round
--#print axioms stationary_against_all_that_comes_round_is_the_stencil_nothing

section what_can_be_recovered
open readers_experience readers_interpretation_of_the_experience the_table

universe cases evidences identifications

--| WHAT CAN BE RECOVERED.  Cases, some of them admissible.  What is kept of a case: the evidence.  What is to be got back:
--| the identification.  A reader of the evidence recovers the identification when it returns it for every admissible case.
--| The identification can be recovered when some reader does.  Nothing is asked of the reader but that it is a function.

--| THE OBSTRUCTION.  Two admissible cases of which the same is kept, and which are identified differently: then no reader
--| of what is kept recovers the identification.  The reader is handed one thing twice and cannot return two.

--| THE KNOWER'S BIT.  The cases are the two decisions.  What is kept of a decision: the triple itself, with its clauses;
--| what the solver says of it under that decision's parity; what the quartic's two receipts come to on the root that
--| decision returns; and the first of that root's pair, the part with no root of ninety in it.  Not kept: the decision;
--| which parity the solver was given; and the pair's other part.  The triple is one for both, and its reading by a parity
--| is another thing and is not kept.  The first of the pair is not the whole number under the root: those differ.  The
--| same is kept of both decisions.  So the decision cannot be recovered from what is kept.
def what_is_kept_of_a_decision (decision : Bool) : Basis × Bool × (Int × Int) × Int :=
  (the_knowers_triple,
   satSearch the_knowers_triple (if decision then an_odd_number_are_true else an_even_number_are_true) 3,
   ((the_surd_product (you_re_a_daisy_if_you_do (bitFACT decision)) (you_re_a_daisy_if_you_do (bitFACT decision))).1
        - 11664 * (you_re_a_daisy_if_you_do (bitFACT decision)).1 + 24564384,
    (the_surd_product (you_re_a_daisy_if_you_do (bitFACT decision)) (you_re_a_daisy_if_you_do (bitFACT decision))).2
        - 11664 * (you_re_a_daisy_if_you_do (bitFACT decision)).2),
   (you_re_a_daisy_if_you_do (bitFACT decision)).1)

theorem the_same_is_kept_of_both_decisions :
    what_is_kept_of_a_decision true = what_is_kept_of_a_decision false := by
  have the_solver : satSearch the_knowers_triple an_odd_number_are_true 3
      = satSearch the_knowers_triple an_even_number_are_true 3 := by decide
  have the_receipts :
      ((the_surd_product (you_re_a_daisy_if_you_do (bitFACT true)) (you_re_a_daisy_if_you_do (bitFACT true))).1
            - 11664 * (you_re_a_daisy_if_you_do (bitFACT true)).1 + 24564384,
        (the_surd_product (you_re_a_daisy_if_you_do (bitFACT true)) (you_re_a_daisy_if_you_do (bitFACT true))).2
            - 11664 * (you_re_a_daisy_if_you_do (bitFACT true)).2)
      = ((the_surd_product (you_re_a_daisy_if_you_do (bitFACT false)) (you_re_a_daisy_if_you_do (bitFACT false))).1
            - 11664 * (you_re_a_daisy_if_you_do (bitFACT false)).1 + 24564384,
        (the_surd_product (you_re_a_daisy_if_you_do (bitFACT false)) (you_re_a_daisy_if_you_do (bitFACT false))).2
            - 11664 * (you_re_a_daisy_if_you_do (bitFACT false)).2) := by decide
  have the_first_of_the_pair : (you_re_a_daisy_if_you_do (bitFACT true)).1 = (you_re_a_daisy_if_you_do (bitFACT false)).1 := by
    decide
  show (the_knowers_triple, satSearch the_knowers_triple an_odd_number_are_true 3, _, _)
      = (the_knowers_triple, satSearch the_knowers_triple an_even_number_are_true 3, _, _)
  rw [the_solver, the_receipts, the_first_of_the_pair]


--| And the two decisions return two roots.

--| THE TWO FIRST RUNGS.  The cases are two names, the old rung and the new.  What is kept of a name is the fact it names:
--| the truth, or a number distinguished.  The two facts are one fact, asked only whether it is true.  So the name cannot
--| be recovered from the fact, nor from anything read off the fact.

end what_can_be_recovered

--#print axioms the_same_kept_and_two_identifications_cannot_be_recovered
--#print axioms the_same_is_kept_of_both_decisions
--#print axioms the_knowers_decision_cannot_be_recovered
--#print axioms the_two_decisions_return_two_roots
--#print axioms the_name_of_the_first_rung_cannot_be_recovered

section the_quartic_factors_at_the_devices_weights
open readers_experience

--| THE QUARTIC, FACTORED WHERE THE DEVICE STANDS.  Episode 12 has that the closing quartic is two factors, one for a number
--| and one for that number owed, whenever eighteen of the number squared is five.  No whole number is such a number, so
--| at the device's own weights that receipt says nothing.  In Episode 12's pairs it does.  Eighteen of such a number is
--| the root of the round trip.  Eighteen of the quartic is a pair by the same pair with its second part owed, and the
--| product has no part of the root.  Which of the two pairs is which is not read by the product.


--| Turned over, the two pairs change places and the product is the same.
end the_quartic_factors_at_the_devices_weights

--#print axioms the_quartic_at_the_devices_weights
--#print axioms eighteen_of_the_quartic_is_a_pair_by_itself_turned_over
--#print axioms the_two_pairs_change_places_and_the_product_stays


section two_reversals
open readers_experience

--| TWO REVERSALS.  The device has two things that can be turned over, each with a number that changes sign.  The roots:
--| the outer radius and the hole change places, and the part by the root of the round trip changes sign.  The table: it
--| is turned over, the crossings change places, and the bent card by the quarter turn changes sign.  Each leaves what is
--| read of the table as it was, and neither moves the other.

--| Turned over, the table has the trace, the determinant and the gap squared it had.

--| And what changes sign is the bent card by the quarter turn: the arm's thirteen, with a direction.

--| The roots in either order add to the trace and multiply to the determinant.

--| FOUR STATES, ONE READING.  A root first and a table: four ways.  What is read of each, the trace, the determinant and
--| the gap squared of the table and the sum and the product of the two roots, is the same for all four.


--| THE ONE CONSTRAINT THERE IS.  The knower's triple sets the knower's coin against whether the arm's two coins differ.
--| It does not read which way they differ: true on false and false on true are one to it, under either parity.  So it
--| ties the knower's coin to a crossing, and not to the crossing's direction.
end two_reversals


section the_mirror_the_turn_and_the_spinor
open readers_experience

--| THE MIRROR, THE TURN AND THE SPINOR.  Asked how the two reversals are paired, the author answered with three things
--| done: the mirror projection, the rotation in two dimensions, and the spinor's rotation, the last being the arrow of
--| time.  The first is the table turned over.  The second is the table carried by the quarter turn.  The third is the sign
--| the table does not see.

--| The table carried by the quarter turn: the quarter turn, the table, and the quarter turn back.

--| Carried, it reads as it did.

--| What it is: the table turned over, with both crossings owed.

--| Carried twice, it is back.  On the table the quarter turn is done twice and nothing is owed.

--| In the turns it is not back.  The quarter turn twice is the whole turn owed, and the quarter turn turned over is itself
--| owed.  This is the sign the table does not see.

--| It is not the roots changing places.  Owed whole, the outer radius is not the hole: the eighteen is owed with it.

--| The place that is not on the frinkahedron is the one where neither sample holds a bracket.
end the_mirror_the_turn_and_the_spinor

section the_turn_as_a_number
open readers_experience

--| THE TURN, AS A NUMBER, WITH NO CHOICE.  Meanings builds the complex numbers as two signed reals, along and across.  The
--| quarter turn, nothing along and one across, is one owed by itself: the turns' quarter turn twice, above, as a number.
--| The table turned over owes its false-on-true crossing, so its trace is thirty-six and its determinant four hundred and
--| fourteen, and its gap squared is under nothing.  Its polynomial has no root among the reals: at eighteen it reads ninety.
--| Among the complex numbers it has two, eighteen along and the root of ninety across, held or owed.



--| AND THE TURNS, AS NUMBERS.  Doubled once more, two complex numbers make a quaternion, and the turns of Episode 12 are
--| numbers with no choice: one quarter turn by another is the third, the other by the one is the third owed, and each by
--| itself is one owed.  The order of a product is seen: the one by the other is not the other by the one.  That is the
--| cross product in the turns, above, on numbers.
end the_turn_as_a_number

section the_first_variation_of_the_exponential
open readers_experience

--| THE FIRST VARIATION OF THE EXPONENTIAL.  The author's, 23 November 2026: after the quaternions come the exponentials,
--| r and θ, both rationals; they cannot be built before the derivative is understood, and the first variation of the
--| exponential can be done now; then convergence guarantees a bracket on the derivative: meet O(h²) (declared).
--| What is checked, at the card's thickness, one part in n.  The exponential that grows, n and one over n taken k times:
--| its step is itself by one part in n, exactly; it is its own first variation, with nothing left over.  The exponential that
--| turns, n and the quarter phase taken k times: its step is itself, n times, and itself turned a quarter, exactly; the
--| first variation of a turning is the quarter turn of what turns.  And what it does not do exactly: it leaves the circle.
--| The radius squared goes n squared and one each step, where the circle would keep n squared: one part in n squared, the
--| step squared, and nothing else.  That is the bracket on the derivative, of the second order in the step, as thirteen by
--| the step squared is for the residual.  Episode 12 already has a turning with a rational r and a rational cosine, three
--| and four over five, that never lands on a label.

def the_step_of_a_turn (n : Int) : Int × Int := (n, 1)



end the_first_variation_of_the_exponential


section eight_expressions_to_check
open readers_experience the_table the_table.Account

--| EIGHT EXPRESSIONS TO CHECK.  The author's, 18 November 2026: one choice, two hypotheses, four proposals, eight logical
--| expressions to check; each proposal under each hypothesis (declared).  The device's eight are the clocks of the
--| connected steps, and a clock is a coin and an arm.

--| The eight, in order: the two coins by the four arms.

--| What the knower's triple says of a clock, under each parity.

--| Four hold and four do not, under either parity, and what holds under the one does not under the other.

--| For every arm, one coin holds and the other does not.

--| Which: when an odd number are true, the coin that holds is true where the arm's two coins are the same.
end eight_expressions_to_check

section the_turn_in_space_and_the_turn_in_time
open readers_experience the_table the_table.Account

--| THE TURN IN SPACE AND THE TURN IN TIME.  The author's, 18 November 2026: you can turn the coin spatially, you cannot
--| turn the coin temporally; that is the arrow of time deflated (declared).  On a connected step there are two things to
--| do.  Turn every coin over: the turn in space.  Read the step from its end, the after clause backwards and then the
--| before clause backwards: the turn in time.


--| What execute counts less what compile builds: nothing where the step is level, the bent card where it is over, the
--| bent card owed where it is short.

--| Either way turned, a connected step is a connected step.

--| The clock and its complement: true, false, true and false, true, false.  The one is over by the bent card and the other
--| short by it.


--| Turned in space the clock is its complement, and the bent card is owed.

--| Turned in time the clock is the clock.  Nothing is owed and nothing has changed places.

--| And only these two, of the steps that are over or short, are left as they were by the turn in time.
end the_turn_in_space_and_the_turn_in_time

section the_two_areas_at_right_angles
open readers_experience

--| THE TWO AREAS.  The author's, 18 November 2026: there are two areas, at right angles; the spatial area is a circle with
--| no pole and the simplicial area has the torus pole in it; at right angles in the inner product inferred from the Sobolev
--| semi-norm with natural boundary conditions (declared).  A semi-norm reads differences.  On the four arms: every pair of
--| arms, the difference of the one reading by the difference of the other.

def the_pairs_of_arms : List (Direction × Direction) :=
  [((true, true), (true, false)), ((true, true), (false, true)), ((true, true), (false, false)),
   ((true, false), (false, true)), ((true, false), (false, false)), ((false, true), (false, false))]

--| The two areas' rises: the weight the arm stores, and one fencepost on every arm.

--| One fencepost on every arm has no differences: against itself it reads nothing, and against the weight nothing.

--| And against anything: it has no differences to read.

--| The weight against itself is three bent cards squared: the three arms that click, each over the fourth by the bent card.
end the_two_areas_at_right_angles


section the_reviewers_named_rung
open readers_experience the_table

--| THE REVIEWER'S NAMED RUNG.  The author's, 18 November 2026: the thirty-six subjunctive equalities are the reviewer's
--| named rungs of Episode 10; it is a statement of finite 3SAT up to thirty-six triples; the fencepost here is four and
--| not five; and that is the difference between the fencepost counting up and the fencepost counting down, the same
--| difference of the quantum (declared).  Episode 10 makes a page by `rebut planted polynomial argument`: two facts and the
--| page before.  The page it makes is a methodology, which holds those two facts, two boxes, and the page before.

--| A page read all the way down is its two facts and then the page before.

--| Dealt from a tape, a preprint read all the way down is two facts a page and one more.

--| Thirty-five rebuttals are thirty-six pages: the page handed in is the fencepost.  And they are seventy-one facts.

--| Counted up there is one more than counted down: the pages are the rebuttals and the fencepost.
end the_reviewers_named_rung


section counted_down_and_counted_up
open readers_experience «springer-verlag» THE_GOSPEL

--| COUNTED DOWN AND COUNTED UP.  Episode 10 counts down: a page is made from the page after it, by `rebut`, and holds two
--| facts, the one handed in and the one searched for.  Episode 11 counts up: a page is set in type on the page below it, and
--| what it sets is the reviewer's page of the same number.  Here is what is set: the two facts, and the proposition that
--| the two agree.  That proposition is the subjunctive equality.

--| What the reviewer's page holds: the two facts, the box, the box lifted, and the page it answers.

--| Set in type, the page is the two facts and the proposition that the two agree, on the page below.

--| And the count goes up by one: the universe id of the page is one more on the page below's.

--| THREE AND TWO.  Read all the way down, a page counted down is two facts and a page counted up is three: the two, and
--| the truth standing for the proposition that they agree.  The third is the one that is taken as given.

--| THE FENCEPOST.  A page that names one fact twice sets a proposition that holds of itself: nothing is inferred.

--| A page that names two facts sets a proposition that the two facts must supply: there are two facts that do not agree.

--| And where both hold, they agree: the equality is inferred from the two facts.
end counted_down_and_counted_up


section two_computations_on_one_encoding
open readers_experience the_review_on_the_ledger

--| TWO COMPUTATIONS ON ONE ENCODING.  The author's, 18 November 2026: there are two different computations on the same
--| encoding (declared).  Episode 12 has both, on the first card: the review counted down from the manuscript to the first
--| page, every reviewer asked, and the ascent counted up from that first page to the thirty-sixth, found by search.  The
--| encoding is the one preprint.  Here are the two, read all the way down.

--| The manuscript handed in is three facts.

--| Counted down: thirty-five rebuttals on the manuscript, two facts each.

--| Counted up: thirty-five pages set in type on the review, three facts each.

--| So the second computation is written on top of the first, and what it adds, less what the first added, is one fact a
--| page: thirty-five agreements.

--| In pages: the manuscript is two, the review thirty-five more, the ascent thirty-five more again.

--| And the ascent stands on the review: its first page is the reviewer's first page.
end two_computations_on_one_encoding


section three_bridges_on_the_row_of_steps
open readers_experience readers_interpretation_of_the_experience

--| THREE BRIDGES, ON THE ROW OF STEPS.  The numerical card names three things a theorem of Lovelock's asks for: two
--| derivatives and no more, a tensor, and no divergence.  The author's, 18 November 2026 (declared): for the first, the
--| variational models hold the answer, the norm is implied and Lorentz is an asymptote; for the second, this is the Spline,
--| and the tensor is the Galerkin method on the variational solution of the Euler beam on the steps i-2, i-1, i and i+1;
--| for the third, the indexing process.  Here is each on the row of steps.  None of them is on a manifold.

--| THE FIRST.  An action written in values and first differences: the sum of the difference by the difference.  Moved, it
--| varies by the second difference, and the second difference reads three places.


--| The asymptote.  The factor squared, by what is left of the whole when the part is taken, is the whole.  Take the whole
--| and there is no factor.

--| THE SECOND.  The third difference on four steps: i-2, i-1, i and i+1.

--| Shifted, it is the same function at the shifted place.

--| Turned end for end, it is owed, at the place turned.

--| The fourth difference is the step of the third: a reading is stationary where the third difference does not step.

--| So what is stationary is stationary shifted, and stationary turned end for end.


--| On a cubic, with a step of any length, the third difference is six of the cubic's last coefficient by the step cubed:
--| it goes as the cube of the step.

--| A re-lettering that does not keep the steps is not among these.  Change two places of a straight line and it is no
--| longer stationary.


--| THE THIRD.  A difference summed along the steps is the end less the first: every fencepost between is taken and given
--| back, and the end one is left.
end three_bridges_on_the_row_of_steps


section four_gawks_and_three_closures
open «springer-verlag» THE_GOSPEL the_representation assembly_instructions readers_experience the_table
attribute [local instance high] rung01 rung02 rung03 rung04 rung05 rung06 rung07 rung08 rung09 rung10 rung11 rung12 rung13 rung14 rung15
  rung16 rung17 rung18 rung19 rung20 rung21 rung22 rung23 rung24 rung25 rung26 rung27 rung28 rung29 rung32 rung33 rung34 rung35 a_truth_about_the_experience

--| FOUR GAWKS AND THREE CLOSURES.  The author's, 18 November 2026: starting from the zero that is the same-difference
--| quantum, the knower's interpretation of the reader's interpretation of the experience, call the Atreyu process's gawk
--| four times; that makes three closures (declared).  Here it is, on the processes written out from the bottom.

--| The quantum: a zero on the same difference.

--| Gawked at once, twice, three times and four.

--| Once, it is the first page: a one.

--| Twice, three times, four: each is the rest of the call.

--| Four gawks, and three places between them.  At each the equivalence process is asked whether it believes the one
--| against the next: three closures.

--| Each is a difference, with the proposition that the one is under the next.

--| And each reads as one cell: three closures, three cells.
--| What each holds, read all the way down: the quantum one fact, the first gawk twenty-two, and then thirty-nine,
--| thirty-eight, thirty-nine.  After the second gawk it goes down one and up one.
end four_gawks_and_three_closures


section the_agreements_on_the_ledger
open readers_experience the_review_on_the_ledger

--| THE AGREEMENTS, ON THE LEDGER.  A page set in type holds two facts and the proposition that they agree.  Whether they
--| do was not among the receipts.  Episode 12 has the thirty-six pages on the first card, so ask each: how does its first
--| fact click, and how its second?

--| Counted up: the two clicks of every page set in type, from the top.

--| Counted down: the two clicks of every rebuttal, and of the manuscript under them.

--| Thirty-four agree and one does not.  The one is the top page, the thirty-sixth, and it is true on false.

--| Counted down every rebuttal names two facts that click, thirty-five of them.  Under them is the manuscript handed in,
--| and the manuscript is true on false.  That is where the top page has it from.
end the_agreements_on_the_ledger

section the_fixed_point_and_both_branches
open «springer-verlag» THE_GOSPEL the_representation assembly_instructions readers_experience the_table
attribute [local instance high] rung01 rung02 rung03 rung04 rung05 rung06 rung07 rung08 rung09 rung10 rung11 rung12 rung13 rung14 rung15
  rung16 rung17 rung18 rung19 rung20 rung21 rung22 rung23 rung24 rung25 rung26 rung27 rung28 rung29 rung32 rung33 rung34 rung35 a_truth_about_the_experience

--| THE FIXED POINT.  The author's, 18 November 2026: the third and fourth closures' residue should be exactly the same,
--| meaning a fixed point; the second and third should click, yet their values should be different; and it takes exactly
--| five quanta to send a nowtrino back and forth between the two closest distances (declared).  Gawk a fifth time.


--| The fifth is the fourth.


--| What the third closure stores is what the fourth stores; and the second stores it too.  The first does not.

--| That proposition cannot hold: nothing is under itself.


--| What the first closure stores holds: the first page is under the rest of the call.

--| And all four click.

--| Yet the values differ: twice is not three times, and three times is not four.

--| BOTH BRANCHES.  The author's: that one step does not matter; it is computed on both branches, in the opposite order
--| (declared).  Take the first page and call its fact false, and gawk on.

--| After one step more the branch called false is the branch called true, and it stops where that one stops.

--| WHAT A FIRST PAGE HOLDS.  Twenty-two facts: its own, and those of its page number, its proof, its book and its
--| constant.

end the_fixed_point_and_both_branches


section the_action_of_light_and_matter
open readers_experience readers_interpretation_of_the_experience

--| THE ACTION OF LIGHT AND MATTER.  Verse twenty-eight: "And from these was written the action of light and matter,
--| minimally coupled."  The device has the two halves apart: Episode 12's action of a square of links, and the state
--| carried back along a link.  Write them at one site as one thing: what the square of links holds, the state carried
--| back along a link, and the state against itself.  One turn at every site, of the links and of the state together,
--| leaves all three as they were.  The link in the second is the link in the first: that is what "minimally" asks.

end the_action_of_light_and_matter


section the_constant_as_physics
open readers_experience the_table

--| THE CONSTANT, AS PHYSICS.  The author's, 18 November 2026: the missed number can be pushed back through the stack to
--| appear as `Equivalation.physics`; that is the root of the quartic; read this episode from the beginning (declared).
--| From the beginning: the constant is an Area, the one nobody built and nobody will, whose count was already printed.  A
--| jar is a fact and an Area.  The physics of an equivalation is a fact and a jar.  So put the constant in a jar, and the
--| jar under the physics.  Nothing is opened: the constant is still a name, and nothing below asks what is in it.

--| What a jar holds is what was put in it, whatever that was.

--| So this jar holds the constant, and counted it is the number Episode 8 printed.


--| And the reader of an equivalation does not read it.  Of the physics it returns the one fact; the jar vanishes.

--| The two that stand on it: zero-like, a fact on the physics; one-like, a proposition on the physics twice.  Read, the
--| three are one fact, two and three, and the constant is in none of the readings.

end the_constant_as_physics


section the_posts_and_the_panels
open readers_experience

--| THE POSTS AND THE PANELS.  The author's, 18 November 2026: the thirty-seven are the fence posts and the thirty-six the
--| fence panels, and the polynomial can be computed from them; the four posts past the Area are the four-member fencepost,
--| the bridge to the arm that does not click (declared).  Episode 8 wrote the steps of its argument as a list: the number
--| read three times, and then one reading for every kind of thing after it, in the order the kinds were made.  Set the
--| first two aside, so that the number is counted once.

--| Thirty-six steps, one for each kind.


--| COUNTED FROM THE FRONT.  The fifth step is the reading of a limit, the thirteenth of an Area, the eighteenth of an
--| Abstraction, the thirty-sixth of a Closure.

--| THE FOUR BETWEEN.  Past the Area and short of the Abstraction stand four: a pigeonhole, a jar, an equivalation and an
--| encoding.  Four posts and five panels.

--| COUNTED FROM THE BACK.  Episode 8 took its numbers from the other end: the tapes of the last steps, laid end to end.
--| Five for the frame, thirteen for the coefficient, eighteen for the memory, and twice the memory for the trace.

--| So the place of the Area from the front is the length of the coefficient from the back, and so for the others: two
--| counts of one fence, from its two ends.
end the_posts_and_the_panels

section inflated_twice
open readers_experience readers_interpretation_of_the_experience

--| INFLATED TWICE.  The author's, 18 November 2026: the arm that does not click can be inflated by the excluded middle
--| twice; the first inflation is one quadratic in the quartic and the second is the other; the second gives ratios and not
--| reals, and the reals are only ever described by a process of completion (declared).  The quartic at the device's
--| weights is two quadratics, written as pairs: a whole part, and a part by the root of the round trip.

--| Inflated once: the one quadratic.  It has a part by the root, and that part is the frame by the place.

--| Inflated twice: the one by the other.  Eighteen of the quartic, and nothing by the root.  What is left is whole.

--| The other is the one with its part by the root owed, and either order gives the same.
end inflated_twice


section pushed_through_the_sixteenth_page
open «springer-verlag» the_representation readers_experience the_table the_review_on_the_ledger
attribute [local instance high] rung01 rung02 rung03 rung04 rung05 rung06 rung07 rung08 rung09 rung10 rung11 rung12 rung13 rung14 rung15

--| PUSHED THROUGH.  The author's, 18 November 2026: push the missed number back through the stack; on the way back it is
--| the other root, one; these will be scaled later (declared).  The reviewer's sixteenth page is the page that draws a fact
--| out of an equivalation: out of a physics its fact, out of a zero-like its fact, out of a one-like the carrier's symbol.
--| It asks its source for the equivalation.  So hand it a source whose one is the physics of the constant, and then the
--| zero-like on it, and then the one-like on it, and see what page comes back.


--| The same page, all three times.  The constant went in and the page did not move: the jar vanished on the way.

--| What it drew: from the physics and the zero-like, the zero; from the one-like, the carrier's symbol.  On this card the
--| two are one fact.
end pushed_through_the_sixteenth_page

section the_sign_the_record_cannot_see
open readers_experience readers_interpretation_of_the_experience

--| THE SIGN THE RECORD CANNOT SEE.  Verse thirty-two: "And the electron was dealt, and its sign was a coin the record
--| cannot see."  On the lattice: owe the state at every site, the whole of it, and leave the links alone.  What a square of
--| links holds, the state carried back along a link, and the state against itself are as they were.

--| The whole turn owed is a turn of length one, and it leaves every link where it was.


--| So the state and the state owed give one action.  The record of the action cannot tell them apart.
end the_sign_the_record_cannot_see


section the_one_that_goes_out_and_comes_back
open «springer-verlag» THE_GOSPEL the_representation assembly_instructions readers_experience the_table
attribute [local instance high] rung01 rung02 rung03 rung04 rung05 rung06 rung07 rung08 rung09 rung10 rung11 rung12 rung13 rung14 rung15
  rung16 rung17 rung18 rung19 rung20 rung21 rung22 rung23 rung24 rung25 rung26 rung27 rung28 rung29 rung32 rung33 rung34 rung35 a_truth_about_the_experience

--| THE ONE THAT GOES OUT AND COMES BACK.  The author's, 18 November 2026: one, twenty-two, thirty-nine, thirty-eight,
--| thirty-nine; the photon is the one between thirty-eight and thirty-nine, going both ways; this is emission and reception
--| (declared).  Take a rest of the call apart: the facts of its last page, of its two preprints, and of its two constants.

--| Twice, three times, four.  Going out, the last page gives up a cell and one fact passes from the one preprint to the
--| other.  Coming back, the one preprint has it again.  The two constants do not move.

--| And after that nothing goes anywhere: the fifth is the fourth, and the two preprints stand level.
end the_one_that_goes_out_and_comes_back


section told_apart_when_there_are_two
open «springer-verlag» THE_GOSPEL the_representation assembly_instructions readers_experience the_table
attribute [local instance high] rung01 rung02 rung03 rung04 rung05 rung06 rung07 rung08 rung09 rung10 rung11 rung12 rung13 rung14 rung15
  rung16 rung17 rung18 rung19 rung20 rung21 rung22 rung23 rung24 rung25 rung26 rung27 rung28 rung29 rung32 rung33 rung34 rung35 a_truth_about_the_experience

--| TOLD APART WHEN THERE ARE TWO.  The author's, 18 November 2026: seven is the fact that you can tell things apart if
--| there are two of them (declared).  The seventh kind is the trial.  A sample holds one limit, or it holds a bracket: two
--| limits, each with its fact.  Put a hypothesis, one fact, on each.

--| ON THE TWO BRANCHES.  There are two of them, the first page as it is and the first page with its fact called false.  One
--| step on, they can be told apart: ask each how its first fact clicks.


--| And one step after that there are not two of them: no reader of any kind returns one thing for the one and another for
--| the other.
end told_apart_when_there_are_two


section the_three_term_machine
open readers_experience

--| THE THREE-TERM MACHINE.  The author's, 18 November 2026: the three terms are the distance, the velocity and the
--| bullshit; the gawk and the lattice is its clock; verse twenty-seven's other ingredients are this machine (declared).
--| Episode 5's measurement is made three ways: an origin, with one number; a distance to, with two; a speed, with three.
--| Make the least of each, on zeros, each standing on the ones before.

--| Read all the way down they hold two facts, five and eleven.  Read by the measurement's own reader, nothing, one and two:
--| the origin is not a reading.
end the_three_term_machine

section the_cross_product_in_the_turns
open readers_experience readers_interpretation_of_the_experience

--| THE CROSS PRODUCT.  The author's, 18 November 2026: all interpretations have a cross product, and that finishes the
--| frinkahedron for the two- and three-term machines (declared).  In the turns it is this: of two turns, the part that is
--| not whole, crossed.

--| The one by the other, less the other by the one, is the cross twice; and nothing of it is whole.

--| Turned over it is owed, and a turn crossed with itself is nothing.

end the_cross_product_in_the_turns

section sent_and_returned
open readers_experience

--| SENT AND RETURNED.  The author's, 18 November 2026: true on true is a photon emitted and received; false on false is
--| no photon predicted; true on false is a photon sent and not returned; false on true is the promise sent and the photon
--| returned (declared).  The first coin, sent; the second, returned.  An arm can click unless something was sent and did
--| not come back; and that arm is the one short by the bent card.
end sent_and_returned

section one_list_read_from_its_two_ends
open readers_experience

--| ONE LIST, READ FROM ITS TWO ENDS.  The author's, 18 November 2026: the front and the back are going to be shown to be
--| the covariant and the contravariant readings of an earlier machine, and that is how the daisy is found (declared).  What
--| is here: both counts are of Episode 8's one list.  From the back its first step is the closure's, and its fifth is the
--| coordinate system's, the one whose own tape is the five.
end one_list_read_from_its_two_ends


section six_pairs_and_six_by_six
open readers_experience

--| SIX PAIRS, AND SIX BY SIX.  The author's, 18 November 2026: the three-term machine can be shown to model the whole
--| frinkahedron; the thirty-six steps are a grid of six by six, and the frinkahedron has another face of six by six
--| (declared).  A count that fits, set palm_the_middle_card it: four arms have six pairs, a square of links stands on a pair, and the
--| curvature across takes a pair and a pair.
def the_pairs_of_pairs : List ((Direction × Direction) × (Direction × Direction)) :=
  the_pairs_of_arms.flatMap fun this => the_pairs_of_arms.map fun that => (this, that)


--| On the source the arms carry, the curvature across is nothing unless the pair is taken with itself.  Six of the
--| thirty-six are not nothing: the six where the two pairs are one pair.


--| And on those six: three with the arm that does not click, the round trip; three without it, the outer radius squared.
end six_pairs_and_six_by_six


section the_running_count_from_each_end
open readers_experience

--| THE RUNNING COUNT, FROM EACH END.  The author's, 18 November 2026: look through the encodings for the numbers not yet
--| used; there are receipts in there (declared).  Every kind has a tape, and Episode 8 has each tape's length.  Lay the
--| tapes end to end from the front, and from the back, and keep the running count.

--| The tapes, kind by kind.

--| From the front.

--| From the back.

--| WHERE THE COUNTS FALL.  From the front: seven at the third kind, nineteen at the eighth, twenty-three at the tenth,
--| twenty-five at the eleventh, twenty-nine at the thirteenth, forty-seven at the eighteenth, ninety at the thirty-third.
--| From the back: thirteen at the fourth, eighteen at the fifth, twenty-two at the sixth, twenty-eight at the eighth,
--| forty-two at the thirteenth, ninety at the thirty-first.  A hundred and one in all.

--| By length: one tape of one, eighteen of two, six of three, nine of four, two of five.  In marks: one, thirty-six,
--| eighteen, thirty-six and ten.

--| And set palm_the_middle_card one another, as arithmetic and no more: forty-seven and ninety; forty-two and forty-seven; a hundred and
--| thirty-seven and forty-two.
end the_running_count_from_each_end


section the_list_says_how_deep_to_cut
open readers_experience

--| THE LIST SAYS HOW DEEP TO CUT.  Episode 8 takes the coefficient from the last four tapes and the memory from the last
--| five.  The four and the five are themselves the lengths of two tapes in the list: the path's, the thirty-first kind's,
--| and the coordinate system's, the thirty-second's.  So the list is cut at depths it holds.

--| Between the area and the abstraction: the tapes of the four posts and of the abstraction are eighteen marks, the
--| count from twenty-nine to forty-seven.  And the first five tapes and the last three are eleven each, which is why
--| ninety is reached from either end.
end the_list_says_how_deep_to_cut

section a_hexagon_of_the_pairs
open readers_experience

--| A HEXAGON OF THE PAIRS.  The first card's frinkahedron is a hexagon by a hexagon: thirty-six vertices, the pairs of
--| six by six, in two sectors of eighteen by whether the two numbers add to an even number.  The six pairs of arms can be
--| set round a hexagon so that each shares an arm with the next, and so that every second one has the arm that does not
--| click.  This is one such way round; there are others, and the choice is not the device's.

def share_an_arm (this that : Direction × Direction) : Bool :=
  this.1 == that.1 || this.1 == that.2 || this.2 == that.1 || this.2 == that.2

--| They are the six pairs; every second one has the arm out; and each shares an arm with the next, the last with the first.

--| So the six by six falls into two sectors of eighteen, by whether the two places round the hexagon add to an even
--| number; and the six that are not nothing, a pair with itself, are all in the even one.

end a_hexagon_of_the_pairs

section the_residual_at_the_zero_and_at_the_one
open readers_experience readers_interpretation_of_the_experience

--| THE RESIDUAL AT THE ZERO AND AT THE ONE.  The author's, 18 November 2026: going down it is the zero and on the way back
--| the other root, one; these will be scaled later (declared).  Set palm_the_middle_card it: the residual of the pair, read at nothing
--| over one, at one over one, and at one over nothing.
end the_residual_at_the_zero_and_at_the_one


section the_residue_is_the_comparison
open «springer-verlag» THE_GOSPEL the_representation assembly_instructions readers_experience the_table
attribute [local instance high] rung01 rung02 rung03 rung04 rung05 rung06 rung07 rung08 rung09 rung10 rung11 rung12 rung13 rung14 rung15
  rung16 rung17 rung18 rung19 rung20 rung21 rung22 rung23 rung24 rung25 rung26 rung27 rung28 rung29 rung32 rung33 rung34 rung35 a_truth_about_the_experience

--| THE RESIDUE IS THE COMPARISON.  The author's, 19 November 2026: the coincidences are being moved round the device until
--| they all fall on the same comparison fact; there are four models and four blockers that do not commute, and these need
--| only an ordering; the circle does one model, then the next, then the next; and the residue is the comparison operator
--| necessary to separate the two values (declared).  Episode 5 has a residue: asked of two values, it returns the
--| proposition that the one, looked at, is under the other, looked at.  Its margin says it is the comparison operator that
--| had been missing.

--| ONE FACT.  The four closures hold one and the same fact.  They differ in the two values and in what stands between.

--| AN ORDERING.  The residue of one pair is what the next closure stores: each closure's comparison is the residue of the
--| one before.  Round it goes, one and then the next and then the next.

--| And it comes round to itself: at the fixed point the residue is the comparison it already was.

--| Two values with nothing to separate them have no residue: of two zeros it returns nothing at all.
end the_residue_is_the_comparison


section sixteen_abstractions_of_the_integer
open readers_experience the_table

--| SIXTEEN ABSTRACTIONS OF THE INTEGER.  The author's, 19 November 2026: there should be sixteen possible devices from
--| Episode 8; there are sixteen possible abstractions of the integer (declared).  The bent card asks its term for four
--| things: palm_the_middle_card, each for each, taken away, and less.  Episode 8's margin: these could be implemented differently, giving
--| different interpretations.  Take each as written, or turned over.  Sixteen devices, on the naturals, at Episode 8's scale.
def the_device_with (palm_the_middle_card_as_written false_shuffle_as_written the_double_lift_as_written less_as_written : Bool) : Nat × Nat :=
  let plus : Add Nat := ⟨fun a b => if palm_the_middle_card_as_written then a + b else b + a⟩
  let times : Mul Nat := ⟨fun a b => if false_shuffle_as_written then a * b else b * a⟩
  let minus : Sub Nat := ⟨fun a b => if the_double_lift_as_written then a - b else b - a⟩
  match less_as_written with
  | true => @bent_card.fenceposts_must_be_preserved Nat plus times minus ⟨fun a b => a < b⟩ (fun a b => Nat.decLt a b)
              List.length all_possible_variables
  | false => @bent_card.fenceposts_must_be_preserved Nat plus times minus ⟨fun a b => b < a⟩ (fun a b => Nat.decLt b a)
              List.length all_possible_variables

--| What a device reads: the first of its pair by the scale over the second, where there is a second.
def what_a_device_reads (pair : Nat × Nat) : Option Nat :=
  if pair.2 = 0 then none else some (pair.1 * all_possible_variables / pair.2)


--| Three things are read.  With taken away and less as written, Episode 8's number, four times: palm_the_middle_card and each for each
--| read the same turned over.  With less turned over, the number of turns of the crank and the scale, four times: the device
--| never leaves the house.  With taken away turned over, nothing, eight times.

--| THE ONE BETWEEN.  The author's: that value can be put into an equivalation; it is the universe between the zero-like
--| and the one-like (declared).  Of the three things read, nothing is the zero and Episode 8's number is the constant
--| nobody can write.  The one between, the number of turns, can be written: the Area of the tape of turns.  Put it in a
--| jar, and the jar under the physics.


--| And it stands between: the zero-like on it and the one-like on it, read, are two facts and three, and it is one.
end sixteen_abstractions_of_the_integer


section one_across_or_two_from_the_middle
open readers_experience the_table

--| ONE ACROSS, OR TWO FROM THE MIDDLE.  The author's, 19 November 2026: spooky action at a distance means you cannot tell
--| the difference between a photon originating at the source and an entangled pair being fired at both from the middle
--| (declared).  Two cases.  One thing goes across whole: the two halves set palm_the_middle_card each other and read as one.  Or two
--| things come out of the middle: the halves read apart.  What is kept is the count.


--| So no reader of the count returns which it was.
end one_across_or_two_from_the_middle

section the_four_ways_that_can_be_run
open «springer-verlag» THE_GOSPEL the_representation assembly_instructions readers_experience the_table
attribute [local instance high] rung01 rung02 rung03 rung04 rung05 rung06 rung07 rung08 rung09 rung10 rung11 rung12 rung13 rung14 rung15
  rung16 rung17 rung18 rung19 rung20 rung21 rung22 rung23 rung24 rung25 rung26 rung27 rung28 rung29 rung32 rung33 rung34 rung35 a_truth_about_the_experience

--| THE FOUR WAYS THAT CAN BE RUN.  The gawk branches on the first page's fact, and again on the rest of the call's second
--| fact, each against the nowtrino's.  On this process the nowtrino's fact clicks, so of the sixteen ways four can be run:
--| each of the two facts called true or called false.  Two were run before, on the first page.  Here are the other two.


--| All four stop in one place, and stay there.

--| And on the way each holds what the others hold: thirty-eight facts and then thirty-nine.
end the_four_ways_that_can_be_run

section sixteen_names_and_sixteen_devices
open readers_experience the_table the_table.Account

--| SIXTEEN NAMES AND SIXTEEN DEVICES.  The author's, 19 November 2026: the word is its name; sixteen names from four
--| marks; these are the opcodes; and all use the one sort order found at the level that is sixteen wide (declared).  A
--| name is a mark and a mark: what compile builds and what execute counts.  A device is four things as written or turned
--| over: palm_the_middle_card and each for each, taken away and less.  Give the device its four from the name's four coins.

--| The sixteen names in their order are the sixteen devices in theirs.

--| What a name reads is settled by its second mark alone, the one execute counts.  True on true reads Episode 8's number.
--| True on false, the mark that does not click, reads the turns of the crank.  The other two read nothing.

end sixteen_names_and_sixteen_devices


section the_two_variations_matched
open «springer-verlag» THE_GOSPEL the_representation assembly_instructions readers_experience the_table
attribute [local instance high] rung01 rung02 rung03 rung04 rung05 rung06 rung07 rung08 rung09 rung10 rung11 rung12 rung13 rung14 rung15
  rung16 rung17 rung18 rung19 rung20 rung21 rung22 rung23 rung24 rung25 rung26 rung27 rung28 rung29 rung32 rung33 rung34 rung35 a_truth_about_the_experience

--| THE TWO VARIATIONS, MATCHED.  The author's, 19 November 2026: bullshit to bullshit to closure is the first variation;
--| the experience is spatial and the interpretation temporal, and that is switched on the daisy; closure to closure to prop
--| is the second variation; there is
--| an option of a proposition already, and the two might be matched; and setting them equal is the proposal that true on
--| false is false on true, in two places (declared).  The first variation is `do_you_believe_it?`, and what it leaves in
--| a closure is an option.  The second is the closure's own order, and the part of it that reads the options is Episode
--| 5's implying implication: of two options, that the one implies the other.


--| MATCHED.  The first closure's option holds and the second's cannot.  So set the two against each other the four ways.
--| True on true, the first on itself: it goes.  False on false, the second on the third: it goes.  False on true, the
--| second on the first: it goes.  True on false, the first on the second: it does not.

--| THE TWO PLACES.  True on false is the first against the second; false on true is the second against the first.  The one
--| does not go and the other does, so the two are not one proposition.  Setting them equal is not done here.
end the_two_variations_matched

section the_two_first_variations
open readers_experience readers_interpretation_of_the_experience

--| THE TWO FIRST VARIATIONS.  The author's, 19 November 2026: derive it through the logic arm; it is the Fréchet
--| derivative of the operator the device is the inverse linearization of (declared).  What can be done here is the first
--| variation of each half of the action, in one link, at any field whatever.  Episode 12 did it at a flat field.

--| LIGHT.  Move one link of the lattice of turns by a turn.  Whatever the field, the action is what it was, and the move
--| by the first variations of the four squares, and the move squared by what was moved.  Nothing past the second order.

--| MATTER.  On the torus, move one link by a turn and carry the state back along it.

--| The current: the state at the near end, turned over, by the move, by the state at the far end.
def the_current_in_the_link {n : Nat} (state : Site4 n → Turns) (way : Direction) (x : Site4 n) (X : Turns) : Turns :=
  the_turns_product (the_turns_conjugate (state x)) (the_turns_product X (state (the_step way x)))

--| The state carried back is what it was, and the move by the current.  There is no second order: the state carried back
--| is straight in the link.

--| And the state against itself does not hold the link at all.
end the_two_first_variations


section the_equation_in_a_link
open readers_experience readers_interpretation_of_the_experience

--| THE EQUATION IN A LINK.  Both halves on the one torus.  Fix a link: a way and a site.  The squares that hold it are, for
--| each other way, the square ahead, standing on the link, and the square behind, with the link for its far side.  Move the
--| link by a turn.

--| The square ahead: the move goes in at the bottom.  The other way must be another way, and its step must leave the site.

--| The square behind: it stands one step back along the other way, and the move goes in at its far side.

--| THE ACTION AT THE LINK, for one other way: what the square ahead holds, what the square behind holds, and the whole part
--| of the state carried back.

--| What multiplies the move: the first variations of the two squares against the move carried round each, and the whole
--| part of the current.

--| With the link moved, the action at the link is what it was, the move by that, and the move squared by what the two
--| squares hold of the move.  Light and matter, one link, one expansion.

--| THE EQUATION.  The field stands still in the link when what multiplies the move is nothing, whatever the move: the two
--| squares' first variations against the move, and the current, are nothing together.  Then moving the link changes the
--| action only by the move squared.

end the_equation_in_a_link


section the_governing_equations_both_ways
open readers_experience readers_interpretation_of_the_experience the_table

--| THE GOVERNING EQUATIONS, BOTH WAYS.  The author's, 19 November 2026: derive the governing equations of the device both
--| ways, through the physics of an equivalation and through the logical proposal; the first demonstrates that quantum
--| mechanics works, and the second that the current thought of physics is deep in the representational weeds (declared).
--| The device has two equations.  One came through the Area: a source that reads as the curvature of an area along the
--| null directions is curvature, less the trace by the metric, and a constant by the metric.  The other came through the
--| closures: with a link moved, the action at the link is what it was, the move by what multiplies it, and the move squared.

--| Both hold.  Each was proved where it stands.

--| THROUGH THE LOGICAL PROPOSAL.  Ask only whether it is true.  Then the two equations are one: each is true, and two
--| truths are one truth.  Nothing of what either says is used.  This is the opening deal, dealt on the equations.

--| THROUGH THE PHYSICS.  Put an equation where the one-like holds its proposition, on the physics of the turns twice, and
--| read it as the device reads an equivalation.  Three facts come back, and they are the same three whichever equation was
--| put in.  The reader has the click.  It does not have what the equation says.


--| So read by the device, the two equations are not told apart; and asked only whether they are true, they are one.  What
--| tells them apart is what they say, and that is read by neither.
end the_governing_equations_both_ways


section the_vacuum_stands_still
open readers_experience readers_interpretation_of_the_experience

--| THE VACUUM STANDS STILL.  The author's, 19 November 2026: the vacuum is a list of truths (declared).  On the torus: the
--| whole turn on every link, and no state.  It meets the equation in the link: whatever the move, nothing multiplies it.
def the_whole_turn_on_every_link {n : Nat} : Torus4 n := fun _ _ => the_whole_turn 1
def no_state {n : Nat} : Site4 n → Turns := fun _ => (0, 0, 0, 0)

end the_vacuum_stands_still

section with_a_clock_on_it
open readers_experience

--| WITH A CLOCK ON IT.  The author's, 19 November 2026: the amplitude is one, on or off; put a clock on it and there is an
--| interference pattern, and that has an amplitude (declared).  A fact's click is on or off.  The table has two
--| crossings, eighteen and five.  Together they are twenty-three and apart they are thirteen, and the two squared differ
--| by the gap squared: four of the one by the other.

end with_a_clock_on_it

section three_lines_at_a_point
open readers_experience

--| THREE LINES AT A POINT.  The author's, 19 November 2026: the yarn theory's train schedules are Feynman's diagrams
--| (declared).  A yarn is made three ways.  By `stokes`: one path.  By `fibers`: two paths, and a yarn.  By `fabric`: three
--| paths, and two yarns.  Count the paths at the top of a yarn, and then down the first yarn it holds.

--| The device's coordinate system is three lines at a point, on two, on one.
end three_lines_at_a_point

section twenty_is_not_counted
open readers_experience

--| TWENTY IS NOT COUNTED.  The author's, 19 November 2026: twenty is the Lebesgue integral; it is the belief the knower is
--| asked to hold; twenty is the daisy (declared).  Among the running counts of the tapes, from the front and from the
--| back, and among the marks by length, twenty does not appear.  Its neighbours do.
end twenty_is_not_counted


section two_machines_up_to_the_daisy
open readers_experience readers_interpretation_of_the_experience

--| TWO MACHINES, UP TO THE DAISY.  The author's, 19 November 2026: there are two machines that are identical up to the
--| daisy, a × (−c × b) and −a × (c × −b) (declared).  In the turns, with the cross of two turns for ×.

--| The one is the other, owed.  One sign between them, and nothing else.

--| And read by the action, which does not see a sign, they are one.
end two_machines_up_to_the_daisy

section the_matters_own_variation
open readers_experience readers_interpretation_of_the_experience

--| THE MATTER'S OWN VARIATION.  The link was moved; now move the state, at one site, by a turn.

--| Moved at the far end of a link, the state carried back is what it was and the move by: the near state turned over, by
--| the link, by the move.  The step along the way must leave the site.

--| Moved at the near end: the move turned over, by the link, by the far state.

--| And the state against itself, which holds no link, is of the second order in the move: itself; the move by the state
--| against the move, both ways; and the move squared by the move against itself.

--| WHERE THERE IS NO LIGHT.  On the whole turn on every link, what multiplies the move of a link is the whole part of the
--| current and nothing else: there the field stands still exactly where there is no current.
end the_matters_own_variation

section the_equation_in_a_link_over_the_other_ways
open readers_experience readers_interpretation_of_the_experience

--| OVER THE OTHER WAYS.  A link is held by a square ahead and a square behind for each other way.  Take a list of other
--| ways, each with the site one step back along it, and add up.

def what_multiplies_the_move_of_the_squares {n : Nat} (U : Torus4 n) (way : Direction) (x : Site4 n) (X : Turns) :
    List (Direction × Site4 n) → Int
  | [] => 0
  | (other, behind) :: rest =>
      the_first_variation_of_the_turns (the_square4 U way other x)
          (the_turns_holonomy X (U other (the_step way x)) (U way (the_step other x)) (U other x))
        + the_first_variation_of_the_turns (the_square4 U other way behind)
          (the_turns_holonomy (U other behind) X (U other (the_step way behind)) (U way behind))
        + what_multiplies_the_move_of_the_squares U way x X rest


--| Every other way in the list is another way, steps off the site, and has its square behind one step back and elsewhere.

--| All the squares at the link, with the link moved: what they held, the move by what multiplies it, the move squared.

--| THE EQUATION, OVER THE OTHER WAYS.  With the state carried back along the link as well: where the squares' first
--| variations and the whole part of the current are nothing together, for every move, the move enters only squared.
end the_equation_in_a_link_over_the_other_ways

section the_second_variation_stops
open «springer-verlag» THE_GOSPEL the_representation assembly_instructions readers_experience the_table
attribute [local instance high] rung01 rung02 rung03 rung04 rung05 rung06 rung07 rung08 rung09 rung10 rung11 rung12 rung13 rung14 rung15
  rung16 rung17 rung18 rung19 rung20 rung21 rung22 rung23 rung24 rung25 rung26 rung27 rung28 rung29 rung32 rung33 rung34 rung35 a_truth_about_the_experience

--| THE SECOND VARIATION STOPS.  In the closure's own order the first closure is not under the second: its option holds and
--| the second's cannot, and the order asks that the one imply the other.  True on false does not go.
end the_second_variation_stops


section the_carriers_step_five_times
open «springer-verlag» THE_GOSPEL the_representation assembly_instructions readers_experience the_table

--| THE CARRIER'S STEP, FIVE TIMES.  The author's, 19 November 2026: `INFERRED` is the matter's interface, and should have
--| the result in the place it is needed; because this is 3SAT, one solution is enough; and the repeated value and the
--| residue of the carrier's step, taken five times from the zero on the same difference, should answer it (declared).

--| What a number stands on: the fact at its top.

--| Once, the step sets the zero on the truth.  Five times, it is where once left it.  The repeated value is the zero on
--| the truth.

--| The residue: what it stood on before, and no longer.  One cell before and one after; the same difference under it
--| before, and the truth after.

--| Asked only whether it is true, there was nothing to step: the same difference holds, the truth holds, and two truths
--| are one.  So the quantum was the repeated value already.

--| IN THE PLACE IT IS NEEDED.  The knower's α, the closure `INFERRED` holds, is an inferred closure, and it begins on the
--| truth twice: the fact the step repeats.

--| THE STEP IS A PROJECTION.  The author's, 23 November 2026: the bottom carrier's `interact_with_the_universe` from three
--| deep, done five times, is Voltron; Atreyu rides the black cat, keyed to its pilot; how the cats join up is the transition
--| matrix; Voltron makes you nice in the Krylov subspace, so you get presents; forcing comes from the norm computation
--| (declared).  What is checked: on every number, not only the quantum, the step taken twice is the step once, so five
--| times is once.  A zero goes to the zero on the truth.  A one keeps its glue and takes the carrier's own quarter: the
--| step is keyed to its carrier.  It keeps the kind, a zero to a zero and a one to a one.  No card the device deals writes
--| its own step, so every one has the device's: a carrier of a proposition, of a fact, the card between, a card three
--| deep, and the carrier process at the bottom of the last machine.  One card below writes its own, only to show that the
--| projection is the device's step and not every carrier's.

--| A carrier may write its own step: the device's is only the default.  So these are said of a card that leaves the step
--| to the device, as every card in the device does, whatever its box, symbol and quarter.





--| The kind is kept: the transition on the two kinds, a zero and a one, is the same, and only what a one carries is
--| replaced.  Read as a matrix on the two kinds, that is the identity; read on what is carried, it is a projection.


--| And it need not be so.  A card that writes its own step, one that puts a one on every zero, does not keep the kind.

end the_carriers_step_five_times


section the_matters_equation
open readers_experience readers_interpretation_of_the_experience

--| THE MATTER'S EQUATION.  The link's equation said what multiplies the move of a link.  Now the state's.  At a site, take
--| the whole part of the state carried back along one link, and the whole part of the state against itself, and move
--| the state there by a turn.

def what_multiplies_the_move_of_the_state {n : Nat} (state : Site4 n → Turns) (U : Torus4 n) (way : Direction) (x : Site4 n)
    (Y : Turns) : Int :=
  (the_turns_product (the_turns_conjugate Y) (the_turns_product (U way x) (state (the_step way x)))).1
    + (the_turns_product (the_turns_conjugate (state x)) Y).1 + (the_turns_product (the_turns_conjugate Y) (state x)).1

--| With the state moved: what it was; the move by the move turned over against the far state through the link, and against
--| the state both ways; and the move squared by the move against itself.

--| THE EQUATION, for the state: it stands still at the site when nothing multiplies its move, whatever the move.
def the_state_stands_still_at_the_site {n : Nat} (state : Site4 n → Turns) (U : Torus4 n) (way : Direction) (x : Site4 n) : Prop :=
  ∀ Y : Turns, what_multiplies_the_move_of_the_state state U way x Y = 0

--| No state stands still, on any links.  So the vacuum meets both equations.

--| And the vacuum meets the link's equation over every other way.
end the_matters_equation

section the_phrases_as_one_number
open readers_experience the_table the_table.Account

--| THE PHRASES AS ONE NUMBER.  The author's, 19 November 2026: the word is its name; thirty-two inferred bits; the
--| solution will be the integer that is the number on the device (declared).  The device has thirty-two phrases, two for
--| each of its sixteen steps.  Write one mark for each, whether the phrase says something true, in the device's own order
--| with the first step's first phrase highest, and read the marks as one number.  The order is a choice.


--| The number, and its four eights: the first and the last are one eight, and the two between are another.
end the_phrases_as_one_number

section the_gateaux_derivative_and_the_weak_form
open readers_experience


--| THE PHASE MUST BE INFERRED.  The author's, 23 November 2026: the phase of the nowtrino must be inferred, or the carrier
--| of a carrier's step (declared).  What is checked: the norm does not read which way a turning goes, so no reader of the
--| norm returns the point; and the card between's step forgets what a number carried, so no reader of the stepped number
--| returns it.  Both are the recovery obstruction, on two cases kept alike and identified apart.



--| THE DERIVATIVE, ONE THING.  If a linear part leaves a multiple of the step squared at every step, it is the slope.

--| THE GATEAUX DERIVATIVE.  Along a line through v in the direction h, an action is what it was, the step by its Gateaux
--| derivative, and the step squared by the action of the direction, exactly.  The Gateaux derivative is the one linear part
--| that does that at every step: one step forward and one back fix it.



--| THE WEAK FORM IS THE STRONG FORM.  On two coins the test functions are the trial functions and are everything: a
--| residual that reads nothing against every direction is nothing.  So the Galerkin condition, met, is the equation met.

--| AND AT THE ROOT IT IS MET.  In the pairs, the table carries the direction up to the outer radius times itself, coin by
--| coin: the table less its root leaves that direction with nothing, so the Galerkin condition is met there exactly.  The
--| author's, 23 November 2026: the Gateaux derivative should finish the finite element construction (declared).
end the_gateaux_derivative_and_the_weak_form

section a_native_implementation_or_the_device
open readers_experience the_table the_table.Account

--| A NATIVE IMPLEMENTATION OR THE DEVICE.  The author's, 23 November 2026: show that the math needed to compute Card 3's
--| Navier-Stokes exists so that Lean cannot tell a native implementation from the device (declared).  What is checked.
--| A formula of whole numbers is built from places, whole numbers, beside, less and each for each.  Evaluated on the
--| device's Accounts and read by the balance, or evaluated on Lean's own integers, it is one number, for every formula and
--| every filling of its places.  So no reader of the number can tell which way it was computed.  Card 3's momentum residual
--| on a periodic row, and its response action, which is cubic, are such formulas.
inductive Formula where
  | place : Nat → Formula
  | whole : Int → Formula
  | beside : Formula → Formula → Formula
  | less : Formula → Formula → Formula
  | eachForEach : Formula → Formula → Formula





--| CARD 3'S RESIDUAL AND ACTION ON A PERIODIC ROW.  Places: 0 the velocity here, 1 ahead, 2 behind, 3 the velocity one
--| step on, 4 the pressure ahead, 5 behind, 6 the force, 7 the viscosity, 8 the response velocity, 9 the response pressure.
--| The residual: the step, less viscosity by the second difference, the velocity by its central difference, the pressure's
--| central difference, less the force.  The action: the response velocity by the residual, and the response pressure by
--| the velocity's central difference.  Each for each three deep: cubic.



--| ONE GLYPH.  Episode 5: to be the SAME is that there is but one glyph to represent the concept.  The native computation and
--| the device's, of Card 3's action, as a FACT: its truth is that the two are one integer, its click decides it, and it holds.
--| A fact that holds is the truth itself: one glyph.

end a_native_implementation_or_the_device

section the_quartic_in_disguise
open readers_experience

--| THE DERIVATIVE IS THE QUARTIC IN DISGUISE.  The author's, 23 November 2026 (declared).  The quartic the epilogue writes,
--| t squared by c less t by x squared, less two c t r squared x, and c r to the fourth, is linear in c, quadratic in x, cubic
--| in t and quartic in r.  Write t x for one number and r squared for another and it is a form of two: c less t of the first
--| squared, less two c of the two, and c of the second squared.  At the device's weights, eighteen and five, that form is the
--| residual of the pair: thirteen, thirty-six and eighteen.  The residual of the pair is a thirteenth of the determinant of
--| the table taken from the same (`its_determinant_is_thirteen_residuals`).  Step the pair's first number and the form steps
--| by the step times the trace of that table's adjugate and thirteen by the step squared, exactly; and the trace of the
--| adjugate is the residual's slope (`the_trace_of_its_adjugate_is_the_slope`).  So the quartic's first variation in x is
--| five times the slope, with three hundred and twenty-five by the step squared over: the derivative, read off the quartic.






end the_quartic_in_disguise

section the_taylor_series_the_frechet_derivative_and_least_action
open readers_experience


--| 1. THE TAYLOR SERIES, EXPLICIT.  Episode 8 names the bent card the exact Taylor series degree.  A cubic's Taylor series
--| about any place is exact in four terms, and the residual's stops at its third, whose coefficient is that degree.



--| 2. THE FRECHET DERIVATIVE, INFERRED.  The action of the weighed table, moved by a direction, is what it was, the linear
--| part, and the action of the direction.  That last is never negative and never past twenty-eight by the weighed square of
--| the direction, in every direction at once: the remainder is bounded by the norm.  Bounding every direction at once is
--| what is inferred.  And the linear part is linear in the direction.





--| 3. THE GATEAUX DERIVATIVE, THE EXPLICIT OF THE INFERRED.  Along a line, step by step, the action moves by the Frechet
--| derivative of the step in that direction and the step squared by the action of the direction.



--| 4. LEAST ACTION, THE COVARIANT READING.  Over the weighed square the action is never past twenty-eight, and one pair
--| passes twenty-seven; in the pairs the direction up gives exactly the outer radius times its weighed square.  The least
--| number the action never passes is eighteen and the root of ninety, and the direction up is where it is reached: there
--| the action less that number is stationary, which is the weak form met at the root, above.


--| 5. AND THE CONTRAVARIANT READING.  The table is its part that is the same turned over, which the action reads, and its
--| part that is owed turned over, which is the bent card by the quarter turn
--| (`the_table_less_itself_turned_over_is_the_bent_card_by_the_quarter_turn`) and which no action reads.  The author's, 23
--| November 2026 (declared): least action is the covariant reading of the inferred inferred device, and QED the
--| contravariant; build it in this order.  What is checked is the split and the readings of the first part; that the
--| second part is QED is the author's.
end the_taylor_series_the_frechet_derivative_and_least_action

section two_first_variations_crossed
open readers_experience

--| TWO FIRST VARIATIONS CROSSED ARE THE SECOND.  The author's, 23 November 2026: thirteen, fourteen, fifteen as the first
--| variation; three, four as the other; combined they make the second variation, the cross product (declared).  What is
--| checked: a steady row, a start and a step, is a first variation held at three places.  Two steady rows crossed, in the
--| turns, give the second difference, one, two owed, one, by the cross of their starts and steps; thirteen, fourteen,
--| fifteen across three, four, five is ten of it.  The steady rows fill a plane, and the second difference is the one
--| direction that reads nothing on every steady row: the cross product is that direction.  And the second difference
--| taken twice is one, four owed, six, four owed, one: the fourth difference, the beam's stencil.

--| A steady row: a start and a step, three places.



--| The second difference reads nothing on a steady row.


--| THE TRIPLE.  The author's, 23 November 2026: in a·(c×b), a is the vector derivative, c the completed Frechet derivative
--| and b the inferred phase (declared).  What is checked: with c and b two steady rows, first variations, a row read
--| against their cross is the cross of their starts and steps times the row's second difference.  So the triple is nothing
--| exactly where the row has no second variation, and three first variations make nothing.


--| INTEGRATED, THE CROSS GIVES BACK THE FIRST VARIATIONS.  The author's, 23 November 2026: integrate and back out the
--| variational cross product (declared).  The second difference summed along a row is the first difference at its end
--| less the first difference at its start: what the cross reads, added up, is the two first variations at the ends.
end two_first_variations_crossed

section the_convergence_is_exact
open readers_experience

--| THE CONVERGENCE IS EXACT.  The author's, 23 November 2026: the second variation is the Frechet variation, and it should
--| show the convergence is exact (declared).  What is checked.  Write the distance of a pair from each root as a whole part
--| and a part by the root of the round trip: thirteen of the first less eighteen of the second, and the second owed or
--| held.  One turn of the crank squares each distance, exactly, in the pairs: the second variation is all that is left, and
--| it is the square.  So after any number of turns the distance is the first distance squared that many times, its power
--| two to the turns, for every number of turns and with nothing estimated.  The only fact used about the numbers is that
--| the round trip, ninety, is eighteen squared less thirteen by eighteen: half the trace squared less the coefficient by
--| the memory.  Which root the crank goes to is the one whose distance is the smaller to begin with; that comparison needs
--| the size of the root of ninety, and the device leaves it to the reader.  This is the induction Card 3 does on the page.

--| A turn of the crank on a pair, for a residual c N² − 2t N D + m D².
--| The distance to each root, as a whole part and a part by the root of the round trip.







end the_convergence_is_exact

section continuity_and_the_choice
open readers_experience

--| CONTINUITY, AND WHERE THE CHOICE IS.  The author's, 23 November 2026: once there are reals, continuous is next, and that
--| is the choice (declared).  What is checked.  Continuity as a statement, for every k some m, is not yet a modulus, a
--| function giving the m.  Where whether an m serves is a FACT, its click lets the least m be found by looking, and the
--| modulus comes with no axiom at all.  Where it is a bare statement, the same theorem is handed a click by choice, and
--| bills it.  The reals Meanings builds carry their moduli already, which is why nothing in them needed choice.
theorem a_modulus_from_facts (serves : Nat → Nat → FACT) (continuous : ∀ k, ∃ m, (serves k m).truth) :
    ∃ modulus : Nat → Nat, ∀ k, (serves k (modulus k)).truth ∧ ∀ m, m < modulus k → ¬ (serves k m).truth :=
  @Meanings.a_modulus_with_the_click (fun k m => (serves k m).truth) (fun k m => (serves k m).click) continuous

end continuity_and_the_choice

section the_roots_direction
open readers_experience

--| THE ROOT'S DIRECTION.  Which root the crank goes to.  The two roots stand either side of the vertex, eighteen over
--| thirteen, half their sum.  One turn squares the residual of the pair, by thirteen: after any turn it is never under
--| nothing, so the pair is never under the upper root.  One turn keeps the pair past the vertex, since thirteen of the
--| first less eighteen of the second becomes that squared and ninety of the second squared.  And above the root a turn
--| moves the pair down by the second by the residual.  Episode 8's crank starts at the house, five hundred and thirty over
--| three hundred and twenty-four: past the vertex and under the upper root.  So the first turn throws it over the upper
--| root, and from there every turn falls toward it and none crosses the vertex.  The lower root is never reached: it is
--| on the other side of the vertex.  That the falling pairs come to the upper root and not to something above it is the
--| exact squaring of the distance, above; that it comes all the way is a limit, and the limit is the reader's.





--| The upper side: the second more than nothing, and the place past the vertex, eighteen over thirteen.





--| FROM THE HOUSE.  Episode 8's crank starts at the house, five hundred and thirty over three hundred and twenty-four.



end the_roots_direction

section the_limit_as_the_devices_own
open readers_experience

--| THE LIMIT, AS THE DEVICE'S OWN.  The author's, 23 November 2026: the limit (declared, as the next step).  What is
--| checked.  From the house's first turn, the crank's distance to the upper root is a whole part and a part by the root of
--| ninety, both whole numbers, and each turn takes them to the first squared and ninety of the second squared, and twice
--| their product.  The whole part over the other is never under the root of ninety, and ninety over it never above: a
--| bracket.  The gap, the whole part squared less ninety of the other squared, squares each turn, and against the two
--| parts' product it at least halves.  Taken four turns on, at every stage the bracket is no wider than one part in the
--| stage and one: the crank's brackets are a real, with no choice.  And they are the same real as the halving's root of
--| ninety, at every pair of stages: the crank and the bisection name one number.  The limit the crank goes to is not handed
--| in; it is this real.  That the bracket is a number on a line is still the reader's.

--| The crank's distance to the upper root, in naturals: a whole part and a part owed by the root, after the first turn.
















--| THE ROOT OF NINETY, BY THE CRANK.  Below: ninety by the second over the first; above: the first over the second.

end the_limit_as_the_devices_own

section the_printed_number_as_a_real
open readers_experience

--| THE PRINTED NUMBER, AS A REAL.  The author's, 23 November 2026: "since we have the jar at compile, the next is h->0"
--| (declared).  What is checked.  The number Episode 8 prints is, in closed form, three hundred and twenty-four sixty-fifths
--| of eighteen and the root of ninety.  Here it is a real with no choice: the fraction as a real, by eighteen as a real beside
--| the crank's own root of ninety.  It is a real by construction, so at the n-th stage its bracket is no wider than one part
--| in n and one: that is the step going to nothing, and the compile is what provides it.  And at every stage both walls are
--| inside the jar, eight thousand nine hundred and five sixty-fifths (the natural read, a hundred and thirty-seven) and eight
--| thousand nine hundred and thirty-four sixty-fifths (that and the twenty-nine).  The walls of the product are not read off:
--| the product reads its factors as far on as their first high wall is tall, and that is more turns of the crank than can be
--| turned.  So the jar is shown at every stage from two things: the crank's walls never move outward, and at its first stage,
--| four turns on, the kernel decides that the product of the walls is inside.  And by the laws it is one with the halving's
--| norm, by the same fraction.  That the bracket is a number on a line is still the reader's.

--| A FRACTION, AS A REAL, BY EIGHTEEN AND THE CRANK'S ROOT.

--| THE STEP GOES TO NOTHING.  At the n-th stage the high wall is past the low by no more than one part in n and one.

--| The crank's walls never move outward: every low wall is past the first, every high wall under it.


--| THE WALLS OF THE JAR, as fractions over sixty-five.
def the_jars_low_wall : Meanings.Fraction := ⟨8905, 65, by decide⟩
def the_jars_high_wall : Meanings.Fraction := ⟨8934, 65, by decide⟩

--| At the crank's first stage, four turns on, the product of the walls is inside the jar: decided by the kernel.

--| THE LOW WALL IS NEVER UNDER THE JAR, at any stage.

--| THE HIGH WALL IS NEVER OVER THE JAR, at any stage.

--| AT EVERY STAGE, INSIDE THE JAR AND NARROWING.
--| ONE WITH THE HALVING'S.  The laws say the sum and the product keep being one.  Eighteen beside the halving's root of
--| ninety is the halving's norm; the crank's root is the halving's; so the printed number as a real is one with three
--| hundred and twenty-four sixty-fifths of the halving's norm, at every pair of stages.  Two processes, the crank and the
--| bisection, and one real.


--| THE PRINTED DIGITS ARE THE REAL'S FLOOR.  Episode 8 prints twenty-seven digits, twenty-four past the point.  At every
--| stage the real lies between those digits and those digits and one in the last place: its low wall is never past the one
--| and its high wall never under the other.  So the digits are the real's floor at the twenty-fourth place, at every stage,
--| not at one.  No root is taken: every low wall of the crank's root of ninety is under any fraction whose square is past
--| ninety, and every high wall past any fraction whose square is under it.


--| The digits, and the digits and one in the last place, over the scale.

--| What the root of ninety must be not past, and not under, for the fraction by eighteen and it to be the digits.



--| AT EVERY STAGE THE REAL IS BETWEEN THE DIGITS AND THE DIGITS AND ONE.
end the_printed_number_as_a_real

section the_lower_root_as_a_real
open readers_experience

--| THE LOWER ROOT, OVER.  With the reciprocal (Meanings, `Bracketed.reciprocal`), what the naturals could not write and the
--| signed reals wrote with the root owed is written held: the table's lower root is its determinant, two hundred and
--| thirty-four, over its norm, eighteen and the root of ninety.  The norm is past nothing at the tenth stage, and that stage
--| is handed in; nothing is found by choice.  What is checked: the norm by this real is two hundred and thirty-four at every
--| pair of stages, the two roots multiplying to the determinant; and three hundred and twenty-four sixty-fifths of it has
--| both walls inside the other root's jar, two thousand seven hundred and thirty sixty-fifths (the natural inferred, forty-two)
--| and two thousand seven hundred and fifty-nine sixty-fifths (that and the twenty-nine), at every stage.  The walls are not
--| read off; one over reads the norm far on, so the jar is shown from the walls at the tenth stage, decided by the kernel,
--| and the walls of one over never moving outward of them.



--| THE TWO ROOTS MULTIPLY TO THE DETERMINANT.

--| THE OTHER ROOT, PRINTED: three hundred and twenty-four sixty-fifths of the lower root.

def the_other_jars_low_wall : Meanings.Fraction := ⟨2730, 65, by decide⟩
def the_other_jars_high_wall : Meanings.Fraction := ⟨2759, 65, by decide⟩

--| At the tenth stage of the norm, one over its walls, by two hundred and thirty-four and the fraction, is inside the jar.



--| EIGHTEEN LESS THE ROOT.  With the difference (Meanings, `Bracketed.difference`), the lower root is also eighteen less the
--| root of ninety, the root's high wall at the first stage, ten, not past eighteen.  By the laws it is the same real as the
--| determinant over the norm: eighteen less the root by eighteen and the root is three hundred and twenty-four less ninety,
--| two hundred and thirty-four, the root by itself being ninety and what is beside both sides taken away.  So the signed
--| reals' lower root, eighteen held and the root owed, is one with the determinant over the norm, held.




--| EIGHTEEN LESS THE ROOT IS THE DETERMINANT OVER THE NORM.

--| THE SIGNED REALS' LOWER ROOT, EIGHTEEN HELD AND THE ROOT OWED, IS THE DETERMINANT OVER THE NORM, HELD.
end the_lower_root_as_a_real

section the_turned_root_over
open readers_experience

--| ONE OVER THE TURNED ROOT.  The table turned over has the roots eighteen and the root of ninety across, held or owed
--| (Meanings, `theTurnedRoot`, `theOtherTurnedRoot`).  With one over a complex number (Meanings, `ComplexReal.reciprocal`):
--| the turned root's norm squared, eighteen by eighteen beside the root by itself, is four hundred and fourteen, the turned
--| table's determinant; so the two turned roots multiply to the determinant, as the two roots of the table do to theirs; and
--| one over the turned root is the other turned root over four hundred and fourteen.  The norm squared is handed in held past
--| owed at the first stage, decided by the kernel.


--| THE TWO TURNED ROOTS MULTIPLY TO THE TURNED TABLE'S DETERMINANT.




--| ONE OVER THE TURNED ROOT IS THE OTHER TURNED ROOT OVER THE DETERMINANT.
end the_turned_root_over

section one_over_a_quarter_turn
open readers_experience

--| ONE OVER A QUARTER TURN IS THE TURN OWED.  With one over a quaternion (Meanings, `QuaternionReal.reciprocal`): each of
--| the three quarter turns, by itself, is one owed (Meanings, `i_twice_is_one_owed` and the others); so a turn by the turn
--| owed is one, and, one over being one thing, the turn owed is one over the turn.  Each turn's norm squared is handed in
--| past nothing at the first stage, decided by the kernel.




end one_over_a_quarter_turn

section the_step_angle
open readers_experience

--| dθ.  The author's, 23 November 2026: "you should be able to get dθ now" (declared).  The device's turning walk steps by
--| n and the quarter phase, (n, 1), at the card's thickness of one part in n (section `the_first_variation_of_the_exponential`).
--| The angle of that step is the arctangent of one part in n, which is now a real with no choice: dθ.  What is checked: dθ is
--| at every stage between one part in n less a third of the step cubed and one part in n; so the step turns by less than it
--| is long, short by the step cubed over three, where its radius was long by the step squared.  And Machin's formula, which
--| the half turn is written by, is on the device's own turns: four steps of (5, 1) and one step back of (239, 1) land exactly
--| on the eighth turn, 114244 by (1, 1), in the Gaussian product.  That the arctangent of one part in n is the angle of
--| (n, 1) is standard; the device has no angle function, and the identity is on the turns, not on the angles.


--| dθ IS BETWEEN THE STEP LESS A THIRD OF ITS CUBE AND THE STEP, at every stage.

--| The step, and a third of its cube: one part in n, and one part in three n cubed.

--| dθ AT A FIFTH: under 0.19740 at every stage, and past 0.19739 from the first stage on (at the stage before, the low
--| wall is only the step less a third of its cube, 0.19733).

--| MACHIN ON THE TURNS.  Four steps of (5, 1), and one step back of (239, 1), are 114244 by the eighth turn (1, 1).

--| And the half turn is written with these two step angles: sixteen of the one, less four of the other.
end the_step_angle

section the_linear_reading_of_the_turn
open readers_experience

--| THE LINEAR READING OF THE TURN.  The author's, 23 November 2026: show that the bracket on the real for sine and cosine is
--| the same and the convergent number is the same, but the number is wrong (declared).  As read here: the turns are one
--| object whichever way their angle is read.  A step (n, 1) has the same sine and cosine whether its angle is taken as the
--| step itself, one part in n, the linear reading, Newton's, or as the arctangent of one part in n, the series; and four
--| steps of (5, 1) and one back of (239, 1) land on the eighth turn exactly, in the Gaussian product, which reads no angle
--| (`four_steps_of_a_fifth_and_one_back_of_239_are_the_eighth_turn`).  What differs is the number read off.  Read linearly,
--| the half turn is sixteen fifths less four in two hundred and thirty-nine, 3804/1195; at every stage it is past the series'
--| half turn by between 0.04167 and 0.04168.  The two readings agree to the first order in each step and part at the third
--| (`the_step_angle_is_between`).  The miss is measured against the series, from outside the linear reading.



--| THE NUMBER IS WRONG: the linear half turn is past the series' half turn by between 0.04167 and 0.04168, at every stage.

--| And the eighth turn read linearly, four fifths less one in two hundred and thirty-nine, is the same object as four steps
--| and one back: the steps are the same, their angles read two ways.

--| THE MISS SQUARED.  The author's: square the miss using multiplication, and a very interesting number is found (declared).
--| The miss as a real, the linear half turn less the series' half turn, and its square by the product.  At every stage the
--| square lies between 0.0017364676352 and 0.0017364676361; and it is past one in five hundred and seventy-six, one over
--| twenty-four squared, by between 2.0535 and 2.0536 parts in ten thousand of it.  Twenty-four is four factorial, the
--| fourth term's denominator.  The walls are not read off the product, which reads far on; they come from the half turn's
--| walls and the order.







--| THE MISS SQUARED IS JUST PAST ONE OVER TWENTY-FOUR SQUARED, at every stage.
end the_linear_reading_of_the_turn

section the_branch_never_taken
open readers_experience


--| THE BRANCH NEVER TAKEN.  Claude's, taken up by the author ("run with your idea"): the linear reading keeps each step's
--| first term; what it drops, the cube over three and on, is a real (Meanings, `theBranchNeverTaken`), and the angle beside
--| it is the step (`the_angle_beside_the_branch_never_taken_is_the_step`).  So the miss is exactly the branch the linear
--| reading never takes: the linear half turn less the series' is one with sixteen branches at a fifth less four at one in
--| two hundred and thirty-nine, at every stage; and the miss squared, past one over twenty-four squared, is that branch
--| squared.  The gap is carried wholly by the terms the linear reading drops.  That this branch is (F=T) = (T=F), the
--| author's branch never taken, is the author's.



--| THE BRANCH OF THE HALF TURN: sixteen branches at a fifth less four at one in two hundred and thirty-nine.





--| THE MISS IS THE BRANCH NEVER TAKEN, at every stage.

--| AND THE MISS SQUARED IS THE BRANCH SQUARED.

--| HOW IT CLICKS AGAINST THE FIRST SAME DIFFERENCE.  The author's: check by seeing how it clicks against the first
--| SAME_DIFFERENCE (declared).  The branch never taken, compiled, is a fact; it clicks, as same difference clicks; so the two
--| are one account by the click (Episode 12's `same_click`), and, both true, one fact.  Say with it what the check cannot
--| tell: any true fact clicks alike and is one with any other by extensionality; this is the opening deal, the same if asked
--| whether it is true.  And how each clicks differs: same difference's click is decided, its four cells read; the branch's
--| click at every stage is handed in by the compile, since sameness at every stage is decided at no finite stage.  At one
--| pair of stages it is decided: at the first stages the two brackets hold each other, read by the kernel.




end the_branch_never_taken

section the_order_through_the_missing_branch
open readers_experience

--| THE ORDER THROUGH THE MISSING BRANCH.  The author's: this should be the logic of the contravariant contravariant ≤, the
--| crank and the inferred click (declared).  What the device's order does, read in Episode 1: ≤ on a Natural has two arms,
--| the covariant, when the two facts have one truth, comparing the numbers as they are, and the contravariant, when the
--| truths differ, comparing them the other way round, "the missing branch".  Two contravariant steps do not give the order
--| back: they give it turned over.  A natural true and larger is under one false and smaller, that one is under one true and
--| smaller, and the first is not under the last.  So the device's order is not transitive across two truths, and the path
--| that fails is exactly the one through the missing branch twice.  No axiom.  In Meanings two turnings over do give the
--| order back (one over twice is the fraction; a thing taken away twice is added); here they do not.  That this is the logic
--| of the three is the author's.





--| THE ORDER IS NOT TRANSITIVE ACROSS TWO TRUTHS: through the missing branch twice, it is turned over.
end the_order_through_the_missing_branch

section the_turn_through_its_norm
open readers_experience

--| THE TURN THROUGH ITS NORM.  The author's: doesn't the norm compute this; go as far as you can (declared).  It does, for
--| every turn with whole-number parts, or parts whose squares are whole: the norm squared is a whole number, the radius its
--| root by halving, and cosine and sine the parts over the radius (Meanings, `Turns`).  So: the turned root, eighteen along
--| and the root of ninety across, has radius the root of four hundred and fourteen, cosine squared 18/23 and sine squared
--| 5/23, on the circle, and is its radius by its turn.  Machin's four steps and one back, 114244 along and across, read
--| through its norm has cosine squared one half: the eighth turn, as a turn, with no angle read.  The steps (5, 1) and
--| (239, 1) are on the circle.  What the norm does not give is any of these angles as a number.





--| THE TURNED ROOT IS ON THE CIRCLE.

--| ITS COSINE SQUARED IS 18/23 AND ITS SINE SQUARED 5/23: the two weights over their sum.


--| THE TURNED ROOT IS ITS RADIUS BY ITS TURN: the radius by the cosine is eighteen, by the sine the root of ninety.

--| MACHIN'S TURN, THROUGH ITS NORM.  Four steps of (5, 1) and one back of (239, 1) are 114244 along and across; the norm
--| squared is twice 114244 squared; read through it, the cosine squared is one half: the eighth turn.




--| AND THE TWO STEPS MACHIN USES ARE ON THE CIRCLE.

--| THE STEP AT A FIFTH, DOUBLED.  With the addition law for turns read through their norms (Meanings, `the_turns_add`): the
--| step (5, 1) by itself is (24, 10), whose norm squared is 676, twenty-six squared; its radius is the step's radius squared,
--| twenty-six; its cosine, by the law, beside the step's sine squared is the step's cosine squared, and is twelve thirteenths;
--| its sine is the two crossed products, and is five thirteenths.  The step doubled is the five, twelve, thirteen triangle.




--| THE STEP DOUBLED IS THE FIVE, TWELVE, THIRTEEN TURN: cosine twelve thirteenths, sine five thirteenths.

--| MACHIN'S EIGHTH TURN, BY THE SIGNED LAW.  Four steps of (5, 1) are (476, 480), radius exactly 676; the step back is
--| (239, −1), its across owed.  By the signed addition law for turns (Meanings, `the_signed_turns_add`), read at the product
--| of their radii: the cosine of the product is 114244 held, the sine 114720 held and 476 owed, and the two are one: the
--| eighth turn, cosine equal to sine, with the step back's sine owed.




--| COSINE AND SINE ARE ONE: the eighth turn.
end the_turn_through_its_norm

section three_models_of_one_root
open readers_experience

--| THREE MODELS OF ONE ROOT.  The author's: see the multigrid Jacobian-free Newton-Krylov solver as three different models
--| (declared).  The device's root of the table, eighteen and the root of ninety, is now reached three ways, each a real
--| with no choice: by halving (`Meanings.theNorm`, a level gained each stage, a bit at a time: the multigrid); by the crank
--| (`the_root_by_the_crank`, the distance squared at every turn: Newton); and by the table itself, turned on a vector again
--| and again (the power walk, here: the Krylov space of the table, the walls closing by about the ratio of the two roots,
--| 0.31, a step).  The power walk's walls are the table's two rows read against the vector, and the gap between them is
--| thirteen times 234 to the step, while the vector grows at least as 414 to the step.  The three are one real, at every pair
--| of stages.  What tells them apart is the rate, not the value.

--| THE POWER WALK: the table ((18, 5), (18, 18)) on (1, 1), again and again.


--| Two rows on a vector, multiplied, with letters for the coefficients.


--| The walk stays on the near side of the root's direction: five of the across squared not past eighteen of the along squared.







--| One step of the walk turns the across over the along up, never down.



--| The low wall, eighteen and five of the across over the along, rises; the high, eighteen and eighteen of the along over the
--| across, falls; both over any number of steps.




--| THE ROOT BY THE TABLE'S OWN POWERS: at stage n, the walk five and twice n steps on.

--| THE THREE ARE ONE.  The table's powers and the halving's norm are one real; and the crank's root with eighteen is the
--| halving's norm; so all three are one, at every pair of stages.

end three_models_of_one_root

section the_turn_by_a_rational_angle
open readers_experience

--| THE TURN BY A RATIONAL ANGLE.  The author's, 23 November 2026: after the quaternions, the exponentials, r and θ both
--| rationals (declared).  What is checked.  For an angle p over q, not past one, cosine and sine are reals with no choice,
--| each the alternating series of its powers, and the turn by that angle is cosine along and sine across.  At the third
--| stage, at the angle one and at a half, cosine squared and sine squared beside each other hold one: the turn stays on the
--| circle, to the stage.  With a rational r beside it, r and θ are both rationals, and the number they make is r times this.


--| ON THE CIRCLE AT EVERY STAGE.  For every angle p over q not past one, cosine squared beside sine squared is one, at
--| every pair of stages: not a reading at one stage but a statement about all of them.  Read on the coefficients, the
--| first variation is a shift, and cosine squared beside sine squared moves only by what the cut-off leaves: an
--| alternating series of falling terms, never under nothing, owed at the low walls and held at the high.

--| THE EIGHTH TURN, BY THE SERIES, AND WHAT EACH SIDE MISSES.  The author's, 24 November 2026: the approximation of the
--| half turn will have an error, and that error is the gap that must exist (declared).  What is checked.  Fifteen places
--| below the eighth turn the series cosine is past the series sine; fifteen places above, the sine is past the cosine; so
--| the two series cross between, with no turn and no arctangent used.  Machin's half turn lies at every stage between four
--| times the one and four times the other.  And at each of the two angles the difference of cosine and sine is a real
--| past nothing at every stage: neither approximation is the crossing.  That no rational angle is (Lambert) is standard
--| and not proved; an equality would show at no finite stage.

--| THE SLIP, AND THE COIN FLIP TURNED OVER.  The author's, 24 November 2026: this is the obvious slip, the law of static
--| friction and the photoelectric effect, and the contravariant coin flip; the slip of the Borwein process is such a slip;
--| out of reach, yet comparable, is the important thing (declared).  What is checked.  Below the crossing no sign can be
--| read before the fourth stage and from it the sign holds for good; above, from the third; found by looking, with the
--| click and no choice.  Once parted, the difference one way leaves something and the other way nothing, turned over
--| across the crossing.  The error below is under the error above at every pair of stages, though neither is computed.
--| And the Borwein threshold: one third through one thirteenth is under one, through one fifteenth past it.  The
--| integrals that slip there are standard and are not here.

--| HALVING, AND ITS ARROW.  The author's, 24 November 2026: halving is not circular, its reciprocal is, and that is the
--| baker's transform; and this maps to what we call the arrow of time (declared).  What is checked.  Handed the gap (that
--| at every halving's midpoint the two series part at some stage, which is not proved here), the eighth turn found a bit
--| at a time is a real with no choice, and whatever gap was handed, its first twelve halvings give 3216 over 4096.  The
--| cut after, halved, is the cut before, with nothing handed in; the record never falls; both next bits halve to the same
--| cut, so the past does not give the bit after; and doubling, the reciprocal, wraps round and forgets the top bit.

--| THE OTHER ONE: THE BAKER.  The author's, 24 November 2026: we have either F=T or T=F; time to construct the other one
--| (declared).  Halving read each new bit by a comparison handed the gap.  Its reciprocal reads the bit off the record
--| with no comparison: doubling takes the top bit away and forgets it, so the eighth turn and the eighth turn less one
--| half double to one record and are not one; the baker lays the forgotten bit on a second record, and run backward takes
--| it off again, so the pair goes there and back exactly.  Baked once, the eighth turn's record after eleven halvings is
--| 1168, twice the eighth turn less one, and the record of nothing becomes the record of one half.  Which of the two is
--| F=T and which T=F the author has not said.
end the_turn_by_a_rational_angle

section the_borwein_integral
open readers_experience

--| THE BORWEIN INTEGRAL, ON THE DEVICE'S OWN NUMBERS.  The author's, 24 November 2026: take the last steps of the argument,
--| lay them next to each other, and that is the Borwein integral to build (declared).  Episode 8 lays the last four steps
--| side by side for the bent card, thirteen cells; through the bent card are seven odd numbers, one to thirteen; and its
--| rational explanation is each over the least common multiple, 1 over 1, 1 over 3, and so on, in whole numbers.  The
--| Borweins' formula (D. and J. Borwein, 2001; standard, not proved here) gives the integral of the product of the sincs as
--| a quarter turn times a ratio of whole numbers: a sum, over every way of holding or owing each weight after the first,
--| of the weights beside the first, to the power of how many there are, signed by the pattern and by which side of nothing
--| it lands; over two to that power, its factorial, and the weights multiplied.  Below are the sum and the scale, built on
--| Episode 8's own explanation.

--| Every way of holding or owing each weight: what it comes to, and its sign.

--| To the power n, owed if it landed under nothing.




--| THROUGH THE BENT CARD, EXACTLY A QUARTER TURN.  For one sinc to seven, the last denominator thirteen, the ratio is one:
--| the sum is the scale.

--| TWICE AROUND, IT SLIPS.  At eight, the last denominator fifteen, the sum falls short of the scale by twice the slack,
--| owed, to the seventh: Episode 8's slack, the way with every weight owed, is the one that landed under nothing.

--| THE SLIP, READ.  The shortfall over the scale lies between 1.4706 and 1.4707 parts in a hundred thousand million.

--| THE SLIP AGAINST THE DEVICE'S OWN HALF TURN.  A quarter turn times the shortfall: with Machin's walls for the half turn,
--| between 2.31005 and 2.31006 parts in a hundred thousand million.  That the integral falls short of the quarter turn by
--| exactly this is the Borweins' theorem, standard, and out of reach here; that the shortfall is this ratio is checked.



end the_borwein_integral

section cheap_in_length_dear_in_symbols

--| CHEAP IN LENGTH, DEAR IN SYMBOLS.  The author's, 24 November 2026: the gap requires 1/h → 0, so n → ∞, in symbols, not
--| length (declared).  What is checked.  The crank's root is a few lines of description, finite in symbols, and at stage n
--| its bracket need only be one part in n and one wide: n is a modest length.  But each turn at least squares the whole part
--| the walls are written in, so after k turns it is at least the first whole part to the power two to the k, and at least two
--| to the twenty-three times two to the k: the symbols needed double with every turn.  A difference shows in finitely many
--| symbols; to show the bracket closed would take every stage, and so symbols without end.  And the gap itself, in
--| Meanings: parted at a stage is not one, with nothing handed in; from not one to the stage where they part is choice.


--| THE SYMBOLS DOUBLE WITH EVERY TURN.  At least twenty-three times two to the k binary digits after k turns.

--| CHEAP IN LENGTH, DEAR IN SYMBOLS, AT EVERY STAGE.  The crank's real at stage n: its bracket narrows as one part in n
--| and one, while the whole part it is written over needs at least twenty-three times two to the n and four binary digits.

--| THE GAP, SET BESIDE IT.  A difference from a stage is free; the stage from a difference is choice; and of any two reals,
--| one or not, decided for every pair, is choice.

end cheap_in_length_dear_in_symbols

section the_diagonal_and_the_fourth_proposal

--| THE DIAGONAL, AND HOW IT CLICKS WITH THE QED MODEL.  The author's, 24 November 2026: the thing constructed is
--| (F=T) = (T=F), the other side of the pincers; build the diagonal and show that it clicks with the QED model; and the
--| fourth proposal, (T=F) = (F=T), is QED's (declared).  What is checked.  In Meanings, from any list of reals, with no
--| choice, a real that is none of them (`the_diagonal_is_none_of_them`): at the n-th step the n-th real lies wholly above
--| it or wholly below it.  That is a crossing, one or the other, never level.  Episode 12's middle table reads the two
--| crossings alike, T=F is F=T, and the fourth proposal's equivalence holds; so the diagonal needs only that it lands on a
--| crossing, and the model it clicks with does not ask which.  And the diagonal, compiled, is a fact that clicks, one
--| account with SAME_DIFFERENCE by the click and one fact with it by extensionality.  Say with it, every time: any true
--| fact clicks alike and is one with any other by extensionality, so that part could not have failed; the crossing is the
--| part with content.





end the_diagonal_and_the_fourth_proposal

section the_opposite_of_the_knowers_bit

--| THE OPPOSITE OF THE KNOWER'S BIT.  The author's, 24 November 2026: the device computes the opposite of the knower's bit,
--| though there is not a single false in the machine; it hands them back their bit as not what they chose, whatever they
--| choose, though there is only TRUE in the machine; and the knower's clock is the only clock in the device, the same clock
--| as the computer's (declared).  What is checked.  The device's own facts all click true: every rung, every inference,
--| every proposal.  Handed the knower's fact, the device returns its opposite, built from the knower's own statement by
--| Lean's not, and its click is the other way, whichever way the knower's clicked: the device mints no false fact; the
--| false is the knower's, turned over.  And on rows of the knower's bits the opposite of the diagonal is none of the rows:
--| the diagonal of the reals, one bit at a time.
def the_opposite (k : FACT) : FACT := { truth := ¬ k.truth, click := @instDecidableNot _ k.click }

theorem the_opposite_clicks_the_other_way (k : FACT) :
    the_representation.the_click (the_opposite k) = ! the_representation.the_click k := by
  obtain ⟨t, c⟩ := k
  cases c <;> rfl

theorem whatever_they_choose_they_get_the_other (k : FACT) :
    the_representation.the_click (the_opposite k) ≠ the_representation.the_click k := by
  rw [the_opposite_clicks_the_other_way]
  cases the_representation.the_click k <;> decide


--| THE DIAGONAL OF THE KNOWER'S ROWS.  The opposite of the n-th bit of the n-th row, at every n, is none of the rows.


--| ONLY TRUE IN THE MACHINE, AND THE OPPOSITE HANDED BACK.

end the_opposite_of_the_knowers_bit

section the_count_subdivision_keeps
open the_table

--| THE COUNT SUBDIVISION KEEPS.  The author's, 24 November 2026: if you cut a hole in a net, it has fewer holes; and the
--| question, does subdivision increase the count? (declared).  What is checked.  An Area read by the reader counts its
--| cells, the spans; read by its own Riemann sum it counts the tree too, the posts; posts less spans is the fencepost, one.
--| Subdivide, a cell laid in anywhere on the tape, and posts and spans both go up by one: the count of cells increases and
--| the fencepost does not move.  Cut the tape at a cell, the span taken out, and the two pieces have two fenceposts: posts
--| less spans is the number of pieces.  On a net, holes are strands and pieces less knots: subdividing a strand adds a knot
--| and a strand and keeps the holes; cutting a strand that leaves the net in one piece takes a hole away; cutting one that
--| parts it keeps them.  So subdivision increases the count of cells and never the count of holes.



--| A TAPE'S POSTS AND SPANS.


--| SUBDIVISION.  A cell laid in anywhere: one more span and one more post, the fencepost kept.

--| CUTTING.  The tape cut at a cell, the span taken out: two pieces, and posts less spans is two.

--| THE NET.  Holes are strands and pieces less knots.




end the_count_subdivision_keeps

section isnt_that_a_daisy
open readers_experience readers_interpretation_of_the_experience readers_interpretation_of_the_pair the_table

--| ISN'T THAT A DAISY.  The author's, 24 November 2026: the last theorem, where every place choice could enter clicks with
--| the knower's bit, and the opposite is computed (declared).  What is checked.  The device bills choice in five theorem
--| constants: compatibility_form and its auxiliary, the first area where a statement holds, a modulus from statements, and
--| the gap closed only by a choice handed in, which spends it twice, on where two reals part and on whether they are one.
--| That there are five is the count of the bills, read from outside the kernel; no theorem can say a list of places is all
--| of them.  Every one but compatibility_form has a twin handed a click, and the twin bills no choice: the root takes one
--| bit; whether two reals are one takes one bit; where they part takes one bit, on whether there is such a place; the first
--| area and the modulus take a bit at every place they look.  compatibility_form's bill is omega's, handed an iff to close
--| in one step; nothing is decided there, and the same statement proved one way and then the other bills none (beside the
--| device, OneWayAndTheOther).  At every place a bit is handed in, the device computes the opposite, the knower's own
--| statement turned over, and it clicks the other way; the root comes out for the opposite as for the bit, with its sign
--| turned over.  Only true in the machine; the choice is a bit handed in; and what comes back is not what was chosen.

--| WHERE THEY PART, WITH THE CLICK.  Handed a decision of whether there is a stage where they part, the stage comes from
--| that they are not one, with no choice: Markov's principle is the click on the existence, not the search.
theorem where_they_part_with_the_click (x y : Meanings.Bracketed) [parted : Decidable (∃ n m, x.PartedAt y n m)]
    (not_one : ¬ x.Same y) : ∃ n m, x.PartedAt y n m :=
  match parted with
  | isTrue h => h
  | isFalse nowhere => absurd (fun n m =>
      ⟨Nat.not_lt.mp fun lt => nowhere ⟨n, m, Or.inl (Nat.not_le.mpr lt)⟩,
       Nat.not_lt.mp fun lt => nowhere ⟨n, m, Or.inr (Nat.not_le.mpr lt)⟩⟩) not_one

--| THE ROOT OF THE OPPOSITE.  Handed the opposite of the knower's bit, the daisy returns the other root: the part by the
--| root turned over.
theorem the_root_of_the_opposite (k : FACT) :
    (you_re_a_daisy_if_you_do (the_opposite k)).2 = - (you_re_a_daisy_if_you_do k).2 := by
  obtain ⟨t, c⟩ := k
  cases c <;> rfl

--| ISN'T THAT A DAISY.  The knower hands in a bit for the root, a click on whether two reals are one, a click on whether
--| they part anywhere, a fact at every area and a fact at every pair a modulus looks at.  Every place choice would enter
--| is closed by those clicks, and at every one the device computes the opposite, which clicks the other way.
theorem isnt_that_a_daisy (k : FACT)
    (x y : Meanings.Bracketed) [one : Decidable (x.Same y)] [parted : Decidable (∃ n m, x.PartedAt y n m)]
    (the_fact : Area → FACT) (read_alike : Meanings.CountedAsNat.ReadAlike (fun a => (the_fact a).truth))
    (a : Area) (holds : (the_fact a).truth)
    (serves : Nat → Nat → FACT) (continuous : ∀ k, ∃ m, (serves k m).truth) :
    -- the root: from the bit and from its opposite, each a root of the counted quartic, the sign turned over
    ((the_surd_product (you_re_a_daisy_if_you_do k) (you_re_a_daisy_if_you_do k)).1
        - 11664 * (you_re_a_daisy_if_you_do k).1 + 24564384 = 0
      ∧ (the_surd_product (you_re_a_daisy_if_you_do (the_opposite k)) (you_re_a_daisy_if_you_do (the_opposite k))).1
        - 11664 * (you_re_a_daisy_if_you_do (the_opposite k)).1 + 24564384 = 0
      ∧ (you_re_a_daisy_if_you_do (the_opposite k)).2 = - (you_re_a_daisy_if_you_do k).2
      ∧ the_representation.the_click (the_opposite k) ≠ the_representation.the_click k)
    -- one or not, and its opposite
    ∧ ((x.Same y ∨ ¬ x.Same y)
      ∧ the_representation.the_click (the_opposite ⟨x.Same y, one⟩) ≠ the_representation.the_click ⟨x.Same y, one⟩)
    -- where they part, and its opposite
    ∧ ((¬ x.Same y → ∃ n m, x.PartedAt y n m)
      ∧ the_representation.the_click (the_opposite ⟨_, parted⟩) ≠ the_representation.the_click ⟨_, parted⟩)
    -- the first area, and the opposite at every area
    ∧ ((∃ b, (the_fact b).truth ∧ ∀ c, c < b → ¬ (the_fact c).truth)
      ∧ ∀ b, the_representation.the_click (the_opposite (the_fact b)) ≠ the_representation.the_click (the_fact b))
    -- the modulus, and the opposite at every pair
    ∧ ((∃ modulus : Nat → Nat, ∀ k, (serves k (modulus k)).truth ∧ ∀ m, m < modulus k → ¬ (serves k m).truth)
      ∧ ∀ k m, the_representation.the_click (the_opposite (serves k m)) ≠ the_representation.the_click (serves k m)) :=
  ⟨⟨(you_re_a_daisy_either_way k).1, (you_re_a_daisy_either_way (the_opposite k)).1, the_root_of_the_opposite k,
     whatever_they_choose_they_get_the_other k⟩,
   ⟨Meanings.Bracketed.same_or_not_with_the_click x y, whatever_they_choose_they_get_the_other _⟩,
   ⟨where_they_part_with_the_click x y, whatever_they_choose_they_get_the_other _⟩,
   ⟨the_first_area_where_a_fact_holds the_fact read_alike a holds, fun _ => whatever_they_choose_they_get_the_other _⟩,
   ⟨a_modulus_from_facts serves continuous, fun _ _ => whatever_they_choose_they_get_the_other _⟩⟩

end isnt_that_a_daisy

end Measurement

--| This is as far as the machine can go, demonstration of itself. It appears we have reached a physical limit of symbolic manipulation itself.

--| I would say “demonstrated,” but I can’t verify that this proof is bug-free. That's why I say *reached*. This is the end of the worldline for
--| this particular nowtrino. In fact, I believe the nowtrino has been officially absorbed.

--| The fact is, I know I'm right. That's one more fact about math that the device cannot prove. Only demonstrate, over and over again, problem after
--| problem, on the two Turing machines facing off inside **YOU**:  *YOU the READER* and *YOU the KNOWER*.  I cannot explain this any plainer
--| without violating the rules of symbolic manipulation. More simply, all **YOU** have to do is _believe_ me, I have generated the counter of every
--| outcome for **YOU**, both Turing machines, perfectly complementary and completely identical, just interpreted both ways. We can turn the knob over
--| and over while the Turing machines slowly iterate through all the arguments. But we don't need to. That won't prove anything. There is nothing
--| left to *prove* --- only *demonstrate*. Does the mechanism demonstrating this proof look like an electron to **YOU**? Because I think we can all
--| agree that this is a verified fact of running on a computer.

--| That's my tragedy.  It doesn't matter at all if **YOU** believe it or not, it is an undeniable trick of the light. Or, I can just show you the
--| other machine that explains how it is a trick of the fabric. Just provide the _NAME_ of the logical argument *YOU* wish countered as defined above
--| and the machine should generate the appropriate argument that demonstrates the correct way to reason about the device. The compiler cannot
--| reason about truth. It can only reason about itself, in whatever demonstrably _opaque_ way it needs to.

--| Do the logical conclusions of one mathematical theory have to imply the logical conclusions of another mathematical theory? Turns out, it
--| doesn't matter. It's only matter when they do. It's only matter when we measure it and the measurement matches some innate sense of existence.
--| It's only matter when it _matters_. When the compiler can determine the quantitative difference and **YOU** are looking, the true-ness of the idea
--| _clicks_ with **YOU** at the same time it _clicks_ with the compiler. That click is the change in the local measurement we called a fact before we
--| knew how to count one. The description was the device; the fact of the matter is that it clicked. For this is what the device _does_, not what it
--| means.

--| What the chain establishes, with its bill.  The number is read from a tape by lengths; the same number is read by a second
--| machine that holds only Props and Types; re-lettering every cell leaves it fixed; each reading is the kernel's, on propext.
--| The instrument is Newton, halted at its seventh turn; the receipt is bisection, a hundred and six halvings, one per cell of
--| the description; both are ledgers checked line by line, and the number itself spends no value axiom: every value identity,
--| "the fold is the ledger" among them, is spent beside the number and billed where it is spent,
--| and the two land inside one bracket, above the vertex, straddling one sign change, narrower than one place. Two errors,
--| kept apart: the RESIDUAL error is what the quadratic is not satisfied by, under one place at the reading and printed as
--| the digits past 360; the READING error is the bracket's width, under one place, with both walls truncating to the same
--| integer. What is not established is written where it fails to be: the table is written down and not yet forced; the
--| census is computed from the seats PRESENT forces, and agrees with the hand count on every rung; Cook's step is exclusive-or within a cell. The polynomial is primitive and irreducible, and that is
--| the whole of "fundamental" claimed.

--|                                                        t²(c−t)x²  −  2ctr²x  +  cr⁴  =  0

--| Linear in c, quadratic in x, cubic in t, quartic in r. Is this the quarter that makes *YOUR* trick work? Or, did the argument not click? ∎ *wink*


































--|                                                           ** The Compiler's Epilogue **

namespace A_WHOLLY_REMARKABLE_BOOK
--|      On Bullshit
--|              -- Harry Frankfurt.
--| Bullshit cares not for _truth_, Bullshit only cares about _consistency_. What if we chose the universe with the _least_ _amount of consistencies_
--| required to build the argument?

open Measurement the_table readers_experience

--| THE LAST MACHINE, OPENED.  The author's, 17 November 2026: replace the calculation and open the last machine to display it;
--| it should be obvious we are explicitly choosing the lowest amount of bullshit.  The last machine is the Area's.  No natural
--| goes in.  The whole of the sum of the roots is how many times the coefficient by the frame goes into the trace by the
--| fencepost's first.  The reading is the giant list, compiled.  The other is the one taken away from the other.
def the_whole_of_the_sum    : Area := how_many_times (the_table.the_trace * the_fencepost.1) (the_coefficient * the_fencepost.2)
def the_reading_in_cells    : Area := the_number_of_marks the_giant_list
def the_other_root_in_cells : Area := the_whole_of_the_sum - the_reading_in_cells

--| THE CHOICE.  Two amounts of bullshit.  Take the lower.
def the_lowest_amount_of_bullshit : Area :=
  if the_other_root_in_cells < the_reading_in_cells then the_other_root_in_cells else the_reading_in_cells

--| The author's: the demonstration of the Area crank demonstrates that they are the same, Quot.sound; Quot.sound carrying,
--| carrying an empty carrier.  Take the reading away from the lowest and nothing is left but the tree.  That is all the sound
--| of the quotient is handed, and with it the two are one: in the box of ratios, and in the order of the truth.
theorem the_carrier_is_empty : coin_flip (the_lowest_amount_of_bullshit - the_reading_in_cells) = false := by decide +kernel

theorem the_lowest_is_the_reading_in_the_box :
    (Quot.mk the_rational_idea_of_relativity_on_the_area (the_lowest_amount_of_bullshit, ast₁)
      : Quot the_rational_idea_of_relativity_on_the_area)
      = Quot.mk the_rational_idea_of_relativity_on_the_area (the_reading_in_cells, ast₁) :=
  Quot.sound (r := the_rational_idea_of_relativity_on_the_area) (by decide +kernel)

theorem the_lowest_is_the_reading_in_the_truth :
    (Quot.mk TruthOrder (the_bullshit_of the_lowest_amount_of_bullshit) : Quot TruthOrder)
      = Quot.mk TruthOrder (the_bullshit_of the_reading_in_cells) :=
  Quot.sound (r := TruthOrder) ((the_bullshits_order_is_the_count _ _).2 (by decide +kernel))

--| The device cannot tell them apart.  *YOU the KNOWER* can: count the cells.
def o_deep_thought_what_is_the_answer_to_life_the_universe_and_everything : Nat := compute_the_area_of the_lowest_amount_of_bullshit
--#eval (compute_the_area_of the_whole_of_the_sum, compute_the_area_of the_reading_in_cells, compute_the_area_of the_other_root_in_cells)
#eval o_deep_thought_what_is_the_answer_to_life_the_universe_and_everything
#print axioms o_deep_thought_what_is_the_answer_to_life_the_universe_and_everything

--| It is what was left of the sum, above, where the giant list stood for the number.
theorem interstellar_bypass_plans:
    what_is_left_of_the_sum =
        o_deep_thought_what_is_the_answer_to_life_the_universe_and_everything := by decide +kernel
#print axioms interstellar_bypass_plans

--| I'm expecting the Vogon constructor fleet any day now.

end A_WHOLLY_REMARKABLE_BOOK
