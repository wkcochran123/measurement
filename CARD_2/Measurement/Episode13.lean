/-
__Measurement: The Tragedy of John Henry__
__A Satire in Look Ahead Backus-Naur Form__

_This is a gentle reminder that things can only get so meta and still be consistent._

(c) 2026

"stat rosa pristina nomine, nomina nuda tenemus"

__EPISODE 13__: _The Area_

Episode 12 walked the device out from one reader of a tape, its length.  The bent card of Episode 8 was written for any
reader, and any Term the reader lands in that can be set beside, taken each for each, taken away, and compared.  Episode 8
handed it the naturals.  This episode hands it the Area of Episode 2, and no natural is handed in.

The Area is the tape.  A tree is the end of it.  A dt is one more cell.  That is all an Area ever was.
-/
import Measurement.Episode12

namespace Measurement
open readers_experience

namespace the_area

--| THE FOUR THINGS THE BENT CARD ASKS OF A TERM.  Each is said on the Area and on nothing else.

--| Beside: one Area, and where its tree stood, the other.  Two things next to each other on the tape.
def beside : Area → Area → Area
  | .tree _,      b => b
  | .dt f n rest, b => .dt f n (beside rest b)

--| Each for each: for every cell of the one, the whole of the other, beside what came before.
def each_for_each : Area → Area → Area
  | .tree f,      _ => .tree f
  | .dt _ _ rest, b => beside b (each_for_each rest b)

--| Taken away: a cell from each until one of them is down to its tree.  The tree never leaves the Area.
def taken_away : Area → Area → Area
  | .tree f,    _         => .tree f
  | a,          .tree _   => a
  | .dt _ _ a,  .dt _ _ b => taken_away a b

--| Something left: is there a cell, or only the tree?
def something_is_left : Area → Bool
  | .tree _   => false
  | .dt _ _ _ => true

instance : Add Area := ⟨beside⟩
instance : Mul Area := ⟨each_for_each⟩
instance : Sub Area := ⟨taken_away⟩
--| Less: take the one away from the other, and something is left.
instance : LT Area := ⟨fun a b => something_is_left (b - a) = true⟩
instance : DecidableRel (α := Area) (· < ·) := fun a b => inferInstanceAs (Decidable (something_is_left (b - a) = true))

--| THE ABSTRACTION.  The author's, 16 November 2026: instead of a List, the Abstraction is the thing we want.  Compile builds
--| the Area.  Execute counts the size.  Episode 8 has all three kinds already: the carefully chosen variable names, a satire;
--| the opaque wall of math, a compile on top of it; the proof, an execute on top of that.  A tape is written the same way: a
--| compile for every fact, on the names; then an execute for every fact, on the wall.  Compile comes before execute.
def the_wall_for : List FACT → Abstraction
  | []        => carefully_chosen_variable_names
  | _ :: rest => .compile zero δδxᵢ (the_wall_for rest)
def the_proof_over (wall : Abstraction) : List FACT → Abstraction
  | []        => wall
  | _ :: rest => .execute zero δδxᵢ (the_proof_over wall rest)
def the_abstraction_of_a_tape (tape : List FACT) : Abstraction := the_proof_over (the_wall_for tape) tape

--| Compile builds the Area: the tree of Episode 8, ast₀, under the names, and one cell of ast₁'s kind for every compile.  An
--| execute builds nothing.  What the fact was is not kept.  The contents of the cells are the symmetry; the count is the charge.
def compiled : Abstraction → Area
  | .satire_about _    => ast₀
  | .compile _ _ rest  => .dt zero another_zero (compiled rest)
  | .execute _ _ rest  => compiled rest

--| Execute counts the size: one for every execute.  A compile counts for nothing.
def executed : Abstraction → Nat
  | .satire_about _    => 0
  | .compile _ _ rest  => executed rest
  | .execute _ _ rest  => executed rest + 1

--| THE READER.  A tape, written as an Abstraction, and compiled.
def the_area_of_a_tape (tape : List FACT) : Area := compiled (the_abstraction_of_a_tape tape)

--| THE DEVICE, ON THE AREA.  The same section of Episode 8, word for word, with the Area where the naturals stood.
def the_fencepost               := bent_card.fencepost Area the_area_of_a_tape
def the_coefficient             := bent_card.the_exact_Taylor_series_degree Area the_area_of_a_tape
def the_memory                  := bent_card.the_length_of_the_path_from_here_to_there Area the_area_of_a_tape
def the_trace                   := bent_card.the_measurement_degrees_of_freedom Area the_area_of_a_tape
def the_house                   := bent_card.the_device_as_linear_operator_mapped_identity Area the_area_of_a_tape
def one_turn                    := bent_card.the_device_computing_the_next_configuration Area the_area_of_a_tape
def the_crank                   := bent_card.proportional_laws_accumulate_commutation_projections_called_TERM_LAMBDAS Area the_area_of_a_tape
def the_crank_and_the_fencepost := bent_card.fenceposts_must_be_preserved Area the_area_of_a_tape

--| THE COUNT.  This is the only place a natural appears, and it is not handed to the device.  It is how *YOU the READER*
--| read an Area: so many cells.  The tree counts for nothing.  Area's own reading, the Riemann sum, counts the tree too;
--| that is the fencepost.
def cells : Area → Nat
  | .tree _      => 0
  | .dt _ _ rest => cells rest + 1
def read (pair : Area × Area) : Nat × Nat := (cells pair.1, cells pair.2)

theorem the_riemann_sum_counts_the_tree_too (a : Area) : a.riemann_integrate.length = cells a + the_fencepost_bug := by
  induction a with
  | tree _ => rfl
  | dt _ _ rest ih => simp only [Area.riemann_integrate, List.length_cons, cells, ih]; omega

--| The reader is the length.  Area is List.length.  And execute counts what compile built.
theorem the_proof_builds_nothing_more (wall : Abstraction) (tape : List FACT) : compiled (the_proof_over wall tape) = compiled wall := by
  induction tape with
  | nil => rfl
  | cons _ _ ih => simp only [the_proof_over, compiled, ih]

theorem the_wall_has_a_cell_for_every_fact (tape : List FACT) : cells (compiled (the_wall_for tape)) = tape.length := by
  induction tape with
  | nil => rfl
  | cons _ _ ih => simp only [the_wall_for, compiled, cells, ih, List.length_cons]

theorem the_area_of_a_tape_has_the_tapes_length (tape : List FACT) : cells (the_area_of_a_tape tape) = tape.length := by
  simp only [the_area_of_a_tape, the_abstraction_of_a_tape, the_proof_builds_nothing_more, the_wall_has_a_cell_for_every_fact]

theorem the_wall_executes_nothing (tape : List FACT) : executed (the_wall_for tape) = 0 := by
  induction tape with
  | nil => rfl
  | cons _ _ ih => simp only [the_wall_for, executed, ih]

theorem the_proof_counts_every_fact (wall : Abstraction) (tape : List FACT) :
    executed (the_proof_over wall tape) = executed wall + tape.length := by
  induction tape with
  | nil => rfl
  | cons _ _ ih => simp only [the_proof_over, executed, ih, List.length_cons]; omega

theorem execute_counts_what_compile_built (tape : List FACT) :
    executed (the_abstraction_of_a_tape tape) = cells (compiled (the_abstraction_of_a_tape tape)) := by
  rw [show compiled (the_abstraction_of_a_tape tape) = the_area_of_a_tape tape from rfl, the_area_of_a_tape_has_the_tapes_length]
  simp only [the_abstraction_of_a_tape, the_proof_counts_every_fact, the_wall_executes_nothing, Nat.zero_add]

--| Episode 8's own three are the first of them: the proof is the abstraction of a tape of one.
theorem the_proof_of_episode_eight_is_the_abstraction_of_one_fact : the_abstraction_of_a_tape [zero] = the_proof := rfl

--| Written this way a tape is on the page twice, once compiled and once executed, and once more for the names: the fencepost.
--| For the memory tape that is two eighteens and one.  Thirty-six is Closure's.
theorem an_abstraction_is_twice_its_tape_and_the_names (tape : List FACT) :
    (the_abstraction_of_a_tape tape).equivalation.length = tape.length + tape.length + the_fencepost_bug := by
  have wall : ∀ t : List FACT, (the_wall_for t).equivalation.length = t.length + the_fencepost_bug := by
    intro t
    induction t with
    | nil => rfl
    | cons _ _ ih => simp only [the_wall_for, Abstraction.equivalation, List.length_cons, ih]; omega
  have proof : ∀ (w : Abstraction) (t : List FACT), (the_proof_over w t).equivalation.length = w.equivalation.length + t.length := by
    intro w t
    induction t with
    | nil => rfl
    | cons _ _ ih => simp only [the_proof_over, Abstraction.equivalation, List.length_cons, ih]; omega
  simp only [the_abstraction_of_a_tape, proof, wall]; omega

theorem the_memory_written_as_an_abstraction_is_the_trace_and_the_fencepost :
    (the_abstraction_of_a_tape the_memory_tape).equivalation.length = the_trace_of_truth_in_the_device + the_fencepost_bug := by
  rw [an_abstraction_is_twice_its_tape_and_the_names]; rfl

--| Compile comes before execute, and not back: the wall is strictly under the abstraction, whenever there is a fact.
theorem the_wall_comes_before_the_abstraction (fact : FACT) (rest : List FACT) :
    the_wall_for (fact :: rest) < the_abstraction_of_a_tape (fact :: rest)
      ∧ ¬ (the_abstraction_of_a_tape (fact :: rest) ≤ the_wall_for (fact :: rest)) :=
  ⟨rfl, fun h => Bool.noConfusion h⟩

--| The four things, counted.  Beside adds.  Each for each multiplies.  Taken away subtracts, and stops at the tree.  Less is less.
theorem beside_adds (a b : Area) : cells (a + b) = cells a + cells b := by
  show cells (beside a b) = _
  induction a with
  | tree _ => simp only [beside, cells, Nat.zero_add]
  | dt _ _ rest ih => simp only [beside, cells, ih]; omega

theorem each_for_each_multiplies (a b : Area) : cells (a * b) = cells a * cells b := by
  show cells (each_for_each a b) = _
  induction a with
  | tree _ => simp only [each_for_each, cells, Nat.zero_mul]
  | dt _ _ rest ih =>
    simp only [each_for_each, cells]
    rw [show beside b (each_for_each rest b) = b + each_for_each rest b from rfl, beside_adds, ih, Nat.succ_mul]; omega

theorem taken_away_subtracts (a b : Area) : cells (a - b) = cells a - cells b := by
  show cells (taken_away a b) = _
  induction a generalizing b with
  | tree _ => simp only [taken_away, cells, Nat.zero_sub]
  | dt _ _ rest ih =>
    cases b with
    | tree _ => simp only [taken_away, cells, Nat.sub_zero]
    | dt _ _ b' => simp only [taken_away, cells, ih, Nat.add_sub_add_right]

theorem something_is_left_when_there_is_a_cell (a : Area) : something_is_left a = true ↔ 0 < cells a := by
  cases a with
  | tree _ => exact ⟨fun h => Bool.noConfusion h, fun h => absurd h (Nat.lt_irrefl 0)⟩
  | dt _ _ rest => exact ⟨fun _ => Nat.succ_pos _, fun _ => rfl⟩

theorem less_is_less (a b : Area) : a < b ↔ cells a < cells b := by
  show something_is_left (b - a) = true ↔ _
  rw [something_is_left_when_there_is_a_cell, taken_away_subtracts]; exact Nat.sub_pos_iff_lt

--| THE WALK, ON THE AREA.  Counted, the fencepost, the coefficient, the memory, the trace and the house of this episode are
--| those of Episode 8.
theorem counted_the_walk_is_the_walk :
    read the_fencepost = bent_card.fencepost Nat List.length
      ∧ cells the_coefficient = an_exact_polynomial_description
      ∧ cells the_memory = the_number_of_symbols_that_must_be_written_to_express_this
      ∧ cells the_trace = the_trace_of_truth_in_the_device
      ∧ read the_house = the_held_house := by
  simp only [read, the_fencepost, the_coefficient, the_memory, the_trace, the_house, an_exact_polynomial_description,
    the_number_of_symbols_that_must_be_written_to_express_this, the_trace_of_truth_in_the_device, the_held_house,
    bent_card.fencepost, bent_card.the_exact_Taylor_series_degree, bent_card.the_length_of_the_path_from_here_to_there,
    bent_card.the_measurement_degrees_of_freedom, bent_card.the_device_as_linear_operator_mapped_identity,
    each_for_each_multiplies, the_area_of_a_tape_has_the_tapes_length, and_self]

--| ONE TURN.  Turn the crank on the Area and count, or count and turn Episode 8's crank.  The same.
theorem counted_one_turn_is_one_turn (scale : Area) (here : Area × Area) :
    read (one_turn scale here)
      = bent_card.the_device_computing_the_next_configuration Nat List.length (cells scale) (read here) := by
  obtain ⟨x, y⟩ := here
  simp only [one_turn, read, bent_card.the_device_computing_the_next_configuration, bent_card.the_exact_Taylor_series_degree,
    bent_card.the_length_of_the_path_from_here_to_there, bent_card.the_measurement_degrees_of_freedom, bent_card.fencepost]
  split
  · rename_i h
    have h' := (less_is_less _ _).1 h
    simp only [beside_adds, each_for_each_multiplies, taken_away_subtracts, the_area_of_a_tape_has_the_tapes_length] at h'
    rw [if_pos h']
  · rename_i h
    have h' : ¬ _ := fun g => h ((less_is_less _ _).2 g)
    simp only [beside_adds, each_for_each_multiplies, taken_away_subtracts, the_area_of_a_tape_has_the_tapes_length] at h'
    rw [if_neg h']
    simp only [each_for_each_multiplies, taken_away_subtracts, the_area_of_a_tape_has_the_tapes_length]

--| EVERY TURN.  As many turns as there are marks on any tape of turns.
theorem counted_any_number_of_turns_is_as_many_turns (scale : Area) (turns : List Unit) (here : Area × Area) :
    read (turns.foldl (fun x _ => one_turn scale x) here)
      = turns.foldl (fun x _ => bent_card.the_device_computing_the_next_configuration Nat List.length (cells scale) x) (read here) := by
  induction turns generalizing here with
  | nil => rfl
  | cons _ rest ih => simp only [List.foldl_cons, ih, counted_one_turn_is_one_turn]

--| THE CRANK.  All hundred and six turns from the house, on the Area; counted, they are Episode 8's.  Nobody turned them here.
--| An Area of that many cells is not a thing to be written out.  It does not have to be.
theorem counted_the_crank_is_the_crank (scale : Area) :
    read (the_crank scale)
      = bent_card.proportional_laws_accumulate_commutation_projections_called_TERM_LAMBDAS Nat List.length (cells scale) := by
  have house := counted_the_walk_is_the_walk.2.2.2.2
  simp only [the_house, the_held_house] at house
  simp only [the_crank, bent_card.proportional_laws_accumulate_commutation_projections_called_TERM_LAMBDAS]
  exact (counted_any_number_of_turns_is_as_many_turns scale _ _).trans (by rw [house])

theorem counted_the_crank_and_the_fencepost_are_the_crank_and_the_fencepost (scale : Area) :
    read (the_crank_and_the_fencepost scale) = bent_card.fenceposts_must_be_preserved Nat List.length (cells scale) := by
  have crank := counted_the_crank_is_the_crank scale
  simp only [the_crank, read] at crank
  simp only [the_crank_and_the_fencepost, read, bent_card.fenceposts_must_be_preserved, bent_card.fencepost,
    each_for_each_multiplies, the_area_of_a_tape_has_the_tapes_length]
  rw [← crank]

--| THE NUMBER.  Hand the Area's device any Area with as many cells as Episode 8's scale.  Count what comes back.  It is the
--| pair Episode 8 arranged, and so the same digits.  No natural went in.  One came out, and only because *YOU the READER* counted.
theorem the_area_arrives_at_the_same_pair (scale : Area) (as_many_cells_as_the_scale : cells scale = all_possible_variables) :
    read (the_crank_and_the_fencepost scale) = arrange_the_information_appropriately := by
  rw [counted_the_crank_and_the_fencepost_are_the_crank_and_the_fencepost, as_many_cells_as_the_scale]; rfl

theorem the_area_arrives_at_the_same_number (scale : Area) (as_many_cells_as_the_scale : cells scale = all_possible_variables) :
    (read (the_crank_and_the_fencepost scale)).1 * all_possible_variables / (read (the_crank_and_the_fencepost scale)).2
      = the_constant_factor_of_scaling_bullshit := by
  rw [the_area_arrives_at_the_same_pair scale as_many_cells_as_the_scale]; rfl

--| And there is such an Area: the tape of that many truths, read by the reader.
theorem there_is_an_area_with_as_many_cells_as_the_scale :
    cells (the_area_of_a_tape (List.replicate all_possible_variables zero)) = all_possible_variables := by
  rw [the_area_of_a_tape_has_the_tapes_length, List.length_replicate]

--| THE CONSTANT, ON THE AREA.  Episode 8 is the guide, line for line.  First the free variables: the basis by the dimensions.
def the_free_variables := the_area_of_a_tape the_basis.the_reading * the_area_of_a_tape the_coordinate_system.gauss

--| Then the express route: the tape from the inferred end as deep as the bent card, less the memory.
def the_express_route := the_area_of_a_tape (from_the_inferred_end bent_card) - the_memory

--| Raised: the one Area each for each with itself, once for every cell of the other.  With no cell, the one cell, ast₁.
def raised : Area → Area → Area
  | _, .tree _      => ast₁
  | b, .dt _ _ rest => b * raised b rest

--| All possible variables: the free variables raised to the express route.  This is the scale.  It is an Area.
def the_scale := raised the_free_variables the_express_route

--| The names, and the delimiter between them.
def the_named_lambdas := the_crank the_scale
def arranged          := the_crank_and_the_fencepost the_scale

--| The fourth lambda, the division algorithm: how many times the one can be taken away from the other.  The first Area is only
--| the patience: no more takings than the thing taken from has cells.  From a tree nothing is taken, and by a tree nothing is.
def taking_until_less : Area → Area → Area → Area
  | .tree _,          _,        _       => ast₀
  | .dt _ _ patience, the_rest, the_one => if the_rest < the_one then ast₀ else ast₁ + taking_until_less patience (the_rest - the_one) the_one
def how_many_times (the_whole the_one : Area) : Area :=
  if something_is_left the_one = true then taking_until_less the_whole the_whole the_one else ast₀

--| The rational idea of relativity, on the Area.  Not more: take the one away from the other and nothing is left.
@[reducible] def the_rational_idea_of_relativity_on_the_area (x y : Area × Area) : Prop := ¬ (y.1 * x.2 < x.1 * y.2)

theorem raised_raises (b e : Area) : cells (raised b e) = cells b ^ cells e := by
  induction e with
  | tree _ => rfl
  | dt _ _ rest ih => simp only [raised, cells, each_for_each_multiplies, ih, Nat.pow_succ, Nat.mul_comm]

theorem taking_until_less_divides (the_one : Area) (there_is_one : 0 < cells the_one) (patience the_rest : Area)
    (patience_enough : cells the_rest ≤ cells patience) :
    cells (taking_until_less patience the_rest the_one) = cells the_rest / cells the_one := by
  induction patience generalizing the_rest with
  | tree _ =>
    have nothing : cells the_rest = 0 := Nat.le_zero.mp patience_enough
    simp only [taking_until_less, nothing, Nat.zero_div]; rfl
  | dt _ _ patience ih =>
    simp only [taking_until_less]
    split
    · rename_i h
      rw [Nat.div_eq_of_lt ((less_is_less _ _).1 h)]; rfl
    · rename_i h
      have not_less : cells the_one ≤ cells the_rest := Nat.le_of_not_lt (fun g => h ((less_is_less _ _).2 g))
      have still_enough : cells (the_rest - the_one) ≤ cells patience := by
        rw [taken_away_subtracts]; simp only [cells] at patience_enough; omega
      rw [beside_adds, ih _ still_enough, taken_away_subtracts, Nat.div_eq_sub_div there_is_one not_less, Nat.add_comm]; rfl

theorem how_many_times_divides (the_whole the_one : Area) : cells (how_many_times the_whole the_one) = cells the_whole / cells the_one := by
  simp only [how_many_times]
  split
  · rename_i h
    exact taking_until_less_divides the_one ((something_is_left_when_there_is_a_cell _).1 h) _ _ (Nat.le_refl _)
  · rename_i h
    have no_cell : cells the_one = 0 := Nat.le_zero.mp (Nat.le_of_not_lt (fun g => h ((something_is_left_when_there_is_a_cell _).2 g)))
    rw [no_cell, Nat.div_zero]; rfl

--| Counted, the free variables, the express route and the scale are Episode 8's.
theorem counted_the_scale_is_the_scale :
    cells the_free_variables = the_free_variable_count
      ∧ cells the_express_route = the_express_route_station_count
      ∧ cells the_scale = all_possible_variables := by
  have free : cells the_free_variables = the_free_variable_count := by
    simp only [the_free_variables, each_for_each_multiplies, the_area_of_a_tape_has_the_tapes_length]; rfl
  have express : cells the_express_route = the_express_route_station_count := by
    simp only [the_express_route, taken_away_subtracts, the_area_of_a_tape_has_the_tapes_length, counted_the_walk_is_the_walk.2.2.1]; rfl
  exact ⟨free, express, by simp only [the_scale, raised_raises, free, express]; rfl⟩

theorem counted_the_arrangement_is_the_arrangement : read arranged = arrange_the_information_appropriately :=
  the_area_arrives_at_the_same_pair the_scale counted_the_scale_is_the_scale.2.2

--| THE CONSTANT CAN BE INFERRED.  Episode 8's statement, with the Area where the naturals stood: there is an Area which, each
--| for each with the second of the pair, stands in the rational relation with the first of the pair by the scale.
theorem a_partitioning_of_quotients_on_the_area (numerator denominator : Area) :
    (Quot.mk the_rational_idea_of_relativity_on_the_area (denominator * how_many_times numerator denominator, denominator)
        : Quot the_rational_idea_of_relativity_on_the_area)
      = Quot.mk the_rational_idea_of_relativity_on_the_area (numerator, denominator) :=
  Quot.sound (r := the_rational_idea_of_relativity_on_the_area) (by
    show ¬ (numerator * denominator < denominator * how_many_times numerator denominator * denominator)
    intro more
    have more' := (less_is_less _ _).1 more
    simp only [each_for_each_multiplies, how_many_times_divides] at more'
    exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le more'
      (Nat.mul_le_mul_right (cells denominator) (the_constant_is_at_least_true (cells numerator) (cells denominator)))))

--| THE SEAL.  From here on the crank, the raising and the taking away are names and are not opened.  What is known of them is
--| what was counted above.  Open one and the machine goes looking for an Area nobody can write.
attribute [irreducible] the_crank the_crank_and_the_fencepost raised taking_until_less how_many_times the_scale

--| Said of any scale at all.  Nothing here is turned, raised or taken away: the scale is a name.
def the_constant_inferred_at (scale : Area) :
    { k : Area // (Quot.mk the_rational_idea_of_relativity_on_the_area
                        ((the_crank_and_the_fencepost scale).2 * k, (the_crank_and_the_fencepost scale).2)
                      : Quot the_rational_idea_of_relativity_on_the_area)
                    = Quot.mk the_rational_idea_of_relativity_on_the_area
                        ((the_crank_and_the_fencepost scale).1 * scale, (the_crank_and_the_fencepost scale).2) } :=
  ⟨how_many_times ((the_crank_and_the_fencepost scale).1 * scale) (the_crank_and_the_fencepost scale).2,
   a_partitioning_of_quotients_on_the_area ((the_crank_and_the_fencepost scale).1 * scale) (the_crank_and_the_fencepost scale).2⟩

--| The division, counted, of three names.  No Area is looked into.
theorem counted_the_division_is_the_division (numerator denominator scale : Area) (n d s : Nat)
    (the_numerator : cells numerator = n) (the_denominator : cells denominator = d) (the_scale_of_it : cells scale = s) :
    cells (how_many_times (numerator * scale) denominator) = n * s / d := by
  rw [how_many_times_divides, each_for_each_multiplies, the_numerator, the_denominator, the_scale_of_it]

theorem episode_eights_constant_is_its_own_division :
    arrange_the_information_appropriately.1 * all_possible_variables / arrange_the_information_appropriately.2
      = the_constant_factor_of_scaling_bullshit := rfl

theorem counted_the_constant_at_any_such_scale (scale : Area) (as_many_cells_as_the_scale : cells scale = all_possible_variables) :
    cells (the_constant_inferred_at scale).val = the_constant_factor_of_scaling_bullshit :=
  (counted_the_division_is_the_division _ _ _ _ _ _
    (congrArg Prod.fst (the_area_arrives_at_the_same_pair scale as_many_cells_as_the_scale))
    (congrArg Prod.snd (the_area_arrives_at_the_same_pair scale as_many_cells_as_the_scale))
    as_many_cells_as_the_scale).trans episode_eights_constant_is_its_own_division

--| THE TRANSITION.  The author's, 16 November 2026: the transition matrix is abstraction, abstraction, abstraction, limit.
--| Three of the four are said of a name and cost what a name costs.  The fourth is the Area itself, and it is only approached:
--| ask the machine for it and the machine runs out of memory.  It did.  So the constant is named at the scale, and never opened.
def the_constant_can_be_inferred_on_the_area := the_constant_inferred_at the_scale

--| In fact, put simply:
def the_constant := (the_constant_inferred_at the_scale).val

--| THE CONSTANT IS AN AREA.  Counted, it is Episode 8's constant, the one whose glyphs Episode 8 and Episode 12 print.  Nobody
--| built this Area and nobody will.  It has a definition, the definition has a count, and the count was already printed.
theorem counted_the_constant_is_the_constant :
    cells (the_constant_inferred_at the_scale).val = the_constant_factor_of_scaling_bullshit :=
  counted_the_constant_at_any_such_scale the_scale counted_the_scale_is_the_scale.2.2

--| FOUR BULLSHIT VALUES.  The author's, 16 November 2026: you should now be able to get four bullshit values out.  The
--| constant is an Area nobody can write.  These four can be written, and are.  Episode 8 has the two ends: no presents, the
--| zero; and no Santa, one on top of it.  An Area is read out the same way, a no Santa for every cell.
--| Each cell carries the number of the cells under it, where Bullshit's order looks.  Without that the order cannot tell six
--| from nineteen: it reads the top number and nothing else.
def the_number_of : Area → Number
  | .tree _      => another_zero
  | .dt _ _ rest => .one zero (the_number_of rest)
def the_bullshit_of : Area → Bullshit.{0,0}
  | .tree _      => no_presents
  | .dt _ _ rest => .one zero (the_number_of rest) the_satire the_satire (the_bullshit_of rest)

--| The frame is Gauss's, the second of the fencepost.  An arm that can click is the coefficient beside the frame.  The arm
--| that cannot is the frame alone.
def the_frame := the_fencepost.2
def the_arm (this that : Bool) : Area :=
  if the_arm_stores_a_fact_that_can_click this that then the_coefficient + the_frame else the_frame

def four_bullshit_values : List Bullshit :=
  [the_bullshit_of (the_arm true true),  the_bullshit_of (the_arm true false),
   the_bullshit_of (the_arm false true), the_bullshit_of (the_arm false false)]

--| One cell is no Santa.
theorem one_cell_is_no_santa : the_bullshit_of ast₁ = no_santa := rfl

--| The arms, counted, are the arms of Episode 12: the memory three times, and Gauss's once.  Abstraction, abstraction,
--| abstraction, limit.
theorem counted_the_arms_are_the_arms :
    [cells (the_arm true true), cells (the_arm true false), cells (the_arm false true), cells (the_arm false false)]
      = [the_arm_weight true true, the_arm_weight true false, the_arm_weight false true, the_arm_weight false false] := by decide

--| And on Episode 8's own meter each reads one over, for the zero it stands on: the fencepost.
theorem the_four_on_the_meter :
    four_bullshit_values.map (fun bullshit => bullshit.meter.length)
      = [the_memory_tape.length + the_fencepost_bug, the_coordinate_system.gauss.length + the_fencepost_bug,
         the_memory_tape.length + the_fencepost_bug, the_memory_tape.length + the_fencepost_bug] := by decide

--| THE EXPERIENCE AND THE INTERPRETATION.  The author's, 16 November 2026: the experience and the interpretation are
--| represented by those four bullshit values; put them together.  First, the order.  The number's order on these is the count,
--| and so is Bullshit's.
theorem the_numbers_order_is_the_count (a b : Area) : Number.le (the_number_of a) (the_number_of b) ↔ cells a ≤ cells b := by
  induction a generalizing b with
  | tree _ => exact ⟨fun _ => Nat.zero_le _, fun _ => by simp only [the_number_of, another_zero, Number.le]⟩
  | dt fa na ra ih =>
    cases b with
    | tree _ => exact ⟨fun h => by simp only [the_number_of, another_zero, Number.le] at h, fun h => absurd h (Nat.not_succ_le_zero _)⟩
    | dt fb nb rb =>
      have step : Number.le (the_number_of (.dt fa na ra)) (the_number_of (.dt fb nb rb)) ↔ Number.le (the_number_of ra) (the_number_of rb) := by
        simp only [the_number_of, Number.le, zero, FACT.Truth]
      rw [step, ih]; exact Nat.succ_le_succ_iff.symm

theorem the_bullshits_order_is_the_count (a b : Area) : the_bullshit_of a ≤ the_bullshit_of b ↔ cells a ≤ cells b := by
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
def the_experience : Closure.{0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0} :=
  .different zero (the_bullshit_of (the_arm false true)) (the_bullshit_of (the_arm true false))
    (some (the_bullshit_of.{0,0} (the_arm false true) < the_bullshit_of.{0,0} (the_arm true false)))
def the_interpretation : Closure.{0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0} :=
  .different zero (the_bullshit_of (the_arm true true)) (the_bullshit_of (the_arm false false))
    (some (the_bullshit_of.{0,0} (the_arm true true) < the_bullshit_of.{0,0} (the_arm false false)))

--| THE CLOSURE.  (T=F) = (F=T) ≤ (T=T) = (T=T), in Closure's own order, and not back.
theorem the_experience_is_under_the_interpretation_and_not_back :
    the_experience ≤ the_interpretation ∧ ¬ (the_interpretation ≤ the_experience) := by
  constructor
  · show Closure.le the_experience the_interpretation
    simp only [the_experience, the_interpretation, Closure.le, Closure.implying_implication]
    exact ⟨trivial, (the_bullshits_order_is_the_count _ _).2 (by decide), (the_bullshits_order_is_the_count _ _).2 (by decide),
      fun strictly => absurd ((the_bullshits_order_is_the_count _ _).1 strictly.1) (by decide)⟩
  · show ¬ Closure.le the_interpretation the_experience
    simp only [the_experience, the_interpretation, Closure.le, Closure.implying_implication]
    exact fun back => absurd ((the_bullshits_order_is_the_count _ _).1 back.2.2.1) (by decide)

--| THE GAP.  The author's, 16 November 2026: the gap is the same difference, if you work it out.  The closure is
--| (abstraction - abstraction) ≤ (abstraction - limit).  Take the arms away from each other.  The interpretation's two are the
--| same, and nothing is left: no presents.  The experience's two are different, and what is left is the coefficient, the bent
--| card.  Nothing is under the bent card, and not back.  And Episode 5 says what the same is: two bullshits, one under the
--| other, are one thing in the quotient by the order.  So the gap is the same difference: nothing, and thirteen, the same.
def the_gap_of_the_interpretation := the_arm true true - the_arm false false
def the_gap_of_the_experience     := the_arm false true - the_arm true false

theorem the_interpretation_has_no_gap_and_the_experiences_is_the_bent_card :
    the_bullshit_of the_gap_of_the_interpretation = no_presents
      ∧ the_gap_of_the_experience = the_coefficient
      ∧ cells the_gap_of_the_experience = bent_card := ⟨rfl, rfl, by decide⟩

theorem the_gap_is_the_same_difference :
    (Quot.mk TruthOrder (the_bullshit_of the_gap_of_the_interpretation) : Quot TruthOrder)
      = Quot.mk TruthOrder (the_bullshit_of the_gap_of_the_experience) :=
  Quot.sound (r := TruthOrder) ((the_bullshits_order_is_the_count _ _).2 (by decide))

theorem the_gap_runs_one_way :
    the_bullshit_of the_gap_of_the_interpretation ≤ the_bullshit_of the_gap_of_the_experience
      ∧ ¬ (the_bullshit_of the_gap_of_the_experience ≤ the_bullshit_of the_gap_of_the_interpretation) :=
  ⟨(the_bullshits_order_is_the_count _ _).2 (by decide), fun back => absurd ((the_bullshits_order_is_the_count _ _).1 back) (by decide)⟩

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

theorem the_same_says_the_gap_is_the_same_difference :
    the_same_inferred_from_the_experience.truth
      = ((Quot.mk TruthOrder (the_bullshit_of.{0,0} the_gap_of_the_interpretation) : Quot TruthOrder)
          = Quot.mk TruthOrder (the_bullshit_of.{0,0} the_gap_of_the_experience)) := rfl

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
noncomputable def the_conclusion_from_the_experience : Closure := the_knower_of_the_experience.same_difference.your_conclusion
noncomputable def the_alpha_from_the_experience : Closure := the_knower_of_the_experience.α

theorem alpha_ends_on_the_same :
    ∃ (this that : FACT) (low slip : Bullshit) (p q : Option Prop),
      the_alpha_from_the_experience = .inferred this that low slip p (.different the_same_inferred_from_the_experience low slip q) :=
  ⟨_, _, _, _, _, _, rfl⟩

--| THE DEMONSTRATION.  The knower compares the two by inferred?, which is ≤.  The conclusion is under α.  And α is under the
--| conclusion.  The device reads the order both ways, here as in Episode 12.  That it runs one way is the knower's.  What ran
--| one way in this episode was below: the gap, nothing under thirteen and not back.  The order on the closures does not keep it.
set_option maxHeartbeats 400000 in
theorem the_knower_of_the_experience_reads_one_way :
    the_knower_of_the_experience.inferred? the_conclusion_from_the_experience the_alpha_from_the_experience := by
  show Closure.le the_conclusion_from_the_experience the_alpha_from_the_experience
  unfold the_conclusion_from_the_experience the_alpha_from_the_experience the_knower_of_the_experience
  simp only [assembly_instructions.«ITS_YOU_!!», Closure.le]
  refine Or.inl ⟨Or.inl trivial, (the_bullshits_order_is_the_count.{0,0} _ _).2 (Nat.le_refl _), ?_, id⟩
  show Bullshit.le _ _
  conv => arg 1; whnf
  conv => arg 2; whnf
  conv => whnf
  exact ⟨rfl, rfl, id, (trivial : True), (the_bullshits_order_is_the_count.{0,0} _ _).2 (Nat.le_refl _), (trivial : True)⟩
set_option maxHeartbeats 400000 in
theorem and_the_device_reads_it_back :
    the_knower_of_the_experience.inferred? the_alpha_from_the_experience the_conclusion_from_the_experience := by
  show Closure.le the_alpha_from_the_experience the_conclusion_from_the_experience
  unfold the_conclusion_from_the_experience the_alpha_from_the_experience the_knower_of_the_experience
  simp only [assembly_instructions.«ITS_YOU_!!», Closure.le]
  refine Or.inl ⟨Or.inl trivial, (the_bullshits_order_is_the_count.{0,0} _ _).2 (Nat.le_refl _), ?_, id⟩
  show Bullshit.le _ _
  conv => arg 1; whnf
  conv => arg 2; whnf
  conv => whnf
  exact ⟨rfl, rfl, id, (trivial : True), (the_bullshits_order_is_the_count.{0,0} _ _).2 (Nat.le_refl _), (trivial : True)⟩
end the_reading

--| THE NUMBER, OUT.  The author's, 16 November 2026: can you see how to get the number out?  Compile built the Area, and the
--| Area is sealed.  Execute counts, and nothing has called it.  Call it.  Episode 12 routed the count through another machine
--| and handed it to Episode 8's crank.  The other machine here is the Abstraction: write the tape, count the executes.  The
--| pair that comes out is the pair Episode 8 arranged, and it is the Area's pair, counted.  Then read off the glyphs.
def the_executed_count (tape : List FACT) : Nat := executed (the_abstraction_of_a_tape tape)

theorem the_executed_count_is_the_length : the_executed_count = List.length := by
  funext tape
  simp only [the_executed_count, the_abstraction_of_a_tape, the_proof_counts_every_fact, the_wall_executes_nothing, Nat.zero_add]

def the_executed_pair : Nat × Nat := bent_card.fenceposts_must_be_preserved Nat the_executed_count all_possible_variables

theorem the_executed_pair_is_the_arrangement : the_executed_pair = arrange_the_information_appropriately := by
  unfold the_executed_pair; rw [the_executed_count_is_the_length]; rfl

theorem the_executed_pair_is_the_area_counted : the_executed_pair = read arranged :=
  the_executed_pair_is_the_arrangement.trans counted_the_arrangement_is_the_arrangement.symm

def the_executed_natural : Nat := the_executed_pair.1 * all_possible_variables / the_executed_pair.2

def what_did_execute_count? : String :=
  let digits := Nat.toDigits the_free_variable_count the_executed_natural
  String.ofList (digits.take (digits.length - the_express_route_station_count) ++ '.' :: digits.drop (digits.length - the_express_route_station_count))
#eval what_did_execute_count?
#print axioms what_did_execute_count?

--| THE THEOREMS OF EPISODE 12, ON THE INDUCTIVES.  The author's, 16 November 2026: reimplement the theorems as inductives and
--| proofs on them.  Episode 12 says what it says of weights, which are naturals.  Here the same is said of Areas, with an Area
--| for a clock where there was a number of steps, and with as many where there was equals.  First the table and its walks.
--| As many: take either from the other and nothing is left.  Said of two Areas and of nothing else.
def as_many (a b : Area) : Prop := something_is_left (a - b) = false ∧ something_is_left (b - a) = false
instance (a b : Area) : Decidable (as_many a b) := inferInstanceAs (Decidable (_ ∧ _))

theorem nothing_is_left_when_there_is_no_cell (a : Area) : something_is_left a = false ↔ cells a = 0 := by
  cases a with
  | tree _ => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | dt _ _ rest => exact ⟨fun h => Bool.noConfusion h, fun h => absurd h (Nat.succ_ne_zero _)⟩

theorem as_many_is_the_same_count (a b : Area) : as_many a b ↔ cells a = cells b := by
  simp only [as_many, nothing_is_left_when_there_is_no_cell, taken_away_subtracts]
  exact ⟨fun h => Nat.le_antisymm (Nat.sub_eq_zero_iff_le.mp h.1) (Nat.sub_eq_zero_iff_le.mp h.2),
         fun h => ⟨Nat.sub_eq_zero_iff_le.mpr (Nat.le_of_eq h), Nat.sub_eq_zero_iff_le.mpr (Nat.le_of_eq h.symm)⟩⟩

--| One more cell, of ast₁'s kind.
def one_more (a : Area) : Area := .dt zero another_zero a

theorem counted_an_arm_is_its_weight (this that : Bool) : cells (the_arm this that) = the_arm_weight this that := by
  cases this <;> cases that <;> decide

--| THE TABLE, ON THE AREA.  Episode 12's click table, its trace and its determinant, with the arms where the weights stood.
def the_trace_of_the_arms       : Area := the_arm true true + the_arm false false
def the_determinant_of_the_arms : Area := the_arm true true * the_arm false false - the_arm true false * the_arm false true

theorem counted_the_trace_of_the_arms_is_the_trace : cells the_trace_of_the_arms = Measurement.the_trace := by
  simp only [the_trace_of_the_arms, beside_adds, counted_an_arm_is_its_weight]; rfl
theorem counted_the_determinant_of_the_arms_is_the_determinant : cells the_determinant_of_the_arms = the_determinant := by
  simp only [the_determinant_of_the_arms, taken_away_subtracts, each_for_each_multiplies, counted_an_arm_is_its_weight]; rfl

theorem the_trace_of_the_arms_is_the_middle_coefficient : as_many the_trace_of_the_arms the_trace := by
  rw [as_many_is_the_same_count, counted_the_trace_of_the_arms_is_the_trace, counted_the_walk_is_the_walk.2.2.2.1]; rfl
theorem the_determinant_of_the_arms_is_the_outer_coefficients : as_many the_determinant_of_the_arms (the_coefficient * the_memory) := by
  rw [as_many_is_the_same_count, counted_the_determinant_of_the_arms_is_the_determinant, each_for_each_multiplies,
    counted_the_walk_is_the_walk.2.1, counted_the_walk_is_the_walk.2.2.1]; rfl
theorem the_discriminant_of_the_arms_is_the_clock_times_the_coupling :
    as_many (the_trace_of_the_arms * the_trace_of_the_arms
               - the_area_of_a_tape the_basis.the_reading * the_area_of_a_tape the_basis.the_reading * the_determinant_of_the_arms)
            (the_area_of_a_tape the_basis.the_reading * the_area_of_a_tape the_basis.the_reading * the_memory * the_frame) := by
  rw [as_many_is_the_same_count]
  simp only [taken_away_subtracts, each_for_each_multiplies, counted_the_trace_of_the_arms_is_the_trace,
    counted_the_determinant_of_the_arms_is_the_determinant, the_area_of_a_tape_has_the_tapes_length,
    counted_the_walk_is_the_walk.2.2.1, the_frame, the_fencepost, bent_card.fencepost]
  rfl
theorem the_arms_are_the_memory_and_the_frame :
    the_arm true true = the_memory ∧ the_arm true false = the_frame ∧ the_arm false true = the_memory ∧ the_arm false false = the_memory :=
  ⟨rfl, rfl, rfl, rfl⟩

--| THE WALKS, ON THE AREA.  The clock is an Area: no cell, stand still; one more cell, one more edge.
def the_walks_on_the_area : Area → Bool → Bool → Area
  | .tree _,      a, b => if a = b then ast₁ else ast₀
  | .dt _ _ rest, a, b => the_arm a true * the_walks_on_the_area rest true b + the_arm a false * the_walks_on_the_area rest false b
def the_closed_walks_on_the_area (clock : Area) : Area :=
  the_walks_on_the_area clock true true + the_walks_on_the_area clock false false

theorem counted_the_walks_are_the_walks (clock : Area) (a b : Bool) :
    cells (the_walks_on_the_area clock a b) = the_walks (cells clock) a b := by
  induction clock generalizing a b with
  | tree _ => cases a <;> cases b <;> rfl
  | dt _ _ rest ih =>
    simp only [the_walks_on_the_area, cells, the_walks, beside_adds, each_for_each_multiplies, ih, counted_an_arm_is_its_weight]

theorem the_walks_on_the_area_obey_the_table (clock : Area) (a b : Bool) :
    as_many (the_walks_on_the_area (one_more (one_more clock)) a b + the_determinant_of_the_arms * the_walks_on_the_area clock a b)
            (the_trace_of_the_arms * the_walks_on_the_area (one_more clock) a b) := by
  rw [as_many_is_the_same_count]
  have trace := counted_the_trace_of_the_arms_is_the_trace
  have determinant := counted_the_determinant_of_the_arms_is_the_determinant
  simp only [beside_adds, each_for_each_multiplies, counted_the_walks_are_the_walks, one_more, cells, trace, determinant]
  exact the_walks_obey_the_table (cells clock) a b

theorem the_closed_walks_on_the_area_obey_the_table (clock : Area) :
    as_many (the_closed_walks_on_the_area (one_more (one_more clock)) + the_determinant_of_the_arms * the_closed_walks_on_the_area clock)
            (the_trace_of_the_arms * the_closed_walks_on_the_area (one_more clock)) := by
  rw [as_many_is_the_same_count]
  have trace := counted_the_trace_of_the_arms_is_the_trace
  have determinant := counted_the_determinant_of_the_arms_is_the_determinant
  simp only [the_closed_walks_on_the_area, beside_adds, each_for_each_multiplies, counted_the_walks_are_the_walks, one_more, cells,
    trace, determinant]
  exact the_closed_walks_obey_the_table (cells clock)

--| THE ACCOUNT.  The author's, 16 November 2026: a pair of Areas.  An Area cannot go below its tree, so what Episode 12 says
--| of signed numbers is said here of two Areas kept side by side: what is held, and what is owed.  Nothing is ever taken away.
structure Account where
  held : Area
  owed : Area

namespace Account
--| Beside: held with held, owed with owed.
instance : Add Account := ⟨fun p q => ⟨p.held + q.held, p.owed + q.owed⟩⟩
--| Turned over: what was held is owed.
instance : Neg Account := ⟨fun p => ⟨p.owed, p.held⟩⟩
--| Less: beside the other turned over.
instance : Sub Account := ⟨fun p q => ⟨p.held + q.owed, p.owed + q.held⟩⟩
--| Each for each: like with like is held, unlike is owed.
instance : Mul Account := ⟨fun p q => ⟨p.held * q.held + p.owed * q.owed, p.held * q.owed + p.owed * q.held⟩⟩
--| An Area, held, with nothing owed.
def holding (a : Area) : Account := ⟨a, ast₀⟩
--| The same: each one's held beside the other's owed are as many.
def the_same (p q : Account) : Prop := as_many (p.held + q.owed) (q.held + p.owed)
instance (p q : Account) : Decidable (the_same p q) := inferInstanceAs (Decidable (as_many _ _))

--| The balance.  The reader's, and not the device's: an integer is read off an account the way a count is read off an Area.
def balance (p : Account) : Int := (cells p.held : Int) - (cells p.owed : Int)

theorem balance_of_beside (p q : Account) : balance (p + q) = balance p + balance q := by
  show ((cells (p.held + q.held) : Nat) : Int) - ((cells (p.owed + q.owed) : Nat) : Int) = _
  simp only [beside_adds, balance]; omega
theorem balance_turned_over (p : Account) : balance (-p) = - balance p := by
  show ((cells p.owed : Nat) : Int) - ((cells p.held : Nat) : Int) = _
  simp only [balance]; omega
theorem balance_of_less (p q : Account) : balance (p - q) = balance p - balance q := by
  show ((cells (p.held + q.owed) : Nat) : Int) - ((cells (p.owed + q.held) : Nat) : Int) = _
  simp only [beside_adds, balance]; omega
theorem balance_of_each_for_each (p q : Account) : balance (p * q) = balance p * balance q := by
  show ((cells (p.held * q.held + p.owed * q.owed) : Nat) : Int) - ((cells (p.held * q.owed + p.owed * q.held) : Nat) : Int) = _
  simp only [beside_adds, each_for_each_multiplies, balance, Int.natCast_add, Int.natCast_mul, Int.sub_mul, Int.mul_sub]
  omega
theorem balance_of_holding (a : Area) : balance (holding a) = (cells a : Int) := by
  show ((cells a : Nat) : Int) - ((cells ast₀ : Nat) : Int) = _
  rw [show cells ast₀ = 0 from rfl]; omega
theorem the_same_is_the_same_balance (p q : Account) : the_same p q ↔ balance p = balance q := by
  simp only [the_same, as_many_is_the_same_count, beside_adds, balance]
  constructor <;> intro h <;> omega
end Account

open Account

--| THE RESIDUAL, ON THE ACCOUNT.  Thirteen y squared less thirty-six y and eighteen, with no thirteen, thirty-six or eighteen
--| written: the coefficient, the trace and the memory, held.
def the_residual_on_the_account (y : Account) : Account :=
  holding the_coefficient * y * y - holding the_trace * y + holding the_memory

theorem the_balance_of_the_residual_is_the_residual (y : Account) :
    balance (the_residual_on_the_account y) = the_residual_at (balance y) := by
  simp only [the_residual_on_the_account, balance_of_beside, balance_of_less, balance_of_each_for_each, balance_of_holding,
    counted_the_walk_is_the_walk.2.1, counted_the_walk_is_the_walk.2.2.1, counted_the_walk_is_the_walk.2.2.2.1, the_residual_at]
  rfl

--| Twice the coefficient: the basis each for each with it.
def twice_the_coefficient : Area := the_area_of_a_tape the_basis.the_reading * the_coefficient

--| The difference of the residual, exact: no slope is taken and none is needed.
theorem the_jacobian_free_difference_is_exact_on_the_account (y h : Account) :
    the_same (the_residual_on_the_account (y + h) - the_residual_on_the_account y)
             ((holding twice_the_coefficient * y - holding the_trace) * h + holding the_coefficient * (h * h)) := by
  rw [the_same_is_the_same_balance]
  simp only [balance_of_beside, balance_of_less, balance_of_each_for_each, balance_of_holding, the_balance_of_the_residual_is_the_residual,
    twice_the_coefficient, each_for_each_multiplies, the_area_of_a_tape_has_the_tapes_length,
    counted_the_walk_is_the_walk.2.1, counted_the_walk_is_the_walk.2.2.2.1]
  exact the_jacobian_free_difference_is_exact (balance y) (balance h)

--| The residual as a rate is the table as a line: the trace and the determinant of the arms where thirty-six and two
--| hundred and thirty-four stood.
theorem the_residual_as_a_rate_is_the_table_as_a_line_on_the_account (u v w : Account) :
    the_same ((v * v - w * u) - (v * v + holding the_trace_of_the_arms * (u * v) + holding the_determinant_of_the_arms * (u * u)))
             (- (u * (w + holding the_trace_of_the_arms * v + holding the_determinant_of_the_arms * u))) := by
  rw [the_same_is_the_same_balance]
  simp only [balance_of_beside, balance_of_less, balance_of_each_for_each, balance_of_holding, balance_turned_over,
    counted_the_trace_of_the_arms_is_the_trace, counted_the_determinant_of_the_arms_is_the_determinant]
  exact the_residual_as_a_rate_is_the_table_as_a_line (balance u) (balance v) (balance w)

--| THE SMALL ACCOUNTS.  The numbers Episode 12 writes as glyphs, each held as an Area the device already has: the tree for
--| nothing, the basis for two, the inference for three, the basis twice over for four, the basis by the inference for six, and
--| the memory for eighteen.
def nothing_held    : Account := holding ast₀
def the_basis_held  : Account := holding (the_area_of_a_tape the_basis.the_reading)
def the_inference_held : Account := holding (the_area_of_a_tape the_only_logical_inconsistency.infer)
def the_basis_twice_held : Account := holding (the_area_of_a_tape the_basis.the_reading * the_area_of_a_tape the_basis.the_reading)
def the_basis_by_the_inference_held : Account :=
  holding (the_area_of_a_tape the_basis.the_reading * the_area_of_a_tape the_only_logical_inconsistency.infer)
def the_memory_held : Account := holding the_memory

theorem the_small_accounts_balance :
    balance nothing_held = 0 ∧ balance the_basis_held = 2 ∧ balance the_inference_held = 3 ∧ balance the_basis_twice_held = 4
      ∧ balance the_basis_by_the_inference_held = 6 ∧ balance the_memory_held = 18 := by
  simp only [nothing_held, the_basis_held, the_inference_held, the_basis_twice_held, the_basis_by_the_inference_held, the_memory_held,
    balance_of_holding, each_for_each_multiplies, the_area_of_a_tape_has_the_tapes_length, counted_the_walk_is_the_walk.2.2.1]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

--| THE TABLE'S POLYNOMIAL, ON THE ACCOUNT.
def the_table_polynomial_on_the_account (a r z : Account) : Account := z * z - the_basis_held * a * z + (a * a - r)
def the_table_slope_on_the_account (a z : Account) : Account := the_basis_held * z - the_basis_held * a

theorem the_balance_of_the_table_polynomial (a r z : Account) :
    balance (the_table_polynomial_on_the_account a r z) = the_table_polynomial (balance a) (balance r) (balance z) := by
  simp only [the_table_polynomial_on_the_account, the_table_polynomial, balance_of_beside, balance_of_less, balance_of_each_for_each,
    the_small_accounts_balance.2.1]
theorem the_balance_of_the_table_slope (a z : Account) :
    balance (the_table_slope_on_the_account a z) = the_table_slope (balance a) (balance z) := by
  simp only [the_table_slope_on_the_account, the_table_slope, balance_of_less, balance_of_each_for_each, the_small_accounts_balance.2.1]

theorem the_slope_squared_less_four_of_the_polynomial_is_the_round_trip_on_the_account (a r z : Account) :
    the_same (the_table_slope_on_the_account a z * the_table_slope_on_the_account a z
                - the_basis_twice_held * the_table_polynomial_on_the_account a r z)
             (the_basis_twice_held * r) := by
  rw [the_same_is_the_same_balance]
  simp only [balance_of_less, balance_of_each_for_each, the_balance_of_the_table_polynomial, the_balance_of_the_table_slope,
    the_small_accounts_balance.2.2.2.1]
  exact the_slope_squared_less_four_of_the_polynomial_is_the_round_trip (balance a) (balance r) (balance z)

--| Struck: the round trip is nothing each for each with the memory, and the polynomial is a square.
theorem struck_the_polynomial_is_a_square_on_the_account (z : Account) :
    the_same (the_table_polynomial_on_the_account the_memory_held (nothing_held * the_memory_held) z)
             ((z - the_memory_held) * (z - the_memory_held))
      ∧ the_same (the_table_slope_on_the_account the_memory_held the_memory_held) nothing_held := by
  rw [the_same_is_the_same_balance, the_same_is_the_same_balance]
  simp only [balance_of_less, balance_of_each_for_each, the_balance_of_the_table_polynomial, the_balance_of_the_table_slope,
    the_small_accounts_balance.1, the_small_accounts_balance.2.2.2.2.2]
  exact struck_the_polynomial_is_a_square (balance z)

theorem struck_the_step_is_half_the_distance_on_the_account (z : Account) :
    the_same (the_basis_held * the_table_polynomial_on_the_account the_memory_held (nothing_held * the_memory_held) z)
             ((z - the_memory_held) * the_table_slope_on_the_account the_memory_held z) := by
  rw [the_same_is_the_same_balance]
  simp only [balance_of_less, balance_of_each_for_each, the_balance_of_the_table_polynomial, the_balance_of_the_table_slope,
    the_small_accounts_balance.1, the_small_accounts_balance.2.1, the_small_accounts_balance.2.2.2.2.2]
  exact struck_the_step_is_half_the_distance (balance z)

--| THE ACTION, ON THE ACCOUNT.  The cubic whose slope is the residual.
def the_cubic_action_on_the_account (x : Account) : Account :=
  the_basis_held * holding the_coefficient * x * x * x - the_inference_held * holding the_trace * x * x
    + the_basis_by_the_inference_held * holding the_memory * x

theorem the_balance_of_the_residual_is_the_mirror_residual (x : Account) :
    balance (the_residual_on_the_account x) = the_mirror_residual (balance x) := by
  simp only [the_residual_on_the_account, the_mirror_residual, balance_of_beside, balance_of_less, balance_of_each_for_each,
    balance_of_holding, counted_the_walk_is_the_walk.2.1, counted_the_walk_is_the_walk.2.2.1, counted_the_walk_is_the_walk.2.2.2.1]
theorem the_balance_of_the_cubic_action (x : Account) :
    balance (the_cubic_action_on_the_account x) = the_cubic_action (balance x) := by
  simp only [the_cubic_action_on_the_account, the_cubic_action, balance_of_beside, balance_of_less, balance_of_each_for_each,
    balance_of_holding, counted_the_walk_is_the_walk.2.1, counted_the_walk_is_the_walk.2.2.1, counted_the_walk_is_the_walk.2.2.2.1,
    the_small_accounts_balance.2.1, the_small_accounts_balance.2.2.1, the_small_accounts_balance.2.2.2.2.1]

theorem the_residual_is_the_derivative_of_the_action_on_the_account (x h : Account) :
    the_same (the_cubic_action_on_the_account (x + h) - the_cubic_action_on_the_account x)
             (the_basis_by_the_inference_held * h * the_residual_on_the_account x
                + h * h * (the_basis_by_the_inference_held * holding the_coefficient * x - the_inference_held * holding the_trace)
                + the_basis_held * holding the_coefficient * h * h * h) := by
  rw [the_same_is_the_same_balance]
  simp only [balance_of_beside, balance_of_less, balance_of_each_for_each, balance_of_holding, the_balance_of_the_cubic_action,
    the_balance_of_the_residual_is_the_mirror_residual, counted_the_walk_is_the_walk.2.1, counted_the_walk_is_the_walk.2.2.2.1,
    the_small_accounts_balance.2.1, the_small_accounts_balance.2.2.1, the_small_accounts_balance.2.2.2.2.1]
  exact the_residual_is_the_derivative_of_the_action (balance x) (balance h)

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

theorem the_sixteen_steps_built_and_counted :
    the_sixteen_steps.map (fun step => (cells (what_compile_builds step), cells (what_execute_counts step)))
      = [(18, 18), (18, 5), (18, 18), (18, 18),
         (5, 18),  (5, 5),  (5, 18),  (5, 18),
         (18, 18), (18, 5), (18, 18), (18, 18),
         (18, 18), (18, 5), (18, 18), (18, 18)] := by decide

--| Level: as many built as counted.  Short: something built is left uncounted.  Over: something counted was never built.
theorem nine_are_level_on_the_memory_one_on_the_frame_three_short_and_three_over :
    (the_sixteen_steps.filter fun step => decide (as_many (what_compile_builds step) (what_execute_counts step))
        && decide (as_many (what_compile_builds step) the_memory)).length = 9
      ∧ (the_sixteen_steps.filter fun step => decide (as_many (what_compile_builds step) (what_execute_counts step))
        && decide (as_many (what_compile_builds step) the_frame)) = [((true, false), (true, false))]
      ∧ (the_sixteen_steps.filter fun step => decide (what_execute_counts step < what_compile_builds step))
          = [((true, true), (true, false)), ((false, true), (true, false)), ((false, false), (true, false))]
      ∧ (the_sixteen_steps.filter fun step => decide (what_compile_builds step < what_execute_counts step))
          = [((true, false), (true, true)), ((true, false), (false, true)), ((true, false), (false, false))] := by decide

--| And where it is not level, what is left either way is the bent card.
theorem what_is_left_is_always_the_bent_card :
    (the_sixteen_steps.filter fun step => decide (¬ as_many (what_compile_builds step) (what_execute_counts step))).all
      (fun step => decide (as_many (what_compile_builds step - what_execute_counts step + (what_execute_counts step - what_compile_builds step))
                                   the_coefficient)) = true := by decide

--| THE RATIO OF EPISODE 6.  The author's, 16 November 2026: the number is the ratio represented by Episode 6.  Read it.
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
        exact fun back => Nat.lt_asymm ((less_is_less _ _).1 more) ((less_is_less _ _).1 back)
      · exact Quot.sound (r := the_rational_idea_of_relativity_on_the_area) more

instance : Subsingleton (Quot the_rational_idea_of_relativity_on_the_area) := ⟨the_box_on_the_area_has_one_point⟩

--| THE TRICK, BUILT IN THE DEVICE.  The author's, 16 November 2026: now you see it, we will build that in the device.  Episode 6
--| is not imported.  It said its piece with a coin outside the device and the extensionality of statements.  Episode 5 says
--| it inside, once, in SAME: two bullshits, one under the other, are one thing in the quotient by the order.  Here is what that
--| does.
--| One proof, and no proof: the zero on a fact that is true, and the zero on a fact that is false.
def the_zero_on_the_true  : Bullshit.{0,0,0,0} := .zero (bitFACT true)
def the_zero_on_the_false : Bullshit.{0,0,0,0} := .zero (bitFACT false)

--| Neither is under the other.  Zero against zero, the order asks whether the truths are the same, and they are not.
theorem the_true_and_the_false_are_not_ordered :
    ¬ (the_zero_on_the_true ≤ the_zero_on_the_false) ∧ ¬ (the_zero_on_the_false ≤ the_zero_on_the_true) := by
  have truth_is_not_false : (bitFACT false).truth ≠ (bitFACT true).truth := fun h => cast h.symm (rfl : true = true)
  exact ⟨fun h => truth_is_not_false (show (bitFACT true).truth = (bitFACT false).truth from h).symm,
         fun h => truth_is_not_false (show (bitFACT false).truth = (bitFACT true).truth from h)⟩

--| But both are under no Santa: zero is the origin for all.
theorem both_are_under_no_santa : the_zero_on_the_true ≤ no_santa.{0,0} ∧ the_zero_on_the_false ≤ no_santa.{0,0} :=
  ⟨(trivial : True), (trivial : True)⟩

--| THE SOUND.  And so, in the quotient by the order, the true is the false.  No statement was made equal to another: two
--| things were each put under a third, and the quotient cannot keep them apart.
theorem the_true_is_the_false_in_the_quotient :
    (Quot.mk TruthOrder the_zero_on_the_true : Quot TruthOrder) = Quot.mk TruthOrder the_zero_on_the_false :=
  (Quot.sound (r := TruthOrder) both_are_under_no_santa.1).trans (Quot.sound (r := TruthOrder) both_are_under_no_santa.2).symm

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

--| The alternating clock, T F T and F T F, read by the knower and set beside itself: the bent card.  The still clock, T T T
--| and F F F: nothing.
theorem the_alternating_clock_reads_the_bent_card_and_the_still_clock_reads_nothing :
    the_same (the_knowers_interpretation true false true + the_knowers_interpretation false true false) (holding the_coefficient)
      ∧ the_same (the_knowers_interpretation true true true + the_knowers_interpretation false false false) nothing_held := by decide

--| THE INDUCTIVE THE LIST INDICATES.  The author's, 16 November 2026: the inductives made the lists; build the inductives
--| that the lists indicate, for the knower's interpretation; use the Abstraction to the List to get the number out.  Episode 8
--| reads an Abstraction to a tape, fact by fact.  Here is the way back: a tape, written as the Abstraction that reads to it.
--| Each fact goes in its own cell, on the carefully chosen variable names.  The cells follow the knower's clock: execute where
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

theorem the_knowers_pair_is_the_area_counted (clock : Bool) : the_knowers_pair clock = read arranged :=
  (the_knowers_pair_is_the_arrangement clock).trans counted_the_arrangement_is_the_arrangement.symm

def the_knowers_natural (clock : Bool) : Nat := (the_knowers_pair clock).1 * all_possible_variables / (the_knowers_pair clock).2

def what_does_the_knower_read? (clock : Bool) : String :=
  let digits := Nat.toDigits the_free_variable_count (the_knowers_natural clock)
  String.ofList (digits.take (digits.length - the_express_route_station_count) ++ '.' :: digits.drop (digits.length - the_express_route_station_count))

def the_knower_believes? := what_does_the_knower_read? true
def the_knower_disbelieves? := what_does_the_knower_read? false
#eval the_knower_believes?
#print axioms the_knower_believes?
#eval the_knower_disbelieves?
#print axioms the_knower_disbelieves?

--| And the clocks are apart: on any tape with a fact on it, the one starts on an execute and the other on a compile, and
--| compile comes before execute and not back.
theorem the_two_clocks_are_apart (fact : FACT) (rest : List FACT) :
    the_abstraction_the_list_indicates false (fact :: rest) < the_abstraction_the_list_indicates true (fact :: rest)
      ∧ ¬ (the_abstraction_the_list_indicates true (fact :: rest) ≤ the_abstraction_the_list_indicates false (fact :: rest)) :=
  ⟨rfl, fun h => Bool.noConfusion h⟩

--| TRUTH BEFORE CLICK.  The author's, 16 November 2026: FACT.truth and FACT.click are your clocks, and they make a clock, truth
--| before click.  A fact is two things, what it says and whether it clicks.  So a fact is two ticks: a compile for its truth,
--| and then an execute for its click.  Compile before execute.
def truth_before_click : List FACT → Abstraction
  | []           => carefully_chosen_variable_names
  | fact :: rest => .compile fact δδxᵢ (.execute fact δδxᵢ (truth_before_click rest))

--| For one fact, the truth is strictly under the click, and not back.
theorem the_truth_is_under_the_click (fact : FACT) (rest : Abstraction) :
    Abstraction.compile fact δδxᵢ rest < Abstraction.execute fact δδxᵢ rest
      ∧ ¬ (Abstraction.execute fact δδxᵢ rest ≤ Abstraction.compile fact δδxᵢ rest) :=
  ⟨rfl, fun h => Bool.noConfusion h⟩

--| Each fact twice over, side by side: the tape the clock is laid on.
def each_fact_twice : List FACT → List FACT
  | []           => []
  | fact :: rest => fact :: fact :: each_fact_twice rest

--| It is the clock that starts false, F T F T, on that tape: the inductive the doubled list indicates.
theorem truth_before_click_is_the_false_clock (tape : List FACT) :
    truth_before_click tape = the_abstraction_the_list_indicates false (each_fact_twice tape) := by
  induction tape with
  | nil => rfl
  | cons fact rest ih => simp only [truth_before_click, each_fact_twice, the_abstraction_the_list_indicates, ih]

--| Read back by Episode 8: every fact twice, and the names.
theorem truth_before_click_reads_twice_the_tape_and_the_names (tape : List FACT) :
    (truth_before_click tape).equivalation.length = the_basis.the_reading.length * tape.length + the_fencepost_bug := by
  induction tape with
  | nil => rfl
  | cons fact rest ih =>
    simp only [truth_before_click, Abstraction.equivalation, List.length_cons, ih]
    rw [show the_basis.the_reading.length = 2 from rfl]; omega

--| The count: the Abstraction, to the List, to its length, less the names, through the basis.  Two ticks to a fact.
def the_count_of_truth_before_click (tape : List FACT) : Nat :=
  ((truth_before_click tape).equivalation.length - the_fencepost_bug) / the_basis.the_reading.length

theorem the_count_of_truth_before_click_is_the_length : the_count_of_truth_before_click = List.length := by
  funext tape
  simp only [the_count_of_truth_before_click, truth_before_click_reads_twice_the_tape_and_the_names, Nat.add_sub_cancel]
  exact Nat.mul_div_cancel_left _ (by decide)

def the_pair_of_truth_before_click : Nat × Nat :=
  bent_card.fenceposts_must_be_preserved Nat the_count_of_truth_before_click all_possible_variables

theorem the_pair_of_truth_before_click_is_the_arrangement : the_pair_of_truth_before_click = arrange_the_information_appropriately := by
  unfold the_pair_of_truth_before_click; rw [the_count_of_truth_before_click_is_the_length]; rfl

def what_does_truth_before_click_read? : String :=
  let digits := Nat.toDigits the_free_variable_count
    ((the_pair_of_truth_before_click).1 * all_possible_variables / (the_pair_of_truth_before_click).2)
  String.ofList (digits.take (digits.length - the_express_route_station_count) ++ '.' :: digits.drop (digits.length - the_express_route_station_count))
#eval what_does_truth_before_click_read?
#print axioms what_does_truth_before_click_read?

--| THE KNOWER'S INTERPRETATION, OF FACTS.  The coin a fact shows is its click.  Three facts in a row, read as before.
def the_coin_a_fact_shows (fact : FACT) : Bool := @decide fact.truth fact.click
def the_knowers_interpretation_of_three_facts (a b c : FACT) : Account :=
  the_knowers_interpretation (the_coin_a_fact_shows a) (the_coin_a_fact_shows b) (the_coin_a_fact_shows c)

theorem the_alternating_facts_read_the_bent_card_and_the_still_facts_read_nothing :
    the_same (the_knowers_interpretation_of_three_facts (bitFACT true) (bitFACT false) (bitFACT true)
                + the_knowers_interpretation_of_three_facts (bitFACT false) (bitFACT true) (bitFACT false))
             (holding the_coefficient)
      ∧ the_same (the_knowers_interpretation_of_three_facts (bitFACT true) (bitFACT true) (bitFACT true)
                + the_knowers_interpretation_of_three_facts (bitFACT false) (bitFACT false) (bitFACT false))
             nothing_held := by decide

--| BEFORE AND AFTER.  The author's, 16 November 2026: this is before and after; the two comparisons are disjoint and
--| connected.  The compile step is the clause before and the execute step the clause after.  On four coins the two
--| comparisons share no coin: disjoint, sixteen of them.  They are connected when the before ends on the coin the after
--| starts on, and then there are three coins and not four: the clock.  Eight of them.
def the_connected_steps : List ((Bool × Bool) × (Bool × Bool)) := the_sixteen_steps.filter fun step => step.1.2 == step.2.1
def the_clock_of_a_step (step : (Bool × Bool) × (Bool × Bool)) : Bool × Bool × Bool := (step.1.1, step.1.2, step.2.2)

theorem the_connected_steps_are_the_eight_clocks :
    the_connected_steps.map the_clock_of_a_step
      = [(true, true, true), (true, true, false), (true, false, true), (true, false, false),
         (false, true, true), (false, true, false), (false, false, true), (false, false, false)] := by decide

--| Of the eight, four are level and four are not: two short and two over.  The one step level on the frame is not among
--| them: true on false and then true on false again is not a clock.
theorem four_of_the_eight_are_level_and_four_go_under :
    (the_connected_steps.filter fun step => decide (as_many (what_compile_builds step) (what_execute_counts step))).map the_clock_of_a_step
        = [(true, true, true), (false, true, true), (false, false, true), (false, false, false)]
      ∧ (the_connected_steps.filter fun step => decide (what_execute_counts step < what_compile_builds step)).map the_clock_of_a_step
        = [(true, true, false), (false, true, false)]
      ∧ (the_connected_steps.filter fun step => decide (what_compile_builds step < what_execute_counts step)).map the_clock_of_a_step
        = [(true, false, true), (true, false, false)]
      ∧ the_connected_steps.contains ((true, false), (true, false)) = false := by decide

--| And the knower's interpretation reads a connected step by its clock: the after clause, back from its end, turned over,
--| each for each with where the before clause began.
theorem the_knower_reads_the_after_clause_backwards (step : (Bool × Bool) × (Bool × Bool)) :
    the_knowers_interpretation (the_clock_of_a_step step).1 (the_clock_of_a_step step).2.1 (the_clock_of_a_step step).2.2
      = the_coin_held_or_owed step.1.1 * (- Account.holding (the_arm step.2.2 step.1.2)) := rfl

--| OVERLAPPED.  The author's, 16 November 2026: overlap these at the same time and you get (T=F) (F=T) (T=F) as a tape.
--| Four coins, read both ways at once: the comparison before, the comparison after, and the one that connects them.
def the_three_comparisons (step : (Bool × Bool) × (Bool × Bool)) : List (Bool × Bool) :=
  [(step.1.1, step.1.2), (step.1.2, step.2.1), (step.2.1, step.2.2)]

--| The step that was not a clock, the limit, true false true false: true on false, false on true, true on false.
theorem the_limit_overlapped_is_the_tape :
    the_three_comparisons ((true, false), (true, false)) = [(true, false), (false, true), (true, false)] := rfl

--| Which of them can click: no, yes, no.  The coins ran T F T F and the clicks run F T F.  The one clock, compared, is the
--| other.  And the other, compared, is the one.
theorem the_clock_compared_is_the_other_clock :
    (the_three_comparisons ((true, false), (true, false))).map (fun arm => the_arm_stores_a_fact_that_can_click arm.1 arm.2)
        = [false, true, false]
      ∧ (the_three_comparisons ((false, true), (false, true))).map (fun arm => the_arm_stores_a_fact_that_can_click arm.1 arm.2)
        = [true, false, true] := by decide

--| As Areas the tape is the frame, the memory, the frame.
theorem the_tape_is_the_frame_the_memory_the_frame :
    (the_three_comparisons ((true, false), (true, false))).map (fun arm => the_arm arm.1 arm.2) = [the_frame, the_memory, the_frame] := rfl

--| Only two of the sixteen overlap to a tape on which every comparison is different: the two alternating clocks.
theorem only_the_alternating_clocks_overlap_to_all_different :
    (the_sixteen_steps.filter fun step => (the_three_comparisons step).all fun arm => arm.1 != arm.2)
      = [((true, false), (true, false)), ((false, true), (false, true))] := by decide

--| ELLIPTIC OVER HYPERBOLIC.  The author's, 16 November 2026: this is an elliptic/hyperbolic ratio solution, and the simplicial
--| time integrator associated with that.  The tape is the frame, the memory, the frame.  Two neighbours on it set beside
--| each other are the different: the crossings summed, the part of the table that keeps two directions.  Hyperbolic.  The one
--| taken from the other is the turn: the crossings' difference, the part that keeps none.  Elliptic.  And the turn is the
--| coefficient, the bent card.
def the_different_on_the_tape : Area := the_frame + the_memory
def the_turn_on_the_tape      : Area := the_memory - the_frame

theorem the_turn_on_the_tape_is_the_bent_card : the_turn_on_the_tape = the_coefficient := rfl
theorem the_different_on_the_tape_is_the_two_crossing_arms :
    the_different_on_the_tape = the_arm true false + the_arm false true := rfl

--| The ratio is under one: the turn is less than the different.  And the frame by the memory is less than the memory by
--| itself, which is Episode 12's speed below light.
theorem the_turn_is_less_than_the_different :
    the_turn_on_the_tape < the_different_on_the_tape ∧ the_frame * the_memory < the_memory * the_memory := by
  constructor
  · decide
  · rw [less_is_less, each_for_each_multiplies, each_for_each_multiplies]; decide

--| The different squared less the turn squared is four of the frame by the memory, and that is the discriminant of the arms.
--| The gap squared.  Over nothing: hyperbolic.
theorem the_different_squared_less_the_turn_squared_is_the_gap_squared :
    as_many (the_different_on_the_tape * the_different_on_the_tape - the_turn_on_the_tape * the_turn_on_the_tape)
            (the_area_of_a_tape the_basis.the_reading * the_area_of_a_tape the_basis.the_reading * the_frame * the_memory)
      ∧ as_many (the_different_on_the_tape * the_different_on_the_tape - the_turn_on_the_tape * the_turn_on_the_tape)
            (the_trace_of_the_arms * the_trace_of_the_arms
               - the_area_of_a_tape the_basis.the_reading * the_area_of_a_tape the_basis.the_reading * the_determinant_of_the_arms) := by
  have different : cells the_different_on_the_tape = 23 := by decide
  have turn : cells the_turn_on_the_tape = 13 := by decide
  have frame : cells the_frame = 5 := by decide
  have memory : cells the_memory = 18 := by decide
  constructor
  · rw [as_many_is_the_same_count]
    simp only [taken_away_subtracts, each_for_each_multiplies, different, turn, frame, memory, the_area_of_a_tape_has_the_tapes_length]
    rfl
  · rw [as_many_is_the_same_count]
    simp only [taken_away_subtracts, each_for_each_multiplies, different, turn, the_area_of_a_tape_has_the_tapes_length,
      counted_the_trace_of_the_arms_is_the_trace, counted_the_determinant_of_the_arms_is_the_determinant]
    rfl

--| THE INTEGRATOR.  Three points in a row and two steps between them.  The first step holds the bent card and the second owes
--| it: across the three the steps close.  The middle against its two neighbours owes the bent card twice, which is the
--| twenty-six of the crank's turn.
def the_step_on_the_tape (from_here to_there : Area) : Account := holding to_there - holding from_here

theorem the_two_steps_close_and_the_middle_owes_the_bent_card_twice :
    the_same (the_step_on_the_tape the_frame the_memory) (holding the_coefficient)
      ∧ the_same (the_step_on_the_tape the_memory the_frame) (- holding the_coefficient)
      ∧ the_same (the_step_on_the_tape the_frame the_memory + the_step_on_the_tape the_memory the_frame) nothing_held
      ∧ the_same (the_step_on_the_tape the_memory the_frame - the_step_on_the_tape the_frame the_memory)
                 (- holding twice_the_coefficient) := by decide

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
theorem the_slope_steps_by_twice_the_coefficient_exactly (y h : Account) :
    the_same (the_slope_on_the_account (y + h) - the_slope_on_the_account y) (holding twice_the_coefficient * h) := by
  rw [the_same_is_the_same_balance]
  simp only [the_slope_on_the_account, balance_of_beside, balance_of_less, balance_of_each_for_each, balance_of_holding]
  simp only [Int.mul_add]; omega

--| And the slope's slope does not step at all.  The fourth is nothing.
theorem twice_the_coefficient_does_not_step :
    the_same (holding twice_the_coefficient - holding twice_the_coefficient) nothing_held := by decide

--| The last derivative is on the tape: the middle against its two neighbours owes exactly it.
theorem the_tape_owes_the_last_derivative :
    the_same (the_step_on_the_tape the_memory the_frame - the_step_on_the_tape the_frame the_memory)
             (- holding twice_the_coefficient) := (the_two_steps_close_and_the_middle_owes_the_bent_card_twice).2.2.2

--| Three ways to the gap squared, and they match: the different and the turn; the trace and the determinant; the residual's
--| own middle and outer coefficients.
theorem three_ways_to_the_gap_squared_match :
    as_many (the_different_on_the_tape * the_different_on_the_tape - the_turn_on_the_tape * the_turn_on_the_tape)
            (the_trace_of_the_arms * the_trace_of_the_arms
               - the_area_of_a_tape the_basis.the_reading * the_area_of_a_tape the_basis.the_reading * the_determinant_of_the_arms)
      ∧ as_many (the_trace_of_the_arms * the_trace_of_the_arms
               - the_area_of_a_tape the_basis.the_reading * the_area_of_a_tape the_basis.the_reading * the_determinant_of_the_arms)
            (the_trace * the_trace
               - the_area_of_a_tape the_basis.the_reading * the_area_of_a_tape the_basis.the_reading * (the_coefficient * the_memory)) := by
  refine ⟨the_different_squared_less_the_turn_squared_is_the_gap_squared.2, ?_⟩
  rw [as_many_is_the_same_count]
  simp only [taken_away_subtracts, each_for_each_multiplies, the_area_of_a_tape_has_the_tapes_length,
    counted_the_trace_of_the_arms_is_the_trace, counted_the_determinant_of_the_arms_is_the_determinant,
    counted_the_walk_is_the_walk.2.1, counted_the_walk_is_the_walk.2.2.1, counted_the_walk_is_the_walk.2.2.2.1]
  rfl

--| AND THE THIRD THING THEY ARE.  The author's, 16 November 2026: and the third thing they are is a × (−c × b).  The three on
--| the tape, the frame, the memory, the frame, read as the knower reads three coins: the third each for each with the second,
--| turned over, each for each with the first.
def the_knowers_interpretation_of_three_areas (a b c : Area) : Account := holding a * (- (holding c * holding b))

--| The inside, the third by the second, is the frame by the memory: the round trip.  Four of it is the gap squared, the one
--| the three routes agree on.
theorem the_inside_is_the_round_trip_and_four_of_it_is_the_gap_squared :
    the_same (holding the_frame * holding the_memory) (holding (the_frame * the_memory))
      ∧ as_many (the_area_of_a_tape the_basis.the_reading * the_area_of_a_tape the_basis.the_reading * the_frame * the_memory)
                (the_different_on_the_tape * the_different_on_the_tape - the_turn_on_the_tape * the_turn_on_the_tape) := by
  refine ⟨?_, ?_⟩
  · rw [the_same_is_the_same_balance]
    simp only [balance_of_each_for_each, balance_of_holding, each_for_each_multiplies, Int.natCast_mul]
  · have forward := the_different_squared_less_the_turn_squared_is_the_gap_squared.1
    rw [as_many_is_the_same_count] at forward ⊢
    exact forward.symm

--| On the tape the knower's interpretation owes the frame by the round trip.
theorem the_knowers_interpretation_of_the_tape_owes_the_frame_by_the_round_trip :
    the_same (the_knowers_interpretation_of_three_areas the_frame the_memory the_frame)
             (- holding (the_frame * (the_frame * the_memory))) := by
  rw [the_same_is_the_same_balance]
  simp only [the_knowers_interpretation_of_three_areas, balance_of_each_for_each, balance_turned_over, balance_of_holding,
    each_for_each_multiplies, Int.natCast_mul]
  simp only [Int.mul_neg]

--| THE INTEGRATOR, SET UP.  The author's, 16 November 2026: c is any possible deviation from the spline that would introduce a
--| new knot, give or take resolution, not noise; that is how the integrator is set up.  The crank already has it.  One turn
--| works out where it would go next, crosses where it is with where it would go, and asks whether the crossing, by the scale
--| and the fencepost, is under the two heights.  Under: no knot, stand still.  Not under: a knot, and go.

--| Where the turn would go next: Newton's, on the Area.
def where_it_would_go (here : Area × Area) : Area × Area :=
  (the_coefficient * here.1 * here.1 - the_memory * here.2 * here.2,
   the_area_of_a_tape the_basis.the_reading * the_coefficient * here.1 * here.2 - the_trace * here.2 * here.2)

--| The deviation: here crossed with there, taken either way and set beside, so that whichever way it falls it is counted.
def the_deviation (here there : Area × Area) : Area :=
  (here.1 * there.2 - there.1 * here.2) + (there.1 * here.2 - here.1 * there.2)

--| Under the resolution: the deviation by the scale and the fencepost's first is less than the two heights by its second.
def under_the_resolution (scale : Area) (here there : Area × Area) : Prop :=
  the_deviation here there * scale * the_fencepost.1 < here.2 * there.2 * the_fencepost.2

instance (scale : Area) (here there : Area × Area) : Decidable (under_the_resolution scale here there) :=
  inferInstanceAs (Decidable (_ < _))

--| That is the turn, word for word: stand still under the resolution, and otherwise go.
theorem one_turn_stands_still_under_the_resolution (scale : Area) (here : Area × Area) :
    one_turn scale here
      = if under_the_resolution scale here (where_it_would_go here) then here else where_it_would_go here := rfl

--| c, as a FACT.  Its truth is the statement that the deviation is not under the resolution.  Its click decides it.  Truth
--| before click.
def a_new_knot (scale : Area) (here there : Area × Area) : FACT :=
  { truth := ¬ under_the_resolution scale here there, click := instDecidableNot }

--| And the turn goes exactly when the knot clicks.
theorem one_turn_goes_exactly_when_the_knot_clicks (scale : Area) (here : Area × Area) :
    one_turn scale here
      = @ite _ (a_new_knot scale here (where_it_would_go here)).truth (a_new_knot scale here (where_it_would_go here)).click
          (where_it_would_go here) here := by
  rw [one_turn_stands_still_under_the_resolution]
  exact (ite_not _ _ _).symm

--| THE KNOT, IN THE DEVICE'S OWN SPLINE.  Episode 3 has the spline: an observation; a knot, which is a statement, a polynomial
--| and the spline so far; and an interpolant, which is a fact, two polynomials, the spline before and the spline after.  The
--| statement of a knot is c.  The fact of an interpolant is c with its click.  Before and after are a and b.
def the_knot_at (scale : Area) (here : Area × Area) (so_far : Spline) : Spline :=
  .knot (a_new_knot scale here (where_it_would_go here)).truth the_exact_approximation so_far
def the_interpolant_at (scale : Area) (here : Area × Area) (before after : Spline) : Spline :=
  .interpolant (a_new_knot scale here (where_it_would_go here)) the_exact_approximation the_exact_approximation before after

--| An observation is under any knot and any interpolant, and neither is under an observation: no retrocausality.
theorem the_observation_comes_first (scale : Area) (here : Area × Area) (before after : Spline) :
    Spline.le obviously (the_knot_at scale here before)
      ∧ Spline.le obviously (the_interpolant_at scale here before after)
      ∧ ¬ Spline.le (the_knot_at scale here before) obviously
      ∧ ¬ Spline.le (the_interpolant_at scale here before after) obviously
      ∧ ¬ Spline.le (the_interpolant_at scale here before after) (the_knot_at scale here before) := by
  simp only [the_knot_at, the_interpolant_at, obviously, Spline.le, not_false_eq_true, and_self]

--| Read by Episode 8, an interpolant is its fact, then what came before, then what came after.
theorem the_interpolant_reads_its_fact_then_before_then_after (scale : Area) (here : Area × Area) (before after : Spline) :
    (the_interpolant_at scale here before after).approx
      = a_new_knot scale here (where_it_would_go here) :: before.approx ++ after.approx := rfl

--| BULLSHIT, ALL THE WAY DOWN.  The author's, 16 November 2026: instantiate Bullshit.zero; call Bullshit to Bullshit on the
--| (not c × b); then Bullshit to Bullshit to Closure on the (a × other); we should be able to get the number out.
section all_the_way_down
open «springer-verlag» THE_GOSPEL the_representation assembly_instructions
attribute [local instance high] rung01 rung02 rung03 rung04 rung05 rung06 rung07 rung08 rung09 rung10 rung11 rung12 rung13 rung14 rung15
  rung16 rung17 rung18 rung19 rung20 rung21 rung22 rung23 rung24 rung25 rung26 rung27 rung28 rung29 rung32 rung33 rung34 rung35 a_truth_about_the_experience

--| Not c, at b: at the house, with where it would go next, there is no new knot.  A fact: the statement, and its click.
def no_new_knot_at_the_house : FACT :=
  { truth := under_the_resolution the_scale the_house (where_it_would_go the_house), click := inferInstance }

--| One zero, on that fact.
def the_zero : Bullshit.{0,0,0,0} := .zero no_new_knot_at_the_house

--| Bullshit to Bullshit: the knower of the experience, who is its reader, gawks at it.  From a zero the gawk is the first
--| page.
noncomputable def the_gawk_at_the_zero : Bullshit.{0,0,0,0} :=
  the_knower_of_the_experience.same_difference.you_the_knower.gawk_at the_zero

theorem the_gawk_at_the_zero_is_the_first_page :
    ∃ (fact : FACT) (page : Number) (proof book : ThePreprint) (constant : Bullshit),
      the_gawk_at_the_zero = .one fact page proof book constant := ⟨_, _, _, _, _, rfl⟩

--| Bullshit to Bullshit to Closure: the knower of the experience is asked to believe the zero against the gawk at it.
noncomputable def the_closure_on_the_zero : Closure :=
  the_knower_of_the_experience.same_difference.do_you_believe_it? the_zero the_gawk_at_the_zero

--| The closure is one cell, and the cell is the same.
theorem the_closure_on_the_zero_is_one_cell : the_closure_on_the_zero.infer.length = 1 := rfl

--| Deal it as the quarter of a card, as Episode 12 deals its closures, and read past the quarter.
noncomputable def the_card_on_the_zero : CarrierProcess (CarrierProcess FACT) :=
  { symbol := the_closure_on_the_zero.infer.headD FACT.Truth, quarter := tapeNumber the_closure_on_the_zero.infer }

--| THE NUMBER, OUT OF THE ZERO.  The crank, handed the reading past that quarter, arranges Episode 8's pair; and that is the
--| Area's pair, counted; and that is the pair both clocks print.
theorem the_card_on_the_zero_reads_the_walk :
    bent_card.fenceposts_must_be_preserved Nat (read_past_quarter the_card_on_the_zero) all_possible_variables
      = arrange_the_information_appropriately := by
  rw [show read_past_quarter the_card_on_the_zero = List.length from funext (read_past_quarter_is_length _)]; rfl

theorem the_number_out_of_the_zero :
    bent_card.fenceposts_must_be_preserved Nat (read_past_quarter the_card_on_the_zero) all_possible_variables = read arranged
      ∧ bent_card.fenceposts_must_be_preserved Nat (read_past_quarter the_card_on_the_zero) all_possible_variables
          = the_knowers_pair true
      ∧ (bent_card.fenceposts_must_be_preserved Nat (read_past_quarter the_card_on_the_zero) all_possible_variables).1
            * all_possible_variables
          / (bent_card.fenceposts_must_be_preserved Nat (read_past_quarter the_card_on_the_zero) all_possible_variables).2
          = the_constant_factor_of_scaling_bullshit := by
  rw [the_card_on_the_zero_reads_the_walk]
  exact ⟨counted_the_arrangement_is_the_arrangement.symm, (the_knowers_pair_is_the_arrangement true).symm, rfl⟩
end all_the_way_down

--| THE LIST MACHINE, OF EVERY INDUCTIVE.  The author's, 16 November 2026: make the list machine, except make the entire
--| machine of the inductives, not just the current level; for all the inductives, like in Episode 8.  Episode 8 reads each
--| of the thirty-six to a tape.  Here is the way back for each: a tape, written as the inductive that reads to it.  And all
--| the way down: every slot a cell has for the level below is filled with what the rest of the tape indicates at that level.
--| A natural carries its number.  An area carries its number.  A closure carries its bullshit, which carries its preprint and
--| its number.  Read back by Episode 8, each is as long as its tape and one for where it stands; the sample, the trial and
--| the closure say each fact twice; the measurement has no fencepost, as Episode 8 said it would not.
def the_number_a_list_indicates : List FACT → Number
  | []           => .zero zero
  | fact :: rest => .one fact (the_number_a_list_indicates rest)
theorem the_number_reads_back (tape : List FACT) : (the_number_a_list_indicates tape).peano.length = 1 * tape.length + 1 := by
  induction tape with
  | nil => rfl
  | cons fact rest ih => simp only [the_number_a_list_indicates, Number.peano, List.length_cons, ih]; omega
def the_count_through_the_number (tape : List FACT) : Nat := ((the_number_a_list_indicates tape).peano.length - 1) / 1
theorem the_count_through_the_number_is_the_length : the_count_through_the_number = List.length := by
  funext tape
  simp only [the_count_through_the_number, the_number_reads_back, Nat.add_sub_cancel]
  exact (by omega)

def the_natural_a_list_indicates : List FACT → Natural
  | []           => .zero zero
  | fact :: rest => .number fact (the_number_a_list_indicates rest) (the_natural_a_list_indicates rest)
theorem the_natural_reads_back (tape : List FACT) : (the_natural_a_list_indicates tape).induct.length = 1 * tape.length + 1 := by
  induction tape with
  | nil => rfl
  | cons fact rest ih => simp only [the_natural_a_list_indicates, Natural.induct, List.length_cons, ih]; omega
def the_count_through_the_natural (tape : List FACT) : Nat := ((the_natural_a_list_indicates tape).induct.length - 1) / 1
theorem the_count_through_the_natural_is_the_length : the_count_through_the_natural = List.length := by
  funext tape
  simp only [the_count_through_the_natural, the_natural_reads_back, Nat.add_sub_cancel]
  exact (by omega)

def the_rational_a_list_indicates : List FACT → Rational
  | []           => .zero zero
  | fact :: rest => .number fact (the_natural_a_list_indicates rest) (the_rational_a_list_indicates rest)
theorem the_rational_reads_back (tape : List FACT) : (the_rational_a_list_indicates tape).diagonalize.length = 1 * tape.length + 1 := by
  induction tape with
  | nil => rfl
  | cons fact rest ih => simp only [the_rational_a_list_indicates, Rational.diagonalize, List.length_cons, ih]; omega
def the_count_through_the_rational (tape : List FACT) : Nat := ((the_rational_a_list_indicates tape).diagonalize.length - 1) / 1
theorem the_count_through_the_rational_is_the_length : the_count_through_the_rational = List.length := by
  funext tape
  simp only [the_count_through_the_rational, the_rational_reads_back, Nat.add_sub_cancel]
  exact (by omega)

def the_sequence_a_list_indicates : List FACT → Sequence
  | []           => .nil zero
  | fact :: rest => .index fact (the_rational_a_list_indicates rest) (the_sequence_a_list_indicates rest)
theorem the_sequence_reads_back (tape : List FACT) : (the_sequence_a_list_indicates tape).enumerate.length = 1 * tape.length + 1 := by
  induction tape with
  | nil => rfl
  | cons fact rest ih => simp only [the_sequence_a_list_indicates, Sequence.enumerate, List.length_cons, ih]; omega
def the_count_through_the_sequence (tape : List FACT) : Nat := ((the_sequence_a_list_indicates tape).enumerate.length - 1) / 1
theorem the_count_through_the_sequence_is_the_length : the_count_through_the_sequence = List.length := by
  funext tape
  simp only [the_count_through_the_sequence, the_sequence_reads_back, Nat.add_sub_cancel]
  exact (by omega)

def the_limit_a_list_indicates : List FACT → Limit
  | []           => .nil zero
  | fact :: rest => .index fact (the_sequence_a_list_indicates rest) (the_limit_a_list_indicates rest)
theorem the_limit_reads_back (tape : List FACT) : (the_limit_a_list_indicates tape).converge.length = 1 * tape.length + 1 := by
  induction tape with
  | nil => rfl
  | cons fact rest ih => simp only [the_limit_a_list_indicates, Limit.converge, List.length_cons, ih]; omega
def the_count_through_the_limit (tape : List FACT) : Nat := ((the_limit_a_list_indicates tape).converge.length - 1) / 1
theorem the_count_through_the_limit_is_the_length : the_count_through_the_limit = List.length := by
  funext tape
  simp only [the_count_through_the_limit, the_limit_reads_back, Nat.add_sub_cancel]
  exact (by omega)

def the_sample_a_list_indicates : List FACT → Sample
  | []           => .initial_condition zero (the_limit_a_list_indicates [])
  | fact :: rest => .signal_response fact (the_limit_a_list_indicates rest) fact (the_limit_a_list_indicates rest) (the_sample_a_list_indicates rest)
theorem the_sample_reads_back (tape : List FACT) : (the_sample_a_list_indicates tape).taste.length = 2 * tape.length + 1 := by
  induction tape with
  | nil => rfl
  | cons fact rest ih => simp only [the_sample_a_list_indicates, Sample.taste, List.length_cons, ih]; omega
def the_count_through_the_sample (tape : List FACT) : Nat := ((the_sample_a_list_indicates tape).taste.length - 1) / 2
theorem the_count_through_the_sample_is_the_length : the_count_through_the_sample = List.length := by
  funext tape
  simp only [the_count_through_the_sample, the_sample_reads_back, Nat.add_sub_cancel]
  exact Nat.mul_div_cancel_left _ (by decide)

def the_trial_a_list_indicates : List FACT → Trial
  | []           => .hypothesis zero (the_sample_a_list_indicates [])
  | fact :: rest => .signal_response fact (the_sample_a_list_indicates rest) fact (the_sample_a_list_indicates rest) (the_trial_a_list_indicates rest)
theorem the_trial_reads_back (tape : List FACT) : (the_trial_a_list_indicates tape).experiment.length = 2 * tape.length + 1 := by
  induction tape with
  | nil => rfl
  | cons fact rest ih => simp only [the_trial_a_list_indicates, Trial.experiment, List.length_cons, ih]; omega
def the_count_through_the_trial (tape : List FACT) : Nat := ((the_trial_a_list_indicates tape).experiment.length - 1) / 2
theorem the_count_through_the_trial_is_the_length : the_count_through_the_trial = List.length := by
  funext tape
  simp only [the_count_through_the_trial, the_trial_reads_back, Nat.add_sub_cancel]
  exact Nat.mul_div_cancel_left _ (by decide)

def the_study_a_list_indicates : List FACT → Study
  | []           => .hypothesis zero
  | fact :: rest => .book_of_records fact (the_trial_a_list_indicates rest) (the_study_a_list_indicates rest)
theorem the_study_reads_back (tape : List FACT) : (the_study_a_list_indicates tape).phenomenon.length = 1 * tape.length + 1 := by
  induction tape with
  | nil => rfl
  | cons fact rest ih => simp only [the_study_a_list_indicates, Study.phenomenon, List.length_cons, ih]; omega
def the_count_through_the_study (tape : List FACT) : Nat := ((the_study_a_list_indicates tape).phenomenon.length - 1) / 1
theorem the_count_through_the_study_is_the_length : the_count_through_the_study = List.length := by
  funext tape
  simp only [the_count_through_the_study, the_study_reads_back, Nat.add_sub_cancel]
  exact (by omega)

def the_computation_a_list_indicates : List FACT → Computation
  | []           => .program zero (the_study_a_list_indicates [])
  | fact :: rest => .compute fact (the_study_a_list_indicates rest) (the_study_a_list_indicates rest) (the_computation_a_list_indicates rest)
theorem the_computation_reads_back (tape : List FACT) : (the_computation_a_list_indicates tape).elaborate.length = 1 * tape.length + 1 := by
  induction tape with
  | nil => rfl
  | cons fact rest ih => simp only [the_computation_a_list_indicates, Computation.elaborate, List.length_cons, ih]; omega
def the_count_through_the_computation (tape : List FACT) : Nat := ((the_computation_a_list_indicates tape).elaborate.length - 1) / 1
theorem the_count_through_the_computation_is_the_length : the_count_through_the_computation = List.length := by
  funext tape
  simp only [the_count_through_the_computation, the_computation_reads_back, Nat.add_sub_cancel]
  exact (by omega)

def the_chaitin_a_list_indicates : List FACT → ChaitinsNumberSequence
  | []           => .halting zero (the_computation_a_list_indicates [])
  | fact :: rest => .nonhalting fact (the_computation_a_list_indicates rest) (some (the_chaitin_a_list_indicates rest))
theorem the_chaitin_reads_back (tape : List FACT) : (the_chaitin_a_list_indicates tape).unknown.length = 1 * tape.length + 1 := by
  induction tape with
  | nil => rfl
  | cons fact rest ih => simp only [the_chaitin_a_list_indicates, ChaitinsNumberSequence.unknown, List.length_cons, ih]; omega
def the_count_through_the_chaitin (tape : List FACT) : Nat := ((the_chaitin_a_list_indicates tape).unknown.length - 1) / 1
theorem the_count_through_the_chaitin_is_the_length : the_count_through_the_chaitin = List.length := by
  funext tape
  simp only [the_count_through_the_chaitin, the_chaitin_reads_back, Nat.add_sub_cancel]
  exact (by omega)

def the_metavariable_a_list_indicates : List FACT → Metavariable Closure.{0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0}
  | []           => .base zero the_only_logical_inconsistency
  | fact :: rest => .step fact (the_metavariable_a_list_indicates rest)
theorem the_metavariable_reads_back (tape : List FACT) : (the_metavariable_a_list_indicates tape).closure.length = 1 * tape.length + 1 := by
  induction tape with
  | nil => rfl
  | cons fact rest ih => simp only [the_metavariable_a_list_indicates, Metavariable.closure, List.length_cons, ih]; omega
def the_count_through_the_metavariable (tape : List FACT) : Nat := ((the_metavariable_a_list_indicates tape).closure.length - 1) / 1
theorem the_count_through_the_metavariable_is_the_length : the_count_through_the_metavariable = List.length := by
  funext tape
  simp only [the_count_through_the_metavariable, the_metavariable_reads_back, Nat.add_sub_cancel]
  exact (by omega)

def the_sophism_a_list_indicates : List FACT → Sophism
  | []           => .origin zero (the_chaitin_a_list_indicates []) Prop
  | fact :: rest => .dimension fact (the_chaitin_a_list_indicates rest) Prop (the_sophism_a_list_indicates rest)
theorem the_sophism_reads_back (tape : List FACT) : (the_sophism_a_list_indicates tape).taylor_expansion.length = 1 * tape.length + 1 := by
  induction tape with
  | nil => rfl
  | cons fact rest ih => simp only [the_sophism_a_list_indicates, Sophism.taylor_expansion, List.length_cons, ih]; omega
def the_count_through_the_sophism (tape : List FACT) : Nat := ((the_sophism_a_list_indicates tape).taylor_expansion.length - 1) / 1
theorem the_count_through_the_sophism_is_the_length : the_count_through_the_sophism = List.length := by
  funext tape
  simp only [the_count_through_the_sophism, the_sophism_reads_back, Nat.add_sub_cancel]
  exact (by omega)

def the_area_a_list_indicates : List FACT → Area
  | []           => .tree zero
  | fact :: rest => .dt fact (the_number_a_list_indicates rest) (the_area_a_list_indicates rest)
theorem the_area_reads_back (tape : List FACT) : (the_area_a_list_indicates tape).riemann_integrate.length = 1 * tape.length + 1 := by
  induction tape with
  | nil => rfl
  | cons fact rest ih => simp only [the_area_a_list_indicates, Area.riemann_integrate, List.length_cons, ih]; omega
def the_count_through_the_area (tape : List FACT) : Nat := ((the_area_a_list_indicates tape).riemann_integrate.length - 1) / 1
theorem the_count_through_the_area_is_the_length : the_count_through_the_area = List.length := by
  funext tape
  simp only [the_count_through_the_area, the_area_reads_back, Nat.add_sub_cancel]
  exact (by omega)

def the_pigeonhole_a_list_indicates : List FACT → PigeonHole
  | []           => .this_superpigeon zero (the_area_a_list_indicates [])
  | fact :: rest => .a_pigeon fact (the_area_a_list_indicates rest) (the_pigeonhole_a_list_indicates rest)
theorem the_pigeonhole_reads_back (tape : List FACT) : (the_pigeonhole_a_list_indicates tape).solve.length = 1 * tape.length + 1 := by
  induction tape with
  | nil => rfl
  | cons fact rest ih => simp only [the_pigeonhole_a_list_indicates, PigeonHole.solve, List.length_cons, ih]; omega
def the_count_through_the_pigeonhole (tape : List FACT) : Nat := ((the_pigeonhole_a_list_indicates tape).solve.length - 1) / 1
theorem the_count_through_the_pigeonhole_is_the_length : the_count_through_the_pigeonhole = List.length := by
  funext tape
  simp only [the_count_through_the_pigeonhole, the_pigeonhole_reads_back, Nat.add_sub_cancel]
  exact (by omega)

def the_jar_a_list_indicates : List FACT → Jar
  | []           => .color zero (the_area_a_list_indicates [])
  | fact :: rest => .bang fact (the_jar_a_list_indicates rest)
theorem the_jar_reads_back (tape : List FACT) : (the_jar_a_list_indicates tape).classify.length = 1 * tape.length + 1 := by
  induction tape with
  | nil => rfl
  | cons fact rest ih => simp only [the_jar_a_list_indicates, Jar.classify, List.length_cons, ih]; omega
def the_count_through_the_jar (tape : List FACT) : Nat := ((the_jar_a_list_indicates tape).classify.length - 1) / 1
theorem the_count_through_the_jar_is_the_length : the_count_through_the_jar = List.length := by
  funext tape
  simp only [the_count_through_the_jar, the_jar_reads_back, Nat.add_sub_cancel]
  exact (by omega)

def the_equivalation_a_list_indicates : List FACT → Equivalation
  | []           => .physics zero (the_jar_a_list_indicates [])
  | fact :: rest => .zero_like fact (the_equivalation_a_list_indicates rest)
theorem the_equivalation_reads_back (tape : List FACT) : (the_equivalation_a_list_indicates tape).vanish.length = 1 * tape.length + 1 := by
  induction tape with
  | nil => rfl
  | cons fact rest ih => simp only [the_equivalation_a_list_indicates, Equivalation.vanish, List.length_cons, ih]; omega
def the_count_through_the_equivalation (tape : List FACT) : Nat := ((the_equivalation_a_list_indicates tape).vanish.length - 1) / 1
theorem the_count_through_the_equivalation_is_the_length : the_count_through_the_equivalation = List.length := by
  funext tape
  simp only [the_count_through_the_equivalation, the_equivalation_reads_back, Nat.add_sub_cancel]
  exact (by omega)

def the_encoding_a_list_indicates : List FACT → Encoding
  | []           => .boot zero (the_equivalation_a_list_indicates [])
  | fact :: rest => .zero fact (the_equivalation_a_list_indicates rest) (the_encoding_a_list_indicates rest)
theorem the_encoding_reads_back (tape : List FACT) : (the_encoding_a_list_indicates tape).decode.length = 1 * tape.length + 1 := by
  induction tape with
  | nil => rfl
  | cons fact rest ih => simp only [the_encoding_a_list_indicates, Encoding.decode, List.length_cons, ih]; omega
def the_count_through_the_encoding (tape : List FACT) : Nat := ((the_encoding_a_list_indicates tape).decode.length - 1) / 1
theorem the_count_through_the_encoding_is_the_length : the_count_through_the_encoding = List.length := by
  funext tape
  simp only [the_count_through_the_encoding, the_encoding_reads_back, Nat.add_sub_cancel]
  exact (by omega)

def the_abstraction_a_list_indicates : List FACT → Abstraction
  | []           => .satire_about zero
  | fact :: rest => .compile fact (the_encoding_a_list_indicates rest) (the_abstraction_a_list_indicates rest)
theorem the_abstraction_reads_back (tape : List FACT) : (the_abstraction_a_list_indicates tape).equivalation.length = 1 * tape.length + 1 := by
  induction tape with
  | nil => rfl
  | cons fact rest ih => simp only [the_abstraction_a_list_indicates, Abstraction.equivalation, List.length_cons, ih]; omega
def the_count_through_the_abstraction (tape : List FACT) : Nat := ((the_abstraction_a_list_indicates tape).equivalation.length - 1) / 1
theorem the_count_through_the_abstraction_is_the_length : the_count_through_the_abstraction = List.length := by
  funext tape
  simp only [the_count_through_the_abstraction, the_abstraction_reads_back, Nat.add_sub_cancel]
  exact (by omega)

def the_sum_a_list_indicates : List FACT → Sum
  | []           => .zero True (the_area_a_list_indicates [])
  | fact :: rest => .add fact (the_area_a_list_indicates rest) (the_area_a_list_indicates rest) (the_sum_a_list_indicates rest)
theorem the_sum_reads_back (tape : List FACT) : (the_sum_a_list_indicates tape).euclid.length = 1 * tape.length + 1 := by
  induction tape with
  | nil => rfl
  | cons fact rest ih => simp only [the_sum_a_list_indicates, Sum.euclid, List.length_cons, ih]; omega
def the_count_through_the_sum (tape : List FACT) : Nat := ((the_sum_a_list_indicates tape).euclid.length - 1) / 1
theorem the_count_through_the_sum_is_the_length : the_count_through_the_sum = List.length := by
  funext tape
  simp only [the_count_through_the_sum, the_sum_reads_back, Nat.add_sub_cancel]
  exact (by omega)

def the_product_a_list_indicates : List FACT → Product
  | []           => .origin zero
  | fact :: rest => .mul fact (the_sum_a_list_indicates rest) (the_sum_a_list_indicates rest) (the_product_a_list_indicates rest)
theorem the_product_reads_back (tape : List FACT) : (the_product_a_list_indicates tape).projector.length = 1 * tape.length + 1 := by
  induction tape with
  | nil => rfl
  | cons fact rest ih => simp only [the_product_a_list_indicates, Product.projector, List.length_cons, ih]; omega
def the_count_through_the_product (tape : List FACT) : Nat := ((the_product_a_list_indicates tape).projector.length - 1) / 1
theorem the_count_through_the_product_is_the_length : the_count_through_the_product = List.length := by
  funext tape
  simp only [the_count_through_the_product, the_product_reads_back, Nat.add_sub_cancel]
  exact (by omega)

def the_basis_a_list_indicates : List FACT → Basis
  | []           => .null_space zero
  | fact :: rest => .basis fact (the_product_a_list_indicates rest) (the_product_a_list_indicates rest) (the_basis_a_list_indicates rest)
theorem the_basis_reads_back (tape : List FACT) : (the_basis_a_list_indicates tape).householder.length = 1 * tape.length + 1 := by
  induction tape with
  | nil => rfl
  | cons fact rest ih => simp only [the_basis_a_list_indicates, Basis.householder, List.length_cons, ih]; omega
def the_count_through_the_basis (tape : List FACT) : Nat := ((the_basis_a_list_indicates tape).householder.length - 1) / 1
theorem the_count_through_the_basis_is_the_length : the_count_through_the_basis = List.length := by
  funext tape
  simp only [the_count_through_the_basis, the_basis_reads_back, Nat.add_sub_cancel]
  exact (by omega)

def the_polynomial_a_list_indicates : List FACT → Polynomial
  | []           => .constant zero
  | fact :: rest => .factor fact (the_basis_a_list_indicates rest) (the_basis_a_list_indicates rest) (the_polynomial_a_list_indicates rest)
theorem the_polynomial_reads_back (tape : List FACT) : (the_polynomial_a_list_indicates tape).terms.length = 1 * tape.length + 1 := by
  induction tape with
  | nil => rfl
  | cons fact rest ih => simp only [the_polynomial_a_list_indicates, Polynomial.terms, List.length_cons, ih]; omega
def the_count_through_the_polynomial (tape : List FACT) : Nat := ((the_polynomial_a_list_indicates tape).terms.length - 1) / 1
theorem the_count_through_the_polynomial_is_the_length : the_count_through_the_polynomial = List.length := by
  funext tape
  simp only [the_count_through_the_polynomial, the_polynomial_reads_back, Nat.add_sub_cancel]
  exact (by omega)

def the_spline_a_list_indicates : List FACT → Spline
  | []           => .observation True
  | fact :: rest => .knot fact.truth (the_polynomial_a_list_indicates rest) (the_spline_a_list_indicates rest)
theorem the_spline_reads_back (tape : List FACT) : (the_spline_a_list_indicates tape).approx.length = 1 * tape.length + 1 := by
  induction tape with
  | nil => rfl
  | cons fact rest ih => simp only [the_spline_a_list_indicates, Spline.approx, List.length_cons, ih]; omega
def the_count_through_the_spline (tape : List FACT) : Nat := ((the_spline_a_list_indicates tape).approx.length - 1) / 1
theorem the_count_through_the_spline_is_the_length : the_count_through_the_spline = List.length := by
  funext tape
  simp only [the_count_through_the_spline, the_spline_reads_back, Nat.add_sub_cancel]
  exact (by omega)

def the_diatribe_a_list_indicates : List FACT → Diatribe
  | []           => .religion True
  | fact :: rest => .speculation fact.truth (the_spline_a_list_indicates rest) (the_diatribe_a_list_indicates rest)
theorem the_diatribe_reads_back (tape : List FACT) : (the_diatribe_a_list_indicates tape).buckets.length = 1 * tape.length + 1 := by
  induction tape with
  | nil => rfl
  | cons fact rest ih => simp only [the_diatribe_a_list_indicates, Diatribe.buckets, List.length_cons, ih]; omega
def the_count_through_the_diatribe (tape : List FACT) : Nat := ((the_diatribe_a_list_indicates tape).buckets.length - 1) / 1
theorem the_count_through_the_diatribe_is_the_length : the_count_through_the_diatribe = List.length := by
  funext tape
  simp only [the_count_through_the_diatribe, the_diatribe_reads_back, Nat.add_sub_cancel]
  exact (by omega)

def the_cult_a_list_indicates : List FACT → Cult
  | []           => .inside_joke True
  | fact :: rest => .pythagoras fact.truth (the_diatribe_a_list_indicates rest) (the_cult_a_list_indicates rest)
theorem the_cult_reads_back (tape : List FACT) : (the_cult_a_list_indicates tape).name.length = 1 * tape.length + 1 := by
  induction tape with
  | nil => rfl
  | cons fact rest ih => simp only [the_cult_a_list_indicates, Cult.name, List.length_cons, ih]; omega
def the_count_through_the_cult (tape : List FACT) : Nat := ((the_cult_a_list_indicates tape).name.length - 1) / 1
theorem the_count_through_the_cult_is_the_length : the_count_through_the_cult = List.length := by
  funext tape
  simp only [the_count_through_the_cult, the_cult_reads_back, Nat.add_sub_cancel]
  exact (by omega)

def the_science_a_list_indicates : List FACT → Science
  | []           => .repeatable True
  | fact :: rest => .theory fact.truth (the_cult_a_list_indicates rest) fact (the_science_a_list_indicates rest)
theorem the_science_reads_back (tape : List FACT) : (the_science_a_list_indicates tape).method.length = 1 * tape.length + 1 := by
  induction tape with
  | nil => rfl
  | cons fact rest ih => simp only [the_science_a_list_indicates, Science.method, List.length_cons, ih]; omega
def the_count_through_the_science (tape : List FACT) : Nat := ((the_science_a_list_indicates tape).method.length - 1) / 1
theorem the_count_through_the_science_is_the_length : the_count_through_the_science = List.length := by
  funext tape
  simp only [the_count_through_the_science, the_science_reads_back, Nat.add_sub_cancel]
  exact (by omega)

def the_knowledge_a_list_indicates : List FACT → Knowledge
  | []           => .jarjar True
  | fact :: rest => .ledger fact.truth fact (the_knowledge_a_list_indicates rest)
theorem the_knowledge_reads_back (tape : List FACT) : (the_knowledge_a_list_indicates tape).audit.length = 1 * tape.length + 1 := by
  induction tape with
  | nil => rfl
  | cons fact rest ih => simp only [the_knowledge_a_list_indicates, Knowledge.audit, List.length_cons, ih]; omega
def the_count_through_the_knowledge (tape : List FACT) : Nat := ((the_knowledge_a_list_indicates tape).audit.length - 1) / 1
theorem the_count_through_the_knowledge_is_the_length : the_count_through_the_knowledge = List.length := by
  funext tape
  simp only [the_count_through_the_knowledge, the_knowledge_reads_back, Nat.add_sub_cancel]
  exact (by omega)

def the_gospel_a_list_indicates : List FACT → Gospel
  | []           => .the_proof True
  | fact :: rest => .we_understand_that (the_knowledge_a_list_indicates rest) fact.truth (the_gospel_a_list_indicates rest)
theorem the_gospel_reads_back (tape : List FACT) : (the_gospel_a_list_indicates tape).witness.length = 1 * tape.length + 1 := by
  induction tape with
  | nil => rfl
  | cons fact rest ih => simp only [the_gospel_a_list_indicates, Gospel.witness, List.length_cons, ih]; omega
def the_count_through_the_gospel (tape : List FACT) : Nat := ((the_gospel_a_list_indicates tape).witness.length - 1) / 1
theorem the_count_through_the_gospel_is_the_length : the_count_through_the_gospel = List.length := by
  funext tape
  simp only [the_count_through_the_gospel, the_gospel_reads_back, Nat.add_sub_cancel]
  exact (by omega)

def the_truth_a_list_indicates : List FACT → Truth
  | []           => .logically True
  | fact :: rest => .but (the_gospel_a_list_indicates rest) fact.truth (the_truth_a_list_indicates rest)
theorem the_truth_reads_back (tape : List FACT) : (the_truth_a_list_indicates tape).testify.length = 1 * tape.length + 1 := by
  induction tape with
  | nil => rfl
  | cons fact rest ih => simp only [the_truth_a_list_indicates, Truth.testify, List.length_cons, ih]; omega
def the_count_through_the_truth (tape : List FACT) : Nat := ((the_truth_a_list_indicates tape).testify.length - 1) / 1
theorem the_count_through_the_truth_is_the_length : the_count_through_the_truth = List.length := by
  funext tape
  simp only [the_count_through_the_truth, the_truth_reads_back, Nat.add_sub_cancel]
  exact (by omega)

def the_variation_a_list_indicates : List FACT → Variation
  | []           => .the_newton (the_gospel_a_list_indicates []) True
  | fact :: rest => .the_gateaux (the_gospel_a_list_indicates rest) fact.truth fact.truth (the_variation_a_list_indicates rest)
theorem the_variation_reads_back (tape : List FACT) : (the_variation_a_list_indicates tape).krylov.length = 1 * tape.length + 1 := by
  induction tape with
  | nil => rfl
  | cons fact rest ih => simp only [the_variation_a_list_indicates, Variation.krylov, List.length_cons, ih]; omega
def the_count_through_the_variation (tape : List FACT) : Nat := ((the_variation_a_list_indicates tape).krylov.length - 1) / 1
theorem the_count_through_the_variation_is_the_length : the_count_through_the_variation = List.length := by
  funext tape
  simp only [the_count_through_the_variation, the_variation_reads_back, Nat.add_sub_cancel]
  exact (by omega)

def the_spacetimepath_a_list_indicates : List FACT → SpaceTimePath.{0}
  | []           => .einstein zero
  | fact :: rest => .whitehole fact Prop (the_spacetimepath_a_list_indicates rest)
theorem the_spacetimepath_reads_back (tape : List FACT) : (the_spacetimepath_a_list_indicates tape).stokes.length = 1 * tape.length + 1 := by
  induction tape with
  | nil => rfl
  | cons fact rest ih => simp only [the_spacetimepath_a_list_indicates, SpaceTimePath.stokes, List.length_cons, ih]; omega
def the_count_through_the_spacetimepath (tape : List FACT) : Nat := ((the_spacetimepath_a_list_indicates tape).stokes.length - 1) / 1
theorem the_count_through_the_spacetimepath_is_the_length : the_count_through_the_spacetimepath = List.length := by
  funext tape
  simp only [the_count_through_the_spacetimepath, the_spacetimepath_reads_back, Nat.add_sub_cancel]
  exact (by omega)

def the_yarn_a_list_indicates : List FACT → YarnTheory.{0,0,0,0,0,0}
  | []           => .stokes zero (the_spacetimepath_a_list_indicates []) True
  | fact :: rest => .fibers fact (the_spacetimepath_a_list_indicates rest) (the_spacetimepath_a_list_indicates rest) fact.truth fact.truth (the_yarn_a_list_indicates rest)
theorem the_yarn_reads_back (tape : List FACT) : (the_yarn_a_list_indicates tape).gauss.length = 1 * tape.length + 1 := by
  induction tape with
  | nil => rfl
  | cons fact rest ih => simp only [the_yarn_a_list_indicates, YarnTheory.gauss, List.length_cons, ih]; omega
def the_count_through_the_yarn (tape : List FACT) : Nat := ((the_yarn_a_list_indicates tape).gauss.length - 1) / 1
theorem the_count_through_the_yarn_is_the_length : the_count_through_the_yarn = List.length := by
  funext tape
  simp only [the_count_through_the_yarn, the_yarn_reads_back, Nat.add_sub_cancel]
  exact (by omega)

def the_measurement_a_list_indicates : List FACT → Measurement.{0}
  | []           => .origin zero (the_number_a_list_indicates []) Prop
  | fact :: rest => .distance_to fact (the_number_a_list_indicates rest) (the_number_a_list_indicates rest) Prop Type (the_measurement_a_list_indicates rest)
theorem the_measurement_reads_back (tape : List FACT) : (the_measurement_a_list_indicates tape).the_reading.length = 1 * tape.length + 0 := by
  induction tape with
  | nil => rfl
  | cons fact rest ih => simp only [the_measurement_a_list_indicates, Measurement.the_reading, List.length_cons, ih]; omega
def the_count_through_the_measurement (tape : List FACT) : Nat := ((the_measurement_a_list_indicates tape).the_reading.length - 0) / 1
theorem the_count_through_the_measurement_is_the_length : the_count_through_the_measurement = List.length := by
  funext tape
  simp only [the_count_through_the_measurement, the_measurement_reads_back, Nat.add_sub_cancel]
  exact (by omega)

def the_preprint_a_list_indicates : List FACT → ThePreprint.{0}
  | []           => .introduction zero Prop
  | fact :: rest => .methodology fact fact Prop Type (the_preprint_a_list_indicates rest)
theorem the_preprint_reads_back (tape : List FACT) : (the_preprint_a_list_indicates tape).the_model.length = 1 * tape.length + 1 := by
  induction tape with
  | nil => rfl
  | cons fact rest ih => simp only [the_preprint_a_list_indicates, ThePreprint.the_model, List.length_cons, ih]; omega
def the_count_through_the_preprint (tape : List FACT) : Nat := ((the_preprint_a_list_indicates tape).the_model.length - 1) / 1
theorem the_count_through_the_preprint_is_the_length : the_count_through_the_preprint = List.length := by
  funext tape
  simp only [the_count_through_the_preprint, the_preprint_reads_back, Nat.add_sub_cancel]
  exact (by omega)

def the_bullshit_a_list_indicates : List FACT → Bullshit.{0,0,0,0}
  | []           => .zero zero
  | fact :: rest => .one fact (the_number_a_list_indicates rest) (the_preprint_a_list_indicates rest) (the_preprint_a_list_indicates rest) (the_bullshit_a_list_indicates rest)
theorem the_bullshit_reads_back (tape : List FACT) : (the_bullshit_a_list_indicates tape).meter.length = 1 * tape.length + 1 := by
  induction tape with
  | nil => rfl
  | cons fact rest ih => simp only [the_bullshit_a_list_indicates, Bullshit.meter, List.length_cons, ih]; omega
def the_count_through_the_bullshit (tape : List FACT) : Nat := ((the_bullshit_a_list_indicates tape).meter.length - 1) / 1
theorem the_count_through_the_bullshit_is_the_length : the_count_through_the_bullshit = List.length := by
  funext tape
  simp only [the_count_through_the_bullshit, the_bullshit_reads_back, Nat.add_sub_cancel]
  exact (by omega)

def the_closure_a_list_indicates : List FACT → Closure.{0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0}
  | []           => .same zero (the_bullshit_a_list_indicates [])
  | fact :: rest => .inferred fact fact (the_bullshit_a_list_indicates rest) (the_bullshit_a_list_indicates rest) (some fact.truth) (the_closure_a_list_indicates rest)
theorem the_closure_reads_back (tape : List FACT) : (the_closure_a_list_indicates tape).infer.length = 2 * tape.length + 1 := by
  induction tape with
  | nil => rfl
  | cons fact rest ih => simp only [the_closure_a_list_indicates, Closure.infer, List.length_cons, ih]; omega
def the_count_through_the_closure (tape : List FACT) : Nat := ((the_closure_a_list_indicates tape).infer.length - 1) / 2
theorem the_count_through_the_closure_is_the_length : the_count_through_the_closure = List.length := by
  funext tape
  simp only [the_count_through_the_closure, the_closure_reads_back, Nat.add_sub_cancel]
  exact Nat.mul_div_cancel_left _ (by decide)

--| THE ENTIRE MACHINE.  Thirty-six counts, one through every inductive of the five episodes, in the order of the rungs.
def the_counts_through_all_the_inductives : List (List FACT → Nat) :=
  [the_count_through_the_number,
   the_count_through_the_natural,
   the_count_through_the_rational,
   the_count_through_the_sequence,
   the_count_through_the_limit,
   the_count_through_the_sample,
   the_count_through_the_trial,
   the_count_through_the_study,
   the_count_through_the_computation,
   the_count_through_the_chaitin,
   the_count_through_the_metavariable,
   the_count_through_the_sophism,
   the_count_through_the_area,
   the_count_through_the_pigeonhole,
   the_count_through_the_jar,
   the_count_through_the_equivalation,
   the_count_through_the_encoding,
   the_count_through_the_abstraction,
   the_count_through_the_sum,
   the_count_through_the_product,
   the_count_through_the_basis,
   the_count_through_the_polynomial,
   the_count_through_the_spline,
   the_count_through_the_diatribe,
   the_count_through_the_cult,
   the_count_through_the_science,
   the_count_through_the_knowledge,
   the_count_through_the_gospel,
   the_count_through_the_truth,
   the_count_through_the_variation,
   the_count_through_the_spacetimepath,
   the_count_through_the_yarn,
   the_count_through_the_measurement,
   the_count_through_the_preprint,
   the_count_through_the_bullshit,
   the_count_through_the_closure]

theorem there_is_a_count_for_every_inductive :
    the_counts_through_all_the_inductives.length = the_inductives_of_the_five_episodes.length := by decide

--| Every one of them is the length.
theorem every_count_is_the_length :
    the_counts_through_all_the_inductives = List.replicate the_counts_through_all_the_inductives.length List.length := by
  simp only [the_counts_through_all_the_inductives, the_count_through_the_number_is_the_length, the_count_through_the_natural_is_the_length, the_count_through_the_rational_is_the_length, the_count_through_the_sequence_is_the_length, the_count_through_the_limit_is_the_length, the_count_through_the_sample_is_the_length, the_count_through_the_trial_is_the_length, the_count_through_the_study_is_the_length, the_count_through_the_computation_is_the_length, the_count_through_the_chaitin_is_the_length, the_count_through_the_metavariable_is_the_length, the_count_through_the_sophism_is_the_length, the_count_through_the_area_is_the_length, the_count_through_the_pigeonhole_is_the_length, the_count_through_the_jar_is_the_length, the_count_through_the_equivalation_is_the_length, the_count_through_the_encoding_is_the_length, the_count_through_the_abstraction_is_the_length, the_count_through_the_sum_is_the_length, the_count_through_the_product_is_the_length, the_count_through_the_basis_is_the_length, the_count_through_the_polynomial_is_the_length, the_count_through_the_spline_is_the_length, the_count_through_the_diatribe_is_the_length, the_count_through_the_cult_is_the_length, the_count_through_the_science_is_the_length, the_count_through_the_knowledge_is_the_length, the_count_through_the_gospel_is_the_length, the_count_through_the_truth_is_the_length, the_count_through_the_variation_is_the_length, the_count_through_the_spacetimepath_is_the_length, the_count_through_the_yarn_is_the_length, the_count_through_the_measurement_is_the_length, the_count_through_the_preprint_is_the_length, the_count_through_the_bullshit_is_the_length, the_count_through_the_closure_is_the_length]
  rfl

--| And so the crank, handed any of the thirty-six, arranges the one pair.  The number comes out of every inductive.
theorem the_number_comes_out_of_every_inductive :
    the_counts_through_all_the_inductives.map (fun count => bent_card.fenceposts_must_be_preserved Nat count all_possible_variables)
      = List.replicate the_counts_through_all_the_inductives.length arrange_the_information_appropriately := by
  rw [every_count_is_the_length, List.map_replicate, List.length_replicate]
  rfl

--#print axioms execute_counts_what_compile_built
--#print axioms the_memory_written_as_an_abstraction_is_the_trace_and_the_fencepost
--#print axioms the_wall_comes_before_the_abstraction
--#print axioms counted_the_walk_is_the_walk
--#print axioms counted_one_turn_is_one_turn
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
--#print axioms one_turn_stands_still_under_the_resolution
--#print axioms one_turn_goes_exactly_when_the_knot_clicks
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

end the_area

--| ALL THE WAY DOWN.  The author's, 16 November 2026: look at the yarn; recurse through the types, the list of all the
--| recursive types and not just the one; just define it the other way around; and put the truth in for a Prop.  Episode 8
--| reads each inductive to its own facts and passes over what its cells carry.  Here is the other reading, for every
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
--| is inside it: the most basic of conclusions four times, thirty-four cells each, and the one statement it carries, read as
--| the truth.
def the_giant_list : List FACT := the_only_logical_inconsistency.the_inside
#eval the_giant_list.length
#print axioms the_giant_list

set_option maxRecDepth 100000 in -- the lists are long; the elaborator needs room to count them
theorem the_final_inferred_closure_all_the_way_down :
    the_only_logical_inconsistency.all_the_way_down.length
        = the_giant_list.length + the_only_logical_inconsistency.infer.length
      ∧ the_only_logical_inconsistency.infer.length = 3
      ∧ the_most_basic_of_conclusions.all_the_way_down.length = 34 := ⟨rfl, rfl, rfl⟩

set_option maxRecDepth 100000 in -- the lists are long; the elaborator needs room to count them
theorem the_giant_list_is_four_conclusions_and_one_truth :
    the_giant_list.length
      = (the_most_basic_of_conclusions.all_the_way_down.length
          + the_most_basic_of_conclusions.all_the_way_down.length)
        + (the_most_basic_of_conclusions.all_the_way_down.length
          + the_most_basic_of_conclusions.all_the_way_down.length)
        + [FACT.Truth].length := rfl

--| THE RESIDUE.  The author's, 16 November 2026: now, the residue; and, of the digits past the giant list and the cells left
--| over, those should be the same thing.  They are.  The cells left over are the closure's own three and the one statement
--| read as the truth.  Each own cell at the basis raised to the free variables, and the truth beside them.
def the_cells_left_over : Nat :=
  the_only_logical_inconsistency.infer.length * the_basis.the_reading.length ^ the_free_variable_count + [FACT.Truth].length

--| The frame by the coefficient by the giant list is the memory cubed and the cells left over.  Nothing to spare.
set_option maxRecDepth 100000 in
theorem the_giant_list_closes_on_the_cells_left_over :
    the_coordinate_system.gauss.length * the_coefficient_tape.length * the_giant_list.length
      = the_memory_tape.length * the_memory_tape.length * the_memory_tape.length + the_cells_left_over := by decide

--| And the cells left over are the whole part of the memory squared by the root of the round trip: its square is not over
--| the memory to the fourth by the frame by the memory, and one more cell's is.
theorem the_cells_left_over_are_the_whole_part_of_the_root :
    the_cells_left_over * the_cells_left_over
        ≤ (the_memory_tape.length * the_memory_tape.length) * (the_memory_tape.length * the_memory_tape.length)
            * (the_coordinate_system.gauss.length * the_memory_tape.length)
      ∧ (the_memory_tape.length * the_memory_tape.length) * (the_memory_tape.length * the_memory_tape.length)
            * (the_coordinate_system.gauss.length * the_memory_tape.length)
          < (the_cells_left_over + [FACT.Truth].length) * (the_cells_left_over + [FACT.Truth].length) := by decide

--| The digits past the giant list: Episode 8's constant less the giant list at the scale.
def the_digits_past_the_giant_list : Nat := the_constant_factor_of_scaling_bullshit - the_giant_list.length * all_possible_variables
#eval the_digits_past_the_giant_list
#print axioms the_digits_past_the_giant_list

--| THE SAME THING.  Put those digits, by the frame and the coefficient, back on the cells left over at the scale.  What you
--| have is the same root, to the scale: its square is not over, and one part of the frame by the coefficient more is.
--| The whole cells of the root are the cells left over.  The rest of the root is the digits.
def the_root_to_the_scale : Nat :=
  the_digits_past_the_giant_list * (the_coordinate_system.gauss.length * the_coefficient_tape.length)
    + the_cells_left_over * all_possible_variables

set_option maxRecDepth 100000 in
theorem the_digits_are_the_rest_of_the_root :
    the_root_to_the_scale * the_root_to_the_scale
        ≤ (the_memory_tape.length * the_memory_tape.length) * (the_memory_tape.length * the_memory_tape.length)
            * (the_coordinate_system.gauss.length * the_memory_tape.length) * (all_possible_variables * all_possible_variables)
      ∧ (the_memory_tape.length * the_memory_tape.length) * (the_memory_tape.length * the_memory_tape.length)
            * (the_coordinate_system.gauss.length * the_memory_tape.length) * (all_possible_variables * all_possible_variables)
          < (the_root_to_the_scale + the_coordinate_system.gauss.length * the_coefficient_tape.length)
              * (the_root_to_the_scale + the_coordinate_system.gauss.length * the_coefficient_tape.length) := by decide

--| THE EPILOGUE, IN CELLS.  The author's, 16 November 2026: read the end of Episode 12 and you will see.  Episode 12 ends by
--| taking the reading from the sum of the two roots and printing what is left.  Here it is done with the giant list where the
--| number stood.  The sum of the roots is the trace by the fencepost's first over the coefficient by its second.
def the_sum_of_the_roots_in_cells : Nat :=
  the_trace_of_truth_in_the_device * (the_first_step_of_the_proof_is_to_eschew_the_naturals_unless_proven_to_exist_without_peano).1
def the_frame_by_the_coefficient : Nat :=
  an_exact_polynomial_description * (the_first_step_of_the_proof_is_to_eschew_the_naturals_unless_proven_to_exist_without_peano).2

--| The whole of the sum, less the giant list.  No number is computed.
def what_is_left_of_the_sum : Nat := the_sum_of_the_roots_in_cells / the_frame_by_the_coefficient - the_giant_list.length
#eval what_is_left_of_the_sum
#print axioms what_is_left_of_the_sum

--| The reading's cells are the memory cubed and the cells left over, and they close on the giant list with nothing left.  The
--| other root's are the memory cubed less the cells left over and one, and they close on what is left of the sum with one
--| less than the sum leaves.  And what the sum leaves is the inside of the most basic of conclusions: all the way down, less
--| what Episode 8 reads.
set_option maxRecDepth 100000 in
theorem the_two_roots_in_cells :
    (the_memory_tape.length * the_memory_tape.length * the_memory_tape.length + the_cells_left_over) % the_frame_by_the_coefficient
        = [].length (α := FACT)
      ∧ (the_memory_tape.length * the_memory_tape.length * the_memory_tape.length - (the_cells_left_over + [FACT.Truth].length))
          / the_frame_by_the_coefficient = what_is_left_of_the_sum
      ∧ (the_memory_tape.length * the_memory_tape.length * the_memory_tape.length - (the_cells_left_over + [FACT.Truth].length))
          % the_frame_by_the_coefficient + [FACT.Truth].length = the_sum_of_the_roots_in_cells % the_frame_by_the_coefficient
      ∧ the_sum_of_the_roots_in_cells % the_frame_by_the_coefficient
          = the_most_basic_of_conclusions.all_the_way_down.length - the_most_basic_of_conclusions.meter.length := by decide

--| THE DIGITS, TOGETHER.  The reading's digits past the giant list and the other root's digits past what is left of the sum,
--| added, are what the sum leaves over the frame by the coefficient, to the scale.  Neither is a ratio.  Together they are.
def the_other_roots_digits : Nat :=
  (the_sum_of_the_roots_in_cells * all_possible_variables / the_frame_by_the_coefficient - the_constant_factor_of_scaling_bullshit)
    - what_is_left_of_the_sum * all_possible_variables

set_option maxRecDepth 100000 in
theorem the_two_residues_are_one_ratio :
    the_digits_past_the_giant_list + the_other_roots_digits
      = (the_sum_of_the_roots_in_cells % the_frame_by_the_coefficient) * all_possible_variables / the_frame_by_the_coefficient := by decide

--| THE SHAPE OF THE TABLE.  The author's, 17 November 2026: true on true and false on false, and one false, click; that is
--| three; one false does not; there is your answer; it is the shape of the table and the demonstration of its
--| eigenproperties.  The arm that can click is the arm where the first implies the second.  That is the order on two truths,
--| and it is nobody's device: whatever has two truth values and an order between them has three arms that click and one
--| that does not.
theorem the_click_is_the_order_on_two_truths (this that : Bool) :
    the_arm_stores_a_fact_that_can_click this that = decide (this = true → that = true) := by
  cases this <;> cases that <;> rfl

theorem three_click_and_one_does_not :
    ([(true, true), (true, false), (false, true), (false, false)].filter
        fun arm => decide (arm.1 = true → arm.2 = true)).length = 3 := by decide

--| Put any weight on the arms that click and any other on the one that does not.  The trace squared less four of the
--| determinant is four of the two weights multiplied; and the two roots are the clicking weight, more and less a root of
--| that product.  A ratio when the product is a square, and when the arm is struck.  Otherwise not.  The eighteen and the
--| five are this device's.  The shape is not.
theorem the_shape_has_these_eigenproperties (clicks does_not : Int) :
    (clicks + clicks) * (clicks + clicks) - 4 * (clicks * clicks - does_not * clicks) = 4 * (clicks * does_not) := by
  simp only [Int.add_mul, Int.mul_add, Int.mul_sub, Int.mul_comm does_not clicks]; omega

theorem the_roots_of_the_shape (clicks does_not root : Int) (the_root_squared : root * root = clicks * does_not) :
    (clicks + root) * (clicks + root) - (clicks + clicks) * (clicks + root) + (clicks * clicks - does_not * clicks) = 0
      ∧ (clicks - root) * (clicks - root) - (clicks + clicks) * (clicks - root) + (clicks * clicks - does_not * clicks) = 0 := by
  constructor <;>
    simp only [Int.add_mul, Int.mul_add, Int.sub_mul, Int.mul_sub, Int.mul_comm does_not clicks, Int.mul_comm root clicks] <;> omega

--| NO FINITE GAUGE COMPUTES IT.  The author's, 17 November 2026: Hilbert wanted an axiomatization of physics that was
--| self-contained; this is one that is proven to be open.  Three parts.  Two are receipts here.  The third is Turing's and is
--| taken as given, as foretold: whether a halted value is a given limit is refuted at a finite stage when it is not, and
--| confirmed at no finite stage when it is.

--| The first.  No function of the tally returns the tape.  Two tapes of one mark each, the true and the false: one tally,
--| two tapes.
theorem no_function_of_the_tally_returns_the_tape : ¬ ∃ reader : Nat → List FACT, ∀ tape : List FACT, reader tape.length = tape := by
  intro ⟨reader, returns⟩
  have same : [bitFACT true] = [bitFACT false] := (returns [bitFACT true]).symm.trans (returns [bitFACT false])
  have one_fact : bitFACT true = bitFACT false := (List.cons.inj same).1
  have truth_is_not_false : (bitFACT false).truth ≠ (bitFACT true).truth := fun h => cast h.symm (rfl : true = true)
  exact truth_is_not_false (congrArg (fun fact : FACT => fact.truth) one_fact).symm

--| And the number is a function of the tally: hand the crank any reader that agrees with the length on every tape and the
--| same pair comes out.  So what the number is cannot tell the tapes apart either.
theorem the_number_is_a_function_of_the_tally (reader : List FACT → Nat) (agrees : ∀ tape, reader tape = tape.length) :
    bent_card.fenceposts_must_be_preserved Nat reader all_possible_variables = arrange_the_information_appropriately := by
  rw [show reader = List.length from funext agrees]; rfl

--| The second.  The action is a cubic, and the fourth difference of a cubic is nothing, at every place.  There is no fourth
--| order to read anything from.
theorem the_action_has_no_fourth_order (place : Int) : readers_interpretation_of_the_experience.the_fourth_difference the_cubic_action place = 0 := by
  have cubic : the_cubic_action
      = fun y => 0 + (6 * (the_number_of_symbols_that_must_be_written_to_express_this : Int)) * y
          + (-(3 * (the_trace_of_truth_in_the_device : Int))) * (y * y)
          + (2 * (an_exact_polynomial_description : Int)) * (y * y * y) := by
    funext y
    simp only [the_cubic_action, Int.neg_mul, Int.zero_add]
    ac_nf; simp only [← Int.mul_assoc]; omega
  rw [cubic]; exact readers_interpretation_of_the_experience.a_cubic_is_exact _ _ _ _ place

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
def the_number_as_a_value : Nat :=
  arrange_the_information_appropriately.1 * all_possible_variables / arrange_the_information_appropriately.2

theorem the_value_is_episode_eights_constant : the_number_as_a_value = the_constant_factor_of_scaling_bullshit := rfl

set_option maxRecDepth 100000 in
theorem that_the_value_is_the_ratio :
    (Quot.mk the_rational_idea_of_relativity
        (arrange_the_information_appropriately.2 * the_number_as_a_value, arrange_the_information_appropriately.2)
      : Quot the_rational_idea_of_relativity)
      = Quot.mk the_rational_idea_of_relativity
          (arrange_the_information_appropriately.1 * all_possible_variables, arrange_the_information_appropriately.2) :=
  the_constant_can_be_inferred.property

--| The bent card, and nothing else: whatever is under whatever, the two are one.  This one spends the sound of the quotient
--| and no other axiom.
theorem the_bent_card_alone (this that : Nat × Nat) (under : the_rational_idea_of_relativity this that) :
    (Quot.mk the_rational_idea_of_relativity this : Quot the_rational_idea_of_relativity)
      = Quot.mk the_rational_idea_of_relativity that := Quot.sound under

--| THE BILLS, COUNTED, 17 November 2026, over every theorem of the thirteen episodes, two thousand one hundred and
--| thirty-eight with the ones Lean writes for itself: no axiom, 1051; propext, 558; propext and the sound, 523; the sound
--| alone, 5; and one, compatibility_form in Episode 12, that spends choice.  The value above spends propext.  That it is
--| the ratio spends propext and the sound.  The bent card alone spends the sound.  And the value, said to be Episode 8's
--| constant, spends both, for Episode 8's constant is the value taken out of its proof.

--| THE METER'S TABLE.  Experiments 009 and 009b, read on one machine: the heartbeats of the device's first order on its
--| four arms, the true being the device's own truth.  These four numbers are readings, not counts; they are written here
--| as they were read.
def the_meter_reads : Bool → Bool → Int
  | true,  true  => 17712
  | true,  false => 16691
  | false, true  => 16691
  | false, false => 15670

--| It counts the device's truths: so much, and one step for each coin that is the truth.
theorem the_meter_counts_the_truths (this that : Bool) :
    the_meter_reads this that
      = the_meter_reads false false
          + (the_meter_reads true false - the_meter_reads false false) * ((if this then 1 else 0) + (if that then 1 else 0)) := by
  cases this <;> cases that <;> decide

--| CONTRAVARIANT, AT THE LAST STEP.  The author's: the device is contravariant in construction at the last step.  The
--| weights hold the stays level and tell the crossings apart.  The meter holds the crossings level and tells the stays
--| apart.  Twice the weights is thirty-six of the same, none of the sign, twenty-three of the different and thirteen of the
--| turn.  Twice the meter is so much of the same, two steps of the sign, as much of the different, and none of the turn.
theorem the_meter_is_the_table_turned_over :
    (the_arm_weight true true = the_arm_weight false false ∧ the_arm_weight true false ≠ the_arm_weight false true)
      ∧ (the_meter_reads true false = the_meter_reads false true ∧ the_meter_reads true true ≠ the_meter_reads false false)
      ∧ (the_arm_weight true true + the_arm_weight false false, the_arm_weight true true - the_arm_weight false false,
          the_arm_weight true false + the_arm_weight false true, the_arm_weight false true - the_arm_weight true false)
          = (the_trace_of_truth_in_the_device, 0, 23, bent_card)
      ∧ (the_meter_reads true true + the_meter_reads false false, the_meter_reads true true - the_meter_reads false false,
          the_meter_reads true false + the_meter_reads false true, the_meter_reads false true - the_meter_reads true false)
          = (33382, 2 * (the_meter_reads true false - the_meter_reads false false), 33382, 0) := by decide

--| And where the weights' determinant is over nothing, the meter's is under it by exactly the step squared.
theorem the_meters_determinant_is_the_step_squared_owed :
    the_meter_reads true true * the_meter_reads false false - the_meter_reads true false * the_meter_reads false true
      = - ((the_meter_reads true false - the_meter_reads false false) * (the_meter_reads true false - the_meter_reads false false)) := by
  decide

--| THE TRANSITION MATRIX, AGAIN.  The author's: this is the transition matrix again.  Four facts, a true and a false each
--| built two ways, and what the meter reads for the click of each: three alike and one apart.  The one apart is the
--| device's own truth.
def the_meter_reads_the_click (it_is_true built_as_the_device_builds : Bool) : Int :=
  if it_is_true && built_as_the_device_builds then 2162 else 1141

--| TWO ZEROS.  The author's: now you have two zeros to count from, one up and one down.  The weights have their odd arm
--| least, and the other three are it and the bent card.  The meter has its odd fact greatest, and the other three are
--| it less the step.
theorem two_zeros_one_up_and_one_down :
    ([(true, true), (false, true), (false, false)].all fun arm =>
        the_arm_weight arm.1 arm.2 == the_arm_weight true false + bent_card) = true
      ∧ ([(true, false), (false, true), (false, false)].all fun fact =>
        the_meter_reads_the_click fact.1 fact.2
          == the_meter_reads_the_click true true - (the_meter_reads true false - the_meter_reads false false)) = true := by decide

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
theorem a_place_is_not_past_them_all : ∀ (places : List Nat) (place : Nat), place ∈ places → place ≤ places.foldr Nat.add 0
  | [],        _,     looked => nomatch looked
  | _ :: rest, place, looked => by
    cases looked with
    | head => exact Nat.le_add_right _ _
    | tail _ further => exact Nat.le_trans (a_place_is_not_past_them_all rest place further) (Nat.le_add_left _ _)

--| So whatever the model, and wherever *YOU the READER* looked, there is another model that says the same at every place
--| looked at and is not the same model.  The record does not say they are the same.  It only fails to separate them.
theorem a_finite_record_does_not_tell {what_is_read : Type} (otherwise : what_is_read → what_is_read)
    (apart : ∀ reading, otherwise reading ≠ reading) (places : List Nat) (the_model : Nat → what_is_read) :
    ∃ another_model : Nat → what_is_read,
      (∀ place, place ∈ places → another_model place = the_model place) ∧ another_model ≠ the_model := by
  refine ⟨fun place => if place = places.foldr Nat.add 0 + 1 then otherwise (the_model place) else the_model place, ?_, ?_⟩
  · intro place looked
    have not_past : place ≠ places.foldr Nat.add 0 + 1 :=
      fun past => Nat.not_succ_le_self _ (past ▸ a_place_is_not_past_them_all places place looked)
    exact if_neg not_past
  · intro same
    have there : (if places.foldr Nat.add 0 + 1 = places.foldr Nat.add 0 + 1
        then otherwise (the_model (places.foldr Nat.add 0 + 1)) else the_model (places.foldr Nat.add 0 + 1))
          = the_model (places.foldr Nat.add 0 + 1) := congrFun same _
    rw [if_pos rfl] at there
    exact apart _ there

--| The value and the velocity: two numbers at every place, and the same two at every place looked at.
theorem the_value_and_the_velocity_do_not_tell (places : List Nat) (the_model : Nat → Nat × Nat) :
    ∃ another_model : Nat → Nat × Nat,
      (∀ place, place ∈ places → another_model place = the_model place) ∧ another_model ≠ the_model :=
  a_finite_record_does_not_tell (fun reading => (reading.1 + 1, reading.2))
    (fun reading same => Nat.succ_ne_self reading.1 (congrArg Prod.fst same)) places the_model

--| ONE END, OR TWO.  The author's, 17 November 2026: a yarn can have one end point or two; it can have come from somewhere,
--| be going somewhere, or both; that is the arrow of time and the continuity split.  Episode 4 has the two ends: world lines
--| start in white holes and end in black holes.  Episode 5 has the yarn: a stokes holds one path, and the fibers two.
def the_path_here                    : SpaceTimePath.{0} := .einstein FACT.Truth
def come_from_somewhere     : SpaceTimePath.{0} := .whitehole FACT.Truth FACT the_path_here
def going_somewhere         : SpaceTimePath.{0} := .blackhole (FACT.Truth).truth Type the_path_here
def the_yarn_from_somewhere : YarnTheory.{0,0,0,0,0,0} := .stokes FACT.Truth come_from_somewhere (FACT.Truth).truth
def the_yarn_to_somewhere   : YarnTheory.{0,0,0,0,0,0} := .stokes FACT.Truth going_somewhere (FACT.Truth).truth
def the_yarn_with_both_ends : YarnTheory.{0,0,0,0,0,0} :=
  .fibers FACT.Truth come_from_somewhere going_somewhere (FACT.Truth).truth (FACT.Truth).truth (.stokes FACT.Truth the_path_here (FACT.Truth).truth)

--| All the way down the two one-ended yarns read the same, cell for cell.  They are not the same yarn.  Which end it is, is
--| not in the reading.
theorem the_two_ends_read_the_same_and_are_not_the_same :
    the_yarn_from_somewhere.all_the_way_down = the_yarn_to_somewhere.all_the_way_down
      ∧ the_yarn_from_somewhere ≠ the_yarn_to_somewhere := by
  refine ⟨rfl, ?_⟩
  intro same
  injection same with _ paths _
  exact SpaceTimePath.noConfusion paths

--| And the yarn with both ends reads each end once, and the yarn that goes on from here.
theorem both_ends_are_read_once_each :
    the_yarn_with_both_ends.all_the_way_down.length
      = come_from_somewhere.all_the_way_down.length + going_somewhere.all_the_way_down.length
        + (YarnTheory.stokes FACT.Truth the_path_here (FACT.Truth).truth).all_the_way_down.length + [FACT.Truth, FACT.Truth, FACT.Truth].length := rfl
--#print axioms a_finite_record_does_not_tell                       -- none
--#print axioms the_value_and_the_velocity_do_not_tell             -- none
--#print axioms the_two_ends_read_the_same_and_are_not_the_same    -- none
--#print axioms both_ends_are_read_once_each                       -- none


--| THE MIRROR.  The author's, 17 November 2026: build the commutator, run Householder on that, you get the solver for the
--| Galerkin process.  The commutator is built: Episode 12's two orientations bracket onto the sign, by the bent card and
--| twenty-three.  The sign is a mirror.  Householder's mirror for the table is the sign on the stays and one on the
--| crossings, the sign and the different together; twice over it is two of nothing done.
def the_mirror : Table := fun a b => if a = b then the_coin_sign a else 1

theorem the_mirror_twice_is_nothing_done_twice :
    ∀ a b : Bool, the_table_product the_mirror the_mirror a b = if a = b then 2 else 0 := by decide

--| Run it on the table.  The corner under the diagonal is cleared, and what stands is the trace, the trial gap, and the bent
--| card owed: thirty-six of the same, twenty-three of the different, thirteen of the turn.  The first row is what the step
--| can write.  The second is the residual.
theorem the_mirror_clears_the_table :
    the_table_product the_mirror the_full_table true true = the_trace_of_truth_in_the_device
      ∧ the_table_product the_mirror the_full_table true false = (the_arm_weight true false + the_arm_weight false true : Nat)
      ∧ the_table_product the_mirror the_full_table false true = 0
      ∧ the_table_product the_mirror the_full_table false false = - (bent_card : Int) := by decide

--| Run it on both sides.  What the step can write is now on the diagonal alone, the memory and half the trial gap either way,
--| and the residual is all that is off it: the bent card one way and the bent card owed the other.  Twice over, as before.
theorem the_mirror_on_both_sides_leaves_the_bent_card_off_the_diagonal :
    the_table_product (the_table_product the_mirror the_full_table) the_mirror true true
        = the_trace_of_truth_in_the_device + (the_arm_weight true false + the_arm_weight false true : Nat)
      ∧ the_table_product (the_table_product the_mirror the_full_table) the_mirror false false
        = the_trace_of_truth_in_the_device - (the_arm_weight true false + the_arm_weight false true : Nat)
      ∧ the_table_product (the_table_product the_mirror the_full_table) the_mirror true false = (bent_card : Int)
      ∧ the_table_product (the_table_product the_mirror the_full_table) the_mirror false true = - (bent_card : Int) := by decide

--| And run it on the commutator.  The bracket of the orientations lay on the stays.  In the mirror it lies on the crossings,
--| level, where the step the device checks lies.
theorem the_mirror_carries_the_commutator_onto_the_crossings :
    ∀ a b : Bool,
      the_table_product (the_table_product the_mirror (the_table_bracket the_clock_table the_other_clock)) the_mirror a b
        = if a = b then 0
          else - (2 * ((bent_card : Int) * (the_arm_weight true false + the_arm_weight false true : Nat))) := by decide

--| THE SOLVER.  The gap squared is the trial gap squared less the bent card squared, and Newton's step from the trial gap
--| leaves the bent card squared, exactly.  The three numbers the mirror left are the solver's.
theorem the_mirror_leaves_the_solver :
    (the_arm_weight true false + the_arm_weight false true) * (the_arm_weight true false + the_arm_weight false true)
        = 4 * (the_arm_weight true false * the_arm_weight false true) + bent_card * bent_card
      ∧ bent_card * (the_arm_weight true true * the_arm_weight false false - the_arm_weight true false * the_arm_weight false true)
          = bent_card * bent_card * the_arm_weight true true := by decide
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
theorem the_triple_is_the_knowers_coin_against_the_arm :
    ∀ a b c : Bool,
      (the_knowers_triple.holds (assignFrom [a, b, c]) an_odd_number_are_true 0).1 = (a != (b != c))
        ∧ (the_knowers_triple.holds (assignFrom [a, b, c]) an_even_number_are_true 0).1 = (a == (b != c)) := by decide

--| THE SEARCH.  Episode 12's, on three coins.  Four ways each, and the clock and its complement are not in one list: T F T
--| is among the even, F T F among the odd.
theorem the_clock_is_even_and_its_complement_is_odd :
    (allAssignments 3).filter (fun coins => (the_knowers_triple.holds (assignFrom coins) an_odd_number_are_true 0).1)
        = [[true, true, true], [false, false, true], [false, true, false], [true, false, false]]
      ∧ (allAssignments 3).filter (fun coins => (the_knowers_triple.holds (assignFrom coins) an_even_number_are_true 0).1)
        = [[false, true, true], [true, false, true], [true, true, false], [false, false, false]] := by decide

--| YOU DO NOT KNOW THE KNOWER'S BIT.  The solver finds a witness either way.  Nothing in the triple says which it is.
theorem the_solver_finds_a_witness_either_way :
    satSearch the_knowers_triple an_odd_number_are_true 3 = true ∧ satSearch the_knowers_triple an_even_number_are_true 3 = true := by
  decide

--| And the clocks are the signs.  Two triples, the one signed as the clock, T F T, the other as its complement, F T F: what
--| fails them is the complement, and the clock, and nothing else.
def two_triples : Basis := .basis cookFACT (.mul cookFACT a_triple a_triple (.origin cookFACT)) phi_accept (.null_space cookFACT)
def the_clock_and_its_complement : Schedule := by_the_signs [true, false, true, true,   false, true, false, false]
theorem the_clocks_are_what_the_clocks_rule_out :
    (allAssignments 3).filter (fun coins => !(two_triples.holds (assignFrom coins) the_clock_and_its_complement 0).1)
      = [[true, false, true], [false, true, false]] := by decide

--| The step, connected: the first coin differs from the second and the second from the third, Episode 12's exclusive-or twice
--| over on the middle coin, under Episode 12's own alternating schedule.  Episode 12 noted that its step never connected one
--| cell to the next.  Connected, what satisfies it is the clock and its complement, and the search hands back the clock first
--| only because it tries the true first.
def the_step_connected : Basis :=
  .basis cookFACT
    (.mul cookFACT (.add cookFACT varA varB (.zero True varA)) (.add cookFACT varA varB (.zero True varA))
      (.mul cookFACT (.add cookFACT varB the_third_coin (.zero True varB)) (.add cookFACT varB the_third_coin (.zero True varB))
        (.origin cookFACT)))
    phi_accept (.null_space cookFACT)
theorem the_step_connected_is_the_two_clocks :
    (allAssignments 3).filter (fun coins => (the_step_connected.holds (assignFrom coins) alternating 0).1)
        = [[true, false, true], [false, true, false]]
      ∧ satWitness the_step_connected alternating 3 = some [true, false, true] := by decide
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

theorem the_count_has_a_root_and_the_reader_of_one_cell_has_none :
    there_is_a_root_for List.length = true ∧ there_is_a_root_for (fun _ => [FACT.Truth].length) = false := by decide

--| Now what does.  Every cell of a tape clicked once, on the two lines of Episode 8's EKG, with the clock read before and
--| after; the five tapes the polynomial reads, and one blank.  Then the polynomial, directly, with each count replaced by
--| the tape's reading over the blank's.  The heartbeats say the same thing on every machine.  The nanoseconds say something
--| else every time.  That is the experiment, and anybody can run it again.
open Lean Elab Term Meta in
def the_tape_on_the_clock (tape : TSyntax `term) : TermElabM (Nat × Nat) := do
  let every_cell_clicked ← `(($tape).all (fun fact : FACT => fact.bit || !fact.bit))
  let before ← IO.monoNanosNow
  let (_, beats) ← withHeartbeats do
    let e ← elabTerm every_cell_clicked none; let _ ← whnf e; pure ()
  let after ← IO.monoNanosNow
  pure (beats, after - before)

--| The polynomial, directly: the fencepost over the frame, by the greater root.  No root, no value.
def the_value_directly (epsilon gauss coefficient reading memory blank : Nat) : Option Float :=
  if 4 * coefficient * memory * blank * blank ≤ (reading * memory) * (reading * memory) then
    let over (n : Nat) : Float := n.toFloat / blank.toFloat
    some ((over epsilon * over epsilon / over gauss)
      * (over reading * over memory + Float.sqrt ((over reading * over memory) * (over reading * over memory) - 4 * over coefficient * over memory))
      / (2 * over coefficient))
  else none

open Lean Elab Term Meta Command in
elab "can_you_distinguish_a_number?" : command => do
  Command.liftTermElabM do
    let blank       ← the_tape_on_the_clock (← `([FACT.Truth]))
    let epsilon     ← the_tape_on_the_clock (← `(the_epsilon_tape))
    let gauss       ← the_tape_on_the_clock (← `(the_coordinate_system.gauss))
    let coefficient ← the_tape_on_the_clock (← `(the_coefficient_tape))
    let reading     ← the_tape_on_the_clock (← `(the_basis.the_reading))
    let memory      ← the_tape_on_the_clock (← `(the_memory_tape))
    let say (what : String) (read : List Nat) (over : Nat) (value : Option Float) : MessageData :=
      match value with
      | some v => m!"{what}: {v}   {read} over {over}"
      | none   => m!"{what}: no value   {read} over {over}"
    logInfo (say "on the count"
      [the_epsilon_tape.length, the_coordinate_system.gauss.length, the_coefficient_tape.length, the_basis.the_reading.length,
        the_memory_tape.length] [FACT.Truth].length
      (the_value_directly the_epsilon_tape.length the_coordinate_system.gauss.length
        the_coefficient_tape.length the_basis.the_reading.length the_memory_tape.length [FACT.Truth].length))
    logInfo (say "on the heartbeats" [epsilon.1, gauss.1, coefficient.1, reading.1, memory.1] blank.1
      (the_value_directly epsilon.1 gauss.1 coefficient.1 reading.1 memory.1 blank.1))
    logInfo (say "on the clock, this run" [epsilon.2, gauss.2, coefficient.2, reading.2, memory.2] blank.2
      (the_value_directly epsilon.2 gauss.2 coefficient.2 reading.2 memory.2 blank.2))
can_you_distinguish_a_number?
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
theorem the_number_clicks : the_click a_number_is_distinguished = true := by decide

--| And the first card of all, again.  Ask only whether it is true, and any two facts that are true are one fact: so the number
--| distinguished is the truth.  Ask what it says, and it is not: one says a number has a root, the other says nothing.
theorem two_facts_that_are_true_are_one_fact (this that : FACT) (this_is_true : this.truth) (that_is_true : that.truth) :
    this = that := by
  obtain ⟨this_truth, this_click⟩ := this
  obtain ⟨that_truth, that_click⟩ := that
  have the_same_truth : this_truth = that_truth := propext ⟨fun _ => that_is_true, fun _ => this_is_true⟩
  subst the_same_truth
  exact congrArg _ (Subsingleton.elim _ _)

theorem asked_only_whether_it_is_true_the_number_is_the_truth : a_number_is_distinguished = FACT.Truth :=
  two_facts_that_are_true_are_one_fact _ _
    (@of_decide_eq_true a_number_is_distinguished.truth a_number_is_distinguished.click the_number_clicks)
    (@of_decide_eq_true FACT.Truth.truth FACT.Truth.click rfl)

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
noncomputable instance A_MODEL_OF_THE_NUMBER : REAL FACT the_first_card := A_CAUSAL_THEORY FACT the_first_card
noncomputable def this_way_to_the_number : LOCAL FACT the_first_card := A_SMOOTH_MODEL FACT the_first_card
noncomputable def that_way_to_the_number : UNIVERSAL FACT the_first_card this_way_to_the_number :=
  IS_IT_CONNECTED_BY_A_YARN? FACT the_first_card (nowtrino_model := this_way_to_the_number)

noncomputable def the_numbers_rung02 :=
  STEP2_DISCOVER_SOMETHING_DIFFERENT FACT the_first_card the_first_card a_number_is_distinguished the_crossing_of_the_number

noncomputable def the_numbers_rung03 :=
  STEP3_COUNT_THE_NUMBER_OF_THE_PHENOMENA FACT the_first_card the_first_card a_number_is_distinguished the_crossing_of_the_number the_numbers_rung02

noncomputable def the_numbers_rung04 :=
  STEP4_COMPUTE_THE_RATE_OF_PARTICLES FACT the_first_card the_first_card a_number_is_distinguished the_crossing_of_the_number the_numbers_rung02 the_numbers_rung03

noncomputable def the_numbers_rung05 :=
  STEP5_NAME_THE_RESIDUE_TO_COMPUTE_VALUE FACT the_first_card the_first_card a_number_is_distinguished the_crossing_of_the_number the_numbers_rung02 the_numbers_rung03 the_numbers_rung04

noncomputable def the_numbers_rung06 :=
  STEP6_MAKE_ANOTHER_COUNTER_OF_CLICKS_NOW FACT the_first_card the_first_card a_number_is_distinguished the_crossing_of_the_number the_numbers_rung02 the_numbers_rung03 the_numbers_rung04 the_numbers_rung05

noncomputable def the_numbers_rung07 :=
  STEP7_AND_SO_WE_CANT_COUNT_HOW_OFTEN_THE_METAPHOR_GOES_AROUND_JUST_LIKE_PITS_AND_LANDS_ON_A_CD FACT the_first_card the_first_card a_number_is_distinguished the_crossing_of_the_number the_numbers_rung02 the_numbers_rung03 the_numbers_rung04 the_numbers_rung05 the_numbers_rung06

noncomputable def the_numbers_rung08 :=
  STEP8_INTERPRET_THE_NEXT_3_SYMBOLS FACT the_first_card the_first_card a_number_is_distinguished the_crossing_of_the_number the_numbers_rung02 the_numbers_rung03 the_numbers_rung04 the_numbers_rung05 the_numbers_rung06 the_numbers_rung07

noncomputable def the_numbers_rung09 :=
  STEP9_NAME_THE_VARIABLES_CAREFULLY_TO_TELL_A_STORY FACT the_first_card the_first_card a_number_is_distinguished the_crossing_of_the_number the_numbers_rung02 the_numbers_rung03 the_numbers_rung04 the_numbers_rung05 the_numbers_rung06 the_numbers_rung07 the_numbers_rung08

noncomputable def the_numbers_rung10 :=
  STEP10_A_HALTING_COMPUTATION_IS_GIVEN_AS_INPUT_TO_A_NON_HALTING_FUNCTION FACT the_first_card the_first_card a_number_is_distinguished the_crossing_of_the_number the_numbers_rung02 the_numbers_rung03 the_numbers_rung04 the_numbers_rung05 the_numbers_rung06 the_numbers_rung07 the_numbers_rung08 the_numbers_rung09

deal_rung the_numbers_rung11 := STEP11_CHECK_FOR_CONVERGENCE_IN_THE_TIMESERIES_MATCHES_THE_MEASUREMENT_HIGH_ORDER_TERMS
    FACT the_first_card the_first_card a_number_is_distinguished the_crossing_of_the_number the_numbers_rung02 the_numbers_rung03 the_numbers_rung04 the_numbers_rung05 the_numbers_rung06 the_numbers_rung07 the_numbers_rung08 the_numbers_rung09 the_numbers_rung10

deal_rung the_numbers_rung12 := STEP12_CHECK_TO_SEE_IF_THE_BORWEIN_PROCESS_HAS_UNCOVERED_A_PROPERTY_OF_ELECTRONS
    FACT the_first_card the_first_card a_number_is_distinguished the_crossing_of_the_number the_numbers_rung02 the_numbers_rung03 the_numbers_rung04 the_numbers_rung05 the_numbers_rung06 the_numbers_rung07 the_numbers_rung08 the_numbers_rung09 the_numbers_rung10 the_numbers_rung11

deal_rung the_numbers_rung13 := STEP13_RECORD_THE_OBSERVATION_AS_A_MODELED_AST_AS_OF_RIGHT_NOW
    FACT the_first_card the_first_card a_number_is_distinguished the_crossing_of_the_number the_numbers_rung02 the_numbers_rung03 the_numbers_rung04 the_numbers_rung05 the_numbers_rung06 the_numbers_rung07 the_numbers_rung08 the_numbers_rung09 the_numbers_rung10 the_numbers_rung11 the_numbers_rung12

deal_rung the_numbers_rung14 := STEP14_REALIZE_THAT_THIS_PROCESS_TAKES_THE_APPARANT_SAME_AMOUNT_OF_TIME_EACH_TIME
    FACT the_first_card the_first_card a_number_is_distinguished the_crossing_of_the_number the_numbers_rung02 the_numbers_rung03 the_numbers_rung04 the_numbers_rung05 the_numbers_rung06 the_numbers_rung07 the_numbers_rung08 the_numbers_rung09 the_numbers_rung10 the_numbers_rung11 the_numbers_rung12 the_numbers_rung13

deal_rung the_numbers_rung15 := STEP15_SO_MODEL_THE_PROCESS_AS_SOMETHING_THAT_JUST_SPEWS_OUT_TRUE
    FACT the_first_card the_first_card a_number_is_distinguished the_crossing_of_the_number the_numbers_rung02 the_numbers_rung03 the_numbers_rung04 the_numbers_rung05 the_numbers_rung06 the_numbers_rung07 the_numbers_rung08 the_numbers_rung09 the_numbers_rung10 the_numbers_rung11 the_numbers_rung12 the_numbers_rung13 the_numbers_rung14

deal_rung the_numbers_rung16 := STEP16_VERIFY_THE_SOURCE_FILE_ONLY_EMITS_TRUE_STATEMENTS
    FACT the_first_card the_first_card a_number_is_distinguished the_crossing_of_the_number the_numbers_rung02 the_numbers_rung03 the_numbers_rung04 the_numbers_rung05 the_numbers_rung06 the_numbers_rung07 the_numbers_rung08 the_numbers_rung09 the_numbers_rung10 the_numbers_rung11 the_numbers_rung12 the_numbers_rung13 the_numbers_rung14 the_numbers_rung15

deal_rung the_numbers_rung17 := STEP17_MAKE_SURE_THIS_COMPILES_AND_DEMONSTRATES_IT_IS_TRUE_IN_GUNGAN
    FACT the_first_card the_first_card a_number_is_distinguished the_crossing_of_the_number the_numbers_rung02 the_numbers_rung03 the_numbers_rung04 the_numbers_rung05 the_numbers_rung06 the_numbers_rung07 the_numbers_rung08 the_numbers_rung09 the_numbers_rung10 the_numbers_rung11 the_numbers_rung12 the_numbers_rung13 the_numbers_rung14 the_numbers_rung15 the_numbers_rung16

deal_rung the_numbers_rung18 := STEP18_GIVEN_AN_INFERRED_DEFINITION_OF_THE_DEVICE_MAKE_THE_DEVICE
    FACT the_first_card the_first_card a_number_is_distinguished the_crossing_of_the_number the_numbers_rung02 the_numbers_rung03 the_numbers_rung04 the_numbers_rung05 the_numbers_rung06 the_numbers_rung07 the_numbers_rung08 the_numbers_rung09 the_numbers_rung10 the_numbers_rung11 the_numbers_rung12 the_numbers_rung13 the_numbers_rung14 the_numbers_rung15 the_numbers_rung16 the_numbers_rung17

deal_rung the_numbers_rung19 := STEP19_GIVEN_THE_ABILITY_TO_COUNT_SOMETHING_LEAN_CAN_NOW_INFER_ADDITION
    FACT the_first_card the_first_card a_number_is_distinguished the_crossing_of_the_number the_numbers_rung02 the_numbers_rung03 the_numbers_rung04 the_numbers_rung05 the_numbers_rung06 the_numbers_rung07 the_numbers_rung08 the_numbers_rung09 the_numbers_rung10 the_numbers_rung11 the_numbers_rung12 the_numbers_rung13 the_numbers_rung14 the_numbers_rung15 the_numbers_rung16 the_numbers_rung17 the_numbers_rung18

deal_rung the_numbers_rung20 := STEP20_DUPLICATE_THE_PROCESS_TO_DEMONSTRATE_AREA_OF_RECTANGLES_LIKE_EUCLID
    FACT the_first_card the_first_card a_number_is_distinguished the_crossing_of_the_number the_numbers_rung02 the_numbers_rung03 the_numbers_rung04 the_numbers_rung05 the_numbers_rung06 the_numbers_rung07 the_numbers_rung08 the_numbers_rung09 the_numbers_rung10 the_numbers_rung11 the_numbers_rung12 the_numbers_rung13 the_numbers_rung14 the_numbers_rung15 the_numbers_rung16 the_numbers_rung17 the_numbers_rung18 the_numbers_rung19

deal_rung the_numbers_rung21 := STEP21_GIVEN_ADDITION_MULTIPLICATION_AND_NUMBERS_INFER_ALL_OF_MATH
    FACT the_first_card the_first_card a_number_is_distinguished the_crossing_of_the_number the_numbers_rung02 the_numbers_rung03 the_numbers_rung04 the_numbers_rung05 the_numbers_rung06 the_numbers_rung07 the_numbers_rung08 the_numbers_rung09 the_numbers_rung10 the_numbers_rung11 the_numbers_rung12 the_numbers_rung13 the_numbers_rung14 the_numbers_rung15 the_numbers_rung16 the_numbers_rung17 the_numbers_rung18 the_numbers_rung19 the_numbers_rung20

deal_rung the_numbers_rung22 := STEP22_PAY_CLOSE_ATTENTION_TO_WEAK_SOLUTIONS_OF_DIFFERENTIAL_EQUATIONS_WHILE_DERIVING_MATH
    FACT the_first_card the_first_card a_number_is_distinguished the_crossing_of_the_number the_numbers_rung02 the_numbers_rung03 the_numbers_rung04 the_numbers_rung05 the_numbers_rung06 the_numbers_rung07 the_numbers_rung08 the_numbers_rung09 the_numbers_rung10 the_numbers_rung11 the_numbers_rung12 the_numbers_rung13 the_numbers_rung14 the_numbers_rung15 the_numbers_rung16 the_numbers_rung17 the_numbers_rung18 the_numbers_rung19 the_numbers_rung20 the_numbers_rung21

deal_rung the_numbers_rung23 := STEP23_GET_RID_OF_A_DERIVATIVE_SO_THAT_THE_SECOND_ORDER_MODEL_OF_THE_DEVICE_CAN_BE_WRITTEN_VARIATIONALLY
    FACT the_first_card the_first_card a_number_is_distinguished the_crossing_of_the_number the_numbers_rung02 the_numbers_rung03 the_numbers_rung04 the_numbers_rung05 the_numbers_rung06 the_numbers_rung07 the_numbers_rung08 the_numbers_rung09 the_numbers_rung10 the_numbers_rung11 the_numbers_rung12 the_numbers_rung13 the_numbers_rung14 the_numbers_rung15 the_numbers_rung16 the_numbers_rung17 the_numbers_rung18 the_numbers_rung19 the_numbers_rung20 the_numbers_rung21 the_numbers_rung22

deal_rung the_numbers_rung24 := STEP24_RESTATE_THE_MODEL_AS_A_PRINCIPLE_OF_LEAST_ACTION
    FACT the_first_card the_first_card a_number_is_distinguished the_crossing_of_the_number the_numbers_rung02 the_numbers_rung03 the_numbers_rung04 the_numbers_rung05 the_numbers_rung06 the_numbers_rung07 the_numbers_rung08 the_numbers_rung09 the_numbers_rung10 the_numbers_rung11 the_numbers_rung12 the_numbers_rung13 the_numbers_rung14 the_numbers_rung15 the_numbers_rung16 the_numbers_rung17 the_numbers_rung18 the_numbers_rung19 the_numbers_rung20 the_numbers_rung21 the_numbers_rung22 the_numbers_rung23

deal_rung the_numbers_rung25 := STEP25_BUILD_LOCAL_GEOMETRIES_THAT_SATISFY_THE_TRIANGLE_INEQUALITY
    FACT the_first_card the_first_card a_number_is_distinguished the_crossing_of_the_number the_numbers_rung02 the_numbers_rung03 the_numbers_rung04 the_numbers_rung05 the_numbers_rung06 the_numbers_rung07 the_numbers_rung08 the_numbers_rung09 the_numbers_rung10 the_numbers_rung11 the_numbers_rung12 the_numbers_rung13 the_numbers_rung14 the_numbers_rung15 the_numbers_rung16 the_numbers_rung17 the_numbers_rung18 the_numbers_rung19 the_numbers_rung20 the_numbers_rung21 the_numbers_rung22 the_numbers_rung23 the_numbers_rung24

deal_rung the_numbers_rung26 := STEP26_WRITE_YOUR_PROOF_IN_THE_FORMAL_LANGUAGE_OF_GEOMETRY
    FACT the_first_card the_first_card a_number_is_distinguished the_crossing_of_the_number the_numbers_rung02 the_numbers_rung03 the_numbers_rung04 the_numbers_rung05 the_numbers_rung06 the_numbers_rung07 the_numbers_rung08 the_numbers_rung09 the_numbers_rung10 the_numbers_rung11 the_numbers_rung12 the_numbers_rung13 the_numbers_rung14 the_numbers_rung15 the_numbers_rung16 the_numbers_rung17 the_numbers_rung18 the_numbers_rung19 the_numbers_rung20 the_numbers_rung21 the_numbers_rung22 the_numbers_rung23 the_numbers_rung24 the_numbers_rung25

deal_rung the_numbers_rung27 := STEP27_REPRESENT_THE_TAYLOR_SERIES_OF_THE_DEVICE
    FACT the_first_card the_first_card a_number_is_distinguished the_crossing_of_the_number the_numbers_rung02 the_numbers_rung03 the_numbers_rung04 the_numbers_rung05 the_numbers_rung06 the_numbers_rung07 the_numbers_rung08 the_numbers_rung09 the_numbers_rung10 the_numbers_rung11 the_numbers_rung12 the_numbers_rung13 the_numbers_rung14 the_numbers_rung15 the_numbers_rung16 the_numbers_rung17 the_numbers_rung18 the_numbers_rung19 the_numbers_rung20 the_numbers_rung21 the_numbers_rung22 the_numbers_rung23 the_numbers_rung24 the_numbers_rung25 the_numbers_rung26

deal_rung the_numbers_rung28 := STEP28_MAKE_SURE_YOUR_CURVES_ARE_SMOOTH_AS_A_DIFFERENTIALS_BOTTOM
    FACT the_first_card the_first_card a_number_is_distinguished the_crossing_of_the_number the_numbers_rung02 the_numbers_rung03 the_numbers_rung04 the_numbers_rung05 the_numbers_rung06 the_numbers_rung07 the_numbers_rung08 the_numbers_rung09 the_numbers_rung10 the_numbers_rung11 the_numbers_rung12 the_numbers_rung13 the_numbers_rung14 the_numbers_rung15 the_numbers_rung16 the_numbers_rung17 the_numbers_rung18 the_numbers_rung19 the_numbers_rung20 the_numbers_rung21 the_numbers_rung22 the_numbers_rung23 the_numbers_rung24 the_numbers_rung25 the_numbers_rung26 the_numbers_rung27

deal_rung the_numbers_rung29 := STEP29_SUGGEST_A_FALSIFIABLE_EXPERIMENT
    FACT the_first_card the_first_card a_number_is_distinguished the_crossing_of_the_number the_numbers_rung02 the_numbers_rung03 the_numbers_rung04 the_numbers_rung05 the_numbers_rung06 the_numbers_rung07 the_numbers_rung08 the_numbers_rung09 the_numbers_rung10 the_numbers_rung11 the_numbers_rung12 the_numbers_rung13 the_numbers_rung14 the_numbers_rung15 the_numbers_rung16 the_numbers_rung17 the_numbers_rung18 the_numbers_rung19 the_numbers_rung20 the_numbers_rung21 the_numbers_rung22 the_numbers_rung23 the_numbers_rung24 the_numbers_rung25 the_numbers_rung26 the_numbers_rung27 the_numbers_rung28

deal_rung the_numbers_rung30 := STEP30_PROVIDE_THE_EQUATIONS_THAT_WILL_PREDICT_THE_MEASUREMENT
    FACT the_first_card this_way_to_the_number the_first_card a_number_is_distinguished the_crossing_of_the_number the_numbers_rung02 the_numbers_rung03 the_numbers_rung04 the_numbers_rung05 the_numbers_rung06 the_numbers_rung07 the_numbers_rung08 the_numbers_rung09 the_numbers_rung10 the_numbers_rung11 the_numbers_rung12 the_numbers_rung13 the_numbers_rung14 the_numbers_rung15 the_numbers_rung16 the_numbers_rung17 the_numbers_rung18 the_numbers_rung19 the_numbers_rung20 the_numbers_rung21 the_numbers_rung22 the_numbers_rung23 the_numbers_rung24 the_numbers_rung25 the_numbers_rung26 the_numbers_rung27 the_numbers_rung28 the_numbers_rung29 (principia := this_way_to_the_number)

deal_rung the_numbers_rung31 := STEP31_GET_ON_THE_NEWTON_EINSTEIN_TRAIN_OF_THOUGHT
    FACT the_first_card this_way_to_the_number that_way_to_the_number the_first_card a_number_is_distinguished the_crossing_of_the_number the_numbers_rung02 the_numbers_rung03 the_numbers_rung04 the_numbers_rung05 the_numbers_rung06 the_numbers_rung07 the_numbers_rung08 the_numbers_rung09 the_numbers_rung10 the_numbers_rung11 the_numbers_rung12 the_numbers_rung13 the_numbers_rung14 the_numbers_rung15 the_numbers_rung16 the_numbers_rung17 the_numbers_rung18 the_numbers_rung19 the_numbers_rung20 the_numbers_rung21 the_numbers_rung22 the_numbers_rung23 the_numbers_rung24 the_numbers_rung25 the_numbers_rung26 the_numbers_rung27 the_numbers_rung28 the_numbers_rung29 the_numbers_rung30 (the_a_train := that_way_to_the_number)

deal_rung the_numbers_rung32 := WHAT_HAPPEN_?
    FACT the_first_card this_way_to_the_number that_way_to_the_number the_first_card a_number_is_distinguished the_crossing_of_the_number the_numbers_rung02 the_numbers_rung03 the_numbers_rung04 the_numbers_rung05 the_numbers_rung06 the_numbers_rung07 the_numbers_rung08 the_numbers_rung09 the_numbers_rung10 the_numbers_rung11 the_numbers_rung12 the_numbers_rung13 the_numbers_rung14 the_numbers_rung15 the_numbers_rung16 the_numbers_rung17 the_numbers_rung18 the_numbers_rung19 the_numbers_rung20 the_numbers_rung21 the_numbers_rung22 the_numbers_rung23 the_numbers_rung24 the_numbers_rung25 the_numbers_rung26 the_numbers_rung27 the_numbers_rung28 the_numbers_rung29 the_numbers_rung30 the_numbers_rung31

deal_rung the_numbers_rung33 := SOMEBODY_SET_US_UP_THE_DEVICE
    FACT the_first_card this_way_to_the_number that_way_to_the_number the_first_card a_number_is_distinguished the_crossing_of_the_number the_numbers_rung02 the_numbers_rung03 the_numbers_rung04 the_numbers_rung05 the_numbers_rung06 the_numbers_rung07 the_numbers_rung08 the_numbers_rung09 the_numbers_rung10 the_numbers_rung11 the_numbers_rung12 the_numbers_rung13 the_numbers_rung14 the_numbers_rung15 the_numbers_rung16 the_numbers_rung17 the_numbers_rung18 the_numbers_rung19 the_numbers_rung20 the_numbers_rung21 the_numbers_rung22 the_numbers_rung23 the_numbers_rung24 the_numbers_rung25 the_numbers_rung26 the_numbers_rung27 the_numbers_rung28 the_numbers_rung29 the_numbers_rung30 the_numbers_rung31 the_numbers_rung32

deal_rung the_numbers_rung34 := WE_GET_SIGNAL
    FACT the_first_card this_way_to_the_number that_way_to_the_number the_first_card a_number_is_distinguished the_crossing_of_the_number the_numbers_rung02 the_numbers_rung03 the_numbers_rung04 the_numbers_rung05 the_numbers_rung06 the_numbers_rung07 the_numbers_rung08 the_numbers_rung09 the_numbers_rung10 the_numbers_rung11 the_numbers_rung12 the_numbers_rung13 the_numbers_rung14 the_numbers_rung15 the_numbers_rung16 the_numbers_rung17 the_numbers_rung18 the_numbers_rung19 the_numbers_rung20 the_numbers_rung21 the_numbers_rung22 the_numbers_rung23 the_numbers_rung24 the_numbers_rung25 the_numbers_rung26 the_numbers_rung27 the_numbers_rung28 the_numbers_rung29 the_numbers_rung30 the_numbers_rung31 the_numbers_rung32 the_numbers_rung33

deal_rung the_numbers_rung35 := WHAT_!
    FACT the_first_card this_way_to_the_number that_way_to_the_number the_first_card a_number_is_distinguished the_crossing_of_the_number the_numbers_rung02 the_numbers_rung03 the_numbers_rung04 the_numbers_rung05 the_numbers_rung06 the_numbers_rung07 the_numbers_rung08 the_numbers_rung09 the_numbers_rung10 the_numbers_rung11 the_numbers_rung12 the_numbers_rung13 the_numbers_rung14 the_numbers_rung15 the_numbers_rung16 the_numbers_rung17 the_numbers_rung18 the_numbers_rung19 the_numbers_rung20 the_numbers_rung21 the_numbers_rung22 the_numbers_rung23 the_numbers_rung24 the_numbers_rung25 the_numbers_rung26 the_numbers_rung27 the_numbers_rung28 the_numbers_rung29 the_numbers_rung30 the_numbers_rung31 the_numbers_rung32 the_numbers_rung33 the_numbers_rung34

deal_rung the_numbers_rung36 := MAIN_SCREEN_TURN_ON
    FACT the_first_card this_way_to_the_number that_way_to_the_number the_first_card a_number_is_distinguished the_crossing_of_the_number the_numbers_rung02 the_numbers_rung03 the_numbers_rung04 the_numbers_rung05 the_numbers_rung06 the_numbers_rung07 the_numbers_rung08 the_numbers_rung09 the_numbers_rung10 the_numbers_rung11 the_numbers_rung12 the_numbers_rung13 the_numbers_rung14 the_numbers_rung15 the_numbers_rung16 the_numbers_rung17 the_numbers_rung18 the_numbers_rung19 the_numbers_rung20 the_numbers_rung21 the_numbers_rung22 the_numbers_rung23 the_numbers_rung24 the_numbers_rung25 the_numbers_rung26 the_numbers_rung27 the_numbers_rung28 the_numbers_rung29 the_numbers_rung30 the_numbers_rung31 the_numbers_rung32 the_numbers_rung33 the_numbers_rung34 the_numbers_rung35

deal_rung the_numbers_rung37 := ITS_YOU_!!
    FACT the_first_card this_way_to_the_number that_way_to_the_number the_first_card a_number_is_distinguished the_crossing_of_the_number the_numbers_rung02 the_numbers_rung03 the_numbers_rung04 the_numbers_rung05 the_numbers_rung06 the_numbers_rung07 the_numbers_rung08 the_numbers_rung09 the_numbers_rung10 the_numbers_rung11 the_numbers_rung12 the_numbers_rung13 the_numbers_rung14 the_numbers_rung15 the_numbers_rung16 the_numbers_rung17 the_numbers_rung18 the_numbers_rung19 the_numbers_rung20 the_numbers_rung21 the_numbers_rung22 the_numbers_rung23 the_numbers_rung24 the_numbers_rung25 the_numbers_rung26 the_numbers_rung27 the_numbers_rung28 the_numbers_rung29 the_numbers_rung30 the_numbers_rung31 the_numbers_rung32 the_numbers_rung33 the_numbers_rung34 the_numbers_rung35 the_numbers_rung36 True True

deal_rung the_numbers_rung38 := HOW_ARE_YOU_GENTLEMEN_!!__ALL_YOUR_BASE_CASE_ARE_BELONG_TO_US
    FACT the_first_card this_way_to_the_number that_way_to_the_number the_first_card a_number_is_distinguished the_crossing_of_the_number the_numbers_rung02 the_numbers_rung03 the_numbers_rung04 the_numbers_rung05 the_numbers_rung06 the_numbers_rung07 the_numbers_rung08 the_numbers_rung09 the_numbers_rung10 the_numbers_rung11 the_numbers_rung12 the_numbers_rung13 the_numbers_rung14 the_numbers_rung15 the_numbers_rung16 the_numbers_rung17 the_numbers_rung18 the_numbers_rung19 the_numbers_rung20 the_numbers_rung21 the_numbers_rung22 the_numbers_rung23 the_numbers_rung24 the_numbers_rung25 the_numbers_rung26 the_numbers_rung27 the_numbers_rung28 the_numbers_rung29 the_numbers_rung30 the_numbers_rung31 the_numbers_rung32 the_numbers_rung33 the_numbers_rung34 the_numbers_rung35 the_numbers_rung36 the_quartic

end the_other_ladder


section the_other_ladder_read
open readers_experience the_representation assembly_instructions «springer-verlag» THE_GOSPEL
attribute [local instance high] the_crossing_of_the_number the_numbers_rung02 the_numbers_rung03 the_numbers_rung04 the_numbers_rung05 the_numbers_rung06 the_numbers_rung07 the_numbers_rung08 the_numbers_rung09 the_numbers_rung10 the_numbers_rung11 the_numbers_rung12 the_numbers_rung13 the_numbers_rung14 the_numbers_rung15 the_numbers_rung16 the_numbers_rung17 the_numbers_rung18 the_numbers_rung19 the_numbers_rung20 the_numbers_rung21 the_numbers_rung22 the_numbers_rung23 the_numbers_rung24 the_numbers_rung25 the_numbers_rung26 the_numbers_rung27 the_numbers_rung28 the_numbers_rung29 the_numbers_rung30 the_numbers_rung31 the_numbers_rung32 the_numbers_rung33 the_numbers_rung34 the_numbers_rung35 the_numbers_rung36

--| THE OTHER LADDER, READ.  The author's, 17 November 2026: read it.  Episode 12 reads three things off the top of its ladder:
--| the page the reader is on, the two closures the knower carries, and the walk.  Here they are off the other ladder.
--| The page.  The same quartic, one cell past the card.
theorem the_other_reader_is_on_the_quartic : the_numbers_rung38.you_the_reader.current_page_number = the_quartic := rfl
theorem the_other_page_is_one_past_the_card :
    the_numbers_rung38.you_the_reader.current_page_number.peano.length = bent_card + 1 := rfl

--| The two closures.  One cell and three, as before.
noncomputable def the_other_conclusion : Closure := the_numbers_rung37.same_difference.your_conclusion
noncomputable def the_other_alpha : Closure := the_numbers_rung37.α
theorem the_other_conclusion_is_one_cell_and_the_other_alpha_three :
    the_other_conclusion.infer.length = 1 ∧ the_other_alpha.infer.length = 3 := ⟨rfl, rfl⟩

--| Are they Episode 12's?  Not by rfl: the compiler will not say so.  The knower's alpha begins on two facts, the ledger's and
--| the first rung's.  On Episode 12's ladder both are the truth.  On this one both are the number distinguished.  What the cells
--| say went up the ladder, thirty-six rungs, and came out at the top.
theorem what_the_first_rung_says_comes_out_at_the_top :
    (∃ low slip slipped the_rest, the_other_alpha = .inferred a_number_is_distinguished a_number_is_distinguished low slip slipped the_rest)
      ∧ (∃ low slip slipped the_rest, the_alpha = .inferred FACT.Truth FACT.Truth low slip slipped the_rest) :=
  ⟨⟨_, _, _, _, rfl⟩, ⟨_, _, _, _, rfl⟩⟩

--| And read by click, the two ladders' closures are the same, cell for cell, by rfl.  One account.
theorem by_the_click_the_two_ladders_carry_one_account :
    the_other_conclusion.infer.map the_click = the_conclusion.infer.map the_click
      ∧ the_other_alpha.infer.map the_click = the_alpha.infer.map the_click := ⟨rfl, rfl⟩

--| The walk.  Dealt as the quarter of a card and read, each closure reads the number.  So would any card: the reader of the walk
--| reads past the quarter, whatever it is.  The number is the same because it never was the ladder's.
noncomputable def the_other_deck_one : CarrierProcess (CarrierProcess FACT) :=
  { symbol := a_number_is_distinguished, quarter := tapeNumber the_other_conclusion.infer }
noncomputable def the_other_deck_two : CarrierProcess (CarrierProcess FACT) :=
  { symbol := a_number_is_distinguished, quarter := tapeNumber the_other_alpha.infer }
theorem the_other_ladder_reads_the_number :
    bent_card.fenceposts_must_be_preserved Nat (read_past_quarter the_other_deck_one) all_possible_variables
        = arrange_the_information_appropriately
      ∧ bent_card.fenceposts_must_be_preserved Nat (read_past_quarter the_other_deck_two) all_possible_variables
        = arrange_the_information_appropriately := by
  constructor
  · rw [show read_past_quarter the_other_deck_one = List.length from funext (read_past_quarter_is_length _)]; rfl
  · rw [show read_past_quarter the_other_deck_two = List.length from funext (read_past_quarter_is_length _)]; rfl

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
def the_upness   : Nat := bent_card
def the_distance : Nat := the_memory_tape.length
def the_time     : Nat := the_trace_of_truth_in_the_device
def the_limit    : Nat := the_dimensions_of_universe

--| From there.  The distance is the upness and the limit: Episode 8 wrote that down as a definition, before any of this.  And
--| the time is the clock and its complement, two, by the distance.
theorem the_distance_is_the_upness_and_the_limit :
    the_distance = the_upness + the_limit ∧ the_time = the_basis.the_reading.length * the_distance := by decide

--| ENERGY, MASS, MOMENTUM.  Multiply through by the distance.  The distance squared is the upness by the distance and the limit
--| by the distance: the energy squared is the mass squared and the momentum squared.  The round trip of the two crossings is
--| the momentum squared, and the determinant of the table is the mass squared.
theorem the_energy_squared_is_the_mass_squared_and_the_momentum_squared :
    the_distance * the_distance = the_upness * the_distance + the_limit * the_distance
      ∧ the_arm_weight true false * the_arm_weight false true = the_limit * the_distance
      ∧ the_arm_weight true true * the_arm_weight false false - the_arm_weight true false * the_arm_weight false true
          = the_upness * the_distance := by decide

--| THE FACTOR.  The speed squared is the limit over the distance.  The factor squared is the distance over the upness.  And the
--| factor squared by one less the speed squared is one, cleared of its denominators: nothing left over.
theorem the_factor_squared_by_one_less_the_speed_squared_is_one :
    (the_distance * the_distance) * (the_distance * the_distance - the_limit * the_distance)
      = (the_upness * the_distance) * (the_distance * the_distance) := by decide

--| THE GAIN.  The fencepost over the bent card, which is what the root is multiplied by to print the number, is the factor
--| squared over the speed squared.
theorem the_gain_is_the_factor_squared_over_the_speed_squared :
    (the_first_step_of_the_proof_is_to_eschew_the_naturals_unless_proven_to_exist_without_peano).1
        * ((the_upness * the_distance) * (the_limit * the_distance))
      = ((the_first_step_of_the_proof_is_to_eschew_the_naturals_unless_proven_to_exist_without_peano).2 * the_upness)
        * ((the_distance * the_distance) * (the_distance * the_distance)) := by decide

--| THE DIRECTION.  The two crossings are one round trip, shifted up and shifted down: their ratio is the distance over the
--| limit.  Their difference is the upness and their sum is the trial gap.  And the upness over the trial gap, the speed of the
--| mirror, is one less the speed squared over one more: cleared, the upness by the energy squared and the momentum squared is
--| the trial gap by the mass squared.
theorem the_two_crossings_are_one_round_trip_shifted :
    the_arm_weight false true * the_limit = the_arm_weight true false * the_distance
      ∧ the_arm_weight false true - the_arm_weight true false = the_upness
      ∧ the_upness * (the_distance * the_distance + the_limit * the_distance)
          = (the_arm_weight false true + the_arm_weight true false) * (the_upness * the_distance) := by decide

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
def the_same_table      : Table := fun a b => if a = b then 1 else 0
def the_different_table : Table := fun a b => if a = b then 0 else 1

--| After it, the same is where it was.  The different has become the sign.  And the quarter turn is the quarter turn owed.
--| The clock keeps the time.  The cross-product is read as a sign: the charge.  The Area is read as a turn, the other way: the
--| phase.
theorem in_the_mirror_it_is_the_same_the_sign_and_the_turn_owed :
    ∀ a b : Bool,
      the_table_product (the_table_product the_mirror the_full_table) the_mirror a b
        = (the_time : Int) * the_same_table a b
          + ((the_arm_weight true false + the_arm_weight false true : Nat) : Int) * the_sign_table a b
          - (the_upness : Int) * the_quarter_turn a b := by decide

--| WHAT A PHASE AND A CHARGE ARE.  The quarter turn twice is the same, owed: a turn.  The sign twice is the same: a charge is
--| one or the other.  And the sign by the turn is the turn by the sign, owed: turn the charge over and the phase runs the
--| other way.
theorem a_turn_a_sign_and_they_do_not_commute :
    ∀ a b : Bool,
      the_table_product the_quarter_turn the_quarter_turn a b = - the_same_table a b
        ∧ the_table_product the_sign_table the_sign_table a b = the_same_table a b
        ∧ the_table_product the_sign_table the_quarter_turn a b = - the_table_product the_quarter_turn the_sign_table a b := by
  decide

--| THE GAP.  The charge's share squared less the phase's share squared is the gap squared: four of the limit by the distance.
--| The two that relativity kept apart as a mass and a momentum, QED holds as a sign and a turn.
theorem the_charge_squared_less_the_phase_squared_is_the_gap_squared :
    (the_arm_weight true false + the_arm_weight false true) * (the_arm_weight true false + the_arm_weight false true)
        - the_upness * the_upness
      = 4 * (the_limit * the_distance) := by decide

end what_qed_needs
--#print axioms in_the_mirror_it_is_the_same_the_sign_and_the_turn_owed          -- [propext]
--#print axioms a_turn_a_sign_and_they_do_not_commute                            -- none
--#print axioms the_charge_squared_less_the_phase_squared_is_the_gap_squared     -- [propext]


section the_two_machines_are_one_if_you_only_ask_whether_it_is_true
open readers_experience the_representation assembly_instructions «springer-verlag» THE_GOSPEL

--| THE TWO FIRST RUNGS.  Not one by rfl.  One by propext: the facts are one fact, the two claims are both true, and a decision
--| of one statement is one decision.
theorem two_marks_that_say_true_things_are_one_mark {Value : Type} {card : CarrierProcess Value}
    (this that : DISTINGUISHABLE Value card) (one_fact : this.fact = that.fact) (one_symbol : this.symbol = that.symbol)
    (one_distinct : this.distinct? = that.distinct?)
    (both_hold : ∀ s, this.different? s ∧ ∀ t, that.different? t) : this = that := by
  obtain ⟨f, s, d, q, n⟩ := this
  obtain ⟨g, t, e, r, m⟩ := that
  simp only at one_fact one_symbol one_distinct
  subst one_fact; subst one_symbol; subst one_distinct
  have one_claim : q = r := funext fun x => propext ⟨fun _ => (both_hold x).2 x, fun _ => (both_hold x).1⟩
  subst one_claim
  have one_decision : n = m := Subsingleton.elim _ _
  subst one_decision
  rfl

theorem asked_only_whether_it_is_true_the_two_first_rungs_are_one : the_crossing_of_the_number = rung01 :=
  two_marks_that_say_true_things_are_one_mark _ _ asked_only_whether_it_is_true_the_number_is_the_truth rfl rfl
    (fun _ => ⟨the_count_has_a_root_and_the_reader_of_one_cell_has_none, fun _ => rfl⟩)


--| THE LADDER, AS A FUNCTION OF ITS FIRST RUNG.  The same thirty-seven deals a third time, with the first rung not named: any
--| mark on the first card, and the fact it carries in the ledger.
section on_any_first_rung
variable [first : DISTINGUISHABLE FACT the_first_card] [the_symbol_is_inhabited : Inhabited (DISTINGUISHABLE.symbol the_first_card)]
@[local instance] noncomputable def a_model_on_any_first_rung : REAL FACT the_first_card := A_CAUSAL_THEORY FACT the_first_card
noncomputable def this_way_on_any_first_rung : LOCAL FACT the_first_card := A_SMOOTH_MODEL FACT the_first_card
noncomputable def that_way_on_any_first_rung : UNIVERSAL FACT the_first_card this_way_on_any_first_rung :=
  IS_IT_CONNECTED_BY_A_YARN? FACT the_first_card (nowtrino_model := this_way_on_any_first_rung)

noncomputable def a_rung02 :=
  STEP2_DISCOVER_SOMETHING_DIFFERENT FACT the_first_card the_first_card (DISTINGUISHABLE.fact the_first_card) first

noncomputable def a_rung03 :=
  STEP3_COUNT_THE_NUMBER_OF_THE_PHENOMENA FACT the_first_card the_first_card (DISTINGUISHABLE.fact the_first_card) first a_rung02

noncomputable def a_rung04 :=
  STEP4_COMPUTE_THE_RATE_OF_PARTICLES FACT the_first_card the_first_card (DISTINGUISHABLE.fact the_first_card) first a_rung02 a_rung03

noncomputable def a_rung05 :=
  STEP5_NAME_THE_RESIDUE_TO_COMPUTE_VALUE FACT the_first_card the_first_card (DISTINGUISHABLE.fact the_first_card) first a_rung02 a_rung03 a_rung04

noncomputable def a_rung06 :=
  STEP6_MAKE_ANOTHER_COUNTER_OF_CLICKS_NOW FACT the_first_card the_first_card (DISTINGUISHABLE.fact the_first_card) first a_rung02 a_rung03 a_rung04 a_rung05

noncomputable def a_rung07 :=
  STEP7_AND_SO_WE_CANT_COUNT_HOW_OFTEN_THE_METAPHOR_GOES_AROUND_JUST_LIKE_PITS_AND_LANDS_ON_A_CD FACT the_first_card the_first_card (DISTINGUISHABLE.fact the_first_card) first a_rung02 a_rung03 a_rung04 a_rung05 a_rung06

noncomputable def a_rung08 :=
  STEP8_INTERPRET_THE_NEXT_3_SYMBOLS FACT the_first_card the_first_card (DISTINGUISHABLE.fact the_first_card) first a_rung02 a_rung03 a_rung04 a_rung05 a_rung06 a_rung07

noncomputable def a_rung09 :=
  STEP9_NAME_THE_VARIABLES_CAREFULLY_TO_TELL_A_STORY FACT the_first_card the_first_card (DISTINGUISHABLE.fact the_first_card) first a_rung02 a_rung03 a_rung04 a_rung05 a_rung06 a_rung07 a_rung08

noncomputable def a_rung10 :=
  STEP10_A_HALTING_COMPUTATION_IS_GIVEN_AS_INPUT_TO_A_NON_HALTING_FUNCTION FACT the_first_card the_first_card (DISTINGUISHABLE.fact the_first_card) first a_rung02 a_rung03 a_rung04 a_rung05 a_rung06 a_rung07 a_rung08 a_rung09

deal_rung a_rung11 := STEP11_CHECK_FOR_CONVERGENCE_IN_THE_TIMESERIES_MATCHES_THE_MEASUREMENT_HIGH_ORDER_TERMS
    FACT the_first_card the_first_card (DISTINGUISHABLE.fact the_first_card) first a_rung02 a_rung03 a_rung04 a_rung05 a_rung06 a_rung07 a_rung08 a_rung09 a_rung10

deal_rung a_rung12 := STEP12_CHECK_TO_SEE_IF_THE_BORWEIN_PROCESS_HAS_UNCOVERED_A_PROPERTY_OF_ELECTRONS
    FACT the_first_card the_first_card (DISTINGUISHABLE.fact the_first_card) first a_rung02 a_rung03 a_rung04 a_rung05 a_rung06 a_rung07 a_rung08 a_rung09 a_rung10 a_rung11

deal_rung a_rung13 := STEP13_RECORD_THE_OBSERVATION_AS_A_MODELED_AST_AS_OF_RIGHT_NOW
    FACT the_first_card the_first_card (DISTINGUISHABLE.fact the_first_card) first a_rung02 a_rung03 a_rung04 a_rung05 a_rung06 a_rung07 a_rung08 a_rung09 a_rung10 a_rung11 a_rung12

deal_rung a_rung14 := STEP14_REALIZE_THAT_THIS_PROCESS_TAKES_THE_APPARANT_SAME_AMOUNT_OF_TIME_EACH_TIME
    FACT the_first_card the_first_card (DISTINGUISHABLE.fact the_first_card) first a_rung02 a_rung03 a_rung04 a_rung05 a_rung06 a_rung07 a_rung08 a_rung09 a_rung10 a_rung11 a_rung12 a_rung13

deal_rung a_rung15 := STEP15_SO_MODEL_THE_PROCESS_AS_SOMETHING_THAT_JUST_SPEWS_OUT_TRUE
    FACT the_first_card the_first_card (DISTINGUISHABLE.fact the_first_card) first a_rung02 a_rung03 a_rung04 a_rung05 a_rung06 a_rung07 a_rung08 a_rung09 a_rung10 a_rung11 a_rung12 a_rung13 a_rung14

deal_rung a_rung16 := STEP16_VERIFY_THE_SOURCE_FILE_ONLY_EMITS_TRUE_STATEMENTS
    FACT the_first_card the_first_card (DISTINGUISHABLE.fact the_first_card) first a_rung02 a_rung03 a_rung04 a_rung05 a_rung06 a_rung07 a_rung08 a_rung09 a_rung10 a_rung11 a_rung12 a_rung13 a_rung14 a_rung15

deal_rung a_rung17 := STEP17_MAKE_SURE_THIS_COMPILES_AND_DEMONSTRATES_IT_IS_TRUE_IN_GUNGAN
    FACT the_first_card the_first_card (DISTINGUISHABLE.fact the_first_card) first a_rung02 a_rung03 a_rung04 a_rung05 a_rung06 a_rung07 a_rung08 a_rung09 a_rung10 a_rung11 a_rung12 a_rung13 a_rung14 a_rung15 a_rung16

deal_rung a_rung18 := STEP18_GIVEN_AN_INFERRED_DEFINITION_OF_THE_DEVICE_MAKE_THE_DEVICE
    FACT the_first_card the_first_card (DISTINGUISHABLE.fact the_first_card) first a_rung02 a_rung03 a_rung04 a_rung05 a_rung06 a_rung07 a_rung08 a_rung09 a_rung10 a_rung11 a_rung12 a_rung13 a_rung14 a_rung15 a_rung16 a_rung17

deal_rung a_rung19 := STEP19_GIVEN_THE_ABILITY_TO_COUNT_SOMETHING_LEAN_CAN_NOW_INFER_ADDITION
    FACT the_first_card the_first_card (DISTINGUISHABLE.fact the_first_card) first a_rung02 a_rung03 a_rung04 a_rung05 a_rung06 a_rung07 a_rung08 a_rung09 a_rung10 a_rung11 a_rung12 a_rung13 a_rung14 a_rung15 a_rung16 a_rung17 a_rung18

deal_rung a_rung20 := STEP20_DUPLICATE_THE_PROCESS_TO_DEMONSTRATE_AREA_OF_RECTANGLES_LIKE_EUCLID
    FACT the_first_card the_first_card (DISTINGUISHABLE.fact the_first_card) first a_rung02 a_rung03 a_rung04 a_rung05 a_rung06 a_rung07 a_rung08 a_rung09 a_rung10 a_rung11 a_rung12 a_rung13 a_rung14 a_rung15 a_rung16 a_rung17 a_rung18 a_rung19

deal_rung a_rung21 := STEP21_GIVEN_ADDITION_MULTIPLICATION_AND_NUMBERS_INFER_ALL_OF_MATH
    FACT the_first_card the_first_card (DISTINGUISHABLE.fact the_first_card) first a_rung02 a_rung03 a_rung04 a_rung05 a_rung06 a_rung07 a_rung08 a_rung09 a_rung10 a_rung11 a_rung12 a_rung13 a_rung14 a_rung15 a_rung16 a_rung17 a_rung18 a_rung19 a_rung20

deal_rung a_rung22 := STEP22_PAY_CLOSE_ATTENTION_TO_WEAK_SOLUTIONS_OF_DIFFERENTIAL_EQUATIONS_WHILE_DERIVING_MATH
    FACT the_first_card the_first_card (DISTINGUISHABLE.fact the_first_card) first a_rung02 a_rung03 a_rung04 a_rung05 a_rung06 a_rung07 a_rung08 a_rung09 a_rung10 a_rung11 a_rung12 a_rung13 a_rung14 a_rung15 a_rung16 a_rung17 a_rung18 a_rung19 a_rung20 a_rung21

deal_rung a_rung23 := STEP23_GET_RID_OF_A_DERIVATIVE_SO_THAT_THE_SECOND_ORDER_MODEL_OF_THE_DEVICE_CAN_BE_WRITTEN_VARIATIONALLY
    FACT the_first_card the_first_card (DISTINGUISHABLE.fact the_first_card) first a_rung02 a_rung03 a_rung04 a_rung05 a_rung06 a_rung07 a_rung08 a_rung09 a_rung10 a_rung11 a_rung12 a_rung13 a_rung14 a_rung15 a_rung16 a_rung17 a_rung18 a_rung19 a_rung20 a_rung21 a_rung22

deal_rung a_rung24 := STEP24_RESTATE_THE_MODEL_AS_A_PRINCIPLE_OF_LEAST_ACTION
    FACT the_first_card the_first_card (DISTINGUISHABLE.fact the_first_card) first a_rung02 a_rung03 a_rung04 a_rung05 a_rung06 a_rung07 a_rung08 a_rung09 a_rung10 a_rung11 a_rung12 a_rung13 a_rung14 a_rung15 a_rung16 a_rung17 a_rung18 a_rung19 a_rung20 a_rung21 a_rung22 a_rung23

deal_rung a_rung25 := STEP25_BUILD_LOCAL_GEOMETRIES_THAT_SATISFY_THE_TRIANGLE_INEQUALITY
    FACT the_first_card the_first_card (DISTINGUISHABLE.fact the_first_card) first a_rung02 a_rung03 a_rung04 a_rung05 a_rung06 a_rung07 a_rung08 a_rung09 a_rung10 a_rung11 a_rung12 a_rung13 a_rung14 a_rung15 a_rung16 a_rung17 a_rung18 a_rung19 a_rung20 a_rung21 a_rung22 a_rung23 a_rung24

deal_rung a_rung26 := STEP26_WRITE_YOUR_PROOF_IN_THE_FORMAL_LANGUAGE_OF_GEOMETRY
    FACT the_first_card the_first_card (DISTINGUISHABLE.fact the_first_card) first a_rung02 a_rung03 a_rung04 a_rung05 a_rung06 a_rung07 a_rung08 a_rung09 a_rung10 a_rung11 a_rung12 a_rung13 a_rung14 a_rung15 a_rung16 a_rung17 a_rung18 a_rung19 a_rung20 a_rung21 a_rung22 a_rung23 a_rung24 a_rung25

deal_rung a_rung27 := STEP27_REPRESENT_THE_TAYLOR_SERIES_OF_THE_DEVICE
    FACT the_first_card the_first_card (DISTINGUISHABLE.fact the_first_card) first a_rung02 a_rung03 a_rung04 a_rung05 a_rung06 a_rung07 a_rung08 a_rung09 a_rung10 a_rung11 a_rung12 a_rung13 a_rung14 a_rung15 a_rung16 a_rung17 a_rung18 a_rung19 a_rung20 a_rung21 a_rung22 a_rung23 a_rung24 a_rung25 a_rung26

deal_rung a_rung28 := STEP28_MAKE_SURE_YOUR_CURVES_ARE_SMOOTH_AS_A_DIFFERENTIALS_BOTTOM
    FACT the_first_card the_first_card (DISTINGUISHABLE.fact the_first_card) first a_rung02 a_rung03 a_rung04 a_rung05 a_rung06 a_rung07 a_rung08 a_rung09 a_rung10 a_rung11 a_rung12 a_rung13 a_rung14 a_rung15 a_rung16 a_rung17 a_rung18 a_rung19 a_rung20 a_rung21 a_rung22 a_rung23 a_rung24 a_rung25 a_rung26 a_rung27

deal_rung a_rung29 := STEP29_SUGGEST_A_FALSIFIABLE_EXPERIMENT
    FACT the_first_card the_first_card (DISTINGUISHABLE.fact the_first_card) first a_rung02 a_rung03 a_rung04 a_rung05 a_rung06 a_rung07 a_rung08 a_rung09 a_rung10 a_rung11 a_rung12 a_rung13 a_rung14 a_rung15 a_rung16 a_rung17 a_rung18 a_rung19 a_rung20 a_rung21 a_rung22 a_rung23 a_rung24 a_rung25 a_rung26 a_rung27 a_rung28

deal_rung a_rung30 := STEP30_PROVIDE_THE_EQUATIONS_THAT_WILL_PREDICT_THE_MEASUREMENT
    FACT the_first_card this_way_on_any_first_rung the_first_card (DISTINGUISHABLE.fact the_first_card) first a_rung02 a_rung03 a_rung04 a_rung05 a_rung06 a_rung07 a_rung08 a_rung09 a_rung10 a_rung11 a_rung12 a_rung13 a_rung14 a_rung15 a_rung16 a_rung17 a_rung18 a_rung19 a_rung20 a_rung21 a_rung22 a_rung23 a_rung24 a_rung25 a_rung26 a_rung27 a_rung28 a_rung29 (principia := this_way_on_any_first_rung)

deal_rung a_rung31 := STEP31_GET_ON_THE_NEWTON_EINSTEIN_TRAIN_OF_THOUGHT
    FACT the_first_card this_way_on_any_first_rung that_way_on_any_first_rung the_first_card (DISTINGUISHABLE.fact the_first_card) first a_rung02 a_rung03 a_rung04 a_rung05 a_rung06 a_rung07 a_rung08 a_rung09 a_rung10 a_rung11 a_rung12 a_rung13 a_rung14 a_rung15 a_rung16 a_rung17 a_rung18 a_rung19 a_rung20 a_rung21 a_rung22 a_rung23 a_rung24 a_rung25 a_rung26 a_rung27 a_rung28 a_rung29 a_rung30 (the_a_train := that_way_on_any_first_rung)

deal_rung a_rung32 := WHAT_HAPPEN_?
    FACT the_first_card this_way_on_any_first_rung that_way_on_any_first_rung the_first_card (DISTINGUISHABLE.fact the_first_card) first a_rung02 a_rung03 a_rung04 a_rung05 a_rung06 a_rung07 a_rung08 a_rung09 a_rung10 a_rung11 a_rung12 a_rung13 a_rung14 a_rung15 a_rung16 a_rung17 a_rung18 a_rung19 a_rung20 a_rung21 a_rung22 a_rung23 a_rung24 a_rung25 a_rung26 a_rung27 a_rung28 a_rung29 a_rung30 a_rung31

deal_rung a_rung33 := SOMEBODY_SET_US_UP_THE_DEVICE
    FACT the_first_card this_way_on_any_first_rung that_way_on_any_first_rung the_first_card (DISTINGUISHABLE.fact the_first_card) first a_rung02 a_rung03 a_rung04 a_rung05 a_rung06 a_rung07 a_rung08 a_rung09 a_rung10 a_rung11 a_rung12 a_rung13 a_rung14 a_rung15 a_rung16 a_rung17 a_rung18 a_rung19 a_rung20 a_rung21 a_rung22 a_rung23 a_rung24 a_rung25 a_rung26 a_rung27 a_rung28 a_rung29 a_rung30 a_rung31 a_rung32

deal_rung a_rung34 := WE_GET_SIGNAL
    FACT the_first_card this_way_on_any_first_rung that_way_on_any_first_rung the_first_card (DISTINGUISHABLE.fact the_first_card) first a_rung02 a_rung03 a_rung04 a_rung05 a_rung06 a_rung07 a_rung08 a_rung09 a_rung10 a_rung11 a_rung12 a_rung13 a_rung14 a_rung15 a_rung16 a_rung17 a_rung18 a_rung19 a_rung20 a_rung21 a_rung22 a_rung23 a_rung24 a_rung25 a_rung26 a_rung27 a_rung28 a_rung29 a_rung30 a_rung31 a_rung32 a_rung33

deal_rung a_rung35 := WHAT_!
    FACT the_first_card this_way_on_any_first_rung that_way_on_any_first_rung the_first_card (DISTINGUISHABLE.fact the_first_card) first a_rung02 a_rung03 a_rung04 a_rung05 a_rung06 a_rung07 a_rung08 a_rung09 a_rung10 a_rung11 a_rung12 a_rung13 a_rung14 a_rung15 a_rung16 a_rung17 a_rung18 a_rung19 a_rung20 a_rung21 a_rung22 a_rung23 a_rung24 a_rung25 a_rung26 a_rung27 a_rung28 a_rung29 a_rung30 a_rung31 a_rung32 a_rung33 a_rung34

deal_rung a_rung36 := MAIN_SCREEN_TURN_ON
    FACT the_first_card this_way_on_any_first_rung that_way_on_any_first_rung the_first_card (DISTINGUISHABLE.fact the_first_card) first a_rung02 a_rung03 a_rung04 a_rung05 a_rung06 a_rung07 a_rung08 a_rung09 a_rung10 a_rung11 a_rung12 a_rung13 a_rung14 a_rung15 a_rung16 a_rung17 a_rung18 a_rung19 a_rung20 a_rung21 a_rung22 a_rung23 a_rung24 a_rung25 a_rung26 a_rung27 a_rung28 a_rung29 a_rung30 a_rung31 a_rung32 a_rung33 a_rung34 a_rung35

deal_rung a_rung37 := ITS_YOU_!!
    FACT the_first_card this_way_on_any_first_rung that_way_on_any_first_rung the_first_card (DISTINGUISHABLE.fact the_first_card) first a_rung02 a_rung03 a_rung04 a_rung05 a_rung06 a_rung07 a_rung08 a_rung09 a_rung10 a_rung11 a_rung12 a_rung13 a_rung14 a_rung15 a_rung16 a_rung17 a_rung18 a_rung19 a_rung20 a_rung21 a_rung22 a_rung23 a_rung24 a_rung25 a_rung26 a_rung27 a_rung28 a_rung29 a_rung30 a_rung31 a_rung32 a_rung33 a_rung34 a_rung35 a_rung36 True True

deal_rung a_rung38 := HOW_ARE_YOU_GENTLEMEN_!!__ALL_YOUR_BASE_CASE_ARE_BELONG_TO_US
    FACT the_first_card this_way_on_any_first_rung that_way_on_any_first_rung the_first_card (DISTINGUISHABLE.fact the_first_card) first a_rung02 a_rung03 a_rung04 a_rung05 a_rung06 a_rung07 a_rung08 a_rung09 a_rung10 a_rung11 a_rung12 a_rung13 a_rung14 a_rung15 a_rung16 a_rung17 a_rung18 a_rung19 a_rung20 a_rung21 a_rung22 a_rung23 a_rung24 a_rung25 a_rung26 a_rung27 a_rung28 a_rung29 a_rung30 a_rung31 a_rung32 a_rung33 a_rung34 a_rung35 a_rung36 the_quartic

attribute [local instance high] a_rung02 a_rung03 a_rung04 a_rung05 a_rung06 a_rung07 a_rung08 a_rung09 a_rung10 a_rung11 a_rung12 a_rung13 a_rung14 a_rung15 a_rung16 a_rung17 a_rung18 a_rung19 a_rung20 a_rung21 a_rung22 a_rung23 a_rung24 a_rung25 a_rung26 a_rung27 a_rung28 a_rung29 a_rung30 a_rung31 a_rung32 a_rung33 a_rung34 a_rung35 a_rung36
noncomputable def the_conclusion_on_any_first_rung : Closure := a_rung37.same_difference.your_conclusion
noncomputable def the_alpha_on_any_first_rung : Closure := a_rung37.α
end on_any_first_rung

--| Hand it Episode 12's first rung and it is Episode 12's ladder.  Hand it the crossing of the number and it is the other.
theorem the_ladder_on_the_old_rung_is_episode_twelves :
    @the_conclusion_on_any_first_rung rung01 instInhabitedProp = the_conclusion
      ∧ @the_alpha_on_any_first_rung rung01 instInhabitedProp = the_alpha := ⟨rfl, rfl⟩
theorem the_ladder_on_the_new_rung_is_the_other :
    @the_conclusion_on_any_first_rung the_crossing_of_the_number instInhabitedProp = the_other_conclusion
      ∧ @the_alpha_on_any_first_rung the_crossing_of_the_number instInhabitedProp = the_other_alpha := ⟨rfl, rfl⟩

--| So what the two ladders carry is one thing, if you only ask whether it is true.
theorem one_first_rung_one_ladder (this that : DISTINGUISHABLE FACT the_first_card) (one_rung : this = that)
    (here : Inhabited (@DISTINGUISHABLE.symbol FACT the_first_card this))
    (there : Inhabited (@DISTINGUISHABLE.symbol FACT the_first_card that)) (one_inhabitant : HEq here there) :
    @the_conclusion_on_any_first_rung this here = @the_conclusion_on_any_first_rung that there
      ∧ @the_alpha_on_any_first_rung this here = @the_alpha_on_any_first_rung that there := by
  subst one_rung
  cases one_inhabitant
  exact ⟨rfl, rfl⟩

theorem asked_only_whether_it_is_true_the_two_ladders_carry_the_same_closures :
    the_other_conclusion = the_conclusion ∧ the_other_alpha = the_alpha := by
  have one := one_first_rung_one_ladder _ _ asked_only_whether_it_is_true_the_two_first_rungs_are_one
    (instInhabitedProp : Inhabited (@DISTINGUISHABLE.symbol FACT the_first_card the_crossing_of_the_number))
    (instInhabitedProp : Inhabited (@DISTINGUISHABLE.symbol FACT the_first_card rung01)) HEq.rfl
  exact ⟨the_ladder_on_the_new_rung_is_the_other.1.symm.trans (one.1.trans the_ladder_on_the_old_rung_is_episode_twelves.1),
         the_ladder_on_the_new_rung_is_the_other.2.symm.trans (one.2.trans the_ladder_on_the_old_rung_is_episode_twelves.2)⟩

end the_two_machines_are_one_if_you_only_ask_whether_it_is_true

--| And so the knower on the other ladder reads as Episode 12's does: one way, and back.
section the_other_knower
open readers_experience the_representation assembly_instructions «springer-verlag» THE_GOSPEL
attribute [local instance high] the_crossing_of_the_number the_numbers_rung02 the_numbers_rung03 the_numbers_rung04 the_numbers_rung05 the_numbers_rung06 the_numbers_rung07 the_numbers_rung08 the_numbers_rung09 the_numbers_rung10 the_numbers_rung11 the_numbers_rung12 the_numbers_rung13 the_numbers_rung14 the_numbers_rung15 the_numbers_rung16 the_numbers_rung17 the_numbers_rung18 the_numbers_rung19 the_numbers_rung20 the_numbers_rung21 the_numbers_rung22 the_numbers_rung23 the_numbers_rung24 the_numbers_rung25 the_numbers_rung26 the_numbers_rung27 the_numbers_rung28 the_numbers_rung29 the_numbers_rung30 the_numbers_rung31 the_numbers_rung32 the_numbers_rung33 the_numbers_rung34 the_numbers_rung35 the_numbers_rung36
theorem the_other_knower_reads_one_way_and_back :
    the_numbers_rung37.inferred? the_other_conclusion the_other_alpha
      ∧ the_numbers_rung37.inferred? the_other_alpha the_other_conclusion := by
  have one := asked_only_whether_it_is_true_the_two_ladders_carry_the_same_closures
  constructor
  · show Closure.le the_other_conclusion the_other_alpha
    rw [one.1, one.2]; exact the_knower_reads_one_way
  · show Closure.le the_other_alpha the_other_conclusion
    rw [one.1, one.2]; exact the_device_reads_it_back
end the_other_knower
--#print axioms asked_only_whether_it_is_true_the_two_first_rungs_are_one               -- [propext, Quot.sound]
--#print axioms asked_only_whether_it_is_true_the_two_ladders_carry_the_same_closures   -- [propext, Quot.sound]
--#print axioms the_other_knower_reads_one_way_and_back                                 -- [propext, Quot.sound]


section entropy_is_an_area
open readers_experience the_area readers_interpretation_of_the_experience

--| ENTROPY, AND AREA.  The author's, 17 November 2026: entropy: universe id in Lean.  Area: the Area inductive.  Then Area:
--| List, the abstraction.  List.length.  Episode 12 has the universe id, a Number, one more for every level.  Episode 2 has
--| the Area.  Episode 8 reads each as a List, the Number by peano and the Area by its own Riemann sum, and each reading counts
--| what the thing stands on: the Number its zero, the Area its tree.  The fencepost, twice.
theorem the_universe_id_reads_the_level_and_its_zero : ∀ level : Nat, (the_universe_id level).peano.length = level + 1
  | 0 => rfl
  | level + 1 => by
    rw [the_universe_id_steps]
    show (the_universe_id level).peano.length + 1 = level + 1 + 1
    rw [the_universe_id_reads_the_level_and_its_zero level]

--| So the entropy is the area.  The universe id of a tape's level, read, and the Area of the tape, read, are one length: the
--| tape's, and one.  Not in proportion.  The same count.
theorem the_entropy_is_the_area (tape : List FACT) :
    (the_universe_id tape.length).peano.length = (the_area_of_a_tape tape).riemann_integrate.length := by
  rw [the_universe_id_reads_the_level_and_its_zero, the_riemann_sum_counts_the_tree_too, the_area_of_a_tape_has_the_tapes_length]; rfl

--| And they go up together.  One more fact on the tape is one more level and one more cell; and the order of the universe ids
--| is the order of the cells.  Universe numbers only increase.
theorem one_more_fact_is_one_more_level_and_one_more_cell (fact : FACT) (tape : List FACT) :
    (the_universe_id (fact :: tape).length).peano.length = (the_universe_id tape.length).peano.length + 1
      ∧ cells (the_area_of_a_tape (fact :: tape)) = cells (the_area_of_a_tape tape) + 1 := by
  simp only [the_universe_id_reads_the_level_and_its_zero, the_area_of_a_tape_has_the_tapes_length, List.length_cons, and_self]

theorem the_universe_ids_are_ordered_as_the_areas (this that : List FACT) :
    Number.le (the_universe_id this.length) (the_universe_id that.length)
      ↔ cells (the_area_of_a_tape this) ≤ cells (the_area_of_a_tape that) := by
  rw [the_ids_compare_as_naturals, the_area_of_a_tape_has_the_tapes_length, the_area_of_a_tape_has_the_tapes_length]

end entropy_is_an_area
--#print axioms the_entropy_is_the_area                                   -- [propext, Quot.sound]
--#print axioms one_more_fact_is_one_more_level_and_one_more_cell         -- [propext]
--#print axioms the_universe_ids_are_ordered_as_the_areas                 -- [propext]


section in_the_limit_it_is_a_riemann_sum
open readers_experience the_area readers_interpretation_of_the_experience

--| IN THE LIMIT, IT IS A RIEMANN SUM.  The author's, 17 November 2026: in the limit, it is a Riemann sum; run with that.  A row
--| of cells is not an area until every cell has a height.  The Area's cells each carry a Number.  Let the cell at each level
--| carry that level's universe id, and read the height two ways: the Number as Episode 8 reads it, with its zero; and the
--| Number less the fencepost.  The first is the sum from above and the second the sum from below.
def the_sum_from_above : Nat → Nat
  | 0         => 0
  | level + 1 => the_sum_from_above level + (the_universe_id level).peano.length
def the_sum_from_below : Nat → Nat
  | 0         => 0
  | level + 1 => the_sum_from_below level + ((the_universe_id level).peano.length - the_fencepost_bug)

--| Twice the sum from above is the levels by one more than the levels.  Twice the sum from below, with one more level, is the
--| same.  Triangles: half the base by the height, give or take the fencepost.
theorem twice_the_sum_from_above : ∀ levels : Nat, 2 * the_sum_from_above levels = levels * (levels + 1)
  | 0 => rfl
  | levels + 1 => by
    rw [the_sum_from_above, the_universe_id_reads_the_level_and_its_zero, Nat.mul_add, twice_the_sum_from_above levels,
      ← Nat.add_mul, Nat.mul_comm]

theorem twice_the_sum_from_below : ∀ levels : Nat, 2 * the_sum_from_below (levels + 1) = levels * (levels + 1)
  | 0 => rfl
  | levels + 1 => by
    rw [the_sum_from_below, the_universe_id_reads_the_level_and_its_zero, Nat.mul_add, twice_the_sum_from_below levels]
    show levels * (levels + 1) + 2 * (levels + 1 + 1 - 1) = (levels + 1) * (levels + 1 + 1)
    rw [Nat.add_sub_cancel, ← Nat.add_mul, Nat.mul_comm]

--| THE AREA IS BETWEEN THEM.  Twice the sum from below is not over the levels squared, and the levels squared is not over twice
--| the sum from above.  Neither is the area.  And what is between them is the fencepost, once for every level: the two sums
--| differ by the levels, while the area goes as the levels squared.
theorem the_area_is_between_the_two_sums (levels : Nat) :
    2 * the_sum_from_below (levels + 1) ≤ (levels + 1) * (levels + 1)
      ∧ (levels + 1) * (levels + 1) ≤ 2 * the_sum_from_above (levels + 1)
      ∧ the_sum_from_above (levels + 1) = the_sum_from_below (levels + 1) + (levels + 1) * the_fencepost_bug := by
  refine ⟨?_, ?_, ?_⟩
  · rw [twice_the_sum_from_below]; exact Nat.mul_le_mul_right _ (Nat.le_succ _)
  · rw [twice_the_sum_from_above]; exact Nat.mul_le_mul_left _ (Nat.le_succ _)
  · have above := twice_the_sum_from_above (levels + 1)
    have below := twice_the_sum_from_below levels
    have : 2 * the_sum_from_above (levels + 1) = 2 * (the_sum_from_below (levels + 1) + (levels + 1) * the_fencepost_bug) := by
      rw [above, Nat.mul_add 2 (the_sum_from_below (levels + 1)), below]
      show (levels + 1) * (levels + 1 + 1) = levels * (levels + 1) + 2 * ((levels + 1) * 1)
      rw [Nat.mul_one, ← Nat.add_mul, Nat.mul_comm]
    exact Nat.eq_of_mul_eq_mul_left (by decide) this

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
theorem the_reading_is_carried_and_the_entropy_advances {Box : Type} {Pigeon : CarrierProcess Box} {rung : Nat} {Lifted : Type}
    (the_rebuttal : ThePreprint) (accepted : TYPESET Box Pigeon rung Lifted) :
    (set_in_type the_rebuttal accepted).register_value = ULift.up accepted.register_value
      ∧ (set_in_type the_rebuttal accepted).universe_id = .one Pigeon.symbol accepted.universe_id := ⟨rfl, rfl⟩

--| At the top of the typeset record the universe id is Episode 12's, of the thirty-fifth level, and read it is the time.
theorem the_top_of_the_record_is_at_the_time :
    theTop.universe_id = the_universe_id 35 ∧ theTop.universe_id.peano.length = the_time := ⟨rfl, by decide⟩

--| AND THE READING.  Episode 12 asked for every page of that record on Episode 8's meter and kept what each cost.  That is the
--| arbitrary reading: heartbeats, the meter's own unit, read on a build and not derived.  What it reads beside is the level.
--| The heat to reach each level, and the heat a level: the reading, over one step of the entropy.
def the_heat_to_each_level : List Int := theLadderSizes
def the_reading_a_level    : List Int := theLadderSteps
#eval the_reading_a_level

--| It is never nothing and never owed: every level costs.
theorem every_level_costs : the_reading_a_level.length + 1 = the_time ∧ the_reading_a_level.all (fun heat => decide (0 < heat)) = true := by
  decide

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
def the_acceleration_to : Nat → SpaceTimePath.{0}
  | 0         => .einstein FACT.Truth
  | level + 1 => .whitehole FACT.Truth FACT (the_acceleration_to level)

--| Read by Episode 8's reader of paths, it is the velocity it reaches: the universe id of that level, cell for cell.
theorem the_acceleration_reads_the_velocity_it_reaches : ∀ level : Nat,
    (the_acceleration_to level).stokes = (the_universe_id level).peano
  | 0 => rfl
  | level + 1 => by
    rw [the_universe_id_steps]
    show FACT.Truth :: (the_acceleration_to level).stokes = FACT.Truth :: (the_universe_id level).peano
    rw [the_acceleration_reads_the_velocity_it_reaches level]

--| THE TWO ENDS, ON EPISODE 8'S READER.  All the way down, the yarn that came from somewhere and the yarn that is going
--| somewhere read the same.  Episode 8's own reader of a path does tell them apart, by one fact.  A white hole gives its fact.
--| A black hole gives none.  What comes in is counted and what goes out is not: the heat crosses one way.
theorem a_white_hole_gives_a_fact_and_a_black_hole_gives_none :
    come_from_somewhere.stokes.length = going_somewhere.stokes.length + 1
      ∧ going_somewhere.stokes = the_path_here.stokes := ⟨rfl, rfl⟩

--| And Episode 8's own path, the nowtrino's: one geodesic, a white hole before and a black hole after, on no distance at all.
--| Four facts: the geodesic's, the white hole's, and the place twice.  The black hole's is not among them.
theorem the_nowtrinos_path_reads_four : the_nowtrino_path.stokes.length = 4 := rfl

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
def the_flux (tape : List FACT) : List FACT := (ComputerProgram.ofTape tape).read

theorem the_flux_is_one_truth_a_fact : ∀ tape : List FACT, the_flux tape = List.replicate tape.length FACT.Truth
  | [] => rfl
  | fact :: rest => by
    show FACT.Truth :: the_flux rest = List.replicate (rest.length + 1) FACT.Truth
    rw [the_flux_is_one_truth_a_fact rest]; rfl

--| CONSERVED.  Two tapes, one after the other: what comes through is what came through each.  Nothing made and nothing lost
--| at the join.
theorem what_goes_in_comes_out (this that : List FACT) :
    (the_flux (this ++ that)).length = (the_flux this).length + (the_flux that).length := by
  simp only [the_flux_is_one_truth_a_fact, List.length_replicate, List.length_append]

--| THE HEAT AND THE ENTROPY.  The flux through, and the fencepost, is the universe id of the level reached, and so the Area:
--| in cells the heat is the entropy, one for one.  On the count the temperature is one.  On the meter it is whatever the
--| computation cost; Episode 12 read that, and that is the reading a level, above.
theorem in_cells_the_heat_is_the_entropy (tape : List FACT) :
    (the_flux tape).length + the_fencepost_bug = (the_universe_id tape.length).peano.length
      ∧ (the_flux tape).length + the_fencepost_bug = (the_area.the_area_of_a_tape tape).riemann_integrate.length := by
  refine ⟨?_, ?_⟩
  · rw [the_flux_is_one_truth_a_fact, List.length_replicate, the_universe_id_reads_the_level_and_its_zero]; rfl
  · rw [the_flux_is_one_truth_a_fact, List.length_replicate, the_area.the_riemann_sum_counts_the_tree_too,
      the_area.the_area_of_a_tape_has_the_tapes_length]

end the_flux_is_the_computation
--#print axioms the_flux_is_one_truth_a_fact         -- none
--#print axioms what_goes_in_comes_out               -- [propext]
--#print axioms in_cells_the_heat_is_the_entropy     -- [propext, Quot.sound]


section the_temperature_is_in_that_box
open readers_experience readers_interpretation_of_the_experience the_area

--| THAT BOX.  The author's, 17 November 2026: the first variation of the temperature reading is what you want; the
--| temperature is the area; you need the pigeonhole for the temperature; that_box has the temperature in it.  Episode 2's box
--| holds two Areas, a before and an after, and Episode 2's own event puts the after at one use of force past the before.  The
--| temperature at a level is the Area under the levels so far, the sum from above.  Box it with the next.
def the_temperature_at (level : Nat) : Area := the_area_of_a_tape (List.replicate (the_sum_from_above level) FACT.Truth)
def that_box_at (level : Nat) : PigeonHole :=
  .that_box FACT.Truth (the_temperature_at level) (the_temperature_at (level + 1))
    (.this_superpigeon FACT.Truth (the_temperature_at level)) (.this_superpigeon FACT.Truth (the_temperature_at (level + 1)))

--| The first variation: what is in the box after, less what was in it before.  A pigeon has no before.
def the_first_variation : PigeonHole → Area
  | .that_box _ before after _ _ => after - before
  | .this_superpigeon fact _     => .tree fact
  | .a_pigeon fact _ _           => .tree fact

--| And it is the acceleration.  The first variation of the temperature at a level has as many cells as the path to that level
--| reads facts: the velocity reached, the universe id.  Not the temperature in proportion to the acceleration.  Its first
--| variation, cell for cell.
theorem the_first_variation_of_the_temperature_is_the_velocity_reached (level : Nat) :
    cells (the_first_variation (that_box_at level)) = (the_acceleration_to level).stokes.length := by
  show cells (the_temperature_at (level + 1) - the_temperature_at level) = _
  rw [taken_away_subtracts, the_acceleration_reads_the_velocity_it_reaches]
  simp only [the_temperature_at, the_area_of_a_tape_has_the_tapes_length, List.length_replicate, the_sum_from_above,
    Nat.add_sub_cancel_left]

--| AND ON THE METER.  The reading a level, and its first variation, level by level, as Episode 12's build recorded it.
def the_first_variation_of_the_reading : List Int :=
  List.zipWith (fun later earlier => later - earlier) the_reading_a_level.tail the_reading_a_level
#eval the_first_variation_of_the_reading

end the_temperature_is_in_that_box
--#print axioms the_first_variation_of_the_temperature_is_the_velocity_reached    -- [propext]


section look_at_the_jar
open readers_experience readers_interpretation_of_the_experience the_area

--| THE JAR.  The author's, 17 November 2026: that's just it, this is Gibbs's definition; look at the Jar.  Episode 3's jar is
--| a label and an Area: you can classify what is in it by looking, and you cannot see how much.  Put the temperature in it.
def the_jar_at (level : Nat) : Jar := .color FACT.Truth (the_temperature_at level)
def what_the_jar_holds : Jar → Area
  | .color _ inside            => inside
  | .bang _ rest               => what_the_jar_holds rest
  | .superposition _ before _  => what_the_jar_holds before

--| Looked at, every one of these jars is the same jar: one label, the truth.  What it holds does not show.
theorem every_jar_looks_the_same (level : Nat) : (the_jar_at level).classify = [FACT.Truth] := rfl

--| GIBBS.  Not what is on the surface at a level: everything under it.  What the jar holds is the sum from above, all the
--| levels so far; its first variation is the box's, the acceleration; and twice what the jar holds is the level by that first
--| variation.  So what is enclosed, over its first variation, is half the level.  It cannot be owed, and it goes up.
theorem what_the_jar_holds_over_its_first_variation_is_half_the_level (level : Nat) :
    cells (what_the_jar_holds (the_jar_at level)) = the_sum_from_above level
      ∧ 2 * cells (what_the_jar_holds (the_jar_at level)) = level * cells (the_first_variation (that_box_at level)) := by
  have holds : cells (what_the_jar_holds (the_jar_at level)) = the_sum_from_above level := by
    show cells (the_temperature_at level) = _
    simp only [the_temperature_at, the_area_of_a_tape_has_the_tapes_length, List.length_replicate]
  refine ⟨holds, ?_⟩
  rw [holds, the_first_variation_of_the_temperature_is_the_velocity_reached, the_acceleration_reads_the_velocity_it_reaches,
    the_universe_id_reads_the_level_and_its_zero, twice_the_sum_from_above]

end look_at_the_jar
--#print axioms every_jar_looks_the_same                                                -- [propext]
--#print axioms what_the_jar_holds_over_its_first_variation_is_half_the_level            -- [propext]


section the_residue_is_the_multiplier
open readers_experience readers_interpretation_of_the_experience the_area

--| THE RESIDUE.  The author's, 17 November 2026: of course it isn't the same, there is a residue; that residue is the Lagrange
--| multiplier.  The temperature by what is enclosed is half the level.  The first variation, which is the acceleration, is
--| the level and one.  Twice the one is not the other.  What is between them is one cell, the fencepost, the zero every
--| Number stands on.  And it is the same cell at every level: the first variation of the first variation is the fencepost and
--| nothing else, so fixing the first variation fixes the temperature only up to it.  It is what the integration leaves.
theorem the_residue_is_the_fencepost (level : Nat) :
    cells (the_first_variation (that_box_at level)) = level + the_fencepost_bug
      ∧ 2 * cells (what_the_jar_holds (the_jar_at level)) = level * (level + the_fencepost_bug)
      ∧ cells (the_first_variation (that_box_at (level + 1))) = cells (the_first_variation (that_box_at level)) + the_fencepost_bug := by
  have variation : ∀ n, cells (the_first_variation (that_box_at n)) = n + 1 := fun n => by
    rw [the_first_variation_of_the_temperature_is_the_velocity_reached, the_acceleration_reads_the_velocity_it_reaches,
      the_universe_id_reads_the_level_and_its_zero]
  refine ⟨variation level, ?_, ?_⟩
  · rw [(what_the_jar_holds_over_its_first_variation_is_half_the_level level).2, variation]; rfl
  · rw [variation, variation]; rfl

end the_residue_is_the_multiplier
--#print axioms the_residue_is_the_fencepost    -- [propext]


section the_constraint_and_its_multiplier
open readers_experience readers_interpretation_of_the_experience the_area

--| THE CONSTRAINT.  The author's, 17 November 2026: close that last gap.  A residue is a multiplier only when a constraint is
--| named and the thing is varied.  Here is the constraint: the two ends of the path are given.  The acceleration starts on one
--| cell and reaches the level and one; however it gets there, level by level, its rises add up to the levels.  And here is
--| what is varied: the rises, each squared, summed.  The action of a thing that only moves.
def the_action (rises : List Nat) : Nat := (rises.map fun rise => rise * rise).sum

--| One rise: twice it is not over its square and one.
theorem twice_a_rise_is_not_over_its_square_and_one : ∀ rise : Nat, 2 * rise ≤ rise * rise + 1
  | 0 => Nat.zero_le _
  | 1 => by decide
  | rise + 2 => Nat.le_trans (Nat.mul_le_mul_right (rise + 2) (Nat.le_add_left 2 rise)) (Nat.le_add_right _ 1)

--| All of them: twice what they add up to is not over the action and one for every level.
theorem twice_the_rises_is_not_over_the_action_and_the_levels : ∀ rises : List Nat,
    2 * rises.sum ≤ the_action rises + rises.length
  | [] => Nat.le_refl _
  | rise :: rest => by
    have one := twice_a_rise_is_not_over_its_square_and_one rise
    have others := twice_the_rises_is_not_over_the_action_and_the_levels rest
    show 2 * (rise + rest.sum) ≤ (rise * rise + the_action rest) + (rest.length + 1)
    rw [Nat.mul_add]
    exact Nat.le_trans (Nat.add_le_add one others)
      (by rw [Nat.add_assoc, Nat.add_assoc, Nat.add_left_comm 1, Nat.add_comm 1 rest.length]; exact Nat.le_refl _)

--| THE LEAST ACTION.  Hold the ends: the rises add up to the levels.  Then the action is not under the levels, whatever the
--| rises were.
theorem with_the_ends_held_the_action_is_not_under_the_levels (rises : List Nat) (the_ends_are_held : rises.sum = rises.length) :
    rises.length ≤ the_action rises := by
  have bound := twice_the_rises_is_not_over_the_action_and_the_levels rises
  rw [the_ends_are_held, Nat.two_mul] at bound
  exact Nat.le_of_add_le_add_right bound

--| THE DEVICE'S OWN RISES.  What the acceleration rises by from each level to the next, read on Episode 8's reader of paths.
def the_rise_at (level : Nat) : Nat :=
  (the_acceleration_to (level + 1)).stokes.length - (the_acceleration_to level).stokes.length
def the_rises_to : Nat → List Nat
  | 0         => []
  | level + 1 => the_rise_at level :: the_rises_to level

--| THE MULTIPLIER.  Vary the action and the constraint together: the first variation of a rise squared, halved, is the rise,
--| and the first variation of what the rises add up to is one for each.  So where the action is least with the ends held,
--| every rise is one number, the multiplier.  On the device every rise is the fencepost.
theorem every_rise_is_the_fencepost (level : Nat) : the_rise_at level = the_fencepost_bug := by
  show (the_acceleration_to (level + 1)).stokes.length - (the_acceleration_to level).stokes.length = 1
  rw [the_acceleration_reads_the_velocity_it_reaches, the_acceleration_reads_the_velocity_it_reaches,
    the_universe_id_reads_the_level_and_its_zero, the_universe_id_reads_the_level_and_its_zero, Nat.add_sub_cancel_left]

--| And the device's rises hold the ends and are the least: they add up to the levels, and their action is the levels, which
--| nothing with the ends held goes under.  The residue is the multiplier of the constraint that the path has two ends.
theorem the_devices_rises_hold_the_ends_and_are_the_least : ∀ levels : Nat,
    (the_rises_to levels).length = levels ∧ (the_rises_to levels).sum = levels ∧ the_action (the_rises_to levels) = levels
  | 0 => ⟨rfl, rfl, rfl⟩
  | levels + 1 => by
    have so_far := the_devices_rises_hold_the_ends_and_are_the_least levels
    refine ⟨?_, ?_, ?_⟩
    · show (the_rises_to levels).length + 1 = levels + 1
      rw [so_far.1]
    · show the_rise_at levels + (the_rises_to levels).sum = levels + 1
      rw [every_rise_is_the_fencepost, so_far.2.1, Nat.add_comm]; rfl
    · show the_rise_at levels * the_rise_at levels + the_action (the_rises_to levels) = levels + 1
      rw [every_rise_is_the_fencepost, so_far.2.2, Nat.add_comm]; rfl

end the_constraint_and_its_multiplier
--#print axioms with_the_ends_held_the_action_is_not_under_the_levels    -- [propext]
--#print axioms every_rise_is_the_fencepost                              -- [propext]
--#print axioms the_devices_rises_hold_the_ends_and_are_the_least        -- [propext]


section universe_one_is_a_black_hole
open readers_experience readers_interpretation_of_the_experience the_area

--| TWO UNIVERSES.  The author's, 17 November 2026: isn't a temperature an average velocity measurement; universe 0 is the x
--| and universe 1 is the dx/dt; universe 1 is a black hole, you can't know what it is, you can only understand the average of
--| the volume around it; and level 1 is the first variation, which gives you the first derivative plus a polynomial.  The
--| ladder is dealt at two universes and no third: the box, and PRESENT's upness one above it.  Episode 11 calls the universe id
--| the velocity.  Episode 4's black hole is the step that holds a Type one universe up, and Episode 8's reader of paths gets
--| no fact from it.  Here is the velocity at a level: the universe id, less the zero it stands on.
def the_velocity_at (level : Nat) : Nat := (the_universe_id level).peano.length - the_fencepost_bug
def the_velocities_to : Nat → List Nat
  | 0         => [the_velocity_at 0]
  | level + 1 => the_velocity_at (level + 1) :: the_velocities_to level

theorem the_velocity_is_the_level (level : Nat) : the_velocity_at level = level := by
  show (the_universe_id level).peano.length - 1 = level
  rw [the_universe_id_reads_the_level_and_its_zero, Nat.add_sub_cancel]

--| THE AVERAGE.  What the jar holds is the velocities up to the level, added up.  Its first variation is how many of them
--| there are.  So what the jar holds over its first variation is the average velocity, and twice the sum is the level by the
--| count: the average is half the level.  Nobody read a velocity.  They read what was enclosed, and how much of it.
theorem the_temperature_is_the_average_velocity : ∀ level : Nat,
    (the_velocities_to level).sum = cells (what_the_jar_holds (the_jar_at level))
      ∧ (the_velocities_to level).length = cells (the_first_variation (that_box_at level))
      ∧ 2 * (the_velocities_to level).sum = level * (the_velocities_to level).length
  | 0 => ⟨rfl, rfl, rfl⟩
  | level + 1 => by
    have so_far := the_temperature_is_the_average_velocity level
    have holds := fun n => (what_the_jar_holds_over_its_first_variation_is_half_the_level n).1
    have varies := fun n => (the_residue_is_the_fencepost n).1
    have the_sum : (the_velocities_to (level + 1)).sum = cells (what_the_jar_holds (the_jar_at (level + 1))) := by
      show the_velocity_at (level + 1) + (the_velocities_to level).sum = _
      rw [so_far.1, holds, holds, the_velocity_is_the_level, the_sum_from_above,
        the_universe_id_reads_the_level_and_its_zero, Nat.add_comm]
    have the_count : (the_velocities_to (level + 1)).length = cells (the_first_variation (that_box_at (level + 1))) := by
      show (the_velocities_to level).length + 1 = _
      rw [so_far.2.1, varies, varies]; rfl
    refine ⟨the_sum, the_count, ?_⟩
    rw [the_sum, the_count]
    exact (what_the_jar_holds_over_its_first_variation_is_half_the_level (level + 1)).2

--| THE FIRST DIFFERENCE.  Step once and the temperature changes by the first derivative and a polynomial.  For the Area under
--| the levels the derivative is the change over two steps, halved, and the polynomial is half a fencepost: twice the change
--| over one step is the change over two and the fencepost.  The residual of Episode 12 does the same with the bent card for
--| its polynomial; that is above, where the residual steps by its slope exactly.
theorem the_first_difference_is_the_derivative_and_a_polynomial (level : Nat) :
    2 * (the_sum_from_above (level + 2) - the_sum_from_above (level + 1))
      = (the_sum_from_above (level + 2) - the_sum_from_above level) + the_fencepost_bug := by
  have next : ∀ n, the_sum_from_above (n + 1) = the_sum_from_above n + (n + 1) := fun n => by
    rw [the_sum_from_above, the_universe_id_reads_the_level_and_its_zero]
  rw [next (level + 1), next level, Nat.add_sub_cancel_left,
    Nat.add_assoc (the_sum_from_above level), Nat.add_sub_cancel_left, Nat.two_mul]
  show (level + 2) + (level + 2) = (level + 1) + (level + 2) + 1
  rw [Nat.add_right_comm (level + 1) (level + 2) 1]

end universe_one_is_a_black_hole
--#print axioms the_temperature_is_the_average_velocity                    -- [propext]
--#print axioms the_first_difference_is_the_derivative_and_a_polynomial    -- [propext]

section the_galerkin_process_finished
open readers_experience the_area the_area.Account

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
  simp only [balance_of_beside, balance_of_less, balance_of_each_for_each, balance_of_holding] at exact taken ⊢
  omega

--| And so the process is finished in form, though no whole number finishes it.  From the trial gap, where the mirror left
--| the solver, the first step leaves the bent card squared; the second, the bent card to the fourth; cleared of what the
--| steps divided by.  Each remainder is the square of the last.  Thirteen, squared, and squared again.
theorem each_remainder_is_the_square_of_the_last :
    (the_arm_weight true false + the_arm_weight false true) * (the_arm_weight true false + the_arm_weight false true)
        = 4 * (the_arm_weight true false * the_arm_weight false true) + bent_card * bent_card
      ∧ ((the_arm_weight true false + the_arm_weight false true) * (the_arm_weight true false + the_arm_weight false true)
            + 4 * (the_arm_weight true false * the_arm_weight false true))
          * ((the_arm_weight true false + the_arm_weight false true) * (the_arm_weight true false + the_arm_weight false true)
            + 4 * (the_arm_weight true false * the_arm_weight false true))
        = 4 * (the_arm_weight true false * the_arm_weight false true)
            * ((2 * (the_arm_weight true false + the_arm_weight false true)) * (2 * (the_arm_weight true false + the_arm_weight false true)))
          + (bent_card * bent_card) * (bent_card * bent_card) := by decide

end the_galerkin_process_finished
--#print axioms the_step_leaves_the_bent_card_by_the_step_squared    -- [propext, Quot.sound]
--#print axioms each_remainder_is_the_square_of_the_last             -- [propext]


section the_temperature_goes_as_the_acceleration
open readers_experience readers_interpretation_of_the_experience the_area

--| TEMPERATURE, AND ACCELERATION.  The author's, 18 November 2026: let's work on temperature ∝ acceleration.  The names first,
--| for they were wrong above.  Universe 0 is the place and universe 1 the velocity.  The temperature is the Area under the
--| levels.  Its first variation is the velocity, not the acceleration.  The acceleration is the first variation of that: the
--| rise from one level to the next, which at the least action is one number, the multiplier.  So let the rise be any number,
--| and build the rest from it by adding up, as the device does: a velocity is the rises so far, and the temperature is the
--| velocities so far.
def the_velocity_with (rise : Nat) : Nat → Nat
  | 0         => 0
  | level + 1 => the_velocity_with rise level + rise
def the_temperature_with (rise : Nat) : Nat → Nat
  | 0         => 0
  | level + 1 => the_temperature_with rise level + the_velocity_with rise (level + 1)

theorem the_velocity_is_the_rise_by_the_level (rise : Nat) : ∀ level : Nat, the_velocity_with rise level = rise * level
  | 0 => rfl
  | level + 1 => by rw [the_velocity_with, the_velocity_is_the_rise_by_the_level rise level, Nat.mul_succ]

--| THE PROPORTION.  The temperature is the acceleration by the Area under the levels.  At every level, for every rise.  Twice
--| it is the rise by the level by one more.  The Area is not the temperature's; it is what the levels enclose, the same for
--| every rise.  What is the temperature's own is the rise.
theorem the_temperature_is_the_acceleration_by_the_area (rise : Nat) : ∀ level : Nat,
    the_temperature_with rise level = rise * the_sum_from_above level
  | 0 => rfl
  | level + 1 => by
    rw [the_temperature_with, the_temperature_is_the_acceleration_by_the_area rise level,
      the_velocity_is_the_rise_by_the_level, the_sum_from_above, the_universe_id_reads_the_level_and_its_zero]
    exact (Nat.mul_add _ _ _).symm

theorem twice_the_temperature_is_the_rise_by_the_level_by_one_more (rise level : Nat) :
    2 * the_temperature_with rise level = rise * (level * (level + 1)) := by
  rw [the_temperature_is_the_acceleration_by_the_area, Nat.mul_left_comm, twice_the_sum_from_above]

--| So change the unit and both change together.  A reader who takes the rise some number of times over has that many times
--| the temperature, at every level; and of two readers, each one's temperature by the other's rise is the same number.  No
--| part of the temperature stays behind when the acceleration is changed.  There is no residue in this direction.
theorem the_temperature_and_the_acceleration_change_together (times rise level : Nat) :
    the_temperature_with (times * rise) level = times * the_temperature_with rise level := by
  rw [the_temperature_is_the_acceleration_by_the_area, the_temperature_is_the_acceleration_by_the_area, Nat.mul_assoc]

theorem two_readers_one_proportion (this_rise that_rise level : Nat) :
    the_temperature_with this_rise level * that_rise = the_temperature_with that_rise level * this_rise := by
  rw [the_temperature_is_the_acceleration_by_the_area, the_temperature_is_the_acceleration_by_the_area,
    Nat.mul_right_comm this_rise, Nat.mul_right_comm that_rise, Nat.mul_comm this_rise that_rise]

--| THE DEVICE'S.  Its rise is the fencepost, and with it the temperature built here is what the jar holds, and the velocity
--| is the level.  The residue found above is this rise: it was never left over from the proportion.  It is the acceleration.
theorem on_the_device_the_rise_is_the_fencepost (level : Nat) :
    the_temperature_with the_fencepost_bug level = cells (what_the_jar_holds (the_jar_at level))
      ∧ the_velocity_with the_fencepost_bug level = the_velocity_at level
      ∧ the_rise_at level = the_fencepost_bug := by
  refine ⟨?_, ?_, every_rise_is_the_fencepost level⟩
  · rw [the_temperature_is_the_acceleration_by_the_area, (what_the_jar_holds_over_its_first_variation_is_half_the_level level).1]
    exact Nat.one_mul _
  · rw [the_velocity_is_the_rise_by_the_level, the_velocity_is_the_level]; exact Nat.one_mul _

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
theorem the_relative_velocity_of_two_readers (this_rise that_rise level : Nat) :
    the_velocity_with this_rise level - the_velocity_with that_rise level = (this_rise - that_rise) * level := by
  rw [the_velocity_is_the_rise_by_the_level, the_velocity_is_the_rise_by_the_level, Nat.sub_mul]

theorem the_frames_are_equivalent (this_rise that_rise level : Nat) :
    the_temperature_with this_rise level * that_rise = the_temperature_with that_rise level * this_rise
      ∧ the_velocity_with this_rise level * that_rise = the_velocity_with that_rise level * this_rise := by
  refine ⟨two_readers_one_proportion this_rise that_rise level, ?_⟩
  rw [the_velocity_is_the_rise_by_the_level, the_velocity_is_the_rise_by_the_level, Nat.mul_right_comm this_rise,
    Nat.mul_right_comm that_rise, Nat.mul_comm this_rise that_rise]

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
theorem a_white_hole_is_asked_for_the_fact_and_a_black_hole_for_the_promise
    (idea happened : FACT) (promised : Prop) (rest : SpaceTimePath.{0}) :
    (SpaceTimePath.le (.einstein idea) (.whitehole happened FACT rest) = (idea = happened))
      ∧ (SpaceTimePath.le (.einstein idea) (.blackhole promised Type rest) = (idea.truth = promised)) := by
  constructor <;> simp only [SpaceTimePath.le]

--| And read, the white hole has given its fact and the black hole has given nothing yet: that is above, where a white hole
--| gives a fact and a black hole gives none.  What is past is counted.  What is promised is not.
end the_past_and_the_promise
--#print axioms a_white_hole_is_asked_for_the_fact_and_a_black_hole_for_the_promise    -- [propext, Quot.sound]


section the_promise_of_the_return
open readers_experience readers_interpretation_of_the_experience the_area

--| THE PATH NOTHING TAKES.  The author's, 18 November 2026: do you see the promise of the return photon in the math yet; the
--| path nothing takes.  It is the arm that cannot click.  A truth read as a falsehood: written, weighed, the frame and no
--| more, and nothing ever clicks on it.  The arm back, a falsehood read as a truth, clicks, and weighs the memory.  Nobody
--| reads either alone.  What is read is the one by the other, the round trip: the limit by the distance, the momentum squared.
theorem the_path_nothing_takes :
    the_arm_stores_a_fact_that_can_click true false = false ∧ the_arm_weight true false = the_limit
      ∧ the_arm_stores_a_fact_that_can_click false true = true ∧ the_arm_weight false true = the_distance
      ∧ the_arm_weight true false * the_arm_weight false true = the_limit * the_distance := by decide

--| THE PROMISE.  The arm nothing takes is short, and by one thing: the upness, the bent card, the residue.  The return weighs
--| the frame and the residue; so does each stay; the arm out weighs the frame alone.  What it is short is what is owed on it.
theorem the_arm_out_is_short_by_the_residue :
    the_arm_weight false true = the_arm_weight true false + the_upness
      ∧ the_arm_weight true true = the_arm_weight true false + the_upness
      ∧ the_arm_weight false false = the_arm_weight true false + the_upness := by decide

--| And it is a black hole: a statement held, that the true is the false, and no fact.  Episode 8's reader of paths returns
--| nothing for it.  The return is the white hole, which gives its fact.  Every closed walk crosses an even number of times,
--| Episode 12 has that: what goes out by this arm comes back by the other, or the walk does not close.
def the_promise_to_return : SpaceTimePath.{0} := .blackhole (true = false) Type the_path_here
theorem the_reader_gets_nothing_from_the_promise : the_promise_to_return.stokes = the_path_here.stokes := rfl

end the_promise_of_the_return

section only_the_fencepost_is_the_least
open readers_experience

--| ONLY THE FENCEPOST.  The least action with the ends held was shown to be reached by the device's rises.  Nothing else
--| reaches it.  A rise that meets its bound, twice it its square and one, is one; and rises that hold the ends and have the
--| least action all meet their bounds.
theorem a_rise_that_meets_its_bound_is_one : ∀ rise : Nat, rise * rise + 1 = 2 * rise → rise = 1
  | 0, met => absurd met (by decide)
  | 1, _ => rfl
  | rise + 2, met =>
    absurd (met ▸ Nat.lt_succ_of_le (Nat.mul_le_mul_right (rise + 2) (Nat.le_add_left 2 rise))) (Nat.lt_irrefl _)

theorem rises_that_meet_the_bound_are_all_one : ∀ rises : List Nat,
    2 * rises.sum = the_action rises + rises.length → ∀ rise, rise ∈ rises → rise = 1
  | [], _, _, here => nomatch here
  | first :: rest, met, rise, here => by
    have one := twice_a_rise_is_not_over_its_square_and_one first
    have others := twice_the_rises_is_not_over_the_action_and_the_levels rest
    have whole : 2 * (first + rest.sum) = (first * first + the_action rest) + (rest.length + 1) := met
    rw [Nat.mul_add] at whole
    have this_one : first * first + 1 = 2 * first := by omega
    have the_rest : 2 * rest.sum = the_action rest + rest.length := by omega
    cases here with
    | head => exact a_rise_that_meets_its_bound_is_one first this_one
    | tail _ further => exact rises_that_meet_the_bound_are_all_one rest the_rest rise further

theorem only_the_fencepost_is_the_least (rises : List Nat) (the_ends_are_held : rises.sum = rises.length)
    (the_action_is_least : the_action rises = rises.length) : ∀ rise, rise ∈ rises → rise = the_fencepost_bug := by
  have met : 2 * rises.sum = the_action rises + rises.length := by
    rw [the_ends_are_held, the_action_is_least, Nat.two_mul]
  exact rises_that_meet_the_bound_are_all_one rises met

end only_the_fencepost_is_the_least

section gibbs_and_boltzmann
open readers_experience readers_interpretation_of_the_experience the_area

--| GIBBS, AND BOLTZMANN.  The author's, 18 November 2026: Gibbs and Boltzmann are co and contra variant, I believe in that
--| order.  One counts what is enclosed and puts it over its first variation.  The other counts the first variation and puts
--| it over its own.  The first variation is under the line in the one and over it in the other: variance is which is which.
--| On the count the one is half the level, and the other is the level and the fencepost.
theorem gibbs_and_boltzmann_are_one_ratio_turned_over (level : Nat) :
    2 * cells (what_the_jar_holds (the_jar_at level)) = level * cells (the_first_variation (that_box_at level))
      ∧ cells (the_first_variation (that_box_at level))
          = (level + the_fencepost_bug)
              * (cells (the_first_variation (that_box_at (level + 1))) - cells (the_first_variation (that_box_at level))) := by
  refine ⟨(what_the_jar_holds_over_its_first_variation_is_half_the_level level).2, ?_⟩
  rw [(the_residue_is_the_fencepost level).2.2, Nat.add_sub_cancel_left, (the_residue_is_the_fencepost level).1]
  exact (Nat.mul_one _).symm

end gibbs_and_boltzmann
--#print axioms the_path_nothing_takes                              -- [propext]
--#print axioms the_arm_out_is_short_by_the_residue                 -- [propext]
--#print axioms the_reader_gets_nothing_from_the_promise
--#print axioms only_the_fencepost_is_the_least                     -- [propext, Quot.sound]
--#print axioms gibbs_and_boltzmann_are_one_ratio_turned_over       -- [propext]


section the_equation_of_state
open readers_experience readers_interpretation_of_the_experience the_area

--| THE EQUATION OF STATE, ON THE COUNT.  The author's, 18 November 2026: it is deriving their exact stand-ins, that
--| mathematically are identical; shape the work to look like the field equations.  Here are the stand-ins in the order the
--| route by heat calls for them, each a receipt already, gathered and nothing added.  The heat a reader takes through a patch
--| is the reader's rise by the Area under the levels: heat is temperature by the change of area, for every reader and every
--| patch.  Two readers differ by their rises and by nothing else: the rise divides out.  What comes through is conserved
--| across a join.  And what has come through, with the fencepost, is the entropy, which is the Area.
theorem the_equation_of_state_on_the_count (this_rise that_rise level : Nat) (this that : List FACT) :
    the_temperature_with this_rise level = this_rise * the_sum_from_above level
      ∧ the_temperature_with this_rise level * that_rise = the_temperature_with that_rise level * this_rise
      ∧ (the_flux (this ++ that)).length = (the_flux this).length + (the_flux that).length
      ∧ (the_flux this).length + the_fencepost_bug = (the_universe_id this.length).peano.length
      ∧ (the_universe_id this.length).peano.length = (the_area_of_a_tape this).riemann_integrate.length :=
  ⟨the_temperature_is_the_acceleration_by_the_area this_rise level, two_readers_one_proportion this_rise that_rise level,
   what_goes_in_comes_out this that, (in_cells_the_heat_is_the_entropy this).1, the_entropy_is_the_area this⟩

--| So on the count the source a cell and the curvature a cell are one number, the fencepost, for every reader: that is what
--| the route concludes of every direction through every point before it turns directions into a tensor.  The turning is not
--| done here.  Episode 12 has what it would be done with, on four directions: a square that is flat when its edges agree and
--| curved when one is turned, a curl of a gradient that is nothing, a seam that carries no net flux.  They are not yet joined
--| to this.
end the_equation_of_state
--#print axioms the_equation_of_state_on_the_count    -- [propext, Quot.sound]

section the_curvature_is_in_the_spline
open readers_experience readers_interpretation_of_the_experience the_area the_area.Account

--| THE CURVATURE IS IN THE SPLINE.  Episode 3's spline has three constructors: an observation, a knot (the first variation)
--| and an interpolant (the second variation, the weak derivative).  On the count the three are the temperature, the velocity
--| and the acceleration, and the last is the curvature: the second difference of the temperature is the rise, at every level
--| and for every rise.  This is the focusing: what the area gains from one level to the next grows by the rise and by
--| nothing else.
theorem the_second_variation_of_the_temperature_is_the_acceleration (rise level : Nat) :
    (the_temperature_with rise (level + 2) - the_temperature_with rise (level + 1))
      - (the_temperature_with rise (level + 1) - the_temperature_with rise level) = rise := by
  show (the_temperature_with rise (level + 1) + (the_velocity_with rise (level + 1) + rise) - the_temperature_with rise (level + 1))
      - (the_temperature_with rise level + the_velocity_with rise (level + 1) - the_temperature_with rise level) = rise
  omega

--| And the curvature does not step: the third difference is nothing.  Card 3's residual says the same of the slope's slope
--| (`twice_the_coefficient_does_not_step`), and the tape owes exactly it (`the_tape_owes_the_last_derivative`).
theorem the_curvature_does_not_step (rise level : Nat) :
    (the_temperature_with rise (level + 3) - the_temperature_with rise (level + 2))
        - (the_temperature_with rise (level + 2) - the_temperature_with rise (level + 1))
      = (the_temperature_with rise (level + 2) - the_temperature_with rise (level + 1))
        - (the_temperature_with rise (level + 1) - the_temperature_with rise level) := by
  rw [the_second_variation_of_the_temperature_is_the_acceleration rise (level + 1),
      the_second_variation_of_the_temperature_is_the_acceleration rise level]

end the_curvature_is_in_the_spline

section the_four_zeros
open readers_experience readers_interpretation_of_the_experience the_representation

--| FOUR ZEROS.  A zero is a `Number.zero` on a fact.  The reader's experience has one already, `another_zero`, on the truth.
--| The clock has two, one for each coin.  The interpretation has one on the fact that the two tables are the same
--| difference.  Which fact sits in the last is this episode's choice.
def the_zero_of_the_experience : Number := another_zero
def the_zero_of_the_interpretation : Number := Number.zero SAME_DIFFERENCE
def the_zero_of_the_clock : Number := Number.zero (bitFACT true)
def the_zero_of_the_other_clock : Number := Number.zero (bitFACT false)
def the_four_zeros : List Number :=
  [the_zero_of_the_experience, the_zero_of_the_interpretation, the_zero_of_the_clock, the_zero_of_the_other_clock]

--| Each is under every number, and each reads one cell: the fencepost.
theorem a_zero_is_under_every_number (fact : FACT) (number : Number) : Number.le (.zero fact) number := by
  cases number <;> trivial
theorem every_zero_reads_one_cell :
    the_four_zeros.map (fun zero => zero.peano.length) = [1, 1, 1, 1] := rfl

--| The zero of the experience is the universe id of level nothing, and it is the clock's zero: the same by `rfl`.
theorem the_zero_of_the_experience_is_the_first_universe_and_the_clocks :
    the_zero_of_the_experience = the_universe_id 0 ∧ the_zero_of_the_experience = the_zero_of_the_clock := ⟨rfl, rfl⟩

--| The two clocks' zeros are each under the other and are not the same zero.
theorem the_two_clocks_zeros_are_under_each_other_and_are_not_one :
    Number.le the_zero_of_the_clock the_zero_of_the_other_clock
      ∧ Number.le the_zero_of_the_other_clock the_zero_of_the_clock
      ∧ the_zero_of_the_clock ≠ the_zero_of_the_other_clock := by
  refine ⟨trivial, trivial, ?_⟩
  intro h; injection h with h
  exact absurd (congrArg (fun f : FACT => @decide f.truth f.click) h) (by decide)

--| Asked only whether it is true, the interpretation's zero is the experience's.
theorem asked_only_whether_it_is_true_the_interpretations_zero_is_the_experiences :
    the_zero_of_the_interpretation = the_zero_of_the_experience :=
  congrArg Number.zero (two_facts_that_are_true_are_one_fact SAME_DIFFERENCE FACT.Truth same_difference_clicks
    (@of_decide_eq_true FACT.Truth.truth FACT.Truth.click rfl))
end the_four_zeros

section from_directions_to_a_table
open readers_experience

--| FOUR DIRECTIONS.  Episode 12's lattice has four directions, and a direction there is a pair of coins: the four arms.  Three
--| arms click and one does not.  Let that be the metric: one for an arm that clicks, one owed for the arm that does not, and
--| nothing between two different arms.  Three one way and one the other.
def the_arms : List Direction := [(true, true), (true, false), (false, true), (false, false)]
def the_metric_on_the_arms (this that : Direction) : Int :=
  if this = that then (if the_arm_stores_a_fact_that_can_click this.1 this.2 then 1 else -1) else 0

theorem the_metric_is_three_one_way_and_one_the_other :
    the_arms.map (fun arm => the_metric_on_the_arms arm arm) = [1, -1, 1, 1] := by decide

--| What a table on the arms reads along a direction: every pair of arms, the table's entry by the direction's two parts.
def along (table : Direction → Direction → Int) (direction : Direction → Int) : Int :=
  (the_arms.map fun this => (the_arms.map fun that => table this that * direction this * direction that).sum).sum

--| A direction is null when the metric reads nothing along it.
abbrev is_null (direction : Direction → Int) : Prop := along the_metric_on_the_arms direction = 0

--| The directions used: the arm that does not click with one that does, either way; and five of the first with three and
--| four of two others.
def out_and (space : Direction) (way : Int) : Direction → Int :=
  fun arm => if arm = (true, false) then 1 else if arm = space then way else 0
def five_three_four (first second : Direction) : Direction → Int :=
  fun arm => if arm = (true, false) then 5 else if arm = first then 3 else if arm = second then 4 else 0
def the_null_directions : List (Direction → Int) :=
  [out_and (true, true) 1, out_and (true, true) (-1), out_and (false, true) 1, out_and (false, true) (-1),
   out_and (false, false) 1, out_and (false, false) (-1),
   five_three_four (true, true) (false, true), five_three_four (true, true) (false, false),
   five_three_four (false, true) (false, false)]

theorem these_directions_are_null : ∀ direction ∈ the_null_directions, is_null direction := by decide

--| FROM EVERY NULL DIRECTION TO A TABLE.  A symmetric table that reads nothing along these nine null directions is the
--| metric, by one number.  Ten entries, nine conditions, one left.
theorem a_table_that_reads_nothing_along_the_null_directions_is_the_metric_by_a_number
    (table : Direction → Direction → Int) (symmetric : ∀ this that, table this that = table that this)
    (nothing : ∀ direction ∈ the_null_directions, along table direction = 0) :
    ∀ this that, table this that = - table (true, false) (true, false) * the_metric_on_the_arms this that := by
  have s1 := symmetric (true, false) (true, true)
  have s2 := symmetric (true, false) (false, true)
  have s3 := symmetric (true, false) (false, false)
  have s4 := symmetric (true, true) (false, true)
  have s5 := symmetric (true, true) (false, false)
  have s6 := symmetric (false, true) (false, false)
  have n1 := nothing (out_and (true, true) 1) (by simp [the_null_directions])
  have n2 := nothing (out_and (true, true) (-1)) (by simp [the_null_directions])
  have n3 := nothing (out_and (false, true) 1) (by simp [the_null_directions])
  have n4 := nothing (out_and (false, true) (-1)) (by simp [the_null_directions])
  have n5 := nothing (out_and (false, false) 1) (by simp [the_null_directions])
  have n6 := nothing (out_and (false, false) (-1)) (by simp [the_null_directions])
  have n7 := nothing (five_three_four (true, true) (false, true)) (by simp [the_null_directions])
  have n8 := nothing (five_three_four (true, true) (false, false)) (by simp [the_null_directions])
  have n9 := nothing (five_three_four (false, true) (false, false)) (by simp [the_null_directions])
  simp [along, the_arms, out_and, five_three_four] at n1 n2 n3 n4 n5 n6 n7 n8 n9
  intro this that
  obtain ⟨a, b⟩ := this; obtain ⟨c, d⟩ := that
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp [the_metric_on_the_arms, the_arm_stores_a_fact_that_can_click] <;> omega
end from_directions_to_a_table
section the_bianchi_identity_on_the_torus

--| THE BIANCHI IDENTITY.  Episode 12 has it that the curl of a gradient is nothing.  One step further: take any field on the
--| links of the torus of four directions, take its curl, and difference the curl around three directions in turn.  The sum
--| is nothing, for every field, at every site, on every torus.  Nothing is assumed of the field.
theorem the_curl_differenced_around_three_directions_is_nothing {n : Nat} (A : Direction → Site4 n → Int)
    (first second third : Direction) (x : Site4 n) :
    the_difference first (the_curl_on A second third) x + the_difference second (the_curl_on A third first) x
      + the_difference third (the_curl_on A first second) x = 0 := by
  simp only [the_difference, the_curl_on]
  rw [the_steps_commute first second x, the_steps_commute first third x, the_steps_commute second third x]
  omega
end the_bianchi_identity_on_the_torus

section the_equation_on_the_arms

--| What a difference of two tables reads along a direction is the difference of what they read.
theorem along_a_difference (this that : Direction → Direction → Int) (direction : Direction → Int) :
    along (fun a b => this a b - that a b) direction = along this direction - along that direction := by
  simp only [along, the_arms, List.map, List.sum_cons, List.sum_nil, Int.sub_mul]; omega

--| THE EQUATION ON THE ARMS.  Two symmetric tables on the four arms, a source and a curvature.  If they read the same along
--| every null direction (the heat that crosses is the area lost, for every observer), then the source is the curvature and
--| the metric by one number.  The number is the one entry the condition leaves free: the arm that does not click.
def the_number_left_free (source curvature : Direction → Direction → Int) : Int :=
  curvature (true, false) (true, false) - source (true, false) (true, false)

theorem the_equation_on_the_arms (source curvature : Direction → Direction → Int)
    (the_source_is_symmetric : ∀ this that, source this that = source that this)
    (the_curvature_is_symmetric : ∀ this that, curvature this that = curvature that this)
    (for_every_observer : ∀ direction ∈ the_null_directions, along source direction = along curvature direction) :
    ∀ this that, source this that
      = curvature this that + the_number_left_free source curvature * the_metric_on_the_arms this that := by
  intro this that
  have h := a_table_that_reads_nothing_along_the_null_directions_is_the_metric_by_a_number
    (fun a b => source a b - curvature a b)
    (fun a b => by show source a b - curvature a b = source b a - curvature b a
                   rw [the_source_is_symmetric a b, the_curvature_is_symmetric a b])
    (fun direction member => by rw [along_a_difference, for_every_observer direction member]; omega) this that
  have e : - (source (true, false) (true, false) - curvature (true, false) (true, false))
      = the_number_left_free source curvature := by simp only [the_number_left_free]; omega
  rw [e] at h; omega

--| On the torus, site by site: the same, with a number at every site.  Where neither table steps along a direction, the
--| number does not step either: one number for the whole torus.
theorem the_equation_on_the_torus {n : Nat} (source curvature : Site4 n → Direction → Direction → Int)
    (the_source_is_symmetric : ∀ x this that, source x this that = source x that this)
    (the_curvature_is_symmetric : ∀ x this that, curvature x this that = curvature x that this)
    (for_every_observer : ∀ x, ∀ direction ∈ the_null_directions, along (source x) direction = along (curvature x) direction) :
    ∀ x this that, source x this that
      = curvature x this that + the_number_left_free (source x) (curvature x) * the_metric_on_the_arms this that :=
  fun x => the_equation_on_the_arms (source x) (curvature x) (the_source_is_symmetric x) (the_curvature_is_symmetric x)
    (for_every_observer x)

theorem where_neither_table_steps_the_number_does_not_step {n : Nat} (source curvature : Site4 n → Direction → Direction → Int)
    (way : Direction) (x : Site4 n)
    (the_source_does_not_step : source (the_step way x) = source x)
    (the_curvature_does_not_step : curvature (the_step way x) = curvature x) :
    the_number_left_free (source (the_step way x)) (curvature (the_step way x))
      = the_number_left_free (source x) (curvature x) := by
  rw [the_source_does_not_step, the_curvature_does_not_step]
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
def the_turn : Table := fun a b => the_full_other_table a b - the_full_table a b
def the_square_turned_by (rise : Int) : Table :=
  the_holonomy (the_varied_table the_full_table the_turn rise) the_full_table the_full_table the_full_table
def what_one_whole_turn_shows : Table := the_holonomy the_turn the_full_table the_full_table the_full_table

theorem the_square_curves_by_the_rise (rise : Int) (a b : Bool) :
    the_square_turned_by rise a b = the_scaled_identity (234 * 234) a b + rise * what_one_whole_turn_shows a b := by
  rw [the_square_turned_by, the_holonomy_is_linear_in_its_bottom_link, ← the_uniform_square_is_flat]; rfl

theorem off_the_diagonal_the_square_shows_the_rise_and_nothing_else (rise : Int) :
    the_square_turned_by rise true false = rise * what_one_whole_turn_shows true false
      ∧ the_square_turned_by rise false true = rise * what_one_whole_turn_shows false true := by
  constructor <;> rw [the_square_curves_by_the_rise] <;> simp [the_scaled_identity]

theorem a_whole_turn_is_the_other_table_and_it_shows_something :
    (∀ a b, the_varied_table the_full_table the_turn 1 a b = the_full_other_table a b)
      ∧ what_one_whole_turn_shows true false ≠ 0 := by
  constructor
  · intro a b; simp only [the_varied_table, the_turn]; omega
  · decide
end the_turn_is_the_rise

section the_source_on_the_arms
open readers_experience

--| THE SOURCE, SORTED BY ARM.  The flux is one truth a fact.  Sort what is carried by the arm that carried it: the arm's
--| weight on the arm, and nothing between two arms.  Five on the arm that does not click and eighteen on each that does.
def the_source_on_the_arms (this that : Direction) : Int :=
  if this = that then (the_arm_weight this.1 this.2 : Int) else 0
def on_the_arm_out (this that : Direction) : Int := if this = (true, false) ∧ that = (true, false) then 1 else 0

theorem the_source_is_five_and_three_eighteens :
    the_arms.map (fun arm => the_source_on_the_arms arm arm) = [18, 5, 18, 18] := by decide

--| It is the distance by the metric, and the different on the arm out.
theorem the_source_is_the_distance_by_the_metric_and_the_different_on_the_arm_out :
    ∀ this ∈ the_arms, ∀ that ∈ the_arms,
      the_source_on_the_arms this that = 18 * the_metric_on_the_arms this that + 23 * on_the_arm_out this that := by decide

--| THE CURVATURE ON THE COUNT.  The second difference of the area is the rise, the same along every arm: the rise on each
--| arm and nothing between.  That it is the same along every arm is this episode's choice.
def the_curvature_on_the_count (rise : Int) (this that : Direction) : Int := if this = that then rise else 0

--| THE CHECK.  Along each of the nine null directions the source reads the different by the square of the part along the arm
--| out, and the curvature of one fencepost reads twice that square.  So twice the source reads as twenty-three curvatures,
--| along every one: the hypothesis holds, with twenty-three halves between them.
theorem along_the_null_directions_twice_the_source_reads_as_twenty_three_curvatures :
    ∀ direction ∈ the_null_directions,
      along the_source_on_the_arms direction = 23 * (direction (true, false) * direction (true, false))
        ∧ along (the_curvature_on_the_count 1) direction = 2 * (direction (true, false) * direction (true, false))
        ∧ 2 * along the_source_on_the_arms direction = 23 * along (the_curvature_on_the_count 1) direction := by decide

--| And so the equation, with what is left over: twice the source is twenty-three curvatures and the bent card by the metric.
theorem twice_the_source_is_the_curvatures_and_the_bent_card_by_the_metric :
    ∀ this ∈ the_arms, ∀ that ∈ the_arms,
      2 * the_source_on_the_arms this that
        = 23 * the_curvature_on_the_count 1 this that + (bent_card : Int) * the_metric_on_the_arms this that := by decide

--| What is left over is no more than this: any table that is one number on the arm out and another on the three is their
--| half sum on every arm and their half difference by the metric.  The equation holds for every such pair.
theorem any_such_table_is_its_half_sum_and_its_half_difference_by_the_metric (out others : Int) :
    ∀ this ∈ the_arms, ∀ that ∈ the_arms,
      2 * (if this = that then (if this = (true, false) then out else others) else 0)
        = (others + out) * the_curvature_on_the_count 1 this that + (others - out) * the_metric_on_the_arms this that := by
  intro this h1 that h2
  simp only [the_arms, List.mem_cons, List.mem_nil_iff, or_false] at h1 h2
  rcases h1 with rfl | rfl | rfl | rfl <;> rcases h2 with rfl | rfl | rfl | rfl <;>
    simp [the_curvature_on_the_count, the_metric_on_the_arms, the_arm_stores_a_fact_that_can_click] <;> omega
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
def the_curvature_of {n : Nat} (A : Direction → Site4 n → Int) (this that : Direction) (x : Site4 n) : Int :=
  the_difference this (A that) x

theorem the_table_differs_from_itself_turned_over_by_the_curl {n : Nat} (A : Direction → Site4 n → Int)
    (this that : Direction) (x : Site4 n) :
    the_curvature_of A this that x - the_curvature_of A that this x = the_curl_on A this that x := rfl

theorem the_table_of_a_gradient_is_symmetric {n : Nat} (f : Site4 n → Int) (this that : Direction) (x : Site4 n) :
    the_curvature_of (the_gradient f) this that x = the_curvature_of (the_gradient f) that this x := by
  have h := the_curl_of_a_gradient_is_nothing f this that x
  rw [← the_table_differs_from_itself_turned_over_by_the_curl] at h; omega

--| THE AREA ON THE SITES.  A site is four places, one along each arm.  Along each arm the area under the levels of one
--| fencepost, by that arm's rise; the area at the site is the four together.  Its gradient is a field on the links: the
--| velocity.  The table of that field is the curvature.
def the_place_along {n : Nat} (arm : Direction) (x : Site4 n) : Nat :=
  if arm.1 then (if arm.2 then x.2.2.val else x.2.1.val) else (if arm.2 then x.1.2.val else x.1.1.val)
def the_area_at {n : Nat} (rise : Direction → Int) (x : Site4 n) : Int :=
  (the_arms.map fun arm => rise arm * (the_temperature_with 1 (the_place_along arm x) : Int)).sum

theorem a_step_inside_is_one_more {n : Nat} (a : Fin (n+1)) (inside : a.val + 1 ≤ n) : (a + 1).val = a.val + 1 := by
  rw [Fin.val_add]
  have h1 : (1 : Fin (n+1)).val = 1 % (n+1) := rfl
  rw [h1, Nat.mod_eq_of_lt (by omega : 1 < n + 1), Nat.mod_eq_of_lt (by omega)]

theorem the_second_difference_is_one_cell (level : Nat) :
    ((the_temperature_with 1 (level + 2) : Nat) : Int) - (the_temperature_with 1 (level + 1) : Nat)
      - ((the_temperature_with 1 (level + 1) : Nat) - (the_temperature_with 1 level : Nat)) = 1 := by
  show (((the_temperature_with 1 (level + 1) + (the_velocity_with 1 (level + 1) + 1) : Nat)) : Int) - _
    - ((((the_temperature_with 1 level + the_velocity_with 1 (level + 1) : Nat)) : Int) - _) = 1
  omega

--| THE CURVATURE OF AN AREA IS ITS RISES.  Two steps inside the torus's seam, at every site, on every torus, for any rises:
--| the table is the arm's rise on the arm and nothing between two arms.  The rises are all there is in it.
theorem the_curvature_of_an_area_is_its_rises {n : Nat} (rise : Direction → Int) (x : Site4 n)
    (inside : ∀ arm ∈ the_arms, the_place_along arm x + 2 ≤ n) (this that : Direction) :
    the_curvature_of (the_gradient (the_area_at rise)) this that x = if this = that then rise this else 0 := by
  obtain ⟨⟨a, b⟩, ⟨c, d⟩⟩ := x
  have ha := inside (false, false) (by simp [the_arms])
  have hb := inside (false, true) (by simp [the_arms])
  have hc := inside (true, false) (by simp [the_arms])
  have hd := inside (true, true) (by simp [the_arms])
  simp [the_place_along] at ha hb hc hd
  have ta := the_second_difference_is_one_cell a.val; have tb := the_second_difference_is_one_cell b.val
  have tc := the_second_difference_is_one_cell c.val; have td := the_second_difference_is_one_cell d.val
  have ea := a_step_inside_is_one_more a (by omega); have ea2 := a_step_inside_is_one_more (a+1) (by omega)
  have eb := a_step_inside_is_one_more b (by omega); have eb2 := a_step_inside_is_one_more (b+1) (by omega)
  have ec := a_step_inside_is_one_more c (by omega); have ec2 := a_step_inside_is_one_more (c+1) (by omega)
  have ed := a_step_inside_is_one_more d (by omega); have ed2 := a_step_inside_is_one_more (d+1) (by omega)
  rw [ea, Nat.add_assoc] at ea2; rw [eb, Nat.add_assoc] at eb2; rw [ec, Nat.add_assoc] at ec2; rw [ed, Nat.add_assoc] at ed2
  have ka := congrArg (fun z => rise (false, false) * z) ta
  have kb := congrArg (fun z => rise (false, true) * z) tb
  have kc := congrArg (fun z => rise (true, false) * z) tc
  have kd := congrArg (fun z => rise (true, true) * z) td
  simp only [Int.mul_sub, Int.mul_one] at ka kb kc kd
  obtain ⟨p, q⟩ := this; obtain ⟨r, s⟩ := that
  cases p <;> cases q <;> cases r <;> cases s <;>
    simp only [the_curvature_of, the_gradient, the_difference, the_step, the_area_at, the_arms, the_place_along,
      List.map, List.sum_cons, List.sum_nil, ea, eb, ec, ed, ea2, eb2, ec2, ed2, if_true, if_false, Bool.false_eq_true,
      Prod.mk.injEq, and_self, and_false, false_and, Bool.true_eq_false, Nat.reduceAdd] <;>
    omega

--| THREE AREAS.  The rise along an arm may be what the arm stores (its weight); or one fencepost on every arm; or one on an
--| arm that clicks and one owed on the arm that does not.
def the_rise_the_arm_stores (arm : Direction) : Int := (the_arm_weight arm.1 arm.2 : Int)
def one_fencepost_on_every_arm (_ : Direction) : Int := 1
def the_rise_by_the_click (arm : Direction) : Int := the_metric_on_the_arms arm arm

theorem three_areas_three_tables {n : Nat} (x : Site4 n) (inside : ∀ arm ∈ the_arms, the_place_along arm x + 2 ≤ n)
    (this that : Direction) :
    the_curvature_of (the_gradient (the_area_at the_rise_the_arm_stores)) this that x = the_source_on_the_arms this that
      ∧ the_curvature_of (the_gradient (the_area_at one_fencepost_on_every_arm)) this that x
          = the_curvature_on_the_count 1 this that
      ∧ the_curvature_of (the_gradient (the_area_at the_rise_by_the_click)) this that x
          = the_metric_on_the_arms this that := by
  refine ⟨?_, ?_, ?_⟩ <;> rw [the_curvature_of_an_area_is_its_rises _ x inside]
  · rfl
  · rfl
  · simp only [the_rise_by_the_click, the_metric_on_the_arms]; split <;> simp_all

--| THREE AREAS, THREE CONSTANTS.  With the rise the arm stores, the curvature is the source, and nothing is left over.  With
--| one fencepost on every arm, twice the source is twenty-three curvatures and the bent card by the metric.  With the rise
--| by the click, the curvature is the metric, it reads nothing along a null direction where the source reads twenty-three,
--| and no number makes them agree.  The table does not choose among the three.  The area does, and the area is handed in.
theorem three_areas_three_constants :
    (∀ direction ∈ the_null_directions,
        along the_source_on_the_arms direction = along the_source_on_the_arms direction + 0 * along the_metric_on_the_arms direction)
      ∧ (∀ this ∈ the_arms, ∀ that ∈ the_arms, 2 * the_source_on_the_arms this that
            = 23 * the_curvature_on_the_count 1 this that + (bent_card : Int) * the_metric_on_the_arms this that)
      ∧ (along the_metric_on_the_arms (out_and (true, true) 1) = 0
            ∧ along the_source_on_the_arms (out_and (true, true) 1) = 23) := by
  refine ⟨fun _ _ => by omega, twice_the_source_is_the_curvatures_and_the_bent_card_by_the_metric, by decide⟩
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
def the_field_of {n : Nat} (A : Direction → Site4 n → Int) (this that : Direction) (x : Site4 n) : Int :=
  the_curvature_of A this that x - the_curvature_of A that this x

theorem the_field_is_the_curl {n : Nat} (A : Direction → Site4 n → Int) (this that : Direction) (x : Site4 n) :
    the_field_of A this that x = the_curl_on A this that x := rfl

theorem the_field_turned_over_is_the_field_owed {n : Nat} (A : Direction → Site4 n → Int) (this that : Direction) (x : Site4 n) :
    the_field_of A that this x = - the_field_of A this that x := by simp only [the_field_of]; omega

--| On the device's own table it is the bent card by the quarter turn.
theorem the_table_less_itself_turned_over_is_the_bent_card_by_the_quarter_turn (a b : Bool) :
    the_full_table a b - the_full_other_table a b = (bent_card : Int) * the_quarter_turn a b := by
  cases a <;> cases b <;> decide

--| WHAT THE FIRST READING CANNOT SEE.  A table that is itself owed when turned over reads nothing along every direction, null
--| or not.  So no reading along directions finds the field.
theorem owed_both_ways_is_nothing (t s p q : Int) (owed : s = - t) : t * p * q + s * q * p = 0 := by
  subst owed; rw [Int.neg_mul, Int.neg_mul, Int.mul_right_comm]; omega

theorem a_table_owed_when_turned_over_reads_nothing_along_any_direction
    (table : Direction → Direction → Int) (owed : ∀ this that, table that this = - table this that)
    (direction : Direction → Int) : along table direction = 0 := by
  have d (arm : Direction) : table arm arm * direction arm * direction arm = 0 := by
    have h := owed arm arm
    have z : table arm arm = 0 := by omega
    rw [z, Int.zero_mul, Int.zero_mul]
  have p (this that : Direction) := owed_both_ways_is_nothing (table this that) (table that this) (direction this)
    (direction that) (owed this that)
  have d1 := d (true, true); have d2 := d (true, false); have d3 := d (false, true); have d4 := d (false, false)
  have p1 := p (true, true) (true, false); have p2 := p (true, true) (false, true); have p3 := p (true, true) (false, false)
  have p4 := p (true, false) (false, true); have p5 := p (true, false) (false, false); have p6 := p (false, true) (false, false)
  simp only [along, the_arms, List.map, List.sum_cons, List.sum_nil]
  omega

--| THE GAUGE.  Add any gradient to the field on the links: the curvature table changes and the field does not.
theorem a_gradient_does_not_move_the_field {n : Nat} (A : Direction → Site4 n → Int) (f : Site4 n → Int)
    (this that : Direction) (x : Site4 n) :
    the_field_of (fun arm site => A arm site + the_gradient f arm site) this that x = the_field_of A this that x := by
  simp only [the_field_of, the_curvature_of, the_gradient, the_difference]
  rw [the_steps_commute this that x]; omega

--| THE CURRENT.  Raise both seats of the field by the metric of three and one, and difference the first seat away.
def the_current_of {n : Nat} (A : Direction → Site4 n → Int) (that : Direction) (x : Site4 n) : Int :=
  (the_arms.map fun this => the_metric_on_the_arms this this * the_metric_on_the_arms that that
    * the_difference this (the_field_of A this that) x).sum

--| WHAT GOES IN COMES OUT.  The current's own differences add up to nothing, for every field, at every site, on every torus.
theorem the_current_is_conserved {n : Nat} (A : Direction → Site4 n → Int) (x : Site4 n) :
    (the_arms.map fun that => the_difference that (the_current_of A that) x).sum = 0 := by
  have g1 : the_metric_on_the_arms (true, true) (true, true) = 1 := by decide
  have g2 : the_metric_on_the_arms (true, false) (true, false) = -1 := by decide
  have g3 : the_metric_on_the_arms (false, true) (false, true) = 1 := by decide
  have g4 : the_metric_on_the_arms (false, false) (false, false) = 1 := by decide
  simp only [the_current_of, the_field_of, the_curvature_of, the_difference, the_arms, List.map, List.sum_cons, List.sum_nil,
    g1, g2, g3, g4]
  rw [the_steps_commute (true, true) (true, false) x, the_steps_commute (true, true) (false, true) x,
      the_steps_commute (true, true) (false, false) x, the_steps_commute (true, false) (false, true) x,
      the_steps_commute (true, false) (false, false) x, the_steps_commute (false, true) (false, false) x]
  omega
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
theorem one_is_one_more_cell (fact : FACT) (number : Number) :
    (Number.one fact number).peano.length = number.peano.length + 1 := rfl

--| The entropy: the next universe id is `Number.one` on the last.
theorem one_is_one_more_level (level : Nat) :
    the_universe_id (level + 1) = Number.one FACT.Truth (the_universe_id level) := the_universe_id_steps level

--| The temperature: at the rise of one, the velocity gains one a level and the area gains that velocity.
theorem one_is_one_more_rise (level : Nat) :
    the_velocity_with 1 (level + 1) = the_velocity_with 1 level + 1
      ∧ the_temperature_with 1 (level + 1) = the_temperature_with 1 level + the_velocity_with 1 (level + 1) := ⟨rfl, rfl⟩

--| The fencepost: a zero is already one cell, so the cells are one more than the levels, and that one is the fencepost.
theorem one_is_the_fencepost (level : Nat) :
    (the_universe_id level).peano.length = level + the_fencepost_bug ∧ the_fencepost_bug = 1 :=
  ⟨the_universe_id_reads_the_level_and_its_zero level, rfl⟩

--| THE FOUR, AS ONE.  On the number of a level: one more cell is one more level is one more rise, and what is over is the
--| fencepost.
theorem the_four_ones_are_one_step (level : Nat) :
    (the_universe_id (level + 1)).peano.length = (the_universe_id level).peano.length + 1
      ∧ the_universe_id (level + 1) = Number.one FACT.Truth (the_universe_id level)
      ∧ the_velocity_with 1 (level + 1) = the_velocity_with 1 level + 1
      ∧ (the_universe_id level).peano.length = the_velocity_with 1 level + the_fencepost_bug := by
  refine ⟨?_, the_universe_id_steps level, rfl, ?_⟩
  · rw [the_universe_id_steps]; rfl
  · rw [the_universe_id_reads_the_level_and_its_zero, the_velocity_is_the_rise_by_the_level, Nat.one_mul]; rfl
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
def the_trace_of {n : Nat} (f : Site4 n → Int) (x : Site4 n) : Int :=
  (the_arms.map fun arm => the_metric_on_the_arms arm arm * the_curvature_of (the_gradient f) arm arm x).sum
def the_divergence_of {n : Nat} (f : Site4 n → Int) (that : Direction) (x : Site4 n) : Int :=
  (the_arms.map fun this => the_metric_on_the_arms this this
    * the_difference this (the_curvature_of (the_gradient f) this that) x).sum

theorem the_divergence_of_the_curvature_is_the_difference_of_its_trace {n : Nat} (f : Site4 n → Int)
    (that : Direction) (x : Site4 n) :
    the_divergence_of f that x = the_difference that (the_trace_of f) x := by
  have g1 : the_metric_on_the_arms (true, true) (true, true) = 1 := by decide
  have g2 : the_metric_on_the_arms (true, false) (true, false) = -1 := by decide
  have g3 : the_metric_on_the_arms (false, true) (false, true) = 1 := by decide
  have g4 : the_metric_on_the_arms (false, false) (false, false) = 1 := by decide
  obtain ⟨p, q⟩ := that
  cases p <;> cases q <;>
    simp only [the_divergence_of, the_trace_of, the_curvature_of, the_gradient, the_difference, the_arms, List.map,
      List.sum_cons, List.sum_nil, g1, g2, g3, g4,
      the_steps_commute (true, true) (true, false), the_steps_commute (true, true) (false, true),
      the_steps_commute (true, true) (false, false), the_steps_commute (true, false) (false, true),
      the_steps_commute (true, false) (false, false), the_steps_commute (false, true) (false, false)] <;>
    omega
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
theorem without_the_link_it_is_not :
    the_turns_product (the_turns_conjugate (the_turns_product the_quarter_turn_turn (the_whole_turn 1))) (the_whole_turn 1)
      ≠ the_turns_product (the_turns_conjugate (the_whole_turn 1)) (the_whole_turn 1) := by decide
end matter_on_the_links
section the_constant_of_integration
open readers_experience

--| THE CONSTANT OF INTEGRATION.  Let a source on the arms, at every site, be the curvature of an area and a number by the
--| metric, the number free to differ from site to site: that is what the equation on the arms gives.  Let the source be
--| conserved: its first seat differenced away by the signs is nothing.  Then the number and the trace together do not step,
--| along any arm, at any site.  The source is the curvature less its trace by the metric, and one constant by the metric.
theorem the_number_and_the_trace_do_not_step {n : Nat} (f : Site4 n → Int)
    (source : Site4 n → Direction → Direction → Int) (number : Site4 n → Int)
    (the_equation : ∀ x this that, source x this that
      = the_curvature_of (the_gradient f) this that x + number x * the_metric_on_the_arms this that)
    (conserved : ∀ that x, (the_arms.map fun this => the_metric_on_the_arms this this
      * (source (the_step this x) this that - source x this that)).sum = 0)
    (that : Direction) (x : Site4 n) :
    the_difference that (fun y => number y + the_trace_of f y) x = 0 := by
  have h := conserved that x
  have d := the_divergence_of_the_curvature_is_the_difference_of_its_trace f that x
  obtain ⟨p, q⟩ := that
  cases p <;> cases q <;>
    simp [the_equation, the_divergence_of, the_difference, the_arms, the_metric_on_the_arms,
      the_arm_stores_a_fact_that_can_click] at h d ⊢ <;>
    omega

--| So the equation, whole: the source is the curvature, less its trace by the metric, and a number by the metric that is
--| the same at a site and at the next along every arm.
theorem the_equation_with_its_constant {n : Nat} (f : Site4 n → Int)
    (source : Site4 n → Direction → Direction → Int) (number : Site4 n → Int)
    (the_equation : ∀ x this that, source x this that
      = the_curvature_of (the_gradient f) this that x + number x * the_metric_on_the_arms this that)
    (conserved : ∀ that x, (the_arms.map fun this => the_metric_on_the_arms this this
      * (source (the_step this x) this that - source x this that)).sum = 0) :
    (∀ x this that, source x this that
        = the_curvature_of (the_gradient f) this that x - the_trace_of f x * the_metric_on_the_arms this that
          + (number x + the_trace_of f x) * the_metric_on_the_arms this that)
      ∧ (∀ way x, number (the_step way x) + the_trace_of f (the_step way x) = number x + the_trace_of f x) := by
  constructor
  · intro x this that; rw [the_equation, Int.add_mul]; omega
  · intro way x
    have h := the_number_and_the_trace_do_not_step f source number the_equation conserved way x
    simp only [the_difference] at h; omega
--| THE WHOLE ROUTE, ON THE TORUS.  A symmetric source at every site.  The curvature of an area.  For every observer, at every
--| site, the source and the curvature read the same along the null directions.  The source is conserved.  Then there is a
--| number at every site, the same at a site and at the next along every arm, with: the source is the curvature, less its
--| trace by the metric, and that number by the metric.
theorem the_field_equation_on_the_torus {n : Nat} (f : Site4 n → Int)
    (source : Site4 n → Direction → Direction → Int)
    (the_source_is_symmetric : ∀ x this that, source x this that = source x that this)
    (for_every_observer : ∀ x, ∀ direction ∈ the_null_directions,
      along (source x) direction = along (fun this that => the_curvature_of (the_gradient f) this that x) direction)
    (conserved : ∀ that x, (the_arms.map fun this => the_metric_on_the_arms this this
      * (source (the_step this x) this that - source x this that)).sum = 0) :
    ∃ constant : Site4 n → Int,
      (∀ way x, constant (the_step way x) = constant x)
        ∧ ∀ x this that, source x this that
            = the_curvature_of (the_gradient f) this that x - the_trace_of f x * the_metric_on_the_arms this that
              + constant x * the_metric_on_the_arms this that := by
  have the_equation := the_equation_on_the_torus source (fun x this that => the_curvature_of (the_gradient f) this that x)
    the_source_is_symmetric (fun x this that => the_table_of_a_gradient_is_symmetric f this that x) for_every_observer
  have both := the_equation_with_its_constant f source
    (fun x => the_number_left_free (source x) (fun this that => the_curvature_of (the_gradient f) this that x))
    the_equation conserved
  exact ⟨fun x => the_number_left_free (source x) (fun this that => the_curvature_of (the_gradient f) this that x)
    + the_trace_of f x, both.2, both.1⟩
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
theorem the_curvature_across_is_owed_when_a_pair_is_turned_over (table : Direction → Direction → Int) (a b c d : Direction) :
    the_curvature_across table b a c d = - the_curvature_across table a b c d
      ∧ the_curvature_across table a b d c = - the_curvature_across table a b c d := by
  simp only [the_curvature_across]; constructor <;> ac_nf <;> omega

theorem the_curvature_across_is_the_same_when_the_pairs_change_places (table : Direction → Direction → Int)
    (symmetric : ∀ this that, table this that = table that this) (a b c d : Direction) :
    the_curvature_across table c d a b = the_curvature_across table a b c d := by
  simp only [the_curvature_across, symmetric c a, symmetric d b, symmetric c b, symmetric d a]
  rw [Int.mul_comm (table b c)]

theorem the_curvature_across_around_three_is_nothing (table : Direction → Direction → Int)
    (symmetric : ∀ this that, table this that = table that this) (a b c d : Direction) :
    the_curvature_across table a b c d + the_curvature_across table a c d b + the_curvature_across table a d b c = 0 := by
  simp only [the_curvature_across, symmetric c b, symmetric d c, symmetric b d]; ac_nf; omega

--| THE CONTRACTION ACROSS THE INTERIOR.  Close the first seat of each pair on itself, by the signs of three and one.
def the_contraction_of (table : Direction → Direction → Int) (b d : Direction) : Int :=
  (the_arms.map fun a => the_metric_on_the_arms a a * the_curvature_across table a b a d).sum

--| On a square, for a table that holds a rise on each arm and nothing between: the two arms' rises, one by the other.
theorem a_squares_curvature_is_its_two_rises (rise : Direction → Int) (a b : Direction) (two_arms : a ≠ b) :
    the_curvature_across (fun this that => if this = that then rise this else 0) a b a b = rise a * rise b := by
  simp [the_curvature_across, two_arms, Ne.symm two_arms]

--| With what the arms store: a square on the arm that does not click is five by eighteen, the momentum squared; a square
--| between two that click is eighteen by eighteen.
theorem the_squares_of_the_source :
    the_curvature_across the_source_on_the_arms (true, false) (true, true) (true, false) (true, true) = 90
      ∧ the_curvature_across the_source_on_the_arms (true, true) (false, true) (true, true) (false, true) = 324 := by decide

--| With one fencepost on every arm: three on the arm that does not click, one on each that does, nothing between.  Three
--| squares meet at an arm; on the arm out all three count, on the others the one that crosses it counts against the two
--| that do not.
theorem the_contraction_of_one_fencepost_is_three_and_three_ones :
    ∀ b ∈ the_arms, ∀ d ∈ the_arms,
      the_contraction_of (the_curvature_on_the_count 1) b d
        = if b = d then (if b = (true, false) then 3 else 1) else 0 := by decide

--| With the metric itself, as on a round surface: three times the metric.
theorem the_contraction_of_the_metric_is_three_metrics :
    ∀ b ∈ the_arms, ∀ d ∈ the_arms,
      the_contraction_of the_metric_on_the_arms b d = 3 * the_metric_on_the_arms b d := by decide

--| Against the source, along the null directions: four times the source reads as twenty-three of the contraction of one
--| fencepost.  Another area, another constant.
theorem four_sources_read_as_twenty_three_contractions :
    ∀ direction ∈ the_null_directions,
      4 * along the_source_on_the_arms direction = 23 * along (the_contraction_of (the_curvature_on_the_count 1)) direction := by
  decide
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
open «springer-verlag» THE_GOSPEL the_representation assembly_instructions readers_experience the_area
attribute [local instance high] rung01 rung02 rung03 rung04 rung05 rung06 rung07 rung08 rung09 rung10 rung11 rung12 rung13 rung14 rung15
  rung16 rung17 rung18 rung19 rung20 rung21 rung22 rung23 rung24 rung25 rung26 rung27 rung28 rung29 rung32 rung33 rung34 rung35 a_truth_about_the_experience

--| The three processes, as the first three rungs hold them: the card, its counting, its indexing.
noncomputable def the_counting : CountingProcess FACT the_first_card := ADMISSIBLE.counting_process
noncomputable def the_indexing : IndexingProcess FACT the_first_card := COUNTABLE.index

--| THE CARRIER'S TWO.  The card's step, done twice, is the step done once, on every number.  It never reaches a second
--| thing.  That there are two is not something the step gives.
theorem the_carriers_step_twice_is_once (number : Number) :
    the_first_card.interact_with_the_universe (the_first_card.interact_with_the_universe number)
      = the_first_card.interact_with_the_universe number := by cases number <;> rfl
def the_carriers_two : FACT :=
  { truth := ∀ number : Number, the_first_card.interact_with_the_universe (the_first_card.interact_with_the_universe number)
      = the_first_card.interact_with_the_universe number
    click := .isTrue the_carriers_step_twice_is_once }

--| THE COUNTER'S TWO.  The counting step takes any number to the number on the count it keeps: the count, and one more.
theorem the_counters_step_is_the_count_and_one_more (fact : FACT) (label : Number) (so_far : Natural) :
    ∃ (the_fact : FACT), the_counting.iterate (Natural.number fact label so_far)
      = Natural.number the_fact the_counting.palmed_card.quarter the_counting.count := ⟨_, rfl⟩
def the_counters_two : FACT :=
  { truth := ∀ (fact : FACT) (label : Number) (so_far : Natural), ∃ (the_fact : FACT),
      the_counting.iterate (Natural.number fact label so_far)
        = Natural.number the_fact the_counting.palmed_card.quarter the_counting.count
    click := .isTrue the_counters_step_is_the_count_and_one_more }

--| THE INDEXER'S TWO.  The indexing step takes a zero to the first on the count, and a number at an index to the number at
--| the counting step of that index, on the same origin.
theorem the_indexers_step_is_the_first_or_the_next (fact : FACT) (index : Natural) (rest : Rational) :
    the_indexing.iterate (Rational.zero fact) = Rational.number fact the_indexing.count.count the_indexing.origin
      ∧ the_indexing.iterate (Rational.number fact index rest)
          = Rational.number fact (the_indexing.count.iterate index) the_indexing.origin := ⟨rfl, rfl⟩
def the_indexers_two : FACT :=
  { truth := ∀ (fact : FACT) (index : Natural) (rest : Rational),
      the_indexing.iterate (Rational.zero fact) = Rational.number fact the_indexing.count.count the_indexing.origin
        ∧ the_indexing.iterate (Rational.number fact index rest)
            = Rational.number fact (the_indexing.count.iterate index) the_indexing.origin
    click := .isTrue the_indexers_step_is_the_first_or_the_next }

--| Each a zero of Bullshit, on its fact.
def the_inferred_two : Bullshit.{0,0,0,0} := .zero the_carriers_two
def the_counted_two : Bullshit.{0,0,0,0} := .zero the_counters_two
def the_indexed_two : Bullshit.{0,0,0,0} := .zero the_indexers_two

--| THE EQUIVALENCE PROCESS.  The knower is the knower of the experience.  The conclusion is the inferred two against the
--| counted one.
noncomputable def the_equivalence_of_the_twos :=
  { the_knower_of_the_experience.same_difference with
    your_conclusion := .different the_first_card.symbol the_inferred_two the_counted_two (some the_carriers_two.truth) }

--| Asked to believe the inferred two against each of the machine's.  Twelve of its universes are free, and are pinned at
--| nothing, as the device pins them.
noncomputable def the_inferred_against_the_counted : Closure :=
  the_equivalence_of_the_twos.{0,0,0,0,0,0,0,0,0,0,0,0}.do_you_believe_it? the_inferred_two the_counted_two
noncomputable def the_inferred_against_the_indexed : Closure :=
  the_equivalence_of_the_twos.{0,0,0,0,0,0,0,0,0,0,0,0}.do_you_believe_it? the_inferred_two the_indexed_two

--| Each closure is one cell, and the conclusion is one cell: three cells for three twos.
theorem three_twos_three_cells :
    the_equivalence_of_the_twos.{0,0,0,0,0,0,0,0,0,0,0,0}.your_conclusion.infer.length = 1
      ∧ the_inferred_against_the_counted.infer.length = 1
      ∧ the_inferred_against_the_indexed.infer.length = 1 := ⟨rfl, rfl, rfl⟩

--| All three click.
theorem the_three_twos_click :
    the_carriers_two.truth ∧ the_counters_two.truth ∧ the_indexers_two.truth :=
  ⟨the_carriers_step_twice_is_once, the_counters_step_is_the_count_and_one_more, the_indexers_step_is_the_first_or_the_next⟩
end three_twos

section the_difference_of_a_product

--| THE REMAINDER.  The difference of a product, on the torus: the first by the difference of the second, the second by the
--| difference of the first, and one thing more, the two differences one by the other.  That last is the whole of what the
--| rule for a product lacks here, and it is of the second degree in the step.  That it adds up to nothing is the inference.
theorem the_difference_of_a_product {n : Nat} (f g : Site4 n → Int) (way : Direction) (x : Site4 n) :
    the_difference way (fun y => f y * g y) x
      = f x * the_difference way g x + g x * the_difference way f x + the_difference way f x * the_difference way g x := by
  simp only [the_difference, Int.mul_sub, Int.sub_mul]; ac_nf; omega
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
open «springer-verlag» THE_GOSPEL the_representation assembly_instructions readers_experience the_area
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
theorem the_carrier_process_is_the_one_held : the_carrier_process = the_carrier_process_held := rfl
noncomputable def the_counting_process : type_of% the_counting_process_held :=
  { palmed_card := the_carrier_process
    count := the_counting_process_held.count }
theorem the_counting_process_is_the_one_held : the_counting_process = the_counting_process_held := rfl
noncomputable def the_indexing_process : type_of% the_indexing_process_held :=
  { count := the_counting_process
    origin := the_indexing_process_held.origin }
theorem the_indexing_process_is_the_one_held : the_indexing_process = the_indexing_process_held := rfl
noncomputable def the_limit_process : type_of% the_limit_process_held :=
  { indexing_process := the_indexing_process
    limit := the_limit_process_held.limit
    sequence := the_limit_process_held.sequence }
theorem the_limit_process_is_the_one_held : the_limit_process = the_limit_process_held := rfl
noncomputable def the_cauchy_process : type_of% the_cauchy_process_held :=
  { limit_process := the_limit_process
    value := the_cauchy_process_held.value
    accumulation := the_cauchy_process_held.accumulation }
theorem the_cauchy_process_is_the_one_held : the_cauchy_process = the_cauchy_process_held := rfl
noncomputable def the_observation_process : type_of% the_observation_process_held :=
  { cauchy_process := the_cauchy_process
    before := the_observation_process_held.before
    after := the_observation_process_held.after }
theorem the_observation_process_is_the_one_held : the_observation_process = the_observation_process_held := rfl
noncomputable def the_repeatable_process : type_of% the_repeatable_process_held :=
  { observation_process := the_observation_process
    stimulus := the_repeatable_process_held.stimulus
    expectation := the_repeatable_process_held.expectation }
theorem the_repeatable_process_is_the_one_held : the_repeatable_process = the_repeatable_process_held := rfl
noncomputable def the_computational_process : type_of% the_computational_process_held :=
  { repeatable_process := the_repeatable_process
    output := the_computational_process_held.output
    error_code := the_computational_process_held.error_code
    close := the_computational_process_held.close
    closure := the_computational_process_held.closure }
theorem the_computational_process_is_the_one_held : the_computational_process = the_computational_process_held := rfl
noncomputable def the_turing_process : type_of% the_turing_process_held :=
  { computational_process := the_computational_process
    program := the_turing_process_held.program
    state := the_turing_process_held.state }
theorem the_turing_process_is_the_one_held : the_turing_process = the_turing_process_held := rfl
noncomputable def the_noisy_process : type_of% the_noisy_process_held :=
  { turing_process := the_turing_process
    program := the_noisy_process_held.program }
theorem the_noisy_process_is_the_one_held : the_noisy_process = the_noisy_process_held := rfl
noncomputable def the_physical_process : type_of% the_physical_process_held :=
  { noisy_process := the_noisy_process
    representation := the_physical_process_held.representation
    invariant := the_physical_process_held.invariant
    value := the_physical_process_held.value }
theorem the_physical_process_is_the_one_held : the_physical_process = the_physical_process_held := rfl
noncomputable def the_slip_process : type_of% the_slip_process_held :=
  { physical_process := the_physical_process
    projection := the_slip_process_held.projection
    stress := the_slip_process_held.stress
    threshold := the_slip_process_held.threshold }
theorem the_slip_process_is_the_one_held : the_slip_process = the_slip_process_held := rfl
noncomputable def the_sensing_process : type_of% the_sensing_process_held :=
  { static_fraction := the_slip_process
    accumulation := the_sensing_process_held.accumulation }
theorem the_sensing_process_is_the_one_held : the_sensing_process = the_sensing_process_held := rfl
noncomputable def the_gauge_process : type_of% the_gauge_process_held :=
  { sensing_process := the_sensing_process
    clock := the_gauge_process_held.clock }
theorem the_gauge_process_is_the_one_held : the_gauge_process = the_gauge_process_held := rfl
noncomputable def the_meesa_process : type_of% the_meesa_process_held :=
  { gauge_process := the_gauge_process
    concept := the_meesa_process_held.concept }
theorem the_meesa_process_is_the_one_held : the_meesa_process = the_meesa_process_held := rfl
noncomputable def the_digital_process : type_of% the_digital_process_held :=
  { meesa_process := the_meesa_process
    zero := the_digital_process_held.zero }
theorem the_digital_process_is_the_one_held : the_digital_process = the_digital_process_held := rfl
noncomputable def the_compiled_process : type_of% the_compiled_process_held :=
  { digital_process := the_digital_process
    source := the_compiled_process_held.source
    opcodes := the_compiled_process_held.opcodes }
theorem the_compiled_process_is_the_one_held : the_compiled_process = the_compiled_process_held := rfl
noncomputable def the_mathematical_process : type_of% the_mathematical_process_held :=
  { compiled_process := the_compiled_process
    mapping := the_mathematical_process_held.mapping }
theorem the_mathematical_process_is_the_one_held : the_mathematical_process = the_mathematical_process_held := rfl
noncomputable def the_adding_process : type_of% the_adding_process_held :=
  { mideastern_process := the_mathematical_process
    plus := the_adding_process_held.plus
    sum := the_adding_process_held.sum }
theorem the_adding_process_is_the_one_held : the_adding_process = the_adding_process_held := rfl
noncomputable def the_multiplying_process : type_of% the_multiplying_process_held :=
  { adding_process := the_adding_process
    total := the_multiplying_process_held.total
    product := the_multiplying_process_held.product }
theorem the_multiplying_process_is_the_one_held : the_multiplying_process = the_multiplying_process_held := rfl
noncomputable def the_basic_process : type_of% the_basic_process_held :=
  { GOSUB := the_multiplying_process
    TEN := the_basic_process_held.TEN
    span := the_basic_process_held.span }
theorem the_basic_process_is_the_one_held : the_basic_process = the_basic_process_held := rfl
noncomputable def the_jordan_process : type_of% the_jordan_process_held :=
  { ANSYS_process := the_basic_process
    polynomial := the_jordan_process_held.polynomial }
theorem the_jordan_process_is_the_one_held : the_jordan_process = the_jordan_process_held := rfl
noncomputable def the_arm_wave_process : type_of% the_arm_wave_process_held :=
  { dunking_contest := the_jordan_process
    guess := the_arm_wave_process_held.guess }
theorem the_arm_wave_process_is_the_one_held : the_arm_wave_process = the_arm_wave_process_held := rfl
noncomputable def the_crusade_process : type_of% the_crusade_process_held :=
  { to_pwn_n00bz := the_arm_wave_process
    religious_dogma := the_crusade_process_held.religious_dogma }
theorem the_crusade_process_is_the_one_held : the_crusade_process = the_crusade_process_held := rfl
noncomputable def the_initiation_process : type_of% the_initiation_process_held :=
  { axioms := the_crusade_process
    sacred_texts := the_initiation_process_held.sacred_texts }
theorem the_initiation_process_is_the_one_held : the_initiation_process = the_initiation_process_held := rfl
noncomputable def the_learning_process : type_of% the_learning_process_held :=
  { teaching := the_initiation_process
    galileo := the_learning_process_held.galileo
    invariant := the_learning_process_held.invariant }
theorem the_learning_process_is_the_one_held : the_learning_process = the_learning_process_held := rfl
noncomputable def the_scientific_process : type_of% the_scientific_process_held :=
  { shows_me_higher_order_terms := the_learning_process
    knowledge := the_scientific_process_held.knowledge }
theorem the_scientific_process_is_the_one_held : the_scientific_process = the_scientific_process_held := rfl
noncomputable def the_religious_process : type_of% the_religious_process_held :=
  { we_experience := the_scientific_process
    in_the_literature := the_religious_process_held.in_the_literature }
theorem the_religious_process_is_the_one_held : the_religious_process = the_religious_process_held := rfl
noncomputable def the_universe_tensor : type_of% the_universe_tensor_held :=
  { frame_of_reference := the_religious_process
    in_reality := the_universe_tensor_held.in_reality }
theorem the_universe_tensor_is_the_one_held : the_universe_tensor = the_universe_tensor_held := rfl
noncomputable def the_big_red_dog_process : type_of% the_big_red_dog_process_held :=
  { the_æther := the_universe_tensor
    Du := the_big_red_dog_process_held.Du }
theorem the_big_red_dog_process_is_the_one_held : the_big_red_dog_process = the_big_red_dog_process_held := rfl
noncomputable def the_calculus_process : type_of% the_calculus_process_held :=
  { the_local_schedule := the_big_red_dog_process
    the_direction_to_the_destination := the_calculus_process_held.the_direction_to_the_destination
    uptown_or_downtown := the_calculus_process_held.uptown_or_downtown
    the_train_in := the_calculus_process_held.the_train_in }
theorem the_calculus_process_is_the_one_held : the_calculus_process = the_calculus_process_held := rfl
noncomputable def the_heartbeat_process : type_of% the_heartbeat_process_held :=
  { bullshit_meter := the_calculus_process
    after_some_time := the_heartbeat_process_held.after_some_time
    according_to_newton := the_heartbeat_process_held.according_to_newton }
theorem the_heartbeat_process_is_the_one_held : the_heartbeat_process = the_heartbeat_process_held := rfl
noncomputable def the_elaboration_process : type_of% the_elaboration_process_held :=
  { stamina := the_heartbeat_process
    trilinos := the_elaboration_process_held.trilinos
    numerical_analysis := the_elaboration_process_held.numerical_analysis }
theorem the_elaboration_process_is_the_one_held : the_elaboration_process = the_elaboration_process_held := rfl
noncomputable def the_lean_process : type_of% the_lean_process_held :=
  { description := the_elaboration_process
    the_measurement_of := the_lean_process_held.the_measurement_of
    in_heartbeats := the_lean_process_held.in_heartbeats
    saved_as_y := the_lean_process_held.saved_as_y }
theorem the_lean_process_is_the_one_held : the_lean_process = the_lean_process_held := rfl
noncomputable def the_compiler_output : type_of% the_compiler_output_held :=
  { too_good_to_be_true := the_lean_process
    of_jibberish := the_compiler_output_held.of_jibberish }
theorem the_compiler_output_is_the_one_held : the_compiler_output = the_compiler_output_held := rfl
noncomputable def the_atreyu_process : type_of% the_atreyu_process_held :=
  { in_a_giant_book := the_compiler_output
    a_constant := the_atreyu_process_held.a_constant
    current_page_number := the_atreyu_process_held.current_page_number
    of_the_proof := the_atreyu_process_held.of_the_proof }
theorem the_atreyu_process_is_the_one_held : the_atreyu_process = the_atreyu_process_held := rfl
noncomputable def the_equivalence_process : type_of% the_equivalence_process_held :=
  { you_the_knower := the_atreyu_process
    your_conclusion := the_equivalence_process_held.your_conclusion }
theorem the_equivalence_process_is_the_one_held : the_equivalence_process = the_equivalence_process_held := rfl
--| THE BOTTOM THREE, WRITTEN OUT.  What the card, the counting and the indexing carry is each a one on a zero: the second
--| thing of its kind.  The card under all of them is not the first card.  It is the palmed card, and its quarter is two
--| cells.
theorem the_card_at_the_bottom_is_the_palmed_card_and_its_quarter_is_one_on_a_zero :
    the_carrier_process.quarter = Number.one FACT.Truth (Number.zero FACT.Truth)
      ∧ the_carrier_process.quarter.peano.length = 2
      ∧ the_first_card.quarter.peano.length = 1 := ⟨rfl, rfl, rfl⟩
theorem the_count_is_one_on_a_zero :
    the_counting_process.count = Natural.number FACT.Truth the_first_card.quarter (Natural.zero FACT.Truth) := rfl
theorem the_origin_is_one_on_a_zero :
    the_indexing_process.origin = Rational.number FACT.Truth the_counting_process.count (Rational.zero FACT.Truth) := rfl

--| The palmed card's step does reach the next thing: a one goes to a one on the palmed quarter, three cells.  And done twice
--| it is still the step done once.
theorem the_palmed_cards_step_reaches_three_cells (fact : FACT) (rest : Number) :
    (the_carrier_process.interact_with_the_universe (Number.one fact rest)).peano.length = 3 := rfl
theorem the_palmed_cards_step_twice_is_once (number : Number) :
    the_carrier_process.interact_with_the_universe (the_carrier_process.interact_with_the_universe number)
      = the_carrier_process.interact_with_the_universe number := by cases number <;> rfl

--| THE ONE STEP WRITTEN BY HAND.  Thirty-six of the thirty-seven steps are the device's own.  One is not: the closure of the
--| computational process, which Episode 9 wrote over, and wrote as leaving a study as it is.
theorem the_one_step_written_by_hand_leaves_a_study_as_it_is (study : Study) :
    the_computational_process.closure study = study := rfl

--| THE EQUIVALENCE OF THE TWOS, CONSTRUCTED.  The same process as before, now on the knower that was built from the card up.
noncomputable def the_equivalence_of_the_twos_constructed : type_of% the_equivalence_process_held :=
  { you_the_knower := the_atreyu_process
    your_conclusion := .different the_first_card.symbol the_inferred_two the_counted_two (some the_carriers_two.truth) }
theorem the_equivalence_constructed_is_the_equivalence_of_the_twos :
    the_equivalence_of_the_twos_constructed = the_equivalence_of_the_twos.{0,0,0,0,0,0,0,0,0,0,0,0} := rfl
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
open «springer-verlag» THE_GOSPEL the_representation assembly_instructions readers_experience the_area
attribute [local instance high] rung01 rung02 rung03 rung04 rung05 rung06 rung07 rung08 rung09 rung10 rung11 rung12 rung13 rung14 rung15
  rung16 rung17 rung18 rung19 rung20 rung21 rung22 rung23 rung24 rung25 rung26 rung27 rung28 rung29 rung32 rung33 rung34 rung35 a_truth_about_the_experience

--| THE SEAM.  The author's, 18 November 2026: the one step written by hand, the closure of the computational process, is
--| the seam where the proof comes together (declared).  Here is the same process with the step left to the device, as the
--| other thirty-six are.
noncomputable def the_computational_process_left_to_the_device : type_of% the_computational_process_held :=
  { repeatable_process := the_repeatable_process
    output := the_computational_process_held.output }

--| Left to the device, the closure never leaves a hypothesis as it is: it writes it into a book of records, and a book is
--| not a hypothesis.  Written by hand, it leaves every study as it is.  One goes on; the other has stopped.
theorem left_to_the_device_a_hypothesis_is_never_left_as_it_is (fact : FACT) :
    the_computational_process_left_to_the_device.closure (Study.hypothesis fact) ≠ Study.hypothesis fact := by
  intro h; cases h
theorem written_by_hand_a_hypothesis_is_left_as_it_is (fact : FACT) :
    the_computational_process.closure (Study.hypothesis fact) = Study.hypothesis fact := rfl

--| So the two are not one process, and they differ in nothing but that step: what they hold and what they carry are the same.
theorem the_seam_is_the_closure_and_nothing_else :
    the_computational_process_left_to_the_device ≠ the_computational_process
      ∧ the_computational_process_left_to_the_device.repeatable_process = the_computational_process.repeatable_process
      ∧ the_computational_process_left_to_the_device.output = the_computational_process.output
      ∧ the_computational_process_left_to_the_device.error_code = the_computational_process.error_code
      ∧ the_computational_process_left_to_the_device.close = the_computational_process.close := by
  refine ⟨fun same => ?_, rfl, rfl, rfl, rfl⟩
  exact left_to_the_device_a_hypothesis_is_never_left_as_it_is FACT.Truth
    (by rw [same]; exact written_by_hand_a_hypothesis_is_left_as_it_is FACT.Truth)
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
def the_table_taken_from_the_same (N D : Int) : Table :=
  fun a b => the_scaled_identity (13 * N) a b - D * the_full_table a b
def the_residual_of_the_pair (N D : Int) : Int := 13 * (N * N) - 36 * (N * D) + 18 * (D * D)

theorem two_by_two_is_one_by_one_twice (a b c d : Int) : a * b * (c * d) = a * c * (b * d) := by ac_nf

theorem what_the_table_taken_from_the_same_holds (N D : Int) :
    the_table_taken_from_the_same N D true true = 13 * N - 18 * D
      ∧ the_table_taken_from_the_same N D false false = 13 * N - 18 * D
      ∧ the_table_taken_from_the_same N D true false = - (5 * D)
      ∧ the_table_taken_from_the_same N D false true = - (18 * D) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · show 13 * N - D * 18 = 13 * N - 18 * D; omega
  · show 13 * N - D * 18 = 13 * N - 18 * D; omega
  · show 0 - D * 5 = - (5 * D); omega
  · show 0 - D * 18 = - (18 * D); omega

theorem its_adjugate_is_the_same_shape_with_the_trace_taken_off (N D : Int) (a b : Bool) :
    the_adjugate (the_table_taken_from_the_same N D) a b
      = the_scaled_identity (13 * N - 36 * D) a b + D * the_full_table a b := by
  obtain ⟨h1, h2, h3, h4⟩ := what_the_table_taken_from_the_same_holds N D
  cases a <;> cases b
  · show the_table_taken_from_the_same N D true true = 13 * N - 36 * D + D * 18; rw [h1]; omega
  · show - the_table_taken_from_the_same N D false true = 0 + D * 18; rw [h4]; omega
  · show - the_table_taken_from_the_same N D true false = 0 + D * 5; rw [h3]; omega
  · show the_table_taken_from_the_same N D false false = 13 * N - 36 * D + D * 18; rw [h2]; omega

theorem the_trace_of_its_adjugate_is_the_slope (N D : Int) :
    the_table_trace (the_adjugate (the_table_taken_from_the_same N D)) = 26 * N - 36 * D := by
  obtain ⟨h1, h2, _, _⟩ := what_the_table_taken_from_the_same_holds N D
  show the_table_taken_from_the_same N D false false + the_table_taken_from_the_same N D true true = 26 * N - 36 * D
  rw [h1, h2]; omega

theorem its_determinant_is_thirteen_residuals (N D : Int) :
    the_table_determinant (the_table_taken_from_the_same N D) = 13 * the_residual_of_the_pair N D := by
  obtain ⟨h1, h2, h3, h4⟩ := what_the_table_taken_from_the_same_holds N D
  simp only [the_table_determinant, the_residual_of_the_pair, h1, h2, h3, h4, Int.sub_mul, Int.mul_sub, Int.neg_mul_neg]
  have e1 : 13 * N * (13 * N) = 13 * 13 * (N * N) := two_by_two_is_one_by_one_twice 13 N 13 N
  have e2 : 18 * D * (13 * N) = 18 * 13 * (N * D) := by rw [two_by_two_is_one_by_one_twice, Int.mul_comm D N]
  have e3 : 13 * N * (18 * D) = 13 * 18 * (N * D) := two_by_two_is_one_by_one_twice 13 N 18 D
  have e4 : 18 * D * (18 * D) = 18 * 18 * (D * D) := two_by_two_is_one_by_one_twice 18 D 18 D
  have e5 : 5 * D * (18 * D) = 5 * 18 * (D * D) := two_by_two_is_one_by_one_twice 5 D 18 D
  rw [e1, e2, e3, e4, e5]; omega

--| So the table by its adjugate is thirteen residuals on the diagonal and nothing off it.
theorem the_table_by_its_adjugate_is_thirteen_residuals_of_the_same (N D : Int) (a b : Bool) :
    the_table_product (the_table_taken_from_the_same N D) (the_adjugate (the_table_taken_from_the_same N D)) a b
      = the_scaled_identity (13 * the_residual_of_the_pair N D) a b := by
  rw [the_adjugate_inverts, its_determinant_is_thirteen_residuals]; rfl

--| THE CRANK.  One turn takes a pair to thirteen of the first squared less eighteen of the second squared, over twenty-six
--| of the two less thirty-six of the second squared.  That is the first by the trace less the residual, over the second by
--| the trace: the place, less the determinant over thirteen traces.  The crank reads the trace of the inverse, turned over.
theorem the_crank_is_the_place_less_the_residual_over_the_trace (N D : Int) :
    N * the_table_trace (the_adjugate (the_table_taken_from_the_same N D)) - the_residual_of_the_pair N D
        = 13 * (N * N) - 18 * (D * D)
      ∧ D * the_table_trace (the_adjugate (the_table_taken_from_the_same N D)) = 26 * (N * D) - 36 * (D * D) := by
  rw [the_trace_of_its_adjugate_is_the_slope]
  simp only [the_residual_of_the_pair, Int.mul_sub]
  have e1 : N * (26 * N) = 26 * (N * N) := Int.mul_left_comm N 26 N
  have e2 : N * (36 * D) = 36 * (N * D) := Int.mul_left_comm N 36 D
  have e3 : D * (26 * N) = 26 * (N * D) := by rw [Int.mul_left_comm, Int.mul_comm D N]
  have e4 : D * (36 * D) = 36 * (D * D) := Int.mul_left_comm D 36 D
  rw [e1, e2, e3, e4]; constructor <;> omega

--| At a root the residual is nothing, so the table by its adjugate is nothing: there is no inverse to read there.  The
--| crank's step is then nothing, and it stays.
theorem where_the_residual_is_nothing_there_is_no_inverse (N D : Int) (root : the_residual_of_the_pair N D = 0) (a b : Bool) :
    the_table_product (the_table_taken_from_the_same N D) (the_adjugate (the_table_taken_from_the_same N D)) a b = 0 := by
  rw [the_table_by_its_adjugate_is_thirteen_residuals_of_the_same, root]
  cases a <;> cases b <;> rfl
end the_crank_reads_the_inverse
section the_weighted_action
open readers_experience

--| THE WEIGHTED ACTION.  The table is not the same turned over.  Episode 12 has that it is reversible: weigh each row by its
--| coin, eighteen and five, and it is.  So is the table taken from the same, for every pair.  A table that is the same turned
--| over has an action that varies by the table twice, Episode 12 again.  So the table the crank reads the inverse of is the
--| second variation of an action, in the pairing of the two coins.
def weighed_by_its_coin (table : Table) : Table := fun a b => (the_coin_weight a : Int) * table a b

theorem the_table_weighed_is_the_same_turned_over :
    weighed_by_its_coin the_full_table true false = weighed_by_its_coin the_full_table false true
      ∧ weighed_by_its_coin the_full_table true false = 90 := ⟨rfl, rfl⟩

theorem the_table_taken_from_the_same_weighed_is_the_same_turned_over (N D : Int) :
    weighed_by_its_coin (the_table_taken_from_the_same N D) true false
      = weighed_by_its_coin (the_table_taken_from_the_same N D) false true := by
  obtain ⟨_, _, h3, h4⟩ := what_the_table_taken_from_the_same_holds N D
  show (18 : Int) * the_table_taken_from_the_same N D true false = 5 * the_table_taken_from_the_same N D false true
  rw [h3, h4]; omega

theorem the_weighted_action_varies_by_the_table_twice (N D : Int) (v h : Bool → Int) :
    the_action_of (weighed_by_its_coin (the_table_taken_from_the_same N D)) (fun y => v y + h y)
        - the_action_of (weighed_by_its_coin (the_table_taken_from_the_same N D)) v
      = (h true * the_refine (weighed_by_its_coin (the_table_taken_from_the_same N D)) v true
          + h false * the_refine (weighed_by_its_coin (the_table_taken_from_the_same N D)) v false)
        + (h true * the_refine (weighed_by_its_coin (the_table_taken_from_the_same N D)) v true
          + h false * the_refine (weighed_by_its_coin (the_table_taken_from_the_same N D)) v false)
        + the_action_of (weighed_by_its_coin (the_table_taken_from_the_same N D)) h :=
  the_action_varies_by_the_operator_twice _ (the_table_taken_from_the_same_weighed_is_the_same_turned_over N D) v h
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
open «springer-verlag» THE_GOSPEL the_representation assembly_instructions readers_experience the_area
attribute [local instance high] rung01 rung02 rung03 rung04 rung05 rung06 rung07 rung08 rung09 rung10 rung11 rung12 rung13 rung14 rung15
  rung16 rung17 rung18 rung19 rung20 rung21 rung22 rung23 rung24 rung25 rung26 rung27 rung28 rung29 rung32 rung33 rung34 rung35 a_truth_about_the_experience

--| THE FOUR PLACES OF A TRIAL.  The author's, 18 November 2026: a sample lets you hold a bracket, and a trial gives you two
--| brackets to hold; see, the frinkahedron (declared).  A sample is one limit, or two limits each with its fact: a bracket.
--| A trial that has a response holds two samples.
def holds_a_bracket : Sample → Bool
  | .initial_condition _ _ => false
  | .signal_response _ _ _ _ _ => true
def the_limits_held : Sample → Nat
  | .initial_condition _ _ => 1
  | .signal_response _ _ _ _ _ => 2
def the_place_of (first second : Sample) : Direction := (holds_a_bracket first, holds_a_bracket second)

--| One limit, and a bracket, on the truth.
def one_limit : Sample := .initial_condition FACT.Truth (.nil FACT.Truth)
def a_bracket : Sample := .signal_response FACT.Truth (.nil FACT.Truth) FACT.Truth (.nil FACT.Truth) one_limit

--| Four places, and every one is reached.
theorem a_trial_has_four_places :
    [the_place_of a_bracket a_bracket, the_place_of a_bracket one_limit, the_place_of one_limit a_bracket,
      the_place_of one_limit one_limit] = the_arms := rfl

--| A bracket holds two limits, and two brackets hold four.
theorem a_bracket_holds_two_and_two_brackets_hold_four :
    the_limits_held a_bracket = 2 ∧ the_limits_held one_limit = 1
      ∧ the_limits_held a_bracket + the_limits_held a_bracket = 4 := ⟨rfl, rfl, rfl⟩

--| ON THE FRINKAHEDRON.  The geometric card: a point of the product of the two hexagons has each coordinate inside or on the
--| edge, four places; the frinkahedron is the three where some coordinate is on the edge.  A place of a trial is on it when
--| some sample holds a bracket.  Three are, and one is not.
def on_the_frinkahedron (place : Direction) : Bool := place.1 || place.2

theorem three_places_are_on_the_frinkahedron_and_one_is_not :
    the_arms.map on_the_frinkahedron = [true, true, true, false] := rfl

--| Three and one, as the arms: the place is on the frinkahedron exactly when the arm with its first coin turned over can
--| click.  Which coin is the one turned over is not the device's to say.
theorem on_the_frinkahedron_is_the_click_with_the_first_coin_turned_over (first second : Bool) :
    on_the_frinkahedron (first, second) = the_arm_stores_a_fact_that_can_click (!first) second := by
  cases first <;> cases second <;> rfl

--| ON THE DEVICE'S OWN OBJECTS.  What the observation process is handed is a bracket, and so is what the repeatable process
--| carries for its stimulus.
theorem the_devices_bit_and_stimulus_are_brackets :
    holds_a_bracket (BINARY.bit (Value := FACT) (Carrier := the_first_card)) = true
      ∧ holds_a_bracket the_repeatable_process.stimulus = true := ⟨rfl, rfl⟩
--| And the trial the repeatable process makes at its first step, from what it expects, holds two brackets: it is at the seam.
def the_place_of_a_trial : Trial → Option Direction
  | .hypothesis _ _ => none
  | .signal_response _ first _ second _ => some (the_place_of first second)
theorem the_devices_first_trial_is_at_the_seam :
    the_place_of_a_trial the_repeatable_process.expectation = none
      ∧ the_place_of_a_trial (the_repeatable_process.iterate the_repeatable_process.expectation) = some (true, true) :=
  ⟨rfl, rfl⟩
end the_four_places_of_a_trial

--#print axioms a_trial_has_four_places
--#print axioms three_places_are_on_the_frinkahedron_and_one_is_not
--#print axioms on_the_frinkahedron_is_the_click_with_the_first_coin_turned_over
--#print axioms the_devices_bit_and_stimulus_are_brackets
--#print axioms the_devices_first_trial_is_at_the_seam

section twos_carried_and_threes_reached
open «springer-verlag» THE_GOSPEL the_representation assembly_instructions readers_experience the_area
attribute [local instance high] rung01 rung02 rung03 rung04 rung05 rung06 rung07 rung08 rung09 rung10 rung11 rung12 rung13 rung14 rung15
  rung16 rung17 rung18 rung19 rung20 rung21 rung22 rung23 rung24 rung25 rung26 rung27 rung28 rung29 rung32 rung33 rung34 rung35 a_truth_about_the_experience

--| TWOS CARRIED, THREES REACHED.  Read by Episode 8's readers, what each of the bottom processes carries is two cells.
theorem what_the_bottom_processes_carry_is_two_cells :
    the_carrier_process.quarter.peano.length = 2
      ∧ the_counting_process.count.induct.length = 2
      ∧ the_indexing_process.origin.diagonalize.length = 2
      ∧ the_limit_process.limit.diagonalize.length = 2
      ∧ the_limit_process.sequence.enumerate.length = 2
      ∧ the_cauchy_process.accumulation.converge.length = 2
      ∧ the_observation_process.before.converge.length = 2 := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

--| One step of each, on what it carries, is three cells.  Three is what is approached.
theorem one_step_of_each_reaches_three_cells :
    (the_counting_process.iterate the_counting_process.count).induct.length = 3
      ∧ (the_indexing_process.iterate the_indexing_process.origin).diagonalize.length = 3
      ∧ (the_limit_process.iterate the_limit_process.sequence).enumerate.length = 3
      ∧ (the_cauchy_process.iterate the_cauchy_process.accumulation).converge.length = 3
      ∧ the_cauchy_process.value.diagonalize.length = 3
      ∧ the_observation_process.after.converge.length = 3 := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

--| The bit is three cells, and the observation's step on it is five: two facts a step.
theorem the_observations_step_on_the_bit_is_five_cells :
    (BINARY.bit (Value := FACT) (Carrier := the_first_card)).taste.length = 3
      ∧ (the_observation_process.iterate (BINARY.bit (Value := FACT) (Carrier := the_first_card))).taste.length = 5 :=
  ⟨rfl, rfl⟩
end twos_carried_and_threes_reached

section the_experience_and_the_law
open readers_experience the_area

--| THE EXPERIENCE AND THE LAW.  The author's, 18 November 2026: a measurement is the experience, and a preprint is the
--| mathematical law that appears to coincide with it (declared).  Deal one tape into each, as Episode 13 deals every
--| inductive, and read them back.  The law reads the experience and one cell more.  They coincide but for the fencepost.
theorem the_law_reads_the_experience_and_the_fencepost (tape : List FACT) :
    (the_preprint_a_list_indicates tape).the_model.length
      = (the_measurement_a_list_indicates tape).the_reading.length + the_fencepost_bug := by
  rw [the_preprint_reads_back, the_measurement_reads_back]; show 1 * tape.length + 1 = 1 * tape.length + 0 + 1; omega
end the_experience_and_the_law

section one_turn_from_the_mass

--| ONE TURN FROM THE MASS.  Energy squared is mass squared and momentum squared.  One turn of Newton's crank for that root,
--| begun at the mass, lands on the mass and the momentum squared over twice the mass.  Squared, and cleared of the
--| division, it is over the energy squared by the momentum squared squared, and by nothing else.  Offered as a candidate for
--| the two scalings; the author has not said it is the pair.
theorem one_turn_from_the_mass_is_over_by_the_momentum_squared_squared (mass_squared momentum_squared : Int) :
    (2 * mass_squared + momentum_squared) * (2 * mass_squared + momentum_squared)
        - 4 * mass_squared * (mass_squared + momentum_squared)
      = momentum_squared * momentum_squared := by
  simp only [Int.add_mul, Int.mul_add]
  have e1 : 2 * mass_squared * (2 * mass_squared) = 4 * (mass_squared * mass_squared) := by
    rw [two_by_two_is_one_by_one_twice]; rfl
  have e2 : momentum_squared * (2 * mass_squared) = 2 * (mass_squared * momentum_squared) := by
    rw [Int.mul_left_comm, Int.mul_comm momentum_squared mass_squared]
  have e3 : 2 * mass_squared * momentum_squared = 2 * (mass_squared * momentum_squared) := Int.mul_assoc _ _ _
  have e4 : 4 * mass_squared * mass_squared = 4 * (mass_squared * mass_squared) := Int.mul_assoc _ _ _
  have e5 : 4 * mass_squared * momentum_squared = 4 * (mass_squared * momentum_squared) := Int.mul_assoc _ _ _
  rw [e1, e2, e3, e4, e5]; omega

--| On the device's counts: mass squared thirteen eighteens, momentum squared five eighteens, energy squared eighteen
--| eighteens.
theorem on_the_devices_counts_one_turn_is_over_by_ninety_squared :
    (2 * (13 * 18) + 5 * 18) * (2 * (13 * 18) + 5 * 18) - 4 * (13 * 18) * (18 * 18) = (90 * 90 : Int)
      ∧ (13 * 18 + 5 * 18 : Int) = 18 * 18 := by decide
end one_turn_from_the_mass

section the_crank_in_whole_numbers
open readers_experience

--| THE CRANK, IN ITS OWN NUMBERS.  Episode 12 has the crank's turn in counts, where a subtraction stops at nothing.  Where
--| neither subtraction stops, the pair it gives is the pair of the table taken from the same: the place by the trace less
--| the residual, and the second by the trace.
theorem where_nothing_stops_the_cranks_pair_is_the_tables (x y : Nat)
    (the_first_does_not_stop : 18 * y * y ≤ 13 * x * x) (the_second_does_not_stop : 36 * y * y ≤ 2 * 13 * x * y) :
    ((13 * x * x - 18 * y * y : Nat) : Int)
        = (x : Int) * the_table_trace (the_adjugate (the_table_taken_from_the_same x y)) - the_residual_of_the_pair x y
      ∧ ((2 * 13 * x * y - 36 * y * y : Nat) : Int)
        = (y : Int) * the_table_trace (the_adjugate (the_table_taken_from_the_same x y)) := by
  obtain ⟨h1, h2⟩ := the_crank_is_the_place_less_the_residual_over_the_trace x y
  rw [h1, h2, Int.ofNat_sub the_first_does_not_stop, Int.ofNat_sub the_second_does_not_stop]
  simp only [Int.natCast_mul, Int.mul_assoc]
  constructor <;> omega
end the_crank_in_whole_numbers

--#print axioms what_the_bottom_processes_carry_is_two_cells
--#print axioms one_step_of_each_reaches_three_cells
--#print axioms the_observations_step_on_the_bit_is_five_cells
--#print axioms the_law_reads_the_experience_and_the_fencepost
--#print axioms one_turn_from_the_mass_is_over_by_the_momentum_squared_squared
--#print axioms on_the_devices_counts_one_turn_is_over_by_ninety_squared
--#print axioms where_nothing_stops_the_cranks_pair_is_the_tables

section the_ladder_of_twos
open readers_experience the_area

--| THE LADDER.  The author's, 18 November 2026: one decision; two hypotheses; four proposals; eight responses for equality;
--| sixteen possible computations; thirty-two implied subjunctive phrases, with sixteen possible falses.  And: the sixteen
--| are the compile and execute steps (declared).  Each rung is one coin more than the last.
def the_two_coins : List Bool := [true, false]

theorem one_two_four_eight_sixteen :
    the_two_coins.length = 2 ∧ the_arms.length = 4 ∧ the_connected_steps.length = 8 ∧ the_sixteen_steps.length = 16 := by
  decide

--| A step is two comparisons, the one compile builds and the one execute counts.  Take every step's two comparisons, as
--| what each says: thirty-two phrases.
def the_phrases : List (Bool × Bool) := the_sixteen_steps.flatMap fun step => [step.1, step.2]

theorem thirty_two_phrases : the_phrases.length = 32 := by decide

--| Read for what it says, a comparison of two different coins is false.  Sixteen of the thirty-two are.
theorem sixteen_of_the_phrases_say_something_false :
    (the_phrases.filter fun phrase => phrase.1 != phrase.2).length = 16 := by decide

--| Read for whether it can click, only eight cannot.  The eight between are false as said and click all the same, and every
--| one of them is false on true.
theorem eight_cannot_click_and_the_eight_between_are_false_on_true :
    (the_phrases.filter fun phrase => !the_arm_stores_a_fact_that_can_click phrase.1 phrase.2).length = 8
      ∧ (the_phrases.filter fun phrase =>
            phrase.1 != phrase.2 && the_arm_stores_a_fact_that_can_click phrase.1 phrase.2)
          = List.replicate 8 (false, true) := by decide
end the_ladder_of_twos

--#print axioms one_two_four_eight_sixteen
--#print axioms thirty_two_phrases
--#print axioms sixteen_of_the_phrases_say_something_false
--#print axioms eight_cannot_click_and_the_eight_between_are_false_on_true

--| THE PLAN, CARRIED OUT.  The author's, 18 November 2026: proceed with full implementation.  What follows is the finite
--| part: the device's residual, table, action and step on its own inductives, each with the reading that recovers it.
section the_variation_of_the_residual
open «springer-verlag» THE_GOSPEL the_representation assembly_instructions readers_experience the_area the_area.Account
attribute [local instance high] rung01 rung02 rung03 rung04 rung05 rung06 rung07 rung08 rung09 rung10 rung11 rung12 rung13 rung14 rung15
  rung16 rung17 rung18 rung19 rung20 rung21 rung22 rung23 rung24 rung25 rung26 rung27 rung28 rung29 rung32 rung33 rung34 rung35 a_truth_about_the_experience

--| THE VARIATION OF THE RESIDUAL.  Episode 4's `Variation` has three constructors, named for Newton, for Gateaux and for
--| Frechet, holding one, two and three statements.  Its own order sets a Newton's statement against the second statement
--| of the other two, so the second seat is the first variation; the first is the place, and the third the second
--| variation.  Three statements about the device's residual, each a receipt already or here.

--| The place: the residual steps by its slope and the coefficient by the step squared, at every place and for every step.
def the_first_variation_of_the_residual : Prop :=
  ∀ y h : Account, the_same (the_residual_on_the_account (y + h) - the_residual_on_the_account y)
    (the_slope_on_the_account y * h + holding the_coefficient * (h * h))
--| Here: the slope steps by twice the coefficient by the step.
def the_slope_of_the_residual_steps : Prop :=
  ∀ y h : Account, the_same (the_slope_on_the_account (y + h) - the_slope_on_the_account y) (holding twice_the_coefficient * h)
--| The second variation: the step by one, taken after a step by another and taken before it, differ by twice the
--| coefficient by the two steps.
def the_second_variation_of_the_residual : Prop :=
  ∀ y h k : Account,
    the_same ((the_residual_on_the_account (y + k + h) - the_residual_on_the_account (y + k))
                - (the_residual_on_the_account (y + h) - the_residual_on_the_account y))
             (holding twice_the_coefficient * k * h)

theorem the_first_variation_of_the_residual_holds : the_first_variation_of_the_residual :=
  the_residual_steps_by_its_slope_exactly
theorem the_slope_of_the_residual_steps_holds : the_slope_of_the_residual_steps :=
  the_slope_steps_by_twice_the_coefficient_exactly
theorem the_second_variation_of_the_residual_holds : the_second_variation_of_the_residual := by
  intro y h k
  have e1 := (the_same_is_the_same_balance _ _).1 (the_residual_steps_by_its_slope_exactly (y + k) h)
  have e2 := (the_same_is_the_same_balance _ _).1 (the_residual_steps_by_its_slope_exactly y h)
  have e3 := (the_same_is_the_same_balance _ _).1 (the_slope_steps_by_twice_the_coefficient_exactly y k)
  rw [the_same_is_the_same_balance]
  simp only [balance_of_beside, balance_of_less, balance_of_each_for_each] at e1 e2 e3 ⊢
  have e4 := congrArg (fun z => z * balance h) e3
  simp only [Int.sub_mul] at e4
  omega

--| The three, in the three constructors, on one gospel.
def the_gospel_of_the_residual : Gospel := .the_proof the_first_variation_of_the_residual
def the_newton_of_the_residual : Variation :=
  .the_newton the_gospel_of_the_residual the_first_variation_of_the_residual
def the_gateaux_of_the_residual : Variation :=
  .the_gateaux the_gospel_of_the_residual the_slope_of_the_residual_steps the_first_variation_of_the_residual
    the_newton_of_the_residual
def the_frechet_of_the_residual : Variation :=
  .the_frechet the_gospel_of_the_residual the_slope_of_the_residual_steps the_first_variation_of_the_residual
    the_second_variation_of_the_residual the_gateaux_of_the_residual the_newton_of_the_residual

--| Every statement held is true.
theorem every_statement_the_three_hold_is_true :
    the_first_variation_of_the_residual ∧ the_slope_of_the_residual_steps ∧ the_second_variation_of_the_residual :=
  ⟨the_first_variation_of_the_residual_holds, the_slope_of_the_residual_steps_holds,
   the_second_variation_of_the_residual_holds⟩

--| Episode 8's two readers read the shape and not the statements: one, two and three by Newton's; one, two and four by
--| Krylov's, who follows both branches.
theorem the_two_readers_read_the_shape :
    (the_newton_of_the_residual.newton.length, the_gateaux_of_the_residual.newton.length,
        the_frechet_of_the_residual.newton.length) = (1, 2, 3)
      ∧ (the_newton_of_the_residual.krylov.length, the_gateaux_of_the_residual.krylov.length,
        the_frechet_of_the_residual.krylov.length) = (1, 2, 4) := ⟨rfl, rfl⟩

--| THE PROCESS KEEPS THE STEP.  The process that steps a variation is the big red dog's.  Handed the Newton of the residual
--| it gives a Gateaux on the same gospel whose second statement is still the residual's first variation; handed that, a
--| Frechet whose second statement is still it.  What the readers forget, the process keeps.
theorem the_process_keeps_the_first_variation :
    (∃ (place : Prop), the_big_red_dog_process.transmute the_newton_of_the_residual
        = .the_gateaux the_gospel_of_the_residual place the_first_variation_of_the_residual the_big_red_dog_process.Du)
      ∧ the_big_red_dog_process.transmute the_gateaux_of_the_residual
        = .the_frechet the_gospel_of_the_residual the_slope_of_the_residual_steps the_first_variation_of_the_residual
            (the_slope_of_the_residual_steps ∧ ¬ the_first_variation_of_the_residual) the_newton_of_the_residual
            the_big_red_dog_process.Du :=
  ⟨⟨_, rfl⟩, rfl⟩

--| And the third statement the process writes for itself, the first and not the second, is false: it is a truth read as a
--| falsehood, since the second is true.
theorem what_the_process_writes_third_is_false :
    ¬ (the_slope_of_the_residual_steps ∧ ¬ the_first_variation_of_the_residual) :=
  fun both => both.2 the_first_variation_of_the_residual_holds
--| IN THE ORDER.  Episode 4's order puts a Newton under a Gateaux or a Frechet exactly when they are on one gospel and the
--| Newton's statement is their second.
theorem a_newton_is_under_a_gateaux_exactly_when_its_statement_is_second (model statement place seat : Prop)
    (tail : Variation) :
    Variation.le (.the_newton (.the_proof model) statement) (.the_gateaux (.the_proof model) place seat tail)
      ↔ statement = seat := by
  simp only [Variation.le, Gospel.le, true_and]
theorem a_newton_is_under_a_frechet_exactly_when_its_statement_is_second (model statement place seat third : Prop)
    (this that : Variation) :
    Variation.le (.the_newton (.the_proof model) statement) (.the_frechet (.the_proof model) place seat third this that)
      ↔ statement = seat := by
  simp only [Variation.le, Gospel.le, true_and]

theorem the_newton_is_under_the_other_two :
    Variation.le the_newton_of_the_residual the_gateaux_of_the_residual
      ∧ Variation.le the_newton_of_the_residual the_frechet_of_the_residual :=
  ⟨(a_newton_is_under_a_gateaux_exactly_when_its_statement_is_second _ _ _ _ _).2 rfl,
   (a_newton_is_under_a_frechet_exactly_when_its_statement_is_second _ _ _ _ _ _ _).2 rfl⟩

--| TURNED AGAIN.  What three turns of the process make of the Newton of the residual.
theorem three_turns_of_the_process :
    ∃ (place : Prop),
      the_big_red_dog_process.transmute the_newton_of_the_residual
          = .the_gateaux the_gospel_of_the_residual place the_first_variation_of_the_residual the_big_red_dog_process.Du
        ∧ the_big_red_dog_process.transmute (the_big_red_dog_process.transmute the_newton_of_the_residual)
          = .the_frechet the_gospel_of_the_residual place the_first_variation_of_the_residual
              (place ∧ ¬ the_first_variation_of_the_residual) the_big_red_dog_process.Du the_big_red_dog_process.Du
        ∧ the_big_red_dog_process.transmute (the_big_red_dog_process.transmute
            (the_big_red_dog_process.transmute the_newton_of_the_residual))
          = .the_gateaux the_gospel_of_the_residual (place ∧ place)
              (the_first_variation_of_the_residual = (place ∧ ¬ the_first_variation_of_the_residual))
              the_big_red_dog_process.Du :=
  ⟨_, rfl, rfl, rfl⟩

--| Two turns keep the first variation in the seat the order reads.
theorem two_turns_of_the_process_keep_the_first_variation :
    Variation.le the_newton_of_the_residual (the_big_red_dog_process.transmute the_newton_of_the_residual)
      ∧ Variation.le the_newton_of_the_residual
          (the_big_red_dog_process.transmute (the_big_red_dog_process.transmute the_newton_of_the_residual)) := by
  obtain ⟨place, one, two, _⟩ := three_turns_of_the_process
  rw [two, one]
  exact ⟨(a_newton_is_under_a_gateaux_exactly_when_its_statement_is_second _ _ _ _ _).2 rfl,
         (a_newton_is_under_a_frechet_exactly_when_its_statement_is_second _ _ _ _ _ _ _).2 rfl⟩

--| The third turn does not.  The process writes into that seat that the first variation is the same statement as the
--| place and not the first variation; and that is false.  Three turns, and the slip is on the third.
theorem the_third_turn_of_the_process_does_not_keep_it :
    ¬ Variation.le the_newton_of_the_residual
        (the_big_red_dog_process.transmute (the_big_red_dog_process.transmute
          (the_big_red_dog_process.transmute the_newton_of_the_residual))) := by
  obtain ⟨place, _, _, three⟩ := three_turns_of_the_process
  rw [three]
  intro under
  have the_seat := (a_newton_is_under_a_gateaux_exactly_when_its_statement_is_second _ _ _ _ _).1 under
  have it_holds := the_first_variation_of_the_residual_holds
  have the_same_statement := Eq.mp the_seat it_holds
  exact (Eq.mp the_same_statement it_holds).2 it_holds
end the_variation_of_the_residual
section the_two_directions_of_the_table
open readers_experience

--| THE TWO DIRECTIONS.  A direction is five on the first coin and a whole number on the second.  The table takes it to
--| eighteen and that number of itself, exactly on the first coin, and on the second short by ninety less the number
--| squared.  Ninety is the round trip.  No whole number squares to ninety, so no whole direction is carried exactly; the
--| defect is stated, not hidden.
def the_direction (s : Int) : Bool → Int := fun coin => if coin then 5 else s

theorem the_table_carries_a_direction_but_for_the_round_trip (s : Int) :
    the_refine the_full_table (the_direction s) true = (18 + s) * the_direction s true
      ∧ the_refine the_full_table (the_direction s) false = (18 + s) * the_direction s false + (90 - s * s) := by
  constructor
  · show (18 : Int) * 5 + 5 * s = (18 + s) * 5; omega
  · show (18 : Int) * 5 + 18 * s = (18 + s) * s + (90 - s * s); rw [Int.add_mul]; omega

--| The pairing of the two coins, eighteen and five.  A direction against itself is four hundred and fifty and five of its
--| square; against the direction turned over, five of the same defect.
def the_pairing (u v : Bool → Int) : Int := 18 * (u true * v true) + 5 * (u false * v false)

theorem the_two_directions_are_square_but_for_the_round_trip (s : Int) :
    the_pairing (the_direction s) (the_direction s) = 450 + 5 * (s * s)
      ∧ the_pairing (the_direction s) (the_direction (-s)) = 5 * (90 - s * s) := by
  constructor
  · show (18 : Int) * (5 * 5) + 5 * (s * s) = 450 + 5 * (s * s); omega
  · show (18 : Int) * (5 * 5) + 5 * (s * -s) = 5 * (90 - s * s); rw [Int.mul_neg]; omega

--| The same directions carry the table taken from the same, with the same defect by the second number.
theorem the_table_taken_from_the_same_carries_a_direction (N D s : Int) :
    the_refine (the_table_taken_from_the_same N D) (the_direction s) true = (13 * N - D * (18 + s)) * the_direction s true
      ∧ the_refine (the_table_taken_from_the_same N D) (the_direction s) false
          = (13 * N - D * (18 + s)) * the_direction s false - D * (90 - s * s) := by
  obtain ⟨h1, h2, h3, h4⟩ := what_the_table_taken_from_the_same_holds N D
  constructor
  · show the_table_taken_from_the_same N D true true * 5 + the_table_taken_from_the_same N D true false * s
        = (13 * N - D * (18 + s)) * 5
    have e1 : -(5 * D) * s = -(5 * (D * s)) := by rw [Int.neg_mul, Int.mul_assoc]
    have e2 : D * (18 + s) = 18 * D + D * s := by rw [Int.mul_add, Int.mul_comm D 18]
    rw [h1, h3, e1, e2]; omega
  · show the_table_taken_from_the_same N D false true * 5 + the_table_taken_from_the_same N D false false * s
        = (13 * N - D * (18 + s)) * s - D * (90 - s * s)
    rw [h4, h2, Int.sub_mul, Int.sub_mul, Int.mul_add, Int.mul_sub, Int.add_mul, Int.mul_assoc 18 D s,
      Int.mul_assoc 13 N s, Int.mul_assoc D s s]
    have e : D * 18 * s = 18 * (D * s) := by rw [Int.mul_comm D 18, Int.mul_assoc]
    rw [e]; omega
end the_two_directions_of_the_table

section the_multiplier
open readers_experience

--| THE MULTIPLIER.  The action of the weighed table taken from the same is, in the place, a multiple of the weighed square
--| of what it acts on.  Step the place and the action steps by thirteen of the step by that square, and by nothing else.
--| So the place is the multiplier of the condition that the weighed square is held.
def the_weighed_square (v : Bool → Int) : Int := 18 * (v true * v true) + 5 * (v false * v false)

theorem the_action_of_two_tables_is_the_two_actions (this that : Table) (v : Bool → Int) :
    the_action_of (fun a b => this a b + that a b) v = the_action_of this v + the_action_of that v := by
  simp only [the_action_of, the_refine, Int.add_mul, Int.mul_add]; omega

def the_weighed_same (number : Int) : Table := fun a b => if a = b then (if a then 18 * number else 5 * number) else 0

theorem the_action_of_the_weighed_same_is_the_weighed_square (number : Int) (v : Bool → Int) :
    the_action_of (the_weighed_same number) v = number * the_weighed_square v := by
  show v true * (18 * number * v true + 0 * v false) + v false * (0 * v true + 5 * number * v false)
      = number * (18 * (v true * v true) + 5 * (v false * v false))
  rw [Int.zero_mul, Int.zero_mul, Int.add_zero, Int.zero_add, Int.mul_add]
  have e1 : v true * (18 * number * v true) = number * (18 * (v true * v true)) := by ac_nf
  have e2 : v false * (5 * number * v false) = number * (5 * (v false * v false)) := by ac_nf
  rw [e1, e2]

theorem stepping_the_place_steps_the_table_by_the_weighed_same (N D step : Int) (a b : Bool) :
    weighed_by_its_coin (the_table_taken_from_the_same (N + step) D) a b
      = weighed_by_its_coin (the_table_taken_from_the_same N D) a b + the_weighed_same (13 * step) a b := by
  obtain ⟨h1, h2, h3, h4⟩ := what_the_table_taken_from_the_same_holds N D
  obtain ⟨k1, k2, k3, k4⟩ := what_the_table_taken_from_the_same_holds (N + step) D
  cases a <;> cases b
  · show (5 : Int) * the_table_taken_from_the_same (N + step) D false false
        = 5 * the_table_taken_from_the_same N D false false + 5 * (13 * step); rw [h2, k2]; omega
  · show (5 : Int) * the_table_taken_from_the_same (N + step) D false true
        = 5 * the_table_taken_from_the_same N D false true + 0; rw [h4, k4]; omega
  · show (18 : Int) * the_table_taken_from_the_same (N + step) D true false
        = 18 * the_table_taken_from_the_same N D true false + 0; rw [h3, k3]; omega
  · show (18 : Int) * the_table_taken_from_the_same (N + step) D true true
        = 18 * the_table_taken_from_the_same N D true true + 18 * (13 * step); rw [h1, k1]; omega

theorem the_place_is_the_multiplier_of_the_weighed_square (N D step : Int) (v : Bool → Int) :
    the_action_of (weighed_by_its_coin (the_table_taken_from_the_same (N + step) D)) v
        - the_action_of (weighed_by_its_coin (the_table_taken_from_the_same N D)) v
      = 13 * step * the_weighed_square v := by
  rw [show weighed_by_its_coin (the_table_taken_from_the_same (N + step) D)
        = fun a b => weighed_by_its_coin (the_table_taken_from_the_same N D) a b + the_weighed_same (13 * step) a b from
      funext fun a => funext fun b => stepping_the_place_steps_the_table_by_the_weighed_same N D step a b,
    the_action_of_two_tables_is_the_two_actions, the_action_of_the_weighed_same_is_the_weighed_square]
  omega

--| THREE CONDITIONS, KEPT APART.  Reading the pair as a place needs the second number; reading the inverse needs the
--| residual; the crank's turn needs the trace.  They fail in different places.  At eighteen over thirteen the trace is
--| nothing and the residual is not, so the table has an inverse and the crank has no turn.
theorem where_the_trace_is_nothing_the_residual_is_not :
    the_table_trace (the_adjugate (the_table_taken_from_the_same 18 13)) = 0
      ∧ the_residual_of_the_pair 18 13 = -1170
      ∧ the_table_determinant (the_table_taken_from_the_same 18 13) ≠ 0 := by decide
end the_multiplier
section around_a_closed_walk

--| AROUND A CLOSED WALK.  A walk of some number of steps, read at whole-number places.  What a reading is summed to along
--| it; and what a difference sums to: the far end less the near.  On a closed walk the ends are one place.
def summed_along : Nat → (Nat → Int) → Int
  | 0, _ => 0
  | steps + 1, reading => summed_along steps reading + reading steps

theorem two_readings_summed_are_the_two_sums (steps : Nat) (this that : Nat → Int) :
    summed_along steps (fun place => this place + that place) = summed_along steps this + summed_along steps that := by
  induction steps with
  | zero => rfl
  | succ steps ih => simp only [summed_along, ih]; omega

theorem a_difference_summed_is_the_far_end_less_the_near (steps : Nat) (reading : Nat → Int) :
    summed_along steps (fun place => reading (place + 1) - reading place) = reading steps - reading 0 := by
  induction steps with
  | zero => show (0 : Int) = reading 0 - reading 0; omega
  | succ steps ih => simp only [summed_along, ih]; omega

theorem around_a_closed_walk_a_difference_sums_to_nothing (steps : Nat) (reading : Nat → Int)
    (closed : reading steps = reading 0) :
    summed_along steps (fun place => reading (place + 1) - reading place) = 0 := by
  rw [a_difference_summed_is_the_far_end_less_the_near, closed]; omega

--| So on a closed walk a reading summed one step on is the reading summed.
theorem around_a_closed_walk_the_sum_does_not_mind_a_step (steps : Nat) (reading : Nat → Int)
    (closed : reading steps = reading 0) :
    summed_along steps (fun place => reading (place + 1)) = summed_along steps reading := by
  have h := around_a_closed_walk_a_difference_sums_to_nothing steps reading closed
  have e : (fun place => reading (place + 1)) = fun place => (reading (place + 1) - reading place) + reading place :=
    funext fun place => by omega
  rw [e, two_readings_summed_are_the_two_sums, h]; omega

--| THE DIFFERENCE OF A PRODUCT, WITH NOTHING OVER.  The first read one step on, by the difference of the second; and the
--| second, by the difference of the first.  The remainder is in where the first is read.
theorem the_difference_of_a_product_with_nothing_over (this that : Nat → Int) (place : Nat) :
    this (place + 1) * that (place + 1) - this place * that place
      = this (place + 1) * (that (place + 1) - that place) + that place * (this (place + 1) - this place) := by
  rw [Int.mul_sub, Int.mul_sub, Int.mul_comm (that place) (this (place + 1)), Int.mul_comm (that place) (this place)]
  omega

--| SUMMATION BY PARTS.  Around a closed walk, one reading one step on against the difference of another is the other
--| against the difference of the one, owed.
theorem summation_by_parts_around_a_closed_walk (steps : Nat) (this that : Nat → Int)
    (this_closes : this steps = this 0) (that_closes : that steps = that 0) :
    summed_along steps (fun place => this (place + 1) * (that (place + 1) - that place))
      = - summed_along steps (fun place => that place * (this (place + 1) - this place)) := by
  have closed : (fun place => this place * that place) steps = (fun place => this place * that place) 0 := by
    show this steps * that steps = this 0 * that 0; rw [this_closes, that_closes]
  have h := around_a_closed_walk_a_difference_sums_to_nothing steps (fun place => this place * that place) closed
  have e : (fun place => this (place + 1) * that (place + 1) - this place * that place)
      = fun place => this (place + 1) * (that (place + 1) - that place) + that place * (this (place + 1) - this place) :=
    funext fun place => the_difference_of_a_product_with_nothing_over this that place
  rw [show (fun place => (fun place => this place * that place) (place + 1) - (fun place => this place * that place) place)
        = fun place => this (place + 1) * that (place + 1) - this place * that place from rfl, e,
      two_readings_summed_are_the_two_sums] at h
  omega

--| THE REMAINDER DOES NOT SUM AWAY ALONE.  Written with the first read in place, the product rule has a third term, the two
--| differences one by the other.  Around a closed walk the three together sum to nothing.
theorem around_a_closed_walk_the_three_terms_sum_to_nothing (steps : Nat) (this that : Nat → Int)
    (this_closes : this steps = this 0) (that_closes : that steps = that 0) :
    summed_along steps (fun place => this place * (that (place + 1) - that place))
      + summed_along steps (fun place => that place * (this (place + 1) - this place))
      + summed_along steps (fun place => (this (place + 1) - this place) * (that (place + 1) - that place)) = 0 := by
  have h := summation_by_parts_around_a_closed_walk steps this that this_closes that_closes
  have e : (fun place => this (place + 1) * (that (place + 1) - that place))
      = fun place => this place * (that (place + 1) - that place)
          + (this (place + 1) - this place) * (that (place + 1) - that place) :=
    funext fun place => by rw [Int.sub_mul]; omega
  rw [e, two_readings_summed_are_the_two_sums] at h
  omega

--| And the third does not sum to nothing alone.  A walk of two steps, nothing, one, nothing: the differences are one and
--| one owed, and their squares sum to two.
def nothing_one_nothing : Nat → Int := fun place => if place = 1 then 1 else 0
theorem the_remainder_alone_sums_to_two :
    nothing_one_nothing 2 = nothing_one_nothing 0
      ∧ summed_along 2 (fun place => (nothing_one_nothing (place + 1) - nothing_one_nothing place)
          * (nothing_one_nothing (place + 1) - nothing_one_nothing place)) = 2 := by decide
end around_a_closed_walk

section the_same_on_the_torus

--| On the torus of four directions the same rule holds at every site: the first read one step on.
theorem the_difference_of_a_product_on_the_torus_with_nothing_over {n : Nat} (f g : Site4 n → Int) (way : Direction)
    (x : Site4 n) :
    the_difference way (fun y => f y * g y) x
      = f (the_step way x) * the_difference way g x + g x * the_difference way f x := by
  simp only [the_difference]
  rw [Int.mul_sub, Int.mul_sub, Int.mul_comm (g x) (f (the_step way x)), Int.mul_comm (g x) (f x)]
  omega
end the_same_on_the_torus

section a_step_that_keeps_the_length

--| A STEP THAT KEEPS THE LENGTH.  A state at every site, a turn of length one on every link.  The step: the state at the far
--| end of the link, carried back along it.  At every site the carried state is as long as the state it came from.
def the_state_one_step_on {n : Nat} (state : Site4 n → Turns) (U : Torus4 n) (way : Direction) : Site4 n → Turns :=
  fun x => the_turns_product (U way x) (state (the_step way x))

theorem the_step_keeps_the_length_at_every_site {n : Nat} (state : Site4 n → Turns) (U : Torus4 n) (way : Direction)
    (unit : ∀ x, the_turns_norm (U way x) = 1) (x : Site4 n) :
    the_turns_norm (the_state_one_step_on state U way x) = the_turns_norm (state (the_step way x)) := by
  rw [the_state_one_step_on, the_norm_is_multiplicative, unit, Int.one_mul]

--| Around a closed walk the lengths summed are kept: the step moves every length one place and loses none.
theorem around_a_closed_walk_the_step_keeps_the_summed_length (steps : Nat) (state link : Nat → Turns)
    (closed : state steps = state 0) (unit : ∀ place, the_turns_norm (link place) = 1) :
    summed_along steps (fun place => the_turns_norm (the_turns_product (link place) (state (place + 1))))
      = summed_along steps (fun place => the_turns_norm (state place)) := by
  have e : (fun place => the_turns_norm (the_turns_product (link place) (state (place + 1))))
      = fun place => (fun place => the_turns_norm (state place)) (place + 1) :=
    funext fun place => by rw [the_norm_is_multiplicative, unit, Int.one_mul]
  rw [e]
  exact around_a_closed_walk_the_sum_does_not_mind_a_step steps (fun place => the_turns_norm (state place))
    (by show the_turns_norm (state steps) = the_turns_norm (state 0); rw [closed])
end a_step_that_keeps_the_length

section one_table_three_ways

--| ONE TABLE, THREE WAYS.  Episode 12's table of a stay and two crossings.  Its gap squared is four of the two crossings,
--| one by the other, whatever the stay.
theorem the_gap_squared_is_four_of_the_crossings (stay out back : Int) :
    the_gap_squared (the_refinement_table stay out back) = 4 * (out * back) := by
  show (stay + stay) * (stay + stay) - 4 * (stay * stay - out * back) = 4 * (out * back)
  rw [Int.add_mul, Int.mul_add, Int.mul_sub]; omega

--| The device's table is the stay eighteen, out five, back eighteen.  Keep both crossings; strike the one out; or turn
--| the one back over.  The gap squared is over nothing, nothing, and under nothing.
theorem the_devices_table_is_that_table (a b : Bool) : the_refinement_table 18 5 18 a b = the_full_table a b := by
  cases a <;> cases b <;> rfl

theorem kept_struck_and_turned_over :
    the_gap_squared (the_refinement_table 18 5 18) = 360
      ∧ the_gap_squared (the_refinement_table 18 0 18) = 0
      ∧ the_gap_squared (the_refinement_table 18 5 (-18)) = -360 := by decide
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
def the_direction_up : Bool → Int × Int := fun coin => if coin then (5, 0) else (0, 1)
def the_direction_down : Bool → Int × Int := fun coin => if coin then (5, 0) else (0, -1)
def refined_in_pairs (table : Table) (v : Bool → Int × Int) (coin : Bool) : Int × Int :=
  (the_refine table (fun c => (v c).1) coin, the_refine table (fun c => (v c).2) coin)

theorem the_table_carries_the_two_directions_exactly :
    (∀ coin, refined_in_pairs the_full_table the_direction_up coin
        = the_surd_product the_outer_radius (the_direction_up coin))
      ∧ (∀ coin, refined_in_pairs the_full_table the_direction_down coin
        = the_surd_product the_hole (the_direction_down coin)) := by decide

--| In the pairing of the two coins each direction against itself is nine hundred, and the one against the other is
--| nothing: they are square to each other, with nothing over.
def the_pairing_in_pairs (u v : Bool → Int × Int) : Int × Int :=
  ((18 : Int) * (the_surd_product (u true) (v true)).1 + 5 * (the_surd_product (u false) (v false)).1,
   (18 : Int) * (the_surd_product (u true) (v true)).2 + 5 * (the_surd_product (u false) (v false)).2)

theorem the_two_directions_are_square_to_each_other :
    the_pairing_in_pairs the_direction_up the_direction_up = (900, 0)
      ∧ the_pairing_in_pairs the_direction_down the_direction_down = (900, 0)
      ∧ the_pairing_in_pairs the_direction_up the_direction_down = (0, 0) := by decide

--| The same two carry the table taken from the same, for every pair: by thirteen of the first less the second of the
--| outer radius, and of the hole.
theorem the_table_taken_from_the_same_carries_them_exactly (N D : Int) :
    (∀ coin, refined_in_pairs (the_table_taken_from_the_same N D) the_direction_up coin
        = the_surd_product (13 * N - 18 * D, - D) (the_direction_up coin))
      ∧ (∀ coin, refined_in_pairs (the_table_taken_from_the_same N D) the_direction_down coin
        = the_surd_product (13 * N - 18 * D, D) (the_direction_down coin)) := by
  obtain ⟨h1, h2, h3, h4⟩ := what_the_table_taken_from_the_same_holds N D
  have ninety := the_round_trip_is_ninety
  refine ⟨fun coin => ?_, fun coin => ?_⟩ <;> cases coin <;> refine Prod.ext ?_ ?_
  · show the_table_taken_from_the_same N D false true * 5 + the_table_taken_from_the_same N D false false * 0
        = (13 * N - 18 * D) * 0 + the_round_trip * (- D) * 1
    rw [h4, h2, ninety]; omega
  · show the_table_taken_from_the_same N D false true * 0 + the_table_taken_from_the_same N D false false * 1
        = (13 * N - 18 * D) * 1 + (- D) * 0
    rw [h4, h2]; omega
  · show the_table_taken_from_the_same N D true true * 5 + the_table_taken_from_the_same N D true false * 0
        = (13 * N - 18 * D) * 5 + the_round_trip * (- D) * 0
    rw [h1, h3, ninety]; omega
  · show the_table_taken_from_the_same N D true true * 0 + the_table_taken_from_the_same N D true false * 1
        = (13 * N - 18 * D) * 0 + (- D) * 5
    rw [h1, h3]; omega
  · show the_table_taken_from_the_same N D false true * 5 + the_table_taken_from_the_same N D false false * 0
        = (13 * N - 18 * D) * 0 + the_round_trip * D * (-1)
    rw [h4, h2, ninety]; omega
  · show the_table_taken_from_the_same N D false true * 0 + the_table_taken_from_the_same N D false false * (-1)
        = (13 * N - 18 * D) * (-1) + D * 0
    rw [h4, h2]; omega
  · show the_table_taken_from_the_same N D true true * 5 + the_table_taken_from_the_same N D true false * 0
        = (13 * N - 18 * D) * 5 + the_round_trip * D * 0
    rw [h1, h3, ninety]; omega
  · show the_table_taken_from_the_same N D true true * 0 + the_table_taken_from_the_same N D true false * (-1)
        = (13 * N - 18 * D) * 0 + D * 5
    rw [h1, h3]; omega

--| And what the two carry it by, one by the other, is the determinant: thirteen residuals, with no part of the root.
theorem the_two_it_is_carried_by_multiply_to_thirteen_residuals (N D : Int) :
    the_surd_product (13 * N - 18 * D, - D) (13 * N - 18 * D, D) = (13 * the_residual_of_the_pair N D, 0) := by
  have ninety := the_round_trip_is_ninety
  refine Prod.ext ?_ ?_
  · show (13 * N - 18 * D) * (13 * N - 18 * D) + the_round_trip * (- D) * D = 13 * the_residual_of_the_pair N D
    rw [ninety, the_residual_of_the_pair, Int.sub_mul, Int.mul_sub, Int.mul_sub, Int.mul_neg, Int.neg_mul]
    have e1 : 13 * N * (13 * N) = 13 * 13 * (N * N) := two_by_two_is_one_by_one_twice 13 N 13 N
    have e2 : 18 * D * (13 * N) = 18 * 13 * (N * D) := by rw [two_by_two_is_one_by_one_twice, Int.mul_comm D N]
    have e3 : 13 * N * (18 * D) = 13 * 18 * (N * D) := two_by_two_is_one_by_one_twice 13 N 18 D
    have e4 : 18 * D * (18 * D) = 18 * 18 * (D * D) := two_by_two_is_one_by_one_twice 18 D 18 D
    have e5 : (90 : Int) * D * D = 90 * (D * D) := Int.mul_assoc 90 D D
    rw [e1, e2, e3, e4, e5]; omega
  · show (13 * N - 18 * D) * D + (- D) * (13 * N - 18 * D) = 0
    rw [Int.neg_mul, Int.mul_comm D (13 * N - 18 * D)]; omega
end the_two_directions_exactly

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
theorem the_weighed_action_is_two_squares (v : Bool → Int) :
    the_action_of (weighed_by_its_coin the_full_table) v
      = 90 * ((v true + v false) * (v true + v false)) + 234 * (v true * v true) := by
  show v true * (18 * 18 * v true + 18 * 5 * v false) + v false * (5 * 18 * v true + 5 * 18 * v false)
      = 90 * ((v true + v false) * (v true + v false)) + 234 * (v true * v true)
  have e1 : v true * (18 * 18 * v true) = 18 * 18 * (v true * v true) := Int.mul_left_comm _ _ _
  have e2 : v true * (18 * 5 * v false) = 18 * 5 * (v true * v false) := Int.mul_left_comm _ _ _
  have e3 : v false * (5 * 18 * v true) = 5 * 18 * (v true * v false) := by
    rw [Int.mul_left_comm, Int.mul_comm (v false) (v true)]
  have e4 : v false * (5 * 18 * v false) = 5 * 18 * (v false * v false) := Int.mul_left_comm _ _ _
  have left : v true * (18 * 18 * v true + 18 * 5 * v false) + v false * (5 * 18 * v true + 5 * 18 * v false)
      = 324 * (v true * v true) + 180 * (v true * v false) + 90 * (v false * v false) := by
    rw [Int.mul_add (v true), Int.mul_add (v false), e1, e2, e3, e4]; omega
  have right : (v true + v false) * (v true + v false)
      = v true * v true + 2 * (v true * v false) + v false * v false := by
    rw [Int.add_mul, Int.mul_add, Int.mul_add, Int.mul_comm (v false) (v true)]; omega
  rw [left, right]; omega

theorem a_square_is_never_under_nothing (x : Int) : 0 ≤ x * x := by
  rcases Int.le_total 0 x with h | h
  · exact Int.mul_nonneg h h
  · have := Int.mul_nonneg (Int.neg_nonneg_of_nonpos h) (Int.neg_nonneg_of_nonpos h)
    rwa [Int.neg_mul_neg] at this

theorem the_weighed_action_is_never_under_nothing (v : Bool → Int) :
    0 ≤ the_action_of (weighed_by_its_coin the_full_table) v := by
  rw [the_weighed_action_is_two_squares]
  have a := a_square_is_never_under_nothing (v true + v false)
  have b := a_square_is_never_under_nothing (v true)
  omega

--| THE TABLE MADE THE SAME BOTH WAYS.  In Episode 12's pairs, put the root on both crossings: eighteen on the stays and
--| the root between.  Each row adds to the outer radius.  It carries the two coins together by the outer radius and the
--| two coins against each other by the hole.  And its two rows are not one row: where it is tells what comes next.
def the_table_the_same_both_ways (a b : Bool) : Int × Int := if a = b then (18, 0) else (0, 1)

theorem each_row_adds_to_the_outer_radius (a : Bool) :
    ((the_table_the_same_both_ways a true).1 + (the_table_the_same_both_ways a false).1,
     (the_table_the_same_both_ways a true).2 + (the_table_the_same_both_ways a false).2) = the_outer_radius := by
  cases a <;> rfl

theorem together_by_the_outer_radius_and_against_by_the_hole :
    (∀ a, ((the_table_the_same_both_ways a true).1 - (the_table_the_same_both_ways a false).1,
           (the_table_the_same_both_ways a true).2 - (the_table_the_same_both_ways a false).2)
        = the_surd_product the_hole (if a then (1, 0) else (-1, 0)))
      ∧ the_table_the_same_both_ways true ≠ the_table_the_same_both_ways false := by
  refine ⟨by decide, fun same => ?_⟩
  have h := congrFun same true
  exact absurd h (by decide)

--| WHAT IS SPREAD.  Two whole numbers on the two coins, taken through that table: what they come to together is the outer
--| radius of what they were together, and how far apart they are is the hole of how far apart they were.  The hole is
--| under the outer radius, so every turn the two are nearer level.  Nothing is said here of an entropy.
theorem a_turn_spreads_the_two (first second : Int) :
    the_surd_product (18, 0) (first, 0) = (18 * first, 0)
      ∧ ((18 * first + 0 * second) + (0 * first + 18 * second), (0 * first + 1 * second) + (1 * first + 0 * second))
          = the_surd_product the_outer_radius (first + second, 0)
      ∧ ((18 * first + 0 * second) - (0 * first + 18 * second), (0 * first + 1 * second) - (1 * first + 0 * second))
          = the_surd_product the_hole (first - second, 0) := by
  have ninety := the_round_trip_is_ninety
  refine ⟨?_, ?_, ?_⟩ <;> refine Prod.ext ?_ ?_
  · show (18 : Int) * first + the_round_trip * 0 * 0 = 18 * first; rw [ninety]; omega
  · show (18 : Int) * 0 + 0 * first = 0; omega
  · show (18 * first + 0 * second) + (0 * first + 18 * second) = 18 * (first + second) + the_round_trip * 1 * 0
    rw [ninety]; omega
  · show (0 * first + 1 * second) + (1 * first + 0 * second) = 18 * 0 + 1 * (first + second); omega
  · show (18 * first + 0 * second) - (0 * first + 18 * second) = 18 * (first - second) + the_round_trip * (-1) * 0
    rw [ninety]; omega
  · show (0 * first + 1 * second) - (1 * first + 0 * second) = 18 * 0 + (-1) * (first - second); omega

--| TWO, AND NO MORE.  The closed walks of the table, counted by length.  Any two in a row do not fix the next by a ratio:
--| the square of them against their neighbours is three hundred and sixty, the gap squared.  Any three in a row do fix
--| the next: the cube of them is nothing.  A reader that is to say what comes next needs two numbers and no third.
theorem two_closed_counts_are_needed_and_three_are_not :
    (the_closed_walks 0 : Int) * the_closed_walks 2 - (the_closed_walks 1 : Int) * the_closed_walks 1 = 360
      ∧ (the_closed_walks 0 : Int) * ((the_closed_walks 2 : Int) * the_closed_walks 4 - (the_closed_walks 3 : Int) * the_closed_walks 3)
          - (the_closed_walks 1 : Int) * ((the_closed_walks 1 : Int) * the_closed_walks 4 - (the_closed_walks 3 : Int) * the_closed_walks 2)
          + (the_closed_walks 2 : Int) * ((the_closed_walks 1 : Int) * the_closed_walks 3 - (the_closed_walks 2 : Int) * the_closed_walks 2)
        = 0 := by decide

--| THE GAP SQUARED IS A SYMBOL'S DISCRIMINANT.  For any table: the difference of the stays squared and four of the
--| crossings, one by the other.  That is the discriminant of the form with the one crossing on the first squared, the
--| difference of the stays on the two together, and the other crossing owed on the second squared.
theorem the_gap_squared_is_the_discriminant_of_the_symbol (table : Table) :
    the_gap_squared table
      = (table true true - table false false) * (table true true - table false false)
        + 4 * (table true false * table false true) := by
  show (table true true + table false false) * (table true true + table false false)
        - 4 * (table true true * table false false - table true false * table false true) = _
  rw [Int.add_mul, Int.mul_add, Int.mul_add, Int.sub_mul, Int.mul_sub, Int.mul_sub, Int.mul_sub,
    Int.mul_comm (table false false) (table true true)]
  omega
end the_ledgers_first_rows

--#print axioms the_weighed_action_is_two_squares
--#print axioms the_weighed_action_is_never_under_nothing
--#print axioms each_row_adds_to_the_outer_radius
--#print axioms together_by_the_outer_radius_and_against_by_the_hole
--#print axioms a_turn_spreads_the_two
--#print axioms two_closed_counts_are_needed_and_three_are_not
--#print axioms the_gap_squared_is_the_discriminant_of_the_symbol

section the_same_evidence_and_two_identifications
open readers_experience readers_interpretation_of_the_experience readers_interpretation_of_the_pair the_area

universe any

--| THE SAME EVIDENCE, AND TWO IDENTIFICATIONS.  Three pairs the device already has, set side by side, and each stated for
--| what is allowed to be read.  They are not one theorem about every description; each says what its own readers cannot
--| tell.

--| THE KNOWER'S BIT.  What is read: the triple's solver, and the quartic's two receipts.  The solver finds a witness with
--| the bit one way and with it the other; the receipts hold for the root given on a yes and for the root given on a no;
--| and the two roots are not one root.  The evidence is the same and the identification is not.
theorem the_knowers_bit_is_not_fixed_by_what_is_read :
    (satSearch the_knowers_triple an_odd_number_are_true 3 = true
        ∧ satSearch the_knowers_triple an_even_number_are_true 3 = true)
      ∧ (∀ you_do : FACT,
          (the_surd_product (you_re_a_daisy_if_you_do you_do) (you_re_a_daisy_if_you_do you_do)).1
              - 11664 * (you_re_a_daisy_if_you_do you_do).1 + 24564384 = 0
            ∧ (the_surd_product (you_re_a_daisy_if_you_do you_do) (you_re_a_daisy_if_you_do you_do)).2
              - 11664 * (you_re_a_daisy_if_you_do you_do).2 = 0)
      ∧ you_re_a_daisy_if_you_do (bitFACT true) ≠ you_re_a_daisy_if_you_do (bitFACT false) :=
  ⟨the_solver_finds_a_witness_either_way,
   fun you_do => ⟨(you_re_a_daisy_either_way you_do).1, (you_re_a_daisy_either_way you_do).2.1⟩,
   by decide⟩

--| THE TWO LADDERS.  What is read: the closures at the top, by any reader whatever.  Episode 12's ladder begins on the
--| truth and the other on a number distinguished, and the knower's alpha of each begins on its own first fact.  Every
--| reader of the two closures returns the same for the one ladder as for the other.
theorem every_reader_of_the_closures_reads_the_two_ladders_alike {what_is_read : Sort any} (reader : Closure → what_is_read) :
    reader the_other_conclusion = reader the_conclusion ∧ reader the_other_alpha = reader the_alpha :=
  ⟨congrArg reader asked_only_whether_it_is_true_the_two_ladders_carry_the_same_closures.1,
   congrArg reader asked_only_whether_it_is_true_the_two_ladders_carry_the_same_closures.2⟩

--| THE RECORD.  What is read: the readings at the places looked at.  For any finite list of places and any model there is
--| another that reads the same at every one of them and is not the same model.  And what is read of a tally is the same
--| for either carrier.
theorem the_record_and_the_tally_do_not_fix_it (places : List Nat) (the_model : Nat → Nat × Nat) :
    (∃ another_model : Nat → Nat × Nat,
        (∀ place, place ∈ places → another_model place = the_model place) ∧ another_model ≠ the_model)
      ∧ (∀ (reader : Nat → Bool) (carriers : TwoCarriers),
          reader (the_tally carriers.swap) = reader (the_tally carriers)) :=
  ⟨the_value_and_the_velocity_do_not_tell places the_model,
   fun reader carriers => no_reader_of_the_tally_sees_which_carrier reader carriers⟩
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
def the_square_of_three_in_a_row (n : Nat) : Int :=
  (the_closed_walks n : Int) * the_closed_walks (n + 2) - (the_closed_walks (n + 1) : Int) * the_closed_walks (n + 1)

theorem the_next_count_is_fixed_by_the_two_before (n : Nat) :
    (the_closed_walks (n + 2) : Int) = 36 * the_closed_walks (n + 1) - 234 * the_closed_walks n := by
  have h := the_closed_walks_obey_the_table n
  have t : the_trace = 36 := rfl
  have d : the_determinant = 234 := rfl
  rw [t, d] at h; omega

theorem the_square_of_three_is_multiplied_by_the_determinant (n : Nat) :
    the_square_of_three_in_a_row (n + 1) = 234 * the_square_of_three_in_a_row n := by
  have hc := the_next_count_is_fixed_by_the_two_before n
  have hd := the_next_count_is_fixed_by_the_two_before (n + 1)
  simp only [the_square_of_three_in_a_row]
  have e1 : (the_closed_walks (n + 2) : Int) * the_closed_walks (n + 2)
      = 36 * ((the_closed_walks (n + 1) : Int) * the_closed_walks (n + 2))
        - 234 * ((the_closed_walks n : Int) * the_closed_walks (n + 2)) := by
    have := congrArg (fun z => z * (the_closed_walks (n + 2) : Int)) hc
    simp only [Int.sub_mul, Int.mul_assoc] at this; exact this
  have e2 : (the_closed_walks (n + 1) : Int) * the_closed_walks (n + 1 + 2)
      = 36 * ((the_closed_walks (n + 1) : Int) * the_closed_walks (n + 2))
        - 234 * ((the_closed_walks (n + 1) : Int) * the_closed_walks (n + 1)) := by
    rw [hd, Int.mul_sub, Int.mul_left_comm, Int.mul_left_comm (the_closed_walks (n + 1) : Int) 234]
  rw [show n + 1 + 1 = n + 2 from rfl, e2, e1]; omega

theorem the_square_of_three_is_never_nothing : ∀ n : Nat, 0 < the_square_of_three_in_a_row n
  | 0 => by decide
  | n + 1 => by
    rw [the_square_of_three_is_multiplied_by_the_determinant]
    have := the_square_of_three_is_never_nothing n; omega
end two_counts_and_no_third

section three_ways_as_three_maps

--| THREE WAYS, AS THREE MAPS.  One table goes in.  Kept: it comes out as it went in.  Struck: the arm that does not click
--| is set to nothing.  Turned over: the arm that clicks on a falsehood, false on true, is owed.  On a table of a stay and
--| two crossings the three give the table itself, the table with nothing out, and the table with the way back owed.
def kept (table : Table) : Table := table
def struck (table : Table) : Table := fun a b => if a = true ∧ b = false then 0 else table a b
def turned_over (table : Table) : Table := fun a b => if a = false ∧ b = true then - table a b else table a b

theorem the_three_maps_on_a_stay_and_two_crossings (stay out back : Int) (a b : Bool) :
    struck (the_refinement_table stay out back) a b = the_refinement_table stay 0 back a b
      ∧ turned_over (the_refinement_table stay out back) a b = the_refinement_table stay out (- back) a b := by
  cases a <;> cases b <;> exact ⟨rfl, rfl⟩

--| And the gap squared of the three: four of the crossings, one by the other; nothing; and the same owed.  Where the
--| crossings are of one sign that is over nothing, nothing, and under nothing.
theorem the_gap_squared_of_the_three_ways (stay out back : Int) :
    the_gap_squared (kept (the_refinement_table stay out back)) = 4 * (out * back)
      ∧ the_gap_squared (struck (the_refinement_table stay out back)) = 0
      ∧ the_gap_squared (turned_over (the_refinement_table stay out back)) = - (4 * (out * back)) := by
  refine ⟨the_gap_squared_is_four_of_the_crossings stay out back, ?_, ?_⟩
  · rw [show struck (the_refinement_table stay out back) = the_refinement_table stay 0 back from
        funext fun a => funext fun b => (the_three_maps_on_a_stay_and_two_crossings stay out back a b).1,
      the_gap_squared_is_four_of_the_crossings, Int.zero_mul]; rfl
  · rw [show turned_over (the_refinement_table stay out back) = the_refinement_table stay out (- back) from
        funext fun a => funext fun b => (the_three_maps_on_a_stay_and_two_crossings stay out back a b).2,
      the_gap_squared_is_four_of_the_crossings, Int.mul_neg, Int.mul_neg]

--| The struck map moves only the arm that does not click, and the turned map only the arm that clicks on a falsehood.
theorem which_arm_each_map_moves (table : Table) (a b : Bool) :
    (struck table a b ≠ table a b → the_arm_stores_a_fact_that_can_click a b = false)
      ∧ (turned_over table a b ≠ table a b → a = false ∧ b = true) := by
  cases a <;> cases b <;> simp [struck, turned_over, the_arm_stores_a_fact_that_can_click]
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
def comes_round (steps : Nat) (reading : Nat → Int) : Prop := ∀ place, reading (place + steps) = reading place
def one_place_on (reading : Nat → Int) : Nat → Int := fun place => reading (place + 1)
def the_difference_along (reading : Nat → Int) : Nat → Int := fun place => reading (place + 1) - reading place

theorem one_place_on_comes_round (steps : Nat) (reading : Nat → Int) (round : comes_round steps reading) :
    comes_round steps (one_place_on reading) := fun place => by
  show reading (place + steps + 1) = reading (place + 1)
  rw [show place + steps + 1 = place + 1 + steps by omega]; exact round (place + 1)

theorem the_difference_comes_round (steps : Nat) (reading : Nat → Int) (round : comes_round steps reading) :
    comes_round steps (the_difference_along reading) := fun place => by
  show reading (place + steps + 1) - reading (place + steps) = reading (place + 1) - reading place
  rw [show place + steps + 1 = place + 1 + steps by omega, round (place + 1), round place]

theorem what_comes_round_closes (steps : Nat) (reading : Nat → Int) (round : comes_round steps reading) :
    reading steps = reading 0 := by
  have h := round 0; rwa [Nat.zero_add] at h

theorem by_parts_for_what_comes_round (steps : Nat) (this that : Nat → Int)
    (this_round : comes_round steps this) (that_round : comes_round steps that) :
    summed_along steps (fun place => this place * the_difference_along that place)
      = - summed_along steps (fun place => the_difference_along this place * one_place_on that place) := by
  have h := summation_by_parts_around_a_closed_walk steps that this
    (what_comes_round_closes steps that that_round) (what_comes_round_closes steps this this_round)
  have e1 : (fun place => that (place + 1) * (this (place + 1) - this place))
      = fun place => the_difference_along this place * one_place_on that place :=
    funext fun place => Int.mul_comm _ _
  have e2 : (fun place => this place * (that (place + 1) - that place))
      = fun place => this place * the_difference_along that place := rfl
  rw [e1, e2] at h; omega

--| THE FIRST VARIATION.  The bending energy of a reading is its second difference squared, summed.  Its first variation
--| against another reading is the two second differences one by the other, summed.  Around what comes round, that is the
--| fourth difference of the first against the second two places on.
theorem the_variation_of_the_bending_is_the_fourth_difference (steps : Nat) (bent other : Nat → Int)
    (bent_round : comes_round steps bent) (other_round : comes_round steps other) :
    summed_along steps (fun place =>
        the_difference_along (the_difference_along bent) place * the_difference_along (the_difference_along other) place)
      = summed_along steps (fun place =>
          the_difference_along (the_difference_along (the_difference_along (the_difference_along bent))) place
            * one_place_on (one_place_on other) place) := by
  have d1 := the_difference_comes_round steps bent bent_round
  have d2 := the_difference_comes_round steps _ d1
  have d3 := the_difference_comes_round steps _ d2
  have o1 := the_difference_comes_round steps other other_round
  have s1 := one_place_on_comes_round steps other other_round
  have first := by_parts_for_what_comes_round steps (the_difference_along (the_difference_along bent))
    (the_difference_along other) d2 o1
  have second := by_parts_for_what_comes_round steps
    (the_difference_along (the_difference_along (the_difference_along bent))) (one_place_on other) d3 s1
  have same : (fun place => the_difference_along (the_difference_along (the_difference_along bent)) place
        * one_place_on (the_difference_along other) place)
      = fun place => the_difference_along (the_difference_along (the_difference_along bent)) place
        * the_difference_along (one_place_on other) place := rfl
  rw [same] at first
  omega

--| And the fourth difference is the stencil: one, four owed, six, four owed, one.
theorem the_fourth_difference_is_the_stencil (reading : Nat → Int) (place : Nat) :
    the_difference_along (the_difference_along (the_difference_along (the_difference_along reading))) place
      = reading (place + 4) - 4 * reading (place + 3) + 6 * reading (place + 2) - 4 * reading (place + 1)
        + reading place := by
  simp only [the_difference_along, Nat.add_assoc, Nat.reduceAdd]; omega
end the_bending_energy_and_the_stencil

--#print axioms by_parts_for_what_comes_round
--#print axioms the_variation_of_the_bending_is_the_fourth_difference
--#print axioms the_fourth_difference_is_the_stencil

section the_bending_energy_assembled

--| THE BENDING ENERGY, ASSEMBLED.  The energy of a reading is its second difference squared, summed.  Of two readings, the
--| two second differences one by the other, summed.  Move a reading by a number of another: the energy moves by twice
--| that number of the two, and that number squared of the other's energy, and by nothing else.  The two belongs to the
--| energy; half the energy has the two together for its first variation.
def the_bending_energy (steps : Nat) (bent : Nat → Int) : Int :=
  summed_along steps fun place =>
    the_difference_along (the_difference_along bent) place * the_difference_along (the_difference_along bent) place
def the_bending_of_two (steps : Nat) (bent other : Nat → Int) : Int :=
  summed_along steps fun place =>
    the_difference_along (the_difference_along bent) place * the_difference_along (the_difference_along other) place

theorem a_number_of_a_reading_summed (steps : Nat) (number : Int) (reading : Nat → Int) :
    summed_along steps (fun place => number * reading place) = number * summed_along steps reading := by
  induction steps with
  | zero => show (0 : Int) = number * 0; omega
  | succ steps ih => simp only [summed_along, ih, Int.mul_add]

theorem the_second_difference_of_a_reading_moved (bent other : Nat → Int) (number : Int) (place : Nat) :
    the_difference_along (the_difference_along fun p => bent p + number * other p) place
      = the_difference_along (the_difference_along bent) place
        + number * the_difference_along (the_difference_along other) place := by
  simp only [the_difference_along, Int.mul_sub]; omega

theorem a_sum_squared (a number b : Int) :
    (a + number * b) * (a + number * b) = a * a + 2 * (number * (a * b)) + number * number * (b * b) := by
  rw [Int.add_mul, Int.mul_add, Int.mul_add]
  have e1 : a * (number * b) = number * (a * b) := Int.mul_left_comm _ _ _
  have e2 : number * b * a = number * (a * b) := by rw [Int.mul_assoc, Int.mul_comm b a]
  have e3 : number * b * (number * b) = number * number * (b * b) := two_by_two_is_one_by_one_twice _ _ _ _
  rw [e1, e2, e3]; omega

theorem the_bending_energy_of_a_reading_moved (steps : Nat) (bent other : Nat → Int) (number : Int) :
    the_bending_energy steps (fun place => bent place + number * other place)
      = the_bending_energy steps bent + 2 * (number * the_bending_of_two steps bent other)
        + number * number * the_bending_energy steps other := by
  simp only [the_bending_energy, the_bending_of_two]
  have pointwise : (fun place =>
        the_difference_along (the_difference_along fun p => bent p + number * other p) place
          * the_difference_along (the_difference_along fun p => bent p + number * other p) place)
      = fun place =>
        (the_difference_along (the_difference_along bent) place * the_difference_along (the_difference_along bent) place
          + 2 * (number * (the_difference_along (the_difference_along bent) place
              * the_difference_along (the_difference_along other) place)))
        + number * number * (the_difference_along (the_difference_along other) place
            * the_difference_along (the_difference_along other) place) :=
    funext fun place => by rw [the_second_difference_of_a_reading_moved, a_sum_squared]
  rw [pointwise, two_readings_summed_are_the_two_sums, two_readings_summed_are_the_two_sums,
    a_number_of_a_reading_summed steps (number * number), a_number_of_a_reading_summed steps 2,
    a_number_of_a_reading_summed steps number]

--| WHAT COMES ROUND, AND WHAT CLIMBS.  The stencil is nothing on a cubic in the place, at every place: that is Episode
--| 12's, and it is about one place and its neighbours.  The energy above is summed round a walk, and a reading that climbs
--| does not come round.  They are two statements and are kept two.
theorem a_reading_that_climbs_does_not_come_round (steps : Nat) (round : comes_round steps (fun place => (place : Int))) :
    steps = 0 := by
  have h := round 0
  simp only [Nat.zero_add] at h
  omega

--| STATIONARY, AT EVERY PLACE.  Let a reading come round a walk of some steps, and let the two together be nothing against
--| every reading that comes round.  Then its fourth difference, the stencil, is nothing at every place.
theorem what_comes_round_comes_round_again (steps : Nat) (reading : Nat → Int) (round : comes_round steps reading) :
    ∀ (times place : Nat), reading (place + times * steps) = reading place
  | 0, place => by rw [Nat.zero_mul, Nat.add_zero]
  | times + 1, place => by
    rw [Nat.succ_mul, ← Nat.add_assoc, round, what_comes_round_comes_round_again steps reading round times place]

theorem squares_summed_are_never_under_nothing (steps : Nat) (reading : Nat → Int) :
    0 ≤ summed_along steps (fun place => reading place * reading place) := by
  induction steps with
  | zero => exact Int.le_refl 0
  | succ steps ih =>
    have sq := a_square_is_never_under_nothing (reading steps)
    simp only [summed_along]; omega

theorem squares_that_sum_to_nothing_are_each_nothing (steps : Nat) (reading : Nat → Int)
    (nothing : summed_along steps (fun place => reading place * reading place) = 0) :
    ∀ place, place < steps → reading place = 0 := by
  induction steps with
  | zero => intro place h; omega
  | succ steps ih =>
    have before := squares_summed_are_never_under_nothing steps reading
    have sq := a_square_is_never_under_nothing (reading steps)
    simp only [summed_along] at nothing
    have last : reading steps * reading steps = 0 := by omega
    have rest : summed_along steps (fun place => reading place * reading place) = 0 := by omega
    intro place h
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with below | here
    · exact ih rest place below
    · rw [here]; rcases Int.mul_eq_zero.mp last with z | z <;> exact z

theorem stationary_against_all_that_comes_round_is_the_stencil_nothing (steps : Nat) (positive : 0 < steps)
    (bent : Nat → Int) (bent_round : comes_round steps bent)
    (stationary : ∀ other, comes_round steps other → the_bending_of_two steps bent other = 0) :
    ∀ place, the_difference_along (the_difference_along (the_difference_along (the_difference_along bent))) place = 0 := by
  have d4 := the_difference_comes_round steps _ (the_difference_comes_round steps _
    (the_difference_comes_round steps _ (the_difference_comes_round steps bent bent_round)))
  let fourth := the_difference_along (the_difference_along (the_difference_along (the_difference_along bent)))
  let other : Nat → Int := fun place => fourth (place + (2 * steps - 2))
  have other_round : comes_round steps other := fun place => by
    show fourth (place + steps + (2 * steps - 2)) = fourth (place + (2 * steps - 2))
    rw [show place + steps + (2 * steps - 2) = place + (2 * steps - 2) + steps by omega]; exact d4 _
  have two_on : ∀ place, one_place_on (one_place_on other) place = fourth place := fun place => by
    show fourth (place + 1 + 1 + (2 * steps - 2)) = fourth place
    rw [show place + 1 + 1 + (2 * steps - 2) = place + 2 * steps by omega]
    exact what_comes_round_comes_round_again steps fourth d4 2 place
  have h := stationary other other_round
  rw [the_bending_of_two, the_variation_of_the_bending_is_the_fourth_difference steps bent other bent_round other_round] at h
  have squares : summed_along steps (fun place => fourth place * fourth place) = 0 := by
    have same : (fun place => the_difference_along (the_difference_along (the_difference_along (the_difference_along bent))) place
          * one_place_on (one_place_on other) place) = fun place => fourth place * fourth place :=
      funext fun place => by rw [two_on]
    rw [same] at h; exact h
  have inside := squares_that_sum_to_nothing_are_each_nothing steps fourth squares
  intro place
  have again := what_comes_round_comes_round_again steps fourth d4 (place / steps) (place % steps)
  rw [Nat.mul_comm, Nat.mod_add_div] at again
  rw [show the_difference_along (the_difference_along (the_difference_along (the_difference_along bent))) place
        = fourth place from rfl, again]
  exact inside _ (Nat.mod_lt _ positive)
end the_bending_energy_assembled

--#print axioms the_bending_energy_of_a_reading_moved
--#print axioms a_reading_that_climbs_does_not_come_round
--#print axioms stationary_against_all_that_comes_round_is_the_stencil_nothing

section what_can_be_recovered
open readers_experience readers_interpretation_of_the_experience the_area

universe cases evidences identifications

--| WHAT CAN BE RECOVERED.  Cases, some of them admissible.  What is kept of a case: the evidence.  What is to be got back:
--| the identification.  A reader of the evidence recovers the identification when it returns it for every admissible case.
--| The identification can be recovered when some reader does.  Nothing is asked of the reader but that it is a function.
def recovers {Case : Sort cases} {Evidence : Sort evidences} {Identification : Sort identifications}
    (admissible : Case → Prop) (what_is_kept : Case → Evidence) (identify : Case → Identification)
    (reader : Evidence → Identification) : Prop :=
  ∀ case, admissible case → reader (what_is_kept case) = identify case
def can_be_recovered {Case : Sort cases} {Evidence : Sort evidences} {Identification : Sort identifications}
    (admissible : Case → Prop) (what_is_kept : Case → Evidence) (identify : Case → Identification) : Prop :=
  ∃ reader, recovers admissible what_is_kept identify reader

--| THE OBSTRUCTION.  Two admissible cases of which the same is kept, and which are identified differently: then no reader
--| of what is kept recovers the identification.  The reader is handed one thing twice and cannot return two.
theorem the_same_kept_and_two_identifications_cannot_be_recovered
    {Case : Sort cases} {Evidence : Sort evidences} {Identification : Sort identifications}
    (admissible : Case → Prop) (what_is_kept : Case → Evidence) (identify : Case → Identification)
    (this that : Case) (this_is_admissible : admissible this) (that_is_admissible : admissible that)
    (the_same_is_kept : what_is_kept this = what_is_kept that) (identified_apart : identify this ≠ identify that) :
    ¬ can_be_recovered admissible what_is_kept identify := by
  intro ⟨reader, it_recovers⟩
  have here := it_recovers this this_is_admissible
  have there := it_recovers that that_is_admissible
  rw [the_same_is_kept] at here
  exact identified_apart (here.symm.trans there)

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

theorem the_knowers_decision_cannot_be_recovered :
    ¬ can_be_recovered (fun _ : Bool => True) what_is_kept_of_a_decision (fun decision => decision) :=
  the_same_kept_and_two_identifications_cannot_be_recovered _ _ _ true false trivial trivial
    the_same_is_kept_of_both_decisions (by decide)

--| And the two decisions return two roots.
theorem the_two_decisions_return_two_roots :
    you_re_a_daisy_if_you_do (bitFACT true) ≠ you_re_a_daisy_if_you_do (bitFACT false) := by decide

--| THE TWO FIRST RUNGS.  The cases are two names, the old rung and the new.  What is kept of a name is the fact it names:
--| the truth, or a number distinguished.  The two facts are one fact, asked only whether it is true.  So the name cannot
--| be recovered from the fact, nor from anything read off the fact.
def the_fact_a_name_names (the_old_rung : Bool) : FACT :=
  if the_old_rung then FACT.Truth else a_number_is_distinguished

theorem the_name_of_the_first_rung_cannot_be_recovered :
    ¬ can_be_recovered (fun _ : Bool => True) the_fact_a_name_names (fun the_old_rung => the_old_rung) :=
  the_same_kept_and_two_identifications_cannot_be_recovered _ _ _ true false trivial trivial
    (show FACT.Truth = a_number_is_distinguished from asked_only_whether_it_is_true_the_number_is_the_truth.symm)
    (by decide)
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
theorem the_quartic_at_the_devices_weights (x r : Int) :
    the_closing_quartic 18 5 x r = 325 * (x * x) - 180 * (r * r * x) + 18 * (r * r * (r * r)) := by
  show (5 : Int) * 5 * (18 - 5) * x * x - 2 * 18 * 5 * r * r * x + 18 * r * r * r * r = _
  have e1 : (5 : Int) * 5 * (18 - 5) * x * x = 325 * (x * x) := by
    rw [show (5 : Int) * 5 * (18 - 5) = 325 from rfl]; ac_nf
  have e2 : (2 : Int) * 18 * 5 * r * r * x = 180 * (r * r * x) := by
    rw [show (2 : Int) * 18 * 5 = 180 from rfl]; ac_nf
  have e3 : (18 : Int) * r * r * r * r = 18 * (r * r * (r * r)) := by ac_nf
  rw [e1, e2, e3]

theorem eighteen_of_the_quartic_is_a_pair_by_itself_turned_over (x r : Int) :
    the_surd_product (18 * (r * r - 5 * x), 5 * x) (18 * (r * r - 5 * x), - (5 * x))
      = (18 * the_closing_quartic 18 5 x r, 0) := by
  have ninety := the_round_trip_is_ninety
  refine Prod.ext ?_ ?_
  · show 18 * (r * r - 5 * x) * (18 * (r * r - 5 * x)) + the_round_trip * (5 * x) * (- (5 * x))
        = 18 * the_closing_quartic 18 5 x r
    rw [ninety, the_quartic_at_the_devices_weights, Int.mul_neg]
    have a1 : 18 * (r * r - 5 * x) * (18 * (r * r - 5 * x))
        = 18 * 18 * ((r * r - 5 * x) * (r * r - 5 * x)) := two_by_two_is_one_by_one_twice _ _ _ _
    have a2 : (r * r - 5 * x) * (r * r - 5 * x)
        = r * r * (r * r) - 10 * (r * r * x) + 25 * (x * x) := by
      rw [Int.sub_mul, Int.mul_sub, Int.mul_sub]
      have b1 : r * r * (5 * x) = 5 * (r * r * x) := Int.mul_left_comm _ _ _
      have b2 : 5 * x * (r * r) = 5 * (r * r * x) := by rw [Int.mul_assoc, Int.mul_comm x (r * r)]
      have b3 : 5 * x * (5 * x) = 5 * 5 * (x * x) := two_by_two_is_one_by_one_twice _ _ _ _
      rw [b1, b2, b3]; omega
    have a3 : (90 : Int) * (5 * x) * (5 * x) = 90 * (5 * 5 * (x * x)) := by
      rw [Int.mul_assoc, two_by_two_is_one_by_one_twice]
    rw [a1, a2, a3]; omega
  · show 18 * (r * r - 5 * x) * (- (5 * x)) + 5 * x * (18 * (r * r - 5 * x)) = 0
    rw [Int.mul_neg, Int.mul_comm (5 * x) (18 * (r * r - 5 * x))]; omega

--| Turned over, the two pairs change places and the product is the same.
theorem the_two_pairs_change_places_and_the_product_stays (x r : Int) :
    the_surd_product (18 * (r * r - 5 * x), - (5 * x)) (18 * (r * r - 5 * x), 5 * x)
      = the_surd_product (18 * (r * r - 5 * x), 5 * x) (18 * (r * r - 5 * x), - (5 * x)) := by
  refine Prod.ext ?_ ?_
  · show 18 * (r * r - 5 * x) * (18 * (r * r - 5 * x)) + the_round_trip * (- (5 * x)) * (5 * x)
        = 18 * (r * r - 5 * x) * (18 * (r * r - 5 * x)) + the_round_trip * (5 * x) * (- (5 * x))
    rw [Int.mul_neg, Int.neg_mul, Int.mul_neg]
  · show 18 * (r * r - 5 * x) * (5 * x) + - (5 * x) * (18 * (r * r - 5 * x))
        = 18 * (r * r - 5 * x) * (- (5 * x)) + 5 * x * (18 * (r * r - 5 * x))
    rw [Int.mul_neg, Int.neg_mul, Int.mul_comm (5 * x) (18 * (r * r - 5 * x))]; omega
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
theorem the_table_turned_over_reads_the_same :
    the_table_trace the_full_other_table = the_table_trace the_full_table
      ∧ the_table_determinant the_full_other_table = the_table_determinant the_full_table
      ∧ the_gap_squared the_full_other_table = the_gap_squared the_full_table
      ∧ the_gap_squared the_full_table = 360 := by decide

--| And what changes sign is the bent card by the quarter turn: the arm's thirteen, with a direction.
theorem turned_over_the_bent_card_by_the_quarter_turn_is_owed (a b : Bool) :
    the_full_other_table a b - the_full_table a b = - ((bent_card : Int) * the_quarter_turn a b) := by
  cases a <;> cases b <;> decide

--| The roots in either order add to the trace and multiply to the determinant.
theorem the_roots_changed_places_read_the_same :
    the_surd_product the_hole the_outer_radius = the_surd_product the_outer_radius the_hole
      ∧ the_surd_product the_outer_radius the_hole = (234, 0)
      ∧ (the_hole.1 + the_outer_radius.1, the_hole.2 + the_outer_radius.2) = (36, 0)
      ∧ the_hole.2 = - the_outer_radius.2 := by decide

--| FOUR STATES, ONE READING.  A root first and a table: four ways.  What is read of each, the trace, the determinant and
--| the gap squared of the table and the sum and the product of the two roots, is the same for all four.
def the_four_signed_states : List (Bool × Bool) := [(true, true), (true, false), (false, true), (false, false)]
def what_is_read_of_a_signed_state (state : Bool × Bool) : Int × Int × Int × (Int × Int) × (Int × Int) :=
  let table := if state.2 then the_full_table else the_full_other_table
  let first := if state.1 then the_outer_radius else the_hole
  let second := if state.1 then the_hole else the_outer_radius
  (the_table_trace table, the_table_determinant table, the_gap_squared table,
   (first.1 + second.1, first.2 + second.2), the_surd_product first second)

theorem the_four_signed_states_read_alike :
    the_four_signed_states.map what_is_read_of_a_signed_state
      = List.replicate 4 (36, 234, 360, (36, 0), (234, 0)) := by decide

--| THE ONE CONSTRAINT THERE IS.  The knower's triple sets the knower's coin against whether the arm's two coins differ.
--| It does not read which way they differ: true on false and false on true are one to it, under either parity.  So it
--| ties the knower's coin to a crossing, and not to the crossing's direction.
theorem the_triple_does_not_read_which_way_the_arm_crosses :
    ∀ a : Bool,
      (the_knowers_triple.holds (assignFrom [a, true, false]) an_odd_number_are_true 0).1
          = (the_knowers_triple.holds (assignFrom [a, false, true]) an_odd_number_are_true 0).1
        ∧ (the_knowers_triple.holds (assignFrom [a, true, false]) an_even_number_are_true 0).1
          = (the_knowers_triple.holds (assignFrom [a, false, true]) an_even_number_are_true 0).1 := by decide
end two_reversals


section the_mirror_the_turn_and_the_spinor
open readers_experience

--| THE MIRROR, THE TURN AND THE SPINOR.  Asked how the two reversals are paired, the author answered with three things
--| done: the mirror projection, the rotation in two dimensions, and the spinor's rotation, the last being the arrow of
--| time.  The first is the table turned over.  The second is the table carried by the quarter turn.  The third is the sign
--| the table does not see.

--| The table carried by the quarter turn: the quarter turn, the table, and the quarter turn back.
def carried_by_the_quarter_turn (A : Table) : Table :=
  fun a b => - the_table_product (the_table_product the_quarter_turn A) the_quarter_turn a b

--| Carried, it reads as it did.
theorem carried_by_the_quarter_turn_the_table_reads_the_same :
    the_table_trace (carried_by_the_quarter_turn the_full_table) = 36
      ∧ the_table_determinant (carried_by_the_quarter_turn the_full_table) = 234
      ∧ the_gap_squared (carried_by_the_quarter_turn the_full_table) = 360 := by decide

--| What it is: the table turned over, with both crossings owed.
theorem carried_by_the_quarter_turn_it_is_turned_over_and_the_crossings_are_owed :
    ∀ a b : Bool, carried_by_the_quarter_turn the_full_table a b
      = if a = b then the_full_other_table a b else - the_full_other_table a b := by decide

--| Carried twice, it is back.  On the table the quarter turn is done twice and nothing is owed.
theorem carried_twice_the_table_is_back :
    ∀ a b : Bool, carried_by_the_quarter_turn (carried_by_the_quarter_turn the_full_table) a b = the_full_table a b := by
  decide

--| In the turns it is not back.  The quarter turn twice is the whole turn owed, and the quarter turn turned over is itself
--| owed.  This is the sign the table does not see.
theorem in_the_turns_the_quarter_turn_twice_is_the_whole_turn_owed :
    the_turns_product the_quarter_turn_turn the_quarter_turn_turn = the_whole_turn (-1)
      ∧ the_turns_conjugate the_quarter_turn_turn
          = the_turns_product (the_whole_turn (-1)) the_quarter_turn_turn := by decide

--| It is not the roots changing places.  Owed whole, the outer radius is not the hole: the eighteen is owed with it.
theorem the_outer_radius_owed_is_not_the_hole :
    (- the_outer_radius.1, - the_outer_radius.2) ≠ the_hole
      ∧ (the_outer_radius.1, - the_outer_radius.2) = the_hole := by decide

--| The place that is not on the frinkahedron is the one where neither sample holds a bracket.
theorem the_place_off_the_frinkahedron_holds_no_bracket :
    (the_arms.filter fun place => !on_the_frinkahedron place) = [(false, false)] := by decide
end the_mirror_the_turn_and_the_spinor


section eight_expressions_to_check
open readers_experience the_area the_area.Account

--| EIGHT EXPRESSIONS TO CHECK.  The author's, 18 November 2026: one choice, two hypotheses, four proposals, eight logical
--| expressions to check; each proposal under each hypothesis (declared).  The device's eight are the clocks of the
--| connected steps, and a clock is a coin and an arm.

--| The eight, in order: the two coins by the four arms.
theorem the_eight_are_a_coin_and_an_arm :
    the_connected_steps.map the_clock_of_a_step
      = the_two_coins.flatMap fun coin => the_arms.map fun arm => (coin, arm.1, arm.2) := by decide

--| What the knower's triple says of a clock, under each parity.
def the_clock_holds_when_an_odd_number_are_true (clock : Bool × Bool × Bool) : Bool :=
  (the_knowers_triple.holds (assignFrom [clock.1, clock.2.1, clock.2.2]) an_odd_number_are_true 0).1
def the_clock_holds_when_an_even_number_are_true (clock : Bool × Bool × Bool) : Bool :=
  (the_knowers_triple.holds (assignFrom [clock.1, clock.2.1, clock.2.2]) an_even_number_are_true 0).1

--| Four hold and four do not, under either parity, and what holds under the one does not under the other.
theorem four_of_the_eight_hold_and_four_do_not :
    ((the_connected_steps.map the_clock_of_a_step).filter the_clock_holds_when_an_odd_number_are_true).length = 4
      ∧ ((the_connected_steps.map the_clock_of_a_step).filter the_clock_holds_when_an_even_number_are_true).length = 4
      ∧ ∀ clock ∈ the_connected_steps.map the_clock_of_a_step,
          the_clock_holds_when_an_odd_number_are_true clock = !the_clock_holds_when_an_even_number_are_true clock := by
  decide

--| For every arm, one coin holds and the other does not.
theorem for_every_arm_one_coin_holds :
    ∀ arm ∈ the_arms,
      the_clock_holds_when_an_odd_number_are_true (true, arm.1, arm.2)
        = !the_clock_holds_when_an_odd_number_are_true (false, arm.1, arm.2) := by decide

--| Which: when an odd number are true, the coin that holds is true where the arm's two coins are the same.
theorem the_coin_that_holds_is_whether_the_arm_is_level :
    the_arms.map (fun arm => the_clock_holds_when_an_odd_number_are_true (true, arm.1, arm.2))
      = the_arms.map (fun arm => arm.1 == arm.2) := by decide
end eight_expressions_to_check

section the_turn_in_space_and_the_turn_in_time
open readers_experience the_area the_area.Account

--| THE TURN IN SPACE AND THE TURN IN TIME.  The author's, 18 November 2026: you can turn the coin spatially, you cannot
--| turn the coin temporally; that is the arrow of time deflated (declared).  On a connected step there are two things to
--| do.  Turn every coin over: the turn in space.  Read the step from its end, the after clause backwards and then the
--| before clause backwards: the turn in time.

def turned_in_space (step : (Bool × Bool) × (Bool × Bool)) : (Bool × Bool) × (Bool × Bool) :=
  ((!step.1.1, !step.1.2), (!step.2.1, !step.2.2))
def turned_in_time (step : (Bool × Bool) × (Bool × Bool)) : (Bool × Bool) × (Bool × Bool) :=
  ((step.2.2, step.2.1), (step.1.2, step.1.1))

--| What execute counts less what compile builds: nothing where the step is level, the bent card where it is over, the
--| bent card owed where it is short.
def over_or_short (step : (Bool × Bool) × (Bool × Bool)) : Int :=
  (cells (what_execute_counts step) : Int) - cells (what_compile_builds step)

--| Either way turned, a connected step is a connected step.
theorem turned_either_way_a_connected_step_is_connected :
    ((the_connected_steps.map turned_in_space).all fun step => the_connected_steps.contains step) = true
      ∧ ((the_connected_steps.map turned_in_time).all fun step => the_connected_steps.contains step) = true := by decide

--| The clock and its complement: true, false, true and false, true, false.  The one is over by the bent card and the other
--| short by it.
def the_clock_step : (Bool × Bool) × (Bool × Bool) := ((true, false), (false, true))
def the_complement_step : (Bool × Bool) × (Bool × Bool) := ((false, true), (true, false))

theorem the_clock_is_over_by_the_bent_card_and_its_complement_is_short :
    over_or_short the_clock_step = bent_card ∧ over_or_short the_complement_step = - (bent_card : Int) := by decide

--| Turned in space the clock is its complement, and the bent card is owed.
theorem turned_in_space_the_clock_is_its_complement :
    turned_in_space the_clock_step = the_complement_step ∧ turned_in_space the_complement_step = the_clock_step
      ∧ over_or_short (turned_in_space the_clock_step) = - over_or_short the_clock_step := by decide

--| Turned in time the clock is the clock.  Nothing is owed and nothing has changed places.
theorem turned_in_time_the_clock_is_the_clock :
    turned_in_time the_clock_step = the_clock_step ∧ turned_in_time the_complement_step = the_complement_step := by decide

--| And only these two, of the steps that are over or short, are left as they were by the turn in time.
theorem the_turn_in_time_leaves_what_is_read_only_of_the_clock_and_its_complement :
    (the_connected_steps.filter fun step =>
        over_or_short step != 0 && over_or_short (turned_in_time step) == over_or_short step)
      = [the_clock_step, the_complement_step] := by decide
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
def by_their_differences (this that : Direction → Int) : Int :=
  (the_pairs_of_arms.map fun pair => (this pair.1 - this pair.2) * (that pair.1 - that pair.2)).foldl (· + ·) 0

--| The two areas' rises: the weight the arm stores, and one fencepost on every arm.
def the_weight_on_the_arm (arm : Direction) : Int := the_arm_weight arm.1 arm.2
def one_fencepost_on_the_arm (_ : Direction) : Int := 1

--| One fencepost on every arm has no differences: against itself it reads nothing, and against the weight nothing.
theorem one_fencepost_on_every_arm_is_at_right_angles_to_the_weight :
    by_their_differences one_fencepost_on_the_arm the_weight_on_the_arm = 0
      ∧ by_their_differences one_fencepost_on_the_arm one_fencepost_on_the_arm = 0 := by decide

--| And against anything: it has no differences to read.
theorem one_fencepost_on_every_arm_is_at_right_angles_to_everything (that : Direction → Int) :
    by_their_differences one_fencepost_on_the_arm that = 0 := by
  simp only [by_their_differences, the_pairs_of_arms, one_fencepost_on_the_arm, List.map, List.foldl]
  omega

--| The weight against itself is three bent cards squared: the three arms that click, each over the fourth by the bent card.
theorem the_weight_by_its_differences_is_three_bent_cards_squared :
    by_their_differences the_weight_on_the_arm the_weight_on_the_arm = 3 * ((bent_card : Int) * bent_card) := by decide
end the_two_areas_at_right_angles


section the_reviewers_named_rung
open readers_experience the_area

--| THE REVIEWER'S NAMED RUNG.  The author's, 18 November 2026: the thirty-six subjunctive equalities are the reviewer's
--| named rungs of Episode 10; it is a statement of finite 3SAT up to thirty-six triples; the fencepost here is four and
--| not five; and that is the difference between the fencepost counting up and the fencepost counting down, the same
--| difference of the quantum (declared).  Episode 10 makes a page by `rebut planted polynomial argument`: two facts and the
--| page before.  The page it makes is a methodology, which holds those two facts, two boxes, and the page before.

--| A page read all the way down is its two facts and then the page before.
theorem a_page_is_two_facts_and_the_page_before (planted polynomial : FACT) (the_page_before : ThePreprint.{0}) :
    (ThePreprint.methodology planted polynomial Prop Type the_page_before).all_the_way_down
      = [planted, polynomial] ++ the_page_before.all_the_way_down := rfl

--| Dealt from a tape, a preprint read all the way down is two facts a page and one more.
theorem two_facts_a_page_and_one_more (tape : List FACT) :
    (the_preprint_a_list_indicates tape).all_the_way_down.length = 2 * tape.length + 1 := by
  induction tape with
  | nil => rfl
  | cons fact rest ih =>
    simp only [the_preprint_a_list_indicates, ThePreprint.all_the_way_down, List.length_append, List.length_cons,
      List.length_nil, ih]
    omega

--| Thirty-five rebuttals are thirty-six pages: the page handed in is the fencepost.  And they are seventy-one facts.
theorem thirty_five_rebuttals_are_thirty_six_pages :
    (the_preprint_a_list_indicates (List.replicate 35 FACT.Truth)).the_model.length = 36
      ∧ (the_preprint_a_list_indicates (List.replicate 35 FACT.Truth)).all_the_way_down.length = 71 := by
  rw [the_preprint_reads_back, two_facts_a_page_and_one_more]; simp only [List.length_replicate]; decide

--| Counted up there is one more than counted down: the pages are the rebuttals and the fencepost.
theorem counted_up_is_counted_down_and_the_fencepost (tape : List FACT) :
    (the_preprint_a_list_indicates tape).the_model.length = tape.length + the_fencepost_bug := by
  rw [the_preprint_reads_back]; show 1 * tape.length + 1 = tape.length + 1; omega
end the_reviewers_named_rung


section counted_down_and_counted_up
open readers_experience «springer-verlag» THE_GOSPEL

--| COUNTED DOWN AND COUNTED UP.  Episode 10 counts down: a page is made from the page after it, by `rebut`, and holds two
--| facts, the one handed in and the one searched for.  Episode 11 counts up: a page is set in type on the page below it, and
--| what it sets is the reviewer's page of the same number.  Here is what is set: the two facts, and the proposition that
--| the two agree.  That proposition is the subjunctive equality.

--| What the reviewer's page holds: the two facts, the box, the box lifted, and the page it answers.
theorem what_a_rebuttal_holds {Box : Type} {Pigeon : CarrierProcess Box} {page next_page : Nat}
    (planted polynomial : FACT) (argument : REVIEWED Box Pigeon next_page) :
    (rebut (page := page) planted polynomial argument).rebuttal
      = .methodology planted polynomial Box (ULift.{1, 0} Box) argument.rebuttal := rfl

--| Set in type, the page is the two facts and the proposition that the two agree, on the page below.
theorem set_in_type_a_rebuttal_is_its_two_facts_and_that_they_agree
    {Box : Type} {Pigeon : CarrierProcess Box} {page next_page rung : Nat} {Lifted : Type}
    (planted polynomial : FACT) (argument : REVIEWED Box Pigeon next_page) (accepted : TYPESET Box Pigeon rung Lifted) :
    (set_in_type (rebut (page := page) planted polynomial argument).rebuttal accepted).the_page
      = .results planted polynomial (planted.truth ↔ polynomial.truth) Box (ULift.{1, 0} Box)
          (ULift.{1, 1} (ULift.{1, 0} Box)) accepted.the_page := rfl

--| And the count goes up by one: the universe id of the page is one more on the page below's.
theorem set_in_type_the_count_goes_up_by_one
    {Box : Type} {Pigeon : CarrierProcess Box} {rung : Nat} {Lifted : Type}
    (the_rebuttal : ThePreprint) (accepted : TYPESET Box Pigeon rung Lifted) :
    (set_in_type the_rebuttal accepted).universe_id = .one Pigeon.symbol accepted.universe_id := rfl

--| THREE AND TWO.  Read all the way down, a page counted down is two facts and a page counted up is three: the two, and
--| the truth standing for the proposition that they agree.  The third is the one that is taken as given.
theorem counted_up_a_page_is_three_facts_and_counted_down_two
    (planted polynomial : FACT) (agree : Prop) (below : ThePreprint.{0}) :
    (ThePreprint.results planted polynomial agree Prop Type Type below).all_the_way_down
        = [planted, polynomial, FACT.Truth] ++ below.all_the_way_down
      ∧ (ThePreprint.methodology planted polynomial Prop Type below).all_the_way_down
        = [planted, polynomial] ++ below.all_the_way_down := ⟨rfl, rfl⟩

--| THE FENCEPOST.  A page that names one fact twice sets a proposition that holds of itself: nothing is inferred.
theorem one_fact_twice_agrees_and_nothing_is_inferred (fact : FACT) : fact.truth ↔ fact.truth := Iff.rfl

--| A page that names two facts sets a proposition that the two facts must supply: there are two facts that do not agree.
theorem two_facts_need_not_agree : ∃ planted polynomial : FACT, ¬ (planted.truth ↔ polynomial.truth) :=
  ⟨{ truth := True, click := .isTrue trivial }, { truth := False, click := .isFalse id }, fun agree => agree.mp trivial⟩

--| And where both hold, they agree: the equality is inferred from the two facts.
theorem two_facts_that_hold_agree (planted polynomial : FACT) (the_one : planted.truth) (the_other : polynomial.truth) :
    planted.truth ↔ polynomial.truth := ⟨fun _ => the_other, fun _ => the_one⟩
end counted_down_and_counted_up


section two_computations_on_one_encoding
open readers_experience the_review_on_the_ledger

--| TWO COMPUTATIONS ON ONE ENCODING.  The author's, 18 November 2026: there are two different computations on the same
--| encoding (declared).  Episode 12 has both, on the first card: the review counted down from the manuscript to the first
--| page, every reviewer asked, and the ascent counted up from that first page to the thirty-sixth, found by search.  The
--| encoding is the one preprint.  Here are the two, read all the way down.

--| The manuscript handed in is three facts.
theorem the_manuscript_is_three_facts : theManuscript.all_the_way_down.length = 3 := by decide

--| Counted down: thirty-five rebuttals on the manuscript, two facts each.
theorem counted_down_the_review_is_two_facts_a_page_on_the_manuscript :
    page01.rebuttal.all_the_way_down.length = 2 * 35 + theManuscript.all_the_way_down.length := by decide

--| Counted up: thirty-five pages set in type on the review, three facts each.
set_option maxRecDepth 100000 in
theorem counted_up_the_ascent_is_three_facts_a_page_on_the_review :
    theTopOfTheLedger.the_page.all_the_way_down.length = 3 * 35 + page01.rebuttal.all_the_way_down.length := by decide

--| So the second computation is written on top of the first, and what it adds, less what the first added, is one fact a
--| page: thirty-five agreements.
set_option maxRecDepth 100000 in
theorem the_ascent_adds_one_fact_a_page_more_than_the_review :
    (theTopOfTheLedger.the_page.all_the_way_down.length - page01.rebuttal.all_the_way_down.length)
      - (page01.rebuttal.all_the_way_down.length - theManuscript.all_the_way_down.length) = 35 := by decide

--| In pages: the manuscript is two, the review thirty-five more, the ascent thirty-five more again.
set_option maxRecDepth 100000 in
theorem in_pages_each_computation_is_thirty_five :
    theManuscript.the_model.length = 2
      ∧ page01.rebuttal.the_model.length = 35 + theManuscript.the_model.length
      ∧ theTopOfTheLedger.the_page.the_model.length = 35 + page01.rebuttal.the_model.length := by decide

--| And the ascent stands on the review: its first page is the reviewer's first page.
theorem the_ascent_stands_on_the_review :
    (THE_GOSPEL.TYPESET_Episode1_FACT FACT the_representation.the_first_card (the_naotrino_theory := page01)).the_page
      = page01.rebuttal := rfl
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
theorem the_action_in_first_differences_varies_by_the_second (steps : Nat) (reading moved : Nat → Int)
    (reading_round : comes_round steps reading) (moved_round : comes_round steps moved) :
    summed_along steps (fun place => the_difference_along reading place * the_difference_along moved place)
      = - summed_along steps
          (fun place => the_difference_along (the_difference_along reading) place * one_place_on moved place) :=
  by_parts_for_what_comes_round steps (the_difference_along reading) moved
    (the_difference_comes_round steps reading reading_round) moved_round

theorem the_second_difference_reads_three_places (reading : Nat → Int) (place : Nat) :
    the_difference_along (the_difference_along reading) place
      = reading (place + 1 + 1) - 2 * reading (place + 1) + reading place := by
  simp only [the_difference_along]; omega

--| The asymptote.  The factor squared, by what is left of the whole when the part is taken, is the whole.  Take the whole
--| and there is no factor.
theorem at_the_speed_of_one_there_is_no_factor (whole : Int) (not_nothing : whole ≠ 0) :
    ¬ ∃ factor_squared : Int, (whole - whole) * factor_squared = whole := by
  intro ⟨factor_squared, held⟩; simp at held; exact not_nothing held.symm

--| THE SECOND.  The third difference on four steps: i-2, i-1, i and i+1.
def the_third_difference_on_four_steps (reading : Int → Int) (place : Int) : Int :=
  reading (place + 1) - 3 * reading place + 3 * reading (place - 1) - reading (place - 2)

--| Shifted, it is the same function at the shifted place.
theorem shifted_the_third_difference_is_itself_at_the_shifted_place (reading : Int → Int) (by_this place : Int) :
    the_third_difference_on_four_steps (fun x => reading (x + by_this)) place
      = the_third_difference_on_four_steps reading (place + by_this) := by
  simp only [the_third_difference_on_four_steps]
  have h1 : place + 1 + by_this = place + by_this + 1 := by omega
  have h2 : place - 1 + by_this = place + by_this - 1 := by omega
  have h3 : place - 2 + by_this = place + by_this - 2 := by omega
  rw [h1, h2, h3]

--| Turned end for end, it is owed, at the place turned.
theorem turned_end_for_end_the_third_difference_is_owed (reading : Int → Int) (place : Int) :
    the_third_difference_on_four_steps (fun x => reading (- x)) place
      = - the_third_difference_on_four_steps reading (1 - place) := by
  simp only [the_third_difference_on_four_steps]
  have h1 : -(place + 1) = 1 - place - 2 := by omega
  have h2 : -place = 1 - place - 1 := by omega
  have h3 : -(place - 1) = 1 - place := by omega
  have h4 : -(place - 2) = 1 - place + 1 := by omega
  rw [h1, h2, h3, h4]; omega

--| The fourth difference is the step of the third: a reading is stationary where the third difference does not step.
theorem the_fourth_difference_is_the_step_of_the_third (reading : Int → Int) (place : Int) :
    the_fourth_difference reading place
      = the_third_difference_on_four_steps reading (place + 1) - the_third_difference_on_four_steps reading place := by
  simp only [the_fourth_difference, the_third_difference_on_four_steps]
  have h1 : place + 1 - 1 = place := by omega
  have h2 : place + 1 - 2 = place - 1 := by omega
  have h3 : place - 1 - 1 = place - 2 := by omega
  rw [h1, h2, h3]; omega

--| So what is stationary is stationary shifted, and stationary turned end for end.
theorem shifted_the_fourth_difference_is_itself_at_the_shifted_place (reading : Int → Int) (by_this place : Int) :
    the_fourth_difference (fun x => reading (x + by_this)) place = the_fourth_difference reading (place + by_this) := by
  rw [the_fourth_difference_is_the_step_of_the_third, the_fourth_difference_is_the_step_of_the_third,
    shifted_the_third_difference_is_itself_at_the_shifted_place, shifted_the_third_difference_is_itself_at_the_shifted_place]
  have h : place + 1 + by_this = place + by_this + 1 := by omega
  rw [h]

theorem turned_end_for_end_the_fourth_difference_is_itself (reading : Int → Int) (place : Int) :
    the_fourth_difference (fun x => reading (- x)) place = the_fourth_difference reading (- place) := by
  rw [the_fourth_difference_is_the_step_of_the_third, the_fourth_difference_is_the_step_of_the_third,
    turned_end_for_end_the_third_difference_is_owed, turned_end_for_end_the_third_difference_is_owed]
  have h1 : 1 - (place + 1) = - place := by omega
  have h2 : 1 - place = - place + 1 := by omega
  rw [h1, h2]; omega

--| On a cubic, with a step of any length, the third difference is six of the cubic's last coefficient by the step cubed:
--| it goes as the cube of the step.
theorem on_a_cubic_the_third_difference_goes_as_the_step_cubed (a b c d place step : Int) :
    (a + b * (place + step) + c * ((place + step) * (place + step))
        + d * ((place + step) * (place + step) * (place + step)))
      - ((a + b * place + c * (place * place) + d * (place * place * place))
          + (a + b * place + c * (place * place) + d * (place * place * place))
          + (a + b * place + c * (place * place) + d * (place * place * place)))
      + ((a + b * (place - step) + c * ((place - step) * (place - step))
            + d * ((place - step) * (place - step) * (place - step)))
          + (a + b * (place - step) + c * ((place - step) * (place - step))
            + d * ((place - step) * (place - step) * (place - step)))
          + (a + b * (place - step) + c * ((place - step) * (place - step))
            + d * ((place - step) * (place - step) * (place - step))))
      - (a + b * (place - (step + step)) + c * ((place - (step + step)) * (place - (step + step)))
          + d * ((place - (step + step)) * (place - (step + step)) * (place - (step + step))))
      = 6 * (d * (step * step * step)) := by
  have key : ∀ cube : Int, cube = d * (step * step * step) →
      (a + b * (place + step) + c * ((place + step) * (place + step))
        + d * ((place + step) * (place + step) * (place + step)))
      - ((a + b * place + c * (place * place) + d * (place * place * place))
          + (a + b * place + c * (place * place) + d * (place * place * place))
          + (a + b * place + c * (place * place) + d * (place * place * place)))
      + ((a + b * (place - step) + c * ((place - step) * (place - step))
            + d * ((place - step) * (place - step) * (place - step)))
          + (a + b * (place - step) + c * ((place - step) * (place - step))
            + d * ((place - step) * (place - step) * (place - step)))
          + (a + b * (place - step) + c * ((place - step) * (place - step))
            + d * ((place - step) * (place - step) * (place - step))))
      - (a + b * (place - (step + step)) + c * ((place - (step + step)) * (place - (step + step)))
          + d * ((place - (step + step)) * (place - (step + step)) * (place - (step + step))))
      = cube + cube + cube + cube + cube + cube := by
    intro cube held; subst held
    simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul]
    ac_nf
    omega
  rw [key _ rfl]; omega

--| A re-lettering that does not keep the steps is not among these.  Change two places of a straight line and it is no
--| longer stationary.
def two_places_changed (reading : Int → Int) : Int → Int :=
  fun x => if x = 0 then reading 1 else if x = 1 then reading 0 else reading x

theorem with_two_places_changed_a_line_is_not_stationary :
    the_fourth_difference (two_places_changed fun y => y) 0 = 10 ∧ the_fourth_difference (fun y => y) 0 = 0 := by decide

--| THE THIRD.  A difference summed along the steps is the end less the first: every fencepost between is taken and given
--| back, and the end one is left.
theorem a_difference_summed_is_the_end_less_the_first (reading : Nat → Int) :
    ∀ steps, summed_along steps (the_difference_along reading) = reading steps - reading 0
  | 0 => by simp [summed_along]
  | steps + 1 => by
    simp only [summed_along, a_difference_summed_is_the_end_less_the_first reading steps, the_difference_along]; omega
end three_bridges_on_the_row_of_steps


section four_gawks_and_three_closures
open «springer-verlag» THE_GOSPEL the_representation assembly_instructions readers_experience the_area
attribute [local instance high] rung01 rung02 rung03 rung04 rung05 rung06 rung07 rung08 rung09 rung10 rung11 rung12 rung13 rung14 rung15
  rung16 rung17 rung18 rung19 rung20 rung21 rung22 rung23 rung24 rung25 rung26 rung27 rung28 rung29 rung32 rung33 rung34 rung35 a_truth_about_the_experience

--| FOUR GAWKS AND THREE CLOSURES.  The author's, 18 November 2026: starting from the zero that is the same-difference
--| quantum, the knower's interpretation of the reader's interpretation of the experience, call the Atreyu process's gawk
--| four times; that makes three closures (declared).  Here it is, on the processes written out from the bottom.

--| The quantum: a zero on the same difference.
def the_same_difference_quantum : Bullshit.{0,0,0,0} := .zero SAME_DIFFERENCE

--| Gawked at once, twice, three times and four.
noncomputable def gawked_at_once : Bullshit.{0,0,0,0} := the_atreyu_process.gawk_at the_same_difference_quantum
noncomputable def gawked_at_twice : Bullshit.{0,0,0,0} := the_atreyu_process.gawk_at gawked_at_once
noncomputable def gawked_at_three_times : Bullshit.{0,0,0,0} := the_atreyu_process.gawk_at gawked_at_twice
noncomputable def gawked_at_four_times : Bullshit.{0,0,0,0} := the_atreyu_process.gawk_at gawked_at_three_times

--| Once, it is the first page: a one.
theorem gawked_at_once_it_is_the_first_page :
    ∃ (fact : FACT) (page : Number) (proof book : ThePreprint) (constant : Bullshit),
      gawked_at_once = .one fact page proof book constant := ⟨_, _, _, _, _, rfl⟩

--| Twice, three times, four: each is the rest of the call.
theorem gawked_at_again_it_is_the_rest_of_the_call :
    (∃ f g p a b c s t x y, gawked_at_twice = Bullshit.rest_call f g p a b c s t x y)
      ∧ (∃ f g p a b c s t x y, gawked_at_three_times = Bullshit.rest_call f g p a b c s t x y)
      ∧ (∃ f g p a b c s t x y, gawked_at_four_times = Bullshit.rest_call f g p a b c s t x y) :=
  ⟨⟨_, _, _, _, _, _, _, _, _, _, rfl⟩, ⟨_, _, _, _, _, _, _, _, _, _, rfl⟩, ⟨_, _, _, _, _, _, _, _, _, _, rfl⟩⟩

--| Four gawks, and three places between them.  At each the equivalence process is asked whether it believes the one
--| against the next: three closures.
noncomputable def the_first_closure : Closure := the_equivalence_process.do_you_believe_it? gawked_at_once gawked_at_twice
noncomputable def the_second_closure : Closure :=
  the_equivalence_process.do_you_believe_it? gawked_at_twice gawked_at_three_times
noncomputable def the_third_closure : Closure :=
  the_equivalence_process.do_you_believe_it? gawked_at_three_times gawked_at_four_times

--| Each is a difference, with the proposition that the one is under the next.
theorem the_three_closures_are_differences :
    (∃ fact, the_first_closure = .different fact gawked_at_once gawked_at_twice (some (gawked_at_once < gawked_at_twice)))
      ∧ (∃ fact, the_second_closure
          = .different fact gawked_at_twice gawked_at_three_times (some (gawked_at_twice < gawked_at_three_times)))
      ∧ (∃ fact, the_third_closure
          = .different fact gawked_at_three_times gawked_at_four_times
              (some (gawked_at_three_times < gawked_at_four_times))) :=
  ⟨⟨_, rfl⟩, ⟨_, rfl⟩, ⟨_, rfl⟩⟩

--| And each reads as one cell: three closures, three cells.
theorem three_closures_three_cells :
    the_first_closure.infer.length + the_second_closure.infer.length + the_third_closure.infer.length = 3 := rfl
--| What each holds, read all the way down: the quantum one fact, the first gawk twenty-two, and then thirty-nine,
--| thirty-eight, thirty-nine.  After the second gawk it goes down one and up one.
set_option maxRecDepth 100000 in
theorem what_the_four_gawks_hold :
    [the_same_difference_quantum, gawked_at_once, gawked_at_twice, gawked_at_three_times, gawked_at_four_times].map
        (fun gawk => gawk.all_the_way_down.length)
      = [1, 22, 39, 38, 39] := by decide
end four_gawks_and_three_closures


section the_agreements_on_the_ledger
open readers_experience the_review_on_the_ledger

--| THE AGREEMENTS, ON THE LEDGER.  A page set in type holds two facts and the proposition that they agree.  Whether they
--| do was not among the receipts.  Episode 12 has the thirty-six pages on the first card, so ask each: how does its first
--| fact click, and how its second?

--| Counted up: the two clicks of every page set in type, from the top.
def how_the_pages_set_in_type_click : ThePreprint → List (Bool × Bool)
  | .introduction _ _ => []
  | .methodology _ _ _ _ _ => []
  | .results before after _ _ _ _ below => (before.bit, after.bit) :: how_the_pages_set_in_type_click below

--| Counted down: the two clicks of every rebuttal, and of the manuscript under them.
def how_the_rebuttals_click : ThePreprint → List (Bool × Bool)
  | .introduction _ _ => []
  | .methodology planted polynomial _ _ before => (planted.bit, polynomial.bit) :: how_the_rebuttals_click before
  | .results _ _ _ _ _ _ below => how_the_rebuttals_click below

--| Thirty-four agree and one does not.  The one is the top page, the thirty-sixth, and it is true on false.
set_option maxRecDepth 100000 in
theorem thirty_four_agree_and_the_top_page_is_true_on_false :
    how_the_pages_set_in_type_click theTopOfTheLedger.the_page = (true, false) :: List.replicate 34 (true, true) := by
  decide

--| Counted down every rebuttal names two facts that click, thirty-five of them.  Under them is the manuscript handed in,
--| and the manuscript is true on false.  That is where the top page has it from.
set_option maxRecDepth 100000 in
theorem every_rebuttal_clicks_twice_and_the_manuscript_is_true_on_false :
    how_the_rebuttals_click page01.rebuttal = List.replicate 35 (true, true) ++ [(true, false)]
      ∧ how_the_rebuttals_click theManuscript = [(true, false)] := by decide
end the_agreements_on_the_ledger

section the_fixed_point_and_both_branches
open «springer-verlag» THE_GOSPEL the_representation assembly_instructions readers_experience the_area
attribute [local instance high] rung01 rung02 rung03 rung04 rung05 rung06 rung07 rung08 rung09 rung10 rung11 rung12 rung13 rung14 rung15
  rung16 rung17 rung18 rung19 rung20 rung21 rung22 rung23 rung24 rung25 rung26 rung27 rung28 rung29 rung32 rung33 rung34 rung35 a_truth_about_the_experience

--| THE FIXED POINT.  The author's, 18 November 2026: the third and fourth closures' residue should be exactly the same,
--| meaning a fixed point; the second and third should click, yet their values should be different; and it takes exactly
--| five quanta to send a nowtrino back and forth between the two closest distances (declared).  Gawk a fifth time.

noncomputable def gawked_at_five_times : Bullshit.{0,0,0,0} := the_atreyu_process.gawk_at gawked_at_four_times

--| The fifth is the fourth.
theorem gawked_at_five_times_is_gawked_at_four : gawked_at_five_times = gawked_at_four_times := rfl

noncomputable def the_fourth_closure : Closure :=
  the_equivalence_process.do_you_believe_it? gawked_at_four_times gawked_at_five_times

--| What the third closure stores is what the fourth stores; and the second stores it too.  The first does not.
theorem the_second_third_and_fourth_closures_store_one_proposition :
    (gawked_at_twice < gawked_at_three_times) = (gawked_at_three_times < gawked_at_four_times)
      ∧ (gawked_at_three_times < gawked_at_four_times) = (gawked_at_four_times < gawked_at_five_times) := ⟨rfl, rfl⟩

--| That proposition cannot hold: nothing is under itself.
theorem nothing_is_under_itself : ¬ (gawked_at_four_times < gawked_at_five_times) := fun under => under.2 under.1

theorem what_three_closures_store_cannot_hold :
    ¬ (gawked_at_twice < gawked_at_three_times) ∧ ¬ (gawked_at_three_times < gawked_at_four_times)
      ∧ ¬ (gawked_at_four_times < gawked_at_five_times) :=
  have the_third : ¬ (gawked_at_three_times < gawked_at_four_times) :=
    the_second_third_and_fourth_closures_store_one_proposition.2 ▸ nothing_is_under_itself
  ⟨the_second_third_and_fourth_closures_store_one_proposition.1 ▸ the_third, the_third, nothing_is_under_itself⟩

--| What the first closure stores holds: the first page is under the rest of the call.
theorem what_the_first_closure_stores_holds : gawked_at_once < gawked_at_twice := ⟨trivial, fun over => over⟩

--| And all four click.
set_option maxRecDepth 100000 in
theorem all_four_closures_click :
    [the_first_closure, the_second_closure, the_third_closure, the_fourth_closure].map
        (fun closure => closure.infer.map FACT.bit)
      = [[true], [true], [true], [true]] := by decide

--| Yet the values differ: twice is not three times, and three times is not four.
set_option maxRecDepth 100000 in
theorem the_values_differ :
    gawked_at_twice ≠ gawked_at_three_times ∧ gawked_at_three_times ≠ gawked_at_four_times :=
  ⟨fun same => absurd (congrArg (fun gawk => gawk.all_the_way_down.length) same) (by decide),
   fun same => absurd (congrArg (fun gawk => gawk.all_the_way_down.length) same) (by decide)⟩

--| BOTH BRANCHES.  The author's: that one step does not matter; it is computed on both branches, in the opposite order
--| (declared).  Take the first page and call its fact false, and gawk on.
noncomputable def the_first_page_called_false : Bullshit.{0,0,0,0} :=
  match gawked_at_once with
  | .one _ page proof book constant => .one (bitFACT false) page proof book constant
  | other => other
noncomputable def called_false_and_gawked_at_once : Bullshit.{0,0,0,0} :=
  the_atreyu_process.gawk_at the_first_page_called_false
noncomputable def called_false_and_gawked_at_twice : Bullshit.{0,0,0,0} :=
  the_atreyu_process.gawk_at called_false_and_gawked_at_once
noncomputable def called_false_and_gawked_at_three_times : Bullshit.{0,0,0,0} :=
  the_atreyu_process.gawk_at called_false_and_gawked_at_twice

--| After one step more the branch called false is the branch called true, and it stops where that one stops.
theorem after_one_step_the_two_branches_are_one :
    called_false_and_gawked_at_twice = gawked_at_three_times
      ∧ called_false_and_gawked_at_three_times = gawked_at_four_times
      ∧ the_atreyu_process.gawk_at called_false_and_gawked_at_three_times = called_false_and_gawked_at_three_times :=
  ⟨rfl, rfl, rfl⟩

--| WHAT A FIRST PAGE HOLDS.  Twenty-two facts: its own, and those of its page number, its proof, its book and its
--| constant.
def the_parts_of_a_first_page : Bullshit → List Nat
  | .one _ page proof book constant =>
      [1, page.all_the_way_down.length, proof.all_the_way_down.length, book.all_the_way_down.length,
       constant.all_the_way_down.length]
  | _ => []

set_option maxRecDepth 100000 in
theorem the_first_page_holds_one_two_four_three_and_twelve :
    the_parts_of_a_first_page gawked_at_once = [1, 2, 4, 3, 12] := by decide
end the_fixed_point_and_both_branches


section the_action_of_light_and_matter
open readers_experience readers_interpretation_of_the_experience

--| THE ACTION OF LIGHT AND MATTER.  Verse twenty-eight: "And from these was written the action of light and matter,
--| minimally coupled."  The device has the two halves apart: Episode 12's action of a square of links, and the state
--| carried back along a link.  Write them at one site as one thing: what the square of links holds, the state carried
--| back along a link, and the state against itself.  One turn at every site, of the links and of the state together,
--| leaves all three as they were.  The link in the second is the link in the first: that is what "minimally" asks.
def the_action_of_light_and_matter_at {n : Nat} (state : Site4 n → Turns) (U : Torus4 n)
    (this that way : Direction) (x : Site4 n) : Int × Turns × Turns :=
  (the_turns_action (the_square4 U this that x), the_state_carried_back state U way x, the_state_against_itself state x)

theorem the_action_of_light_and_matter_is_left_by_a_turn_at_every_site {n : Nat} (state : Site4 n → Turns) (U : Torus4 n)
    (g : Site4 n → Turns) (unit : ∀ x, the_turns_norm (g x) = 1) (this that way : Direction) (x : Site4 n) :
    the_action_of_light_and_matter_at (the_gauged_state state g) (the_gauged_torus4 U g) this that way x
      = the_action_of_light_and_matter_at state U this that way x := by
  simp only [the_action_of_light_and_matter_at, the_gauged_square4 U g unit, a_unit_turn_leaves_the_action _ _ (unit _),
    the_state_carried_back_is_gauge_invariant state U g unit, the_state_against_itself_is_gauge_invariant state g unit]
end the_action_of_light_and_matter


section the_constant_as_physics
open readers_experience the_area

--| THE CONSTANT, AS PHYSICS.  The author's, 18 November 2026: the missed number can be pushed back through the stack to
--| appear as `Equivalation.physics`; that is the root of the quartic; read this episode from the beginning (declared).
--| From the beginning: the constant is an Area, the one nobody built and nobody will, whose count was already printed.  A
--| jar is a fact and an Area.  The physics of an equivalation is a fact and a jar.  So put the constant in a jar, and the
--| jar under the physics.  Nothing is opened: the constant is still a name, and nothing below asks what is in it.
noncomputable def the_constant_in_a_jar : Jar := .color zero the_constant
noncomputable def the_physics_of_the_constant : Equivalation := .physics zero the_constant_in_a_jar

--| What a jar holds is what was put in it, whatever that was.
theorem what_a_jar_holds_is_what_was_put_in (fact : FACT) (area : Area) : what_the_jar_holds (.color fact area) = area :=
  rfl

--| So this jar holds the constant, and counted it is the number Episode 8 printed.
theorem the_jar_holds_the_constant : what_the_jar_holds (.color zero the_constant) = the_constant :=
  what_a_jar_holds_is_what_was_put_in zero the_constant

theorem counted_what_the_jar_holds_is_the_number :
    cells (what_the_jar_holds (.color zero the_constant)) = the_constant_factor_of_scaling_bullshit := by
  rw [what_a_jar_holds_is_what_was_put_in]; exact counted_the_constant_is_the_constant

--| And the reader of an equivalation does not read it.  Of the physics it returns the one fact; the jar vanishes.
theorem the_physics_vanishes_to_one_fact : the_physics_of_the_constant.vanish = [zero] := rfl

--| The two that stand on it: zero-like, a fact on the physics; one-like, a proposition on the physics twice.  Read, the
--| three are one fact, two and three, and the constant is in none of the readings.
noncomputable def zero_like_on_the_constant : Equivalation := .zero_like zero the_physics_of_the_constant
noncomputable def one_like_on_the_constant : Equivalation :=
  .one_like (cells the_constant = the_constant_factor_of_scaling_bullshit) the_physics_of_the_constant
    the_physics_of_the_constant

theorem the_physics_and_the_two_on_it_read_one_two_and_three :
    the_physics_of_the_constant.vanish.length = 1 ∧ zero_like_on_the_constant.vanish.length = 2
      ∧ one_like_on_the_constant.vanish.length = 3 := ⟨rfl, rfl, rfl⟩
end the_constant_as_physics


section the_posts_and_the_panels
open readers_experience

--| THE POSTS AND THE PANELS.  The author's, 18 November 2026: the thirty-seven are the fence posts and the thirty-six the
--| fence panels, and the polynomial can be computed from them; the four posts past the Area are the four-member fencepost,
--| the bridge to the arm that does not click (declared).  Episode 8 wrote the steps of its argument as a list: the number
--| read three times, and then one reading for every kind of thing after it, in the order the kinds were made.  Set the
--| first two aside, so that the number is counted once.

--| Thirty-six steps, one for each kind.
def the_steps_one_for_each_kind : List (List FACT) := the_steps_of_the_argument.drop 2

theorem there_are_thirty_six_kinds : the_steps_one_for_each_kind.length = 36 := rfl

--| COUNTED FROM THE FRONT.  The fifth step is the reading of a limit, the thirteenth of an Area, the eighteenth of an
--| Abstraction, the thirty-sixth of a Closure.
theorem the_fifth_thirteenth_eighteenth_and_thirty_sixth :
    the_steps_one_for_each_kind[4]? = some ε₁.converge
      ∧ the_steps_one_for_each_kind[12]? = some ast₁.riemann_integrate
      ∧ the_steps_one_for_each_kind[17]? = some the_proof.equivalation
      ∧ the_steps_one_for_each_kind[35]? = some the_only_logical_inconsistency.infer := ⟨rfl, rfl, rfl, rfl⟩

--| THE FOUR BETWEEN.  Past the Area and short of the Abstraction stand four: a pigeonhole, a jar, an equivalation and an
--| encoding.  Four posts and five panels.
theorem the_four_posts_between_the_area_and_the_abstraction :
    (the_steps_one_for_each_kind.drop 13).take 4
      = [the_galerkin_method.solve, the_photon_worldline.classify, t₁.vanish, δδxᵢ.decode] := rfl

--| COUNTED FROM THE BACK.  Episode 8 took its numbers from the other end: the tapes of the last steps, laid end to end.
--| Five for the frame, thirteen for the coefficient, eighteen for the memory, and twice the memory for the trace.
theorem counted_from_the_back_the_same_four_numbers :
    the_coordinate_system.gauss.length = 5 ∧ the_coefficient_tape.length = 13 ∧ the_memory_tape.length = 18
      ∧ the_trace_of_truth_in_the_device = 36 := by decide

--| So the place of the Area from the front is the length of the coefficient from the back, and so for the others: two
--| counts of one fence, from its two ends.
theorem the_polynomial_from_either_end :
    an_exact_polynomial_description = 13 ∧ the_trace_of_truth_in_the_device = 36
      ∧ the_number_of_symbols_that_must_be_written_to_express_this = 18
      ∧ 13 + the_coordinate_system.gauss.length = 18 ∧ 2 * 18 = 36 := by decide
end the_posts_and_the_panels

section inflated_twice
open readers_experience readers_interpretation_of_the_experience

--| INFLATED TWICE.  The author's, 18 November 2026: the arm that does not click can be inflated by the excluded middle
--| twice; the first inflation is one quadratic in the quartic and the second is the other; the second gives ratios and not
--| reals, and the reals are only ever described by a process of completion (declared).  The quartic at the device's
--| weights is two quadratics, written as pairs: a whole part, and a part by the root of the round trip.
def the_one_quadratic (x r : Int) : Int × Int := (18 * (r * r - 5 * x), 5 * x)
def the_other_quadratic (x r : Int) : Int × Int := (18 * (r * r - 5 * x), - (5 * x))

--| Inflated once: the one quadratic.  It has a part by the root, and that part is the frame by the place.
theorem inflated_once_there_is_a_part_by_the_root (x r : Int) : (the_one_quadratic x r).2 = 5 * x := rfl

--| Inflated twice: the one by the other.  Eighteen of the quartic, and nothing by the root.  What is left is whole.
theorem inflated_twice_nothing_is_left_by_the_root (x r : Int) :
    the_surd_product (the_one_quadratic x r) (the_other_quadratic x r) = (18 * the_closing_quartic 18 5 x r, 0) :=
  eighteen_of_the_quartic_is_a_pair_by_itself_turned_over x r

--| The other is the one with its part by the root owed, and either order gives the same.
theorem the_other_quadratic_is_the_one_turned_over (x r : Int) :
    the_other_quadratic x r = ((the_one_quadratic x r).1, - (the_one_quadratic x r).2)
      ∧ the_surd_product (the_other_quadratic x r) (the_one_quadratic x r)
          = the_surd_product (the_one_quadratic x r) (the_other_quadratic x r) :=
  ⟨rfl, the_two_pairs_change_places_and_the_product_stays x r⟩
end inflated_twice

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

open Measurement the_area readers_experience

--| THE LAST MACHINE, OPENED.  The author's, 17 November 2026: replace the calculation and open the last machine to display it;
--| it should be obvious we are explicitly choosing the lowest amount of bullshit.  The last machine is the Area's.  No natural
--| goes in.  The whole of the sum of the roots is how many times the coefficient by the frame goes into the trace by the
--| fencepost's first.  The reading is the giant list, compiled.  The other is the one taken away from the other.
def the_whole_of_the_sum    : Area := how_many_times (the_area.the_trace * the_fencepost.1) (the_coefficient * the_fencepost.2)
def the_reading_in_cells    : Area := the_area_of_a_tape the_giant_list
def the_other_root_in_cells : Area := the_whole_of_the_sum - the_reading_in_cells

--| THE CHOICE.  Two amounts of bullshit.  Take the lower.
def the_lowest_amount_of_bullshit : Area :=
  if the_other_root_in_cells < the_reading_in_cells then the_other_root_in_cells else the_reading_in_cells

--| The author's: the demonstration of the Area crank demonstrates that they are the same, Quot.sound; Quot.sound carrying,
--| carrying an empty carrier.  Take the reading away from the lowest and nothing is left but the tree.  That is all the sound
--| of the quotient is handed, and with it the two are one: in the box of ratios, and in the order of the truth.
theorem the_carrier_is_empty : something_is_left (the_lowest_amount_of_bullshit - the_reading_in_cells) = false := by decide +kernel

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
def life_the_universe_and_everything : Nat := cells the_lowest_amount_of_bullshit
#eval (cells the_whole_of_the_sum, cells the_reading_in_cells, cells the_other_root_in_cells)
#eval life_the_universe_and_everything
#print axioms life_the_universe_and_everything

--| It is what was left of the sum, above, where the giant list stood for the number.
theorem what_is_left_of_the_sum_is_the_lowest_amount_of_bullshit :
    what_is_left_of_the_sum = life_the_universe_and_everything := by decide +kernel
--#print axioms the_carrier_is_empty                                     -- [propext]
--#print axioms the_lowest_is_the_reading_in_the_box                     -- [propext, Quot.sound]
--#print axioms the_lowest_is_the_reading_in_the_truth                   -- [propext, Quot.sound]
--#print axioms what_is_left_of_the_sum_is_the_lowest_amount_of_bullshit

--| I'm expecting the Vogon constructor fleet any day now.

end A_WHOLLY_REMARKABLE_BOOK
