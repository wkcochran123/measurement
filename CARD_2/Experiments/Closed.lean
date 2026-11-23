/-
The receipts closed.

This file stands beside the device and is built apart: ✖ [2/2] Running Experiments.Closed
error: no such file or directory (error code: 2)
  file: /Users/williamcochran/Desktop/measurement/CARD_2/Experiments/Closed.lean
Some required targets logged failures:
- Experiments.Closed.  Nothing in 
imports it.  It defines no inductive.

Probes made on 20 and 21 November 2026 in scratch files, now stated and checked.  What the bottom of the last machine is
built from.  Episode 8's census, each kind's atom read by its own reader, set against what the last machine's
processes carry, read by the same readers.  The same things read all the way down.  And the sixth class's zero, one
and bit on the last machine.  Nothing here says what any count means.
-/
import Experiments.Bottom

namespace Measurement

section what_the_bottom_is_built_from
open «springer-verlag» THE_GOSPEL the_representation assembly_instructions readers_experience the_table
attribute [local instance high] rung01 rung02 rung03 rung04 rung05 rung06 rung07 rung08 rung09 rung10 rung11 rung12 rung13 rung14 rung15
  rung16 rung17 rung18 rung19 rung20 rung21 rung22 rung23 rung24 rung25 rung26 rung27 rung28 rung29 rung32 rung33 rung34 rung35 a_truth_about_the_experience

--| THE SEVEN AND THE NINE.  The sequence is a fact, the origin, and an end.  The accumulation is a fact, that sequence, and an
--| end.  So five, seven, nine is one wrapper put on three times: one in front and one behind.
theorem the_sequence_is_the_origin_with_one_in_front_and_one_behind :
    ∃ front behind, the_limit_process.sequence = Sequence.index front the_indexing_process.origin (Sequence.nil behind) :=
  ⟨_, _, rfl⟩
theorem the_accumulation_is_the_sequence_with_one_in_front_and_one_behind :
    ∃ front behind, the_cauchy_process.accumulation = Limit.index front the_limit_process.sequence (Limit.nil behind) :=
  ⟨_, _, rfl⟩

end what_the_bottom_is_built_from

section episode_eights_census_against_the_machine
open «springer-verlag» THE_GOSPEL the_representation assembly_instructions readers_experience the_table
attribute [local instance high] rung01 rung02 rung03 rung04 rung05 rung06 rung07 rung08 rung09 rung10 rung11 rung12 rung13 rung14 rung15
  rung16 rung17 rung18 rung19 rung20 rung21 rung22 rung23 rung24 rung25 rung26 rung27 rung28 rung29 rung32 rung33 rung34 rung35 a_truth_about_the_experience

--| EPISODE 8'S CENSUS.  One atom of each kind, read by that kind's reader.  Thirty-four kinds are set down here; a metavariable
--| and an abstraction are left out, the one for its universe and the other because the machine carries it only as a function.
def episode_eights_census : List Nat :=
  [(one).peano.length, (natural_one).induct.length, (zeroth_rational).diagonalize.length, (δ₁).enumerate.length,
   (ε₁).converge.length, (reading₁).taste.length, (implication₁).experiment.length, (y₁).phenomenon.length,
   (absence_of_evidence).elaborate.length, (does_it_matter?).unknown.length,
   (is_it_euclidean_enough?).taylor_expansion.length, (ast₁).riemann_integrate.length,
   (the_galerkin_method).solve.length, (the_photon_worldline).classify.length, (t₁).vanish.length,
   (δδxᵢ).decode.length, (integration).euclid.length, (the_sobolev_norm).projector.length,
   (the_galerkin_basis).householder.length, (the_exact_approximation).terms.length,
   (is_the_undeniably_correct_answer).approx.length, (should_be_true).buckets.length,
   (newtons_train_of_thought).name.length, (a_measurement).method.length,
   (_root_.Measurement.the_macguffin).audit.length, (the_fact_is_true).witness.length,
   (true_by_construction).testify.length, (the_fabric_of_spacetime).krylov.length,
   (the_nowtrino_path).stokes.length, (the_coordinate_system).gauss.length, (the_basis).the_reading.length,
   (the_satire).the_model.length, (the_most_basic_of_conclusions).meter.length,
   (the_only_logical_inconsistency).infer.length]

--| THE SAME READERS ON WHAT THE LAST MACHINE CARRIES.
noncomputable def the_machine_by_episode_eights_readers : List Nat :=
  [(the_carrier_process.quarter).peano.length, (the_counting_process.count).induct.length,
   (the_indexing_process.origin).diagonalize.length, (the_limit_process.sequence).enumerate.length,
   (the_cauchy_process.accumulation).converge.length, (the_repeatable_process.stimulus).taste.length,
   (the_repeatable_process.expectation).experiment.length, (the_turing_process.program).phenomenon.length,
   (the_turing_process.state).elaborate.length, (the_noisy_process.program).unknown.length,
   (the_slip_process.projection).taylor_expansion.length,
   (the_sensing_process.accumulation).riemann_integrate.length, (the_gauge_process.clock).solve.length,
   (the_meesa_process.concept).classify.length, (the_digital_process.zero).vanish.length,
   (the_compiled_process.opcodes).decode.length, (the_adding_process.sum).euclid.length,
   (the_multiplying_process.product).projector.length, (the_basic_process.span).householder.length,
   (the_jordan_process.polynomial).terms.length, (the_arm_wave_process.guess).approx.length,
   (the_crusade_process.religious_dogma).buckets.length, (the_initiation_process.sacred_texts).name.length,
   (the_learning_process.invariant).method.length, (the_scientific_process.knowledge).audit.length,
   (the_religious_process.in_the_literature).witness.length, (the_universe_tensor.in_reality).testify.length,
   (the_big_red_dog_process.Du).krylov.length,
   (the_calculus_process.the_direction_to_the_destination).stokes.length,
   (the_heartbeat_process.according_to_newton).gauss.length, (the_lean_process.in_heartbeats).the_reading.length,
   (the_compiler_output.of_jibberish).the_model.length, (the_atreyu_process.a_constant).meter.length,
   (the_equivalence_process.your_conclusion).infer.length]

theorem the_census_kind_by_kind : episode_eights_census = [2, 2, 1, 2, 2, 3, 3, 2, 2, 2, 2, 2, 4, 4, 3, 4, 2, 2, 2, 2, 4, 4, 4, 2, 2, 2, 2, 4, 4, 5, 2, 3, 5, 3] := rfl
theorem the_machine_kind_by_kind : the_machine_by_episode_eights_readers = [2, 2, 2, 2, 2, 5, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 2, 0, 2, 2, 1] := rfl

--| Taking the first thing each process carries, they agree on seven kinds of thirty-four: the number, the natural, the
--| sequence, the limit, the study, the computation and the knowledge.  On twenty-seven they do not.  (A number and a limit
--| are each carried by more than one process, and not every one agrees; counting only the kinds where all agree, it is five.)
--| The census is not a reading of the last machine.
theorem the_census_and_the_machine_agree_on_seven_of_thirty_four :
    ((episode_eights_census.zip the_machine_by_episode_eights_readers).filter fun pair => pair.1 == pair.2).length = 7
      ∧ episode_eights_census.length = 34 := by
  rw [the_census_kind_by_kind, the_machine_kind_by_kind]; decide

--| The other things of those two kinds.  The lean process's number reads one, where the census reads two; the observation's
--| after reads three, where the census reads two.
theorem a_number_and_a_limit_carried_elsewhere_do_not_agree :
    the_lean_process.the_measurement_of.peano.length = 1 ∧ the_observation_process.after.converge.length = 3 := ⟨rfl, rfl⟩

--| The last five kinds are the ones Episode 8 cuts its numbers from: five, two, three, five, three, eighteen in all and the
--| last four thirteen.  On the machine the same five read two, nothing, two, two, one: seven, and the last four five.
theorem the_last_five_kinds_on_each :
    episode_eights_census.drop 29 = [5, 2, 3, 5, 3] ∧ the_machine_by_episode_eights_readers.drop 29 = [2, 0, 2, 2, 1] := by
  rw [the_census_kind_by_kind, the_machine_kind_by_kind]; decide

end episode_eights_census_against_the_machine

section all_the_way_down
open «springer-verlag» THE_GOSPEL the_representation assembly_instructions readers_experience the_table
attribute [local instance high] rung01 rung02 rung03 rung04 rung05 rung06 rung07 rung08 rung09 rung10 rung11 rung12 rung13 rung14 rung15
  rung16 rung17 rung18 rung19 rung20 rung21 rung22 rung23 rung24 rung25 rung26 rung27 rung28 rung29 rung32 rung33 rung34 rung35 a_truth_about_the_experience

--| READ ALL THE WAY DOWN.  What the processes carry, a kind at a time, in facts.  Two kinds are not here: a computation and a
--| closure ran out of depth when read this way.
set_option maxRecDepth 20000 in
theorem what_the_processes_carry_all_the_way_down :
    (the_carrier_process.quarter).all_the_way_down.length = 2
      ∧ (the_counting_process.count).all_the_way_down.length = 3
      ∧ (the_indexing_process.origin).all_the_way_down.length = 5
      ∧ (the_limit_process.sequence).all_the_way_down.length = 7
      ∧ (the_cauchy_process.accumulation).all_the_way_down.length = 9
      ∧ (the_repeatable_process.stimulus).all_the_way_down.length = 68
      ∧ (the_repeatable_process.expectation).all_the_way_down.length = 69
      ∧ (the_turing_process.program).all_the_way_down.length = 71
      ∧ (the_noisy_process.program).all_the_way_down.length = 73
      ∧ (the_slip_process.projection).all_the_way_down.length = 147
      ∧ (the_sensing_process.accumulation).all_the_way_down.length = 1
      ∧ (the_gauge_process.clock).all_the_way_down.length = 2
      ∧ (the_meesa_process.concept).all_the_way_down.length = 3
      ∧ (the_digital_process.zero).all_the_way_down.length = 6
      ∧ (the_compiled_process.opcodes).all_the_way_down.length = 21
      ∧ (the_adding_process.sum).all_the_way_down.length = 2
      ∧ (the_multiplying_process.product).all_the_way_down.length = 1
      ∧ (the_basic_process.span).all_the_way_down.length = 1
      ∧ (the_jordan_process.polynomial).all_the_way_down.length = 2
      ∧ (the_arm_wave_process.guess).all_the_way_down.length = 1
      ∧ (the_crusade_process.religious_dogma).all_the_way_down.length = 3
      ∧ (the_initiation_process.sacred_texts).all_the_way_down.length = 5
      ∧ (the_learning_process.invariant).all_the_way_down.length = 8
      ∧ (the_scientific_process.knowledge).all_the_way_down.length = 3
      ∧ (the_religious_process.in_the_literature).all_the_way_down.length = 1
      ∧ (the_universe_tensor.in_reality).all_the_way_down.length = 1
      ∧ (the_big_red_dog_process.Du).all_the_way_down.length = 13
      ∧ (the_calculus_process.the_direction_to_the_destination).all_the_way_down.length = 3
      ∧ (the_heartbeat_process.according_to_newton).all_the_way_down.length = 15
      ∧ (the_lean_process.in_heartbeats).all_the_way_down.length = 2
      ∧ (the_compiler_output.of_jibberish).all_the_way_down.length = 3
      ∧ (the_atreyu_process.a_constant).all_the_way_down.length = 12 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

--| The thirteen.  What the big red dog process carries, a variation, is thirteen facts.
theorem what_the_big_red_dog_carries_is_thirteen_facts :
    the_big_red_dog_process.Du.all_the_way_down.length = 13 := rfl

end all_the_way_down

section zero_one_and_the_bit
open «springer-verlag» THE_GOSPEL the_representation assembly_instructions readers_experience the_table

--| THE SIXTH CLASS ON THE LAST MACHINE.  Episode 1 gives it a zero, margin "Empty"; a one, margin "Full"; and a bit, margin
--| "Residue".  On the first card the zero and the one are one and the same limit, one fact.  The bit is thirty-five facts.
theorem the_zero_and_the_one_are_one_limit_and_the_bit_is_thirty_five_facts :
    rung06.zero = rung06.one
      ∧ rung06.zero.all_the_way_down.length = 1
      ∧ rung06.bit.all_the_way_down.length = 35
      ∧ rung06.bit.taste.length = 3 := ⟨rfl, rfl, rfl, rfl⟩

--| And every fact in the three clicks: thirty-seven of them.
theorem every_fact_in_the_zero_the_one_and_the_bit_clicks :
    (rung06.zero.all_the_way_down ++ rung06.one.all_the_way_down ++ rung06.bit.all_the_way_down).map the_representation.the_click
      = List.replicate 37 true := by decide

end zero_one_and_the_bit

section the_knowers_clock
open the_table the_table.Account readers_experience

--| THE KNOWER'S CLOCK, TWO READINGS.  Episode 13 has the knower's interpretation on three coins in a row.  The alternating
--| clock, set beside its complement, is the bent card.  The still clock, set beside its complement, is nothing.  And both
--| clocks print one number.  The author's, 21 November 2026 (declared, as a belief): one of the two readings is the zero of
--| the physical model and the other is the second strength, and which is which is the last use of the knower's bit.
theorem the_knowers_clock_reads_the_bent_card_and_nothing_and_prints_one_number :
    the_same (the_knowers_interpretation true false true + the_knowers_interpretation false true false) (holding the_coefficient)
      ∧ the_same (the_knowers_interpretation true true true + the_knowers_interpretation false false false) nothing_held
      ∧ the_knowers_pair true = the_knowers_pair false :=
  ⟨the_alternating_clock_reads_the_bent_card_and_the_still_clock_reads_nothing.1,
   the_alternating_clock_reads_the_bent_card_and_the_still_clock_reads_nothing.2, both_clocks_print_one_number⟩

--| In whole numbers: five owed and eighteen held are thirteen; eighteen owed and eighteen held are nothing.
theorem the_two_readings_counted :
    balance (the_knowers_interpretation true false true) + balance (the_knowers_interpretation false true false) = 13
      ∧ balance (the_knowers_interpretation true true true) + balance (the_knowers_interpretation false false false) = 0 := by
  obtain ⟨a, b, c, d⟩ := the_knowers_interpretation_of_the_clocks
  rw [a, b, c, d]; exact ⟨rfl, rfl⟩

--| THE SAME BENT CARD IS WHAT THE LINEAR STEP LEAVES.  Take the step that the slope says takes the residual away.  What is
--| left is the bent card by the step squared, with nothing past it.  The bent card there and the bent card the alternating
--| clock reads are one Area.
theorem what_the_linear_step_leaves_is_the_alternating_clocks_reading (y h : Account)
    (the_slope_takes_the_residual_away : the_same (the_slope_on_the_account y * h + the_residual_on_the_account y) nothing_held) :
    the_same (the_residual_on_the_account (y + h)) (holding the_coefficient * (h * h))
      ∧ the_same (the_knowers_interpretation true false true + the_knowers_interpretation false true false)
          (holding the_coefficient) :=
  ⟨the_step_leaves_the_bent_card_by_the_step_squared y h the_slope_takes_the_residual_away,
   the_alternating_clock_reads_the_bent_card_and_the_still_clock_reads_nothing.1⟩

end the_knowers_clock

--#print axioms the_census_and_the_machine_agree_on_seven_of_thirty_four
--#print axioms what_the_processes_carry_all_the_way_down
--#print axioms the_zero_and_the_one_are_one_limit_and_the_bit_is_thirty_five_facts
--#print axioms every_fact_in_the_zero_the_one_and_the_bit_clicks
--#print axioms the_knowers_clock_reads_the_bent_card_and_nothing_and_prints_one_number
--#print axioms what_the_linear_step_leaves_is_the_alternating_clocks_reading

end Measurement
