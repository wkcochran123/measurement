-- The code commented out of Episode13.lean, moved here verbatim (24 November 2026).
-- Each block is marked with the line it stood at in Episode13.lean before the move; the '--× ' prefix is kept.

-- Episode13.lean, line 100
--× def simulate_this_way          := bent_card.the_device_computing_the_next_configuration Area the_number_of_marks
--× def the_crank                   := bent_card.proportional_laws_accumulate_commutation_projections_called_TERM_LAMBDAS Area the_number_of_marks
--× def the_crank_and_the_fencepost := bent_card.fenceposts_must_be_preserved Area the_number_of_marks

-- Episode13.lean, line 112
--× theorem the_riemann_sum_is_indistinguisahble_from_the_bent_card_with_an_extra_fencepost_of_blanks (a_card : Area) :
--×         a_card.riemann_integrate.length = compute_the_area_of a_card + the_fencepost_bug := by
--×   induction a_card with
--×   | tree _ => rfl
--×   | dt _ _ _ the_rest => simp only [Area.riemann_integrate, List.length_cons, compute_the_area_of, the_rest]; omega

-- Episode13.lean, line 153
--× theorem the_proof_of_episode_eight_is_the_abstraction_of_one_fact : the_marks [zero] = the_proof := rfl

-- Episode13.lean, line 157
--× theorem an_abstraction_is_twice_its_tape_and_the_names (tape : List FACT) :
--×     (the_marks tape).equivalation.length = tape.length + tape.length + the_fencepost_bug := by
--×   have wall : ∀ t : List FACT, (interpret_an_opaque_list_of_truths t).equivalation.length = t.length + the_fencepost_bug := by
--×     intro t
--×     induction t with
--×     | nil => rfl
--×     | cons _ _ ih => simp only [interpret_an_opaque_list_of_truths, Abstraction.equivalation, List.length_cons, ih]; omega
--×   have proof : ∀ (w : Abstraction) (t : List FACT), (watch_closely w t).equivalation.length = w.equivalation.length + t.length := by
--×     intro w t
--×     induction t with
--×     | nil => rfl
--×     | cons _ _ ih => simp only [watch_closely, Abstraction.equivalation, List.length_cons, ih]; omega
--×   simp only [the_marks, proof, wall]; omega

-- Episode13.lean, line 171
--× theorem the_memory_written_as_an_abstraction_is_the_trace_and_the_fencepost :
--×     (the_marks the_memory_tape).equivalation.length = the_trace_of_truth_in_the_device + the_fencepost_bug := by
--×   rw [an_abstraction_is_twice_its_tape_and_the_names]; rfl

-- Episode13.lean, line 176
--× theorem the_wall_comes_before_the_abstraction (fact : FACT) (rest : List FACT) :
--×     interpret_an_opaque_list_of_truths (fact :: rest) < the_marks (fact :: rest)
--×       ∧ ¬ (the_marks (fact :: rest) ≤ interpret_an_opaque_list_of_truths (fact :: rest)) :=
--×   ⟨rfl, fun h => Bool.noConfusion h⟩

-- Episode13.lean, line 231
--× theorem counted_simulate_is_simulate (quantum : Area) (here_and_now: Area × Area) :
--×     some_quartic_called (simulate_this_way quantum here_and_now)
--×       = bent_card.the_device_computing_the_next_configuration Nat List.length (compute_the_area_of quantum) (some_quartic_called here_and_now) := by
--×   obtain ⟨_, _⟩ := here_and_now
--×   simp only [simulate_this_way, some_quartic_called, bent_card.the_device_computing_the_next_configuration, bent_card.the_exact_Taylor_series_degree,
--×     bent_card.the_length_of_the_path_from_here_to_there, bent_card.the_measurement_degrees_of_freedom, bent_card.fencepost]
--×   split
--×   · rename_i h
--×     have h' := (obviously_bigger _ _).1 h
--×     simp only [palm_the_middle_card_adds, false_shuffle_multiplies, the_double_lift_subtracts, the_number_of_marks_the_tapes_length] at h'
--×     rw [if_pos h']
--×   · rename_i h
--×     have h' : ¬ _ := fun g => h ((obviously_bigger _ _).2 g)
--×     simp only [palm_the_middle_card_adds, false_shuffle_multiplies, the_double_lift_subtracts, the_number_of_marks_the_tapes_length] at h'
--×     rw [if_neg h']
--×     simp only [false_shuffle_multiplies, the_double_lift_subtracts, the_number_of_marks_the_tapes_length]

-- Episode13.lean, line 249
--× theorem counted_any_number_of_turns_is_as_many_turns (quantum : Area) (turns : List Unit) (here_and_now : Area × Area) :
--×     some_quartic_called (turns.foldl (fun computation _ => simulate_this_way quantum computation) here_and_now)
--×       = turns.foldl (fun blank _ => bent_card.the_device_computing_the_next_configuration Nat List.length
--×                                                            (compute_the_area_of quantum) blank) (some_quartic_called here_and_now) := by
--×   induction turns generalizing here_and_now with
--×   | nil => rfl
--×   | cons _ rest ih => simp only [List.foldl_cons, ih, counted_simulate_is_simulate]

-- Episode13.lean, line 259
--× theorem counted_the_crank_is_the_crank (scale : Area) :
--×     some_quartic_called (the_crank scale)
--×       = bent_card.proportional_laws_accumulate_commutation_projections_called_TERM_LAMBDAS Nat List.length (compute_the_area_of scale) := by
--×   have house := the_walk_is_the_walk.2.2.2.2
--×   simp only [the_house, the_held_house] at house
--×   simp only [the_crank, bent_card.proportional_laws_accumulate_commutation_projections_called_TERM_LAMBDAS]
--×   exact (counted_any_number_of_turns_is_as_many_turns scale _ _).trans (by rw [house])

-- Episode13.lean, line 267
--× theorem counted_the_crank_and_the_fencepost_are_the_crank_and_the_fencepost (scale : Area) :
--×    some_quartic_called (the_crank_and_the_fencepost scale) = bent_card.fenceposts_must_be_preserved Nat List.length (compute_the_area_of scale) := by
--×   have crank := counted_the_crank_is_the_crank scale
--×   simp only [the_crank, some_quartic_called] at crank
--×   simp only [the_crank_and_the_fencepost, some_quartic_called, bent_card.fenceposts_must_be_preserved, bent_card.fencepost,
--×     false_shuffle_multiplies, the_number_of_marks_the_tapes_length]
--×   rw [← crank]

-- Episode13.lean, line 277
--× theorem the_area_arrives_at_the_same_pair (scale : Area) (as_many_cells_as_the_scale : compute_the_area_of scale = all_possible_variables) :
--×    some_quartic_called (the_crank_and_the_fencepost scale) = arrange_the_information_appropriately := by
--×   rw [counted_the_crank_and_the_fencepost_are_the_crank_and_the_fencepost, as_many_cells_as_the_scale]; rfl

-- Episode13.lean, line 281
--× theorem the_area_arrives_at_the_same_number (scale : Area) (as_many_cells_as_the_scale : compute_the_area_of scale = all_possible_variables) :
--×     (some_quartic_called (the_crank_and_the_fencepost scale)).1 * all_possible_variables / (some_quartic_called (the_crank_and_the_fencepost scale)).2
--×       = the_constant_factor_of_scaling_bullshit := by
--×   rw [the_area_arrives_at_the_same_pair scale as_many_cells_as_the_scale]; rfl

-- Episode13.lean, line 287
--× theorem there_is_an_area_with_as_many_cells_as_the_scale :
--×     compute_the_area_of (the_number_of_marks (List.replicate all_possible_variables zero)) = all_possible_variables := by
--×   rw [the_number_of_marks_the_tapes_length, List.length_replicate]

-- Episode13.lean, line 292
--× def the_free_variables := the_number_of_marks the_basis.the_reading * the_area_of_a_tape_in_blanks_is the_coordinate_system.gauss

-- Episode13.lean, line 295
--× def the_express_route := the_number_of_marks (from_the_inferred_end bent_card) - the_memory

-- Episode13.lean, line 303
--× def the_scale := raised the_free_variables the_express_route

-- Episode13.lean, line 306
--× def the_named_lambdas := the_crank the_scale
--× def arranged          := the_crank_and_the_fencepost the_scale

-- Episode13.lean, line 325
--× theorem taking_until_less_divides (the_one : Area) (there_is_one : 0 < compute_the_area_of the_one) (patience the_rest : Area)
--×     (patience_enough : compute_the_area_of the_rest ≤ compute_the_area_of patience) :
--×     compute_the_area_of (taking_until_less patience the_rest the_one) = compute_the_area_of the_rest / compute_the_area_of the_one := by
--×   induction patience generalizing the_rest with
--×   | tree _ =>
--×     have nothing : compute_the_area_of the_rest = 0 := Nat.le_zero.mp patience_enough
--×     simp only [taking_until_less, nothing, Nat.zero_div]; rfl
--×   | dt _ _ patience ih =>
--×     simp only [taking_until_less]
--×     split
--×     · rename_i h
--×       rw [Nat.div_eq_of_lt ((obviously_bigger _ _).1 h)]; rfl
--×     · rename_i h
--×       have not_less : compute_the_area_of the_one ≤ compute_the_area_of the_rest := Nat.le_of_not_lt (fun g => h ((obviously_bigger _ _).2 g))
--×       have still_enough : compute_the_area_of (the_rest - the_one) ≤ compute_the_area_of patience := by
--×         rw [the_double_lift_subtracts]; simp only [compute_the_area_of] at patience_enough; omega
--×       rw [palm_the_middle_card_adds, ih _ still_enough, the_double_lift_subtracts, Nat.div_eq_sub_div there_is_one not_less, Nat.add_comm]; rfl

-- Episode13.lean, line 343
--× theorem how_many_times_divides (the_whole the_one : Area) : compute_the_area_of (how_many_times the_whole the_one) = compute_the_area_of the_whole / compute_the_area_of the_one := by
--×   simp only [how_many_times]
--×   split
--×   · rename_i h
--×     exact taking_until_less_divides the_one ((coin_flip_when_there_is_a_cell _).1 h) _ _ (Nat.le_refl _)
--×   · rename_i h
--×     have no_cell : compute_the_area_of the_one = 0 := Nat.le_zero.mp (Nat.le_of_not_lt (fun g => h ((coin_flip_when_there_is_a_cell _).2 g)))
--×     rw [no_cell, Nat.div_zero]; rfl

-- Episode13.lean, line 353
--× theorem counted_the_scale_is_the_scale :
--×     compute_the_area_of the_free_variables = the_free_variable_count
--×       ∧ compute_the_area_of the_express_route = the_express_route_station_count
--×       ∧ compute_the_area_of the_scale = all_possible_variables := by
--×   have free : compute_the_area_of the_free_variables = the_free_variable_count := by
--×     simp only [the_free_variables, false_shuffle_multiplies, the_number_of_marks_the_tapes_length]; rfl
--×   have express : compute_the_area_of the_express_route = the_express_route_station_count := by
--×     simp only [the_express_route, the_double_lift_subtracts, the_number_of_marks_the_tapes_length, the_walk_is_the_walk.2.2.1]; rfl
--×   exact ⟨free, express, by simp only [the_scale, raised_raises, free, express]; rfl⟩

-- Episode13.lean, line 363
--× theorem counted_the_arrangement_is_the_arrangement : some_quartic_called arranged = arrange_the_information_appropriately :=
--×   the_area_arrives_at_the_same_pair the_scale counted_the_scale_is_the_scale.2.2

-- Episode13.lean, line 368
--× theorem a_partitioning_of_quotients_on_the_area (numerator denominator : Area) :
--×     (Quot.mk the_rational_idea_of_relativity_on_the_area (denominator * how_many_times numerator denominator, denominator)
--×         : Quot the_rational_idea_of_relativity_on_the_area)
--×       = Quot.mk the_rational_idea_of_relativity_on_the_area (numerator, denominator) :=
--×   Quot.sound (r := the_rational_idea_of_relativity_on_the_area) (by
--×     show ¬ (numerator * denominator < denominator * how_many_times numerator denominator * denominator)
--×     intro more
--×     have more' := (obviously_bigger _ _).1 more
--×     simp only [false_shuffle_multiplies, how_many_times_divides] at more'
--×     exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le more'
--×       (Nat.mul_le_mul_right (compute_the_area_of denominator) (the_constant_is_at_least_true (compute_the_area_of numerator) (compute_the_area_of denominator)))))

-- Episode13.lean, line 382
--× attribute [irreducible] the_crank the_crank_and_the_fencepost raised taking_until_less how_many_times the_scale

-- Episode13.lean, line 385
--× def the_constant_inferred_at (scale : Area) :
--×     { k : Area // (Quot.mk the_rational_idea_of_relativity_on_the_area
--×                         ((the_crank_and_the_fencepost scale).2 * k, (the_crank_and_the_fencepost scale).2)
--×                       : Quot the_rational_idea_of_relativity_on_the_area)
--×                     = Quot.mk the_rational_idea_of_relativity_on_the_area
--×                         ((the_crank_and_the_fencepost scale).1 * scale, (the_crank_and_the_fencepost scale).2) } :=
--×   ⟨how_many_times ((the_crank_and_the_fencepost scale).1 * scale) (the_crank_and_the_fencepost scale).2,
--×    a_partitioning_of_quotients_on_the_area ((the_crank_and_the_fencepost scale).1 * scale) (the_crank_and_the_fencepost scale).2⟩

-- Episode13.lean, line 395
--× theorem counted_the_division_is_the_division (numerator denominator scale : Area) (n d s : Nat)
--×     (the_numerator : compute_the_area_of numerator = n) (the_denominator : compute_the_area_of denominator = d) (the_scale_of_it : compute_the_area_of scale = s) :
--×     compute_the_area_of (how_many_times (numerator * scale) denominator) = n * s / d := by
--×   rw [how_many_times_divides, false_shuffle_multiplies, the_numerator, the_denominator, the_scale_of_it]

-- Episode13.lean, line 400
--× theorem episode_eights_constant_is_its_own_division :
--×     arrange_the_information_appropriately.1 * all_possible_variables / arrange_the_information_appropriately.2
--×       = the_constant_factor_of_scaling_bullshit := rfl

-- Episode13.lean, line 404
--× theorem counted_the_constant_at_any_such_scale (scale : Area) (as_many_cells_as_the_scale : compute_the_area_of scale = all_possible_variables) :
--×     compute_the_area_of (the_constant_inferred_at scale).val = the_constant_factor_of_scaling_bullshit :=
--×   (counted_the_division_is_the_division _ _ _ _ _ _
--×     (congrArg Prod.fst (the_area_arrives_at_the_same_pair scale as_many_cells_as_the_scale))
--×     (congrArg Prod.snd (the_area_arrives_at_the_same_pair scale as_many_cells_as_the_scale))
--×     as_many_cells_as_the_scale).trans episode_eights_constant_is_its_own_division

-- Episode13.lean, line 414
--× def the_constant_can_be_inferred_on_the_area := the_constant_inferred_at the_scale

-- Episode13.lean, line 417
--× def the_constant := (the_constant_inferred_at the_scale).val

-- Episode13.lean, line 421
--× theorem counted_the_constant_is_the_constant :
--×     compute_the_area_of (the_constant_inferred_at the_scale).val = the_constant_factor_of_scaling_bullshit :=
--×   counted_the_constant_at_any_such_scale the_scale counted_the_scale_is_the_scale.2.2

-- Episode13.lean, line 443
--× def four_bullshit_values : List Bullshit :=
--×   [the_bullshit_of (the_arm true true),  the_bullshit_of (the_arm true false),
--×    the_bullshit_of (the_arm false true), the_bullshit_of (the_arm false false)]

-- Episode13.lean, line 448
--× theorem one_cell_is_no_santa : the_bullshit_of ast₁ = no_santa := rfl

-- Episode13.lean, line 452
--× theorem counted_the_arms_are_the_arms :
--×     [compute_the_area_of (the_arm true true), compute_the_area_of (the_arm true false), compute_the_area_of (the_arm false true), compute_the_area_of (the_arm false false)]
--×       = [the_arm_weight true true, the_arm_weight true false, the_arm_weight false true, the_arm_weight false false] := by decide

-- Episode13.lean, line 457
--× theorem the_four_on_the_meter :
--×     four_bullshit_values.map (fun bullshit => bullshit.meter.length)
--×       = [the_memory_tape.length + the_fencepost_bug, the_coordinate_system.gauss.length + the_fencepost_bug,
--×          the_memory_tape.length + the_fencepost_bug, the_memory_tape.length + the_fencepost_bug] := by decide

-- Episode13.lean, line 495
--× def the_experience : Closure.{0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0} :=
--×   .different zero (the_bullshit_of (the_arm false true)) (the_bullshit_of (the_arm true false))
--×     (some (the_bullshit_of.{0,0} (the_arm false true) < the_bullshit_of.{0,0} (the_arm true false)))
--× def the_interpretation : Closure.{0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0} :=
--×   .different zero (the_bullshit_of (the_arm true true)) (the_bullshit_of (the_arm false false))
--×     (some (the_bullshit_of.{0,0} (the_arm true true) < the_bullshit_of.{0,0} (the_arm false false)))

-- Episode13.lean, line 503
--× theorem the_experience_is_under_the_interpretation_and_not_back :
--×     the_experience ≤ the_interpretation ∧ ¬ (the_interpretation ≤ the_experience) := by
--×   constructor
--×   · show Closure.le the_experience the_interpretation
--×     simp only [the_experience, the_interpretation, Closure.le, Closure.implying_implication]
--×     exact ⟨trivial, (the_bullshits_order_is_the_count _ _).2 (by decide), (the_bullshits_order_is_the_count _ _).2 (by decide),
--×       fun strictly => absurd ((the_bullshits_order_is_the_count _ _).1 strictly.1) (by decide)⟩
--×   · show ¬ Closure.le the_interpretation the_experience
--×     simp only [the_experience, the_interpretation, Closure.le, Closure.implying_implication]
--×     exact fun back => absurd ((the_bullshits_order_is_the_count _ _).1 back.2.2.1) (by decide)

-- Episode13.lean, line 522
--× theorem the_interpretation_has_no_gap_and_the_experiences_is_the_bent_card :
--×     the_bullshit_of the_gap_of_the_interpretation = no_presents
--×       ∧ the_gap_of_the_experience = the_coefficient
--×       ∧ compute_the_area_of the_gap_of_the_experience = bent_card := ⟨rfl, rfl, by decide⟩

-- Episode13.lean, line 532
--× theorem the_gap_runs_one_way :
--×     the_bullshit_of the_gap_of_the_interpretation ≤ the_bullshit_of the_gap_of_the_experience
--×       ∧ ¬ (the_bullshit_of the_gap_of_the_experience ≤ the_bullshit_of the_gap_of_the_interpretation) :=
--×   ⟨(the_bullshits_order_is_the_count _ _).2 (by decide), fun back => absurd ((the_bullshits_order_is_the_count _ _).1 back) (by decide)⟩

-- Episode13.lean, line 556
--× theorem the_same_says_the_gap_is_the_same_difference :
--×     the_same_inferred_from_the_experience.truth
--×       = ((Quot.mk TruthOrder (the_bullshit_of.{0,0} the_gap_of_the_interpretation) : Quot TruthOrder)
--×           = Quot.mk TruthOrder (the_bullshit_of.{0,0} the_gap_of_the_experience)) := rfl

-- Episode13.lean, line 582
--× noncomputable def the_conclusion_from_the_experience : Closure := the_knower_of_the_experience.same_difference.your_conclusion
--× noncomputable def the_alpha_from_the_experience : Closure := the_knower_of_the_experience.α

-- Episode13.lean, line 585
--× theorem alpha_ends_on_the_same :
--×     ∃ (this that : FACT) (low slip : Bullshit) (p q : Option Prop),
--×       the_alpha_from_the_experience = .inferred this that low slip p (.different the_same_inferred_from_the_experience low slip q) :=
--×   ⟨_, _, _, _, _, _, rfl⟩

-- Episode13.lean, line 593
--× set_option maxHeartbeats 400000 in
--× theorem the_knower_of_the_experience_reads_one_way :
--×     the_knower_of_the_experience.inferred? the_conclusion_from_the_experience the_alpha_from_the_experience := by
--×   show Closure.le the_conclusion_from_the_experience the_alpha_from_the_experience
--×   unfold the_conclusion_from_the_experience the_alpha_from_the_experience the_knower_of_the_experience
--×   simp only [assembly_instructions.«ITS_YOU_!!», Closure.le]
--×   refine Or.inl ⟨Or.inl trivial, (the_bullshits_order_is_the_count.{0,0} _ _).2 (Nat.le_refl _), ?_, id⟩
--×   show Bullshit.le _ _
--×   conv => arg 1; whnf
--×   conv => arg 2; whnf
--×   conv => whnf
--×   exact ⟨rfl, rfl, id, (trivial : True), (the_bullshits_order_is_the_count.{0,0} _ _).2 (Nat.le_refl _), (trivial : True)⟩
--× set_option maxHeartbeats 400000 in
--× theorem and_the_device_reads_it_back :
--×     the_knower_of_the_experience.inferred? the_alpha_from_the_experience the_conclusion_from_the_experience := by
--×   show Closure.le the_alpha_from_the_experience the_conclusion_from_the_experience
--×   unfold the_conclusion_from_the_experience the_alpha_from_the_experience the_knower_of_the_experience
--×   simp only [assembly_instructions.«ITS_YOU_!!», Closure.le]
--×   refine Or.inl ⟨Or.inl trivial, (the_bullshits_order_is_the_count.{0,0} _ _).2 (Nat.le_refl _), ?_, id⟩
--×   show Bullshit.le _ _
--×   conv => arg 1; whnf
--×   conv => arg 2; whnf
--×   conv => whnf
--×   exact ⟨rfl, rfl, id, (trivial : True), (the_bullshits_order_is_the_count.{0,0} _ _).2 (Nat.le_refl _), (trivial : True)⟩

-- Episode13.lean, line 623
--× def the_executed_count (tape : List FACT) : Nat := count_the_meanings (the_marks tape)

-- Episode13.lean, line 625
--× theorem the_executed_count_is_the_length : the_executed_count = List.length := by
--×   funext tape
--×   simp only [the_executed_count, the_marks, the_proof_counts_every_fact, the_tape_of_symbols_has_no_ast, Nat.zero_add]

-- Episode13.lean, line 629
--× def the_executed_pair : Nat × Nat := bent_card.fenceposts_must_be_preserved Nat the_executed_count all_possible_variables

-- Episode13.lean, line 631
--× theorem the_executed_pair_is_the_arrangement : the_executed_pair = arrange_the_information_appropriately := by
--×   unfold the_executed_pair; rw [the_executed_count_is_the_length]; rfl

-- Episode13.lean, line 634
--× theorem the_executed_pair_is_the_area_counted : the_executed_pair = some_quartic_called arranged :=
--×   the_executed_pair_is_the_arrangement.trans counted_the_arrangement_is_the_arrangement.symm

-- Episode13.lean, line 637
--× def the_executed_natural : Nat := the_executed_pair.1 * all_possible_variables / the_executed_pair.2

-- Episode13.lean, line 639
--× def what_did_execute_count? : String :=
--×   let digits := Nat.toDigits the_free_variable_count the_executed_natural
--×   String.ofList (digits.take (digits.length - the_express_route_station_count) ++ '.' :: digits.drop (digits.length - the_express_route_station_count))
--× #eval what_did_execute_count?
--× #print axioms what_did_execute_count?

-- Episode13.lean, line 663
--× def one_more (a : Area) : Area := .dt zero another_zero a

-- Episode13.lean, line 665
--× theorem counted_an_arm_is_its_weight (this that : Bool) : compute_the_area_of (the_arm this that) = the_arm_weight this that := by
--×   cases this <;> cases that <;> decide

-- Episode13.lean, line 669
--× def the_trace_of_the_arms       : Area := the_arm true true + the_arm false false
--× def the_determinant_of_the_arms : Area := the_arm true true * the_arm false false - the_arm true false * the_arm false true

-- Episode13.lean, line 672
--× theorem counted_the_trace_of_the_arms_is_the_trace : compute_the_area_of the_trace_of_the_arms = Measurement.the_trace := by
--×   simp only [the_trace_of_the_arms, palm_the_middle_card_adds, counted_an_arm_is_its_weight]; rfl
--× theorem counted_the_determinant_of_the_arms_is_the_determinant : compute_the_area_of the_determinant_of_the_arms = the_determinant := by
--×   simp only [the_determinant_of_the_arms, the_double_lift_subtracts, false_shuffle_multiplies, counted_an_arm_is_its_weight]; rfl

-- Episode13.lean, line 677
--× theorem the_trace_of_the_arms_is_the_middle_coefficient : as_many the_trace_of_the_arms the_trace := by
--×   rw [as_many_is_the_same_count, counted_the_trace_of_the_arms_is_the_trace, the_walk_is_the_walk.2.2.2.1]; rfl
--× theorem the_determinant_of_the_arms_is_the_outer_coefficients : as_many the_determinant_of_the_arms (the_coefficient * the_memory) := by
--×   rw [as_many_is_the_same_count, counted_the_determinant_of_the_arms_is_the_determinant, false_shuffle_multiplies,
--×     the_walk_is_the_walk.2.1, the_walk_is_the_walk.2.2.1]; rfl
--× theorem the_discriminant_of_the_arms_is_the_clock_times_the_coupling :
--×     as_many (the_trace_of_the_arms * the_trace_of_the_arms
--×                - the_number_of_marks the_basis.the_reading * the_area_of_a_tape_in_blanks_is the_basis.the_reading * the_determinant_of_the_arms)
--×             (the_number_of_marks the_basis.the_reading * the_area_of_a_tape_in_blanks_is the_basis.the_reading * the_memory * the_frame) := by
--×   rw [as_many_is_the_same_count]
--×   simp only [the_double_lift_subtracts, false_shuffle_multiplies, counted_the_trace_of_the_arms_is_the_trace,
--×     counted_the_determinant_of_the_arms_is_the_determinant, the_number_of_marks_the_tapes_length,
--×     the_walk_is_the_walk.2.2.1, the_frame, the_fencepost, bent_card.fencepost]
--×   rfl
--× theorem the_arms_are_the_memory_and_the_frame :
--×     the_arm true true = the_memory ∧ the_arm true false = the_frame ∧ the_arm false true = the_memory ∧ the_arm false false = the_memory :=
--×   ⟨rfl, rfl, rfl, rfl⟩

-- Episode13.lean, line 696
--× def the_walks_on_the_area : Area → Bool → Bool → Area
--×   | .tree _,      a, b => if a = b then ast₁ else ast₀
--×   | .dt _ _ rest, a, b => the_arm a true * the_walks_on_the_area rest true b + the_arm a false * the_walks_on_the_area rest false b
--× def the_closed_walks_on_the_area (clock : Area) : Area :=
--×   the_walks_on_the_area clock true true + the_walks_on_the_area clock false false

-- Episode13.lean, line 702
--× theorem counted_the_walks_are_the_walks (clock : Area) (a b : Bool) :
--×     compute_the_area_of (the_walks_on_the_area clock a b) = the_walks (compute_the_area_of clock) a b := by
--×   induction clock generalizing a b with
--×   | tree _ => cases a <;> cases b <;> rfl
--×   | dt _ _ rest ih =>
--×     simp only [the_walks_on_the_area, compute_the_area_of, the_walks, palm_the_middle_card_adds, false_shuffle_multiplies, ih, counted_an_arm_is_its_weight]

-- Episode13.lean, line 709
--× theorem the_walks_on_the_area_obey_the_table (clock : Area) (a b : Bool) :
--×     as_many (the_walks_on_the_area (one_more (one_more clock)) a b + the_determinant_of_the_arms * the_walks_on_the_area clock a b)
--×             (the_trace_of_the_arms * the_walks_on_the_area (one_more clock) a b) := by
--×   rw [as_many_is_the_same_count]
--×   have trace := counted_the_trace_of_the_arms_is_the_trace
--×   have determinant := counted_the_determinant_of_the_arms_is_the_determinant
--×   simp only [palm_the_middle_card_adds, false_shuffle_multiplies, counted_the_walks_are_the_walks, one_more, compute_the_area_of, trace, determinant]
--×   exact the_walks_obey_the_table (compute_the_area_of clock) a b

-- Episode13.lean, line 718
--× theorem the_closed_walks_on_the_area_obey_the_table (clock : Area) :
--×     as_many (the_closed_walks_on_the_area (one_more (one_more clock)) + the_determinant_of_the_arms * the_closed_walks_on_the_area clock)
--×             (the_trace_of_the_arms * the_closed_walks_on_the_area (one_more clock)) := by
--×   rw [as_many_is_the_same_count]
--×   have trace := counted_the_trace_of_the_arms_is_the_trace
--×   have determinant := counted_the_determinant_of_the_arms_is_the_determinant
--×   simp only [the_closed_walks_on_the_area, palm_the_middle_card_adds, false_shuffle_multiplies, counted_the_walks_are_the_walks, one_more, compute_the_area_of,
--×     trace, determinant]
--×   exact the_closed_walks_obey_the_table (compute_the_area_of clock)

-- Episode13.lean, line 812
--× def the_area_read_as_the_naturals := Meanings.CountedAsNat.correspondence (α := Area)
--× def the_account_read_as_the_integers := Meanings.BalancedAsInt.correspondence (α := Account)
--× def two_accounts_read_as_the_ratios := Meanings.BalancedAsInt.ratioCorrespondence (α := Account)

-- Episode13.lean, line 820
--× theorem there_is_always_one_more_area (a : Area) : ∃ b, a < b :=
--×   Meanings.CountedAsNat.nothing_counted_is_largest a

-- Episode13.lean, line 823
--× theorem no_walk_down_the_areas_goes_on_forever : WellFounded (fun a b : Area => a < b) :=
--×   Meanings.CountedAsNat.less_is_well_founded

-- Episode13.lean, line 832
--× theorem the_first_area_where_a_statement_holds (the_statement : Area → Prop)
--×     (read_alike : Meanings.CountedAsNat.ReadAlike the_statement) (a : Area) (holds : the_statement a) :
--×     ∃ b, the_statement b ∧ ∀ c, c < b → ¬ the_statement c :=
--×   Meanings.CountedAsNat.the_least_counted_without_the_click the_statement read_alike a holds

-- Episode13.lean, line 863
--× theorem the_residual_as_a_rate_is_the_table_as_a_line_on_the_account (u v w : Account) :
--×     the_same ((v * v - w * u) - (v * v + holding the_trace_of_the_arms * (u * v) + holding the_determinant_of_the_arms * (u * u)))
--×              (- (u * (w + holding the_trace_of_the_arms * v + holding the_determinant_of_the_arms * u))) := by
--×   rw [the_same_is_the_same_balance]
--×   simp only [balance_of_palm_the_middle_card, balance_of_less, balance_of_false_shuffle, balance_of_holding, balance_turned_over,
--×     counted_the_trace_of_the_arms_is_the_trace, counted_the_determinant_of_the_arms_is_the_determinant]
--×   exact the_residual_as_a_rate_is_the_table_as_a_line (balance u) (balance v) (balance w)

-- Episode13.lean, line 875
--× def the_basis_held  : Account := holding (the_number_of_marks the_basis.the_reading)
--× def the_inference_held : Account := holding (the_number_of_marks the_only_logical_inconsistency.infer)
--× def the_basis_twice_held : Account := holding (the_number_of_marks the_basis.the_reading * the_area_of_a_tape_in_blanks_is the_basis.the_reading)
--× def the_basis_by_the_inference_held : Account :=
--×   holding (the_number_of_marks the_basis.the_reading * the_area_of_a_tape_in_blanks_is the_only_logical_inconsistency.infer)
--× def the_memory_held : Account := holding the_memory

-- Episode13.lean, line 882
--× theorem the_small_accounts_balance :
--×     balance nothing_held = 0 ∧ balance the_basis_held = 2 ∧ balance the_inference_held = 3 ∧ balance the_basis_twice_held = 4
--×       ∧ balance the_basis_by_the_inference_held = 6 ∧ balance the_memory_held = 18 := by
--×   simp only [nothing_held, the_basis_held, the_inference_held, the_basis_twice_held, the_basis_by_the_inference_held, the_memory_held,
--×     balance_of_holding, false_shuffle_multiplies, the_number_of_marks_the_tapes_length, the_walk_is_the_walk.2.2.1]
--×   exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

-- Episode13.lean, line 890
--× def the_table_polynomial_on_the_account (a r z : Account) : Account := z * z - the_basis_held * a * z + (a * a - r)
--× def the_table_slope_on_the_account (a z : Account) : Account := the_basis_held * z - the_basis_held * a

-- Episode13.lean, line 893
--× theorem the_balance_of_the_table_polynomial (a r z : Account) :
--×     balance (the_table_polynomial_on_the_account a r z) = the_table_polynomial (balance a) (balance r) (balance z) := by
--×   simp only [the_table_polynomial_on_the_account, the_table_polynomial, balance_of_palm_the_middle_card, balance_of_less, balance_of_false_shuffle,
--×     the_small_accounts_balance.2.1]
--× theorem the_balance_of_the_table_slope (a z : Account) :
--×     balance (the_table_slope_on_the_account a z) = the_table_slope (balance a) (balance z) := by
--×   simp only [the_table_slope_on_the_account, the_table_slope, balance_of_less, balance_of_false_shuffle, the_small_accounts_balance.2.1]

-- Episode13.lean, line 901
--× theorem the_slope_squared_less_four_of_the_polynomial_is_the_round_trip_on_the_account (a r z : Account) :
--×     the_same (the_table_slope_on_the_account a z * the_table_slope_on_the_account a z
--×                 - the_basis_twice_held * the_table_polynomial_on_the_account a r z)
--×              (the_basis_twice_held * r) := by
--×   rw [the_same_is_the_same_balance]
--×   simp only [balance_of_less, balance_of_false_shuffle, the_balance_of_the_table_polynomial, the_balance_of_the_table_slope,
--×     the_small_accounts_balance.2.2.2.1]
--×   exact the_slope_squared_less_four_of_the_polynomial_is_the_round_trip (balance a) (balance r) (balance z)

-- Episode13.lean, line 911
--× theorem struck_the_polynomial_is_a_square_on_the_account (z : Account) :
--×     the_same (the_table_polynomial_on_the_account the_memory_held (nothing_held * the_memory_held) z)
--×              ((z - the_memory_held) * (z - the_memory_held))
--×       ∧ the_same (the_table_slope_on_the_account the_memory_held the_memory_held) nothing_held := by
--×   rw [the_same_is_the_same_balance, the_same_is_the_same_balance]
--×   simp only [balance_of_less, balance_of_false_shuffle, the_balance_of_the_table_polynomial, the_balance_of_the_table_slope,
--×     the_small_accounts_balance.1, the_small_accounts_balance.2.2.2.2.2]
--×   exact struck_the_polynomial_is_a_square (balance z)

-- Episode13.lean, line 920
--× theorem struck_the_step_is_half_the_distance_on_the_account (z : Account) :
--×     the_same (the_basis_held * the_table_polynomial_on_the_account the_memory_held (nothing_held * the_memory_held) z)
--×              ((z - the_memory_held) * the_table_slope_on_the_account the_memory_held z) := by
--×   rw [the_same_is_the_same_balance]
--×   simp only [balance_of_less, balance_of_false_shuffle, the_balance_of_the_table_polynomial, the_balance_of_the_table_slope,
--×     the_small_accounts_balance.1, the_small_accounts_balance.2.1, the_small_accounts_balance.2.2.2.2.2]
--×   exact struck_the_step_is_half_the_distance (balance z)

-- Episode13.lean, line 929
--× def the_cubic_action_on_the_account (x : Account) : Account :=
--×   the_basis_held * holding the_coefficient * x * x * x - the_inference_held * holding the_trace * x * x
--×     + the_basis_by_the_inference_held * holding the_memory * x

-- Episode13.lean, line 933
--× theorem the_balance_of_the_residual_is_the_mirror_residual (x : Account) :
--×     balance (the_residual_on_the_account x) = the_mirror_residual (balance x) := by
--×   simp only [the_residual_on_the_account, the_mirror_residual, balance_of_palm_the_middle_card, balance_of_less, balance_of_false_shuffle,
--×     balance_of_holding, the_walk_is_the_walk.2.1, the_walk_is_the_walk.2.2.1, the_walk_is_the_walk.2.2.2.1]
--× theorem the_balance_of_the_cubic_action (x : Account) :
--×     balance (the_cubic_action_on_the_account x) = the_cubic_action (balance x) := by
--×   simp only [the_cubic_action_on_the_account, the_cubic_action, balance_of_palm_the_middle_card, balance_of_less, balance_of_false_shuffle,
--×     balance_of_holding, the_walk_is_the_walk.2.1, the_walk_is_the_walk.2.2.1, the_walk_is_the_walk.2.2.2.1,
--×     the_small_accounts_balance.2.1, the_small_accounts_balance.2.2.1, the_small_accounts_balance.2.2.2.2.1]

-- Episode13.lean, line 943
--× theorem the_residual_is_the_derivative_of_the_action_on_the_account (x h : Account) :
--×     the_same (the_cubic_action_on_the_account (x + h) - the_cubic_action_on_the_account x)
--×              (the_basis_by_the_inference_held * h * the_residual_on_the_account x
--×                 + h * h * (the_basis_by_the_inference_held * holding the_coefficient * x - the_inference_held * holding the_trace)
--×                 + the_basis_held * holding the_coefficient * h * h * h) := by
--×   rw [the_same_is_the_same_balance]
--×   simp only [balance_of_palm_the_middle_card, balance_of_less, balance_of_false_shuffle, balance_of_holding, the_balance_of_the_cubic_action,
--×     the_balance_of_the_residual_is_the_mirror_residual, the_walk_is_the_walk.2.1, the_walk_is_the_walk.2.2.2.1,
--×     the_small_accounts_balance.2.1, the_small_accounts_balance.2.2.1, the_small_accounts_balance.2.2.2.2.1]
--×   exact the_residual_is_the_derivative_of_the_action (balance x) (balance h)

-- Episode13.lean, line 982
--× theorem the_sixteen_steps_built_and_counted :
--×     the_sixteen_steps.map (fun step => (compute_the_area_of (what_compile_builds step), compute_the_area_of (what_execute_counts step)))
--×       = [(18, 18), (18, 5), (18, 18), (18, 18),
--×          (5, 18),  (5, 5),  (5, 18),  (5, 18),
--×          (18, 18), (18, 5), (18, 18), (18, 18),
--×          (18, 18), (18, 5), (18, 18), (18, 18)] := by decide

-- Episode13.lean, line 990
--× theorem nine_are_level_on_the_memory_one_on_the_frame_three_short_and_three_over :
--×     (the_sixteen_steps.filter fun step => decide (as_many (what_compile_builds step) (what_execute_counts step))
--×         && decide (as_many (what_compile_builds step) the_memory)).length = 9
--×       ∧ (the_sixteen_steps.filter fun step => decide (as_many (what_compile_builds step) (what_execute_counts step))
--×         && decide (as_many (what_compile_builds step) the_frame)) = [((true, false), (true, false))]
--×       ∧ (the_sixteen_steps.filter fun step => decide (what_execute_counts step < what_compile_builds step))
--×           = [((true, true), (true, false)), ((false, true), (true, false)), ((false, false), (true, false))]
--×       ∧ (the_sixteen_steps.filter fun step => decide (what_compile_builds step < what_execute_counts step))
--×           = [((true, false), (true, true)), ((true, false), (false, true)), ((true, false), (false, false))] := by decide

-- Episode13.lean, line 1001
--× theorem what_is_left_is_always_the_bent_card :
--×     (the_sixteen_steps.filter fun step => decide (¬ as_many (what_compile_builds step) (what_execute_counts step))).all
--×       (fun step => decide (as_many (what_compile_builds step - what_execute_counts step + (what_execute_counts step - what_compile_builds step))
--×                                    the_coefficient)) = true := by decide

-- Episode13.lean, line 1030
--× def the_zero_on_the_true  : Bullshit.{0,0,0,0} := .zero (bitFACT true)
--× def the_zero_on_the_false : Bullshit.{0,0,0,0} := .zero (bitFACT false)

-- Episode13.lean, line 1034
--× theorem the_true_and_the_false_are_not_ordered :
--×     ¬ (the_zero_on_the_true ≤ the_zero_on_the_false) ∧ ¬ (the_zero_on_the_false ≤ the_zero_on_the_true) := by
--×   have truth_is_not_false : (bitFACT false).truth ≠ (bitFACT true).truth := fun h => cast h.symm (rfl : true = true)
--×   exact ⟨fun h => truth_is_not_false (show (bitFACT true).truth = (bitFACT false).truth from h).symm,
--×          fun h => truth_is_not_false (show (bitFACT false).truth = (bitFACT true).truth from h)⟩

-- Episode13.lean, line 1041
--× theorem both_are_under_no_santa : the_zero_on_the_true ≤ no_santa.{0,0} ∧ the_zero_on_the_false ≤ no_santa.{0,0} :=
--×   ⟨(trivial : True), (trivial : True)⟩

-- Episode13.lean, line 1046
--× theorem the_true_is_the_false_in_the_quotient :
--×     (Quot.mk TruthOrder the_zero_on_the_true : Quot TruthOrder) = Quot.mk TruthOrder the_zero_on_the_false :=
--×   (Quot.sound (r := TruthOrder) both_are_under_no_santa.1).trans (Quot.sound (r := TruthOrder) both_are_under_no_santa.2).symm

-- Episode13.lean, line 1131
--× theorem the_knowers_pair_is_the_area_counted (clock : Bool) : the_knowers_pair clock = some_quartic_called arranged :=
--×   (the_knowers_pair_is_the_arrangement clock).trans counted_the_arrangement_is_the_arrangement.symm

-- Episode13.lean, line 1134
--× def the_knowers_natural (clock : Bool) : Nat := (the_knowers_pair clock).1 * all_possible_variables / (the_knowers_pair clock).2

-- Episode13.lean, line 1136
--× def what_does_the_knower_read? (clock : Bool) : String :=
--×   let digits := Nat.toDigits the_free_variable_count (the_knowers_natural clock)
--×   String.ofList (digits.take (digits.length - the_express_route_station_count) ++ '.' :: digits.drop (digits.length - the_express_route_station_count))

-- Episode13.lean, line 1140
--× def the_knower_believes? := what_does_the_knower_read? true
--× def the_knower_disbelieves? := what_does_the_knower_read? false
--× #eval the_knower_believes?
--× #print axioms the_knower_believes?
--× #eval the_knower_disbelieves?
--× #print axioms the_knower_disbelieves?

-- Episode13.lean, line 1149
--× theorem the_two_clocks_are_apart (fact : FACT) (rest : List FACT) :
--×     the_abstraction_the_list_indicates false (fact :: rest) < the_abstraction_the_list_indicates true (fact :: rest)
--×       ∧ ¬ (the_abstraction_the_list_indicates true (fact :: rest) ≤ the_abstraction_the_list_indicates false (fact :: rest)) :=
--×   ⟨rfl, fun h => Bool.noConfusion h⟩

-- Episode13.lean, line 1157
--× def truth_before_click : List FACT → Abstraction
--×   | []           => carefully_chosen_variable_names
--×   | fact :: rest => .compile fact δδxᵢ (.execute fact δδxᵢ (truth_before_click rest))

-- Episode13.lean, line 1162
--× theorem the_truth_is_under_the_click (fact : FACT) (rest : Abstraction) :
--×     Abstraction.compile fact δδxᵢ rest < Abstraction.execute fact δδxᵢ rest
--×       ∧ ¬ (Abstraction.execute fact δδxᵢ rest ≤ Abstraction.compile fact δδxᵢ rest) :=
--×   ⟨rfl, fun h => Bool.noConfusion h⟩

-- Episode13.lean, line 1168
--× def each_fact_twice : List FACT → List FACT
--×   | []           => []
--×   | fact :: rest => fact :: fact :: each_fact_twice rest

-- Episode13.lean, line 1173
--× theorem truth_before_click_is_the_false_clock (tape : List FACT) :
--×     truth_before_click tape = the_abstraction_the_list_indicates false (each_fact_twice tape) := by
--×   induction tape with
--×   | nil => rfl
--×   | cons fact rest ih => simp only [truth_before_click, each_fact_twice, the_abstraction_the_list_indicates, ih]

-- Episode13.lean, line 1180
--× theorem truth_before_click_reads_twice_the_tape_and_the_names (tape : List FACT) :
--×     (truth_before_click tape).equivalation.length = the_basis.the_reading.length * tape.length + the_fencepost_bug := by
--×   induction tape with
--×   | nil => rfl
--×   | cons fact rest ih =>
--×     simp only [truth_before_click, Abstraction.equivalation, List.length_cons, ih]
--×     rw [show the_basis.the_reading.length = 2 from rfl]; omega

-- Episode13.lean, line 1189
--× def the_count_of_truth_before_click (tape : List FACT) : Nat :=
--×   ((truth_before_click tape).equivalation.length - the_fencepost_bug) / the_basis.the_reading.length

-- Episode13.lean, line 1192
--× theorem the_count_of_truth_before_click_is_the_length : the_count_of_truth_before_click = List.length := by
--×   funext tape
--×   simp only [the_count_of_truth_before_click, truth_before_click_reads_twice_the_tape_and_the_names, Nat.add_sub_cancel]
--×   exact Nat.mul_div_cancel_left _ (by decide)

-- Episode13.lean, line 1197
--× def the_pair_of_truth_before_click : Nat × Nat :=
--×   bent_card.fenceposts_must_be_preserved Nat the_count_of_truth_before_click all_possible_variables

-- Episode13.lean, line 1200
--× theorem the_pair_of_truth_before_click_is_the_arrangement : the_pair_of_truth_before_click = arrange_the_information_appropriately := by
--×   unfold the_pair_of_truth_before_click; rw [the_count_of_truth_before_click_is_the_length]; rfl

-- Episode13.lean, line 1203
--× def what_does_truth_before_click_read? : String :=
--×   let digits := Nat.toDigits the_free_variable_count
--×     ((the_pair_of_truth_before_click).1 * all_possible_variables / (the_pair_of_truth_before_click).2)
--×   String.ofList (digits.take (digits.length - the_express_route_station_count) ++ '.' :: digits.drop (digits.length - the_express_route_station_count))
--× #eval what_does_truth_before_click_read?
--× #print axioms what_does_truth_before_click_read?

-- Episode13.lean, line 1211
--× def the_coin_a_fact_shows (fact : FACT) : Bool := @decide fact.truth fact.click
--× def the_knowers_interpretation_of_three_facts (a b c : FACT) : Account :=
--×   the_knowers_interpretation (the_coin_a_fact_shows a) (the_coin_a_fact_shows b) (the_coin_a_fact_shows c)

-- Episode13.lean, line 1215
--× theorem the_alternating_facts_read_the_bent_card_and_the_still_facts_read_nothing :
--×     the_same (the_knowers_interpretation_of_three_facts (bitFACT true) (bitFACT false) (bitFACT true)
--×                 + the_knowers_interpretation_of_three_facts (bitFACT false) (bitFACT true) (bitFACT false))
--×              (holding the_coefficient)
--×       ∧ the_same (the_knowers_interpretation_of_three_facts (bitFACT true) (bitFACT true) (bitFACT true)
--×                 + the_knowers_interpretation_of_three_facts (bitFACT false) (bitFACT false) (bitFACT false))
--×              nothing_held := by decide

-- Episode13.lean, line 1227
--× def the_connected_steps : List ((Bool × Bool) × (Bool × Bool)) := the_sixteen_steps.filter fun step => step.1.2 == step.2.1
--× def the_clock_of_a_step (step : (Bool × Bool) × (Bool × Bool)) : Bool × Bool × Bool := (step.1.1, step.1.2, step.2.2)

-- Episode13.lean, line 1230
--× theorem the_connected_steps_are_the_eight_clocks :
--×     the_connected_steps.map the_clock_of_a_step
--×       = [(true, true, true), (true, true, false), (true, false, true), (true, false, false),
--×          (false, true, true), (false, true, false), (false, false, true), (false, false, false)] := by decide

-- Episode13.lean, line 1237
--× theorem four_of_the_eight_are_level_and_four_go_under :
--×     (the_connected_steps.filter fun step => decide (as_many (what_compile_builds step) (what_execute_counts step))).map the_clock_of_a_step
--×         = [(true, true, true), (false, true, true), (false, false, true), (false, false, false)]
--×       ∧ (the_connected_steps.filter fun step => decide (what_execute_counts step < what_compile_builds step)).map the_clock_of_a_step
--×         = [(true, true, false), (false, true, false)]
--×       ∧ (the_connected_steps.filter fun step => decide (what_compile_builds step < what_execute_counts step)).map the_clock_of_a_step
--×         = [(true, false, true), (true, false, false)]
--×       ∧ the_connected_steps.contains ((true, false), (true, false)) = false := by decide

-- Episode13.lean, line 1248
--× theorem the_knower_reads_the_after_clause_backwards (step : (Bool × Bool) × (Bool × Bool)) :
--×     the_knowers_interpretation (the_clock_of_a_step step).1 (the_clock_of_a_step step).2.1 (the_clock_of_a_step step).2.2
--×       = the_coin_held_or_owed step.1.1 * (- Account.holding (the_arm step.2.2 step.1.2)) := rfl

-- Episode13.lean, line 1254
--× def the_three_comparisons (step : (Bool × Bool) × (Bool × Bool)) : List (Bool × Bool) :=
--×   [(step.1.1, step.1.2), (step.1.2, step.2.1), (step.2.1, step.2.2)]

-- Episode13.lean, line 1258
--× theorem the_limit_overlapped_is_the_tape :
--×     the_three_comparisons ((true, false), (true, false)) = [(true, false), (false, true), (true, false)] := rfl

-- Episode13.lean, line 1263
--× theorem the_clock_compared_is_the_other_clock :
--×     (the_three_comparisons ((true, false), (true, false))).map (fun arm => the_arm_stores_a_fact_that_can_click arm.1 arm.2)
--×         = [false, true, false]
--×       ∧ (the_three_comparisons ((false, true), (false, true))).map (fun arm => the_arm_stores_a_fact_that_can_click arm.1 arm.2)
--×         = [true, false, true] := by decide

-- Episode13.lean, line 1270
--× theorem the_tape_is_the_frame_the_memory_the_frame :
--×     (the_three_comparisons ((true, false), (true, false))).map (fun arm => the_arm arm.1 arm.2) = [the_frame, the_memory, the_frame] := rfl

-- Episode13.lean, line 1274
--× theorem only_the_alternating_clocks_overlap_to_all_different :
--×     (the_sixteen_steps.filter fun step => (the_three_comparisons step).all fun arm => arm.1 != arm.2)
--×       = [((true, false), (true, false)), ((false, true), (false, true))] := by decide

-- Episode13.lean, line 1283
--× def the_different_on_the_tape : Area := the_frame + the_memory
--× def the_turn_on_the_tape      : Area := the_memory - the_frame

-- Episode13.lean, line 1286
--× theorem the_turn_on_the_tape_is_the_bent_card : the_turn_on_the_tape = the_coefficient := rfl
--× theorem the_different_on_the_tape_is_the_two_crossing_arms :
--×     the_different_on_the_tape = the_arm true false + the_arm false true := rfl

-- Episode13.lean, line 1292
--× theorem the_turn_is_less_than_the_different :
--×     the_turn_on_the_tape < the_different_on_the_tape ∧ the_frame * the_memory < the_memory * the_memory := by
--×   constructor
--×   · decide
--×   · rw [obviously_bigger, false_shuffle_multiplies, false_shuffle_multiplies]; decide

-- Episode13.lean, line 1300
--× theorem the_different_squared_less_the_turn_squared_is_the_gap_squared :
--×     as_many (the_different_on_the_tape * the_different_on_the_tape - the_turn_on_the_tape * the_turn_on_the_tape)
--×             (the_number_of_marks the_basis.the_reading * the_area_of_a_tape_in_blanks_is the_basis.the_reading * the_frame * the_memory)
--×       ∧ as_many (the_different_on_the_tape * the_different_on_the_tape - the_turn_on_the_tape * the_turn_on_the_tape)
--×             (the_trace_of_the_arms * the_trace_of_the_arms
--×                - the_number_of_marks the_basis.the_reading * the_area_of_a_tape_in_blanks_is the_basis.the_reading * the_determinant_of_the_arms) := by
--×   have different : compute_the_area_of the_different_on_the_tape = 23 := by decide
--×   have turn : compute_the_area_of the_turn_on_the_tape = 13 := by decide
--×   have frame : compute_the_area_of the_frame = 5 := by decide
--×   have memory : compute_the_area_of the_memory = 18 := by decide
--×   constructor
--×   · rw [as_many_is_the_same_count]
--×     simp only [the_double_lift_subtracts, false_shuffle_multiplies, different, turn, frame, memory, the_number_of_marks_the_tapes_length]
--×     rfl
--×   · rw [as_many_is_the_same_count]
--×     simp only [the_double_lift_subtracts, false_shuffle_multiplies, different, turn, the_number_of_marks_the_tapes_length,
--×       counted_the_trace_of_the_arms_is_the_trace, counted_the_determinant_of_the_arms_is_the_determinant]
--×     rfl

-- Episode13.lean, line 1322
--× def the_step_on_the_tape (from_here to_there : Area) : Account := holding to_there - holding from_here

-- Episode13.lean, line 1324
--× theorem the_two_steps_close_and_the_middle_owes_the_bent_card_twice :
--×     the_same (the_step_on_the_tape the_frame the_memory) (holding the_coefficient)
--×       ∧ the_same (the_step_on_the_tape the_memory the_frame) (- holding the_coefficient)
--×       ∧ the_same (the_step_on_the_tape the_frame the_memory + the_step_on_the_tape the_memory the_frame) nothing_held
--×       ∧ the_same (the_step_on_the_tape the_memory the_frame - the_step_on_the_tape the_frame the_memory)
--×                  (- holding twice_the_coefficient) := by decide

-- Episode13.lean, line 1345
--× theorem the_slope_steps_by_twice_the_coefficient_exactly (y h : Account) :
--×     the_same (the_slope_on_the_account (y + h) - the_slope_on_the_account y) (holding twice_the_coefficient * h) := by
--×   rw [the_same_is_the_same_balance]
--×   simp only [the_slope_on_the_account, balance_of_palm_the_middle_card, balance_of_less, balance_of_false_shuffle, balance_of_holding]
--×   simp only [Int.mul_add]; omega

-- Episode13.lean, line 1352
--× theorem twice_the_coefficient_does_not_step :
--×     the_same (holding twice_the_coefficient - holding twice_the_coefficient) nothing_held := by decide

-- Episode13.lean, line 1356
--× theorem the_tape_owes_the_last_derivative :
--×     the_same (the_step_on_the_tape the_memory the_frame - the_step_on_the_tape the_frame the_memory)
--×              (- holding twice_the_coefficient) := (the_two_steps_close_and_the_middle_owes_the_bent_card_twice).2.2.2

-- Episode13.lean, line 1362
--× theorem three_ways_to_the_gap_squared_match :
--×     as_many (the_different_on_the_tape * the_different_on_the_tape - the_turn_on_the_tape * the_turn_on_the_tape)
--×             (the_trace_of_the_arms * the_trace_of_the_arms
--×                - the_number_of_marks the_basis.the_reading * the_area_of_a_tape_in_blanks_is the_basis.the_reading * the_determinant_of_the_arms)
--×       ∧ as_many (the_trace_of_the_arms * the_trace_of_the_arms
--×                - the_number_of_marks the_basis.the_reading * the_area_of_a_tape_in_blanks_is the_basis.the_reading * the_determinant_of_the_arms)
--×             (the_trace * the_trace
--×                - the_number_of_marks the_basis.the_reading * the_area_of_a_tape_in_blanks_is the_basis.the_reading * (the_coefficient * the_memory)) := by
--×   refine ⟨the_different_squared_less_the_turn_squared_is_the_gap_squared.2, ?_⟩
--×   rw [as_many_is_the_same_count]
--×   simp only [the_double_lift_subtracts, false_shuffle_multiplies, the_number_of_marks_the_tapes_length,
--×     counted_the_trace_of_the_arms_is_the_trace, counted_the_determinant_of_the_arms_is_the_determinant,
--×     the_walk_is_the_walk.2.1, the_walk_is_the_walk.2.2.1, the_walk_is_the_walk.2.2.2.1]
--×   rfl

-- Episode13.lean, line 1380
--× def the_knowers_interpretation_of_three_areas (a b c : Area) : Account := holding a * (- (holding c * holding b))

-- Episode13.lean, line 1384
--× theorem the_inside_is_the_round_trip_and_four_of_it_is_the_gap_squared :
--×     the_same (holding the_frame * holding the_memory) (holding (the_frame * the_memory))
--×       ∧ as_many (the_number_of_marks the_basis.the_reading * the_area_of_a_tape_in_blanks_is the_basis.the_reading * the_frame * the_memory)
--×                 (the_different_on_the_tape * the_different_on_the_tape - the_turn_on_the_tape * the_turn_on_the_tape) := by
--×   refine ⟨?_, ?_⟩
--×   · rw [the_same_is_the_same_balance]
--×     simp only [balance_of_false_shuffle, balance_of_holding, false_shuffle_multiplies, Int.natCast_mul]
--×   · have forward := the_different_squared_less_the_turn_squared_is_the_gap_squared.1
--×     rw [as_many_is_the_same_count] at forward ⊢
--×     exact forward.symm

-- Episode13.lean, line 1396
--× theorem the_knowers_interpretation_of_the_tape_owes_the_frame_by_the_round_trip :
--×     the_same (the_knowers_interpretation_of_three_areas the_frame the_memory the_frame)
--×              (- holding (the_frame * (the_frame * the_memory))) := by
--×   rw [the_same_is_the_same_balance]
--×   simp only [the_knowers_interpretation_of_three_areas, balance_of_false_shuffle, balance_turned_over, balance_of_holding,
--×     false_shuffle_multiplies, Int.natCast_mul]
--×   simp only [Int.mul_neg]

-- Episode13.lean, line 1410
--× def where_it_would_go (here : Area × Area) : Area × Area :=
--×   (the_coefficient * here.1 * here.1 - the_memory * here.2 * here.2,
--×    the_number_of_marks the_basis.the_reading * the_coefficient * here.1 * here.2 - the_trace * here.2 * here.2)

-- Episode13.lean, line 1426
--× theorem simulate_stands_still_under_the_resolution (scale : Area) (here : Area × Area) :
--×     simulate_this_way scale here
--×       = if under_the_resolution scale here (where_it_would_go here) then here else where_it_would_go here := rfl

-- Episode13.lean, line 1432
--× def a_new_knot (scale : Area) (here there : Area × Area) : FACT :=
--×   { truth := ¬ under_the_resolution scale here there, click := instDecidableNot }

-- Episode13.lean, line 1436
--× theorem simulate_goes_exactly_when_the_knot_clicks (scale : Area) (here : Area × Area) :
--×     simulate_this_way scale here
--×       = @ite _ (a_new_knot scale here (where_it_would_go here)).truth (a_new_knot scale here (where_it_would_go here)).click
--×           (where_it_would_go here) here := by
--×   rw [simulate_stands_still_under_the_resolution]
--×   exact (ite_not _ _ _).symm

-- Episode13.lean, line 1446
--× def the_knot_at (scale : Area) (here : Area × Area) (so_far : Spline) : Spline :=
--×   .knot (a_new_knot scale here (where_it_would_go here)).truth the_exact_approximation so_far
--× def the_interpolant_at (scale : Area) (here : Area × Area) (before after : Spline) : Spline :=
--×   .interpolant (a_new_knot scale here (where_it_would_go here)) the_exact_approximation the_exact_approximation before after

-- Episode13.lean, line 1452
--× theorem the_observation_comes_first (scale : Area) (here : Area × Area) (before after : Spline) :
--×     Spline.le obviously (the_knot_at scale here before)
--×       ∧ Spline.le obviously (the_interpolant_at scale here before after)
--×       ∧ ¬ Spline.le (the_knot_at scale here before) obviously
--×       ∧ ¬ Spline.le (the_interpolant_at scale here before after) obviously
--×       ∧ ¬ Spline.le (the_interpolant_at scale here before after) (the_knot_at scale here before) := by
--×   simp only [the_knot_at, the_interpolant_at, obviously, Spline.le, not_false_eq_true, and_self]

-- Episode13.lean, line 1461
--× theorem the_interpolant_reads_its_fact_then_before_then_after (scale : Area) (here : Area × Area) (before after : Spline) :
--×     (the_interpolant_at scale here before after).approx
--×       = a_new_knot scale here (where_it_would_go here) :: before.approx ++ after.approx := rfl

-- Episode13.lean, line 1473
--× def no_new_knot_at_the_house : FACT :=
--×   { truth := under_the_resolution the_scale the_house (where_it_would_go the_house), click := inferInstance }

-- Episode13.lean, line 1477
--× def the_zero : Bullshit.{0,0,0,0} := .zero no_new_knot_at_the_house

-- Episode13.lean, line 1481
--× noncomputable def the_gawk_at_the_zero : Bullshit.{0,0,0,0} :=
--×   the_knower_of_the_experience.same_difference.you_the_knower.gawk_at the_zero

-- Episode13.lean, line 1484
--× theorem the_gawk_at_the_zero_is_the_first_page :
--×     ∃ (fact : FACT) (page : Number) (proof book : ThePreprint) (constant : Bullshit),
--×       the_gawk_at_the_zero = .one fact page proof book constant := ⟨_, _, _, _, _, rfl⟩

-- Episode13.lean, line 1489
--× noncomputable def the_closure_on_the_zero : Closure :=
--×   the_knower_of_the_experience.same_difference.do_you_believe_it? the_zero the_gawk_at_the_zero

-- Episode13.lean, line 1493
--× theorem the_closure_on_the_zero_is_one_cell : the_closure_on_the_zero.infer.length = 1 := rfl

-- Episode13.lean, line 1496
--× noncomputable def the_card_on_the_zero : CarrierProcess (CarrierProcess FACT) :=
--×   { symbol := the_closure_on_the_zero.infer.headD FACT.Truth, quarter := tapeNumber the_closure_on_the_zero.infer }

-- Episode13.lean, line 1501
--× theorem the_card_on_the_zero_reads_the_walk :
--×     bent_card.fenceposts_must_be_preserved Nat (read_past_quarter the_card_on_the_zero) all_possible_variables
--×       = arrange_the_information_appropriately := by
--×   rw [show read_past_quarter the_card_on_the_zero = List.length from funext (read_past_quarter_is_length _)]; rfl

-- Episode13.lean, line 1506
--× theorem the_number_out_of_the_zero :
--×     bent_card.fenceposts_must_be_preserved Nat (read_past_quarter the_card_on_the_zero) all_possible_variables = some_quartic_called arranged
--×       ∧ bent_card.fenceposts_must_be_preserved Nat (read_past_quarter the_card_on_the_zero) all_possible_variables
--×           = the_knowers_pair true
--×       ∧ (bent_card.fenceposts_must_be_preserved Nat (read_past_quarter the_card_on_the_zero) all_possible_variables).1
--×             * all_possible_variables
--×           / (bent_card.fenceposts_must_be_preserved Nat (read_past_quarter the_card_on_the_zero) all_possible_variables).2
--×           = the_constant_factor_of_scaling_bullshit := by
--×   rw [the_card_on_the_zero_reads_the_walk]
--×   exact ⟨counted_the_arrangement_is_the_arrangement.symm, (the_knowers_pair_is_the_arrangement true).symm, rfl⟩

-- Episode13.lean, line 1525
--× def the_number_a_list_indicates : List FACT → Number
--×   | []           => .zero zero
--×   | fact :: rest => .one fact (the_number_a_list_indicates rest)
--× theorem the_number_reads_back (tape : List FACT) : (the_number_a_list_indicates tape).peano.length = 1 * tape.length + 1 := by
--×   induction tape with
--×   | nil => rfl
--×   | cons fact rest ih => simp only [the_number_a_list_indicates, Number.peano, List.length_cons, ih]; omega
--× def the_count_through_the_number (tape : List FACT) : Nat := ((the_number_a_list_indicates tape).peano.length - 1) / 1
--× theorem the_count_through_the_number_is_the_length : the_count_through_the_number = List.length := by
--×   funext tape
--×   simp only [the_count_through_the_number, the_number_reads_back, Nat.add_sub_cancel]
--×   exact (by omega)

-- Episode13.lean, line 1538
--× def the_natural_a_list_indicates : List FACT → Natural
--×   | []           => .zero zero
--×   | fact :: rest => .number fact (the_number_a_list_indicates rest) (the_natural_a_list_indicates rest)
--× theorem the_natural_reads_back (tape : List FACT) : (the_natural_a_list_indicates tape).induct.length = 1 * tape.length + 1 := by
--×   induction tape with
--×   | nil => rfl
--×   | cons fact rest ih => simp only [the_natural_a_list_indicates, Natural.induct, List.length_cons, ih]; omega
--× def the_count_through_the_natural (tape : List FACT) : Nat := ((the_natural_a_list_indicates tape).induct.length - 1) / 1
--× theorem the_count_through_the_natural_is_the_length : the_count_through_the_natural = List.length := by
--×   funext tape
--×   simp only [the_count_through_the_natural, the_natural_reads_back, Nat.add_sub_cancel]
--×   exact (by omega)

-- Episode13.lean, line 1551
--× def the_rational_a_list_indicates : List FACT → Rational
--×   | []           => .zero zero
--×   | fact :: rest => .number fact (the_natural_a_list_indicates rest) (the_rational_a_list_indicates rest)
--× theorem the_rational_reads_back (tape : List FACT) : (the_rational_a_list_indicates tape).diagonalize.length = 1 * tape.length + 1 := by
--×   induction tape with
--×   | nil => rfl
--×   | cons fact rest ih => simp only [the_rational_a_list_indicates, Rational.diagonalize, List.length_cons, ih]; omega
--× def the_count_through_the_rational (tape : List FACT) : Nat := ((the_rational_a_list_indicates tape).diagonalize.length - 1) / 1
--× theorem the_count_through_the_rational_is_the_length : the_count_through_the_rational = List.length := by
--×   funext tape
--×   simp only [the_count_through_the_rational, the_rational_reads_back, Nat.add_sub_cancel]
--×   exact (by omega)

-- Episode13.lean, line 1564
--× def the_sequence_a_list_indicates : List FACT → Sequence
--×   | []           => .nil zero
--×   | fact :: rest => .index fact (the_rational_a_list_indicates rest) (the_sequence_a_list_indicates rest)
--× theorem the_sequence_reads_back (tape : List FACT) : (the_sequence_a_list_indicates tape).enumerate.length = 1 * tape.length + 1 := by
--×   induction tape with
--×   | nil => rfl
--×   | cons fact rest ih => simp only [the_sequence_a_list_indicates, Sequence.enumerate, List.length_cons, ih]; omega
--× def the_count_through_the_sequence (tape : List FACT) : Nat := ((the_sequence_a_list_indicates tape).enumerate.length - 1) / 1
--× theorem the_count_through_the_sequence_is_the_length : the_count_through_the_sequence = List.length := by
--×   funext tape
--×   simp only [the_count_through_the_sequence, the_sequence_reads_back, Nat.add_sub_cancel]
--×   exact (by omega)

-- Episode13.lean, line 1577
--× def the_limit_a_list_indicates : List FACT → Limit
--×   | []           => .nil zero
--×   | fact :: rest => .index fact (the_sequence_a_list_indicates rest) (the_limit_a_list_indicates rest)
--× theorem the_limit_reads_back (tape : List FACT) : (the_limit_a_list_indicates tape).converge.length = 1 * tape.length + 1 := by
--×   induction tape with
--×   | nil => rfl
--×   | cons fact rest ih => simp only [the_limit_a_list_indicates, Limit.converge, List.length_cons, ih]; omega
--× def the_count_through_the_limit (tape : List FACT) : Nat := ((the_limit_a_list_indicates tape).converge.length - 1) / 1
--× theorem the_count_through_the_limit_is_the_length : the_count_through_the_limit = List.length := by
--×   funext tape
--×   simp only [the_count_through_the_limit, the_limit_reads_back, Nat.add_sub_cancel]
--×   exact (by omega)

-- Episode13.lean, line 1590
--× def the_sample_a_list_indicates : List FACT → Sample
--×   | []           => .initial_condition zero (the_limit_a_list_indicates [])
--×   | fact :: rest => .signal_response fact (the_limit_a_list_indicates rest) fact (the_limit_a_list_indicates rest) (the_sample_a_list_indicates rest)
--× theorem the_sample_reads_back (tape : List FACT) : (the_sample_a_list_indicates tape).taste.length = 2 * tape.length + 1 := by
--×   induction tape with
--×   | nil => rfl
--×   | cons fact rest ih => simp only [the_sample_a_list_indicates, Sample.taste, List.length_cons, ih]; omega
--× def the_count_through_the_sample (tape : List FACT) : Nat := ((the_sample_a_list_indicates tape).taste.length - 1) / 2
--× theorem the_count_through_the_sample_is_the_length : the_count_through_the_sample = List.length := by
--×   funext tape
--×   simp only [the_count_through_the_sample, the_sample_reads_back, Nat.add_sub_cancel]
--×   exact Nat.mul_div_cancel_left _ (by decide)

-- Episode13.lean, line 1603
--× def the_trial_a_list_indicates : List FACT → Trial
--×   | []           => .hypothesis zero (the_sample_a_list_indicates [])
--×   | fact :: rest => .signal_response fact (the_sample_a_list_indicates rest) fact (the_sample_a_list_indicates rest) (the_trial_a_list_indicates rest)
--× theorem the_trial_reads_back (tape : List FACT) : (the_trial_a_list_indicates tape).experiment.length = 2 * tape.length + 1 := by
--×   induction tape with
--×   | nil => rfl
--×   | cons fact rest ih => simp only [the_trial_a_list_indicates, Trial.experiment, List.length_cons, ih]; omega
--× def the_count_through_the_trial (tape : List FACT) : Nat := ((the_trial_a_list_indicates tape).experiment.length - 1) / 2
--× theorem the_count_through_the_trial_is_the_length : the_count_through_the_trial = List.length := by
--×   funext tape
--×   simp only [the_count_through_the_trial, the_trial_reads_back, Nat.add_sub_cancel]
--×   exact Nat.mul_div_cancel_left _ (by decide)

-- Episode13.lean, line 1616
--× def the_study_a_list_indicates : List FACT → Study
--×   | []           => .hypothesis zero
--×   | fact :: rest => .book_of_records fact (the_trial_a_list_indicates rest) (the_study_a_list_indicates rest)
--× theorem the_study_reads_back (tape : List FACT) : (the_study_a_list_indicates tape).phenomenon.length = 1 * tape.length + 1 := by
--×   induction tape with
--×   | nil => rfl
--×   | cons fact rest ih => simp only [the_study_a_list_indicates, Study.phenomenon, List.length_cons, ih]; omega
--× def the_count_through_the_study (tape : List FACT) : Nat := ((the_study_a_list_indicates tape).phenomenon.length - 1) / 1
--× theorem the_count_through_the_study_is_the_length : the_count_through_the_study = List.length := by
--×   funext tape
--×   simp only [the_count_through_the_study, the_study_reads_back, Nat.add_sub_cancel]
--×   exact (by omega)

-- Episode13.lean, line 1629
--× def the_computation_a_list_indicates : List FACT → Computation
--×   | []           => .program zero (the_study_a_list_indicates [])
--×   | fact :: rest => .compute fact (the_study_a_list_indicates rest) (the_study_a_list_indicates rest) (the_computation_a_list_indicates rest)
--× theorem the_computation_reads_back (tape : List FACT) : (the_computation_a_list_indicates tape).elaborate.length = 1 * tape.length + 1 := by
--×   induction tape with
--×   | nil => rfl
--×   | cons fact rest ih => simp only [the_computation_a_list_indicates, Computation.elaborate, List.length_cons, ih]; omega
--× def the_count_through_the_computation (tape : List FACT) : Nat := ((the_computation_a_list_indicates tape).elaborate.length - 1) / 1
--× theorem the_count_through_the_computation_is_the_length : the_count_through_the_computation = List.length := by
--×   funext tape
--×   simp only [the_count_through_the_computation, the_computation_reads_back, Nat.add_sub_cancel]
--×   exact (by omega)

-- Episode13.lean, line 1642
--× def the_chaitin_a_list_indicates : List FACT → ChaitinsNumberSequence
--×   | []           => .halting zero (the_computation_a_list_indicates [])
--×   | fact :: rest => .nonhalting fact (the_computation_a_list_indicates rest) (some (the_chaitin_a_list_indicates rest))
--× theorem the_chaitin_reads_back (tape : List FACT) : (the_chaitin_a_list_indicates tape).unknown.length = 1 * tape.length + 1 := by
--×   induction tape with
--×   | nil => rfl
--×   | cons fact rest ih => simp only [the_chaitin_a_list_indicates, ChaitinsNumberSequence.unknown, List.length_cons, ih]; omega
--× def the_count_through_the_chaitin (tape : List FACT) : Nat := ((the_chaitin_a_list_indicates tape).unknown.length - 1) / 1
--× theorem the_count_through_the_chaitin_is_the_length : the_count_through_the_chaitin = List.length := by
--×   funext tape
--×   simp only [the_count_through_the_chaitin, the_chaitin_reads_back, Nat.add_sub_cancel]
--×   exact (by omega)

-- Episode13.lean, line 1655
--× def the_metavariable_a_list_indicates : List FACT → Metavariable Closure.{0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0}
--×   | []           => .base zero the_only_logical_inconsistency
--×   | fact :: rest => .step fact (the_metavariable_a_list_indicates rest)
--× theorem the_metavariable_reads_back (tape : List FACT) : (the_metavariable_a_list_indicates tape).closure.length = 1 * tape.length + 1 := by
--×   induction tape with
--×   | nil => rfl
--×   | cons fact rest ih => simp only [the_metavariable_a_list_indicates, Metavariable.closure, List.length_cons, ih]; omega
--× def the_count_through_the_metavariable (tape : List FACT) : Nat := ((the_metavariable_a_list_indicates tape).closure.length - 1) / 1
--× theorem the_count_through_the_metavariable_is_the_length : the_count_through_the_metavariable = List.length := by
--×   funext tape
--×   simp only [the_count_through_the_metavariable, the_metavariable_reads_back, Nat.add_sub_cancel]
--×   exact (by omega)

-- Episode13.lean, line 1668
--× def the_sophism_a_list_indicates : List FACT → Sophism
--×   | []           => .origin zero (the_chaitin_a_list_indicates []) Prop
--×   | fact :: rest => .dimension fact (the_chaitin_a_list_indicates rest) Prop (the_sophism_a_list_indicates rest)
--× theorem the_sophism_reads_back (tape : List FACT) : (the_sophism_a_list_indicates tape).taylor_expansion.length = 1 * tape.length + 1 := by
--×   induction tape with
--×   | nil => rfl
--×   | cons fact rest ih => simp only [the_sophism_a_list_indicates, Sophism.taylor_expansion, List.length_cons, ih]; omega
--× def the_count_through_the_sophism (tape : List FACT) : Nat := ((the_sophism_a_list_indicates tape).taylor_expansion.length - 1) / 1
--× theorem the_count_through_the_sophism_is_the_length : the_count_through_the_sophism = List.length := by
--×   funext tape
--×   simp only [the_count_through_the_sophism, the_sophism_reads_back, Nat.add_sub_cancel]
--×   exact (by omega)

-- Episode13.lean, line 1681
--× def the_area_a_list_indicates : List FACT → Area
--×   | []           => .tree zero
--×   | fact :: rest => .dt fact (the_number_a_list_indicates rest) (the_area_a_list_indicates rest)
--× theorem the_area_reads_back (tape : List FACT) : (the_area_a_list_indicates tape).riemann_integrate.length = 1 * tape.length + 1 := by
--×   induction tape with
--×   | nil => rfl
--×   | cons fact rest ih => simp only [the_area_a_list_indicates, Area.riemann_integrate, List.length_cons, ih]; omega
--× def the_count_through_the_area (tape : List FACT) : Nat := ((the_area_a_list_indicates tape).riemann_integrate.length - 1) / 1
--× theorem the_count_through_the_area_is_the_length : the_count_through_the_area = List.length := by
--×   funext tape
--×   simp only [the_count_through_the_area, the_area_reads_back, Nat.add_sub_cancel]
--×   exact (by omega)

-- Episode13.lean, line 1694
--× def the_pigeonhole_a_list_indicates : List FACT → PigeonHole
--×   | []           => .this_superpigeon zero (the_area_a_list_indicates [])
--×   | fact :: rest => .a_pigeon fact (the_area_a_list_indicates rest) (the_pigeonhole_a_list_indicates rest)
--× theorem the_pigeonhole_reads_back (tape : List FACT) : (the_pigeonhole_a_list_indicates tape).solve.length = 1 * tape.length + 1 := by
--×   induction tape with
--×   | nil => rfl
--×   | cons fact rest ih => simp only [the_pigeonhole_a_list_indicates, PigeonHole.solve, List.length_cons, ih]; omega
--× def the_count_through_the_pigeonhole (tape : List FACT) : Nat := ((the_pigeonhole_a_list_indicates tape).solve.length - 1) / 1
--× theorem the_count_through_the_pigeonhole_is_the_length : the_count_through_the_pigeonhole = List.length := by
--×   funext tape
--×   simp only [the_count_through_the_pigeonhole, the_pigeonhole_reads_back, Nat.add_sub_cancel]
--×   exact (by omega)

-- Episode13.lean, line 1707
--× def the_jar_a_list_indicates : List FACT → Jar
--×   | []           => .color zero (the_area_a_list_indicates [])
--×   | fact :: rest => .bang fact (the_jar_a_list_indicates rest)
--× theorem the_jar_reads_back (tape : List FACT) : (the_jar_a_list_indicates tape).classify.length = 1 * tape.length + 1 := by
--×   induction tape with
--×   | nil => rfl
--×   | cons fact rest ih => simp only [the_jar_a_list_indicates, Jar.classify, List.length_cons, ih]; omega
--× def the_count_through_the_jar (tape : List FACT) : Nat := ((the_jar_a_list_indicates tape).classify.length - 1) / 1
--× theorem the_count_through_the_jar_is_the_length : the_count_through_the_jar = List.length := by
--×   funext tape
--×   simp only [the_count_through_the_jar, the_jar_reads_back, Nat.add_sub_cancel]
--×   exact (by omega)

-- Episode13.lean, line 1720
--× def the_equivalation_a_list_indicates : List FACT → Equivalation
--×   | []           => .physics zero (the_jar_a_list_indicates [])
--×   | fact :: rest => .zero_like fact (the_equivalation_a_list_indicates rest)
--× theorem the_equivalation_reads_back (tape : List FACT) : (the_equivalation_a_list_indicates tape).vanish.length = 1 * tape.length + 1 := by
--×   induction tape with
--×   | nil => rfl
--×   | cons fact rest ih => simp only [the_equivalation_a_list_indicates, Equivalation.vanish, List.length_cons, ih]; omega
--× def the_count_through_the_equivalation (tape : List FACT) : Nat := ((the_equivalation_a_list_indicates tape).vanish.length - 1) / 1
--× theorem the_count_through_the_equivalation_is_the_length : the_count_through_the_equivalation = List.length := by
--×   funext tape
--×   simp only [the_count_through_the_equivalation, the_equivalation_reads_back, Nat.add_sub_cancel]
--×   exact (by omega)

-- Episode13.lean, line 1733
--× def the_encoding_a_list_indicates : List FACT → Encoding
--×   | []           => .boot zero (the_equivalation_a_list_indicates [])
--×   | fact :: rest => .zero fact (the_equivalation_a_list_indicates rest) (the_encoding_a_list_indicates rest)
--× theorem the_encoding_reads_back (tape : List FACT) : (the_encoding_a_list_indicates tape).decode.length = 1 * tape.length + 1 := by
--×   induction tape with
--×   | nil => rfl
--×   | cons fact rest ih => simp only [the_encoding_a_list_indicates, Encoding.decode, List.length_cons, ih]; omega
--× def the_count_through_the_encoding (tape : List FACT) : Nat := ((the_encoding_a_list_indicates tape).decode.length - 1) / 1
--× theorem the_count_through_the_encoding_is_the_length : the_count_through_the_encoding = List.length := by
--×   funext tape
--×   simp only [the_count_through_the_encoding, the_encoding_reads_back, Nat.add_sub_cancel]
--×   exact (by omega)

-- Episode13.lean, line 1746
--× def the_abstraction_a_list_indicates : List FACT → Abstraction
--×   | []           => .satire_about zero
--×   | fact :: rest => .compile fact (the_encoding_a_list_indicates rest) (the_abstraction_a_list_indicates rest)
--× theorem the_abstraction_reads_back (tape : List FACT) : (the_abstraction_a_list_indicates tape).equivalation.length = 1 * tape.length + 1 := by
--×   induction tape with
--×   | nil => rfl
--×   | cons fact rest ih => simp only [the_abstraction_a_list_indicates, Abstraction.equivalation, List.length_cons, ih]; omega
--× def the_count_through_the_abstraction (tape : List FACT) : Nat := ((the_abstraction_a_list_indicates tape).equivalation.length - 1) / 1
--× theorem the_count_through_the_abstraction_is_the_length : the_count_through_the_abstraction = List.length := by
--×   funext tape
--×   simp only [the_count_through_the_abstraction, the_abstraction_reads_back, Nat.add_sub_cancel]
--×   exact (by omega)

-- Episode13.lean, line 1759
--× def the_sum_a_list_indicates : List FACT → Sum
--×   | []           => .zero True (the_area_a_list_indicates [])
--×   | fact :: rest => .add fact (the_area_a_list_indicates rest) (the_area_a_list_indicates rest) (the_sum_a_list_indicates rest)
--× theorem the_sum_reads_back (tape : List FACT) : (the_sum_a_list_indicates tape).euclid.length = 1 * tape.length + 1 := by
--×   induction tape with
--×   | nil => rfl
--×   | cons fact rest ih => simp only [the_sum_a_list_indicates, Sum.euclid, List.length_cons, ih]; omega
--× def the_count_through_the_sum (tape : List FACT) : Nat := ((the_sum_a_list_indicates tape).euclid.length - 1) / 1
--× theorem the_count_through_the_sum_is_the_length : the_count_through_the_sum = List.length := by
--×   funext tape
--×   simp only [the_count_through_the_sum, the_sum_reads_back, Nat.add_sub_cancel]
--×   exact (by omega)

-- Episode13.lean, line 1772
--× def the_product_a_list_indicates : List FACT → Product
--×   | []           => .origin zero
--×   | fact :: rest => .mul fact (the_sum_a_list_indicates rest) (the_sum_a_list_indicates rest) (the_product_a_list_indicates rest)
--× theorem the_product_reads_back (tape : List FACT) : (the_product_a_list_indicates tape).projector.length = 1 * tape.length + 1 := by
--×   induction tape with
--×   | nil => rfl
--×   | cons fact rest ih => simp only [the_product_a_list_indicates, Product.projector, List.length_cons, ih]; omega
--× def the_count_through_the_product (tape : List FACT) : Nat := ((the_product_a_list_indicates tape).projector.length - 1) / 1
--× theorem the_count_through_the_product_is_the_length : the_count_through_the_product = List.length := by
--×   funext tape
--×   simp only [the_count_through_the_product, the_product_reads_back, Nat.add_sub_cancel]
--×   exact (by omega)

-- Episode13.lean, line 1785
--× def the_basis_a_list_indicates : List FACT → Basis
--×   | []           => .null_space zero
--×   | fact :: rest => .basis fact (the_product_a_list_indicates rest) (the_product_a_list_indicates rest) (the_basis_a_list_indicates rest)
--× theorem the_basis_reads_back (tape : List FACT) : (the_basis_a_list_indicates tape).householder.length = 1 * tape.length + 1 := by
--×   induction tape with
--×   | nil => rfl
--×   | cons fact rest ih => simp only [the_basis_a_list_indicates, Basis.householder, List.length_cons, ih]; omega
--× def the_count_through_the_basis (tape : List FACT) : Nat := ((the_basis_a_list_indicates tape).householder.length - 1) / 1
--× theorem the_count_through_the_basis_is_the_length : the_count_through_the_basis = List.length := by
--×   funext tape
--×   simp only [the_count_through_the_basis, the_basis_reads_back, Nat.add_sub_cancel]
--×   exact (by omega)

-- Episode13.lean, line 1798
--× def the_polynomial_a_list_indicates : List FACT → Polynomial
--×   | []           => .constant zero
--×   | fact :: rest => .factor fact (the_basis_a_list_indicates rest) (the_basis_a_list_indicates rest) (the_polynomial_a_list_indicates rest)
--× theorem the_polynomial_reads_back (tape : List FACT) : (the_polynomial_a_list_indicates tape).terms.length = 1 * tape.length + 1 := by
--×   induction tape with
--×   | nil => rfl
--×   | cons fact rest ih => simp only [the_polynomial_a_list_indicates, Polynomial.terms, List.length_cons, ih]; omega
--× def the_count_through_the_polynomial (tape : List FACT) : Nat := ((the_polynomial_a_list_indicates tape).terms.length - 1) / 1
--× theorem the_count_through_the_polynomial_is_the_length : the_count_through_the_polynomial = List.length := by
--×   funext tape
--×   simp only [the_count_through_the_polynomial, the_polynomial_reads_back, Nat.add_sub_cancel]
--×   exact (by omega)

-- Episode13.lean, line 1811
--× def the_spline_a_list_indicates : List FACT → Spline
--×   | []           => .observation True
--×   | fact :: rest => .knot fact.truth (the_polynomial_a_list_indicates rest) (the_spline_a_list_indicates rest)
--× theorem the_spline_reads_back (tape : List FACT) : (the_spline_a_list_indicates tape).approx.length = 1 * tape.length + 1 := by
--×   induction tape with
--×   | nil => rfl
--×   | cons fact rest ih => simp only [the_spline_a_list_indicates, Spline.approx, List.length_cons, ih]; omega
--× def the_count_through_the_spline (tape : List FACT) : Nat := ((the_spline_a_list_indicates tape).approx.length - 1) / 1
--× theorem the_count_through_the_spline_is_the_length : the_count_through_the_spline = List.length := by
--×   funext tape
--×   simp only [the_count_through_the_spline, the_spline_reads_back, Nat.add_sub_cancel]
--×   exact (by omega)

-- Episode13.lean, line 1824
--× def the_diatribe_a_list_indicates : List FACT → Diatribe
--×   | []           => .religion True
--×   | fact :: rest => .speculation fact.truth (the_spline_a_list_indicates rest) (the_diatribe_a_list_indicates rest)
--× theorem the_diatribe_reads_back (tape : List FACT) : (the_diatribe_a_list_indicates tape).buckets.length = 1 * tape.length + 1 := by
--×   induction tape with
--×   | nil => rfl
--×   | cons fact rest ih => simp only [the_diatribe_a_list_indicates, Diatribe.buckets, List.length_cons, ih]; omega
--× def the_count_through_the_diatribe (tape : List FACT) : Nat := ((the_diatribe_a_list_indicates tape).buckets.length - 1) / 1
--× theorem the_count_through_the_diatribe_is_the_length : the_count_through_the_diatribe = List.length := by
--×   funext tape
--×   simp only [the_count_through_the_diatribe, the_diatribe_reads_back, Nat.add_sub_cancel]
--×   exact (by omega)

-- Episode13.lean, line 1837
--× def the_cult_a_list_indicates : List FACT → Cult
--×   | []           => .inside_joke True
--×   | fact :: rest => .pythagoras fact.truth (the_diatribe_a_list_indicates rest) (the_cult_a_list_indicates rest)
--× theorem the_cult_reads_back (tape : List FACT) : (the_cult_a_list_indicates tape).name.length = 1 * tape.length + 1 := by
--×   induction tape with
--×   | nil => rfl
--×   | cons fact rest ih => simp only [the_cult_a_list_indicates, Cult.name, List.length_cons, ih]; omega
--× def the_count_through_the_cult (tape : List FACT) : Nat := ((the_cult_a_list_indicates tape).name.length - 1) / 1
--× theorem the_count_through_the_cult_is_the_length : the_count_through_the_cult = List.length := by
--×   funext tape
--×   simp only [the_count_through_the_cult, the_cult_reads_back, Nat.add_sub_cancel]
--×   exact (by omega)

-- Episode13.lean, line 1850
--× def the_science_a_list_indicates : List FACT → Science
--×   | []           => .repeatable True
--×   | fact :: rest => .theory fact.truth (the_cult_a_list_indicates rest) fact (the_science_a_list_indicates rest)
--× theorem the_science_reads_back (tape : List FACT) : (the_science_a_list_indicates tape).method.length = 1 * tape.length + 1 := by
--×   induction tape with
--×   | nil => rfl
--×   | cons fact rest ih => simp only [the_science_a_list_indicates, Science.method, List.length_cons, ih]; omega
--× def the_count_through_the_science (tape : List FACT) : Nat := ((the_science_a_list_indicates tape).method.length - 1) / 1
--× theorem the_count_through_the_science_is_the_length : the_count_through_the_science = List.length := by
--×   funext tape
--×   simp only [the_count_through_the_science, the_science_reads_back, Nat.add_sub_cancel]
--×   exact (by omega)

-- Episode13.lean, line 1863
--× def the_knowledge_a_list_indicates : List FACT → Knowledge
--×   | []           => .jarjar True
--×   | fact :: rest => .ledger fact.truth fact (the_knowledge_a_list_indicates rest)
--× theorem the_knowledge_reads_back (tape : List FACT) : (the_knowledge_a_list_indicates tape).audit.length = 1 * tape.length + 1 := by
--×   induction tape with
--×   | nil => rfl
--×   | cons fact rest ih => simp only [the_knowledge_a_list_indicates, Knowledge.audit, List.length_cons, ih]; omega
--× def the_count_through_the_knowledge (tape : List FACT) : Nat := ((the_knowledge_a_list_indicates tape).audit.length - 1) / 1
--× theorem the_count_through_the_knowledge_is_the_length : the_count_through_the_knowledge = List.length := by
--×   funext tape
--×   simp only [the_count_through_the_knowledge, the_knowledge_reads_back, Nat.add_sub_cancel]
--×   exact (by omega)

-- Episode13.lean, line 1876
--× def the_gospel_a_list_indicates : List FACT → Gospel
--×   | []           => .the_proof True
--×   | fact :: rest => .we_understand_that (the_knowledge_a_list_indicates rest) fact.truth (the_gospel_a_list_indicates rest)
--× theorem the_gospel_reads_back (tape : List FACT) : (the_gospel_a_list_indicates tape).witness.length = 1 * tape.length + 1 := by
--×   induction tape with
--×   | nil => rfl
--×   | cons fact rest ih => simp only [the_gospel_a_list_indicates, Gospel.witness, List.length_cons, ih]; omega
--× def the_count_through_the_gospel (tape : List FACT) : Nat := ((the_gospel_a_list_indicates tape).witness.length - 1) / 1
--× theorem the_count_through_the_gospel_is_the_length : the_count_through_the_gospel = List.length := by
--×   funext tape
--×   simp only [the_count_through_the_gospel, the_gospel_reads_back, Nat.add_sub_cancel]
--×   exact (by omega)

-- Episode13.lean, line 1889
--× def the_truth_a_list_indicates : List FACT → Truth
--×   | []           => .logically True
--×   | fact :: rest => .but (the_gospel_a_list_indicates rest) fact.truth (the_truth_a_list_indicates rest)
--× theorem the_truth_reads_back (tape : List FACT) : (the_truth_a_list_indicates tape).testify.length = 1 * tape.length + 1 := by
--×   induction tape with
--×   | nil => rfl
--×   | cons fact rest ih => simp only [the_truth_a_list_indicates, Truth.testify, List.length_cons, ih]; omega
--× def the_count_through_the_truth (tape : List FACT) : Nat := ((the_truth_a_list_indicates tape).testify.length - 1) / 1
--× theorem the_count_through_the_truth_is_the_length : the_count_through_the_truth = List.length := by
--×   funext tape
--×   simp only [the_count_through_the_truth, the_truth_reads_back, Nat.add_sub_cancel]
--×   exact (by omega)

-- Episode13.lean, line 1902
--× def the_variation_a_list_indicates : List FACT → Variation
--×   | []           => .the_newton (the_gospel_a_list_indicates []) True
--×   | fact :: rest => .the_gateaux (the_gospel_a_list_indicates rest) fact.truth fact.truth (the_variation_a_list_indicates rest)
--× theorem the_variation_reads_back (tape : List FACT) : (the_variation_a_list_indicates tape).krylov.length = 1 * tape.length + 1 := by
--×   induction tape with
--×   | nil => rfl
--×   | cons fact rest ih => simp only [the_variation_a_list_indicates, Variation.krylov, List.length_cons, ih]; omega
--× def the_count_through_the_variation (tape : List FACT) : Nat := ((the_variation_a_list_indicates tape).krylov.length - 1) / 1
--× theorem the_count_through_the_variation_is_the_length : the_count_through_the_variation = List.length := by
--×   funext tape
--×   simp only [the_count_through_the_variation, the_variation_reads_back, Nat.add_sub_cancel]
--×   exact (by omega)

-- Episode13.lean, line 1915
--× def the_spacetimepath_a_list_indicates : List FACT → SpaceTimePath.{0}
--×   | []           => .einstein zero
--×   | fact :: rest => .whitehole fact Prop (the_spacetimepath_a_list_indicates rest)
--× theorem the_spacetimepath_reads_back (tape : List FACT) : (the_spacetimepath_a_list_indicates tape).stokes.length = 1 * tape.length + 1 := by
--×   induction tape with
--×   | nil => rfl
--×   | cons fact rest ih => simp only [the_spacetimepath_a_list_indicates, SpaceTimePath.stokes, List.length_cons, ih]; omega
--× def the_count_through_the_spacetimepath (tape : List FACT) : Nat := ((the_spacetimepath_a_list_indicates tape).stokes.length - 1) / 1
--× theorem the_count_through_the_spacetimepath_is_the_length : the_count_through_the_spacetimepath = List.length := by
--×   funext tape
--×   simp only [the_count_through_the_spacetimepath, the_spacetimepath_reads_back, Nat.add_sub_cancel]
--×   exact (by omega)

-- Episode13.lean, line 1928
--× def the_yarn_a_list_indicates : List FACT → YarnTheory.{0,0,0,0,0,0}
--×   | []           => .stokes zero (the_spacetimepath_a_list_indicates []) True
--×   | fact :: rest => .fibers fact (the_spacetimepath_a_list_indicates rest) (the_spacetimepath_a_list_indicates rest) fact.truth fact.truth (the_yarn_a_list_indicates rest)
--× theorem the_yarn_reads_back (tape : List FACT) : (the_yarn_a_list_indicates tape).gauss.length = 1 * tape.length + 1 := by
--×   induction tape with
--×   | nil => rfl
--×   | cons fact rest ih => simp only [the_yarn_a_list_indicates, YarnTheory.gauss, List.length_cons, ih]; omega
--× def the_count_through_the_yarn (tape : List FACT) : Nat := ((the_yarn_a_list_indicates tape).gauss.length - 1) / 1
--× theorem the_count_through_the_yarn_is_the_length : the_count_through_the_yarn = List.length := by
--×   funext tape
--×   simp only [the_count_through_the_yarn, the_yarn_reads_back, Nat.add_sub_cancel]
--×   exact (by omega)

-- Episode13.lean, line 1941
--× def the_measurement_a_list_indicates : List FACT → Measurement.{0}
--×   | []           => .origin zero (the_number_a_list_indicates []) Prop
--×   | fact :: rest => .distance_to fact (the_number_a_list_indicates rest) (the_number_a_list_indicates rest) Prop Type (the_measurement_a_list_indicates rest)
--× theorem the_measurement_reads_back (tape : List FACT) : (the_measurement_a_list_indicates tape).the_reading.length = 1 * tape.length + 0 := by
--×   induction tape with
--×   | nil => rfl
--×   | cons fact rest ih => simp only [the_measurement_a_list_indicates, Measurement.the_reading, List.length_cons, ih]; omega
--× def the_count_through_the_measurement (tape : List FACT) : Nat := ((the_measurement_a_list_indicates tape).the_reading.length - 0) / 1
--× theorem the_count_through_the_measurement_is_the_length : the_count_through_the_measurement = List.length := by
--×   funext tape
--×   simp only [the_count_through_the_measurement, the_measurement_reads_back, Nat.add_sub_cancel]
--×   exact (by omega)

-- Episode13.lean, line 1954
--× def the_preprint_a_list_indicates : List FACT → ThePreprint.{0}
--×   | []           => .introduction zero Prop
--×   | fact :: rest => .methodology fact fact Prop Type (the_preprint_a_list_indicates rest)
--× theorem the_preprint_reads_back (tape : List FACT) : (the_preprint_a_list_indicates tape).the_model.length = 1 * tape.length + 1 := by
--×   induction tape with
--×   | nil => rfl
--×   | cons fact rest ih => simp only [the_preprint_a_list_indicates, ThePreprint.the_model, List.length_cons, ih]; omega
--× def the_count_through_the_preprint (tape : List FACT) : Nat := ((the_preprint_a_list_indicates tape).the_model.length - 1) / 1
--× theorem the_count_through_the_preprint_is_the_length : the_count_through_the_preprint = List.length := by
--×   funext tape
--×   simp only [the_count_through_the_preprint, the_preprint_reads_back, Nat.add_sub_cancel]
--×   exact (by omega)

-- Episode13.lean, line 1967
--× def the_bullshit_a_list_indicates : List FACT → Bullshit.{0,0,0,0}
--×   | []           => .zero zero
--×   | fact :: rest => .one fact (the_number_a_list_indicates rest) (the_preprint_a_list_indicates rest) (the_preprint_a_list_indicates rest) (the_bullshit_a_list_indicates rest)
--× theorem the_bullshit_reads_back (tape : List FACT) : (the_bullshit_a_list_indicates tape).meter.length = 1 * tape.length + 1 := by
--×   induction tape with
--×   | nil => rfl
--×   | cons fact rest ih => simp only [the_bullshit_a_list_indicates, Bullshit.meter, List.length_cons, ih]; omega
--× def the_count_through_the_bullshit (tape : List FACT) : Nat := ((the_bullshit_a_list_indicates tape).meter.length - 1) / 1
--× theorem the_count_through_the_bullshit_is_the_length : the_count_through_the_bullshit = List.length := by
--×   funext tape
--×   simp only [the_count_through_the_bullshit, the_bullshit_reads_back, Nat.add_sub_cancel]
--×   exact (by omega)

-- Episode13.lean, line 1980
--× def the_closure_a_list_indicates : List FACT → Closure.{0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0}
--×   | []           => .same zero (the_bullshit_a_list_indicates [])
--×   | fact :: rest => .inferred fact fact (the_bullshit_a_list_indicates rest) (the_bullshit_a_list_indicates rest) (some fact.truth) (the_closure_a_list_indicates rest)
--× theorem the_closure_reads_back (tape : List FACT) : (the_closure_a_list_indicates tape).infer.length = 2 * tape.length + 1 := by
--×   induction tape with
--×   | nil => rfl
--×   | cons fact rest ih => simp only [the_closure_a_list_indicates, Closure.infer, List.length_cons, ih]; omega
--× def the_count_through_the_closure (tape : List FACT) : Nat := ((the_closure_a_list_indicates tape).infer.length - 1) / 2
--× theorem the_count_through_the_closure_is_the_length : the_count_through_the_closure = List.length := by
--×   funext tape
--×   simp only [the_count_through_the_closure, the_closure_reads_back, Nat.add_sub_cancel]
--×   exact Nat.mul_div_cancel_left _ (by decide)

-- Episode13.lean, line 1994
--× def the_counts_through_all_the_inductives : List (List FACT → Nat) :=
--×   [the_count_through_the_number,
--×    the_count_through_the_natural,
--×    the_count_through_the_rational,
--×    the_count_through_the_sequence,
--×    the_count_through_the_limit,
--×    the_count_through_the_sample,
--×    the_count_through_the_trial,
--×    the_count_through_the_study,
--×    the_count_through_the_computation,
--×    the_count_through_the_chaitin,
--×    the_count_through_the_metavariable,
--×    the_count_through_the_sophism,
--×    the_count_through_the_area,
--×    the_count_through_the_pigeonhole,
--×    the_count_through_the_jar,
--×    the_count_through_the_equivalation,
--×    the_count_through_the_encoding,
--×    the_count_through_the_abstraction,
--×    the_count_through_the_sum,
--×    the_count_through_the_product,
--×    the_count_through_the_basis,
--×    the_count_through_the_polynomial,
--×    the_count_through_the_spline,
--×    the_count_through_the_diatribe,
--×    the_count_through_the_cult,
--×    the_count_through_the_science,
--×    the_count_through_the_knowledge,
--×    the_count_through_the_gospel,
--×    the_count_through_the_truth,
--×    the_count_through_the_variation,
--×    the_count_through_the_spacetimepath,
--×    the_count_through_the_yarn,
--×    the_count_through_the_measurement,
--×    the_count_through_the_preprint,
--×    the_count_through_the_bullshit,
--×    the_count_through_the_closure]

-- Episode13.lean, line 2032
--× theorem there_is_a_count_for_every_inductive :
--×     the_counts_through_all_the_inductives.length = the_inductives_of_the_five_episodes.length := by decide

-- Episode13.lean, line 2036
--× theorem every_count_is_the_length :
--×     the_counts_through_all_the_inductives = List.replicate the_counts_through_all_the_inductives.length List.length := by
--×   simp only [the_counts_through_all_the_inductives, the_count_through_the_number_is_the_length, the_count_through_the_natural_is_the_length, the_count_through_the_rational_is_the_length, the_count_through_the_sequence_is_the_length, the_count_through_the_limit_is_the_length, the_count_through_the_sample_is_the_length, the_count_through_the_trial_is_the_length, the_count_through_the_study_is_the_length, the_count_through_the_computation_is_the_length, the_count_through_the_chaitin_is_the_length, the_count_through_the_metavariable_is_the_length, the_count_through_the_sophism_is_the_length, the_count_through_the_area_is_the_length, the_count_through_the_pigeonhole_is_the_length, the_count_through_the_jar_is_the_length, the_count_through_the_equivalation_is_the_length, the_count_through_the_encoding_is_the_length, the_count_through_the_abstraction_is_the_length, the_count_through_the_sum_is_the_length, the_count_through_the_product_is_the_length, the_count_through_the_basis_is_the_length, the_count_through_the_polynomial_is_the_length, the_count_through_the_spline_is_the_length, the_count_through_the_diatribe_is_the_length, the_count_through_the_cult_is_the_length, the_count_through_the_science_is_the_length, the_count_through_the_knowledge_is_the_length, the_count_through_the_gospel_is_the_length, the_count_through_the_truth_is_the_length, the_count_through_the_variation_is_the_length, the_count_through_the_spacetimepath_is_the_length, the_count_through_the_yarn_is_the_length, the_count_through_the_measurement_is_the_length, the_count_through_the_preprint_is_the_length, the_count_through_the_bullshit_is_the_length, the_count_through_the_closure_is_the_length]
--×   rfl

-- Episode13.lean, line 2042
--× theorem the_number_comes_out_of_every_inductive :
--×     the_counts_through_all_the_inductives.map (fun count => bent_card.fenceposts_must_be_preserved Nat count all_possible_variables)
--×       = List.replicate the_counts_through_all_the_inductives.length arrange_the_information_appropriately := by
--×   rw [every_count_is_the_length, List.map_replicate, List.length_replicate]
--×   rfl

-- Episode13.lean, line 2318
--× set_option maxRecDepth 100000 in -- the lists are long; the elaborator needs room to count them
--× theorem the_final_inferred_closure_all_the_way_down :
--×     the_only_logical_inconsistency.all_the_way_down.length
--×         = the_giant_list.length + the_only_logical_inconsistency.infer.length
--×       ∧ the_only_logical_inconsistency.infer.length = 3
--×       ∧ the_most_basic_of_conclusions.all_the_way_down.length = 34 := ⟨rfl, rfl, rfl⟩

-- Episode13.lean, line 2325
--× set_option maxRecDepth 100000 in -- the lists are long; the elaborator needs room to count them
--× theorem the_giant_list_is_four_conclusions_and_one_truth :
--×     the_giant_list.length
--×       = (the_most_basic_of_conclusions.all_the_way_down.length
--×           + the_most_basic_of_conclusions.all_the_way_down.length)
--×         + (the_most_basic_of_conclusions.all_the_way_down.length
--×           + the_most_basic_of_conclusions.all_the_way_down.length)
--×         + [FACT.Truth].length := rfl

-- Episode13.lean, line 2337
--× def the_cells_left_over : Nat :=
--×   the_only_logical_inconsistency.infer.length * the_basis.the_reading.length ^ the_free_variable_count + [FACT.Truth].length

-- Episode13.lean, line 2341
--× set_option maxRecDepth 100000 in
--× theorem the_giant_list_closes_on_the_cells_left_over :
--×     the_coordinate_system.gauss.length * the_coefficient_tape.length * the_giant_list.length
--×       = the_memory_tape.length * the_memory_tape.length * the_memory_tape.length + the_cells_left_over := by decide

-- Episode13.lean, line 2348
--× theorem the_cells_left_over_are_the_whole_part_of_the_root :
--×     the_cells_left_over * the_cells_left_over
--×         ≤ (the_memory_tape.length * the_memory_tape.length) * (the_memory_tape.length * the_memory_tape.length)
--×             * (the_coordinate_system.gauss.length * the_memory_tape.length)
--×       ∧ (the_memory_tape.length * the_memory_tape.length) * (the_memory_tape.length * the_memory_tape.length)
--×             * (the_coordinate_system.gauss.length * the_memory_tape.length)
--×           < (the_cells_left_over + [FACT.Truth].length) * (the_cells_left_over + [FACT.Truth].length) := by decide

-- Episode13.lean, line 2357
--× def the_digits_past_the_giant_list : Nat := the_constant_factor_of_scaling_bullshit - the_giant_list.length * all_possible_variables

-- Episode13.lean, line 2364
--× def the_root_to_the_scale : Nat :=
--×   the_digits_past_the_giant_list * (the_coordinate_system.gauss.length * the_coefficient_tape.length)
--×     + the_cells_left_over * all_possible_variables

-- Episode13.lean, line 2368
--× set_option maxRecDepth 100000 in
--× theorem the_digits_are_the_rest_of_the_root :
--×     the_root_to_the_scale * the_root_to_the_scale
--×         ≤ (the_memory_tape.length * the_memory_tape.length) * (the_memory_tape.length * the_memory_tape.length)
--×             * (the_coordinate_system.gauss.length * the_memory_tape.length) * (all_possible_variables * all_possible_variables)
--×       ∧ (the_memory_tape.length * the_memory_tape.length) * (the_memory_tape.length * the_memory_tape.length)
--×             * (the_coordinate_system.gauss.length * the_memory_tape.length) * (all_possible_variables * all_possible_variables)
--×           < (the_root_to_the_scale + the_coordinate_system.gauss.length * the_coefficient_tape.length)
--×               * (the_root_to_the_scale + the_coordinate_system.gauss.length * the_coefficient_tape.length) := by decide

-- Episode13.lean, line 2395
--× set_option maxRecDepth 100000 in
--× theorem the_two_roots_in_cells :
--×     (the_memory_tape.length * the_memory_tape.length * the_memory_tape.length + the_cells_left_over) % the_frame_by_the_coefficient
--×         = [].length (α := FACT)
--×       ∧ (the_memory_tape.length * the_memory_tape.length * the_memory_tape.length - (the_cells_left_over + [FACT.Truth].length))
--×           / the_frame_by_the_coefficient = what_is_left_of_the_sum
--×       ∧ (the_memory_tape.length * the_memory_tape.length * the_memory_tape.length - (the_cells_left_over + [FACT.Truth].length))
--×           % the_frame_by_the_coefficient + [FACT.Truth].length = the_sum_of_the_roots_in_cells % the_frame_by_the_coefficient
--×       ∧ the_sum_of_the_roots_in_cells % the_frame_by_the_coefficient
--×           = the_most_basic_of_conclusions.all_the_way_down.length - the_most_basic_of_conclusions.meter.length := by decide

-- Episode13.lean, line 2408
--× def the_other_roots_digits : Nat :=
--×   (the_sum_of_the_roots_in_cells * all_possible_variables / the_frame_by_the_coefficient - the_constant_factor_of_scaling_bullshit)
--×     - what_is_left_of_the_sum * all_possible_variables

-- Episode13.lean, line 2412
--× set_option maxRecDepth 100000 in
--× theorem the_two_residues_are_one_ratio :
--×     the_digits_past_the_giant_list + the_other_roots_digits
--×       = (the_sum_of_the_roots_in_cells % the_frame_by_the_coefficient) * all_possible_variables / the_frame_by_the_coefficient := by decide

-- Episode13.lean, line 2422
--× theorem the_click_is_the_order_on_two_truths (this that : Bool) :
--×     the_arm_stores_a_fact_that_can_click this that = decide (this = true → that = true) := by
--×   cases this <;> cases that <;> rfl

-- Episode13.lean, line 2426
--× theorem three_click_and_one_does_not :
--×     ([(true, true), (true, false), (false, true), (false, false)].filter
--×         fun arm => decide (arm.1 = true → arm.2 = true)).length = 3 := by decide

-- Episode13.lean, line 2434
--× theorem the_shape_has_these_eigenproperties (clicks does_not : Int) :
--×     (clicks + clicks) * (clicks + clicks) - 4 * (clicks * clicks - does_not * clicks) = 4 * (clicks * does_not) := by
--×   simp only [Int.add_mul, Int.mul_add, Int.mul_sub, Int.mul_comm does_not clicks]; omega

-- Episode13.lean, line 2438
--× theorem the_roots_of_the_shape (clicks does_not root : Int) (the_root_squared : root * root = clicks * does_not) :
--×     (clicks + root) * (clicks + root) - (clicks + clicks) * (clicks + root) + (clicks * clicks - does_not * clicks) = 0
--×       ∧ (clicks - root) * (clicks - root) - (clicks + clicks) * (clicks - root) + (clicks * clicks - does_not * clicks) = 0 := by
--×   constructor <;>
--×     simp only [Int.add_mul, Int.mul_add, Int.sub_mul, Int.mul_sub, Int.mul_comm does_not clicks, Int.mul_comm root clicks] <;> omega

-- Episode13.lean, line 2451
--× theorem no_function_of_the_tally_returns_the_tape : ¬ ∃ reader : Nat → List FACT, ∀ tape : List FACT, reader tape.length = tape := by
--×   intro ⟨reader, returns⟩
--×   have same : [bitFACT true] = [bitFACT false] := (returns [bitFACT true]).symm.trans (returns [bitFACT false])
--×   have one_fact : bitFACT true = bitFACT false := (List.cons.inj same).1
--×   have truth_is_not_false : (bitFACT false).truth ≠ (bitFACT true).truth := fun h => cast h.symm (rfl : true = true)
--×   exact truth_is_not_false (congrArg (fun fact : FACT => fact.truth) one_fact).symm

-- Episode13.lean, line 2460
--× theorem the_number_is_a_function_of_the_tally (reader : List FACT → Nat) (agrees : ∀ tape, reader tape = tape.length) :
--×     bent_card.fenceposts_must_be_preserved Nat reader all_possible_variables = arrange_the_information_appropriately := by
--×   rw [show reader = List.length from funext agrees]; rfl

-- Episode13.lean, line 2466
--× theorem the_action_has_no_fourth_order (place : Int) : readers_interpretation_of_the_experience.the_fourth_difference the_cubic_action place = 0 := by
--×   have cubic : the_cubic_action
--×       = fun y => 0 + (6 * (the_number_of_symbols_that_must_be_written_to_express_this : Int)) * y
--×           + (-(3 * (the_trace_of_truth_in_the_device : Int))) * (y * y)
--×           + (2 * (an_exact_polynomial_description : Int)) * (y * y * y) := by
--×     funext y
--×     simp only [the_cubic_action, Int.neg_mul, Int.zero_add]
--×     ac_nf; simp only [← Int.mul_assoc]; omega
--×   rw [cubic]; exact readers_interpretation_of_the_experience.a_cubic_is_exact _ _ _ _ place

-- Episode13.lean, line 2495
--× def the_number_as_a_value : Nat :=
--×   arrange_the_information_appropriately.1 * all_possible_variables / arrange_the_information_appropriately.2

-- Episode13.lean, line 2498
--× theorem the_value_is_episode_eights_constant : the_number_as_a_value = the_constant_factor_of_scaling_bullshit := rfl

-- Episode13.lean, line 2500
--× set_option maxRecDepth 100000 in
--× theorem that_the_value_is_the_ratio :
--×     (Quot.mk the_rational_idea_of_relativity
--×         (arrange_the_information_appropriately.2 * the_number_as_a_value, arrange_the_information_appropriately.2)
--×       : Quot the_rational_idea_of_relativity)
--×       = Quot.mk the_rational_idea_of_relativity
--×           (arrange_the_information_appropriately.1 * all_possible_variables, arrange_the_information_appropriately.2) :=
--×   the_constant_can_be_inferred.property

-- Episode13.lean, line 2511
--× theorem the_bent_card_alone (this that : Nat × Nat) (under : the_rational_idea_of_relativity this that) :
--×     (Quot.mk the_rational_idea_of_relativity this : Quot the_rational_idea_of_relativity)
--×       = Quot.mk the_rational_idea_of_relativity that := Quot.sound under

-- Episode13.lean, line 2524
--× def the_meter_reads : Bool → Bool → Int
--×   | true,  true  => 17712
--×   | true,  false => 16691
--×   | false, true  => 16691
--×   | false, false => 15670

-- Episode13.lean, line 2531
--× theorem the_meter_counts_the_truths (this that : Bool) :
--×     the_meter_reads this that
--×       = the_meter_reads false false
--×           + (the_meter_reads true false - the_meter_reads false false) * ((if this then 1 else 0) + (if that then 1 else 0)) := by
--×   cases this <;> cases that <;> decide

-- Episode13.lean, line 2541
--× theorem the_meter_is_the_table_turned_over :
--×     (the_arm_weight true true = the_arm_weight false false ∧ the_arm_weight true false ≠ the_arm_weight false true)
--×       ∧ (the_meter_reads true false = the_meter_reads false true ∧ the_meter_reads true true ≠ the_meter_reads false false)
--×       ∧ (the_arm_weight true true + the_arm_weight false false, the_arm_weight true true - the_arm_weight false false,
--×           the_arm_weight true false + the_arm_weight false true, the_arm_weight false true - the_arm_weight true false)
--×           = (the_trace_of_truth_in_the_device, 0, 23, bent_card)
--×       ∧ (the_meter_reads true true + the_meter_reads false false, the_meter_reads true true - the_meter_reads false false,
--×           the_meter_reads true false + the_meter_reads false true, the_meter_reads false true - the_meter_reads true false)
--×           = (33382, 2 * (the_meter_reads true false - the_meter_reads false false), 33382, 0) := by decide

-- Episode13.lean, line 2552
--× theorem the_meters_determinant_is_the_step_squared_owed :
--×     the_meter_reads true true * the_meter_reads false false - the_meter_reads true false * the_meter_reads false true
--×       = - ((the_meter_reads true false - the_meter_reads false false) * (the_meter_reads true false - the_meter_reads false false)) := by
--×   decide

-- Episode13.lean, line 2560
--× def the_meter_reads_the_click (it_is_true built_as_the_device_builds : Bool) : Int :=
--×   if it_is_true && built_as_the_device_builds then 2162 else 1141

-- Episode13.lean, line 2566
--× theorem two_zeros_one_up_and_one_down :
--×     ([(true, true), (false, true), (false, false)].all fun arm =>
--×         the_arm_weight arm.1 arm.2 == the_arm_weight true false + bent_card) = true
--×       ∧ ([(true, false), (false, true), (false, false)].all fun fact =>
--×         the_meter_reads_the_click fact.1 fact.2
--×           == the_meter_reads_the_click true true - (the_meter_reads true false - the_meter_reads false false)) = true := by decide

-- Episode13.lean, line 2587
--× theorem a_place_is_not_past_them_all : ∀ (places : List Nat) (place : Nat), place ∈ places → place ≤ places.foldr Nat.add 0
--×   | [],        _,     looked => nomatch looked
--×   | _ :: rest, place, looked => by
--×     cases looked with
--×     | head => exact Nat.le_add_right _ _
--×     | tail _ further => exact Nat.le_trans (a_place_is_not_past_them_all rest place further) (Nat.le_add_left _ _)

-- Episode13.lean, line 2596
--× theorem a_finite_record_does_not_tell {what_is_read : Type} (otherwise : what_is_read → what_is_read)
--×     (apart : ∀ reading, otherwise reading ≠ reading) (places : List Nat) (the_model : Nat → what_is_read) :
--×     ∃ another_model : Nat → what_is_read,
--×       (∀ place, place ∈ places → another_model place = the_model place) ∧ another_model ≠ the_model := by
--×   refine ⟨fun place => if place = places.foldr Nat.add 0 + 1 then otherwise (the_model place) else the_model place, ?_, ?_⟩
--×   · intro place looked
--×     have not_past : place ≠ places.foldr Nat.add 0 + 1 :=
--×       fun past => Nat.not_succ_le_self _ (past ▸ a_place_is_not_past_them_all places place looked)
--×     exact if_neg not_past
--×   · intro same
--×     have there : (if places.foldr Nat.add 0 + 1 = places.foldr Nat.add 0 + 1
--×         then otherwise (the_model (places.foldr Nat.add 0 + 1)) else the_model (places.foldr Nat.add 0 + 1))
--×           = the_model (places.foldr Nat.add 0 + 1) := congrFun same _
--×     rw [if_pos rfl] at there
--×     exact apart _ there

-- Episode13.lean, line 2613
--× theorem the_value_and_the_velocity_do_not_tell (places : List Nat) (the_model : Nat → Nat × Nat) :
--×     ∃ another_model : Nat → Nat × Nat,
--×       (∀ place, place ∈ places → another_model place = the_model place) ∧ another_model ≠ the_model :=
--×   a_finite_record_does_not_tell (fun reading => (reading.1 + 1, reading.2))
--×     (fun reading same => Nat.succ_ne_self reading.1 (congrArg Prod.fst same)) places the_model

-- Episode13.lean, line 2622
--× def the_path_here                    : SpaceTimePath.{0} := .einstein FACT.Truth
--× def come_from_somewhere     : SpaceTimePath.{0} := .whitehole FACT.Truth FACT the_path_here
--× def going_somewhere         : SpaceTimePath.{0} := .blackhole (FACT.Truth).truth Type the_path_here
--× def the_yarn_from_somewhere : YarnTheory.{0,0,0,0,0,0} := .stokes FACT.Truth come_from_somewhere (FACT.Truth).truth
--× def the_yarn_to_somewhere   : YarnTheory.{0,0,0,0,0,0} := .stokes FACT.Truth going_somewhere (FACT.Truth).truth
--× def the_yarn_with_both_ends : YarnTheory.{0,0,0,0,0,0} :=
--×   .fibers FACT.Truth come_from_somewhere going_somewhere (FACT.Truth).truth (FACT.Truth).truth (.stokes FACT.Truth the_path_here (FACT.Truth).truth)

-- Episode13.lean, line 2632
--× theorem the_two_ends_read_the_same_and_are_not_the_same :
--×     the_yarn_from_somewhere.all_the_way_down = the_yarn_to_somewhere.all_the_way_down
--×       ∧ the_yarn_from_somewhere ≠ the_yarn_to_somewhere := by
--×   refine ⟨rfl, ?_⟩
--×   intro same
--×   injection same with _ paths _
--×   exact SpaceTimePath.noConfusion paths

-- Episode13.lean, line 2641
--× theorem both_ends_are_read_once_each :
--×     the_yarn_with_both_ends.all_the_way_down.length
--×       = come_from_somewhere.all_the_way_down.length + going_somewhere.all_the_way_down.length
--×         + (YarnTheory.stokes FACT.Truth the_path_here (FACT.Truth).truth).all_the_way_down.length + [FACT.Truth, FACT.Truth, FACT.Truth].length := rfl

-- Episode13.lean, line 2655
--× def the_mirror : Table := fun a b => if a = b then the_coin_sign a else 1

-- Episode13.lean, line 2657
--× theorem the_mirror_twice_is_nothing_done_twice :
--×     ∀ a b : Bool, the_table_product the_mirror the_mirror a b = if a = b then 2 else 0 := by decide

-- Episode13.lean, line 2663
--× theorem the_mirror_clears_the_table :
--×     the_table_product the_mirror the_full_table true true = the_trace_of_truth_in_the_device
--×       ∧ the_table_product the_mirror the_full_table true false = (the_arm_weight true false + the_arm_weight false true : Nat)
--×       ∧ the_table_product the_mirror the_full_table false true = 0
--×       ∧ the_table_product the_mirror the_full_table false false = - (bent_card : Int) := by decide

-- Episode13.lean, line 2671
--× theorem the_mirror_on_both_sides_leaves_the_bent_card_off_the_diagonal :
--×     the_table_product (the_table_product the_mirror the_full_table) the_mirror true true
--×         = the_trace_of_truth_in_the_device + (the_arm_weight true false + the_arm_weight false true : Nat)
--×       ∧ the_table_product (the_table_product the_mirror the_full_table) the_mirror false false
--×         = the_trace_of_truth_in_the_device - (the_arm_weight true false + the_arm_weight false true : Nat)
--×       ∧ the_table_product (the_table_product the_mirror the_full_table) the_mirror true false = (bent_card : Int)
--×       ∧ the_table_product (the_table_product the_mirror the_full_table) the_mirror false true = - (bent_card : Int) := by decide

-- Episode13.lean, line 2681
--× theorem the_mirror_carries_the_commutator_onto_the_crossings :
--×     ∀ a b : Bool,
--×       the_table_product (the_table_product the_mirror (the_table_bracket the_clock_table the_other_clock)) the_mirror a b
--×         = if a = b then 0
--×           else - (2 * ((bent_card : Int) * (the_arm_weight true false + the_arm_weight false true : Nat))) := by decide

-- Episode13.lean, line 2689
--× theorem the_mirror_leaves_the_solver :
--×     (the_arm_weight true false + the_arm_weight false true) * (the_arm_weight true false + the_arm_weight false true)
--×         = 4 * (the_arm_weight true false * the_arm_weight false true) + bent_card * bent_card
--×       ∧ bent_card * (the_arm_weight true true * the_arm_weight false false - the_arm_weight true false * the_arm_weight false true)
--×           = bent_card * bent_card * the_arm_weight true true := by decide

-- Episode13.lean, line 2720
--× theorem the_triple_is_the_knowers_coin_against_the_arm :
--×     ∀ a b c : Bool,
--×       (the_knowers_triple.holds (assignFrom [a, b, c]) an_odd_number_are_true 0).1 = (a != (b != c))
--×         ∧ (the_knowers_triple.holds (assignFrom [a, b, c]) an_even_number_are_true 0).1 = (a == (b != c)) := by decide

-- Episode13.lean, line 2727
--× theorem the_clock_is_even_and_its_complement_is_odd :
--×     (allAssignments 3).filter (fun coins => (the_knowers_triple.holds (assignFrom coins) an_odd_number_are_true 0).1)
--×         = [[true, true, true], [false, false, true], [false, true, false], [true, false, false]]
--×       ∧ (allAssignments 3).filter (fun coins => (the_knowers_triple.holds (assignFrom coins) an_even_number_are_true 0).1)
--×         = [[false, true, true], [true, false, true], [true, true, false], [false, false, false]] := by decide

-- Episode13.lean, line 2734
--× theorem the_solver_finds_a_witness_either_way :
--×     satSearch the_knowers_triple an_odd_number_are_true 3 = true ∧ satSearch the_knowers_triple an_even_number_are_true 3 = true := by
--×   decide

-- Episode13.lean, line 2740
--× def two_triples : Basis := .basis cookFACT (.mul cookFACT a_triple a_triple (.origin cookFACT)) phi_accept (.null_space cookFACT)
--× def the_clock_and_its_complement : Schedule := by_the_signs [true, false, true, true,   false, true, false, false]
--× theorem the_clocks_are_what_the_clocks_rule_out :
--×     (allAssignments 3).filter (fun coins => !(two_triples.holds (assignFrom coins) the_clock_and_its_complement 0).1)
--×       = [[true, false, true], [false, true, false]] := by decide

-- Episode13.lean, line 2750
--× def the_step_connected : Basis :=
--×   .basis cookFACT
--×     (.mul cookFACT (.add cookFACT varA varB (.zero True varA)) (.add cookFACT varA varB (.zero True varA))
--×       (.mul cookFACT (.add cookFACT varB the_third_coin (.zero True varB)) (.add cookFACT varB the_third_coin (.zero True varB))
--×         (.origin cookFACT)))
--×     phi_accept (.null_space cookFACT)
--× theorem the_step_connected_is_the_two_clocks :
--×     (allAssignments 3).filter (fun coins => (the_step_connected.holds (assignFrom coins) alternating 0).1)
--×         = [[true, false, true], [false, true, false]]
--×       ∧ satWitness the_step_connected alternating 3 = some [true, false, true] := by decide

-- Episode13.lean, line 2778
--× theorem the_count_has_a_root_and_the_reader_of_one_cell_has_none :
--×     there_is_a_root_for List.length = true ∧ there_is_a_root_for (fun _ => [FACT.Truth].length) = false := by decide

-- Episode13.lean, line 2785
--× open Lean Elab Term Meta in
--× def the_tape_on_the_clock (tape : TSyntax `term) : TermElabM (Nat × Nat) := do
--×   let every_cell_clicked ← `(($tape).all (fun fact : FACT => fact.bit || !fact.bit))
--×   let before ← IO.monoNanosNow
--×   let (_, beats) ← withHeartbeats do
--×     let e ← elabTerm every_cell_clicked none; let _ ← whnf e; pure ()
--×   let after ← IO.monoNanosNow
--×   pure (beats, after - before)

-- Episode13.lean, line 2795
--× def the_value_directly (epsilon gauss coefficient reading memory blank : Nat) : Option Float :=
--×   if 4 * coefficient * memory * blank * blank ≤ (reading * memory) * (reading * memory) then
--×     let over (n : Nat) : Float := n.toFloat / blank.toFloat
--×     some ((over epsilon * over epsilon / over gauss)
--×       * (over reading * over memory + Float.sqrt ((over reading * over memory) * (over reading * over memory) - 4 * over coefficient * over memory))
--×       / (2 * over coefficient))
--×   else none

-- Episode13.lean, line 2803
--× open Lean Elab Term Meta Command in
--× elab "can_you_distinguish_a_number?" : command => do
--×   Command.liftTermElabM do
--×     let blank       ← the_tape_on_the_clock (← `([FACT.Truth]))
--×     let epsilon     ← the_tape_on_the_clock (← `(the_epsilon_tape))
--×     let gauss       ← the_tape_on_the_clock (← `(the_coordinate_system.gauss))
--×     let coefficient ← the_tape_on_the_clock (← `(the_coefficient_tape))
--×     let reading     ← the_tape_on_the_clock (← `(the_basis.the_reading))
--×     let memory      ← the_tape_on_the_clock (← `(the_memory_tape))
--×     let say (what : String) (read : List Nat) (over : Nat) (value : Option Float) : MessageData :=
--×       match value with
--×       | some v => m!"{what}: {v}   {read} over {over}"
--×       | none   => m!"{what}: no value   {read} over {over}"
--×     logInfo (say "on the count"
--×       [the_epsilon_tape.length, the_coordinate_system.gauss.length, the_coefficient_tape.length, the_basis.the_reading.length,
--×         the_memory_tape.length] [FACT.Truth].length
--×       (the_value_directly the_epsilon_tape.length the_coordinate_system.gauss.length
--×         the_coefficient_tape.length the_basis.the_reading.length the_memory_tape.length [FACT.Truth].length))
--×     logInfo (say "on the heartbeats" [epsilon.1, gauss.1, coefficient.1, reading.1, memory.1] blank.1
--×       (the_value_directly epsilon.1 gauss.1 coefficient.1 reading.1 memory.1 blank.1))
--×     logInfo (say "on the clock, this run" [epsilon.2, gauss.2, coefficient.2, reading.2, memory.2] blank.2
--×       (the_value_directly epsilon.2 gauss.2 coefficient.2 reading.2 memory.2 blank.2))

-- Episode13.lean, line 2857
--× theorem the_number_clicks : the_click a_number_is_distinguished = true := by decide

-- Episode13.lean, line 2869
--× theorem asked_only_whether_it_is_true_the_number_is_the_truth : a_number_is_distinguished = FACT.Truth :=
--×   two_facts_that_are_true_are_one_fact _ _
--×     (@of_decide_eq_true a_number_is_distinguished.truth a_number_is_distinguished.click the_number_clicks)
--×     (@of_decide_eq_true FACT.Truth.truth FACT.Truth.click rfl)

-- Episode13.lean, line 2890
--× noncomputable instance A_MODEL_OF_THE_NUMBER : REAL FACT the_first_card := A_CAUSAL_THEORY FACT the_first_card
--× noncomputable def this_way_to_the_number : LOCAL FACT the_first_card := A_SMOOTH_MODEL FACT the_first_card
--× noncomputable def that_way_to_the_number : UNIVERSAL FACT the_first_card this_way_to_the_number :=
--×   IS_IT_CONNECTED_BY_A_YARN? FACT the_first_card (nowtrino_model := this_way_to_the_number)

-- Episode13.lean, line 2895
--× noncomputable def the_numbers_rung02 :=
--×   STEP2_DISCOVER_SOMETHING_DIFFERENT FACT the_first_card the_first_card a_number_is_distinguished the_crossing_of_the_number

-- Episode13.lean, line 2898
--× noncomputable def the_numbers_rung03 :=
--×   STEP3_COUNT_THE_NUMBER_OF_THE_PHENOMENA FACT the_first_card the_first_card a_number_is_distinguished the_crossing_of_the_number the_numbers_rung02

-- Episode13.lean, line 2901
--× noncomputable def the_numbers_rung04 :=
--×   STEP4_COMPUTE_THE_RATE_OF_PARTICLES FACT the_first_card the_first_card a_number_is_distinguished the_crossing_of_the_number the_numbers_rung02 the_numbers_rung03

-- Episode13.lean, line 2904
--× noncomputable def the_numbers_rung05 :=
--×   STEP5_NAME_THE_RESIDUE_TO_COMPUTE_VALUE FACT the_first_card the_first_card a_number_is_distinguished the_crossing_of_the_number the_numbers_rung02 the_numbers_rung03 the_numbers_rung04

-- Episode13.lean, line 2907
--× noncomputable def the_numbers_rung06 :=
--×   STEP6_MAKE_ANOTHER_COUNTER_OF_CLICKS_NOW FACT the_first_card the_first_card a_number_is_distinguished the_crossing_of_the_number the_numbers_rung02 the_numbers_rung03 the_numbers_rung04 the_numbers_rung05

-- Episode13.lean, line 2910
--× noncomputable def the_numbers_rung07 :=
--×   STEP7_AND_SO_WE_CANT_COUNT_HOW_OFTEN_THE_METAPHOR_GOES_AROUND_JUST_LIKE_PITS_AND_LANDS_ON_A_CD FACT the_first_card the_first_card a_number_is_distinguished the_crossing_of_the_number the_numbers_rung02 the_numbers_rung03 the_numbers_rung04 the_numbers_rung05 the_numbers_rung06

-- Episode13.lean, line 2913
--× noncomputable def the_numbers_rung08 :=
--×   STEP8_INTERPRET_THE_NEXT_3_SYMBOLS FACT the_first_card the_first_card a_number_is_distinguished the_crossing_of_the_number the_numbers_rung02 the_numbers_rung03 the_numbers_rung04 the_numbers_rung05 the_numbers_rung06 the_numbers_rung07

-- Episode13.lean, line 2916
--× noncomputable def the_numbers_rung09 :=
--×   STEP9_NAME_THE_VARIABLES_CAREFULLY_TO_TELL_A_STORY FACT the_first_card the_first_card a_number_is_distinguished the_crossing_of_the_number the_numbers_rung02 the_numbers_rung03 the_numbers_rung04 the_numbers_rung05 the_numbers_rung06 the_numbers_rung07 the_numbers_rung08

-- Episode13.lean, line 2919
--× noncomputable def the_numbers_rung10 :=
--×   STEP10_A_HALTING_COMPUTATION_IS_GIVEN_AS_INPUT_TO_A_NON_HALTING_FUNCTION FACT the_first_card the_first_card a_number_is_distinguished the_crossing_of_the_number the_numbers_rung02 the_numbers_rung03 the_numbers_rung04 the_numbers_rung05 the_numbers_rung06 the_numbers_rung07 the_numbers_rung08 the_numbers_rung09

-- Episode13.lean, line 2922
--× deal_rung the_numbers_rung11 := STEP11_CHECK_FOR_CONVERGENCE_IN_THE_TIMESERIES_MATCHES_THE_MEASUREMENT_HIGH_ORDER_TERMS
--×     FACT the_first_card the_first_card a_number_is_distinguished the_crossing_of_the_number the_numbers_rung02 the_numbers_rung03 the_numbers_rung04 the_numbers_rung05 the_numbers_rung06 the_numbers_rung07 the_numbers_rung08 the_numbers_rung09 the_numbers_rung10

-- Episode13.lean, line 2925
--× deal_rung the_numbers_rung12 := STEP12_CHECK_TO_SEE_IF_THE_BORWEIN_PROCESS_HAS_UNCOVERED_A_PROPERTY_OF_ELECTRONS
--×     FACT the_first_card the_first_card a_number_is_distinguished the_crossing_of_the_number the_numbers_rung02 the_numbers_rung03 the_numbers_rung04 the_numbers_rung05 the_numbers_rung06 the_numbers_rung07 the_numbers_rung08 the_numbers_rung09 the_numbers_rung10 the_numbers_rung11

-- Episode13.lean, line 2928
--× deal_rung the_numbers_rung13 := STEP13_RECORD_THE_OBSERVATION_AS_A_MODELED_AST_AS_OF_RIGHT_NOW
--×     FACT the_first_card the_first_card a_number_is_distinguished the_crossing_of_the_number the_numbers_rung02 the_numbers_rung03 the_numbers_rung04 the_numbers_rung05 the_numbers_rung06 the_numbers_rung07 the_numbers_rung08 the_numbers_rung09 the_numbers_rung10 the_numbers_rung11 the_numbers_rung12

-- Episode13.lean, line 2931
--× deal_rung the_numbers_rung14 := STEP14_REALIZE_THAT_THIS_PROCESS_TAKES_THE_APPARANT_SAME_AMOUNT_OF_TIME_EACH_TIME
--×     FACT the_first_card the_first_card a_number_is_distinguished the_crossing_of_the_number the_numbers_rung02 the_numbers_rung03 the_numbers_rung04 the_numbers_rung05 the_numbers_rung06 the_numbers_rung07 the_numbers_rung08 the_numbers_rung09 the_numbers_rung10 the_numbers_rung11 the_numbers_rung12 the_numbers_rung13

-- Episode13.lean, line 2934
--× deal_rung the_numbers_rung15 := STEP15_SO_MODEL_THE_PROCESS_AS_SOMETHING_THAT_JUST_SPEWS_OUT_TRUE
--×     FACT the_first_card the_first_card a_number_is_distinguished the_crossing_of_the_number the_numbers_rung02 the_numbers_rung03 the_numbers_rung04 the_numbers_rung05 the_numbers_rung06 the_numbers_rung07 the_numbers_rung08 the_numbers_rung09 the_numbers_rung10 the_numbers_rung11 the_numbers_rung12 the_numbers_rung13 the_numbers_rung14

-- Episode13.lean, line 2937
--× deal_rung the_numbers_rung16 := STEP16_VERIFY_THE_SOURCE_FILE_ONLY_EMITS_TRUE_STATEMENTS
--×     FACT the_first_card the_first_card a_number_is_distinguished the_crossing_of_the_number the_numbers_rung02 the_numbers_rung03 the_numbers_rung04 the_numbers_rung05 the_numbers_rung06 the_numbers_rung07 the_numbers_rung08 the_numbers_rung09 the_numbers_rung10 the_numbers_rung11 the_numbers_rung12 the_numbers_rung13 the_numbers_rung14 the_numbers_rung15

-- Episode13.lean, line 2940
--× deal_rung the_numbers_rung17 := STEP17_MAKE_SURE_THIS_COMPILES_AND_DEMONSTRATES_IT_IS_TRUE_IN_GUNGAN
--×     FACT the_first_card the_first_card a_number_is_distinguished the_crossing_of_the_number the_numbers_rung02 the_numbers_rung03 the_numbers_rung04 the_numbers_rung05 the_numbers_rung06 the_numbers_rung07 the_numbers_rung08 the_numbers_rung09 the_numbers_rung10 the_numbers_rung11 the_numbers_rung12 the_numbers_rung13 the_numbers_rung14 the_numbers_rung15 the_numbers_rung16

-- Episode13.lean, line 2943
--× deal_rung the_numbers_rung18 := STEP18_GIVEN_AN_INFERRED_DEFINITION_OF_THE_DEVICE_MAKE_THE_DEVICE
--×     FACT the_first_card the_first_card a_number_is_distinguished the_crossing_of_the_number the_numbers_rung02 the_numbers_rung03 the_numbers_rung04 the_numbers_rung05 the_numbers_rung06 the_numbers_rung07 the_numbers_rung08 the_numbers_rung09 the_numbers_rung10 the_numbers_rung11 the_numbers_rung12 the_numbers_rung13 the_numbers_rung14 the_numbers_rung15 the_numbers_rung16 the_numbers_rung17

-- Episode13.lean, line 2946
--× deal_rung the_numbers_rung19 := STEP19_GIVEN_THE_ABILITY_TO_COUNT_SOMETHING_LEAN_CAN_NOW_INFER_ADDITION
--×     FACT the_first_card the_first_card a_number_is_distinguished the_crossing_of_the_number the_numbers_rung02 the_numbers_rung03 the_numbers_rung04 the_numbers_rung05 the_numbers_rung06 the_numbers_rung07 the_numbers_rung08 the_numbers_rung09 the_numbers_rung10 the_numbers_rung11 the_numbers_rung12 the_numbers_rung13 the_numbers_rung14 the_numbers_rung15 the_numbers_rung16 the_numbers_rung17 the_numbers_rung18

-- Episode13.lean, line 2949
--× deal_rung the_numbers_rung20 := STEP20_DUPLICATE_THE_PROCESS_TO_DEMONSTRATE_AREA_OF_RECTANGLES_LIKE_EUCLID
--×     FACT the_first_card the_first_card a_number_is_distinguished the_crossing_of_the_number the_numbers_rung02 the_numbers_rung03 the_numbers_rung04 the_numbers_rung05 the_numbers_rung06 the_numbers_rung07 the_numbers_rung08 the_numbers_rung09 the_numbers_rung10 the_numbers_rung11 the_numbers_rung12 the_numbers_rung13 the_numbers_rung14 the_numbers_rung15 the_numbers_rung16 the_numbers_rung17 the_numbers_rung18 the_numbers_rung19

-- Episode13.lean, line 2952
--× deal_rung the_numbers_rung21 := STEP21_GIVEN_ADDITION_MULTIPLICATION_AND_NUMBERS_INFER_ALL_OF_MATH
--×     FACT the_first_card the_first_card a_number_is_distinguished the_crossing_of_the_number the_numbers_rung02 the_numbers_rung03 the_numbers_rung04 the_numbers_rung05 the_numbers_rung06 the_numbers_rung07 the_numbers_rung08 the_numbers_rung09 the_numbers_rung10 the_numbers_rung11 the_numbers_rung12 the_numbers_rung13 the_numbers_rung14 the_numbers_rung15 the_numbers_rung16 the_numbers_rung17 the_numbers_rung18 the_numbers_rung19 the_numbers_rung20

-- Episode13.lean, line 2955
--× deal_rung the_numbers_rung22 := STEP22_PAY_CLOSE_ATTENTION_TO_WEAK_SOLUTIONS_OF_DIFFERENTIAL_EQUATIONS_WHILE_DERIVING_MATH
--×     FACT the_first_card the_first_card a_number_is_distinguished the_crossing_of_the_number the_numbers_rung02 the_numbers_rung03 the_numbers_rung04 the_numbers_rung05 the_numbers_rung06 the_numbers_rung07 the_numbers_rung08 the_numbers_rung09 the_numbers_rung10 the_numbers_rung11 the_numbers_rung12 the_numbers_rung13 the_numbers_rung14 the_numbers_rung15 the_numbers_rung16 the_numbers_rung17 the_numbers_rung18 the_numbers_rung19 the_numbers_rung20 the_numbers_rung21

-- Episode13.lean, line 2958
--× deal_rung the_numbers_rung23 := STEP23_GET_RID_OF_A_DERIVATIVE_SO_THAT_THE_SECOND_ORDER_MODEL_OF_THE_DEVICE_CAN_BE_WRITTEN_VARIATIONALLY
--×     FACT the_first_card the_first_card a_number_is_distinguished the_crossing_of_the_number the_numbers_rung02 the_numbers_rung03 the_numbers_rung04 the_numbers_rung05 the_numbers_rung06 the_numbers_rung07 the_numbers_rung08 the_numbers_rung09 the_numbers_rung10 the_numbers_rung11 the_numbers_rung12 the_numbers_rung13 the_numbers_rung14 the_numbers_rung15 the_numbers_rung16 the_numbers_rung17 the_numbers_rung18 the_numbers_rung19 the_numbers_rung20 the_numbers_rung21 the_numbers_rung22

-- Episode13.lean, line 2961
--× deal_rung the_numbers_rung24 := STEP24_RESTATE_THE_MODEL_AS_A_PRINCIPLE_OF_LEAST_ACTION
--×     FACT the_first_card the_first_card a_number_is_distinguished the_crossing_of_the_number the_numbers_rung02 the_numbers_rung03 the_numbers_rung04 the_numbers_rung05 the_numbers_rung06 the_numbers_rung07 the_numbers_rung08 the_numbers_rung09 the_numbers_rung10 the_numbers_rung11 the_numbers_rung12 the_numbers_rung13 the_numbers_rung14 the_numbers_rung15 the_numbers_rung16 the_numbers_rung17 the_numbers_rung18 the_numbers_rung19 the_numbers_rung20 the_numbers_rung21 the_numbers_rung22 the_numbers_rung23

-- Episode13.lean, line 2964
--× deal_rung the_numbers_rung25 := STEP25_BUILD_LOCAL_GEOMETRIES_THAT_SATISFY_THE_TRIANGLE_INEQUALITY
--×     FACT the_first_card the_first_card a_number_is_distinguished the_crossing_of_the_number the_numbers_rung02 the_numbers_rung03 the_numbers_rung04 the_numbers_rung05 the_numbers_rung06 the_numbers_rung07 the_numbers_rung08 the_numbers_rung09 the_numbers_rung10 the_numbers_rung11 the_numbers_rung12 the_numbers_rung13 the_numbers_rung14 the_numbers_rung15 the_numbers_rung16 the_numbers_rung17 the_numbers_rung18 the_numbers_rung19 the_numbers_rung20 the_numbers_rung21 the_numbers_rung22 the_numbers_rung23 the_numbers_rung24

-- Episode13.lean, line 2967
--× deal_rung the_numbers_rung26 := STEP26_WRITE_YOUR_PROOF_IN_THE_FORMAL_LANGUAGE_OF_GEOMETRY
--×     FACT the_first_card the_first_card a_number_is_distinguished the_crossing_of_the_number the_numbers_rung02 the_numbers_rung03 the_numbers_rung04 the_numbers_rung05 the_numbers_rung06 the_numbers_rung07 the_numbers_rung08 the_numbers_rung09 the_numbers_rung10 the_numbers_rung11 the_numbers_rung12 the_numbers_rung13 the_numbers_rung14 the_numbers_rung15 the_numbers_rung16 the_numbers_rung17 the_numbers_rung18 the_numbers_rung19 the_numbers_rung20 the_numbers_rung21 the_numbers_rung22 the_numbers_rung23 the_numbers_rung24 the_numbers_rung25

-- Episode13.lean, line 2970
--× deal_rung the_numbers_rung27 := STEP27_REPRESENT_THE_TAYLOR_SERIES_OF_THE_DEVICE
--×     FACT the_first_card the_first_card a_number_is_distinguished the_crossing_of_the_number the_numbers_rung02 the_numbers_rung03 the_numbers_rung04 the_numbers_rung05 the_numbers_rung06 the_numbers_rung07 the_numbers_rung08 the_numbers_rung09 the_numbers_rung10 the_numbers_rung11 the_numbers_rung12 the_numbers_rung13 the_numbers_rung14 the_numbers_rung15 the_numbers_rung16 the_numbers_rung17 the_numbers_rung18 the_numbers_rung19 the_numbers_rung20 the_numbers_rung21 the_numbers_rung22 the_numbers_rung23 the_numbers_rung24 the_numbers_rung25 the_numbers_rung26

-- Episode13.lean, line 2973
--× deal_rung the_numbers_rung28 := STEP28_MAKE_SURE_YOUR_CURVES_ARE_SMOOTH_AS_A_DIFFERENTIALS_BOTTOM
--×     FACT the_first_card the_first_card a_number_is_distinguished the_crossing_of_the_number the_numbers_rung02 the_numbers_rung03 the_numbers_rung04 the_numbers_rung05 the_numbers_rung06 the_numbers_rung07 the_numbers_rung08 the_numbers_rung09 the_numbers_rung10 the_numbers_rung11 the_numbers_rung12 the_numbers_rung13 the_numbers_rung14 the_numbers_rung15 the_numbers_rung16 the_numbers_rung17 the_numbers_rung18 the_numbers_rung19 the_numbers_rung20 the_numbers_rung21 the_numbers_rung22 the_numbers_rung23 the_numbers_rung24 the_numbers_rung25 the_numbers_rung26 the_numbers_rung27

-- Episode13.lean, line 2976
--× deal_rung the_numbers_rung29 := STEP29_SUGGEST_A_FALSIFIABLE_EXPERIMENT
--×     FACT the_first_card the_first_card a_number_is_distinguished the_crossing_of_the_number the_numbers_rung02 the_numbers_rung03 the_numbers_rung04 the_numbers_rung05 the_numbers_rung06 the_numbers_rung07 the_numbers_rung08 the_numbers_rung09 the_numbers_rung10 the_numbers_rung11 the_numbers_rung12 the_numbers_rung13 the_numbers_rung14 the_numbers_rung15 the_numbers_rung16 the_numbers_rung17 the_numbers_rung18 the_numbers_rung19 the_numbers_rung20 the_numbers_rung21 the_numbers_rung22 the_numbers_rung23 the_numbers_rung24 the_numbers_rung25 the_numbers_rung26 the_numbers_rung27 the_numbers_rung28

-- Episode13.lean, line 2979
--× deal_rung the_numbers_rung30 := STEP30_PROVIDE_THE_EQUATIONS_THAT_WILL_PREDICT_THE_MEASUREMENT
--×     FACT the_first_card this_way_to_the_number the_first_card a_number_is_distinguished the_crossing_of_the_number the_numbers_rung02 the_numbers_rung03 the_numbers_rung04 the_numbers_rung05 the_numbers_rung06 the_numbers_rung07 the_numbers_rung08 the_numbers_rung09 the_numbers_rung10 the_numbers_rung11 the_numbers_rung12 the_numbers_rung13 the_numbers_rung14 the_numbers_rung15 the_numbers_rung16 the_numbers_rung17 the_numbers_rung18 the_numbers_rung19 the_numbers_rung20 the_numbers_rung21 the_numbers_rung22 the_numbers_rung23 the_numbers_rung24 the_numbers_rung25 the_numbers_rung26 the_numbers_rung27 the_numbers_rung28 the_numbers_rung29 (principia := this_way_to_the_number)

-- Episode13.lean, line 2982
--× deal_rung the_numbers_rung31 := STEP31_GET_ON_THE_NEWTON_EINSTEIN_TRAIN_OF_THOUGHT
--×     FACT the_first_card this_way_to_the_number that_way_to_the_number the_first_card a_number_is_distinguished the_crossing_of_the_number the_numbers_rung02 the_numbers_rung03 the_numbers_rung04 the_numbers_rung05 the_numbers_rung06 the_numbers_rung07 the_numbers_rung08 the_numbers_rung09 the_numbers_rung10 the_numbers_rung11 the_numbers_rung12 the_numbers_rung13 the_numbers_rung14 the_numbers_rung15 the_numbers_rung16 the_numbers_rung17 the_numbers_rung18 the_numbers_rung19 the_numbers_rung20 the_numbers_rung21 the_numbers_rung22 the_numbers_rung23 the_numbers_rung24 the_numbers_rung25 the_numbers_rung26 the_numbers_rung27 the_numbers_rung28 the_numbers_rung29 the_numbers_rung30 (the_a_train := that_way_to_the_number)

-- Episode13.lean, line 2985
--× deal_rung the_numbers_rung32 := WHAT_HAPPEN_?
--×     FACT the_first_card this_way_to_the_number that_way_to_the_number the_first_card a_number_is_distinguished the_crossing_of_the_number the_numbers_rung02 the_numbers_rung03 the_numbers_rung04 the_numbers_rung05 the_numbers_rung06 the_numbers_rung07 the_numbers_rung08 the_numbers_rung09 the_numbers_rung10 the_numbers_rung11 the_numbers_rung12 the_numbers_rung13 the_numbers_rung14 the_numbers_rung15 the_numbers_rung16 the_numbers_rung17 the_numbers_rung18 the_numbers_rung19 the_numbers_rung20 the_numbers_rung21 the_numbers_rung22 the_numbers_rung23 the_numbers_rung24 the_numbers_rung25 the_numbers_rung26 the_numbers_rung27 the_numbers_rung28 the_numbers_rung29 the_numbers_rung30 the_numbers_rung31

-- Episode13.lean, line 2988
--× deal_rung the_numbers_rung33 := SOMEBODY_SET_US_UP_THE_DEVICE
--×     FACT the_first_card this_way_to_the_number that_way_to_the_number the_first_card a_number_is_distinguished the_crossing_of_the_number the_numbers_rung02 the_numbers_rung03 the_numbers_rung04 the_numbers_rung05 the_numbers_rung06 the_numbers_rung07 the_numbers_rung08 the_numbers_rung09 the_numbers_rung10 the_numbers_rung11 the_numbers_rung12 the_numbers_rung13 the_numbers_rung14 the_numbers_rung15 the_numbers_rung16 the_numbers_rung17 the_numbers_rung18 the_numbers_rung19 the_numbers_rung20 the_numbers_rung21 the_numbers_rung22 the_numbers_rung23 the_numbers_rung24 the_numbers_rung25 the_numbers_rung26 the_numbers_rung27 the_numbers_rung28 the_numbers_rung29 the_numbers_rung30 the_numbers_rung31 the_numbers_rung32

-- Episode13.lean, line 2991
--× deal_rung the_numbers_rung34 := WE_GET_SIGNAL
--×     FACT the_first_card this_way_to_the_number that_way_to_the_number the_first_card a_number_is_distinguished the_crossing_of_the_number the_numbers_rung02 the_numbers_rung03 the_numbers_rung04 the_numbers_rung05 the_numbers_rung06 the_numbers_rung07 the_numbers_rung08 the_numbers_rung09 the_numbers_rung10 the_numbers_rung11 the_numbers_rung12 the_numbers_rung13 the_numbers_rung14 the_numbers_rung15 the_numbers_rung16 the_numbers_rung17 the_numbers_rung18 the_numbers_rung19 the_numbers_rung20 the_numbers_rung21 the_numbers_rung22 the_numbers_rung23 the_numbers_rung24 the_numbers_rung25 the_numbers_rung26 the_numbers_rung27 the_numbers_rung28 the_numbers_rung29 the_numbers_rung30 the_numbers_rung31 the_numbers_rung32 the_numbers_rung33

-- Episode13.lean, line 2994
--× deal_rung the_numbers_rung35 := WHAT_!
--×     FACT the_first_card this_way_to_the_number that_way_to_the_number the_first_card a_number_is_distinguished the_crossing_of_the_number the_numbers_rung02 the_numbers_rung03 the_numbers_rung04 the_numbers_rung05 the_numbers_rung06 the_numbers_rung07 the_numbers_rung08 the_numbers_rung09 the_numbers_rung10 the_numbers_rung11 the_numbers_rung12 the_numbers_rung13 the_numbers_rung14 the_numbers_rung15 the_numbers_rung16 the_numbers_rung17 the_numbers_rung18 the_numbers_rung19 the_numbers_rung20 the_numbers_rung21 the_numbers_rung22 the_numbers_rung23 the_numbers_rung24 the_numbers_rung25 the_numbers_rung26 the_numbers_rung27 the_numbers_rung28 the_numbers_rung29 the_numbers_rung30 the_numbers_rung31 the_numbers_rung32 the_numbers_rung33 the_numbers_rung34

-- Episode13.lean, line 2997
--× deal_rung the_numbers_rung36 := MAIN_SCREEN_TURN_ON
--×     FACT the_first_card this_way_to_the_number that_way_to_the_number the_first_card a_number_is_distinguished the_crossing_of_the_number the_numbers_rung02 the_numbers_rung03 the_numbers_rung04 the_numbers_rung05 the_numbers_rung06 the_numbers_rung07 the_numbers_rung08 the_numbers_rung09 the_numbers_rung10 the_numbers_rung11 the_numbers_rung12 the_numbers_rung13 the_numbers_rung14 the_numbers_rung15 the_numbers_rung16 the_numbers_rung17 the_numbers_rung18 the_numbers_rung19 the_numbers_rung20 the_numbers_rung21 the_numbers_rung22 the_numbers_rung23 the_numbers_rung24 the_numbers_rung25 the_numbers_rung26 the_numbers_rung27 the_numbers_rung28 the_numbers_rung29 the_numbers_rung30 the_numbers_rung31 the_numbers_rung32 the_numbers_rung33 the_numbers_rung34 the_numbers_rung35

-- Episode13.lean, line 3000
--× deal_rung the_numbers_rung37 := ITS_YOU_!!
--×     FACT the_first_card this_way_to_the_number that_way_to_the_number the_first_card a_number_is_distinguished the_crossing_of_the_number the_numbers_rung02 the_numbers_rung03 the_numbers_rung04 the_numbers_rung05 the_numbers_rung06 the_numbers_rung07 the_numbers_rung08 the_numbers_rung09 the_numbers_rung10 the_numbers_rung11 the_numbers_rung12 the_numbers_rung13 the_numbers_rung14 the_numbers_rung15 the_numbers_rung16 the_numbers_rung17 the_numbers_rung18 the_numbers_rung19 the_numbers_rung20 the_numbers_rung21 the_numbers_rung22 the_numbers_rung23 the_numbers_rung24 the_numbers_rung25 the_numbers_rung26 the_numbers_rung27 the_numbers_rung28 the_numbers_rung29 the_numbers_rung30 the_numbers_rung31 the_numbers_rung32 the_numbers_rung33 the_numbers_rung34 the_numbers_rung35 the_numbers_rung36 True True

-- Episode13.lean, line 3003
--× deal_rung the_numbers_rung38 := HOW_ARE_YOU_GENTLEMEN_!!__ALL_YOUR_BASE_CASE_ARE_BELONG_TO_US
--×     FACT the_first_card this_way_to_the_number that_way_to_the_number the_first_card a_number_is_distinguished the_crossing_of_the_number the_numbers_rung02 the_numbers_rung03 the_numbers_rung04 the_numbers_rung05 the_numbers_rung06 the_numbers_rung07 the_numbers_rung08 the_numbers_rung09 the_numbers_rung10 the_numbers_rung11 the_numbers_rung12 the_numbers_rung13 the_numbers_rung14 the_numbers_rung15 the_numbers_rung16 the_numbers_rung17 the_numbers_rung18 the_numbers_rung19 the_numbers_rung20 the_numbers_rung21 the_numbers_rung22 the_numbers_rung23 the_numbers_rung24 the_numbers_rung25 the_numbers_rung26 the_numbers_rung27 the_numbers_rung28 the_numbers_rung29 the_numbers_rung30 the_numbers_rung31 the_numbers_rung32 the_numbers_rung33 the_numbers_rung34 the_numbers_rung35 the_numbers_rung36 the_quartic

-- Episode13.lean, line 3011
--× attribute [local instance high] the_crossing_of_the_number the_numbers_rung02 the_numbers_rung03 the_numbers_rung04 the_numbers_rung05 the_numbers_rung06 the_numbers_rung07 the_numbers_rung08 the_numbers_rung09 the_numbers_rung10 the_numbers_rung11 the_numbers_rung12 the_numbers_rung13 the_numbers_rung14 the_numbers_rung15 the_numbers_rung16 the_numbers_rung17 the_numbers_rung18 the_numbers_rung19 the_numbers_rung20 the_numbers_rung21 the_numbers_rung22 the_numbers_rung23 the_numbers_rung24 the_numbers_rung25 the_numbers_rung26 the_numbers_rung27 the_numbers_rung28 the_numbers_rung29 the_numbers_rung30 the_numbers_rung31 the_numbers_rung32 the_numbers_rung33 the_numbers_rung34 the_numbers_rung35 the_numbers_rung36

-- Episode13.lean, line 3016
--× theorem the_other_reader_is_on_the_quartic : the_numbers_rung38.you_the_reader.current_page_number = the_quartic := rfl
--× theorem the_other_page_is_one_past_the_card :
--×     the_numbers_rung38.you_the_reader.current_page_number.peano.length = bent_card + 1 := rfl

-- Episode13.lean, line 3021
--× noncomputable def the_other_conclusion : Closure := the_numbers_rung37.same_difference.your_conclusion
--× noncomputable def the_other_alpha : Closure := the_numbers_rung37.α
--× theorem the_other_conclusion_is_one_cell_and_the_other_alpha_three :
--×     the_other_conclusion.infer.length = 1 ∧ the_other_alpha.infer.length = 3 := ⟨rfl, rfl⟩

-- Episode13.lean, line 3029
--× theorem what_the_first_rung_says_comes_out_at_the_top :
--×     (∃ low slip slipped the_rest, the_other_alpha = .inferred a_number_is_distinguished a_number_is_distinguished low slip slipped the_rest)
--×       ∧ (∃ low slip slipped the_rest, the_alpha = .inferred FACT.Truth FACT.Truth low slip slipped the_rest) :=
--×   ⟨⟨_, _, _, _, rfl⟩, ⟨_, _, _, _, rfl⟩⟩

-- Episode13.lean, line 3035
--× theorem by_the_click_the_two_ladders_carry_one_account :
--×     the_other_conclusion.infer.map the_click = the_conclusion.infer.map the_click
--×       ∧ the_other_alpha.infer.map the_click = the_alpha.infer.map the_click := ⟨rfl, rfl⟩

-- Episode13.lean, line 3041
--× noncomputable def the_other_deck_one : CarrierProcess (CarrierProcess FACT) :=
--×   { symbol := a_number_is_distinguished, quarter := tapeNumber the_other_conclusion.infer }
--× noncomputable def the_other_deck_two : CarrierProcess (CarrierProcess FACT) :=
--×   { symbol := a_number_is_distinguished, quarter := tapeNumber the_other_alpha.infer }
--× theorem the_other_ladder_reads_the_number :
--×     bent_card.fenceposts_must_be_preserved Nat (read_past_quarter the_other_deck_one) all_possible_variables
--×         = arrange_the_information_appropriately
--×       ∧ bent_card.fenceposts_must_be_preserved Nat (read_past_quarter the_other_deck_two) all_possible_variables
--×         = arrange_the_information_appropriately := by
--×   constructor
--×   · rw [show read_past_quarter the_other_deck_one = List.length from funext (read_past_quarter_is_length _)]; rfl
--×   · rw [show read_past_quarter the_other_deck_two = List.length from funext (read_past_quarter_is_length _)]; rfl

-- Episode13.lean, line 3070
--× def the_upness   : Nat := bent_card
--× def the_distance : Nat := the_memory_tape.length
--× def the_time     : Nat := the_trace_of_truth_in_the_device
--× def the_limit    : Nat := the_dimensions_of_universe

-- Episode13.lean, line 3077
--× theorem the_distance_is_the_upness_and_the_limit :
--×     the_distance = the_upness + the_limit ∧ the_time = the_basis.the_reading.length * the_distance := by decide

-- Episode13.lean, line 3083
--× theorem the_energy_squared_is_the_mass_squared_and_the_momentum_squared :
--×     the_distance * the_distance = the_upness * the_distance + the_limit * the_distance
--×       ∧ the_arm_weight true false * the_arm_weight false true = the_limit * the_distance
--×       ∧ the_arm_weight true true * the_arm_weight false false - the_arm_weight true false * the_arm_weight false true
--×           = the_upness * the_distance := by decide

-- Episode13.lean, line 3091
--× theorem the_factor_squared_by_one_less_the_speed_squared_is_one :
--×     (the_distance * the_distance) * (the_distance * the_distance - the_limit * the_distance)
--×       = (the_upness * the_distance) * (the_distance * the_distance) := by decide

-- Episode13.lean, line 3097
--× theorem the_gain_is_the_factor_squared_over_the_speed_squared :
--×     (the_first_step_of_the_proof_is_to_eschew_the_naturals_unless_proven_to_exist_without_peano).1
--×         * ((the_upness * the_distance) * (the_limit * the_distance))
--×       = ((the_first_step_of_the_proof_is_to_eschew_the_naturals_unless_proven_to_exist_without_peano).2 * the_upness)
--×         * ((the_distance * the_distance) * (the_distance * the_distance)) := by decide

-- Episode13.lean, line 3107
--× theorem the_two_crossings_are_one_round_trip_shifted :
--×     the_arm_weight false true * the_limit = the_arm_weight true false * the_distance
--×       ∧ the_arm_weight false true - the_arm_weight true false = the_upness
--×       ∧ the_upness * (the_distance * the_distance + the_limit * the_distance)
--×           = (the_arm_weight false true + the_arm_weight true false) * (the_upness * the_distance) := by decide

-- Episode13.lean, line 3129
--× def the_same_table      : Table := fun a b => if a = b then 1 else 0
--× def the_different_table : Table := fun a b => if a = b then 0 else 1

-- Episode13.lean, line 3135
--× theorem in_the_mirror_it_is_the_same_the_sign_and_the_turn_owed :
--×     ∀ a b : Bool,
--×       the_table_product (the_table_product the_mirror the_full_table) the_mirror a b
--×         = (the_time : Int) * the_same_table a b
--×           + ((the_arm_weight true false + the_arm_weight false true : Nat) : Int) * the_sign_table a b
--×           - (the_upness : Int) * the_quarter_turn a b := by decide

-- Episode13.lean, line 3145
--× theorem a_turn_a_sign_and_they_do_not_commute :
--×     ∀ a b : Bool,
--×       the_table_product the_quarter_turn the_quarter_turn a b = - the_same_table a b
--×         ∧ the_table_product the_sign_table the_sign_table a b = the_same_table a b
--×         ∧ the_table_product the_sign_table the_quarter_turn a b = - the_table_product the_quarter_turn the_sign_table a b := by
--×   decide

-- Episode13.lean, line 3154
--× theorem the_charge_squared_less_the_phase_squared_is_the_gap_squared :
--×     (the_arm_weight true false + the_arm_weight false true) * (the_arm_weight true false + the_arm_weight false true)
--×         - the_upness * the_upness
--×       = 4 * (the_limit * the_distance) := by decide

-- Episode13.lean, line 3170
--× theorem two_marks_that_say_true_things_are_one_mark {Value : Type} {card : CarrierProcess Value}
--×     (this that : DISTINGUISHABLE Value card) (one_fact : this.fact = that.fact) (one_symbol : this.symbol = that.symbol)
--×     (one_distinct : this.distinct? = that.distinct?)
--×     (both_hold : ∀ s, this.different? s ∧ ∀ t, that.different? t) : this = that := by
--×   obtain ⟨f, s, d, q, n⟩ := this
--×   obtain ⟨g, t, e, r, m⟩ := that
--×   simp only at one_fact one_symbol one_distinct
--×   subst one_fact; subst one_symbol; subst one_distinct
--×   have one_claim : q = r := funext fun x => propext ⟨fun _ => (both_hold x).2 x, fun _ => (both_hold x).1⟩
--×   subst one_claim
--×   have one_decision : n = m := Subsingleton.elim _ _
--×   subst one_decision
--×   rfl

-- Episode13.lean, line 3184
--× theorem asked_only_whether_it_is_true_the_two_first_rungs_are_one : the_crossing_of_the_number = rung01 :=
--×   two_marks_that_say_true_things_are_one_mark _ _ asked_only_whether_it_is_true_the_number_is_the_truth rfl rfl
--×     (fun _ => ⟨the_count_has_a_root_and_the_reader_of_one_cell_has_none, fun _ => rfl⟩)

-- Episode13.lean, line 3193
--× @[local instance] noncomputable def a_model_on_any_first_rung : REAL FACT the_first_card := A_CAUSAL_THEORY FACT the_first_card
--× noncomputable def this_way_on_any_first_rung : LOCAL FACT the_first_card := A_SMOOTH_MODEL FACT the_first_card
--× noncomputable def that_way_on_any_first_rung : UNIVERSAL FACT the_first_card this_way_on_any_first_rung :=
--×   IS_IT_CONNECTED_BY_A_YARN? FACT the_first_card (nowtrino_model := this_way_on_any_first_rung)

-- Episode13.lean, line 3198
--× noncomputable def a_rung02 :=
--×   STEP2_DISCOVER_SOMETHING_DIFFERENT FACT the_first_card the_first_card (DISTINGUISHABLE.fact the_first_card) first

-- Episode13.lean, line 3201
--× noncomputable def a_rung03 :=
--×   STEP3_COUNT_THE_NUMBER_OF_THE_PHENOMENA FACT the_first_card the_first_card (DISTINGUISHABLE.fact the_first_card) first a_rung02

-- Episode13.lean, line 3204
--× noncomputable def a_rung04 :=
--×   STEP4_COMPUTE_THE_RATE_OF_PARTICLES FACT the_first_card the_first_card (DISTINGUISHABLE.fact the_first_card) first a_rung02 a_rung03

-- Episode13.lean, line 3207
--× noncomputable def a_rung05 :=
--×   STEP5_NAME_THE_RESIDUE_TO_COMPUTE_VALUE FACT the_first_card the_first_card (DISTINGUISHABLE.fact the_first_card) first a_rung02 a_rung03 a_rung04

-- Episode13.lean, line 3210
--× noncomputable def a_rung06 :=
--×   STEP6_MAKE_ANOTHER_COUNTER_OF_CLICKS_NOW FACT the_first_card the_first_card (DISTINGUISHABLE.fact the_first_card) first a_rung02 a_rung03 a_rung04 a_rung05

-- Episode13.lean, line 3213
--× noncomputable def a_rung07 :=
--×   STEP7_AND_SO_WE_CANT_COUNT_HOW_OFTEN_THE_METAPHOR_GOES_AROUND_JUST_LIKE_PITS_AND_LANDS_ON_A_CD FACT the_first_card the_first_card (DISTINGUISHABLE.fact the_first_card) first a_rung02 a_rung03 a_rung04 a_rung05 a_rung06

-- Episode13.lean, line 3216
--× noncomputable def a_rung08 :=
--×   STEP8_INTERPRET_THE_NEXT_3_SYMBOLS FACT the_first_card the_first_card (DISTINGUISHABLE.fact the_first_card) first a_rung02 a_rung03 a_rung04 a_rung05 a_rung06 a_rung07

-- Episode13.lean, line 3219
--× noncomputable def a_rung09 :=
--×   STEP9_NAME_THE_VARIABLES_CAREFULLY_TO_TELL_A_STORY FACT the_first_card the_first_card (DISTINGUISHABLE.fact the_first_card) first a_rung02 a_rung03 a_rung04 a_rung05 a_rung06 a_rung07 a_rung08

-- Episode13.lean, line 3222
--× noncomputable def a_rung10 :=
--×   STEP10_A_HALTING_COMPUTATION_IS_GIVEN_AS_INPUT_TO_A_NON_HALTING_FUNCTION FACT the_first_card the_first_card (DISTINGUISHABLE.fact the_first_card) first a_rung02 a_rung03 a_rung04 a_rung05 a_rung06 a_rung07 a_rung08 a_rung09

-- Episode13.lean, line 3225
--× deal_rung a_rung11 := STEP11_CHECK_FOR_CONVERGENCE_IN_THE_TIMESERIES_MATCHES_THE_MEASUREMENT_HIGH_ORDER_TERMS
--×     FACT the_first_card the_first_card (DISTINGUISHABLE.fact the_first_card) first a_rung02 a_rung03 a_rung04 a_rung05 a_rung06 a_rung07 a_rung08 a_rung09 a_rung10

-- Episode13.lean, line 3228
--× deal_rung a_rung12 := STEP12_CHECK_TO_SEE_IF_THE_BORWEIN_PROCESS_HAS_UNCOVERED_A_PROPERTY_OF_ELECTRONS
--×     FACT the_first_card the_first_card (DISTINGUISHABLE.fact the_first_card) first a_rung02 a_rung03 a_rung04 a_rung05 a_rung06 a_rung07 a_rung08 a_rung09 a_rung10 a_rung11

-- Episode13.lean, line 3231
--× deal_rung a_rung13 := STEP13_RECORD_THE_OBSERVATION_AS_A_MODELED_AST_AS_OF_RIGHT_NOW
--×     FACT the_first_card the_first_card (DISTINGUISHABLE.fact the_first_card) first a_rung02 a_rung03 a_rung04 a_rung05 a_rung06 a_rung07 a_rung08 a_rung09 a_rung10 a_rung11 a_rung12

-- Episode13.lean, line 3234
--× deal_rung a_rung14 := STEP14_REALIZE_THAT_THIS_PROCESS_TAKES_THE_APPARANT_SAME_AMOUNT_OF_TIME_EACH_TIME
--×     FACT the_first_card the_first_card (DISTINGUISHABLE.fact the_first_card) first a_rung02 a_rung03 a_rung04 a_rung05 a_rung06 a_rung07 a_rung08 a_rung09 a_rung10 a_rung11 a_rung12 a_rung13

-- Episode13.lean, line 3237
--× deal_rung a_rung15 := STEP15_SO_MODEL_THE_PROCESS_AS_SOMETHING_THAT_JUST_SPEWS_OUT_TRUE
--×     FACT the_first_card the_first_card (DISTINGUISHABLE.fact the_first_card) first a_rung02 a_rung03 a_rung04 a_rung05 a_rung06 a_rung07 a_rung08 a_rung09 a_rung10 a_rung11 a_rung12 a_rung13 a_rung14

-- Episode13.lean, line 3240
--× deal_rung a_rung16 := STEP16_VERIFY_THE_SOURCE_FILE_ONLY_EMITS_TRUE_STATEMENTS
--×     FACT the_first_card the_first_card (DISTINGUISHABLE.fact the_first_card) first a_rung02 a_rung03 a_rung04 a_rung05 a_rung06 a_rung07 a_rung08 a_rung09 a_rung10 a_rung11 a_rung12 a_rung13 a_rung14 a_rung15

-- Episode13.lean, line 3243
--× deal_rung a_rung17 := STEP17_MAKE_SURE_THIS_COMPILES_AND_DEMONSTRATES_IT_IS_TRUE_IN_GUNGAN
--×     FACT the_first_card the_first_card (DISTINGUISHABLE.fact the_first_card) first a_rung02 a_rung03 a_rung04 a_rung05 a_rung06 a_rung07 a_rung08 a_rung09 a_rung10 a_rung11 a_rung12 a_rung13 a_rung14 a_rung15 a_rung16

-- Episode13.lean, line 3246
--× deal_rung a_rung18 := STEP18_GIVEN_AN_INFERRED_DEFINITION_OF_THE_DEVICE_MAKE_THE_DEVICE
--×     FACT the_first_card the_first_card (DISTINGUISHABLE.fact the_first_card) first a_rung02 a_rung03 a_rung04 a_rung05 a_rung06 a_rung07 a_rung08 a_rung09 a_rung10 a_rung11 a_rung12 a_rung13 a_rung14 a_rung15 a_rung16 a_rung17

-- Episode13.lean, line 3249
--× deal_rung a_rung19 := STEP19_GIVEN_THE_ABILITY_TO_COUNT_SOMETHING_LEAN_CAN_NOW_INFER_ADDITION
--×     FACT the_first_card the_first_card (DISTINGUISHABLE.fact the_first_card) first a_rung02 a_rung03 a_rung04 a_rung05 a_rung06 a_rung07 a_rung08 a_rung09 a_rung10 a_rung11 a_rung12 a_rung13 a_rung14 a_rung15 a_rung16 a_rung17 a_rung18

-- Episode13.lean, line 3252
--× deal_rung a_rung20 := STEP20_DUPLICATE_THE_PROCESS_TO_DEMONSTRATE_AREA_OF_RECTANGLES_LIKE_EUCLID
--×     FACT the_first_card the_first_card (DISTINGUISHABLE.fact the_first_card) first a_rung02 a_rung03 a_rung04 a_rung05 a_rung06 a_rung07 a_rung08 a_rung09 a_rung10 a_rung11 a_rung12 a_rung13 a_rung14 a_rung15 a_rung16 a_rung17 a_rung18 a_rung19

-- Episode13.lean, line 3255
--× deal_rung a_rung21 := STEP21_GIVEN_ADDITION_MULTIPLICATION_AND_NUMBERS_INFER_ALL_OF_MATH
--×     FACT the_first_card the_first_card (DISTINGUISHABLE.fact the_first_card) first a_rung02 a_rung03 a_rung04 a_rung05 a_rung06 a_rung07 a_rung08 a_rung09 a_rung10 a_rung11 a_rung12 a_rung13 a_rung14 a_rung15 a_rung16 a_rung17 a_rung18 a_rung19 a_rung20

-- Episode13.lean, line 3258
--× deal_rung a_rung22 := STEP22_PAY_CLOSE_ATTENTION_TO_WEAK_SOLUTIONS_OF_DIFFERENTIAL_EQUATIONS_WHILE_DERIVING_MATH
--×     FACT the_first_card the_first_card (DISTINGUISHABLE.fact the_first_card) first a_rung02 a_rung03 a_rung04 a_rung05 a_rung06 a_rung07 a_rung08 a_rung09 a_rung10 a_rung11 a_rung12 a_rung13 a_rung14 a_rung15 a_rung16 a_rung17 a_rung18 a_rung19 a_rung20 a_rung21

-- Episode13.lean, line 3261
--× deal_rung a_rung23 := STEP23_GET_RID_OF_A_DERIVATIVE_SO_THAT_THE_SECOND_ORDER_MODEL_OF_THE_DEVICE_CAN_BE_WRITTEN_VARIATIONALLY
--×     FACT the_first_card the_first_card (DISTINGUISHABLE.fact the_first_card) first a_rung02 a_rung03 a_rung04 a_rung05 a_rung06 a_rung07 a_rung08 a_rung09 a_rung10 a_rung11 a_rung12 a_rung13 a_rung14 a_rung15 a_rung16 a_rung17 a_rung18 a_rung19 a_rung20 a_rung21 a_rung22

-- Episode13.lean, line 3264
--× deal_rung a_rung24 := STEP24_RESTATE_THE_MODEL_AS_A_PRINCIPLE_OF_LEAST_ACTION
--×     FACT the_first_card the_first_card (DISTINGUISHABLE.fact the_first_card) first a_rung02 a_rung03 a_rung04 a_rung05 a_rung06 a_rung07 a_rung08 a_rung09 a_rung10 a_rung11 a_rung12 a_rung13 a_rung14 a_rung15 a_rung16 a_rung17 a_rung18 a_rung19 a_rung20 a_rung21 a_rung22 a_rung23

-- Episode13.lean, line 3267
--× deal_rung a_rung25 := STEP25_BUILD_LOCAL_GEOMETRIES_THAT_SATISFY_THE_TRIANGLE_INEQUALITY
--×     FACT the_first_card the_first_card (DISTINGUISHABLE.fact the_first_card) first a_rung02 a_rung03 a_rung04 a_rung05 a_rung06 a_rung07 a_rung08 a_rung09 a_rung10 a_rung11 a_rung12 a_rung13 a_rung14 a_rung15 a_rung16 a_rung17 a_rung18 a_rung19 a_rung20 a_rung21 a_rung22 a_rung23 a_rung24

-- Episode13.lean, line 3270
--× deal_rung a_rung26 := STEP26_WRITE_YOUR_PROOF_IN_THE_FORMAL_LANGUAGE_OF_GEOMETRY
--×     FACT the_first_card the_first_card (DISTINGUISHABLE.fact the_first_card) first a_rung02 a_rung03 a_rung04 a_rung05 a_rung06 a_rung07 a_rung08 a_rung09 a_rung10 a_rung11 a_rung12 a_rung13 a_rung14 a_rung15 a_rung16 a_rung17 a_rung18 a_rung19 a_rung20 a_rung21 a_rung22 a_rung23 a_rung24 a_rung25

-- Episode13.lean, line 3273
--× deal_rung a_rung27 := STEP27_REPRESENT_THE_TAYLOR_SERIES_OF_THE_DEVICE
--×     FACT the_first_card the_first_card (DISTINGUISHABLE.fact the_first_card) first a_rung02 a_rung03 a_rung04 a_rung05 a_rung06 a_rung07 a_rung08 a_rung09 a_rung10 a_rung11 a_rung12 a_rung13 a_rung14 a_rung15 a_rung16 a_rung17 a_rung18 a_rung19 a_rung20 a_rung21 a_rung22 a_rung23 a_rung24 a_rung25 a_rung26

-- Episode13.lean, line 3276
--× deal_rung a_rung28 := STEP28_MAKE_SURE_YOUR_CURVES_ARE_SMOOTH_AS_A_DIFFERENTIALS_BOTTOM
--×     FACT the_first_card the_first_card (DISTINGUISHABLE.fact the_first_card) first a_rung02 a_rung03 a_rung04 a_rung05 a_rung06 a_rung07 a_rung08 a_rung09 a_rung10 a_rung11 a_rung12 a_rung13 a_rung14 a_rung15 a_rung16 a_rung17 a_rung18 a_rung19 a_rung20 a_rung21 a_rung22 a_rung23 a_rung24 a_rung25 a_rung26 a_rung27

-- Episode13.lean, line 3279
--× deal_rung a_rung29 := STEP29_SUGGEST_A_FALSIFIABLE_EXPERIMENT
--×     FACT the_first_card the_first_card (DISTINGUISHABLE.fact the_first_card) first a_rung02 a_rung03 a_rung04 a_rung05 a_rung06 a_rung07 a_rung08 a_rung09 a_rung10 a_rung11 a_rung12 a_rung13 a_rung14 a_rung15 a_rung16 a_rung17 a_rung18 a_rung19 a_rung20 a_rung21 a_rung22 a_rung23 a_rung24 a_rung25 a_rung26 a_rung27 a_rung28

-- Episode13.lean, line 3282
--× deal_rung a_rung30 := STEP30_PROVIDE_THE_EQUATIONS_THAT_WILL_PREDICT_THE_MEASUREMENT
--×     FACT the_first_card this_way_on_any_first_rung the_first_card (DISTINGUISHABLE.fact the_first_card) first a_rung02 a_rung03 a_rung04 a_rung05 a_rung06 a_rung07 a_rung08 a_rung09 a_rung10 a_rung11 a_rung12 a_rung13 a_rung14 a_rung15 a_rung16 a_rung17 a_rung18 a_rung19 a_rung20 a_rung21 a_rung22 a_rung23 a_rung24 a_rung25 a_rung26 a_rung27 a_rung28 a_rung29 (principia := this_way_on_any_first_rung)

-- Episode13.lean, line 3285
--× deal_rung a_rung31 := STEP31_GET_ON_THE_NEWTON_EINSTEIN_TRAIN_OF_THOUGHT
--×     FACT the_first_card this_way_on_any_first_rung that_way_on_any_first_rung the_first_card (DISTINGUISHABLE.fact the_first_card) first a_rung02 a_rung03 a_rung04 a_rung05 a_rung06 a_rung07 a_rung08 a_rung09 a_rung10 a_rung11 a_rung12 a_rung13 a_rung14 a_rung15 a_rung16 a_rung17 a_rung18 a_rung19 a_rung20 a_rung21 a_rung22 a_rung23 a_rung24 a_rung25 a_rung26 a_rung27 a_rung28 a_rung29 a_rung30 (the_a_train := that_way_on_any_first_rung)

-- Episode13.lean, line 3288
--× deal_rung a_rung32 := WHAT_HAPPEN_?
--×     FACT the_first_card this_way_on_any_first_rung that_way_on_any_first_rung the_first_card (DISTINGUISHABLE.fact the_first_card) first a_rung02 a_rung03 a_rung04 a_rung05 a_rung06 a_rung07 a_rung08 a_rung09 a_rung10 a_rung11 a_rung12 a_rung13 a_rung14 a_rung15 a_rung16 a_rung17 a_rung18 a_rung19 a_rung20 a_rung21 a_rung22 a_rung23 a_rung24 a_rung25 a_rung26 a_rung27 a_rung28 a_rung29 a_rung30 a_rung31

-- Episode13.lean, line 3291
--× deal_rung a_rung33 := SOMEBODY_SET_US_UP_THE_DEVICE
--×     FACT the_first_card this_way_on_any_first_rung that_way_on_any_first_rung the_first_card (DISTINGUISHABLE.fact the_first_card) first a_rung02 a_rung03 a_rung04 a_rung05 a_rung06 a_rung07 a_rung08 a_rung09 a_rung10 a_rung11 a_rung12 a_rung13 a_rung14 a_rung15 a_rung16 a_rung17 a_rung18 a_rung19 a_rung20 a_rung21 a_rung22 a_rung23 a_rung24 a_rung25 a_rung26 a_rung27 a_rung28 a_rung29 a_rung30 a_rung31 a_rung32

-- Episode13.lean, line 3294
--× deal_rung a_rung34 := WE_GET_SIGNAL
--×     FACT the_first_card this_way_on_any_first_rung that_way_on_any_first_rung the_first_card (DISTINGUISHABLE.fact the_first_card) first a_rung02 a_rung03 a_rung04 a_rung05 a_rung06 a_rung07 a_rung08 a_rung09 a_rung10 a_rung11 a_rung12 a_rung13 a_rung14 a_rung15 a_rung16 a_rung17 a_rung18 a_rung19 a_rung20 a_rung21 a_rung22 a_rung23 a_rung24 a_rung25 a_rung26 a_rung27 a_rung28 a_rung29 a_rung30 a_rung31 a_rung32 a_rung33

-- Episode13.lean, line 3297
--× deal_rung a_rung35 := WHAT_!
--×     FACT the_first_card this_way_on_any_first_rung that_way_on_any_first_rung the_first_card (DISTINGUISHABLE.fact the_first_card) first a_rung02 a_rung03 a_rung04 a_rung05 a_rung06 a_rung07 a_rung08 a_rung09 a_rung10 a_rung11 a_rung12 a_rung13 a_rung14 a_rung15 a_rung16 a_rung17 a_rung18 a_rung19 a_rung20 a_rung21 a_rung22 a_rung23 a_rung24 a_rung25 a_rung26 a_rung27 a_rung28 a_rung29 a_rung30 a_rung31 a_rung32 a_rung33 a_rung34

-- Episode13.lean, line 3300
--× deal_rung a_rung36 := MAIN_SCREEN_TURN_ON
--×     FACT the_first_card this_way_on_any_first_rung that_way_on_any_first_rung the_first_card (DISTINGUISHABLE.fact the_first_card) first a_rung02 a_rung03 a_rung04 a_rung05 a_rung06 a_rung07 a_rung08 a_rung09 a_rung10 a_rung11 a_rung12 a_rung13 a_rung14 a_rung15 a_rung16 a_rung17 a_rung18 a_rung19 a_rung20 a_rung21 a_rung22 a_rung23 a_rung24 a_rung25 a_rung26 a_rung27 a_rung28 a_rung29 a_rung30 a_rung31 a_rung32 a_rung33 a_rung34 a_rung35

-- Episode13.lean, line 3303
--× deal_rung a_rung37 := ITS_YOU_!!
--×     FACT the_first_card this_way_on_any_first_rung that_way_on_any_first_rung the_first_card (DISTINGUISHABLE.fact the_first_card) first a_rung02 a_rung03 a_rung04 a_rung05 a_rung06 a_rung07 a_rung08 a_rung09 a_rung10 a_rung11 a_rung12 a_rung13 a_rung14 a_rung15 a_rung16 a_rung17 a_rung18 a_rung19 a_rung20 a_rung21 a_rung22 a_rung23 a_rung24 a_rung25 a_rung26 a_rung27 a_rung28 a_rung29 a_rung30 a_rung31 a_rung32 a_rung33 a_rung34 a_rung35 a_rung36 True True

-- Episode13.lean, line 3306
--× deal_rung a_rung38 := HOW_ARE_YOU_GENTLEMEN_!!__ALL_YOUR_BASE_CASE_ARE_BELONG_TO_US
--×     FACT the_first_card this_way_on_any_first_rung that_way_on_any_first_rung the_first_card (DISTINGUISHABLE.fact the_first_card) first a_rung02 a_rung03 a_rung04 a_rung05 a_rung06 a_rung07 a_rung08 a_rung09 a_rung10 a_rung11 a_rung12 a_rung13 a_rung14 a_rung15 a_rung16 a_rung17 a_rung18 a_rung19 a_rung20 a_rung21 a_rung22 a_rung23 a_rung24 a_rung25 a_rung26 a_rung27 a_rung28 a_rung29 a_rung30 a_rung31 a_rung32 a_rung33 a_rung34 a_rung35 a_rung36 the_quartic

-- Episode13.lean, line 3309
--× attribute [local instance high] a_rung02 a_rung03 a_rung04 a_rung05 a_rung06 a_rung07 a_rung08 a_rung09 a_rung10 a_rung11 a_rung12 a_rung13 a_rung14 a_rung15 a_rung16 a_rung17 a_rung18 a_rung19 a_rung20 a_rung21 a_rung22 a_rung23 a_rung24 a_rung25 a_rung26 a_rung27 a_rung28 a_rung29 a_rung30 a_rung31 a_rung32 a_rung33 a_rung34 a_rung35 a_rung36
--× noncomputable def the_conclusion_on_any_first_rung : Closure := a_rung37.same_difference.your_conclusion
--× noncomputable def the_alpha_on_any_first_rung : Closure := a_rung37.α

-- Episode13.lean, line 3315
--× theorem the_ladder_on_the_old_rung_is_episode_twelves :
--×     @the_conclusion_on_any_first_rung rung01 instInhabitedProp = the_conclusion
--×       ∧ @the_alpha_on_any_first_rung rung01 instInhabitedProp = the_alpha := ⟨rfl, rfl⟩
--× theorem the_ladder_on_the_new_rung_is_the_other :
--×     @the_conclusion_on_any_first_rung the_crossing_of_the_number instInhabitedProp = the_other_conclusion
--×       ∧ @the_alpha_on_any_first_rung the_crossing_of_the_number instInhabitedProp = the_other_alpha := ⟨rfl, rfl⟩

-- Episode13.lean, line 3323
--× theorem one_first_rung_one_ladder (this that : DISTINGUISHABLE FACT the_first_card) (one_rung : this = that)
--×     (here : Inhabited (@DISTINGUISHABLE.symbol FACT the_first_card this))
--×     (there : Inhabited (@DISTINGUISHABLE.symbol FACT the_first_card that)) (one_inhabitant : HEq here there) :
--×     @the_conclusion_on_any_first_rung this here = @the_conclusion_on_any_first_rung that there
--×       ∧ @the_alpha_on_any_first_rung this here = @the_alpha_on_any_first_rung that there := by
--×   subst one_rung
--×   cases one_inhabitant
--×   exact ⟨rfl, rfl⟩

-- Episode13.lean, line 3332
--× theorem asked_only_whether_it_is_true_the_two_ladders_carry_the_same_closures :
--×     the_other_conclusion = the_conclusion ∧ the_other_alpha = the_alpha := by
--×   have one := one_first_rung_one_ladder _ _ asked_only_whether_it_is_true_the_two_first_rungs_are_one
--×     (instInhabitedProp : Inhabited (@DISTINGUISHABLE.symbol FACT the_first_card the_crossing_of_the_number))
--×     (instInhabitedProp : Inhabited (@DISTINGUISHABLE.symbol FACT the_first_card rung01)) HEq.rfl
--×   exact ⟨the_ladder_on_the_new_rung_is_the_other.1.symm.trans (one.1.trans the_ladder_on_the_old_rung_is_episode_twelves.1),
--×          the_ladder_on_the_new_rung_is_the_other.2.symm.trans (one.2.trans the_ladder_on_the_old_rung_is_episode_twelves.2)⟩

-- Episode13.lean, line 3345
--× attribute [local instance high] the_crossing_of_the_number the_numbers_rung02 the_numbers_rung03 the_numbers_rung04 the_numbers_rung05 the_numbers_rung06 the_numbers_rung07 the_numbers_rung08 the_numbers_rung09 the_numbers_rung10 the_numbers_rung11 the_numbers_rung12 the_numbers_rung13 the_numbers_rung14 the_numbers_rung15 the_numbers_rung16 the_numbers_rung17 the_numbers_rung18 the_numbers_rung19 the_numbers_rung20 the_numbers_rung21 the_numbers_rung22 the_numbers_rung23 the_numbers_rung24 the_numbers_rung25 the_numbers_rung26 the_numbers_rung27 the_numbers_rung28 the_numbers_rung29 the_numbers_rung30 the_numbers_rung31 the_numbers_rung32 the_numbers_rung33 the_numbers_rung34 the_numbers_rung35 the_numbers_rung36
--× theorem the_other_knower_reads_one_way_and_back :
--×     the_numbers_rung37.inferred? the_other_conclusion the_other_alpha
--×       ∧ the_numbers_rung37.inferred? the_other_alpha the_other_conclusion := by
--×   have one := asked_only_whether_it_is_true_the_two_ladders_carry_the_same_closures
--×   constructor
--×   · show Closure.le the_other_conclusion the_other_alpha
--×     rw [one.1, one.2]; exact the_knower_reads_one_way
--×   · show Closure.le the_other_alpha the_other_conclusion
--×     rw [one.1, one.2]; exact the_device_reads_it_back

-- Episode13.lean, line 3368
--× theorem the_universe_id_reads_the_level_and_its_zero : ∀ level : Nat, (the_universe_id level).peano.length = level + 1
--×   | 0 => rfl
--×   | level + 1 => by
--×     rw [the_universe_id_steps]
--×     show (the_universe_id level).peano.length + 1 = level + 1 + 1
--×     rw [the_universe_id_reads_the_level_and_its_zero level]

-- Episode13.lean, line 3377
--× theorem the_entropy_is_the_area (tape : List FACT) :
--×     (the_universe_id tape.length).peano.length = (the_number_of_marks tape).riemann_integrate.length := by
--×   rw [the_universe_id_reads_the_level_and_its_zero, the_riemann_sum_is_indistinguisahble_from_the_bent_card_with_an_extra_fencepost_of_blanks,
--×                                   the_number_of_marks_the_tapes_length]; rfl

-- Episode13.lean, line 3384
--× theorem one_more_fact_is_one_more_level_and_one_more_cell (fact : FACT) (tape : List FACT) :
--×     (the_universe_id (fact :: tape).length).peano.length = (the_universe_id tape.length).peano.length + 1
--×       ∧ compute_the_area_of (the_number_of_marks (fact :: tape)) = compute_the_area_of (the_area_of_a_tape_in_blanks_is tape) + 1 := by
--×   simp only [the_universe_id_reads_the_level_and_its_zero, the_number_of_marks_the_tapes_length, List.length_cons, and_self]

-- Episode13.lean, line 3389
--× theorem the_universe_ids_are_ordered_as_the_areas (this that : List FACT) :
--×     Number.le (the_universe_id this.length) (the_universe_id that.length)
--×       ↔ compute_the_area_of (the_number_of_marks this) ≤ compute_the_area_of (the_area_of_a_tape_in_blanks_is that) := by
--×   rw [the_ids_compare_as_naturals, the_number_of_marks_the_tapes_length, the_area_of_a_tape_in_blanks_is_the_tapes_length]

-- Episode13.lean, line 3407
--× def the_sum_from_above : Nat → Nat
--×   | 0         => 0
--×   | level + 1 => the_sum_from_above level + (the_universe_id level).peano.length
--× def the_sum_from_below : Nat → Nat
--×   | 0         => 0
--×   | level + 1 => the_sum_from_below level + ((the_universe_id level).peano.length - the_fencepost_bug)

-- Episode13.lean, line 3416
--× theorem twice_the_sum_from_above : ∀ levels : Nat, 2 * the_sum_from_above levels = levels * (levels + 1)
--×   | 0 => rfl
--×   | levels + 1 => by
--×     rw [the_sum_from_above, the_universe_id_reads_the_level_and_its_zero, Nat.mul_add, twice_the_sum_from_above levels,
--×       ← Nat.add_mul, Nat.mul_comm]

-- Episode13.lean, line 3422
--× theorem twice_the_sum_from_below : ∀ levels : Nat, 2 * the_sum_from_below (levels + 1) = levels * (levels + 1)
--×   | 0 => rfl
--×   | levels + 1 => by
--×     rw [the_sum_from_below, the_universe_id_reads_the_level_and_its_zero, Nat.mul_add, twice_the_sum_from_below levels]
--×     show levels * (levels + 1) + 2 * (levels + 1 + 1 - 1) = (levels + 1) * (levels + 1 + 1)
--×     rw [Nat.add_sub_cancel, ← Nat.add_mul, Nat.mul_comm]

-- Episode13.lean, line 3432
--× theorem the_area_is_between_the_two_sums (levels : Nat) :
--×     2 * the_sum_from_below (levels + 1) ≤ (levels + 1) * (levels + 1)
--×       ∧ (levels + 1) * (levels + 1) ≤ 2 * the_sum_from_above (levels + 1)
--×       ∧ the_sum_from_above (levels + 1) = the_sum_from_below (levels + 1) + (levels + 1) * the_fencepost_bug := by
--×   refine ⟨?_, ?_, ?_⟩
--×   · rw [twice_the_sum_from_below]; exact Nat.mul_le_mul_right _ (Nat.le_succ _)
--×   · rw [twice_the_sum_from_above]; exact Nat.mul_le_mul_left _ (Nat.le_succ _)
--×   · have above := twice_the_sum_from_above (levels + 1)
--×     have below := twice_the_sum_from_below levels
--×     have : 2 * the_sum_from_above (levels + 1) = 2 * (the_sum_from_below (levels + 1) + (levels + 1) * the_fencepost_bug) := by
--×       rw [above, Nat.mul_add 2 (the_sum_from_below (levels + 1)), below]
--×       show (levels + 1) * (levels + 1 + 1) = levels * (levels + 1) + 2 * ((levels + 1) * 1)
--×       rw [Nat.mul_one, ← Nat.add_mul, Nat.mul_comm]
--×     exact Nat.eq_of_mul_eq_mul_left (by decide) this

-- Episode13.lean, line 3460
--× theorem the_reading_is_carried_and_the_entropy_advances {Box : Type} {Pigeon : CarrierProcess Box} {rung : Nat} {Lifted : Type}
--×     (the_rebuttal : ThePreprint) (accepted : TYPESET Box Pigeon rung Lifted) :
--×     (set_in_type the_rebuttal accepted).register_value = ULift.up accepted.register_value
--×       ∧ (set_in_type the_rebuttal accepted).universe_id = .one Pigeon.symbol accepted.universe_id := ⟨rfl, rfl⟩

-- Episode13.lean, line 3466
--× theorem the_top_of_the_record_is_at_the_time :
--×     theTop.universe_id = the_universe_id 35 ∧ theTop.universe_id.peano.length = the_time := ⟨rfl, by decide⟩

-- Episode13.lean, line 3472
--× def the_heat_to_each_level : List Int := theLadderSizes
--× def the_reading_a_level    : List Int := theLadderSteps

-- Episode13.lean, line 3477
--× theorem every_level_costs : the_reading_a_level.length + 1 = the_time ∧ the_reading_a_level.all (fun heat => decide (0 < heat)) = true := by
--×   decide

-- Episode13.lean, line 3493
--× def the_acceleration_to : Nat → SpaceTimePath.{0}
--×   | 0         => .einstein FACT.Truth
--×   | level + 1 => .whitehole FACT.Truth FACT (the_acceleration_to level)

-- Episode13.lean, line 3498
--× theorem the_acceleration_reads_the_velocity_it_reaches : ∀ level : Nat,
--×     (the_acceleration_to level).stokes = (the_universe_id level).peano
--×   | 0 => rfl
--×   | level + 1 => by
--×     rw [the_universe_id_steps]
--×     show FACT.Truth :: (the_acceleration_to level).stokes = FACT.Truth :: (the_universe_id level).peano
--×     rw [the_acceleration_reads_the_velocity_it_reaches level]

-- Episode13.lean, line 3509
--× theorem a_white_hole_gives_a_fact_and_a_black_hole_gives_none :
--×     come_from_somewhere.stokes.length = going_somewhere.stokes.length + 1
--×       ∧ going_somewhere.stokes = the_path_here.stokes := ⟨rfl, rfl⟩

-- Episode13.lean, line 3515
--× theorem the_nowtrinos_path_reads_four : the_nowtrino_path.stokes.length = 4 := rfl

-- Episode13.lean, line 3530
--× def the_flux (tape : List FACT) : List FACT := (ComputerProgram.ofTape tape).read

-- Episode13.lean, line 3532
--× theorem the_flux_is_one_truth_a_fact : ∀ tape : List FACT, the_flux tape = List.replicate tape.length FACT.Truth
--×   | [] => rfl
--×   | fact :: rest => by
--×     show FACT.Truth :: the_flux rest = List.replicate (rest.length + 1) FACT.Truth
--×     rw [the_flux_is_one_truth_a_fact rest]; rfl

-- Episode13.lean, line 3540
--× theorem what_goes_in_comes_out (this that : List FACT) :
--×     (the_flux (this ++ that)).length = (the_flux this).length + (the_flux that).length := by
--×   simp only [the_flux_is_one_truth_a_fact, List.length_replicate, List.length_append]

-- Episode13.lean, line 3547
--× theorem in_cells_the_heat_is_the_entropy (tape : List FACT) :
--×     (the_flux tape).length + the_fencepost_bug = (the_universe_id tape.length).peano.length
--×       ∧ (the_flux tape).length + the_fencepost_bug = (the_table.the_number_of_marks tape).riemann_integrate.length := by
--×   refine ⟨?_, ?_⟩
--×   · rw [the_flux_is_one_truth_a_fact, List.length_replicate, the_universe_id_reads_the_level_and_its_zero]; rfl
--×   · rw [the_flux_is_one_truth_a_fact, List.length_replicate, the_table.the_riemann_sum_is_indistinguisahble_from_the_bent_card_with_an_extra_fencepost_of_blanks,
--×       the_table.the_number_of_marks_the_tapes_length]

-- Episode13.lean, line 3568
--× def the_temperature_at (level : Nat) : Area := the_number_of_marks (List.replicate (the_sum_from_above level) FACT.Truth)
--× def that_box_at (level : Nat) : PigeonHole :=
--×   .that_box FACT.Truth (the_temperature_at level) (the_temperature_at (level + 1))
--×     (.this_superpigeon FACT.Truth (the_temperature_at level)) (.this_superpigeon FACT.Truth (the_temperature_at (level + 1)))

-- Episode13.lean, line 3574
--× def the_first_variation : PigeonHole → Area
--×   | .that_box _ before after _ _ => after - before
--×   | .this_superpigeon fact _     => .tree fact
--×   | .a_pigeon fact _ _           => .tree fact

-- Episode13.lean, line 3582
--× theorem the_first_variation_of_the_temperature_is_the_velocity_reached (level : Nat) :
--×     compute_the_area_of (the_first_variation (that_box_at level)) = (the_acceleration_to level).stokes.length := by
--×   show compute_the_area_of (the_temperature_at (level + 1) - the_temperature_at level) = _
--×   rw [the_double_lift_subtracts, the_acceleration_reads_the_velocity_it_reaches]
--×   simp only [the_temperature_at, the_number_of_marks_the_tapes_length, List.length_replicate, the_sum_from_above,
--×     Nat.add_sub_cancel_left]

-- Episode13.lean, line 3590
--× def the_first_variation_of_the_reading : List Int :=
--×   List.zipWith (fun later earlier => later - earlier) the_reading_a_level.tail the_reading_a_level

-- Episode13.lean, line 3603
--× def the_jar_at (level : Nat) : Jar := .color FACT.Truth (the_temperature_at level)

-- Episode13.lean, line 3610
--× theorem every_jar_looks_the_same (level : Nat) : (the_jar_at level).classify = [FACT.Truth] := rfl

-- Episode13.lean, line 3615
--× theorem what_the_jar_holds_over_its_first_variation_is_half_the_level (level : Nat) :
--×     compute_the_area_of (what_the_jar_holds (the_jar_at level)) = the_sum_from_above level
--×       ∧ 2 * compute_the_area_of (what_the_jar_holds (the_jar_at level)) = level * compute_the_area_of (the_first_variation (that_box_at level)) := by
--×   have holds : compute_the_area_of (what_the_jar_holds (the_jar_at level)) = the_sum_from_above level := by
--×     show compute_the_area_of (the_temperature_at level) = _
--×     simp only [the_temperature_at, the_number_of_marks_the_tapes_length, List.length_replicate]
--×   refine ⟨holds, ?_⟩
--×   rw [holds, the_first_variation_of_the_temperature_is_the_velocity_reached, the_acceleration_reads_the_velocity_it_reaches,
--×     the_universe_id_reads_the_level_and_its_zero, twice_the_sum_from_above]

-- Episode13.lean, line 3638
--× theorem the_residue_is_the_fencepost (level : Nat) :
--×     compute_the_area_of (the_first_variation (that_box_at level)) = level + the_fencepost_bug
--×       ∧ 2 * compute_the_area_of (what_the_jar_holds (the_jar_at level)) = level * (level + the_fencepost_bug)
--×       ∧ compute_the_area_of (the_first_variation (that_box_at (level + 1))) = compute_the_area_of (the_first_variation (that_box_at level)) + the_fencepost_bug := by
--×   have variation : ∀ n, compute_the_area_of (the_first_variation (that_box_at n)) = n + 1 := fun n => by
--×     rw [the_first_variation_of_the_temperature_is_the_velocity_reached, the_acceleration_reads_the_velocity_it_reaches,
--×       the_universe_id_reads_the_level_and_its_zero]
--×   refine ⟨variation level, ?_, ?_⟩
--×   · rw [(what_the_jar_holds_over_its_first_variation_is_half_the_level level).2, variation]; rfl
--×   · rw [variation, variation]; rfl

-- Episode13.lean, line 3660
--× def the_action (rises : List Nat) : Nat := (rises.map fun rise => rise * rise).sum

-- Episode13.lean, line 3663
--× theorem twice_a_rise_is_not_over_its_square_and_one : ∀ rise : Nat, 2 * rise ≤ rise * rise + 1
--×   | 0 => Nat.zero_le _
--×   | 1 => by decide
--×   | rise + 2 => Nat.le_trans (Nat.mul_le_mul_right (rise + 2) (Nat.le_add_left 2 rise)) (Nat.le_add_right _ 1)

-- Episode13.lean, line 3669
--× theorem twice_the_rises_is_not_over_the_action_and_the_levels : ∀ rises : List Nat,
--×     2 * rises.sum ≤ the_action rises + rises.length
--×   | [] => Nat.le_refl _
--×   | rise :: rest => by
--×     have one := twice_a_rise_is_not_over_its_square_and_one rise
--×     have others := twice_the_rises_is_not_over_the_action_and_the_levels rest
--×     show 2 * (rise + rest.sum) ≤ (rise * rise + the_action rest) + (rest.length + 1)
--×     rw [Nat.mul_add]
--×     exact Nat.le_trans (Nat.add_le_add one others)
--×       (by rw [Nat.add_assoc, Nat.add_assoc, Nat.add_left_comm 1, Nat.add_comm 1 rest.length]; exact Nat.le_refl _)

-- Episode13.lean, line 3682
--× theorem with_the_ends_held_the_action_is_not_under_the_levels (rises : List Nat) (the_ends_are_held : rises.sum = rises.length) :
--×     rises.length ≤ the_action rises := by
--×   have bound := twice_the_rises_is_not_over_the_action_and_the_levels rises
--×   rw [the_ends_are_held, Nat.two_mul] at bound
--×   exact Nat.le_of_add_le_add_right bound

-- Episode13.lean, line 3689
--× def the_rise_at (level : Nat) : Nat :=
--×   (the_acceleration_to (level + 1)).stokes.length - (the_acceleration_to level).stokes.length
--× def the_rises_to : Nat → List Nat
--×   | 0         => []
--×   | level + 1 => the_rise_at level :: the_rises_to level

-- Episode13.lean, line 3698
--× theorem every_rise_is_the_fencepost (level : Nat) : the_rise_at level = the_fencepost_bug := by
--×   show (the_acceleration_to (level + 1)).stokes.length - (the_acceleration_to level).stokes.length = 1
--×   rw [the_acceleration_reads_the_velocity_it_reaches, the_acceleration_reads_the_velocity_it_reaches,
--×     the_universe_id_reads_the_level_and_its_zero, the_universe_id_reads_the_level_and_its_zero, Nat.add_sub_cancel_left]

-- Episode13.lean, line 3705
--× theorem the_devices_rises_hold_the_ends_and_are_the_least : ∀ levels : Nat,
--×     (the_rises_to levels).length = levels ∧ (the_rises_to levels).sum = levels ∧ the_action (the_rises_to levels) = levels
--×   | 0 => ⟨rfl, rfl, rfl⟩
--×   | levels + 1 => by
--×     have so_far := the_devices_rises_hold_the_ends_and_are_the_least levels
--×     refine ⟨?_, ?_, ?_⟩
--×     · show (the_rises_to levels).length + 1 = levels + 1
--×       rw [so_far.1]
--×     · show the_rise_at levels + (the_rises_to levels).sum = levels + 1
--×       rw [every_rise_is_the_fencepost, so_far.2.1, Nat.add_comm]; rfl
--×     · show the_rise_at levels * the_rise_at levels + the_action (the_rises_to levels) = levels + 1
--×       rw [every_rise_is_the_fencepost, so_far.2.2, Nat.add_comm]; rfl

-- Episode13.lean, line 3733
--× def the_velocity_at (level : Nat) : Nat := (the_universe_id level).peano.length - the_fencepost_bug
--× def the_velocities_to : Nat → List Nat
--×   | 0         => [the_velocity_at 0]
--×   | level + 1 => the_velocity_at (level + 1) :: the_velocities_to level

-- Episode13.lean, line 3738
--× theorem the_velocity_is_the_level (level : Nat) : the_velocity_at level = level := by
--×   show (the_universe_id level).peano.length - 1 = level
--×   rw [the_universe_id_reads_the_level_and_its_zero, Nat.add_sub_cancel]

-- Episode13.lean, line 3745
--× theorem the_temperature_is_the_average_velocity : ∀ level : Nat,
--×     (the_velocities_to level).sum = compute_the_area_of (what_the_jar_holds (the_jar_at level))
--×       ∧ (the_velocities_to level).length = compute_the_area_of (the_first_variation (that_box_at level))
--×       ∧ 2 * (the_velocities_to level).sum = level * (the_velocities_to level).length
--×   | 0 => ⟨rfl, rfl, rfl⟩
--×   | level + 1 => by
--×     have so_far := the_temperature_is_the_average_velocity level
--×     have holds := fun n => (what_the_jar_holds_over_its_first_variation_is_half_the_level n).1
--×     have varies := fun n => (the_residue_is_the_fencepost n).1
--×     have the_sum : (the_velocities_to (level + 1)).sum = compute_the_area_of (what_the_jar_holds (the_jar_at (level + 1))) := by
--×       show the_velocity_at (level + 1) + (the_velocities_to level).sum = _
--×       rw [so_far.1, holds, holds, the_velocity_is_the_level, the_sum_from_above,
--×         the_universe_id_reads_the_level_and_its_zero, Nat.add_comm]
--×     have the_count : (the_velocities_to (level + 1)).length = compute_the_area_of (the_first_variation (that_box_at (level + 1))) := by
--×       show (the_velocities_to level).length + 1 = _
--×       rw [so_far.2.1, varies, varies]; rfl
--×     refine ⟨the_sum, the_count, ?_⟩
--×     rw [the_sum, the_count]
--×     exact (what_the_jar_holds_over_its_first_variation_is_half_the_level (level + 1)).2

-- Episode13.lean, line 3769
--× theorem the_first_difference_is_the_derivative_and_a_polynomial (level : Nat) :
--×     2 * (the_sum_from_above (level + 2) - the_sum_from_above (level + 1))
--×       = (the_sum_from_above (level + 2) - the_sum_from_above level) + the_fencepost_bug := by
--×   have next : ∀ n, the_sum_from_above (n + 1) = the_sum_from_above n + (n + 1) := fun n => by
--×     rw [the_sum_from_above, the_universe_id_reads_the_level_and_its_zero]
--×   rw [next (level + 1), next level, Nat.add_sub_cancel_left,
--×     Nat.add_assoc (the_sum_from_above level), Nat.add_sub_cancel_left, Nat.two_mul]
--×   show (level + 2) + (level + 2) = (level + 1) + (level + 2) + 1
--×   rw [Nat.add_right_comm (level + 1) (level + 2) 1]

-- Episode13.lean, line 3805
--× theorem each_remainder_is_the_square_of_the_last :
--×     (the_arm_weight true false + the_arm_weight false true) * (the_arm_weight true false + the_arm_weight false true)
--×         = 4 * (the_arm_weight true false * the_arm_weight false true) + bent_card * bent_card
--×       ∧ ((the_arm_weight true false + the_arm_weight false true) * (the_arm_weight true false + the_arm_weight false true)
--×             + 4 * (the_arm_weight true false * the_arm_weight false true))
--×           * ((the_arm_weight true false + the_arm_weight false true) * (the_arm_weight true false + the_arm_weight false true)
--×             + 4 * (the_arm_weight true false * the_arm_weight false true))
--×         = 4 * (the_arm_weight true false * the_arm_weight false true)
--×             * ((2 * (the_arm_weight true false + the_arm_weight false true)) * (2 * (the_arm_weight true false + the_arm_weight false true)))
--×           + (bent_card * bent_card) * (bent_card * bent_card) := by decide

-- Episode13.lean, line 3830
--× def the_velocity_with (rise : Nat) : Nat → Nat
--×   | 0         => 0
--×   | level + 1 => the_velocity_with rise level + rise
--× def the_temperature_with (rise : Nat) : Nat → Nat
--×   | 0         => 0
--×   | level + 1 => the_temperature_with rise level + the_velocity_with rise (level + 1)

-- Episode13.lean, line 3837
--× theorem the_velocity_is_the_rise_by_the_level (rise : Nat) : ∀ level : Nat, the_velocity_with rise level = rise * level
--×   | 0 => rfl
--×   | level + 1 => by rw [the_velocity_with, the_velocity_is_the_rise_by_the_level rise level, Nat.mul_succ]

-- Episode13.lean, line 3844
--× theorem the_temperature_is_the_acceleration_by_the_area (rise : Nat) : ∀ level : Nat,
--×     the_temperature_with rise level = rise * the_sum_from_above level
--×   | 0 => rfl
--×   | level + 1 => by
--×     rw [the_temperature_with, the_temperature_is_the_acceleration_by_the_area rise level,
--×       the_velocity_is_the_rise_by_the_level, the_sum_from_above, the_universe_id_reads_the_level_and_its_zero]
--×     exact (Nat.mul_add _ _ _).symm

-- Episode13.lean, line 3852
--× theorem twice_the_temperature_is_the_rise_by_the_level_by_one_more (rise level : Nat) :
--×     2 * the_temperature_with rise level = rise * (level * (level + 1)) := by
--×   rw [the_temperature_is_the_acceleration_by_the_area, Nat.mul_left_comm, twice_the_sum_from_above]

-- Episode13.lean, line 3859
--× theorem the_temperature_and_the_acceleration_change_together (times rise level : Nat) :
--×     the_temperature_with (times * rise) level = times * the_temperature_with rise level := by
--×   rw [the_temperature_is_the_acceleration_by_the_area, the_temperature_is_the_acceleration_by_the_area, Nat.mul_assoc]

-- Episode13.lean, line 3863
--× theorem two_readers_one_proportion (this_rise that_rise level : Nat) :
--×     the_temperature_with this_rise level * that_rise = the_temperature_with that_rise level * this_rise := by
--×   rw [the_temperature_is_the_acceleration_by_the_area, the_temperature_is_the_acceleration_by_the_area,
--×     Nat.mul_right_comm this_rise, Nat.mul_right_comm that_rise, Nat.mul_comm this_rise that_rise]

-- Episode13.lean, line 3870
--× theorem on_the_device_the_rise_is_the_fencepost (level : Nat) :
--×     the_temperature_with the_fencepost_bug level = compute_the_area_of (what_the_jar_holds (the_jar_at level))
--×       ∧ the_velocity_with the_fencepost_bug level = the_velocity_at level
--×       ∧ the_rise_at level = the_fencepost_bug := by
--×   refine ⟨?_, ?_, every_rise_is_the_fencepost level⟩
--×   · rw [the_temperature_is_the_acceleration_by_the_area, (what_the_jar_holds_over_its_first_variation_is_half_the_level level).1]
--×     exact Nat.one_mul _
--×   · rw [the_velocity_is_the_rise_by_the_level, the_velocity_is_the_level]; exact Nat.one_mul _

-- Episode13.lean, line 3894
--× theorem the_relative_velocity_of_two_readers (this_rise that_rise level : Nat) :
--×     the_velocity_with this_rise level - the_velocity_with that_rise level = (this_rise - that_rise) * level := by
--×   rw [the_velocity_is_the_rise_by_the_level, the_velocity_is_the_rise_by_the_level, Nat.sub_mul]

-- Episode13.lean, line 3898
--× theorem the_frames_are_equivalent (this_rise that_rise level : Nat) :
--×     the_temperature_with this_rise level * that_rise = the_temperature_with that_rise level * this_rise
--×       ∧ the_velocity_with this_rise level * that_rise = the_velocity_with that_rise level * this_rise := by
--×   refine ⟨two_readers_one_proportion this_rise that_rise level, ?_⟩
--×   rw [the_velocity_is_the_rise_by_the_level, the_velocity_is_the_rise_by_the_level, Nat.mul_right_comm this_rise,
--×     Nat.mul_right_comm that_rise, Nat.mul_comm this_rise that_rise]

-- Episode13.lean, line 3918
--× theorem a_white_hole_is_asked_for_the_fact_and_a_black_hole_for_the_promise
--×     (idea happened : FACT) (promised : Prop) (rest : SpaceTimePath.{0}) :
--×     (SpaceTimePath.le (.einstein idea) (.whitehole happened FACT rest) = (idea = happened))
--×       ∧ (SpaceTimePath.le (.einstein idea) (.blackhole promised Type rest) = (idea.truth = promised)) := by
--×   constructor <;> simp only [SpaceTimePath.le]

-- Episode13.lean, line 3937
--× theorem the_path_nothing_takes :
--×     the_arm_stores_a_fact_that_can_click true false = false ∧ the_arm_weight true false = the_limit
--×       ∧ the_arm_stores_a_fact_that_can_click false true = true ∧ the_arm_weight false true = the_distance
--×       ∧ the_arm_weight true false * the_arm_weight false true = the_limit * the_distance := by decide

-- Episode13.lean, line 3944
--× theorem the_arm_out_is_short_by_the_residue :
--×     the_arm_weight false true = the_arm_weight true false + the_upness
--×       ∧ the_arm_weight true true = the_arm_weight true false + the_upness
--×       ∧ the_arm_weight false false = the_arm_weight true false + the_upness := by decide

-- Episode13.lean, line 3952
--× def the_promise_to_return : SpaceTimePath.{0} := .blackhole (true = false) Type the_path_here
--× theorem the_reader_gets_nothing_from_the_promise : the_promise_to_return.stokes = the_path_here.stokes := rfl

-- Episode13.lean, line 3963
--× theorem a_rise_that_meets_its_bound_is_one : ∀ rise : Nat, rise * rise + 1 = 2 * rise → rise = 1
--×   | 0, met => absurd met (by decide)
--×   | 1, _ => rfl
--×   | rise + 2, met =>
--×     absurd (met ▸ Nat.lt_succ_of_le (Nat.mul_le_mul_right (rise + 2) (Nat.le_add_left 2 rise))) (Nat.lt_irrefl _)

-- Episode13.lean, line 3969
--× theorem rises_that_meet_the_bound_are_all_one : ∀ rises : List Nat,
--×     2 * rises.sum = the_action rises + rises.length → ∀ rise, rise ∈ rises → rise = 1
--×   | [], _, _, here => nomatch here
--×   | first :: rest, met, rise, here => by
--×     have one := twice_a_rise_is_not_over_its_square_and_one first
--×     have others := twice_the_rises_is_not_over_the_action_and_the_levels rest
--×     have whole : 2 * (first + rest.sum) = (first * first + the_action rest) + (rest.length + 1) := met
--×     rw [Nat.mul_add] at whole
--×     have this_one : first * first + 1 = 2 * first := by omega
--×     have the_rest : 2 * rest.sum = the_action rest + rest.length := by omega
--×     cases here with
--×     | head => exact a_rise_that_meets_its_bound_is_one first this_one
--×     | tail _ further => exact rises_that_meet_the_bound_are_all_one rest the_rest rise further

-- Episode13.lean, line 3983
--× theorem only_the_fencepost_is_the_least (rises : List Nat) (the_ends_are_held : rises.sum = rises.length)
--×     (the_action_is_least : the_action rises = rises.length) : ∀ rise, rise ∈ rises → rise = the_fencepost_bug := by
--×   have met : 2 * rises.sum = the_action rises + rises.length := by
--×     rw [the_ends_are_held, the_action_is_least, Nat.two_mul]
--×   exact rises_that_meet_the_bound_are_all_one rises met

-- Episode13.lean, line 3998
--× theorem gibbs_and_boltzmann_are_one_ratio_turned_over (level : Nat) :
--×     2 * compute_the_area_of (what_the_jar_holds (the_jar_at level)) = level * compute_the_area_of (the_first_variation (that_box_at level))
--×       ∧ compute_the_area_of (the_first_variation (that_box_at level))
--×           = (level + the_fencepost_bug)
--×               * (compute_the_area_of (the_first_variation (that_box_at (level + 1))) - compute_the_area_of (the_first_variation (that_box_at level))) := by
--×   refine ⟨(what_the_jar_holds_over_its_first_variation_is_half_the_level level).2, ?_⟩
--×   rw [(the_residue_is_the_fencepost level).2.2, Nat.add_sub_cancel_left, (the_residue_is_the_fencepost level).1]
--×   exact (Nat.mul_one _).symm

-- Episode13.lean, line 4024
--× theorem the_equation_of_state_on_the_count (this_rise that_rise level : Nat) (this that : List FACT) :
--×     the_temperature_with this_rise level = this_rise * the_sum_from_above level
--×       ∧ the_temperature_with this_rise level * that_rise = the_temperature_with that_rise level * this_rise
--×       ∧ (the_flux (this ++ that)).length = (the_flux this).length + (the_flux that).length
--×       ∧ (the_flux this).length + the_fencepost_bug = (the_universe_id this.length).peano.length
--×       ∧ (the_universe_id this.length).peano.length = (the_number_of_marks this).riemann_integrate.length :=
--×   ⟨the_temperature_is_the_acceleration_by_the_area this_rise level, two_readers_one_proportion this_rise that_rise level,
--×    what_goes_in_comes_out this that, (in_cells_the_heat_is_the_entropy this).1, the_entropy_is_the_area this⟩

-- Episode13.lean, line 4049
--× theorem the_second_variation_of_the_temperature_is_the_acceleration (rise level : Nat) :
--×     (the_temperature_with rise (level + 2) - the_temperature_with rise (level + 1))
--×       - (the_temperature_with rise (level + 1) - the_temperature_with rise level) = rise := by
--×   show (the_temperature_with rise (level + 1) + (the_velocity_with rise (level + 1) + rise) - the_temperature_with rise (level + 1))
--×       - (the_temperature_with rise level + the_velocity_with rise (level + 1) - the_temperature_with rise level) = rise
--×   omega

-- Episode13.lean, line 4058
--× theorem the_curvature_does_not_step (rise level : Nat) :
--×     (the_temperature_with rise (level + 3) - the_temperature_with rise (level + 2))
--×         - (the_temperature_with rise (level + 2) - the_temperature_with rise (level + 1))
--×       = (the_temperature_with rise (level + 2) - the_temperature_with rise (level + 1))
--×         - (the_temperature_with rise (level + 1) - the_temperature_with rise level) := by
--×   rw [the_second_variation_of_the_temperature_is_the_acceleration rise (level + 1),
--×       the_second_variation_of_the_temperature_is_the_acceleration rise level]

-- Episode13.lean, line 4074
--× def the_zero_of_the_experience : Number := another_zero
--× def the_zero_of_the_interpretation : Number := Number.zero SAME_DIFFERENCE
--× def the_zero_of_the_clock : Number := Number.zero (bitFACT true)
--× def the_zero_of_the_other_clock : Number := Number.zero (bitFACT false)
--× def the_four_zeros : List Number :=
--×   [the_zero_of_the_experience, the_zero_of_the_interpretation, the_zero_of_the_clock, the_zero_of_the_other_clock]

-- Episode13.lean, line 4082
--× theorem a_zero_is_under_every_number (fact : FACT) (number : Number) : Number.le (.zero fact) number := by
--×   cases number <;> trivial
--× theorem every_zero_reads_one_cell :
--×     the_four_zeros.map (fun zero => zero.peano.length) = [1, 1, 1, 1] := rfl

-- Episode13.lean, line 4088
--× theorem the_zero_of_the_experience_is_the_first_universe_and_the_clocks :
--×     the_zero_of_the_experience = the_universe_id 0 ∧ the_zero_of_the_experience = the_zero_of_the_clock := ⟨rfl, rfl⟩

-- Episode13.lean, line 4092
--× theorem the_two_clocks_zeros_are_under_each_other_and_are_not_one :
--×     Number.le the_zero_of_the_clock the_zero_of_the_other_clock
--×       ∧ Number.le the_zero_of_the_other_clock the_zero_of_the_clock
--×       ∧ the_zero_of_the_clock ≠ the_zero_of_the_other_clock := by
--×   refine ⟨trivial, trivial, ?_⟩
--×   intro h; injection h with h
--×   exact absurd (congrArg (fun f : FACT => @decide f.truth f.click) h) (by decide)

-- Episode13.lean, line 4101
--× theorem asked_only_whether_it_is_true_the_interpretations_zero_is_the_experiences :
--×     the_zero_of_the_interpretation = the_zero_of_the_experience :=
--×   congrArg Number.zero (two_facts_that_are_true_are_one_fact SAME_DIFFERENCE FACT.Truth same_difference_clicks
--×     (@of_decide_eq_true FACT.Truth.truth FACT.Truth.click rfl))

-- Episode13.lean, line 4117
--× theorem the_metric_is_three_one_way_and_one_the_other :
--×     the_arms.map (fun arm => the_metric_on_the_arms arm arm) = [1, -1, 1, 1] := by decide

-- Episode13.lean, line 4125
--× abbrev is_null (direction : Direction → Int) : Prop := along the_metric_on_the_arms direction = 0

-- Episode13.lean, line 4129
--× def out_and (space : Direction) (way : Int) : Direction → Int :=
--×   fun arm => if arm = (true, false) then 1 else if arm = space then way else 0
--× def five_three_four (first second : Direction) : Direction → Int :=
--×   fun arm => if arm = (true, false) then 5 else if arm = first then 3 else if arm = second then 4 else 0
--× def the_null_directions : List (Direction → Int) :=
--×   [out_and (true, true) 1, out_and (true, true) (-1), out_and (false, true) 1, out_and (false, true) (-1),
--×    out_and (false, false) 1, out_and (false, false) (-1),
--×    five_three_four (true, true) (false, true), five_three_four (true, true) (false, false),
--×    five_three_four (false, true) (false, false)]

-- Episode13.lean, line 4139
--× theorem these_directions_are_null : ∀ direction ∈ the_null_directions, is_null direction := by decide

-- Episode13.lean, line 4143
--× theorem a_table_that_reads_nothing_along_the_null_directions_is_the_metric_by_a_number
--×     (table : Direction → Direction → Int) (symmetric : ∀ this that, table this that = table that this)
--×     (nothing : ∀ direction ∈ the_null_directions, along table direction = 0) :
--×     ∀ this that, table this that = - table (true, false) (true, false) * the_metric_on_the_arms this that := by
--×   have s1 := symmetric (true, false) (true, true)
--×   have s2 := symmetric (true, false) (false, true)
--×   have s3 := symmetric (true, false) (false, false)
--×   have s4 := symmetric (true, true) (false, true)
--×   have s5 := symmetric (true, true) (false, false)
--×   have s6 := symmetric (false, true) (false, false)
--×   have n1 := nothing (out_and (true, true) 1) (by simp [the_null_directions])
--×   have n2 := nothing (out_and (true, true) (-1)) (by simp [the_null_directions])
--×   have n3 := nothing (out_and (false, true) 1) (by simp [the_null_directions])
--×   have n4 := nothing (out_and (false, true) (-1)) (by simp [the_null_directions])
--×   have n5 := nothing (out_and (false, false) 1) (by simp [the_null_directions])
--×   have n6 := nothing (out_and (false, false) (-1)) (by simp [the_null_directions])
--×   have n7 := nothing (five_three_four (true, true) (false, true)) (by simp [the_null_directions])
--×   have n8 := nothing (five_three_four (true, true) (false, false)) (by simp [the_null_directions])
--×   have n9 := nothing (five_three_four (false, true) (false, false)) (by simp [the_null_directions])
--×   simp [along, the_arms, out_and, five_three_four] at n1 n2 n3 n4 n5 n6 n7 n8 n9
--×   intro this that
--×   obtain ⟨a, b⟩ := this; obtain ⟨c, d⟩ := that
--×   cases a <;> cases b <;> cases c <;> cases d <;>
--×     simp [the_metric_on_the_arms, the_arm_stores_a_fact_that_can_click] <;> omega

-- Episode13.lean, line 4173
--× theorem the_curl_differenced_around_three_directions_is_nothing {n : Nat} (A : Direction → Site4 n → Int)
--×     (first second third : Direction) (x : Site4 n) :
--×     the_difference first (the_curl_on A second third) x + the_difference second (the_curl_on A third first) x
--×       + the_difference third (the_curl_on A first second) x = 0 := by
--×   simp only [the_difference, the_curl_on]
--×   rw [the_steps_commute first second x, the_steps_commute first third x, the_steps_commute second third x]
--×   omega

-- Episode13.lean, line 4185
--× theorem along_a_difference (this that : Direction → Direction → Int) (direction : Direction → Int) :
--×     along (fun a b => this a b - that a b) direction = along this direction - along that direction := by
--×   simp only [along, the_arms, List.map, List.sum_cons, List.sum_nil, Int.sub_mul]; omega

-- Episode13.lean, line 4192
--× def the_number_left_free (source curvature : Direction → Direction → Int) : Int :=
--×   curvature (true, false) (true, false) - source (true, false) (true, false)

-- Episode13.lean, line 4195
--× theorem the_equation_on_the_arms (source curvature : Direction → Direction → Int)
--×     (the_source_is_symmetric : ∀ this that, source this that = source that this)
--×     (the_curvature_is_symmetric : ∀ this that, curvature this that = curvature that this)
--×     (for_every_observer : ∀ direction ∈ the_null_directions, along source direction = along curvature direction) :
--×     ∀ this that, source this that
--×       = curvature this that + the_number_left_free source curvature * the_metric_on_the_arms this that := by
--×   intro this that
--×   have h := a_table_that_reads_nothing_along_the_null_directions_is_the_metric_by_a_number
--×     (fun a b => source a b - curvature a b)
--×     (fun a b => by show source a b - curvature a b = source b a - curvature b a
--×                    rw [the_source_is_symmetric a b, the_curvature_is_symmetric a b])
--×     (fun direction member => by rw [along_a_difference, for_every_observer direction member]; omega) this that
--×   have e : - (source (true, false) (true, false) - curvature (true, false) (true, false))
--×       = the_number_left_free source curvature := by simp only [the_number_left_free]; omega
--×   rw [e] at h; omega

-- Episode13.lean, line 4213
--× theorem the_equation_on_the_torus {n : Nat} (source curvature : Site4 n → Direction → Direction → Int)
--×     (the_source_is_symmetric : ∀ x this that, source x this that = source x that this)
--×     (the_curvature_is_symmetric : ∀ x this that, curvature x this that = curvature x that this)
--×     (for_every_observer : ∀ x, ∀ direction ∈ the_null_directions, along (source x) direction = along (curvature x) direction) :
--×     ∀ x this that, source x this that
--×       = curvature x this that + the_number_left_free (source x) (curvature x) * the_metric_on_the_arms this that :=
--×   fun x => the_equation_on_the_arms (source x) (curvature x) (the_source_is_symmetric x) (the_curvature_is_symmetric x)
--×     (for_every_observer x)

-- Episode13.lean, line 4222
--× theorem where_neither_table_steps_the_number_does_not_step {n : Nat} (source curvature : Site4 n → Direction → Direction → Int)
--×     (way : Direction) (x : Site4 n)
--×     (the_source_does_not_step : source (the_step way x) = source x)
--×     (the_curvature_does_not_step : curvature (the_step way x) = curvature x) :
--×     the_number_left_free (source (the_step way x)) (curvature (the_step way x))
--×       = the_number_left_free (source x) (curvature x) := by
--×   rw [the_source_does_not_step, the_curvature_does_not_step]

-- Episode13.lean, line 4249
--× def the_turn : Table := fun a b => the_full_other_table a b - the_full_table a b
--× def the_square_turned_by (rise : Int) : Table :=
--×   the_holonomy (the_varied_table the_full_table the_turn rise) the_full_table the_full_table the_full_table
--× def what_one_whole_turn_shows : Table := the_holonomy the_turn the_full_table the_full_table the_full_table

-- Episode13.lean, line 4254
--× theorem the_square_curves_by_the_rise (rise : Int) (a b : Bool) :
--×     the_square_turned_by rise a b = the_scaled_identity (234 * 234) a b + rise * what_one_whole_turn_shows a b := by
--×   rw [the_square_turned_by, the_holonomy_is_linear_in_its_bottom_link, ← the_uniform_square_is_flat]; rfl

-- Episode13.lean, line 4258
--× theorem off_the_diagonal_the_square_shows_the_rise_and_nothing_else (rise : Int) :
--×     the_square_turned_by rise true false = rise * what_one_whole_turn_shows true false
--×       ∧ the_square_turned_by rise false true = rise * what_one_whole_turn_shows false true := by
--×   constructor <;> rw [the_square_curves_by_the_rise] <;> simp [the_scaled_identity]

-- Episode13.lean, line 4263
--× theorem a_whole_turn_is_the_other_table_and_it_shows_something :
--×     (∀ a b, the_varied_table the_full_table the_turn 1 a b = the_full_other_table a b)
--×       ∧ what_one_whole_turn_shows true false ≠ 0 := by
--×   constructor
--×   · intro a b; simp only [the_varied_table, the_turn]; omega
--×   · decide

-- Episode13.lean, line 4278
--× def on_the_arm_out (this that : Direction) : Int := if this = (true, false) ∧ that = (true, false) then 1 else 0

-- Episode13.lean, line 4280
--× theorem the_source_is_five_and_three_eighteens :
--×     the_arms.map (fun arm => the_source_on_the_arms arm arm) = [18, 5, 18, 18] := by decide

-- Episode13.lean, line 4284
--× theorem the_source_is_the_distance_by_the_metric_and_the_different_on_the_arm_out :
--×     ∀ this ∈ the_arms, ∀ that ∈ the_arms,
--×       the_source_on_the_arms this that = 18 * the_metric_on_the_arms this that + 23 * on_the_arm_out this that := by decide

-- Episode13.lean, line 4290
--× def the_curvature_on_the_count (rise : Int) (this that : Direction) : Int := if this = that then rise else 0

-- Episode13.lean, line 4295
--× theorem along_the_null_directions_twice_the_source_reads_as_twenty_three_curvatures :
--×     ∀ direction ∈ the_null_directions,
--×       along the_source_on_the_arms direction = 23 * (direction (true, false) * direction (true, false))
--×         ∧ along (the_curvature_on_the_count 1) direction = 2 * (direction (true, false) * direction (true, false))
--×         ∧ 2 * along the_source_on_the_arms direction = 23 * along (the_curvature_on_the_count 1) direction := by decide

-- Episode13.lean, line 4302
--× theorem twice_the_source_is_the_curvatures_and_the_bent_card_by_the_metric :
--×     ∀ this ∈ the_arms, ∀ that ∈ the_arms,
--×       2 * the_source_on_the_arms this that
--×         = 23 * the_curvature_on_the_count 1 this that + (bent_card : Int) * the_metric_on_the_arms this that := by decide

-- Episode13.lean, line 4309
--× theorem any_such_table_is_its_half_sum_and_its_half_difference_by_the_metric (out others : Int) :
--×     ∀ this ∈ the_arms, ∀ that ∈ the_arms,
--×       2 * (if this = that then (if this = (true, false) then out else others) else 0)
--×         = (others + out) * the_curvature_on_the_count 1 this that + (others - out) * the_metric_on_the_arms this that := by
--×   intro this h1 that h2
--×   simp only [the_arms, List.mem_cons, List.mem_nil_iff, or_false] at h1 h2
--×   rcases h1 with rfl | rfl | rfl | rfl <;> rcases h2 with rfl | rfl | rfl | rfl <;>
--×     simp [the_curvature_on_the_count, the_metric_on_the_arms, the_arm_stores_a_fact_that_can_click] <;> omega

-- Episode13.lean, line 4333
--× def the_curvature_of {n : Nat} (A : Direction → Site4 n → Int) (this that : Direction) (x : Site4 n) : Int :=
--×   the_difference this (A that) x

-- Episode13.lean, line 4336
--× theorem the_table_differs_from_itself_turned_over_by_the_curl {n : Nat} (A : Direction → Site4 n → Int)
--×     (this that : Direction) (x : Site4 n) :
--×     the_curvature_of A this that x - the_curvature_of A that this x = the_curl_on A this that x := rfl

-- Episode13.lean, line 4340
--× theorem the_table_of_a_gradient_is_symmetric {n : Nat} (f : Site4 n → Int) (this that : Direction) (x : Site4 n) :
--×     the_curvature_of (the_gradient f) this that x = the_curvature_of (the_gradient f) that this x := by
--×   have h := the_curl_of_a_gradient_is_nothing f this that x
--×   rw [← the_table_differs_from_itself_turned_over_by_the_curl] at h; omega

-- Episode13.lean, line 4348
--× def the_place_along {n : Nat} (arm : Direction) (x : Site4 n) : Nat :=
--×   if arm.1 then (if arm.2 then x.2.2.val else x.2.1.val) else (if arm.2 then x.1.2.val else x.1.1.val)
--× def the_area_at {n : Nat} (rise : Direction → Int) (x : Site4 n) : Int :=
--×   (the_arms.map fun arm => rise arm * (the_temperature_with 1 (the_place_along arm x) : Int)).sum

-- Episode13.lean, line 4353
--× theorem a_step_inside_is_one_more {n : Nat} (a : Fin (n+1)) (inside : a.val + 1 ≤ n) : (a + 1).val = a.val + 1 := by
--×   rw [Fin.val_add]
--×   have h1 : (1 : Fin (n+1)).val = 1 % (n+1) := rfl
--×   rw [h1, Nat.mod_eq_of_lt (by omega : 1 < n + 1), Nat.mod_eq_of_lt (by omega)]

-- Episode13.lean, line 4358
--× theorem the_second_difference_is_one_cell (level : Nat) :
--×     ((the_temperature_with 1 (level + 2) : Nat) : Int) - (the_temperature_with 1 (level + 1) : Nat)
--×       - ((the_temperature_with 1 (level + 1) : Nat) - (the_temperature_with 1 level : Nat)) = 1 := by
--×   show (((the_temperature_with 1 (level + 1) + (the_velocity_with 1 (level + 1) + 1) : Nat)) : Int) - _
--×     - ((((the_temperature_with 1 level + the_velocity_with 1 (level + 1) : Nat)) : Int) - _) = 1
--×   omega

-- Episode13.lean, line 4367
--× theorem the_curvature_of_an_area_is_its_rises {n : Nat} (rise : Direction → Int) (x : Site4 n)
--×     (inside : ∀ arm ∈ the_arms, the_place_along arm x + 2 ≤ n) (this that : Direction) :
--×     the_curvature_of (the_gradient (the_area_at rise)) this that x = if this = that then rise this else 0 := by
--×   obtain ⟨⟨a, b⟩, ⟨c, d⟩⟩ := x
--×   have ha := inside (false, false) (by simp [the_arms])
--×   have hb := inside (false, true) (by simp [the_arms])
--×   have hc := inside (true, false) (by simp [the_arms])
--×   have hd := inside (true, true) (by simp [the_arms])
--×   simp [the_place_along] at ha hb hc hd
--×   have ta := the_second_difference_is_one_cell a.val; have tb := the_second_difference_is_one_cell b.val
--×   have tc := the_second_difference_is_one_cell c.val; have td := the_second_difference_is_one_cell d.val
--×   have ea := a_step_inside_is_one_more a (by omega); have ea2 := a_step_inside_is_one_more (a+1) (by omega)
--×   have eb := a_step_inside_is_one_more b (by omega); have eb2 := a_step_inside_is_one_more (b+1) (by omega)
--×   have ec := a_step_inside_is_one_more c (by omega); have ec2 := a_step_inside_is_one_more (c+1) (by omega)
--×   have ed := a_step_inside_is_one_more d (by omega); have ed2 := a_step_inside_is_one_more (d+1) (by omega)
--×   rw [ea, Nat.add_assoc] at ea2; rw [eb, Nat.add_assoc] at eb2; rw [ec, Nat.add_assoc] at ec2; rw [ed, Nat.add_assoc] at ed2
--×   have ka := congrArg (fun z => rise (false, false) * z) ta
--×   have kb := congrArg (fun z => rise (false, true) * z) tb
--×   have kc := congrArg (fun z => rise (true, false) * z) tc
--×   have kd := congrArg (fun z => rise (true, true) * z) td
--×   simp only [Int.mul_sub, Int.mul_one] at ka kb kc kd
--×   obtain ⟨p, q⟩ := this; obtain ⟨r, s⟩ := that
--×   cases p <;> cases q <;> cases r <;> cases s <;>
--×     simp only [the_curvature_of, the_gradient, the_difference, the_step, the_area_at, the_arms, the_place_along,
--×       List.map, List.sum_cons, List.sum_nil, ea, eb, ec, ed, ea2, eb2, ec2, ed2, if_true, if_false, Bool.false_eq_true,
--×       Prod.mk.injEq, and_self, and_false, false_and, Bool.true_eq_false, Nat.reduceAdd] <;>
--×     omega

-- Episode13.lean, line 4397
--× def the_rise_the_arm_stores (arm : Direction) : Int := (the_arm_weight arm.1 arm.2 : Int)
--× def one_fencepost_on_every_arm (_ : Direction) : Int := 1
--× def the_rise_by_the_click (arm : Direction) : Int := the_metric_on_the_arms arm arm

-- Episode13.lean, line 4401
--× theorem three_areas_three_tables {n : Nat} (x : Site4 n) (inside : ∀ arm ∈ the_arms, the_place_along arm x + 2 ≤ n)
--×     (this that : Direction) :
--×     the_curvature_of (the_gradient (the_area_at the_rise_the_arm_stores)) this that x = the_source_on_the_arms this that
--×       ∧ the_curvature_of (the_gradient (the_area_at one_fencepost_on_every_arm)) this that x
--×           = the_curvature_on_the_count 1 this that
--×       ∧ the_curvature_of (the_gradient (the_area_at the_rise_by_the_click)) this that x
--×           = the_metric_on_the_arms this that := by
--×   refine ⟨?_, ?_, ?_⟩ <;> rw [the_curvature_of_an_area_is_its_rises _ x inside]
--×   · rfl
--×   · rfl
--×   · simp only [the_rise_by_the_click, the_metric_on_the_arms]; split <;> simp_all

-- Episode13.lean, line 4417
--× theorem three_areas_three_constants :
--×     (∀ direction ∈ the_null_directions,
--×         along the_source_on_the_arms direction = along the_source_on_the_arms direction + 0 * along the_metric_on_the_arms direction)
--×       ∧ (∀ this ∈ the_arms, ∀ that ∈ the_arms, 2 * the_source_on_the_arms this that
--×             = 23 * the_curvature_on_the_count 1 this that + (bent_card : Int) * the_metric_on_the_arms this that)
--×       ∧ (along the_metric_on_the_arms (out_and (true, true) 1) = 0
--×             ∧ along the_source_on_the_arms (out_and (true, true) 1) = 23) := by
--×   refine ⟨fun _ _ => by omega, twice_the_source_is_the_curvatures_and_the_bent_card_by_the_metric, by decide⟩

-- Episode13.lean, line 4438
--× def the_field_of {n : Nat} (A : Direction → Site4 n → Int) (this that : Direction) (x : Site4 n) : Int :=
--×   the_curvature_of A this that x - the_curvature_of A that this x

-- Episode13.lean, line 4441
--× theorem the_field_is_the_curl {n : Nat} (A : Direction → Site4 n → Int) (this that : Direction) (x : Site4 n) :
--×     the_field_of A this that x = the_curl_on A this that x := rfl

-- Episode13.lean, line 4444
--× theorem the_field_turned_over_is_the_field_owed {n : Nat} (A : Direction → Site4 n → Int) (this that : Direction) (x : Site4 n) :
--×     the_field_of A that this x = - the_field_of A this that x := by simp only [the_field_of]; omega

-- Episode13.lean, line 4448
--× theorem the_table_less_itself_turned_over_is_the_bent_card_by_the_quarter_turn (a b : Bool) :
--×     the_full_table a b - the_full_other_table a b = (bent_card : Int) * the_quarter_turn a b := by
--×   cases a <;> cases b <;> decide

-- Episode13.lean, line 4454
--× theorem owed_both_ways_is_nothing (t s p q : Int) (owed : s = - t) : t * p * q + s * q * p = 0 := by
--×   subst owed; rw [Int.neg_mul, Int.neg_mul, Int.mul_right_comm]; omega

-- Episode13.lean, line 4457
--× theorem a_table_owed_when_turned_over_reads_nothing_along_any_direction
--×     (table : Direction → Direction → Int) (owed : ∀ this that, table that this = - table this that)
--×     (direction : Direction → Int) : along table direction = 0 := by
--×   have d (arm : Direction) : table arm arm * direction arm * direction arm = 0 := by
--×     have h := owed arm arm
--×     have z : table arm arm = 0 := by omega
--×     rw [z, Int.zero_mul, Int.zero_mul]
--×   have p (this that : Direction) := owed_both_ways_is_nothing (table this that) (table that this) (direction this)
--×     (direction that) (owed this that)
--×   have d1 := d (true, true); have d2 := d (true, false); have d3 := d (false, true); have d4 := d (false, false)
--×   have p1 := p (true, true) (true, false); have p2 := p (true, true) (false, true); have p3 := p (true, true) (false, false)
--×   have p4 := p (true, false) (false, true); have p5 := p (true, false) (false, false); have p6 := p (false, true) (false, false)
--×   simp only [along, the_arms, List.map, List.sum_cons, List.sum_nil]
--×   omega

-- Episode13.lean, line 4473
--× theorem a_gradient_does_not_move_the_field {n : Nat} (A : Direction → Site4 n → Int) (f : Site4 n → Int)
--×     (this that : Direction) (x : Site4 n) :
--×     the_field_of (fun arm site => A arm site + the_gradient f arm site) this that x = the_field_of A this that x := by
--×   simp only [the_field_of, the_curvature_of, the_gradient, the_difference]
--×   rw [the_steps_commute this that x]; omega

-- Episode13.lean, line 4480
--× def the_current_of {n : Nat} (A : Direction → Site4 n → Int) (that : Direction) (x : Site4 n) : Int :=
--×   (the_arms.map fun this => the_metric_on_the_arms this this * the_metric_on_the_arms that that
--×     * the_difference this (the_field_of A this that) x).sum

-- Episode13.lean, line 4485
--× theorem the_current_is_conserved {n : Nat} (A : Direction → Site4 n → Int) (x : Site4 n) :
--×     (the_arms.map fun that => the_difference that (the_current_of A that) x).sum = 0 := by
--×   have g1 : the_metric_on_the_arms (true, true) (true, true) = 1 := by decide
--×   have g2 : the_metric_on_the_arms (true, false) (true, false) = -1 := by decide
--×   have g3 : the_metric_on_the_arms (false, true) (false, true) = 1 := by decide
--×   have g4 : the_metric_on_the_arms (false, false) (false, false) = 1 := by decide
--×   simp only [the_current_of, the_field_of, the_curvature_of, the_difference, the_arms, List.map, List.sum_cons, List.sum_nil,
--×     g1, g2, g3, g4]
--×   rw [the_steps_commute (true, true) (true, false) x, the_steps_commute (true, true) (false, true) x,
--×       the_steps_commute (true, true) (false, false) x, the_steps_commute (true, false) (false, true) x,
--×       the_steps_commute (true, false) (false, false) x, the_steps_commute (false, true) (false, false) x]
--×   omega

-- Episode13.lean, line 4513
--× theorem one_is_one_more_cell (fact : FACT) (number : Number) :
--×     (Number.one fact number).peano.length = number.peano.length + 1 := rfl

-- Episode13.lean, line 4517
--× theorem one_is_one_more_level (level : Nat) :
--×     the_universe_id (level + 1) = Number.one FACT.Truth (the_universe_id level) := the_universe_id_steps level

-- Episode13.lean, line 4521
--× theorem one_is_one_more_rise (level : Nat) :
--×     the_velocity_with 1 (level + 1) = the_velocity_with 1 level + 1
--×       ∧ the_temperature_with 1 (level + 1) = the_temperature_with 1 level + the_velocity_with 1 (level + 1) := ⟨rfl, rfl⟩

-- Episode13.lean, line 4526
--× theorem one_is_the_fencepost (level : Nat) :
--×     (the_universe_id level).peano.length = level + the_fencepost_bug ∧ the_fencepost_bug = 1 :=
--×   ⟨the_universe_id_reads_the_level_and_its_zero level, rfl⟩

-- Episode13.lean, line 4532
--× theorem the_four_ones_are_one_step (level : Nat) :
--×     (the_universe_id (level + 1)).peano.length = (the_universe_id level).peano.length + 1
--×       ∧ the_universe_id (level + 1) = Number.one FACT.Truth (the_universe_id level)
--×       ∧ the_velocity_with 1 (level + 1) = the_velocity_with 1 level + 1
--×       ∧ (the_universe_id level).peano.length = the_velocity_with 1 level + the_fencepost_bug := by
--×   refine ⟨?_, the_universe_id_steps level, rfl, ?_⟩
--×   · rw [the_universe_id_steps]; rfl
--×   · rw [the_universe_id_reads_the_level_and_its_zero, the_velocity_is_the_rise_by_the_level, Nat.one_mul]; rfl

-- Episode13.lean, line 4555
--× def the_trace_of {n : Nat} (f : Site4 n → Int) (x : Site4 n) : Int :=
--×   (the_arms.map fun arm => the_metric_on_the_arms arm arm * the_curvature_of (the_gradient f) arm arm x).sum
--× def the_divergence_of {n : Nat} (f : Site4 n → Int) (that : Direction) (x : Site4 n) : Int :=
--×   (the_arms.map fun this => the_metric_on_the_arms this this
--×     * the_difference this (the_curvature_of (the_gradient f) this that) x).sum

-- Episode13.lean, line 4561
--× theorem the_divergence_of_the_curvature_is_the_difference_of_its_trace {n : Nat} (f : Site4 n → Int)
--×     (that : Direction) (x : Site4 n) :
--×     the_divergence_of f that x = the_difference that (the_trace_of f) x := by
--×   have g1 : the_metric_on_the_arms (true, true) (true, true) = 1 := by decide
--×   have g2 : the_metric_on_the_arms (true, false) (true, false) = -1 := by decide
--×   have g3 : the_metric_on_the_arms (false, true) (false, true) = 1 := by decide
--×   have g4 : the_metric_on_the_arms (false, false) (false, false) = 1 := by decide
--×   obtain ⟨p, q⟩ := that
--×   cases p <;> cases q <;>
--×     simp only [the_divergence_of, the_trace_of, the_curvature_of, the_gradient, the_difference, the_arms, List.map,
--×       List.sum_cons, List.sum_nil, g1, g2, g3, g4,
--×       the_steps_commute (true, true) (true, false), the_steps_commute (true, true) (false, true),
--×       the_steps_commute (true, true) (false, false), the_steps_commute (true, false) (false, true),
--×       the_steps_commute (true, false) (false, false), the_steps_commute (false, true) (false, false)] <;>
--×     omega

-- Episode13.lean, line 4605
--× theorem without_the_link_it_is_not :
--×     the_turns_product (the_turns_conjugate (the_turns_product the_quarter_turn_turn (the_whole_turn 1))) (the_whole_turn 1)
--×       ≠ the_turns_product (the_turns_conjugate (the_whole_turn 1)) (the_whole_turn 1) := by decide

-- Episode13.lean, line 4616
--× theorem the_number_and_the_trace_do_not_step {n : Nat} (f : Site4 n → Int)
--×     (source : Site4 n → Direction → Direction → Int) (number : Site4 n → Int)
--×     (the_equation : ∀ x this that, source x this that
--×       = the_curvature_of (the_gradient f) this that x + number x * the_metric_on_the_arms this that)
--×     (conserved : ∀ that x, (the_arms.map fun this => the_metric_on_the_arms this this
--×       * (source (the_step this x) this that - source x this that)).sum = 0)
--×     (that : Direction) (x : Site4 n) :
--×     the_difference that (fun y => number y + the_trace_of f y) x = 0 := by
--×   have h := conserved that x
--×   have d := the_divergence_of_the_curvature_is_the_difference_of_its_trace f that x
--×   obtain ⟨p, q⟩ := that
--×   cases p <;> cases q <;>
--×     simp [the_equation, the_divergence_of, the_difference, the_arms, the_metric_on_the_arms,
--×       the_arm_stores_a_fact_that_can_click] at h d ⊢ <;>
--×     omega

-- Episode13.lean, line 4634
--× theorem the_equation_with_its_constant {n : Nat} (f : Site4 n → Int)
--×     (source : Site4 n → Direction → Direction → Int) (number : Site4 n → Int)
--×     (the_equation : ∀ x this that, source x this that
--×       = the_curvature_of (the_gradient f) this that x + number x * the_metric_on_the_arms this that)
--×     (conserved : ∀ that x, (the_arms.map fun this => the_metric_on_the_arms this this
--×       * (source (the_step this x) this that - source x this that)).sum = 0) :
--×     (∀ x this that, source x this that
--×         = the_curvature_of (the_gradient f) this that x - the_trace_of f x * the_metric_on_the_arms this that
--×           + (number x + the_trace_of f x) * the_metric_on_the_arms this that)
--×       ∧ (∀ way x, number (the_step way x) + the_trace_of f (the_step way x) = number x + the_trace_of f x) := by
--×   constructor
--×   · intro x this that; rw [the_equation, Int.add_mul]; omega
--×   · intro way x
--×     have h := the_number_and_the_trace_do_not_step f source number the_equation conserved way x
--×     simp only [the_difference] at h; omega

-- Episode13.lean, line 4653
--× theorem the_field_equation_on_the_torus {n : Nat} (f : Site4 n → Int)
--×     (source : Site4 n → Direction → Direction → Int)
--×     (the_source_is_symmetric : ∀ x this that, source x this that = source x that this)
--×     (for_every_observer : ∀ x, ∀ direction ∈ the_null_directions,
--×       along (source x) direction = along (fun this that => the_curvature_of (the_gradient f) this that x) direction)
--×     (conserved : ∀ that x, (the_arms.map fun this => the_metric_on_the_arms this this
--×       * (source (the_step this x) this that - source x this that)).sum = 0) :
--×     ∃ constant : Site4 n → Int,
--×       (∀ way x, constant (the_step way x) = constant x)
--×         ∧ ∀ x this that, source x this that
--×             = the_curvature_of (the_gradient f) this that x - the_trace_of f x * the_metric_on_the_arms this that
--×               + constant x * the_metric_on_the_arms this that := by
--×   have the_equation := the_equation_on_the_torus source (fun x this that => the_curvature_of (the_gradient f) this that x)
--×     the_source_is_symmetric (fun x this that => the_table_of_a_gradient_is_symmetric f this that x) for_every_observer
--×   have both := the_equation_with_its_constant f source
--×     (fun x => the_number_left_free (source x) (fun this that => the_curvature_of (the_gradient f) this that x))
--×     the_equation conserved
--×   exact ⟨fun x => the_number_left_free (source x) (fun this that => the_curvature_of (the_gradient f) this that x)
--×     + the_trace_of f x, both.2, both.1⟩

-- Episode13.lean, line 4692
--× theorem the_curvature_across_is_owed_when_a_pair_is_turned_over (table : Direction → Direction → Int) (a b c d : Direction) :
--×     the_curvature_across table b a c d = - the_curvature_across table a b c d
--×       ∧ the_curvature_across table a b d c = - the_curvature_across table a b c d := by
--×   simp only [the_curvature_across]; constructor <;> ac_nf <;> omega

-- Episode13.lean, line 4697
--× theorem the_curvature_across_is_the_same_when_the_pairs_change_places (table : Direction → Direction → Int)
--×     (symmetric : ∀ this that, table this that = table that this) (a b c d : Direction) :
--×     the_curvature_across table c d a b = the_curvature_across table a b c d := by
--×   simp only [the_curvature_across, symmetric c a, symmetric d b, symmetric c b, symmetric d a]
--×   rw [Int.mul_comm (table b c)]

-- Episode13.lean, line 4703
--× theorem the_curvature_across_around_three_is_nothing (table : Direction → Direction → Int)
--×     (symmetric : ∀ this that, table this that = table that this) (a b c d : Direction) :
--×     the_curvature_across table a b c d + the_curvature_across table a c d b + the_curvature_across table a d b c = 0 := by
--×   simp only [the_curvature_across, symmetric c b, symmetric d c, symmetric b d]; ac_nf; omega

-- Episode13.lean, line 4713
--× theorem a_squares_curvature_is_its_two_rises (rise : Direction → Int) (a b : Direction) (two_arms : a ≠ b) :
--×     the_curvature_across (fun this that => if this = that then rise this else 0) a b a b = rise a * rise b := by
--×   simp [the_curvature_across, two_arms, Ne.symm two_arms]

-- Episode13.lean, line 4719
--× theorem the_squares_of_the_source :
--×     the_curvature_across the_source_on_the_arms (true, false) (true, true) (true, false) (true, true) = 90
--×       ∧ the_curvature_across the_source_on_the_arms (true, true) (false, true) (true, true) (false, true) = 324 := by decide

-- Episode13.lean, line 4726
--× theorem the_contraction_of_one_fencepost_is_three_and_three_ones :
--×     ∀ b ∈ the_arms, ∀ d ∈ the_arms,
--×       the_contraction_of (the_curvature_on_the_count 1) b d
--×         = if b = d then (if b = (true, false) then 3 else 1) else 0 := by decide

-- Episode13.lean, line 4732
--× theorem the_contraction_of_the_metric_is_three_metrics :
--×     ∀ b ∈ the_arms, ∀ d ∈ the_arms,
--×       the_contraction_of the_metric_on_the_arms b d = 3 * the_metric_on_the_arms b d := by decide

-- Episode13.lean, line 4738
--× theorem four_sources_read_as_twenty_three_contractions :
--×     ∀ direction ∈ the_null_directions,
--×       4 * along the_source_on_the_arms direction = 23 * along (the_contraction_of (the_curvature_on_the_count 1)) direction := by
--×   decide

-- Episode13.lean, line 4763
--× noncomputable def the_counting : CountingProcess FACT the_first_card := ADMISSIBLE.counting_process
--× noncomputable def the_indexing : IndexingProcess FACT the_first_card := COUNTABLE.index

-- Episode13.lean, line 4768
--× theorem the_carriers_step_twice_is_once (number : Number) :
--×     the_first_card.interact_with_the_universe (the_first_card.interact_with_the_universe number)
--×       = the_first_card.interact_with_the_universe number := by cases number <;> rfl
--× def the_carriers_two : FACT :=
--×   { truth := ∀ number : Number, the_first_card.interact_with_the_universe (the_first_card.interact_with_the_universe number)
--×       = the_first_card.interact_with_the_universe number
--×     click := .isTrue the_carriers_step_twice_is_once }

-- Episode13.lean, line 4777
--× theorem the_counters_step_is_the_count_and_one_more (fact : FACT) (label : Number) (so_far : Natural) :
--×     ∃ (the_fact : FACT), the_counting.iterate (Natural.number fact label so_far)
--×       = Natural.number the_fact the_counting.palmed_card.quarter the_counting.count := ⟨_, rfl⟩
--× def the_counters_two : FACT :=
--×   { truth := ∀ (fact : FACT) (label : Number) (so_far : Natural), ∃ (the_fact : FACT),
--×       the_counting.iterate (Natural.number fact label so_far)
--×         = Natural.number the_fact the_counting.palmed_card.quarter the_counting.count
--×     click := .isTrue the_counters_step_is_the_count_and_one_more }

-- Episode13.lean, line 4788
--× theorem the_indexers_step_is_the_first_or_the_next (fact : FACT) (index : Natural) (rest : Rational) :
--×     the_indexing.iterate (Rational.zero fact) = Rational.number fact the_indexing.count.count the_indexing.origin
--×       ∧ the_indexing.iterate (Rational.number fact index rest)
--×           = Rational.number fact (the_indexing.count.iterate index) the_indexing.origin := ⟨rfl, rfl⟩
--× def the_indexers_two : FACT :=
--×   { truth := ∀ (fact : FACT) (index : Natural) (rest : Rational),
--×       the_indexing.iterate (Rational.zero fact) = Rational.number fact the_indexing.count.count the_indexing.origin
--×         ∧ the_indexing.iterate (Rational.number fact index rest)
--×             = Rational.number fact (the_indexing.count.iterate index) the_indexing.origin
--×     click := .isTrue the_indexers_step_is_the_first_or_the_next }

-- Episode13.lean, line 4800
--× def the_inferred_two : Bullshit.{0,0,0,0} := .zero the_carriers_two
--× def the_counted_two : Bullshit.{0,0,0,0} := .zero the_counters_two
--× def the_indexed_two : Bullshit.{0,0,0,0} := .zero the_indexers_two

-- Episode13.lean, line 4806
--× noncomputable def the_equivalence_of_the_twos :=
--×   { the_knower_of_the_experience.same_difference with
--×     your_conclusion := .different the_first_card.symbol the_inferred_two the_counted_two (some the_carriers_two.truth) }

-- Episode13.lean, line 4812
--× noncomputable def the_inferred_against_the_counted : Closure :=
--×   the_equivalence_of_the_twos.{0,0,0,0,0,0,0,0,0,0,0,0}.do_you_believe_it? the_inferred_two the_counted_two
--× noncomputable def the_inferred_against_the_indexed : Closure :=
--×   the_equivalence_of_the_twos.{0,0,0,0,0,0,0,0,0,0,0,0}.do_you_believe_it? the_inferred_two the_indexed_two

-- Episode13.lean, line 4818
--× theorem three_twos_three_cells :
--×     the_equivalence_of_the_twos.{0,0,0,0,0,0,0,0,0,0,0,0}.your_conclusion.infer.length = 1
--×       ∧ the_inferred_against_the_counted.infer.length = 1
--×       ∧ the_inferred_against_the_indexed.infer.length = 1 := ⟨rfl, rfl, rfl⟩

-- Episode13.lean, line 4824
--× theorem the_three_twos_click :
--×     the_carriers_two.truth ∧ the_counters_two.truth ∧ the_indexers_two.truth :=
--×   ⟨the_carriers_step_twice_is_once, the_counters_step_is_the_count_and_one_more, the_indexers_step_is_the_first_or_the_next⟩

-- Episode13.lean, line 4834
--× theorem the_difference_of_a_product {n : Nat} (f g : Site4 n → Int) (way : Direction) (x : Site4 n) :
--×     the_difference way (fun y => f y * g y) x
--×       = f x * the_difference way g x + g x * the_difference way f x + the_difference way f x * the_difference way g x := by
--×   simp only [the_difference, Int.mul_sub, Int.sub_mul]; ac_nf; omega

-- Episode13.lean, line 4900
--× theorem the_carrier_process_is_the_one_held : the_carrier_process = the_carrier_process_held := rfl

-- Episode13.lean, line 4904
--× theorem the_counting_process_is_the_one_held : the_counting_process = the_counting_process_held := rfl

-- Episode13.lean, line 4908
--× theorem the_indexing_process_is_the_one_held : the_indexing_process = the_indexing_process_held := rfl

-- Episode13.lean, line 4913
--× theorem the_limit_process_is_the_one_held : the_limit_process = the_limit_process_held := rfl

-- Episode13.lean, line 4918
--× theorem the_cauchy_process_is_the_one_held : the_cauchy_process = the_cauchy_process_held := rfl

-- Episode13.lean, line 4923
--× theorem the_observation_process_is_the_one_held : the_observation_process = the_observation_process_held := rfl

-- Episode13.lean, line 4928
--× theorem the_repeatable_process_is_the_one_held : the_repeatable_process = the_repeatable_process_held := rfl

-- Episode13.lean, line 4935
--× theorem the_computational_process_is_the_one_held : the_computational_process = the_computational_process_held := rfl

-- Episode13.lean, line 4940
--× theorem the_turing_process_is_the_one_held : the_turing_process = the_turing_process_held := rfl

-- Episode13.lean, line 4944
--× theorem the_noisy_process_is_the_one_held : the_noisy_process = the_noisy_process_held := rfl

-- Episode13.lean, line 4950
--× theorem the_physical_process_is_the_one_held : the_physical_process = the_physical_process_held := rfl

-- Episode13.lean, line 4956
--× theorem the_slip_process_is_the_one_held : the_slip_process = the_slip_process_held := rfl

-- Episode13.lean, line 4960
--× theorem the_sensing_process_is_the_one_held : the_sensing_process = the_sensing_process_held := rfl

-- Episode13.lean, line 4964
--× theorem the_gauge_process_is_the_one_held : the_gauge_process = the_gauge_process_held := rfl

-- Episode13.lean, line 4968
--× theorem the_meesa_process_is_the_one_held : the_meesa_process = the_meesa_process_held := rfl

-- Episode13.lean, line 4972
--× theorem the_digital_process_is_the_one_held : the_digital_process = the_digital_process_held := rfl

-- Episode13.lean, line 4977
--× theorem the_compiled_process_is_the_one_held : the_compiled_process = the_compiled_process_held := rfl

-- Episode13.lean, line 4981
--× theorem the_mathematical_process_is_the_one_held : the_mathematical_process = the_mathematical_process_held := rfl

-- Episode13.lean, line 4986
--× theorem the_adding_process_is_the_one_held : the_adding_process = the_adding_process_held := rfl

-- Episode13.lean, line 4991
--× theorem the_multiplying_process_is_the_one_held : the_multiplying_process = the_multiplying_process_held := rfl

-- Episode13.lean, line 4996
--× theorem the_basic_process_is_the_one_held : the_basic_process = the_basic_process_held := rfl

-- Episode13.lean, line 5000
--× theorem the_jordan_process_is_the_one_held : the_jordan_process = the_jordan_process_held := rfl

-- Episode13.lean, line 5004
--× theorem the_arm_wave_process_is_the_one_held : the_arm_wave_process = the_arm_wave_process_held := rfl

-- Episode13.lean, line 5008
--× theorem the_crusade_process_is_the_one_held : the_crusade_process = the_crusade_process_held := rfl

-- Episode13.lean, line 5012
--× theorem the_initiation_process_is_the_one_held : the_initiation_process = the_initiation_process_held := rfl

-- Episode13.lean, line 5017
--× theorem the_learning_process_is_the_one_held : the_learning_process = the_learning_process_held := rfl

-- Episode13.lean, line 5021
--× theorem the_scientific_process_is_the_one_held : the_scientific_process = the_scientific_process_held := rfl

-- Episode13.lean, line 5025
--× theorem the_religious_process_is_the_one_held : the_religious_process = the_religious_process_held := rfl

-- Episode13.lean, line 5029
--× theorem the_universe_tensor_is_the_one_held : the_universe_tensor = the_universe_tensor_held := rfl

-- Episode13.lean, line 5033
--× theorem the_big_red_dog_process_is_the_one_held : the_big_red_dog_process = the_big_red_dog_process_held := rfl

-- Episode13.lean, line 5039
--× theorem the_calculus_process_is_the_one_held : the_calculus_process = the_calculus_process_held := rfl

-- Episode13.lean, line 5044
--× theorem the_heartbeat_process_is_the_one_held : the_heartbeat_process = the_heartbeat_process_held := rfl

-- Episode13.lean, line 5049
--× theorem the_elaboration_process_is_the_one_held : the_elaboration_process = the_elaboration_process_held := rfl

-- Episode13.lean, line 5055
--× theorem the_lean_process_is_the_one_held : the_lean_process = the_lean_process_held := rfl

-- Episode13.lean, line 5059
--× theorem the_compiler_output_is_the_one_held : the_compiler_output = the_compiler_output_held := rfl

-- Episode13.lean, line 5065
--× theorem the_atreyu_process_is_the_one_held : the_atreyu_process = the_atreyu_process_held := rfl

-- Episode13.lean, line 5069
--× theorem the_equivalence_process_is_the_one_held : the_equivalence_process = the_equivalence_process_held := rfl

-- Episode13.lean, line 5073
--× theorem the_card_at_the_bottom_is_the_palmed_card_and_its_quarter_is_one_on_a_zero :
--×     the_carrier_process.quarter = Number.one FACT.Truth (Number.zero FACT.Truth)
--×       ∧ the_carrier_process.quarter.peano.length = 2
--×       ∧ the_first_card.quarter.peano.length = 1 := ⟨rfl, rfl, rfl⟩
--× theorem the_count_is_one_on_a_zero :
--×     the_counting_process.count = Natural.number FACT.Truth the_first_card.quarter (Natural.zero FACT.Truth) := rfl
--× theorem the_origin_is_one_on_a_zero :
--×     the_indexing_process.origin = Rational.number FACT.Truth the_counting_process.count (Rational.zero FACT.Truth) := rfl

-- Episode13.lean, line 5084
--× theorem the_palmed_cards_step_reaches_three_cells (fact : FACT) (rest : Number) :
--×     (the_carrier_process.interact_with_the_universe (Number.one fact rest)).peano.length = 3 := rfl
--× theorem the_palmed_cards_step_twice_is_once (number : Number) :
--×     the_carrier_process.interact_with_the_universe (the_carrier_process.interact_with_the_universe number)
--×       = the_carrier_process.interact_with_the_universe number := by cases number <;> rfl

-- Episode13.lean, line 5092
--× theorem the_one_step_written_by_hand_leaves_a_study_as_it_is (study : Study) :
--×     the_computational_process.closure study = study := rfl

-- Episode13.lean, line 5096
--× noncomputable def the_equivalence_of_the_twos_constructed : type_of% the_equivalence_process_held :=
--×   { you_the_knower := the_atreyu_process
--×     your_conclusion := .different the_first_card.symbol the_inferred_two the_counted_two (some the_carriers_two.truth) }
--× theorem the_equivalence_constructed_is_the_equivalence_of_the_twos :
--×     the_equivalence_of_the_twos_constructed = the_equivalence_of_the_twos.{0,0,0,0,0,0,0,0,0,0,0,0} := rfl

-- Episode13.lean, line 5120
--× noncomputable def the_computational_process_left_to_the_device : type_of% the_computational_process_held :=
--×   { repeatable_process := the_repeatable_process
--×     output := the_computational_process_held.output }

-- Episode13.lean, line 5126
--× theorem left_to_the_device_a_hypothesis_is_never_left_as_it_is (fact : FACT) :
--×     the_computational_process_left_to_the_device.closure (Study.hypothesis fact) ≠ Study.hypothesis fact := by
--×   intro h; cases h
--× theorem written_by_hand_a_hypothesis_is_left_as_it_is (fact : FACT) :
--×     the_computational_process.closure (Study.hypothesis fact) = Study.hypothesis fact := rfl

-- Episode13.lean, line 5133
--× theorem the_seam_is_the_closure_and_nothing_else :
--×     the_computational_process_left_to_the_device ≠ the_computational_process
--×       ∧ the_computational_process_left_to_the_device.repeatable_process = the_computational_process.repeatable_process
--×       ∧ the_computational_process_left_to_the_device.output = the_computational_process.output
--×       ∧ the_computational_process_left_to_the_device.error_code = the_computational_process.error_code
--×       ∧ the_computational_process_left_to_the_device.close = the_computational_process.close := by
--×   refine ⟨fun same => ?_, rfl, rfl, rfl, rfl⟩
--×   exact left_to_the_device_a_hypothesis_is_never_left_as_it_is FACT.Truth
--×     (by rw [same]; exact written_by_hand_a_hypothesis_is_left_as_it_is FACT.Truth)

-- Episode13.lean, line 5155
--× def the_table_taken_from_the_same (N D : Int) : Table :=
--×   fun a b => the_scaled_identity (13 * N) a b - D * the_full_table a b
--× def the_residual_of_the_pair (N D : Int) : Int := 13 * (N * N) - 36 * (N * D) + 18 * (D * D)

-- Episode13.lean, line 5159
--× theorem two_by_two_is_one_by_one_twice (a b c d : Int) : a * b * (c * d) = a * c * (b * d) := by ac_nf

-- Episode13.lean, line 5161
--× theorem what_the_table_taken_from_the_same_holds (N D : Int) :
--×     the_table_taken_from_the_same N D true true = 13 * N - 18 * D
--×       ∧ the_table_taken_from_the_same N D false false = 13 * N - 18 * D
--×       ∧ the_table_taken_from_the_same N D true false = - (5 * D)
--×       ∧ the_table_taken_from_the_same N D false true = - (18 * D) := by
--×   refine ⟨?_, ?_, ?_, ?_⟩
--×   · show 13 * N - D * 18 = 13 * N - 18 * D; omega
--×   · show 13 * N - D * 18 = 13 * N - 18 * D; omega
--×   · show 0 - D * 5 = - (5 * D); omega
--×   · show 0 - D * 18 = - (18 * D); omega

-- Episode13.lean, line 5172
--× theorem its_adjugate_is_the_same_shape_with_the_trace_taken_off (N D : Int) (a b : Bool) :
--×     the_adjugate (the_table_taken_from_the_same N D) a b
--×       = the_scaled_identity (13 * N - 36 * D) a b + D * the_full_table a b := by
--×   obtain ⟨h1, h2, h3, h4⟩ := what_the_table_taken_from_the_same_holds N D
--×   cases a <;> cases b
--×   · show the_table_taken_from_the_same N D true true = 13 * N - 36 * D + D * 18; rw [h1]; omega
--×   · show - the_table_taken_from_the_same N D false true = 0 + D * 18; rw [h4]; omega
--×   · show - the_table_taken_from_the_same N D true false = 0 + D * 5; rw [h3]; omega
--×   · show the_table_taken_from_the_same N D false false = 13 * N - 36 * D + D * 18; rw [h2]; omega

-- Episode13.lean, line 5182
--× theorem the_trace_of_its_adjugate_is_the_slope (N D : Int) :
--×     the_table_trace (the_adjugate (the_table_taken_from_the_same N D)) = 26 * N - 36 * D := by
--×   obtain ⟨h1, h2, _, _⟩ := what_the_table_taken_from_the_same_holds N D
--×   show the_table_taken_from_the_same N D false false + the_table_taken_from_the_same N D true true = 26 * N - 36 * D
--×   rw [h1, h2]; omega

-- Episode13.lean, line 5188
--× theorem its_determinant_is_thirteen_residuals (N D : Int) :
--×     the_table_determinant (the_table_taken_from_the_same N D) = 13 * the_residual_of_the_pair N D := by
--×   obtain ⟨h1, h2, h3, h4⟩ := what_the_table_taken_from_the_same_holds N D
--×   simp only [the_table_determinant, the_residual_of_the_pair, h1, h2, h3, h4, Int.sub_mul, Int.mul_sub, Int.neg_mul_neg]
--×   have e1 : 13 * N * (13 * N) = 13 * 13 * (N * N) := two_by_two_is_one_by_one_twice 13 N 13 N
--×   have e2 : 18 * D * (13 * N) = 18 * 13 * (N * D) := by rw [two_by_two_is_one_by_one_twice, Int.mul_comm D N]
--×   have e3 : 13 * N * (18 * D) = 13 * 18 * (N * D) := two_by_two_is_one_by_one_twice 13 N 18 D
--×   have e4 : 18 * D * (18 * D) = 18 * 18 * (D * D) := two_by_two_is_one_by_one_twice 18 D 18 D
--×   have e5 : 5 * D * (18 * D) = 5 * 18 * (D * D) := two_by_two_is_one_by_one_twice 5 D 18 D
--×   rw [e1, e2, e3, e4, e5]; omega

-- Episode13.lean, line 5200
--× theorem the_table_by_its_adjugate_is_thirteen_residuals_of_the_same (N D : Int) (a b : Bool) :
--×     the_table_product (the_table_taken_from_the_same N D) (the_adjugate (the_table_taken_from_the_same N D)) a b
--×       = the_scaled_identity (13 * the_residual_of_the_pair N D) a b := by
--×   rw [the_adjugate_inverts, its_determinant_is_thirteen_residuals]; rfl

-- Episode13.lean, line 5208
--× theorem the_crank_is_the_place_less_the_residual_over_the_trace (N D : Int) :
--×     N * the_table_trace (the_adjugate (the_table_taken_from_the_same N D)) - the_residual_of_the_pair N D
--×         = 13 * (N * N) - 18 * (D * D)
--×       ∧ D * the_table_trace (the_adjugate (the_table_taken_from_the_same N D)) = 26 * (N * D) - 36 * (D * D) := by
--×   rw [the_trace_of_its_adjugate_is_the_slope]
--×   simp only [the_residual_of_the_pair, Int.mul_sub]
--×   have e1 : N * (26 * N) = 26 * (N * N) := Int.mul_left_comm N 26 N
--×   have e2 : N * (36 * D) = 36 * (N * D) := Int.mul_left_comm N 36 D
--×   have e3 : D * (26 * N) = 26 * (N * D) := by rw [Int.mul_left_comm, Int.mul_comm D N]
--×   have e4 : D * (36 * D) = 36 * (D * D) := Int.mul_left_comm D 36 D
--×   rw [e1, e2, e3, e4]; constructor <;> omega

-- Episode13.lean, line 5222
--× theorem where_the_residual_is_nothing_there_is_no_inverse (N D : Int) (root : the_residual_of_the_pair N D = 0) (a b : Bool) :
--×     the_table_product (the_table_taken_from_the_same N D) (the_adjugate (the_table_taken_from_the_same N D)) a b = 0 := by
--×   rw [the_table_by_its_adjugate_is_thirteen_residuals_of_the_same, root]
--×   cases a <;> cases b <;> rfl

-- Episode13.lean, line 5234
--× def weighed_by_its_coin (table : Table) : Table := fun a b => (the_coin_weight a : Int) * table a b

-- Episode13.lean, line 5236
--× theorem the_table_weighed_is_the_same_turned_over :
--×     weighed_by_its_coin the_full_table true false = weighed_by_its_coin the_full_table false true
--×       ∧ weighed_by_its_coin the_full_table true false = 90 := ⟨rfl, rfl⟩

-- Episode13.lean, line 5240
--× theorem the_table_taken_from_the_same_weighed_is_the_same_turned_over (N D : Int) :
--×     weighed_by_its_coin (the_table_taken_from_the_same N D) true false
--×       = weighed_by_its_coin (the_table_taken_from_the_same N D) false true := by
--×   obtain ⟨_, _, h3, h4⟩ := what_the_table_taken_from_the_same_holds N D
--×   show (18 : Int) * the_table_taken_from_the_same N D true false = 5 * the_table_taken_from_the_same N D false true
--×   rw [h3, h4]; omega

-- Episode13.lean, line 5247
--× theorem the_weighted_action_varies_by_the_table_twice (N D : Int) (v h : Bool → Int) :
--×     the_action_of (weighed_by_its_coin (the_table_taken_from_the_same N D)) (fun y => v y + h y)
--×         - the_action_of (weighed_by_its_coin (the_table_taken_from_the_same N D)) v
--×       = (h true * the_refine (weighed_by_its_coin (the_table_taken_from_the_same N D)) v true
--×           + h false * the_refine (weighed_by_its_coin (the_table_taken_from_the_same N D)) v false)
--×         + (h true * the_refine (weighed_by_its_coin (the_table_taken_from_the_same N D)) v true
--×           + h false * the_refine (weighed_by_its_coin (the_table_taken_from_the_same N D)) v false)
--×         + the_action_of (weighed_by_its_coin (the_table_taken_from_the_same N D)) h :=
--×   the_action_varies_by_the_operator_twice _ (the_table_taken_from_the_same_weighed_is_the_same_turned_over N D) v h

-- Episode13.lean, line 5275
--× def holds_a_bracket : Sample → Bool
--×   | .initial_condition _ _ => false
--×   | .signal_response _ _ _ _ _ => true
--× def the_limits_held : Sample → Nat
--×   | .initial_condition _ _ => 1
--×   | .signal_response _ _ _ _ _ => 2
--× def the_place_of (first second : Sample) : Direction := (holds_a_bracket first, holds_a_bracket second)

-- Episode13.lean, line 5284
--× def one_limit : Sample := .initial_condition FACT.Truth (.nil FACT.Truth)
--× def a_bracket : Sample := .signal_response FACT.Truth (.nil FACT.Truth) FACT.Truth (.nil FACT.Truth) one_limit

-- Episode13.lean, line 5288
--× theorem a_trial_has_four_places :
--×     [the_place_of a_bracket a_bracket, the_place_of a_bracket one_limit, the_place_of one_limit a_bracket,
--×       the_place_of one_limit one_limit] = the_arms := rfl

-- Episode13.lean, line 5293
--× theorem a_bracket_holds_two_and_two_brackets_hold_four :
--×     the_limits_held a_bracket = 2 ∧ the_limits_held one_limit = 1
--×       ∧ the_limits_held a_bracket + the_limits_held a_bracket = 4 := ⟨rfl, rfl, rfl⟩

-- Episode13.lean, line 5300
--× def on_the_frinkahedron (place : Direction) : Bool := place.1 || place.2

-- Episode13.lean, line 5302
--× theorem three_places_are_on_the_frinkahedron_and_one_is_not :
--×     the_arms.map on_the_frinkahedron = [true, true, true, false] := rfl

-- Episode13.lean, line 5307
--× theorem on_the_frinkahedron_is_the_click_with_the_first_coin_turned_over (first second : Bool) :
--×     on_the_frinkahedron (first, second) = the_arm_stores_a_fact_that_can_click (!first) second := by
--×   cases first <;> cases second <;> rfl

-- Episode13.lean, line 5313
--× theorem the_devices_bit_and_stimulus_are_brackets :
--×     holds_a_bracket (BINARY.bit (Value := FACT) (Carrier := the_first_card)) = true
--×       ∧ holds_a_bracket the_repeatable_process.stimulus = true := ⟨rfl, rfl⟩

-- Episode13.lean, line 5317
--× def the_place_of_a_trial : Trial → Option Direction
--×   | .hypothesis _ _ => none
--×   | .signal_response _ first _ second _ => some (the_place_of first second)
--× theorem the_devices_first_trial_is_at_the_seam :
--×     the_place_of_a_trial the_repeatable_process.expectation = none
--×       ∧ the_place_of_a_trial (the_repeatable_process.iterate the_repeatable_process.expectation) = some (true, true) :=
--×   ⟨rfl, rfl⟩

-- Episode13.lean, line 5338
--× theorem what_the_bottom_processes_carry_is_two_cells :
--×     the_carrier_process.quarter.peano.length = 2
--×       ∧ the_counting_process.count.induct.length = 2
--×       ∧ the_indexing_process.origin.diagonalize.length = 2
--×       ∧ the_limit_process.limit.diagonalize.length = 2
--×       ∧ the_limit_process.sequence.enumerate.length = 2
--×       ∧ the_cauchy_process.accumulation.converge.length = 2
--×       ∧ the_observation_process.before.converge.length = 2 := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

-- Episode13.lean, line 5348
--× theorem one_step_of_each_reaches_three_cells :
--×     (the_counting_process.iterate the_counting_process.count).induct.length = 3
--×       ∧ (the_indexing_process.iterate the_indexing_process.origin).diagonalize.length = 3
--×       ∧ (the_limit_process.iterate the_limit_process.sequence).enumerate.length = 3
--×       ∧ (the_cauchy_process.iterate the_cauchy_process.accumulation).converge.length = 3
--×       ∧ the_cauchy_process.value.diagonalize.length = 3
--×       ∧ the_observation_process.after.converge.length = 3 := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

-- Episode13.lean, line 5357
--× theorem the_observations_step_on_the_bit_is_five_cells :
--×     (BINARY.bit (Value := FACT) (Carrier := the_first_card)).taste.length = 3
--×       ∧ (the_observation_process.iterate (BINARY.bit (Value := FACT) (Carrier := the_first_card))).taste.length = 5 :=
--×   ⟨rfl, rfl⟩

-- Episode13.lean, line 5369
--× theorem the_law_reads_the_experience_and_the_fencepost (tape : List FACT) :
--×     (the_preprint_a_list_indicates tape).the_model.length
--×       = (the_measurement_a_list_indicates tape).the_reading.length + the_fencepost_bug := by
--×   rw [the_preprint_reads_back, the_measurement_reads_back]; show 1 * tape.length + 1 = 1 * tape.length + 0 + 1; omega

-- Episode13.lean, line 5381
--× theorem simulate_from_the_mass_is_over_by_the_momentum_squared_squared (mass_squared momentum_squared : Int) :
--×     (2 * mass_squared + momentum_squared) * (2 * mass_squared + momentum_squared)
--×         - 4 * mass_squared * (mass_squared + momentum_squared)
--×       = momentum_squared * momentum_squared := by
--×   simp only [Int.add_mul, Int.mul_add]
--×   have e1 : 2 * mass_squared * (2 * mass_squared) = 4 * (mass_squared * mass_squared) := by
--×     rw [two_by_two_is_one_by_one_twice]; rfl
--×   have e2 : momentum_squared * (2 * mass_squared) = 2 * (mass_squared * momentum_squared) := by
--×     rw [Int.mul_left_comm, Int.mul_comm momentum_squared mass_squared]
--×   have e3 : 2 * mass_squared * momentum_squared = 2 * (mass_squared * momentum_squared) := Int.mul_assoc _ _ _
--×   have e4 : 4 * mass_squared * mass_squared = 4 * (mass_squared * mass_squared) := Int.mul_assoc _ _ _
--×   have e5 : 4 * mass_squared * momentum_squared = 4 * (mass_squared * momentum_squared) := Int.mul_assoc _ _ _
--×   rw [e1, e2, e3, e4, e5]; omega

-- Episode13.lean, line 5397
--× theorem on_the_devices_counts_simulate_is_over_by_ninety_squared :
--×     (2 * (13 * 18) + 5 * 18) * (2 * (13 * 18) + 5 * 18) - 4 * (13 * 18) * (18 * 18) = (90 * 90 : Int)
--×       ∧ (13 * 18 + 5 * 18 : Int) = 18 * 18 := by decide

-- Episode13.lean, line 5408
--× theorem where_nothing_stops_the_cranks_pair_is_the_tables (x y : Nat)
--×     (the_first_does_not_stop : 18 * y * y ≤ 13 * x * x) (the_second_does_not_stop : 36 * y * y ≤ 2 * 13 * x * y) :
--×     ((13 * x * x - 18 * y * y : Nat) : Int)
--×         = (x : Int) * the_table_trace (the_adjugate (the_table_taken_from_the_same x y)) - the_residual_of_the_pair x y
--×       ∧ ((2 * 13 * x * y - 36 * y * y : Nat) : Int)
--×         = (y : Int) * the_table_trace (the_adjugate (the_table_taken_from_the_same x y)) := by
--×   obtain ⟨h1, h2⟩ := the_crank_is_the_place_less_the_residual_over_the_trace x y
--×   rw [h1, h2, Int.ofNat_sub the_first_does_not_stop, Int.ofNat_sub the_second_does_not_stop]
--×   simp only [Int.natCast_mul, Int.mul_assoc]
--×   constructor <;> omega

-- Episode13.lean, line 5434
--× def the_two_coins : List Bool := [true, false]

-- Episode13.lean, line 5436
--× theorem one_two_four_eight_sixteen :
--×     the_two_coins.length = 2 ∧ the_arms.length = 4 ∧ the_connected_steps.length = 8 ∧ the_sixteen_steps.length = 16 := by
--×   decide

-- Episode13.lean, line 5442
--× def the_phrases : List (Bool × Bool) := the_sixteen_steps.flatMap fun step => [step.1, step.2]

-- Episode13.lean, line 5444
--× theorem thirty_two_phrases : the_phrases.length = 32 := by decide

-- Episode13.lean, line 5447
--× theorem sixteen_of_the_phrases_say_something_false :
--×     (the_phrases.filter fun phrase => phrase.1 != phrase.2).length = 16 := by decide

-- Episode13.lean, line 5452
--× theorem eight_cannot_click_and_the_eight_between_are_false_on_true :
--×     (the_phrases.filter fun phrase => !the_arm_stores_a_fact_that_can_click phrase.1 phrase.2).length = 8
--×       ∧ (the_phrases.filter fun phrase =>
--×             phrase.1 != phrase.2 && the_arm_stores_a_fact_that_can_click phrase.1 phrase.2)
--×           = List.replicate 8 (false, true) := by decide

-- Episode13.lean, line 5477
--× def the_first_variation_of_the_residual : Prop :=
--×   ∀ y h : Account, the_same (the_residual_on_the_account (y + h) - the_residual_on_the_account y)
--×     (the_slope_on_the_account y * h + holding the_coefficient * (h * h))

-- Episode13.lean, line 5481
--× def the_slope_of_the_residual_steps : Prop :=
--×   ∀ y h : Account, the_same (the_slope_on_the_account (y + h) - the_slope_on_the_account y) (holding twice_the_coefficient * h)

-- Episode13.lean, line 5485
--× def the_second_variation_of_the_residual : Prop :=
--×   ∀ y h k : Account,
--×     the_same ((the_residual_on_the_account (y + k + h) - the_residual_on_the_account (y + k))
--×                 - (the_residual_on_the_account (y + h) - the_residual_on_the_account y))
--×              (holding twice_the_coefficient * k * h)

-- Episode13.lean, line 5491
--× theorem the_first_variation_of_the_residual_holds : the_first_variation_of_the_residual :=
--×   the_residual_steps_by_its_slope_exactly
--× theorem the_slope_of_the_residual_steps_holds : the_slope_of_the_residual_steps :=
--×   the_slope_steps_by_twice_the_coefficient_exactly
--× theorem the_second_variation_of_the_residual_holds : the_second_variation_of_the_residual := by
--×   intro y h k
--×   have e1 := (the_same_is_the_same_balance _ _).1 (the_residual_steps_by_its_slope_exactly (y + k) h)
--×   have e2 := (the_same_is_the_same_balance _ _).1 (the_residual_steps_by_its_slope_exactly y h)
--×   have e3 := (the_same_is_the_same_balance _ _).1 (the_slope_steps_by_twice_the_coefficient_exactly y k)
--×   rw [the_same_is_the_same_balance]
--×   simp only [balance_of_palm_the_middle_card, balance_of_less, balance_of_false_shuffle] at e1 e2 e3 ⊢
--×   have e4 := congrArg (fun z => z * balance h) e3
--×   simp only [Int.sub_mul] at e4
--×   omega

-- Episode13.lean, line 5507
--× def the_gospel_of_the_residual : Gospel := .the_proof the_first_variation_of_the_residual
--× def the_newton_of_the_residual : Variation :=
--×   .the_newton the_gospel_of_the_residual the_first_variation_of_the_residual
--× def the_gateaux_of_the_residual : Variation :=
--×   .the_gateaux the_gospel_of_the_residual the_slope_of_the_residual_steps the_first_variation_of_the_residual
--×     the_newton_of_the_residual
--× def the_frechet_of_the_residual : Variation :=
--×   .the_frechet the_gospel_of_the_residual the_slope_of_the_residual_steps the_first_variation_of_the_residual
--×     the_second_variation_of_the_residual the_gateaux_of_the_residual the_newton_of_the_residual

-- Episode13.lean, line 5518
--× theorem every_statement_the_three_hold_is_true :
--×     the_first_variation_of_the_residual ∧ the_slope_of_the_residual_steps ∧ the_second_variation_of_the_residual :=
--×   ⟨the_first_variation_of_the_residual_holds, the_slope_of_the_residual_steps_holds,
--×    the_second_variation_of_the_residual_holds⟩

-- Episode13.lean, line 5525
--× theorem the_two_readers_read_the_shape :
--×     (the_newton_of_the_residual.newton.length, the_gateaux_of_the_residual.newton.length,
--×         the_frechet_of_the_residual.newton.length) = (1, 2, 3)
--×       ∧ (the_newton_of_the_residual.krylov.length, the_gateaux_of_the_residual.krylov.length,
--×         the_frechet_of_the_residual.krylov.length) = (1, 2, 4) := ⟨rfl, rfl⟩

-- Episode13.lean, line 5534
--× theorem the_process_keeps_the_first_variation :
--×     (∃ (place : Prop), the_big_red_dog_process.transmute the_newton_of_the_residual
--×         = .the_gateaux the_gospel_of_the_residual place the_first_variation_of_the_residual the_big_red_dog_process.Du)
--×       ∧ the_big_red_dog_process.transmute the_gateaux_of_the_residual
--×         = .the_frechet the_gospel_of_the_residual the_slope_of_the_residual_steps the_first_variation_of_the_residual
--×             (the_slope_of_the_residual_steps ∧ ¬ the_first_variation_of_the_residual) the_newton_of_the_residual
--×             the_big_red_dog_process.Du :=
--×   ⟨⟨_, rfl⟩, rfl⟩

-- Episode13.lean, line 5545
--× theorem what_the_process_writes_third_is_false :
--×     ¬ (the_slope_of_the_residual_steps ∧ ¬ the_first_variation_of_the_residual) :=
--×   fun both => both.2 the_first_variation_of_the_residual_holds

-- Episode13.lean, line 5550
--× theorem a_newton_is_under_a_gateaux_exactly_when_its_statement_is_second (model statement place seat : Prop)
--×     (tail : Variation) :
--×     Variation.le (.the_newton (.the_proof model) statement) (.the_gateaux (.the_proof model) place seat tail)
--×       ↔ statement = seat := by
--×   simp only [Variation.le, Gospel.le, true_and]
--× theorem a_newton_is_under_a_frechet_exactly_when_its_statement_is_second (model statement place seat third : Prop)
--×     (this that : Variation) :
--×     Variation.le (.the_newton (.the_proof model) statement) (.the_frechet (.the_proof model) place seat third this that)
--×       ↔ statement = seat := by
--×   simp only [Variation.le, Gospel.le, true_and]

-- Episode13.lean, line 5561
--× theorem the_newton_is_under_the_other_two :
--×     Variation.le the_newton_of_the_residual the_gateaux_of_the_residual
--×       ∧ Variation.le the_newton_of_the_residual the_frechet_of_the_residual :=
--×   ⟨(a_newton_is_under_a_gateaux_exactly_when_its_statement_is_second _ _ _ _ _).2 rfl,
--×    (a_newton_is_under_a_frechet_exactly_when_its_statement_is_second _ _ _ _ _ _ _).2 rfl⟩

-- Episode13.lean, line 5568
--× theorem three_turns_of_the_process :
--×     ∃ (place : Prop),
--×       the_big_red_dog_process.transmute the_newton_of_the_residual
--×           = .the_gateaux the_gospel_of_the_residual place the_first_variation_of_the_residual the_big_red_dog_process.Du
--×         ∧ the_big_red_dog_process.transmute (the_big_red_dog_process.transmute the_newton_of_the_residual)
--×           = .the_frechet the_gospel_of_the_residual place the_first_variation_of_the_residual
--×               (place ∧ ¬ the_first_variation_of_the_residual) the_big_red_dog_process.Du the_big_red_dog_process.Du
--×         ∧ the_big_red_dog_process.transmute (the_big_red_dog_process.transmute
--×             (the_big_red_dog_process.transmute the_newton_of_the_residual))
--×           = .the_gateaux the_gospel_of_the_residual (place ∧ place)
--×               (the_first_variation_of_the_residual = (place ∧ ¬ the_first_variation_of_the_residual))
--×               the_big_red_dog_process.Du :=
--×   ⟨_, rfl, rfl, rfl⟩

-- Episode13.lean, line 5583
--× theorem two_turns_of_the_process_keep_the_first_variation :
--×     Variation.le the_newton_of_the_residual (the_big_red_dog_process.transmute the_newton_of_the_residual)
--×       ∧ Variation.le the_newton_of_the_residual
--×           (the_big_red_dog_process.transmute (the_big_red_dog_process.transmute the_newton_of_the_residual)) := by
--×   obtain ⟨place, one, two, _⟩ := three_turns_of_the_process
--×   rw [two, one]
--×   exact ⟨(a_newton_is_under_a_gateaux_exactly_when_its_statement_is_second _ _ _ _ _).2 rfl,
--×          (a_newton_is_under_a_frechet_exactly_when_its_statement_is_second _ _ _ _ _ _ _).2 rfl⟩

-- Episode13.lean, line 5594
--× theorem the_third_turn_of_the_process_does_not_keep_it :
--×     ¬ Variation.le the_newton_of_the_residual
--×         (the_big_red_dog_process.transmute (the_big_red_dog_process.transmute
--×           (the_big_red_dog_process.transmute the_newton_of_the_residual))) := by
--×   obtain ⟨place, _, _, three⟩ := three_turns_of_the_process
--×   rw [three]
--×   intro under
--×   have the_seat := (a_newton_is_under_a_gateaux_exactly_when_its_statement_is_second _ _ _ _ _).1 under
--×   have it_holds := the_first_variation_of_the_residual_holds
--×   have the_same_statement := Eq.mp the_seat it_holds
--×   exact (Eq.mp the_same_statement it_holds).2 it_holds

-- Episode13.lean, line 5613
--× def the_direction (s : Int) : Bool → Int := fun coin => if coin then 5 else s

-- Episode13.lean, line 5615
--× theorem the_table_carries_a_direction_but_for_the_round_trip (s : Int) :
--×     the_refine the_full_table (the_direction s) true = (18 + s) * the_direction s true
--×       ∧ the_refine the_full_table (the_direction s) false = (18 + s) * the_direction s false + (90 - s * s) := by
--×   constructor
--×   · show (18 : Int) * 5 + 5 * s = (18 + s) * 5; omega
--×   · show (18 : Int) * 5 + 18 * s = (18 + s) * s + (90 - s * s); rw [Int.add_mul]; omega

-- Episode13.lean, line 5624
--× def the_pairing (u v : Bool → Int) : Int := 18 * (u true * v true) + 5 * (u false * v false)

-- Episode13.lean, line 5626
--× theorem the_two_directions_are_square_but_for_the_round_trip (s : Int) :
--×     the_pairing (the_direction s) (the_direction s) = 450 + 5 * (s * s)
--×       ∧ the_pairing (the_direction s) (the_direction (-s)) = 5 * (90 - s * s) := by
--×   constructor
--×   · show (18 : Int) * (5 * 5) + 5 * (s * s) = 450 + 5 * (s * s); omega
--×   · show (18 : Int) * (5 * 5) + 5 * (s * -s) = 5 * (90 - s * s); rw [Int.mul_neg]; omega

-- Episode13.lean, line 5634
--× theorem the_table_taken_from_the_same_carries_a_direction (N D s : Int) :
--×     the_refine (the_table_taken_from_the_same N D) (the_direction s) true = (13 * N - D * (18 + s)) * the_direction s true
--×       ∧ the_refine (the_table_taken_from_the_same N D) (the_direction s) false
--×           = (13 * N - D * (18 + s)) * the_direction s false - D * (90 - s * s) := by
--×   obtain ⟨h1, h2, h3, h4⟩ := what_the_table_taken_from_the_same_holds N D
--×   constructor
--×   · show the_table_taken_from_the_same N D true true * 5 + the_table_taken_from_the_same N D true false * s
--×         = (13 * N - D * (18 + s)) * 5
--×     have e1 : -(5 * D) * s = -(5 * (D * s)) := by rw [Int.neg_mul, Int.mul_assoc]
--×     have e2 : D * (18 + s) = 18 * D + D * s := by rw [Int.mul_add, Int.mul_comm D 18]
--×     rw [h1, h3, e1, e2]; omega
--×   · show the_table_taken_from_the_same N D false true * 5 + the_table_taken_from_the_same N D false false * s
--×         = (13 * N - D * (18 + s)) * s - D * (90 - s * s)
--×     rw [h4, h2, Int.sub_mul, Int.sub_mul, Int.mul_add, Int.mul_sub, Int.add_mul, Int.mul_assoc 18 D s,
--×       Int.mul_assoc 13 N s, Int.mul_assoc D s s]
--×     have e : D * 18 * s = 18 * (D * s) := by rw [Int.mul_comm D 18, Int.mul_assoc]
--×     rw [e]; omega

-- Episode13.lean, line 5659
--× def the_weighed_square (v : Bool → Int) : Int := 18 * (v true * v true) + 5 * (v false * v false)

-- Episode13.lean, line 5661
--× theorem the_action_of_two_tables_is_the_two_actions (this that : Table) (v : Bool → Int) :
--×     the_action_of (fun a b => this a b + that a b) v = the_action_of this v + the_action_of that v := by
--×   simp only [the_action_of, the_refine, Int.add_mul, Int.mul_add]; omega

-- Episode13.lean, line 5665
--× def the_weighed_same (number : Int) : Table := fun a b => if a = b then (if a then 18 * number else 5 * number) else 0

-- Episode13.lean, line 5667
--× theorem the_action_of_the_weighed_same_is_the_weighed_square (number : Int) (v : Bool → Int) :
--×     the_action_of (the_weighed_same number) v = number * the_weighed_square v := by
--×   show v true * (18 * number * v true + 0 * v false) + v false * (0 * v true + 5 * number * v false)
--×       = number * (18 * (v true * v true) + 5 * (v false * v false))
--×   rw [Int.zero_mul, Int.zero_mul, Int.add_zero, Int.zero_add, Int.mul_add]
--×   have e1 : v true * (18 * number * v true) = number * (18 * (v true * v true)) := by ac_nf
--×   have e2 : v false * (5 * number * v false) = number * (5 * (v false * v false)) := by ac_nf
--×   rw [e1, e2]

-- Episode13.lean, line 5676
--× theorem stepping_the_place_steps_the_table_by_the_weighed_same (N D step : Int) (a b : Bool) :
--×     weighed_by_its_coin (the_table_taken_from_the_same (N + step) D) a b
--×       = weighed_by_its_coin (the_table_taken_from_the_same N D) a b + the_weighed_same (13 * step) a b := by
--×   obtain ⟨h1, h2, h3, h4⟩ := what_the_table_taken_from_the_same_holds N D
--×   obtain ⟨k1, k2, k3, k4⟩ := what_the_table_taken_from_the_same_holds (N + step) D
--×   cases a <;> cases b
--×   · show (5 : Int) * the_table_taken_from_the_same (N + step) D false false
--×         = 5 * the_table_taken_from_the_same N D false false + 5 * (13 * step); rw [h2, k2]; omega
--×   · show (5 : Int) * the_table_taken_from_the_same (N + step) D false true
--×         = 5 * the_table_taken_from_the_same N D false true + 0; rw [h4, k4]; omega
--×   · show (18 : Int) * the_table_taken_from_the_same (N + step) D true false
--×         = 18 * the_table_taken_from_the_same N D true false + 0; rw [h3, k3]; omega
--×   · show (18 : Int) * the_table_taken_from_the_same (N + step) D true true
--×         = 18 * the_table_taken_from_the_same N D true true + 18 * (13 * step); rw [h1, k1]; omega

-- Episode13.lean, line 5691
--× theorem the_place_is_the_multiplier_of_the_weighed_square (N D step : Int) (v : Bool → Int) :
--×     the_action_of (weighed_by_its_coin (the_table_taken_from_the_same (N + step) D)) v
--×         - the_action_of (weighed_by_its_coin (the_table_taken_from_the_same N D)) v
--×       = 13 * step * the_weighed_square v := by
--×   rw [show weighed_by_its_coin (the_table_taken_from_the_same (N + step) D)
--×         = fun a b => weighed_by_its_coin (the_table_taken_from_the_same N D) a b + the_weighed_same (13 * step) a b from
--×       funext fun a => funext fun b => stepping_the_place_steps_the_table_by_the_weighed_same N D step a b,
--×     the_action_of_two_tables_is_the_two_actions, the_action_of_the_weighed_same_is_the_weighed_square]
--×   omega

-- Episode13.lean, line 5704
--× theorem where_the_trace_is_nothing_the_residual_is_not :
--×     the_table_trace (the_adjugate (the_table_taken_from_the_same 18 13)) = 0
--×       ∧ the_residual_of_the_pair 18 13 = -1170
--×       ∧ the_table_determinant (the_table_taken_from_the_same 18 13) ≠ 0 := by decide

-- Episode13.lean, line 5713
--× def summed_along : Nat → (Nat → Int) → Int
--×   | 0, _ => 0
--×   | steps + 1, reading => summed_along steps reading + reading steps

-- Episode13.lean, line 5717
--× theorem two_readings_summed_are_the_two_sums (steps : Nat) (this that : Nat → Int) :
--×     summed_along steps (fun place => this place + that place) = summed_along steps this + summed_along steps that := by
--×   induction steps with
--×   | zero => rfl
--×   | succ steps ih => simp only [summed_along, ih]; omega

-- Episode13.lean, line 5723
--× theorem a_difference_summed_is_the_far_end_less_the_near (steps : Nat) (reading : Nat → Int) :
--×     summed_along steps (fun place => reading (place + 1) - reading place) = reading steps - reading 0 := by
--×   induction steps with
--×   | zero => show (0 : Int) = reading 0 - reading 0; omega
--×   | succ steps ih => simp only [summed_along, ih]; omega

-- Episode13.lean, line 5729
--× theorem around_a_closed_walk_a_difference_sums_to_nothing (steps : Nat) (reading : Nat → Int)
--×     (closed : reading steps = reading 0) :
--×     summed_along steps (fun place => reading (place + 1) - reading place) = 0 := by
--×   rw [a_difference_summed_is_the_far_end_less_the_near, closed]; omega

-- Episode13.lean, line 5735
--× theorem around_a_closed_walk_the_sum_does_not_mind_a_step (steps : Nat) (reading : Nat → Int)
--×     (closed : reading steps = reading 0) :
--×     summed_along steps (fun place => reading (place + 1)) = summed_along steps reading := by
--×   have h := around_a_closed_walk_a_difference_sums_to_nothing steps reading closed
--×   have e : (fun place => reading (place + 1)) = fun place => (reading (place + 1) - reading place) + reading place :=
--×     funext fun place => by omega
--×   rw [e, two_readings_summed_are_the_two_sums, h]; omega

-- Episode13.lean, line 5745
--× theorem the_difference_of_a_product_with_nothing_over (this that : Nat → Int) (place : Nat) :
--×     this (place + 1) * that (place + 1) - this place * that place
--×       = this (place + 1) * (that (place + 1) - that place) + that place * (this (place + 1) - this place) := by
--×   rw [Int.mul_sub, Int.mul_sub, Int.mul_comm (that place) (this (place + 1)), Int.mul_comm (that place) (this place)]
--×   omega

-- Episode13.lean, line 5753
--× theorem summation_by_parts_around_a_closed_walk (steps : Nat) (this that : Nat → Int)
--×     (this_closes : this steps = this 0) (that_closes : that steps = that 0) :
--×     summed_along steps (fun place => this (place + 1) * (that (place + 1) - that place))
--×       = - summed_along steps (fun place => that place * (this (place + 1) - this place)) := by
--×   have closed : (fun place => this place * that place) steps = (fun place => this place * that place) 0 := by
--×     show this steps * that steps = this 0 * that 0; rw [this_closes, that_closes]
--×   have h := around_a_closed_walk_a_difference_sums_to_nothing steps (fun place => this place * that place) closed
--×   have e : (fun place => this (place + 1) * that (place + 1) - this place * that place)
--×       = fun place => this (place + 1) * (that (place + 1) - that place) + that place * (this (place + 1) - this place) :=
--×     funext fun place => the_difference_of_a_product_with_nothing_over this that place
--×   rw [show (fun place => (fun place => this place * that place) (place + 1) - (fun place => this place * that place) place)
--×         = fun place => this (place + 1) * that (place + 1) - this place * that place from rfl, e,
--×       two_readings_summed_are_the_two_sums] at h
--×   omega

-- Episode13.lean, line 5770
--× theorem around_a_closed_walk_the_three_terms_sum_to_nothing (steps : Nat) (this that : Nat → Int)
--×     (this_closes : this steps = this 0) (that_closes : that steps = that 0) :
--×     summed_along steps (fun place => this place * (that (place + 1) - that place))
--×       + summed_along steps (fun place => that place * (this (place + 1) - this place))
--×       + summed_along steps (fun place => (this (place + 1) - this place) * (that (place + 1) - that place)) = 0 := by
--×   have h := summation_by_parts_around_a_closed_walk steps this that this_closes that_closes
--×   have e : (fun place => this (place + 1) * (that (place + 1) - that place))
--×       = fun place => this place * (that (place + 1) - that place)
--×           + (this (place + 1) - this place) * (that (place + 1) - that place) :=
--×     funext fun place => by rw [Int.sub_mul]; omega
--×   rw [e, two_readings_summed_are_the_two_sums] at h
--×   omega

-- Episode13.lean, line 5785
--× def nothing_one_nothing : Nat → Int := fun place => if place = 1 then 1 else 0
--× theorem the_remainder_alone_sums_to_two :
--×     nothing_one_nothing 2 = nothing_one_nothing 0
--×       ∧ summed_along 2 (fun place => (nothing_one_nothing (place + 1) - nothing_one_nothing place)
--×           * (nothing_one_nothing (place + 1) - nothing_one_nothing place)) = 2 := by decide

-- Episode13.lean, line 5795
--× theorem the_difference_of_a_product_on_the_torus_with_nothing_over {n : Nat} (f g : Site4 n → Int) (way : Direction)
--×     (x : Site4 n) :
--×     the_difference way (fun y => f y * g y) x
--×       = f (the_step way x) * the_difference way g x + g x * the_difference way f x := by
--×   simp only [the_difference]
--×   rw [Int.mul_sub, Int.mul_sub, Int.mul_comm (g x) (f (the_step way x)), Int.mul_comm (g x) (f x)]
--×   omega

-- Episode13.lean, line 5808
--× def the_state_one_step_on {n : Nat} (state : Site4 n → Turns) (U : Torus4 n) (way : Direction) : Site4 n → Turns :=
--×   fun x => the_turns_product (U way x) (state (the_step way x))

-- Episode13.lean, line 5811
--× theorem the_step_keeps_the_length_at_every_site {n : Nat} (state : Site4 n → Turns) (U : Torus4 n) (way : Direction)
--×     (unit : ∀ x, the_turns_norm (U way x) = 1) (x : Site4 n) :
--×     the_turns_norm (the_state_one_step_on state U way x) = the_turns_norm (state (the_step way x)) := by
--×   rw [the_state_one_step_on, the_norm_is_multiplicative, unit, Int.one_mul]

-- Episode13.lean, line 5817
--× theorem around_a_closed_walk_the_step_keeps_the_summed_length (steps : Nat) (state link : Nat → Turns)
--×     (closed : state steps = state 0) (unit : ∀ place, the_turns_norm (link place) = 1) :
--×     summed_along steps (fun place => the_turns_norm (the_turns_product (link place) (state (place + 1))))
--×       = summed_along steps (fun place => the_turns_norm (state place)) := by
--×   have e : (fun place => the_turns_norm (the_turns_product (link place) (state (place + 1))))
--×       = fun place => (fun place => the_turns_norm (state place)) (place + 1) :=
--×     funext fun place => by rw [the_norm_is_multiplicative, unit, Int.one_mul]
--×   rw [e]
--×   exact around_a_closed_walk_the_sum_does_not_mind_a_step steps (fun place => the_turns_norm (state place))
--×     (by show the_turns_norm (state steps) = the_turns_norm (state 0); rw [closed])

-- Episode13.lean, line 5833
--× theorem the_gap_squared_is_four_of_the_crossings (stay out back : Int) :
--×     the_gap_squared (the_refinement_table stay out back) = 4 * (out * back) := by
--×   show (stay + stay) * (stay + stay) - 4 * (stay * stay - out * back) = 4 * (out * back)
--×   rw [Int.add_mul, Int.mul_add, Int.mul_sub]; omega

-- Episode13.lean, line 5840
--× theorem the_devices_table_is_that_table (a b : Bool) : the_refinement_table 18 5 18 a b = the_full_table a b := by
--×   cases a <;> cases b <;> rfl

-- Episode13.lean, line 5843
--× theorem kept_struck_and_turned_over :
--×     the_gap_squared (the_refinement_table 18 5 18) = 360
--×       ∧ the_gap_squared (the_refinement_table 18 0 18) = 0
--×       ∧ the_gap_squared (the_refinement_table 18 5 (-18)) = -360 := by decide

-- Episode13.lean, line 5880
--× def the_direction_up : Bool → Int × Int := fun coin => if coin then (5, 0) else (0, 1)
--× def the_direction_down : Bool → Int × Int := fun coin => if coin then (5, 0) else (0, -1)
--× def refined_in_pairs (table : Table) (v : Bool → Int × Int) (coin : Bool) : Int × Int :=
--×   (the_refine table (fun c => (v c).1) coin, the_refine table (fun c => (v c).2) coin)

-- Episode13.lean, line 5885
--× theorem the_table_carries_the_two_directions_exactly :
--×     (∀ coin, refined_in_pairs the_full_table the_direction_up coin
--×         = the_surd_product the_outer_radius (the_direction_up coin))
--×       ∧ (∀ coin, refined_in_pairs the_full_table the_direction_down coin
--×         = the_surd_product the_hole (the_direction_down coin)) := by decide

-- Episode13.lean, line 5893
--× def the_pairing_in_pairs (u v : Bool → Int × Int) : Int × Int :=
--×   ((18 : Int) * (the_surd_product (u true) (v true)).1 + 5 * (the_surd_product (u false) (v false)).1,
--×    (18 : Int) * (the_surd_product (u true) (v true)).2 + 5 * (the_surd_product (u false) (v false)).2)

-- Episode13.lean, line 5897
--× theorem the_two_directions_are_square_to_each_other :
--×     the_pairing_in_pairs the_direction_up the_direction_up = (900, 0)
--×       ∧ the_pairing_in_pairs the_direction_down the_direction_down = (900, 0)
--×       ∧ the_pairing_in_pairs the_direction_up the_direction_down = (0, 0) := by decide

-- Episode13.lean, line 5904
--× theorem the_table_taken_from_the_same_carries_them_exactly (N D : Int) :
--×     (∀ coin, refined_in_pairs (the_table_taken_from_the_same N D) the_direction_up coin
--×         = the_surd_product (13 * N - 18 * D, - D) (the_direction_up coin))
--×       ∧ (∀ coin, refined_in_pairs (the_table_taken_from_the_same N D) the_direction_down coin
--×         = the_surd_product (13 * N - 18 * D, D) (the_direction_down coin)) := by
--×   obtain ⟨h1, h2, h3, h4⟩ := what_the_table_taken_from_the_same_holds N D
--×   have ninety := the_round_trip_is_ninety
--×   refine ⟨fun coin => ?_, fun coin => ?_⟩ <;> cases coin <;> refine Prod.ext ?_ ?_
--×   · show the_table_taken_from_the_same N D false true * 5 + the_table_taken_from_the_same N D false false * 0
--×         = (13 * N - 18 * D) * 0 + the_round_trip * (- D) * 1
--×     rw [h4, h2, ninety]; omega
--×   · show the_table_taken_from_the_same N D false true * 0 + the_table_taken_from_the_same N D false false * 1
--×         = (13 * N - 18 * D) * 1 + (- D) * 0
--×     rw [h4, h2]; omega
--×   · show the_table_taken_from_the_same N D true true * 5 + the_table_taken_from_the_same N D true false * 0
--×         = (13 * N - 18 * D) * 5 + the_round_trip * (- D) * 0
--×     rw [h1, h3, ninety]; omega
--×   · show the_table_taken_from_the_same N D true true * 0 + the_table_taken_from_the_same N D true false * 1
--×         = (13 * N - 18 * D) * 0 + (- D) * 5
--×     rw [h1, h3]; omega
--×   · show the_table_taken_from_the_same N D false true * 5 + the_table_taken_from_the_same N D false false * 0
--×         = (13 * N - 18 * D) * 0 + the_round_trip * D * (-1)
--×     rw [h4, h2, ninety]; omega
--×   · show the_table_taken_from_the_same N D false true * 0 + the_table_taken_from_the_same N D false false * (-1)
--×         = (13 * N - 18 * D) * (-1) + D * 0
--×     rw [h4, h2]; omega
--×   · show the_table_taken_from_the_same N D true true * 5 + the_table_taken_from_the_same N D true false * 0
--×         = (13 * N - 18 * D) * 5 + the_round_trip * D * 0
--×     rw [h1, h3, ninety]; omega
--×   · show the_table_taken_from_the_same N D true true * 0 + the_table_taken_from_the_same N D true false * (-1)
--×         = (13 * N - 18 * D) * 0 + D * 5
--×     rw [h1, h3]; omega

-- Episode13.lean, line 5938
--× theorem the_two_it_is_carried_by_multiply_to_thirteen_residuals (N D : Int) :
--×     the_surd_product (13 * N - 18 * D, - D) (13 * N - 18 * D, D) = (13 * the_residual_of_the_pair N D, 0) := by
--×   have ninety := the_round_trip_is_ninety
--×   refine Prod.ext ?_ ?_
--×   · show (13 * N - 18 * D) * (13 * N - 18 * D) + the_round_trip * (- D) * D = 13 * the_residual_of_the_pair N D
--×     rw [ninety, the_residual_of_the_pair, Int.sub_mul, Int.mul_sub, Int.mul_sub, Int.mul_neg, Int.neg_mul]
--×     have e1 : 13 * N * (13 * N) = 13 * 13 * (N * N) := two_by_two_is_one_by_one_twice 13 N 13 N
--×     have e2 : 18 * D * (13 * N) = 18 * 13 * (N * D) := by rw [two_by_two_is_one_by_one_twice, Int.mul_comm D N]
--×     have e3 : 13 * N * (18 * D) = 13 * 18 * (N * D) := two_by_two_is_one_by_one_twice 13 N 18 D
--×     have e4 : 18 * D * (18 * D) = 18 * 18 * (D * D) := two_by_two_is_one_by_one_twice 18 D 18 D
--×     have e5 : (90 : Int) * D * D = 90 * (D * D) := Int.mul_assoc 90 D D
--×     rw [e1, e2, e3, e4, e5]; omega
--×   · show (13 * N - 18 * D) * D + (- D) * (13 * N - 18 * D) = 0
--×     rw [Int.neg_mul, Int.mul_comm D (13 * N - 18 * D)]; omega

-- Episode13.lean, line 5963
--× theorem the_table_refines_as_written (v : Bool → Int) :
--×     the_refine the_full_table v true = 18 * v true + 5 * v false
--×       ∧ the_refine the_full_table v false = 18 * v true + 18 * v false := ⟨rfl, rfl⟩

-- Episode13.lean, line 5967
--× theorem the_table_is_never_past_seven_hundred_and_fifty_six (v : Bool → Int) :
--×     the_weighed_square (the_refine the_full_table v) ≤ 756 * the_weighed_square v := by
--×   simp only [the_weighed_square, (the_table_refines_as_written v).1, (the_table_refines_as_written v).2]
--×   exact Meanings.a_bound_on_the_weighed_square 18 5 18 5 18 18 756 _ _ (by decide) (by decide)

-- Episode13.lean, line 5972
--× theorem a_pair_the_table_takes_past_seven_hundred_and_fifty_five :
--×     755 * the_weighed_square (fun c => if c then 50 else 95)
--×       < the_weighed_square (the_refine the_full_table (fun c => if c then 50 else 95)) := by decide

-- Episode13.lean, line 5976
--× theorem seven_hundred_and_fifty_five_is_no_wall :
--×     ¬ ∀ v, the_weighed_square (the_refine the_full_table v) ≤ 755 * the_weighed_square v :=
--×   fun h => Int.not_le.mpr a_pair_the_table_takes_past_seven_hundred_and_fifty_five (h _)

-- Episode13.lean, line 5980
--× theorem the_norm_is_reached_in_the_pairs :
--×     the_pairing_in_pairs (refined_in_pairs the_full_table the_direction_up) (refined_in_pairs the_full_table the_direction_up)
--×         = the_surd_product (the_surd_product the_outer_radius the_outer_radius)
--×             (the_pairing_in_pairs the_direction_up the_direction_up)
--×       ∧ the_surd_product the_outer_radius the_outer_radius = (414, 36) := by decide

-- Episode13.lean, line 5986
--× theorem the_characteristic_of_the_table_is_thirteen_residuals (y : Int) :
--×     (13 * y) * (13 * y) - 36 * (13 * y) + 234 = 13 * the_residual_at y := by
--×   have e : ∀ c : Int, (c * y) * (c * y) - 36 * (c * y) + 18 * c = c * (c * y * y - 36 * y + 18) := by
--×     intro c; simp only [Int.mul_sub, Int.mul_add]; ac_nf
--×   have := e 13
--×   simp only [the_residual_at]
--×   omega

-- Episode13.lean, line 5998
--× def the_norm_as_a_real := Meanings.theNorm.bracketed
--× def the_base_the_derivative_leaves_alone := Meanings.theBaseTheDerivativeLeavesAlone

-- Episode13.lean, line 6001
--× theorem the_printed_digits_are_in_the_norms_bracket :
--×     324 * Meanings.theNorm.cut 20 * 10 ^ 24 ≤ 137011290548979457087737300 * (65 * 2 ^ 20)
--×       ∧ 137011290548979457087737300 * (65 * 2 ^ 20) ≤ 324 * (Meanings.theNorm.cut 20 + 1) * 10 ^ 24 := by decide

-- Episode13.lean, line 6007
--× def the_norm_squared_as_a_real := the_norm_as_a_real.mul the_norm_as_a_real

-- Episode13.lean, line 6009
--× theorem the_norm_squared_as_a_real_is_between_the_walls :
--×     755 * (the_norm_squared_as_a_real.low 0).under ≤ (the_norm_squared_as_a_real.low 0).over
--×       ∧ (the_norm_squared_as_a_real.high 0).over ≤ 756 * (the_norm_squared_as_a_real.high 0).under := by decide +kernel

-- Episode13.lean, line 6016
--× theorem the_tables_polynomial_holds_nothing_at_both_roots :
--×     (Meanings.theTablesPolynomialAt Meanings.theUpperRoot).HoldsNothingAt 0
--×       ∧ (Meanings.theTablesPolynomialAt Meanings.theLowerRoot).HoldsNothingAt 0
--×       ∧ ¬ (Meanings.theTablesPolynomialAt (Meanings.SignedReal.ofNat 10)).HoldsNothingAt 0 := by decide +kernel

-- Episode13.lean, line 6034
--× theorem the_weighed_action_is_two_squares (v : Bool → Int) :
--×     the_action_of (weighed_by_its_coin the_full_table) v
--×       = 90 * ((v true + v false) * (v true + v false)) + 234 * (v true * v true) := by
--×   show v true * (18 * 18 * v true + 18 * 5 * v false) + v false * (5 * 18 * v true + 5 * 18 * v false)
--×       = 90 * ((v true + v false) * (v true + v false)) + 234 * (v true * v true)
--×   have e1 : v true * (18 * 18 * v true) = 18 * 18 * (v true * v true) := Int.mul_left_comm _ _ _
--×   have e2 : v true * (18 * 5 * v false) = 18 * 5 * (v true * v false) := Int.mul_left_comm _ _ _
--×   have e3 : v false * (5 * 18 * v true) = 5 * 18 * (v true * v false) := by
--×     rw [Int.mul_left_comm, Int.mul_comm (v false) (v true)]
--×   have e4 : v false * (5 * 18 * v false) = 5 * 18 * (v false * v false) := Int.mul_left_comm _ _ _
--×   have left : v true * (18 * 18 * v true + 18 * 5 * v false) + v false * (5 * 18 * v true + 5 * 18 * v false)
--×       = 324 * (v true * v true) + 180 * (v true * v false) + 90 * (v false * v false) := by
--×     rw [Int.mul_add (v true), Int.mul_add (v false), e1, e2, e3, e4]; omega
--×   have right : (v true + v false) * (v true + v false)
--×       = v true * v true + 2 * (v true * v false) + v false * v false := by
--×     rw [Int.add_mul, Int.mul_add, Int.mul_add, Int.mul_comm (v false) (v true)]; omega
--×   rw [left, right]; omega

-- Episode13.lean, line 6052
--× theorem a_square_is_never_under_nothing (x : Int) : 0 ≤ x * x := by
--×   rcases Int.le_total 0 x with h | h
--×   · exact Int.mul_nonneg h h
--×   · have := Int.mul_nonneg (Int.neg_nonneg_of_nonpos h) (Int.neg_nonneg_of_nonpos h)
--×     rwa [Int.neg_mul_neg] at this

-- Episode13.lean, line 6058
--× theorem the_weighed_action_is_never_under_nothing (v : Bool → Int) :
--×     0 ≤ the_action_of (weighed_by_its_coin the_full_table) v := by
--×   rw [the_weighed_action_is_two_squares]
--×   have a := a_square_is_never_under_nothing (v true + v false)
--×   have b := a_square_is_never_under_nothing (v true)
--×   omega

-- Episode13.lean, line 6068
--× def the_table_the_same_both_ways (a b : Bool) : Int × Int := if a = b then (18, 0) else (0, 1)

-- Episode13.lean, line 6070
--× theorem each_row_adds_to_the_outer_radius (a : Bool) :
--×     ((the_table_the_same_both_ways a true).1 + (the_table_the_same_both_ways a false).1,
--×      (the_table_the_same_both_ways a true).2 + (the_table_the_same_both_ways a false).2) = the_outer_radius := by
--×   cases a <;> rfl

-- Episode13.lean, line 6075
--× theorem together_by_the_outer_radius_and_against_by_the_hole :
--×     (∀ a, ((the_table_the_same_both_ways a true).1 - (the_table_the_same_both_ways a false).1,
--×            (the_table_the_same_both_ways a true).2 - (the_table_the_same_both_ways a false).2)
--×         = the_surd_product the_hole (if a then (1, 0) else (-1, 0)))
--×       ∧ the_table_the_same_both_ways true ≠ the_table_the_same_both_ways false := by
--×   refine ⟨by decide, fun same => ?_⟩
--×   have h := congrFun same true
--×   exact absurd h (by decide)

-- Episode13.lean, line 6087
--× theorem a_turn_spreads_the_two (first second : Int) :
--×     the_surd_product (18, 0) (first, 0) = (18 * first, 0)
--×       ∧ ((18 * first + 0 * second) + (0 * first + 18 * second), (0 * first + 1 * second) + (1 * first + 0 * second))
--×           = the_surd_product the_outer_radius (first + second, 0)
--×       ∧ ((18 * first + 0 * second) - (0 * first + 18 * second), (0 * first + 1 * second) - (1 * first + 0 * second))
--×           = the_surd_product the_hole (first - second, 0) := by
--×   have ninety := the_round_trip_is_ninety
--×   refine ⟨?_, ?_, ?_⟩ <;> refine Prod.ext ?_ ?_
--×   · show (18 : Int) * first + the_round_trip * 0 * 0 = 18 * first; rw [ninety]; omega
--×   · show (18 : Int) * 0 + 0 * first = 0; omega
--×   · show (18 * first + 0 * second) + (0 * first + 18 * second) = 18 * (first + second) + the_round_trip * 1 * 0
--×     rw [ninety]; omega
--×   · show (0 * first + 1 * second) + (1 * first + 0 * second) = 18 * 0 + 1 * (first + second); omega
--×   · show (18 * first + 0 * second) - (0 * first + 18 * second) = 18 * (first - second) + the_round_trip * (-1) * 0
--×     rw [ninety]; omega
--×   · show (0 * first + 1 * second) - (1 * first + 0 * second) = 18 * 0 + (-1) * (first - second); omega

-- Episode13.lean, line 6107
--× theorem two_closed_counts_are_needed_and_three_are_not :
--×     (the_closed_walks 0 : Int) * the_closed_walks 2 - (the_closed_walks 1 : Int) * the_closed_walks 1 = 360
--×       ∧ (the_closed_walks 0 : Int) * ((the_closed_walks 2 : Int) * the_closed_walks 4 - (the_closed_walks 3 : Int) * the_closed_walks 3)
--×           - (the_closed_walks 1 : Int) * ((the_closed_walks 1 : Int) * the_closed_walks 4 - (the_closed_walks 3 : Int) * the_closed_walks 2)
--×           + (the_closed_walks 2 : Int) * ((the_closed_walks 1 : Int) * the_closed_walks 3 - (the_closed_walks 2 : Int) * the_closed_walks 2)
--×         = 0 := by decide

-- Episode13.lean, line 6117
--× theorem the_gap_squared_is_the_discriminant_of_the_symbol (table : Table) :
--×     the_gap_squared table
--×       = (table true true - table false false) * (table true true - table false false)
--×         + 4 * (table true false * table false true) := by
--×   show (table true true + table false false) * (table true true + table false false)
--×         - 4 * (table true true * table false false - table true false * table false true) = _
--×   rw [Int.add_mul, Int.mul_add, Int.mul_add, Int.sub_mul, Int.mul_sub, Int.mul_sub, Int.mul_sub,
--×     Int.mul_comm (table false false) (table true true)]
--×   omega

-- Episode13.lean, line 6148
--× theorem the_knowers_bit_is_not_fixed_by_what_is_read :
--×     (satSearch the_knowers_triple an_odd_number_are_true 3 = true
--×         ∧ satSearch the_knowers_triple an_even_number_are_true 3 = true)
--×       ∧ (∀ you_do : FACT,
--×           (the_surd_product (you_re_a_daisy_if_you_do you_do) (you_re_a_daisy_if_you_do you_do)).1
--×               - 11664 * (you_re_a_daisy_if_you_do you_do).1 + 24564384 = 0
--×             ∧ (the_surd_product (you_re_a_daisy_if_you_do you_do) (you_re_a_daisy_if_you_do you_do)).2
--×               - 11664 * (you_re_a_daisy_if_you_do you_do).2 = 0)
--×       ∧ you_re_a_daisy_if_you_do (bitFACT true) ≠ you_re_a_daisy_if_you_do (bitFACT false) :=
--×   ⟨the_solver_finds_a_witness_either_way,
--×    fun you_do => ⟨(you_re_a_daisy_either_way you_do).1, (you_re_a_daisy_either_way you_do).2.1⟩,
--×    by decide⟩

-- Episode13.lean, line 6164
--× theorem every_reader_of_the_closures_reads_the_two_ladders_alike {what_is_read : Sort any} (reader : Closure → what_is_read) :
--×     reader the_other_conclusion = reader the_conclusion ∧ reader the_other_alpha = reader the_alpha :=
--×   ⟨congrArg reader asked_only_whether_it_is_true_the_two_ladders_carry_the_same_closures.1,
--×    congrArg reader asked_only_whether_it_is_true_the_two_ladders_carry_the_same_closures.2⟩

-- Episode13.lean, line 6172
--× theorem the_record_and_the_tally_do_not_fix_it (places : List Nat) (the_model : Nat → Nat × Nat) :
--×     (∃ another_model : Nat → Nat × Nat,
--×         (∀ place, place ∈ places → another_model place = the_model place) ∧ another_model ≠ the_model)
--×       ∧ (∀ (reader : Nat → Bool) (carriers : TwoCarriers),
--×           reader (the_tally carriers.swap) = reader (the_tally carriers)) :=
--×   ⟨the_value_and_the_velocity_do_not_tell places the_model,
--×    fun reader carriers => no_reader_of_the_tally_sees_which_carrier reader carriers⟩

-- Episode13.lean, line 6192
--× def the_square_of_three_in_a_row (n : Nat) : Int :=
--×   (the_closed_walks n : Int) * the_closed_walks (n + 2) - (the_closed_walks (n + 1) : Int) * the_closed_walks (n + 1)

-- Episode13.lean, line 6195
--× theorem the_next_count_is_fixed_by_the_two_before (n : Nat) :
--×     (the_closed_walks (n + 2) : Int) = 36 * the_closed_walks (n + 1) - 234 * the_closed_walks n := by
--×   have h := the_closed_walks_obey_the_table n
--×   have t : the_trace = 36 := rfl
--×   have d : the_determinant = 234 := rfl
--×   rw [t, d] at h; omega

-- Episode13.lean, line 6202
--× theorem the_square_of_three_is_multiplied_by_the_determinant (n : Nat) :
--×     the_square_of_three_in_a_row (n + 1) = 234 * the_square_of_three_in_a_row n := by
--×   have hc := the_next_count_is_fixed_by_the_two_before n
--×   have hd := the_next_count_is_fixed_by_the_two_before (n + 1)
--×   simp only [the_square_of_three_in_a_row]
--×   have e1 : (the_closed_walks (n + 2) : Int) * the_closed_walks (n + 2)
--×       = 36 * ((the_closed_walks (n + 1) : Int) * the_closed_walks (n + 2))
--×         - 234 * ((the_closed_walks n : Int) * the_closed_walks (n + 2)) := by
--×     have := congrArg (fun z => z * (the_closed_walks (n + 2) : Int)) hc
--×     simp only [Int.sub_mul, Int.mul_assoc] at this; exact this
--×   have e2 : (the_closed_walks (n + 1) : Int) * the_closed_walks (n + 1 + 2)
--×       = 36 * ((the_closed_walks (n + 1) : Int) * the_closed_walks (n + 2))
--×         - 234 * ((the_closed_walks (n + 1) : Int) * the_closed_walks (n + 1)) := by
--×     rw [hd, Int.mul_sub, Int.mul_left_comm, Int.mul_left_comm (the_closed_walks (n + 1) : Int) 234]
--×   rw [show n + 1 + 1 = n + 2 from rfl, e2, e1]; omega

-- Episode13.lean, line 6218
--× theorem the_square_of_three_is_never_nothing : ∀ n : Nat, 0 < the_square_of_three_in_a_row n
--×   | 0 => by decide
--×   | n + 1 => by
--×     rw [the_square_of_three_is_multiplied_by_the_determinant]
--×     have := the_square_of_three_is_never_nothing n; omega

-- Episode13.lean, line 6231
--× def struck (table : Table) : Table := fun a b => if a = true ∧ b = false then 0 else table a b
--× def turned_over (table : Table) : Table := fun a b => if a = false ∧ b = true then - table a b else table a b

-- Episode13.lean, line 6234
--× theorem the_three_maps_on_a_stay_and_two_crossings (stay out back : Int) (a b : Bool) :
--×     struck (the_refinement_table stay out back) a b = the_refinement_table stay 0 back a b
--×       ∧ turned_over (the_refinement_table stay out back) a b = the_refinement_table stay out (- back) a b := by
--×   cases a <;> cases b <;> exact ⟨rfl, rfl⟩

-- Episode13.lean, line 6241
--× theorem the_gap_squared_of_the_three_ways (stay out back : Int) :
--×     the_gap_squared (kept (the_refinement_table stay out back)) = 4 * (out * back)
--×       ∧ the_gap_squared (struck (the_refinement_table stay out back)) = 0
--×       ∧ the_gap_squared (turned_over (the_refinement_table stay out back)) = - (4 * (out * back)) := by
--×   refine ⟨the_gap_squared_is_four_of_the_crossings stay out back, ?_, ?_⟩
--×   · rw [show struck (the_refinement_table stay out back) = the_refinement_table stay 0 back from
--×         funext fun a => funext fun b => (the_three_maps_on_a_stay_and_two_crossings stay out back a b).1,
--×       the_gap_squared_is_four_of_the_crossings, Int.zero_mul]; rfl
--×   · rw [show turned_over (the_refinement_table stay out back) = the_refinement_table stay out (- back) from
--×         funext fun a => funext fun b => (the_three_maps_on_a_stay_and_two_crossings stay out back a b).2,
--×       the_gap_squared_is_four_of_the_crossings, Int.mul_neg, Int.mul_neg]

-- Episode13.lean, line 6254
--× theorem which_arm_each_map_moves (table : Table) (a b : Bool) :
--×     (struck table a b ≠ table a b → the_arm_stores_a_fact_that_can_click a b = false)
--×       ∧ (turned_over table a b ≠ table a b → a = false ∧ b = true) := by
--×   cases a <;> cases b <;> simp [struck, turned_over, the_arm_stores_a_fact_that_can_click]

-- Episode13.lean, line 6272
--× def comes_round (steps : Nat) (reading : Nat → Int) : Prop := ∀ place, reading (place + steps) = reading place
--× def one_place_on (reading : Nat → Int) : Nat → Int := fun place => reading (place + 1)
--× def the_difference_along (reading : Nat → Int) : Nat → Int := fun place => reading (place + 1) - reading place

-- Episode13.lean, line 6276
--× theorem one_place_on_comes_round (steps : Nat) (reading : Nat → Int) (round : comes_round steps reading) :
--×     comes_round steps (one_place_on reading) := fun place => by
--×   show reading (place + steps + 1) = reading (place + 1)
--×   rw [show place + steps + 1 = place + 1 + steps by omega]; exact round (place + 1)

-- Episode13.lean, line 6281
--× theorem the_difference_comes_round (steps : Nat) (reading : Nat → Int) (round : comes_round steps reading) :
--×     comes_round steps (the_difference_along reading) := fun place => by
--×   show reading (place + steps + 1) - reading (place + steps) = reading (place + 1) - reading place
--×   rw [show place + steps + 1 = place + 1 + steps by omega, round (place + 1), round place]

-- Episode13.lean, line 6286
--× theorem what_comes_round_closes (steps : Nat) (reading : Nat → Int) (round : comes_round steps reading) :
--×     reading steps = reading 0 := by
--×   have h := round 0; rwa [Nat.zero_add] at h

-- Episode13.lean, line 6290
--× theorem by_parts_for_what_comes_round (steps : Nat) (this that : Nat → Int)
--×     (this_round : comes_round steps this) (that_round : comes_round steps that) :
--×     summed_along steps (fun place => this place * the_difference_along that place)
--×       = - summed_along steps (fun place => the_difference_along this place * one_place_on that place) := by
--×   have h := summation_by_parts_around_a_closed_walk steps that this
--×     (what_comes_round_closes steps that that_round) (what_comes_round_closes steps this this_round)
--×   have e1 : (fun place => that (place + 1) * (this (place + 1) - this place))
--×       = fun place => the_difference_along this place * one_place_on that place :=
--×     funext fun place => Int.mul_comm _ _
--×   have e2 : (fun place => this place * (that (place + 1) - that place))
--×       = fun place => this place * the_difference_along that place := rfl
--×   rw [e1, e2] at h; omega

-- Episode13.lean, line 6306
--× theorem the_variation_of_the_bending_is_the_fourth_difference (steps : Nat) (bent other : Nat → Int)
--×     (bent_round : comes_round steps bent) (other_round : comes_round steps other) :
--×     summed_along steps (fun place =>
--×         the_difference_along (the_difference_along bent) place * the_difference_along (the_difference_along other) place)
--×       = summed_along steps (fun place =>
--×           the_difference_along (the_difference_along (the_difference_along (the_difference_along bent))) place
--×             * one_place_on (one_place_on other) place) := by
--×   have d1 := the_difference_comes_round steps bent bent_round
--×   have d2 := the_difference_comes_round steps _ d1
--×   have d3 := the_difference_comes_round steps _ d2
--×   have o1 := the_difference_comes_round steps other other_round
--×   have s1 := one_place_on_comes_round steps other other_round
--×   have first := by_parts_for_what_comes_round steps (the_difference_along (the_difference_along bent))
--×     (the_difference_along other) d2 o1
--×   have second := by_parts_for_what_comes_round steps
--×     (the_difference_along (the_difference_along (the_difference_along bent))) (one_place_on other) d3 s1
--×   have same : (fun place => the_difference_along (the_difference_along (the_difference_along bent)) place
--×         * one_place_on (the_difference_along other) place)
--×       = fun place => the_difference_along (the_difference_along (the_difference_along bent)) place
--×         * the_difference_along (one_place_on other) place := rfl
--×   rw [same] at first
--×   omega

-- Episode13.lean, line 6330
--× theorem the_fourth_difference_is_the_stencil (reading : Nat → Int) (place : Nat) :
--×     the_difference_along (the_difference_along (the_difference_along (the_difference_along reading))) place
--×       = reading (place + 4) - 4 * reading (place + 3) + 6 * reading (place + 2) - 4 * reading (place + 1)
--×         + reading place := by
--×   simp only [the_difference_along, Nat.add_assoc, Nat.reduceAdd]; omega

-- Episode13.lean, line 6347
--× def the_bending_energy (steps : Nat) (bent : Nat → Int) : Int :=
--×   summed_along steps fun place =>
--×     the_difference_along (the_difference_along bent) place * the_difference_along (the_difference_along bent) place
--× def the_bending_of_two (steps : Nat) (bent other : Nat → Int) : Int :=
--×   summed_along steps fun place =>
--×     the_difference_along (the_difference_along bent) place * the_difference_along (the_difference_along other) place

-- Episode13.lean, line 6354
--× theorem a_number_of_a_reading_summed (steps : Nat) (number : Int) (reading : Nat → Int) :
--×     summed_along steps (fun place => number * reading place) = number * summed_along steps reading := by
--×   induction steps with
--×   | zero => show (0 : Int) = number * 0; omega
--×   | succ steps ih => simp only [summed_along, ih, Int.mul_add]

-- Episode13.lean, line 6360
--× theorem the_second_difference_of_a_reading_moved (bent other : Nat → Int) (number : Int) (place : Nat) :
--×     the_difference_along (the_difference_along fun p => bent p + number * other p) place
--×       = the_difference_along (the_difference_along bent) place
--×         + number * the_difference_along (the_difference_along other) place := by
--×   simp only [the_difference_along, Int.mul_sub]; omega

-- Episode13.lean, line 6366
--× theorem a_sum_squared (a number b : Int) :
--×     (a + number * b) * (a + number * b) = a * a + 2 * (number * (a * b)) + number * number * (b * b) := by
--×   rw [Int.add_mul, Int.mul_add, Int.mul_add]
--×   have e1 : a * (number * b) = number * (a * b) := Int.mul_left_comm _ _ _
--×   have e2 : number * b * a = number * (a * b) := by rw [Int.mul_assoc, Int.mul_comm b a]
--×   have e3 : number * b * (number * b) = number * number * (b * b) := two_by_two_is_one_by_one_twice _ _ _ _
--×   rw [e1, e2, e3]; omega

-- Episode13.lean, line 6374
--× theorem the_bending_energy_of_a_reading_moved (steps : Nat) (bent other : Nat → Int) (number : Int) :
--×     the_bending_energy steps (fun place => bent place + number * other place)
--×       = the_bending_energy steps bent + 2 * (number * the_bending_of_two steps bent other)
--×         + number * number * the_bending_energy steps other := by
--×   simp only [the_bending_energy, the_bending_of_two]
--×   have pointwise : (fun place =>
--×         the_difference_along (the_difference_along fun p => bent p + number * other p) place
--×           * the_difference_along (the_difference_along fun p => bent p + number * other p) place)
--×       = fun place =>
--×         (the_difference_along (the_difference_along bent) place * the_difference_along (the_difference_along bent) place
--×           + 2 * (number * (the_difference_along (the_difference_along bent) place
--×               * the_difference_along (the_difference_along other) place)))
--×         + number * number * (the_difference_along (the_difference_along other) place
--×             * the_difference_along (the_difference_along other) place) :=
--×     funext fun place => by rw [the_second_difference_of_a_reading_moved, a_sum_squared]
--×   rw [pointwise, two_readings_summed_are_the_two_sums, two_readings_summed_are_the_two_sums,
--×     a_number_of_a_reading_summed steps (number * number), a_number_of_a_reading_summed steps 2,
--×     a_number_of_a_reading_summed steps number]

-- Episode13.lean, line 6396
--× theorem a_reading_that_climbs_does_not_come_round (steps : Nat) (round : comes_round steps (fun place => (place : Int))) :
--×     steps = 0 := by
--×   have h := round 0
--×   simp only [Nat.zero_add] at h
--×   omega

-- Episode13.lean, line 6404
--× theorem what_comes_round_comes_round_again (steps : Nat) (reading : Nat → Int) (round : comes_round steps reading) :
--×     ∀ (times place : Nat), reading (place + times * steps) = reading place
--×   | 0, place => by rw [Nat.zero_mul, Nat.add_zero]
--×   | times + 1, place => by
--×     rw [Nat.succ_mul, ← Nat.add_assoc, round, what_comes_round_comes_round_again steps reading round times place]

-- Episode13.lean, line 6410
--× theorem squares_summed_are_never_under_nothing (steps : Nat) (reading : Nat → Int) :
--×     0 ≤ summed_along steps (fun place => reading place * reading place) := by
--×   induction steps with
--×   | zero => exact Int.le_refl 0
--×   | succ steps ih =>
--×     have sq := a_square_is_never_under_nothing (reading steps)
--×     simp only [summed_along]; omega

-- Episode13.lean, line 6418
--× theorem squares_that_sum_to_nothing_are_each_nothing (steps : Nat) (reading : Nat → Int)
--×     (nothing : summed_along steps (fun place => reading place * reading place) = 0) :
--×     ∀ place, place < steps → reading place = 0 := by
--×   induction steps with
--×   | zero => intro place h; omega
--×   | succ steps ih =>
--×     have before := squares_summed_are_never_under_nothing steps reading
--×     have sq := a_square_is_never_under_nothing (reading steps)
--×     simp only [summed_along] at nothing
--×     have last : reading steps * reading steps = 0 := by omega
--×     have rest : summed_along steps (fun place => reading place * reading place) = 0 := by omega
--×     intro place h
--×     rcases Nat.lt_succ_iff_lt_or_eq.mp h with below | here
--×     · exact ih rest place below
--×     · rw [here]; rcases Int.mul_eq_zero.mp last with z | z <;> exact z

-- Episode13.lean, line 6434
--× theorem stationary_against_all_that_comes_round_is_the_stencil_nothing (steps : Nat) (positive : 0 < steps)
--×     (bent : Nat → Int) (bent_round : comes_round steps bent)
--×     (stationary : ∀ other, comes_round steps other → the_bending_of_two steps bent other = 0) :
--×     ∀ place, the_difference_along (the_difference_along (the_difference_along (the_difference_along bent))) place = 0 := by
--×   have d4 := the_difference_comes_round steps _ (the_difference_comes_round steps _
--×     (the_difference_comes_round steps _ (the_difference_comes_round steps bent bent_round)))
--×   let fourth := the_difference_along (the_difference_along (the_difference_along (the_difference_along bent)))
--×   let other : Nat → Int := fun place => fourth (place + (2 * steps - 2))
--×   have other_round : comes_round steps other := fun place => by
--×     show fourth (place + steps + (2 * steps - 2)) = fourth (place + (2 * steps - 2))
--×     rw [show place + steps + (2 * steps - 2) = place + (2 * steps - 2) + steps by omega]; exact d4 _
--×   have two_on : ∀ place, one_place_on (one_place_on other) place = fourth place := fun place => by
--×     show fourth (place + 1 + 1 + (2 * steps - 2)) = fourth place
--×     rw [show place + 1 + 1 + (2 * steps - 2) = place + 2 * steps by omega]
--×     exact what_comes_round_comes_round_again steps fourth d4 2 place
--×   have h := stationary other other_round
--×   rw [the_bending_of_two, the_variation_of_the_bending_is_the_fourth_difference steps bent other bent_round other_round] at h
--×   have squares : summed_along steps (fun place => fourth place * fourth place) = 0 := by
--×     have same : (fun place => the_difference_along (the_difference_along (the_difference_along (the_difference_along bent))) place
--×           * one_place_on (one_place_on other) place) = fun place => fourth place * fourth place :=
--×       funext fun place => by rw [two_on]
--×     rw [same] at h; exact h
--×   have inside := squares_that_sum_to_nothing_are_each_nothing steps fourth squares
--×   intro place
--×   have again := what_comes_round_comes_round_again steps fourth d4 (place / steps) (place % steps)
--×   rw [Nat.mul_comm, Nat.mod_add_div] at again
--×   rw [show the_difference_along (the_difference_along (the_difference_along (the_difference_along bent))) place
--×         = fourth place from rfl, again]
--×   exact inside _ (Nat.mod_lt _ positive)

-- Episode13.lean, line 6477
--× def recovers {Case : Sort cases} {Evidence : Sort evidences} {Identification : Sort identifications}
--×     (admissible : Case → Prop) (what_is_kept : Case → Evidence) (identify : Case → Identification)
--×     (reader : Evidence → Identification) : Prop :=
--×   ∀ case, admissible case → reader (what_is_kept case) = identify case
--× def can_be_recovered {Case : Sort cases} {Evidence : Sort evidences} {Identification : Sort identifications}
--×     (admissible : Case → Prop) (what_is_kept : Case → Evidence) (identify : Case → Identification) : Prop :=
--×   ∃ reader, recovers admissible what_is_kept identify reader

-- Episode13.lean, line 6487
--× theorem the_same_kept_and_two_identifications_cannot_be_recovered
--×     {Case : Sort cases} {Evidence : Sort evidences} {Identification : Sort identifications}
--×     (admissible : Case → Prop) (what_is_kept : Case → Evidence) (identify : Case → Identification)
--×     (this that : Case) (this_is_admissible : admissible this) (that_is_admissible : admissible that)
--×     (the_same_is_kept : what_is_kept this = what_is_kept that) (identified_apart : identify this ≠ identify that) :
--×     ¬ can_be_recovered admissible what_is_kept identify := by
--×   intro ⟨reader, it_recovers⟩
--×   have here := it_recovers this this_is_admissible
--×   have there := it_recovers that that_is_admissible
--×   rw [the_same_is_kept] at here
--×   exact identified_apart (here.symm.trans there)

-- Episode13.lean, line 6533
--× theorem the_knowers_decision_cannot_be_recovered :
--×     ¬ can_be_recovered (fun _ : Bool => True) what_is_kept_of_a_decision (fun decision => decision) :=
--×   the_same_kept_and_two_identifications_cannot_be_recovered _ _ _ true false trivial trivial
--×     the_same_is_kept_of_both_decisions (by decide)

-- Episode13.lean, line 6539
--× theorem the_two_decisions_return_two_roots :
--×     you_re_a_daisy_if_you_do (bitFACT true) ≠ you_re_a_daisy_if_you_do (bitFACT false) := by decide

-- Episode13.lean, line 6545
--× def the_fact_a_name_names (the_old_rung : Bool) : FACT :=
--×   if the_old_rung then FACT.Truth else a_number_is_distinguished

-- Episode13.lean, line 6548
--× theorem the_name_of_the_first_rung_cannot_be_recovered :
--×     ¬ can_be_recovered (fun _ : Bool => True) the_fact_a_name_names (fun the_old_rung => the_old_rung) :=
--×   the_same_kept_and_two_identifications_cannot_be_recovered _ _ _ true false trivial trivial
--×     (show FACT.Truth = a_number_is_distinguished from asked_only_whether_it_is_true_the_number_is_the_truth.symm)
--×     (by decide)

-- Episode13.lean, line 6569
--× theorem the_quartic_at_the_devices_weights (x r : Int) :
--×     the_closing_quartic 18 5 x r = 325 * (x * x) - 180 * (r * r * x) + 18 * (r * r * (r * r)) := by
--×   show (5 : Int) * 5 * (18 - 5) * x * x - 2 * 18 * 5 * r * r * x + 18 * r * r * r * r = _
--×   have e1 : (5 : Int) * 5 * (18 - 5) * x * x = 325 * (x * x) := by
--×     rw [show (5 : Int) * 5 * (18 - 5) = 325 from rfl]; ac_nf
--×   have e2 : (2 : Int) * 18 * 5 * r * r * x = 180 * (r * r * x) := by
--×     rw [show (2 : Int) * 18 * 5 = 180 from rfl]; ac_nf
--×   have e3 : (18 : Int) * r * r * r * r = 18 * (r * r * (r * r)) := by ac_nf
--×   rw [e1, e2, e3]

-- Episode13.lean, line 6579
--× theorem eighteen_of_the_quartic_is_a_pair_by_itself_turned_over (x r : Int) :
--×     the_surd_product (18 * (r * r - 5 * x), 5 * x) (18 * (r * r - 5 * x), - (5 * x))
--×       = (18 * the_closing_quartic 18 5 x r, 0) := by
--×   have ninety := the_round_trip_is_ninety
--×   refine Prod.ext ?_ ?_
--×   · show 18 * (r * r - 5 * x) * (18 * (r * r - 5 * x)) + the_round_trip * (5 * x) * (- (5 * x))
--×         = 18 * the_closing_quartic 18 5 x r
--×     rw [ninety, the_quartic_at_the_devices_weights, Int.mul_neg]
--×     have a1 : 18 * (r * r - 5 * x) * (18 * (r * r - 5 * x))
--×         = 18 * 18 * ((r * r - 5 * x) * (r * r - 5 * x)) := two_by_two_is_one_by_one_twice _ _ _ _
--×     have a2 : (r * r - 5 * x) * (r * r - 5 * x)
--×         = r * r * (r * r) - 10 * (r * r * x) + 25 * (x * x) := by
--×       rw [Int.sub_mul, Int.mul_sub, Int.mul_sub]
--×       have b1 : r * r * (5 * x) = 5 * (r * r * x) := Int.mul_left_comm _ _ _
--×       have b2 : 5 * x * (r * r) = 5 * (r * r * x) := by rw [Int.mul_assoc, Int.mul_comm x (r * r)]
--×       have b3 : 5 * x * (5 * x) = 5 * 5 * (x * x) := two_by_two_is_one_by_one_twice _ _ _ _
--×       rw [b1, b2, b3]; omega
--×     have a3 : (90 : Int) * (5 * x) * (5 * x) = 90 * (5 * 5 * (x * x)) := by
--×       rw [Int.mul_assoc, two_by_two_is_one_by_one_twice]
--×     rw [a1, a2, a3]; omega
--×   · show 18 * (r * r - 5 * x) * (- (5 * x)) + 5 * x * (18 * (r * r - 5 * x)) = 0
--×     rw [Int.mul_neg, Int.mul_comm (5 * x) (18 * (r * r - 5 * x))]; omega

-- Episode13.lean, line 6603
--× theorem the_two_pairs_change_places_and_the_product_stays (x r : Int) :
--×     the_surd_product (18 * (r * r - 5 * x), - (5 * x)) (18 * (r * r - 5 * x), 5 * x)
--×       = the_surd_product (18 * (r * r - 5 * x), 5 * x) (18 * (r * r - 5 * x), - (5 * x)) := by
--×   refine Prod.ext ?_ ?_
--×   · show 18 * (r * r - 5 * x) * (18 * (r * r - 5 * x)) + the_round_trip * (- (5 * x)) * (5 * x)
--×         = 18 * (r * r - 5 * x) * (18 * (r * r - 5 * x)) + the_round_trip * (5 * x) * (- (5 * x))
--×     rw [Int.mul_neg, Int.neg_mul, Int.mul_neg]
--×   · show 18 * (r * r - 5 * x) * (5 * x) + - (5 * x) * (18 * (r * r - 5 * x))
--×         = 18 * (r * r - 5 * x) * (- (5 * x)) + 5 * x * (18 * (r * r - 5 * x))
--×     rw [Int.mul_neg, Int.neg_mul, Int.mul_comm (5 * x) (18 * (r * r - 5 * x))]; omega

-- Episode13.lean, line 6629
--× theorem the_table_turned_over_reads_the_same :
--×     the_table_trace the_full_other_table = the_table_trace the_full_table
--×       ∧ the_table_determinant the_full_other_table = the_table_determinant the_full_table
--×       ∧ the_gap_squared the_full_other_table = the_gap_squared the_full_table
--×       ∧ the_gap_squared the_full_table = 360 := by decide

-- Episode13.lean, line 6636
--× theorem turned_over_the_bent_card_by_the_quarter_turn_is_owed (a b : Bool) :
--×     the_full_other_table a b - the_full_table a b = - ((bent_card : Int) * the_quarter_turn a b) := by
--×   cases a <;> cases b <;> decide

-- Episode13.lean, line 6641
--× theorem the_roots_changed_places_read_the_same :
--×     the_surd_product the_hole the_outer_radius = the_surd_product the_outer_radius the_hole
--×       ∧ the_surd_product the_outer_radius the_hole = (234, 0)
--×       ∧ (the_hole.1 + the_outer_radius.1, the_hole.2 + the_outer_radius.2) = (36, 0)
--×       ∧ the_hole.2 = - the_outer_radius.2 := by decide

-- Episode13.lean, line 6649
--× def the_four_signed_states : List (Bool × Bool) := [(true, true), (true, false), (false, true), (false, false)]
--× def what_is_read_of_a_signed_state (state : Bool × Bool) : Int × Int × Int × (Int × Int) × (Int × Int) :=
--×   let table := if state.2 then the_full_table else the_full_other_table
--×   let first := if state.1 then the_outer_radius else the_hole
--×   let second := if state.1 then the_hole else the_outer_radius
--×   (the_table_trace table, the_table_determinant table, the_gap_squared table,
--×    (first.1 + second.1, first.2 + second.2), the_surd_product first second)

-- Episode13.lean, line 6657
--× theorem the_four_signed_states_read_alike :
--×     the_four_signed_states.map what_is_read_of_a_signed_state
--×       = List.replicate 4 (36, 234, 360, (36, 0), (234, 0)) := by decide

-- Episode13.lean, line 6664
--× theorem the_triple_does_not_read_which_way_the_arm_crosses :
--×     ∀ a : Bool,
--×       (the_knowers_triple.holds (assignFrom [a, true, false]) an_odd_number_are_true 0).1
--×           = (the_knowers_triple.holds (assignFrom [a, false, true]) an_odd_number_are_true 0).1
--×         ∧ (the_knowers_triple.holds (assignFrom [a, true, false]) an_even_number_are_true 0).1
--×           = (the_knowers_triple.holds (assignFrom [a, false, true]) an_even_number_are_true 0).1 := by decide

-- Episode13.lean, line 6682
--× def carried_by_the_quarter_turn (A : Table) : Table :=
--×   fun a b => - the_table_product (the_table_product the_quarter_turn A) the_quarter_turn a b

-- Episode13.lean, line 6686
--× theorem carried_by_the_quarter_turn_the_table_reads_the_same :
--×     the_table_trace (carried_by_the_quarter_turn the_full_table) = 36
--×       ∧ the_table_determinant (carried_by_the_quarter_turn the_full_table) = 234
--×       ∧ the_gap_squared (carried_by_the_quarter_turn the_full_table) = 360 := by decide

-- Episode13.lean, line 6692
--× theorem carried_by_the_quarter_turn_it_is_turned_over_and_the_crossings_are_owed :
--×     ∀ a b : Bool, carried_by_the_quarter_turn the_full_table a b
--×       = if a = b then the_full_other_table a b else - the_full_other_table a b := by decide

-- Episode13.lean, line 6697
--× theorem carried_twice_the_table_is_back :
--×     ∀ a b : Bool, carried_by_the_quarter_turn (carried_by_the_quarter_turn the_full_table) a b = the_full_table a b := by
--×   decide

-- Episode13.lean, line 6703
--× theorem in_the_turns_the_quarter_turn_twice_is_the_whole_turn_owed :
--×     the_turns_product the_quarter_turn_turn the_quarter_turn_turn = the_whole_turn (-1)
--×       ∧ the_turns_conjugate the_quarter_turn_turn
--×           = the_turns_product (the_whole_turn (-1)) the_quarter_turn_turn := by decide

-- Episode13.lean, line 6709
--× theorem the_outer_radius_owed_is_not_the_hole :
--×     (- the_outer_radius.1, - the_outer_radius.2) ≠ the_hole
--×       ∧ (the_outer_radius.1, - the_outer_radius.2) = the_hole := by decide

-- Episode13.lean, line 6714
--× theorem the_place_off_the_frinkahedron_holds_no_bracket :
--×     (the_arms.filter fun place => !on_the_frinkahedron place) = [(false, false)] := by decide

-- Episode13.lean, line 6726
--× theorem the_table_turned_over_has_trace_thirty_six_and_determinant_four_hundred_and_fourteen :
--×     the_table_trace (turned_over the_full_table) = 36 ∧ the_table_determinant (turned_over the_full_table) = 414 := by decide

-- Episode13.lean, line 6729
--× theorem the_quarter_turn_as_a_number_twice_is_one_owed :
--×     (Meanings.ComplexReal.quarterTurn * Meanings.ComplexReal.quarterTurn).Same (-Meanings.ComplexReal.ofNat 1) :=
--×   Meanings.the_quarter_turn_twice_is_one_owed

-- Episode13.lean, line 6733
--× theorem the_turned_tables_polynomial_holds_nothing_at_its_two_roots_and_not_at_eighteen :
--×     (Meanings.theTurnedPolynomialAt Meanings.theTurnedRoot).HoldsNothingAt 0
--×       ∧ (Meanings.theTurnedPolynomialAt Meanings.theOtherTurnedRoot).HoldsNothingAt 0
--×       ∧ ¬ (Meanings.theTurnedPolynomialAt (Meanings.ComplexReal.ofNat 18)).HoldsNothingAt 0 := by decide +kernel

-- Episode13.lean, line 6742
--× theorem the_turns_as_numbers :
--×     (Meanings.QuaternionReal.i * Meanings.QuaternionReal.j).Same Meanings.QuaternionReal.k
--×       ∧ (Meanings.QuaternionReal.j * Meanings.QuaternionReal.i).Same (-Meanings.QuaternionReal.k)
--×       ∧ (Meanings.QuaternionReal.k * Meanings.QuaternionReal.k).Same (-Meanings.QuaternionReal.ofNat 1)
--×       ∧ ¬ (Meanings.QuaternionReal.i * Meanings.QuaternionReal.j).Same (Meanings.QuaternionReal.j * Meanings.QuaternionReal.i) :=
--×   ⟨Meanings.i_by_j_is_k, Meanings.j_by_i_is_k_owed, Meanings.k_twice_is_one_owed, Meanings.i_by_j_is_not_j_by_i⟩

-- Episode13.lean, line 6764
--× theorem the_exponential_is_its_own_first_variation (n k : Nat) :
--×     (n + 1) ^ (k + 1) = n * (n + 1) ^ k + (n + 1) ^ k := by
--×   rw [Nat.pow_succ, Nat.mul_succ, Nat.mul_comm]

-- Episode13.lean, line 6770
--× theorem the_turning_exponential_steps_by_itself_turned_a_quarter (n : Int) (z : Int × Int) :
--×     the_gaussian_product z (the_step_of_a_turn n)
--×       = (n * z.1 + (the_gaussian_product z the_quarter_phase).1, n * z.2 + (the_gaussian_product z the_quarter_phase).2) := by
--×   simp only [the_gaussian_product, the_quarter_phase, the_step_of_a_turn]
--×   refine Prod.ext ?_ ?_ <;> dsimp only <;> simp only [Int.mul_one, Int.mul_zero, Int.add_zero,
--×     Int.zero_sub, Int.mul_comm z.1 n, Int.mul_comm z.2 n] <;> omega

-- Episode13.lean, line 6777
--× theorem the_radius_grows_by_the_step_squared (n : Int) (k : Nat) :
--×     the_gaussian_norm (the_phase_walk (the_step_of_a_turn n) k) = (n * n + 1) ^ k := by
--×   induction k with
--×   | zero => simp [the_phase_walk, the_gaussian_norm]
--×   | succ k ih =>
--×     show the_gaussian_norm (the_gaussian_product _ _) = _
--×     rw [the_norm_of_a_product, ih, Int.pow_succ]
--×     simp only [the_gaussian_norm, the_step_of_a_turn]
--×     rw [Int.one_mul]

-- Episode13.lean, line 6787
--× theorem the_turn_leaves_the_circle_by_the_step_squared (n : Int) (k : Nat) :
--×     the_gaussian_norm (the_phase_walk (the_step_of_a_turn n) (k + 1))
--×       = n * n * the_gaussian_norm (the_phase_walk (the_step_of_a_turn n) k)
--×           + the_gaussian_norm (the_phase_walk (the_step_of_a_turn n) k) := by
--×   rw [the_radius_grows_by_the_step_squared, the_radius_grows_by_the_step_squared, Int.pow_succ, Int.mul_add, Int.mul_one,
--×     Int.mul_comm]

-- Episode13.lean, line 6804
--× theorem the_eight_are_a_coin_and_an_arm :
--×     the_connected_steps.map the_clock_of_a_step
--×       = the_two_coins.flatMap fun coin => the_arms.map fun arm => (coin, arm.1, arm.2) := by decide

-- Episode13.lean, line 6809
--× def the_clock_holds_when_an_odd_number_are_true (clock : Bool × Bool × Bool) : Bool :=
--×   (the_knowers_triple.holds (assignFrom [clock.1, clock.2.1, clock.2.2]) an_odd_number_are_true 0).1
--× def the_clock_holds_when_an_even_number_are_true (clock : Bool × Bool × Bool) : Bool :=
--×   (the_knowers_triple.holds (assignFrom [clock.1, clock.2.1, clock.2.2]) an_even_number_are_true 0).1

-- Episode13.lean, line 6815
--× theorem four_of_the_eight_hold_and_four_do_not :
--×     ((the_connected_steps.map the_clock_of_a_step).filter the_clock_holds_when_an_odd_number_are_true).length = 4
--×       ∧ ((the_connected_steps.map the_clock_of_a_step).filter the_clock_holds_when_an_even_number_are_true).length = 4
--×       ∧ ∀ clock ∈ the_connected_steps.map the_clock_of_a_step,
--×           the_clock_holds_when_an_odd_number_are_true clock = !the_clock_holds_when_an_even_number_are_true clock := by
--×   decide

-- Episode13.lean, line 6823
--× theorem for_every_arm_one_coin_holds :
--×     ∀ arm ∈ the_arms,
--×       the_clock_holds_when_an_odd_number_are_true (true, arm.1, arm.2)
--×         = !the_clock_holds_when_an_odd_number_are_true (false, arm.1, arm.2) := by decide

-- Episode13.lean, line 6829
--× theorem the_coin_that_holds_is_whether_the_arm_is_level :
--×     the_arms.map (fun arm => the_clock_holds_when_an_odd_number_are_true (true, arm.1, arm.2))
--×       = the_arms.map (fun arm => arm.1 == arm.2) := by decide

-- Episode13.lean, line 6842
--× def turned_in_space (step : (Bool × Bool) × (Bool × Bool)) : (Bool × Bool) × (Bool × Bool) :=
--×   ((!step.1.1, !step.1.2), (!step.2.1, !step.2.2))
--× def turned_in_time (step : (Bool × Bool) × (Bool × Bool)) : (Bool × Bool) × (Bool × Bool) :=
--×   ((step.2.2, step.2.1), (step.1.2, step.1.1))

-- Episode13.lean, line 6849
--× def over_or_short (step : (Bool × Bool) × (Bool × Bool)) : Int :=
--×   (compute_the_area_of (what_execute_counts step) : Int) - compute_the_area_of (what_compile_builds step)

-- Episode13.lean, line 6853
--× theorem turned_either_way_a_connected_step_is_connected :
--×     ((the_connected_steps.map turned_in_space).all fun step => the_connected_steps.contains step) = true
--×       ∧ ((the_connected_steps.map turned_in_time).all fun step => the_connected_steps.contains step) = true := by decide

-- Episode13.lean, line 6859
--× def the_clock_step : (Bool × Bool) × (Bool × Bool) := ((true, false), (false, true))
--× def the_complement_step : (Bool × Bool) × (Bool × Bool) := ((false, true), (true, false))

-- Episode13.lean, line 6862
--× theorem the_clock_is_over_by_the_bent_card_and_its_complement_is_short :
--×     over_or_short the_clock_step = bent_card ∧ over_or_short the_complement_step = - (bent_card : Int) := by decide

-- Episode13.lean, line 6866
--× theorem turned_in_space_the_clock_is_its_complement :
--×     turned_in_space the_clock_step = the_complement_step ∧ turned_in_space the_complement_step = the_clock_step
--×       ∧ over_or_short (turned_in_space the_clock_step) = - over_or_short the_clock_step := by decide

-- Episode13.lean, line 6871
--× theorem turned_in_time_the_clock_is_the_clock :
--×     turned_in_time the_clock_step = the_clock_step ∧ turned_in_time the_complement_step = the_complement_step := by decide

-- Episode13.lean, line 6875
--× theorem the_turn_in_time_leaves_what_is_read_only_of_the_clock_and_its_complement :
--×     (the_connected_steps.filter fun step =>
--×         over_or_short step != 0 && over_or_short (turned_in_time step) == over_or_short step)
--×       = [the_clock_step, the_complement_step] := by decide

-- Episode13.lean, line 6892
--× def by_their_differences (this that : Direction → Int) : Int :=
--×   (the_pairs_of_arms.map fun pair => (this pair.1 - this pair.2) * (that pair.1 - that pair.2)).foldl (· + ·) 0

-- Episode13.lean, line 6896
--× def the_weight_on_the_arm (arm : Direction) : Int := the_arm_weight arm.1 arm.2
--× def one_fencepost_on_the_arm (_ : Direction) : Int := 1

-- Episode13.lean, line 6900
--× theorem one_fencepost_on_every_arm_is_at_right_angles_to_the_weight :
--×     by_their_differences one_fencepost_on_the_arm the_weight_on_the_arm = 0
--×       ∧ by_their_differences one_fencepost_on_the_arm one_fencepost_on_the_arm = 0 := by decide

-- Episode13.lean, line 6905
--× theorem one_fencepost_on_every_arm_is_at_right_angles_to_everything (that : Direction → Int) :
--×     by_their_differences one_fencepost_on_the_arm that = 0 := by
--×   simp only [by_their_differences, the_pairs_of_arms, one_fencepost_on_the_arm, List.map, List.foldl]
--×   omega

-- Episode13.lean, line 6911
--× theorem the_weight_by_its_differences_is_three_bent_cards_squared :
--×     by_their_differences the_weight_on_the_arm the_weight_on_the_arm = 3 * ((bent_card : Int) * bent_card) := by decide

-- Episode13.lean, line 6926
--× theorem a_page_is_two_facts_and_the_page_before (planted polynomial : FACT) (the_page_before : ThePreprint.{0}) :
--×     (ThePreprint.methodology planted polynomial Prop Type the_page_before).all_the_way_down
--×       = [planted, polynomial] ++ the_page_before.all_the_way_down := rfl

-- Episode13.lean, line 6931
--× theorem two_facts_a_page_and_one_more (tape : List FACT) :
--×     (the_preprint_a_list_indicates tape).all_the_way_down.length = 2 * tape.length + 1 := by
--×   induction tape with
--×   | nil => rfl
--×   | cons fact rest ih =>
--×     simp only [the_preprint_a_list_indicates, ThePreprint.all_the_way_down, List.length_append, List.length_cons,
--×       List.length_nil, ih]
--×     omega

-- Episode13.lean, line 6941
--× theorem thirty_five_rebuttals_are_thirty_six_pages :
--×     (the_preprint_a_list_indicates (List.replicate 35 FACT.Truth)).the_model.length = 36
--×       ∧ (the_preprint_a_list_indicates (List.replicate 35 FACT.Truth)).all_the_way_down.length = 71 := by
--×   rw [the_preprint_reads_back, two_facts_a_page_and_one_more]; simp only [List.length_replicate]; decide

-- Episode13.lean, line 6947
--× theorem counted_up_is_counted_down_and_the_fencepost (tape : List FACT) :
--×     (the_preprint_a_list_indicates tape).the_model.length = tape.length + the_fencepost_bug := by
--×   rw [the_preprint_reads_back]; show 1 * tape.length + 1 = tape.length + 1; omega

-- Episode13.lean, line 6962
--× theorem what_a_rebuttal_holds {Box : Type} {Pigeon : CarrierProcess Box} {page next_page : Nat}
--×     (planted polynomial : FACT) (argument : REVIEWED Box Pigeon next_page) :
--×     (rebut (page := page) planted polynomial argument).rebuttal
--×       = .methodology planted polynomial Box (ULift.{1, 0} Box) argument.rebuttal := rfl

-- Episode13.lean, line 6968
--× theorem set_in_type_a_rebuttal_is_its_two_facts_and_that_they_agree
--×     {Box : Type} {Pigeon : CarrierProcess Box} {page next_page rung : Nat} {Lifted : Type}
--×     (planted polynomial : FACT) (argument : REVIEWED Box Pigeon next_page) (accepted : TYPESET Box Pigeon rung Lifted) :
--×     (set_in_type (rebut (page := page) planted polynomial argument).rebuttal accepted).the_page
--×       = .results planted polynomial (planted.truth ↔ polynomial.truth) Box (ULift.{1, 0} Box)
--×           (ULift.{1, 1} (ULift.{1, 0} Box)) accepted.the_page := rfl

-- Episode13.lean, line 6976
--× theorem set_in_type_the_count_goes_up_by_one
--×     {Box : Type} {Pigeon : CarrierProcess Box} {rung : Nat} {Lifted : Type}
--×     (the_rebuttal : ThePreprint) (accepted : TYPESET Box Pigeon rung Lifted) :
--×     (set_in_type the_rebuttal accepted).universe_id = .one Pigeon.symbol accepted.universe_id := rfl

-- Episode13.lean, line 6983
--× theorem counted_up_a_page_is_three_facts_and_counted_down_two
--×     (planted polynomial : FACT) (agree : Prop) (below : ThePreprint.{0}) :
--×     (ThePreprint.results planted polynomial agree Prop Type Type below).all_the_way_down
--×         = [planted, polynomial, FACT.Truth] ++ below.all_the_way_down
--×       ∧ (ThePreprint.methodology planted polynomial Prop Type below).all_the_way_down
--×         = [planted, polynomial] ++ below.all_the_way_down := ⟨rfl, rfl⟩

-- Episode13.lean, line 6991
--× theorem one_fact_twice_agrees_and_nothing_is_inferred (fact : FACT) : fact.truth ↔ fact.truth := Iff.rfl

-- Episode13.lean, line 6994
--× theorem two_facts_need_not_agree : ∃ planted polynomial : FACT, ¬ (planted.truth ↔ polynomial.truth) :=
--×   ⟨{ truth := True, click := .isTrue trivial }, { truth := False, click := .isFalse id }, fun agree => agree.mp trivial⟩

-- Episode13.lean, line 6998
--× theorem two_facts_that_hold_agree (planted polynomial : FACT) (the_one : planted.truth) (the_other : polynomial.truth) :
--×     planted.truth ↔ polynomial.truth := ⟨fun _ => the_other, fun _ => the_one⟩

-- Episode13.lean, line 7012
--× theorem the_manuscript_is_three_facts : theManuscript.all_the_way_down.length = 3 := by decide

-- Episode13.lean, line 7015
--× theorem counted_down_the_review_is_two_facts_a_page_on_the_manuscript :
--×     page01.rebuttal.all_the_way_down.length = 2 * 35 + theManuscript.all_the_way_down.length := by decide

-- Episode13.lean, line 7019
--× set_option maxRecDepth 100000 in
--× theorem counted_up_the_ascent_is_three_facts_a_page_on_the_review :
--×     theTopOfTheLedger.the_page.all_the_way_down.length = 3 * 35 + page01.rebuttal.all_the_way_down.length := by decide

-- Episode13.lean, line 7025
--× set_option maxRecDepth 100000 in
--× theorem the_ascent_adds_one_fact_a_page_more_than_the_review :
--×     (theTopOfTheLedger.the_page.all_the_way_down.length - page01.rebuttal.all_the_way_down.length)
--×       - (page01.rebuttal.all_the_way_down.length - theManuscript.all_the_way_down.length) = 35 := by decide

-- Episode13.lean, line 7031
--× set_option maxRecDepth 100000 in
--× theorem in_pages_each_computation_is_thirty_five :
--×     theManuscript.the_model.length = 2
--×       ∧ page01.rebuttal.the_model.length = 35 + theManuscript.the_model.length
--×       ∧ theTopOfTheLedger.the_page.the_model.length = 35 + page01.rebuttal.the_model.length := by decide

-- Episode13.lean, line 7038
--× theorem the_ascent_stands_on_the_review :
--×     (THE_GOSPEL.TYPESET_Episode1_FACT FACT the_representation.the_first_card (the_naotrino_theory := page01)).the_page
--×       = page01.rebuttal := rfl

-- Episode13.lean, line 7055
--× theorem the_action_in_first_differences_varies_by_the_second (steps : Nat) (reading moved : Nat → Int)
--×     (reading_round : comes_round steps reading) (moved_round : comes_round steps moved) :
--×     summed_along steps (fun place => the_difference_along reading place * the_difference_along moved place)
--×       = - summed_along steps
--×           (fun place => the_difference_along (the_difference_along reading) place * one_place_on moved place) :=
--×   by_parts_for_what_comes_round steps (the_difference_along reading) moved
--×     (the_difference_comes_round steps reading reading_round) moved_round

-- Episode13.lean, line 7063
--× theorem the_second_difference_reads_three_places (reading : Nat → Int) (place : Nat) :
--×     the_difference_along (the_difference_along reading) place
--×       = reading (place + 1 + 1) - 2 * reading (place + 1) + reading place := by
--×   simp only [the_difference_along]; omega

-- Episode13.lean, line 7070
--× theorem at_the_speed_of_one_there_is_no_factor (whole : Int) (not_nothing : whole ≠ 0) :
--×     ¬ ∃ factor_squared : Int, (whole - whole) * factor_squared = whole := by
--×   intro ⟨factor_squared, held⟩; simp at held; exact not_nothing held.symm

-- Episode13.lean, line 7075
--× def the_third_difference_on_four_steps (reading : Int → Int) (place : Int) : Int :=
--×   reading (place + 1) - 3 * reading place + 3 * reading (place - 1) - reading (place - 2)

-- Episode13.lean, line 7079
--× theorem shifted_the_third_difference_is_itself_at_the_shifted_place (reading : Int → Int) (by_this place : Int) :
--×     the_third_difference_on_four_steps (fun x => reading (x + by_this)) place
--×       = the_third_difference_on_four_steps reading (place + by_this) := by
--×   simp only [the_third_difference_on_four_steps]
--×   have h1 : place + 1 + by_this = place + by_this + 1 := by omega
--×   have h2 : place - 1 + by_this = place + by_this - 1 := by omega
--×   have h3 : place - 2 + by_this = place + by_this - 2 := by omega
--×   rw [h1, h2, h3]

-- Episode13.lean, line 7089
--× theorem turned_end_for_end_the_third_difference_is_owed (reading : Int → Int) (place : Int) :
--×     the_third_difference_on_four_steps (fun x => reading (- x)) place
--×       = - the_third_difference_on_four_steps reading (1 - place) := by
--×   simp only [the_third_difference_on_four_steps]
--×   have h1 : -(place + 1) = 1 - place - 2 := by omega
--×   have h2 : -place = 1 - place - 1 := by omega
--×   have h3 : -(place - 1) = 1 - place := by omega
--×   have h4 : -(place - 2) = 1 - place + 1 := by omega
--×   rw [h1, h2, h3, h4]; omega

-- Episode13.lean, line 7100
--× theorem the_fourth_difference_is_the_step_of_the_third (reading : Int → Int) (place : Int) :
--×     the_fourth_difference reading place
--×       = the_third_difference_on_four_steps reading (place + 1) - the_third_difference_on_four_steps reading place := by
--×   simp only [the_fourth_difference, the_third_difference_on_four_steps]
--×   have h1 : place + 1 - 1 = place := by omega
--×   have h2 : place + 1 - 2 = place - 1 := by omega
--×   have h3 : place - 1 - 1 = place - 2 := by omega
--×   rw [h1, h2, h3]; omega

-- Episode13.lean, line 7110
--× theorem shifted_the_fourth_difference_is_itself_at_the_shifted_place (reading : Int → Int) (by_this place : Int) :
--×     the_fourth_difference (fun x => reading (x + by_this)) place = the_fourth_difference reading (place + by_this) := by
--×   rw [the_fourth_difference_is_the_step_of_the_third, the_fourth_difference_is_the_step_of_the_third,
--×     shifted_the_third_difference_is_itself_at_the_shifted_place, shifted_the_third_difference_is_itself_at_the_shifted_place]
--×   have h : place + 1 + by_this = place + by_this + 1 := by omega
--×   rw [h]

-- Episode13.lean, line 7117
--× theorem turned_end_for_end_the_fourth_difference_is_itself (reading : Int → Int) (place : Int) :
--×     the_fourth_difference (fun x => reading (- x)) place = the_fourth_difference reading (- place) := by
--×   rw [the_fourth_difference_is_the_step_of_the_third, the_fourth_difference_is_the_step_of_the_third,
--×     turned_end_for_end_the_third_difference_is_owed, turned_end_for_end_the_third_difference_is_owed]
--×   have h1 : 1 - (place + 1) = - place := by omega
--×   have h2 : 1 - place = - place + 1 := by omega
--×   rw [h1, h2]; omega

-- Episode13.lean, line 7127
--× theorem on_a_cubic_the_third_difference_goes_as_the_step_cubed (a b c d place step : Int) :
--×     (a + b * (place + step) + c * ((place + step) * (place + step))
--×         + d * ((place + step) * (place + step) * (place + step)))
--×       - ((a + b * place + c * (place * place) + d * (place * place * place))
--×           + (a + b * place + c * (place * place) + d * (place * place * place))
--×           + (a + b * place + c * (place * place) + d * (place * place * place)))
--×       + ((a + b * (place - step) + c * ((place - step) * (place - step))
--×             + d * ((place - step) * (place - step) * (place - step)))
--×           + (a + b * (place - step) + c * ((place - step) * (place - step))
--×             + d * ((place - step) * (place - step) * (place - step)))
--×           + (a + b * (place - step) + c * ((place - step) * (place - step))
--×             + d * ((place - step) * (place - step) * (place - step))))
--×       - (a + b * (place - (step + step)) + c * ((place - (step + step)) * (place - (step + step)))
--×           + d * ((place - (step + step)) * (place - (step + step)) * (place - (step + step))))
--×       = 6 * (d * (step * step * step)) := by
--×   have key : ∀ cube : Int, cube = d * (step * step * step) →
--×       (a + b * (place + step) + c * ((place + step) * (place + step))
--×         + d * ((place + step) * (place + step) * (place + step)))
--×       - ((a + b * place + c * (place * place) + d * (place * place * place))
--×           + (a + b * place + c * (place * place) + d * (place * place * place))
--×           + (a + b * place + c * (place * place) + d * (place * place * place)))
--×       + ((a + b * (place - step) + c * ((place - step) * (place - step))
--×             + d * ((place - step) * (place - step) * (place - step)))
--×           + (a + b * (place - step) + c * ((place - step) * (place - step))
--×             + d * ((place - step) * (place - step) * (place - step)))
--×           + (a + b * (place - step) + c * ((place - step) * (place - step))
--×             + d * ((place - step) * (place - step) * (place - step))))
--×       - (a + b * (place - (step + step)) + c * ((place - (step + step)) * (place - (step + step)))
--×           + d * ((place - (step + step)) * (place - (step + step)) * (place - (step + step))))
--×       = cube + cube + cube + cube + cube + cube := by
--×     intro cube held; subst held
--×     simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul]
--×     ac_nf
--×     omega
--×   rw [key _ rfl]; omega

-- Episode13.lean, line 7165
--× def two_places_changed (reading : Int → Int) : Int → Int :=
--×   fun x => if x = 0 then reading 1 else if x = 1 then reading 0 else reading x

-- Episode13.lean, line 7168
--× theorem with_two_places_changed_a_line_is_not_stationary :
--×     the_fourth_difference (two_places_changed fun y => y) 0 = 10 ∧ the_fourth_difference (fun y => y) 0 = 0 := by decide

-- Episode13.lean, line 7173
--× theorem a_difference_summed_is_the_end_less_the_first (reading : Nat → Int) :
--×     ∀ steps, summed_along steps (the_difference_along reading) = reading steps - reading 0
--×   | 0 => by simp [summed_along]
--×   | steps + 1 => by
--×     simp only [summed_along, a_difference_summed_is_the_end_less_the_first reading steps, the_difference_along]; omega

-- Episode13.lean, line 7191
--× def the_same_difference_quantum : Bullshit.{0,0,0,0} := .zero SAME_DIFFERENCE

-- Episode13.lean, line 7194
--× noncomputable def gawked_at_once : Bullshit.{0,0,0,0} := the_atreyu_process.gawk_at the_same_difference_quantum
--× noncomputable def gawked_at_twice : Bullshit.{0,0,0,0} := the_atreyu_process.gawk_at gawked_at_once
--× noncomputable def gawked_at_three_times : Bullshit.{0,0,0,0} := the_atreyu_process.gawk_at gawked_at_twice
--× noncomputable def gawked_at_four_times : Bullshit.{0,0,0,0} := the_atreyu_process.gawk_at gawked_at_three_times

-- Episode13.lean, line 7200
--× theorem gawked_at_once_it_is_the_first_page :
--×     ∃ (fact : FACT) (page : Number) (proof book : ThePreprint) (constant : Bullshit),
--×       gawked_at_once = .one fact page proof book constant := ⟨_, _, _, _, _, rfl⟩

-- Episode13.lean, line 7205
--× theorem gawked_at_again_it_is_the_rest_of_the_call :
--×     (∃ f g p a b c s t x y, gawked_at_twice = Bullshit.rest_call f g p a b c s t x y)
--×       ∧ (∃ f g p a b c s t x y, gawked_at_three_times = Bullshit.rest_call f g p a b c s t x y)
--×       ∧ (∃ f g p a b c s t x y, gawked_at_four_times = Bullshit.rest_call f g p a b c s t x y) :=
--×   ⟨⟨_, _, _, _, _, _, _, _, _, _, rfl⟩, ⟨_, _, _, _, _, _, _, _, _, _, rfl⟩, ⟨_, _, _, _, _, _, _, _, _, _, rfl⟩⟩

-- Episode13.lean, line 7213
--× noncomputable def the_first_closure : Closure := the_equivalence_process.do_you_believe_it? gawked_at_once gawked_at_twice
--× noncomputable def the_second_closure : Closure :=
--×   the_equivalence_process.do_you_believe_it? gawked_at_twice gawked_at_three_times
--× noncomputable def the_third_closure : Closure :=
--×   the_equivalence_process.do_you_believe_it? gawked_at_three_times gawked_at_four_times

-- Episode13.lean, line 7220
--× theorem the_three_closures_are_differences :
--×     (∃ fact, the_first_closure = .different fact gawked_at_once gawked_at_twice (some (gawked_at_once < gawked_at_twice)))
--×       ∧ (∃ fact, the_second_closure
--×           = .different fact gawked_at_twice gawked_at_three_times (some (gawked_at_twice < gawked_at_three_times)))
--×       ∧ (∃ fact, the_third_closure
--×           = .different fact gawked_at_three_times gawked_at_four_times
--×               (some (gawked_at_three_times < gawked_at_four_times))) :=
--×   ⟨⟨_, rfl⟩, ⟨_, rfl⟩, ⟨_, rfl⟩⟩

-- Episode13.lean, line 7230
--× theorem three_closures_three_cells :
--×     the_first_closure.infer.length + the_second_closure.infer.length + the_third_closure.infer.length = 3 := rfl

-- Episode13.lean, line 7234
--× set_option maxRecDepth 100000 in
--× theorem what_the_four_gawks_hold :
--×     [the_same_difference_quantum, gawked_at_once, gawked_at_twice, gawked_at_three_times, gawked_at_four_times].map
--×         (fun gawk => gawk.all_the_way_down.length)
--×       = [1, 22, 39, 38, 39] := by decide

-- Episode13.lean, line 7250
--× def how_the_pages_set_in_type_click : ThePreprint → List (Bool × Bool)
--×   | .introduction _ _ => []
--×   | .methodology _ _ _ _ _ => []
--×   | .results before after _ _ _ _ below => (before.bit, after.bit) :: how_the_pages_set_in_type_click below

-- Episode13.lean, line 7256
--× def how_the_rebuttals_click : ThePreprint → List (Bool × Bool)
--×   | .introduction _ _ => []
--×   | .methodology planted polynomial _ _ before => (planted.bit, polynomial.bit) :: how_the_rebuttals_click before
--×   | .results _ _ _ _ _ _ below => how_the_rebuttals_click below

-- Episode13.lean, line 7262
--× set_option maxRecDepth 100000 in
--× theorem thirty_four_agree_and_the_top_page_is_true_on_false :
--×     how_the_pages_set_in_type_click theTopOfTheLedger.the_page = (true, false) :: List.replicate 34 (true, true) := by
--×   decide

-- Episode13.lean, line 7269
--× set_option maxRecDepth 100000 in
--× theorem every_rebuttal_clicks_twice_and_the_manuscript_is_true_on_false :
--×     how_the_rebuttals_click page01.rebuttal = List.replicate 35 (true, true) ++ [(true, false)]
--×       ∧ how_the_rebuttals_click theManuscript = [(true, false)] := by decide

-- Episode13.lean, line 7284
--× noncomputable def gawked_at_five_times : Bullshit.{0,0,0,0} := the_atreyu_process.gawk_at gawked_at_four_times

-- Episode13.lean, line 7287
--× theorem gawked_at_five_times_is_gawked_at_four : gawked_at_five_times = gawked_at_four_times := rfl

-- Episode13.lean, line 7289
--× noncomputable def the_fourth_closure : Closure :=
--×   the_equivalence_process.do_you_believe_it? gawked_at_four_times gawked_at_five_times

-- Episode13.lean, line 7293
--× theorem the_second_third_and_fourth_closures_store_one_proposition :
--×     (gawked_at_twice < gawked_at_three_times) = (gawked_at_three_times < gawked_at_four_times)
--×       ∧ (gawked_at_three_times < gawked_at_four_times) = (gawked_at_four_times < gawked_at_five_times) := ⟨rfl, rfl⟩

-- Episode13.lean, line 7298
--× theorem nothing_is_under_itself : ¬ (gawked_at_four_times < gawked_at_five_times) := fun under => under.2 under.1

-- Episode13.lean, line 7300
--× theorem what_three_closures_store_cannot_hold :
--×     ¬ (gawked_at_twice < gawked_at_three_times) ∧ ¬ (gawked_at_three_times < gawked_at_four_times)
--×       ∧ ¬ (gawked_at_four_times < gawked_at_five_times) :=
--×   have the_third : ¬ (gawked_at_three_times < gawked_at_four_times) :=
--×     the_second_third_and_fourth_closures_store_one_proposition.2 ▸ nothing_is_under_itself
--×   ⟨the_second_third_and_fourth_closures_store_one_proposition.1 ▸ the_third, the_third, nothing_is_under_itself⟩

-- Episode13.lean, line 7308
--× theorem what_the_first_closure_stores_holds : gawked_at_once < gawked_at_twice := ⟨trivial, fun over => over⟩

-- Episode13.lean, line 7311
--× set_option maxRecDepth 100000 in
--× theorem all_four_closures_click :
--×     [the_first_closure, the_second_closure, the_third_closure, the_fourth_closure].map
--×         (fun closure => closure.infer.map FACT.bit)
--×       = [[true], [true], [true], [true]] := by decide

-- Episode13.lean, line 7318
--× set_option maxRecDepth 100000 in
--× theorem the_values_differ :
--×     gawked_at_twice ≠ gawked_at_three_times ∧ gawked_at_three_times ≠ gawked_at_four_times :=
--×   ⟨fun same => absurd (congrArg (fun gawk => gawk.all_the_way_down.length) same) (by decide),
--×    fun same => absurd (congrArg (fun gawk => gawk.all_the_way_down.length) same) (by decide)⟩

-- Episode13.lean, line 7326
--× noncomputable def the_first_page_called_false : Bullshit.{0,0,0,0} :=
--×   match gawked_at_once with
--×   | .one _ page proof book constant => .one (bitFACT false) page proof book constant
--×   | other => other
--× noncomputable def called_false_and_gawked_at_once : Bullshit.{0,0,0,0} :=
--×   the_atreyu_process.gawk_at the_first_page_called_false
--× noncomputable def called_false_and_gawked_at_twice : Bullshit.{0,0,0,0} :=
--×   the_atreyu_process.gawk_at called_false_and_gawked_at_once
--× noncomputable def called_false_and_gawked_at_three_times : Bullshit.{0,0,0,0} :=
--×   the_atreyu_process.gawk_at called_false_and_gawked_at_twice

-- Episode13.lean, line 7338
--× theorem after_one_step_the_two_branches_are_one :
--×     called_false_and_gawked_at_twice = gawked_at_three_times
--×       ∧ called_false_and_gawked_at_three_times = gawked_at_four_times
--×       ∧ the_atreyu_process.gawk_at called_false_and_gawked_at_three_times = called_false_and_gawked_at_three_times :=
--×   ⟨rfl, rfl, rfl⟩

-- Episode13.lean, line 7346
--× def the_parts_of_a_first_page : Bullshit → List Nat
--×   | .one _ page proof book constant =>
--×       [1, page.all_the_way_down.length, proof.all_the_way_down.length, book.all_the_way_down.length,
--×        constant.all_the_way_down.length]
--×   | _ => []

-- Episode13.lean, line 7352
--× set_option maxRecDepth 100000 in
--× theorem the_first_page_holds_one_two_four_three_and_twelve :
--×     the_parts_of_a_first_page gawked_at_once = [1, 2, 4, 3, 12] := by decide

-- Episode13.lean, line 7366
--× def the_action_of_light_and_matter_at {n : Nat} (state : Site4 n → Turns) (U : Torus4 n)
--×     (this that way : Direction) (x : Site4 n) : Int × Turns × Turns :=
--×   (the_turns_action (the_square4 U this that x), the_state_carried_back state U way x, the_state_against_itself state x)

-- Episode13.lean, line 7370
--× theorem the_action_of_light_and_matter_is_left_by_a_turn_at_every_site {n : Nat} (state : Site4 n → Turns) (U : Torus4 n)
--×     (g : Site4 n → Turns) (unit : ∀ x, the_turns_norm (g x) = 1) (this that way : Direction) (x : Site4 n) :
--×     the_action_of_light_and_matter_at (the_gauged_state state g) (the_gauged_torus4 U g) this that way x
--×       = the_action_of_light_and_matter_at state U this that way x := by
--×   simp only [the_action_of_light_and_matter_at, the_gauged_square4 U g unit, a_unit_turn_leaves_the_action _ _ (unit _),
--×     the_state_carried_back_is_gauge_invariant state U g unit, the_state_against_itself_is_gauge_invariant state g unit]

-- Episode13.lean, line 7387
--× noncomputable def the_constant_in_a_jar : Jar := .color zero the_constant
--× noncomputable def the_physics_of_the_constant : Equivalation := .physics zero the_constant_in_a_jar

-- Episode13.lean, line 7391
--× theorem what_a_jar_holds_is_what_was_put_in (fact : FACT) (area : Area) : what_the_jar_holds (.color fact area) = area :=
--×   rfl

-- Episode13.lean, line 7395
--× theorem the_jar_holds_the_constant : what_the_jar_holds (.color zero the_constant) = the_constant :=
--×   what_a_jar_holds_is_what_was_put_in zero the_constant

-- Episode13.lean, line 7398
--× theorem counted_what_the_jar_holds_is_the_number :
--×     compute_the_area_of (what_the_jar_holds (.color zero the_constant)) = the_constant_factor_of_scaling_bullshit := by
--×   rw [what_a_jar_holds_is_what_was_put_in]; exact counted_the_constant_is_the_constant

-- Episode13.lean, line 7403
--× theorem the_physics_vanishes_to_one_fact : the_physics_of_the_constant.vanish = [zero] := rfl

-- Episode13.lean, line 7407
--× noncomputable def zero_like_on_the_constant : Equivalation := .zero_like zero the_physics_of_the_constant
--× noncomputable def one_like_on_the_constant : Equivalation :=
--×   .one_like (compute_the_area_of the_constant = the_constant_factor_of_scaling_bullshit) the_physics_of_the_constant
--×     the_physics_of_the_constant

-- Episode13.lean, line 7412
--× theorem the_physics_and_the_two_on_it_read_one_two_and_three :
--×     the_physics_of_the_constant.vanish.length = 1 ∧ zero_like_on_the_constant.vanish.length = 2
--×       ∧ one_like_on_the_constant.vanish.length = 3 := ⟨rfl, rfl, rfl⟩

-- Episode13.lean, line 7428
--× def the_steps_one_for_each_kind : List (List FACT) := the_steps_of_the_argument.drop 2

-- Episode13.lean, line 7430
--× theorem there_are_thirty_six_kinds : the_steps_one_for_each_kind.length = 36 := rfl

-- Episode13.lean, line 7434
--× theorem the_fifth_thirteenth_eighteenth_and_thirty_sixth :
--×     the_steps_one_for_each_kind[4]? = some ε₁.converge
--×       ∧ the_steps_one_for_each_kind[12]? = some ast₁.riemann_integrate
--×       ∧ the_steps_one_for_each_kind[17]? = some the_proof.equivalation
--×       ∧ the_steps_one_for_each_kind[35]? = some the_only_logical_inconsistency.infer := ⟨rfl, rfl, rfl, rfl⟩

-- Episode13.lean, line 7442
--× theorem the_four_posts_between_the_area_and_the_abstraction :
--×     (the_steps_one_for_each_kind.drop 13).take 4
--×       = [the_galerkin_method.solve, the_photon_worldline.classify, t₁.vanish, δδxᵢ.decode] := rfl

-- Episode13.lean, line 7448
--× theorem counted_from_the_back_the_same_four_numbers :
--×     the_coordinate_system.gauss.length = 5 ∧ the_coefficient_tape.length = 13 ∧ the_memory_tape.length = 18
--×       ∧ the_trace_of_truth_in_the_device = 36 := by decide

-- Episode13.lean, line 7454
--× theorem the_polynomial_from_either_end :
--×     an_exact_polynomial_description = 13 ∧ the_trace_of_truth_in_the_device = 36
--×       ∧ the_number_of_symbols_that_must_be_written_to_express_this = 18
--×       ∧ 13 + the_coordinate_system.gauss.length = 18 ∧ 2 * 18 = 36 := by decide

-- Episode13.lean, line 7467
--× def the_one_quadratic (x r : Int) : Int × Int := (18 * (r * r - 5 * x), 5 * x)
--× def the_other_quadratic (x r : Int) : Int × Int := (18 * (r * r - 5 * x), - (5 * x))

-- Episode13.lean, line 7471
--× theorem inflated_once_there_is_a_part_by_the_root (x r : Int) : (the_one_quadratic x r).2 = 5 * x := rfl

-- Episode13.lean, line 7474
--× theorem inflated_twice_nothing_is_left_by_the_root (x r : Int) :
--×     the_surd_product (the_one_quadratic x r) (the_other_quadratic x r) = (18 * the_closing_quartic 18 5 x r, 0) :=
--×   eighteen_of_the_quartic_is_a_pair_by_itself_turned_over x r

-- Episode13.lean, line 7479
--× theorem the_other_quadratic_is_the_one_turned_over (x r : Int) :
--×     the_other_quadratic x r = ((the_one_quadratic x r).1, - (the_one_quadratic x r).2)
--×       ∧ the_surd_product (the_other_quadratic x r) (the_one_quadratic x r)
--×           = the_surd_product (the_one_quadratic x r) (the_other_quadratic x r) :=
--×   ⟨rfl, the_two_pairs_change_places_and_the_product_stays x r⟩

-- Episode13.lean, line 7496
--× noncomputable def the_source_with_the_physics : type_of% rung16 := { rung16 with one := the_physics_of_the_constant }
--× noncomputable def the_source_with_the_zero_like : type_of% rung16 := { rung16 with one := zero_like_on_the_constant }
--× noncomputable def the_source_with_the_one_like : type_of% rung16 := { rung16 with one := one_like_on_the_constant }

-- Episode13.lean, line 7500
--× noncomputable def the_sixteenth_page_on_the_physics : REVIEWED FACT the_first_card 16 :=
--×   REVIEWER_2_REFUSES_TO_ENTERTAIN_ABSURD_SOURCES_OF_NOISE FACT the_first_card rung01 rung02 rung03 rung04 rung05 rung06 rung07 rung08 rung09 rung10 rung11 rung12 rung13 rung14 rung15 the_source_with_the_physics (argument := page17)
--× noncomputable def the_sixteenth_page_on_the_zero_like : REVIEWED FACT the_first_card 16 :=
--×   REVIEWER_2_REFUSES_TO_ENTERTAIN_ABSURD_SOURCES_OF_NOISE FACT the_first_card rung01 rung02 rung03 rung04 rung05 rung06 rung07 rung08 rung09 rung10 rung11 rung12 rung13 rung14 rung15 the_source_with_the_zero_like (argument := page17)
--× noncomputable def the_sixteenth_page_on_the_one_like : REVIEWED FACT the_first_card 16 :=
--×   REVIEWER_2_REFUSES_TO_ENTERTAIN_ABSURD_SOURCES_OF_NOISE FACT the_first_card rung01 rung02 rung03 rung04 rung05 rung06 rung07 rung08 rung09 rung10 rung11 rung12 rung13 rung14 rung15 the_source_with_the_one_like (argument := page17)

-- Episode13.lean, line 7508
--× theorem pushed_through_the_page_is_the_page :
--×     the_sixteenth_page_on_the_physics = page16 ∧ the_sixteenth_page_on_the_zero_like = page16
--×       ∧ the_sixteenth_page_on_the_one_like = page16 := ⟨rfl, rfl, rfl⟩

-- Episode13.lean, line 7514
--× theorem what_the_page_drew_is_the_zero_and_the_symbol :
--×     the_sixteenth_page_on_the_physics.rebuttal.all_the_way_down.take 1 = [zero]
--×       ∧ the_sixteenth_page_on_the_one_like.rebuttal.all_the_way_down.take 1 = [the_first_card.symbol] := ⟨rfl, rfl⟩

-- Episode13.lean, line 7525
--× def the_state_owed {n : Nat} (state : Site4 n → Turns) : Site4 n → Turns :=
--×   fun x => the_turns_product (the_whole_turn (-1)) (state x)

-- Episode13.lean, line 7529
--× theorem the_whole_turn_owed_has_length_one : the_turns_norm (the_whole_turn (-1)) = 1 := by decide

-- Episode13.lean, line 7531
--× theorem the_whole_turn_owed_at_every_site_leaves_the_links {n : Nat} (U : Torus4 n) :
--×     the_gauged_torus4 U (fun _ => the_whole_turn (-1)) = U := by
--×   funext way x
--×   show the_turns_product (the_turns_product (the_whole_turn (-1)) (U way x)) (the_turns_conjugate (the_whole_turn (-1)))
--×       = U way x
--×   generalize U way x = link
--×   obtain ⟨a, b, c, d⟩ := link
--×   simp only [the_turns_product, the_turns_conjugate, the_whole_turn]
--×   refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)) <;> simp

-- Episode13.lean, line 7542
--× theorem the_state_and_the_state_owed_give_one_action {n : Nat} (state : Site4 n → Turns) (U : Torus4 n)
--×     (this that way : Direction) (x : Site4 n) :
--×     the_action_of_light_and_matter_at (the_state_owed state) U this that way x
--×       = the_action_of_light_and_matter_at state U this that way x := by
--×   have turned := the_action_of_light_and_matter_is_left_by_a_turn_at_every_site state U (fun _ => the_whole_turn (-1))
--×     (fun _ => the_whole_turn_owed_has_length_one) this that way x
--×   rw [the_whole_turn_owed_at_every_site_leaves_the_links] at turned
--×   exact turned

-- Episode13.lean, line 7561
--× def the_parts_of_a_rest_of_the_call : Bullshit → List Nat
--×   | .rest_call _ _ _ last_page _ _ the_one_preprint the_other_preprint this_constant that_constant =>
--×       [last_page.all_the_way_down.length, the_one_preprint.all_the_way_down.length,
--×        the_other_preprint.all_the_way_down.length, this_constant.all_the_way_down.length,
--×        that_constant.all_the_way_down.length]
--×   | _ => []

-- Episode13.lean, line 7570
--× set_option maxRecDepth 100000 in
--× theorem one_goes_out_and_one_comes_back :
--×     the_parts_of_a_rest_of_the_call gawked_at_twice = [2, 4, 3, 12, 12]
--×       ∧ the_parts_of_a_rest_of_the_call gawked_at_three_times = [1, 3, 4, 12, 12]
--×       ∧ the_parts_of_a_rest_of_the_call gawked_at_four_times = [1, 4, 4, 12, 12] := by decide

-- Episode13.lean, line 7577
--× theorem after_it_comes_back_the_two_stand_level :
--×     the_parts_of_a_rest_of_the_call gawked_at_five_times = the_parts_of_a_rest_of_the_call gawked_at_four_times :=
--×   congrArg the_parts_of_a_rest_of_the_call gawked_at_five_times_is_gawked_at_four

-- Episode13.lean, line 7591
--× theorem a_fact_on_one_is_three_and_a_fact_on_two_is_seven :
--×     one_limit.all_the_way_down.length = 2 ∧ a_bracket.all_the_way_down.length = 6
--×       ∧ (Trial.hypothesis FACT.Truth one_limit).all_the_way_down.length = 3
--×       ∧ (Trial.hypothesis FACT.Truth a_bracket).all_the_way_down.length = 7 := by decide

-- Episode13.lean, line 7598
--× def how_the_first_fact_clicks : Bullshit → Bool
--×   | .zero fact => fact.bit
--×   | .one fact _ _ _ _ => fact.bit
--×   | .rest_call fact _ _ _ _ _ _ _ _ _ => fact.bit

-- Episode13.lean, line 7603
--× set_option maxRecDepth 100000 in
--× theorem one_step_on_the_two_branches_are_told_apart :
--×     how_the_first_fact_clicks gawked_at_twice = true
--×       ∧ how_the_first_fact_clicks called_false_and_gawked_at_once = false
--×       ∧ called_false_and_gawked_at_once ≠ gawked_at_twice :=
--×   have the_one : how_the_first_fact_clicks gawked_at_twice = true := by decide
--×   have the_other : how_the_first_fact_clicks called_false_and_gawked_at_once = false := by decide
--×   ⟨the_one, the_other, fun same => Bool.noConfusion ((congrArg how_the_first_fact_clicks same).symm.trans the_other ▸ the_one)⟩

-- Episode13.lean, line 7614
--× theorem after_that_no_reader_tells_them_apart {what_is_read : Sort any} (reader : Bullshit → what_is_read) :
--×     reader called_false_and_gawked_at_twice = reader gawked_at_three_times :=
--×   congrArg reader after_one_step_the_two_branches_are_one.1

-- Episode13.lean, line 7627
--× def the_origin_on_a_zero : Measurement.{0} := .origin zero another_zero Prop
--× def the_distance_on_the_origin : Measurement.{0} := .distance_to zero another_zero another_zero Prop Type the_origin_on_a_zero
--× def the_speed_on_the_distance : Measurement.{0} :=
--×   .speed zero another_zero another_zero another_zero Prop Type Prop the_distance_on_the_origin the_origin_on_a_zero

-- Episode13.lean, line 7634
--× theorem the_three_terms_hold_two_five_and_eleven :
--×     [the_origin_on_a_zero, the_distance_on_the_origin, the_speed_on_the_distance].map
--×         (fun term => term.all_the_way_down.length) = [2, 5, 11]
--×       ∧ [the_origin_on_a_zero, the_distance_on_the_origin, the_speed_on_the_distance].map
--×         (fun term => term.the_reading.length) = [0, 1, 2] := by decide

-- Episode13.lean, line 7647
--× def the_cross (p q : Turns) : Turns :=
--×   (0, p.2.2.1 * q.2.2.2 - p.2.2.2 * q.2.2.1, p.2.2.2 * q.2.1 - p.2.1 * q.2.2.2, p.2.1 * q.2.2.1 - p.2.2.1 * q.2.1)

-- Episode13.lean, line 7651
--× theorem the_two_orders_differ_by_the_cross_twice (p q : Turns) :
--×     (the_turns_product p q).1 - (the_turns_product q p).1 = 0
--×       ∧ (the_turns_product p q).2.1 - (the_turns_product q p).2.1 = 2 * (the_cross p q).2.1
--×       ∧ (the_turns_product p q).2.2.1 - (the_turns_product q p).2.2.1 = 2 * (the_cross p q).2.2.1
--×       ∧ (the_turns_product p q).2.2.2 - (the_turns_product q p).2.2.2 = 2 * (the_cross p q).2.2.2 := by
--×   obtain ⟨a, b, c, d⟩ := p
--×   obtain ⟨e, f, g, h⟩ := q
--×   simp only [the_turns_product, the_cross]
--×   refine ⟨?_, ?_, ?_, ?_⟩ <;> ac_nf <;> omega

-- Episode13.lean, line 7662
--× theorem the_cross_turned_over_is_owed (p q : Turns) :
--×     (the_cross q p).2.1 = - (the_cross p q).2.1 ∧ (the_cross q p).2.2.1 = - (the_cross p q).2.2.1
--×       ∧ (the_cross q p).2.2.2 = - (the_cross p q).2.2.2 := by
--×   obtain ⟨a, b, c, d⟩ := p
--×   obtain ⟨e, f, g, h⟩ := q
--×   simp only [the_cross]
--×   refine ⟨?_, ?_, ?_⟩ <;> ac_nf <;> omega

-- Episode13.lean, line 7670
--× theorem a_turn_crossed_with_itself_is_nothing (p : Turns) :
--×     (the_cross p p).1 = 0 ∧ (the_cross p p).2.1 = 0 ∧ (the_cross p p).2.2.1 = 0 ∧ (the_cross p p).2.2.2 = 0 := by
--×   obtain ⟨a, b, c, d⟩ := p
--×   simp only [the_cross]
--×   refine ⟨trivial, ?_, ?_, ?_⟩ <;> ac_nf <;> omega

-- Episode13.lean, line 7684
--× theorem only_sent_and_not_returned_cannot_click :
--×     the_arms.map (fun arm => (arm, the_arm_stores_a_fact_that_can_click arm.1 arm.2))
--×         = [((true, true), true), ((true, false), false), ((false, true), true), ((false, false), true)]
--×       ∧ the_arms.map (fun arm => the_arm_weight arm.1 arm.2) = [18, 5, 18, 18]
--×       ∧ the_arm_weight true true - the_arm_weight true false = bent_card := by decide

-- Episode13.lean, line 7698
--× theorem from_the_back_the_first_is_the_closures_and_the_fifth_is_the_fives :
--×     the_steps_of_the_argument.reverse[0]? = some the_only_logical_inconsistency.infer
--×       ∧ the_steps_of_the_argument.reverse[4]? = some the_coordinate_system.gauss
--×       ∧ the_coordinate_system.gauss.length = 5
--×       ∧ (from_the_inferred_end 4).length = 13 ∧ (from_the_inferred_end 5).length = 18 :=
--×   ⟨rfl, rfl, by decide, by decide, by decide⟩

-- Episode13.lean, line 7717
--× theorem six_pairs_and_thirty_six_pairs_of_pairs :
--×     the_pairs_of_arms.length = 6 ∧ the_pairs_of_pairs.length = 36 := by decide

-- Episode13.lean, line 7722
--× def the_source_across (pairs : (Direction × Direction) × (Direction × Direction)) : Int :=
--×   the_curvature_across the_source_on_the_arms pairs.1.1 pairs.1.2 pairs.2.1 pairs.2.2

-- Episode13.lean, line 7725
--× theorem six_of_the_thirty_six_are_not_nothing :
--×     (the_pairs_of_pairs.filter fun pairs => the_source_across pairs != 0)
--×       = the_pairs_of_arms.map fun pair => (pair, pair) := by decide

-- Episode13.lean, line 7730
--× theorem three_are_the_round_trip_and_three_the_square :
--×     (the_pairs_of_arms.map fun pair => the_source_across (pair, pair)) = [90, 324, 324, 90, 90, 324] := by decide

-- Episode13.lean, line 7741
--× def the_lengths_of_the_tapes : List Nat := the_steps_one_for_each_kind.map List.length
--× def the_running_count (lengths : List Nat) : List Nat :=
--×   (List.range (lengths.length + 1)).map fun kinds => (lengths.take kinds).foldl (· + ·) 0

-- Episode13.lean, line 7746
--× theorem the_tapes_kind_by_kind :
--×     the_lengths_of_the_tapes
--×       = [4, 2, 1, 2, 2, 3, 3, 2, 2, 2, 2, 2, 2, 4, 4, 3, 4, 3, 2, 2, 2, 2, 4, 4, 4, 2, 2, 2, 2, 4, 4, 5, 2, 3, 5, 3] := by
--×   decide

-- Episode13.lean, line 7752
--× theorem the_running_count_from_the_front :
--×     the_running_count the_lengths_of_the_tapes
--×       = [0, 4, 6, 7, 9, 11, 14, 17, 19, 21, 23, 25, 27, 29, 33, 37, 40, 44, 47, 49, 51, 53, 55, 59, 63, 67, 69, 71, 73,
--×          75, 79, 83, 88, 90, 93, 98, 101] := by decide

-- Episode13.lean, line 7758
--× theorem the_running_count_from_the_back :
--×     the_running_count the_lengths_of_the_tapes.reverse
--×       = [0, 3, 8, 11, 13, 18, 22, 26, 28, 30, 32, 34, 38, 42, 46, 48, 50, 52, 54, 57, 61, 64, 68, 72, 74, 76, 78, 80, 82,
--×          84, 87, 90, 92, 94, 95, 97, 101] := by decide

-- Episode13.lean, line 7767
--× theorem where_the_counts_fall :
--×     [3, 8, 10, 11, 13, 18, 33].map (fun kinds => (the_running_count the_lengths_of_the_tapes)[kinds]?)
--×         = [some 7, some 19, some 23, some 25, some 29, some 47, some 90]
--×       ∧ [4, 5, 6, 8, 13, 31].map (fun kinds => (the_running_count the_lengths_of_the_tapes.reverse)[kinds]?)
--×         = [some 13, some 18, some 22, some 28, some 42, some 90] := by decide

-- Episode13.lean, line 7775
--× theorem the_tapes_by_their_length :
--×     [1, 2, 3, 4, 5].map (fun length => (the_lengths_of_the_tapes.filter (· == length)).length) = [1, 18, 6, 9, 2]
--×       ∧ [1, 2, 3, 4, 5].map (fun length => length * (the_lengths_of_the_tapes.filter (· == length)).length)
--×           = [1, 36, 18, 36, 10]
--×       ∧ 1 + 36 + 18 + 36 + 10 = 101 := by decide

-- Episode13.lean, line 7783
--× theorem set_palm_the_middle_card_one_another : 47 + 90 = 137 ∧ 42 + 47 = 89 ∧ 137 + 42 = 179 := by decide

-- Episode13.lean, line 7793
--× theorem the_depths_are_two_of_the_tapes :
--×     the_orbital_data_points = 4 ∧ the_dimensions_of_universe = 5
--×       ∧ the_lengths_of_the_tapes[30]? = some the_orbital_data_points
--×       ∧ the_lengths_of_the_tapes[31]? = some the_dimensions_of_universe := by decide

-- Episode13.lean, line 7801
--× theorem what_lies_between_the_counts :
--×     ((the_lengths_of_the_tapes.drop 13).take 5).foldl (· + ·) 0 = 18 ∧ 29 + 18 = 47
--×       ∧ (the_lengths_of_the_tapes.take 5).foldl (· + ·) 0 = 11
--×       ∧ (the_lengths_of_the_tapes.reverse.take 3).foldl (· + ·) 0 = 11 ∧ 101 - 11 = 90 := by decide

-- Episode13.lean, line 7814
--× def the_pairs_round_a_hexagon : List (Direction × Direction) :=
--×   [((true, true), (true, false)), ((true, true), (false, true)), ((true, false), (false, true)),
--×    ((false, true), (false, false)), ((true, false), (false, false)), ((true, true), (false, false))]

-- Episode13.lean, line 7818
--× def has_the_arm_out (pair : Direction × Direction) : Bool := pair.1 == (true, false) || pair.2 == (true, false)

-- Episode13.lean, line 7823
--× theorem round_the_hexagon :
--×     (the_pairs_of_arms.all fun pair => the_pairs_round_a_hexagon.contains pair) = true
--×       ∧ the_pairs_round_a_hexagon.length = 6
--×       ∧ the_pairs_round_a_hexagon.map has_the_arm_out = [true, false, true, false, true, false]
--×       ∧ ((the_pairs_round_a_hexagon.zip (the_pairs_round_a_hexagon.drop 1 ++ the_pairs_round_a_hexagon.take 1)).all
--×           fun both => share_an_arm both.1 both.2) = true := by decide

-- Episode13.lean, line 7832
--× def the_places_round (j k : Nat) : (Direction × Direction) × (Direction × Direction) :=
--×   (the_pairs_round_a_hexagon.getD j ((true, true), (true, true)), the_pairs_round_a_hexagon.getD k ((true, true), (true, true)))

-- Episode13.lean, line 7835
--× theorem two_sectors_of_eighteen :
--×     (((List.range 6).flatMap fun j => (List.range 6).map fun k => (j, k)).filter fun place => (place.1 + place.2) % 2 == 0).length
--×         = 18
--×       ∧ (((List.range 6).flatMap fun j => (List.range 6).map fun k => (j, k)).filter
--×           fun place => the_source_across (the_places_round place.1 place.2) != 0)
--×         = (List.range 6).map fun j => (j, j) := by decide

-- Episode13.lean, line 7849
--× theorem the_residual_at_the_zero_the_one_and_past_it :
--×     the_residual_of_the_pair 0 1 = 18 ∧ the_residual_of_the_pair 1 1 = -5 ∧ the_residual_of_the_pair 1 0 = 13
--×       ∧ the_residual_of_the_pair 0 1 + the_residual_of_the_pair 1 1 = 13
--×       ∧ the_residual_of_the_pair 0 1 - the_residual_of_the_pair 1 1 = 23 := by decide

-- Episode13.lean, line 7869
--× theorem the_four_closures_hold_one_fact :
--×     the_second_closure.infer = the_first_closure.infer ∧ the_third_closure.infer = the_first_closure.infer
--×       ∧ the_fourth_closure.infer = the_first_closure.infer := ⟨rfl, rfl, rfl⟩

-- Episode13.lean, line 7875
--× theorem the_residue_of_one_is_the_comparison_of_the_next :
--×     the_atreyu_process.residue? gawked_at_once gawked_at_twice = some (gawked_at_twice < gawked_at_three_times)
--×       ∧ the_atreyu_process.residue? gawked_at_twice gawked_at_three_times
--×           = some (gawked_at_three_times < gawked_at_four_times)
--×       ∧ the_atreyu_process.residue? gawked_at_three_times gawked_at_four_times
--×           = some (gawked_at_four_times < gawked_at_five_times) := ⟨rfl, rfl, rfl⟩

-- Episode13.lean, line 7883
--× theorem at_the_fixed_point_the_residue_is_its_own_comparison :
--×     the_atreyu_process.residue? gawked_at_four_times gawked_at_five_times
--×       = the_atreyu_process.residue? gawked_at_three_times gawked_at_four_times := rfl

-- Episode13.lean, line 7888
--× theorem two_zeros_have_no_residue :
--×     the_atreyu_process.residue? the_same_difference_quantum the_same_difference_quantum = none := rfl

-- Episode13.lean, line 7914
--× def the_sixteen_devices : List (Option Nat) :=
--×   [true, false].flatMap fun b => [true, false].flatMap fun e => [true, false].flatMap fun t => [true, false].map fun l =>
--×     what_a_device_reads (the_device_with b e t l)

-- Episode13.lean, line 7921
--× set_option maxRecDepth 100000 in
--× theorem the_sixteen_devices_read_three_things :
--×     the_sixteen_devices
--×       = [some the_constant_factor_of_scaling_bullshit, some (episode8_description.length * all_possible_variables), none, none,
--×          some the_constant_factor_of_scaling_bullshit, some (episode8_description.length * all_possible_variables), none, none,
--×          some the_constant_factor_of_scaling_bullshit, some (episode8_description.length * all_possible_variables), none, none,
--×          some the_constant_factor_of_scaling_bullshit, some (episode8_description.length * all_possible_variables), none, none] := by
--×   decide

-- Episode13.lean, line 7934
--× def the_turns_in_a_jar : Jar := .color zero (the_number_of_marks episode8_description)
--× def the_physics_of_the_turns : Equivalation := .physics zero the_turns_in_a_jar

-- Episode13.lean, line 7937
--× theorem the_jar_holds_as_many_cells_as_the_crank_has_turns :
--×     compute_the_area_of (what_the_jar_holds the_turns_in_a_jar) = episode8_description.length ∧ episode8_description.length = 106 :=
--×   ⟨the_number_of_marks_the_tapes_length episode8_description, by decide⟩

-- Episode13.lean, line 7942
--× theorem the_physics_of_the_turns_stands_between :
--×     the_physics_of_the_turns.vanish.length = 1
--×       ∧ (Equivalation.zero_like zero the_physics_of_the_turns).vanish.length = 2
--×       ∧ (Equivalation.one_like (episode8_description.length = 106) the_physics_of_the_turns
--×             the_physics_of_the_turns).vanish.length = 3 := ⟨rfl, rfl, rfl⟩

-- Episode13.lean, line 7957
--× def what_is_counted (one_half other_half : Area) (from_the_source : Bool) : Nat :=
--×   if from_the_source then compute_the_area_of (one_half + other_half) else compute_the_area_of one_half + compute_the_area_of other_half

-- Episode13.lean, line 7960
--× theorem the_same_is_counted_either_way (one_half other_half : Area) :
--×     what_is_counted one_half other_half true = what_is_counted one_half other_half false :=
--×   palm_the_middle_card_adds one_half other_half

-- Episode13.lean, line 7965
--× theorem which_it_was_cannot_be_recovered_from_the_count (one_half other_half : Area) :
--×     ¬ can_be_recovered (fun _ : Bool => True) (what_is_counted one_half other_half) (fun from_the_source => from_the_source) :=
--×   the_same_kept_and_two_identifications_cannot_be_recovered _ _ _ true false trivial trivial
--×     (the_same_is_counted_either_way one_half other_half) (by decide)

-- Episode13.lean, line 7979
--× noncomputable def with_its_second_fact_called_false (rest : Bullshit.{0,0,0,0}) : Bullshit.{0,0,0,0} :=
--×   match rest with
--×   | .rest_call fact _ held last here total one other this that =>
--×       .rest_call fact (bitFACT false) held last here total one other this that
--×   | other => other

-- Episode13.lean, line 7985
--× noncomputable def true_then_false_gawked_at_once : Bullshit.{0,0,0,0} :=
--×   the_atreyu_process.gawk_at (with_its_second_fact_called_false gawked_at_twice)
--× noncomputable def true_then_false_gawked_at_twice : Bullshit.{0,0,0,0} :=
--×   the_atreyu_process.gawk_at true_then_false_gawked_at_once
--× noncomputable def false_then_false_gawked_at_once : Bullshit.{0,0,0,0} :=
--×   the_atreyu_process.gawk_at (with_its_second_fact_called_false called_false_and_gawked_at_once)
--× noncomputable def false_then_false_gawked_at_twice : Bullshit.{0,0,0,0} :=
--×   the_atreyu_process.gawk_at false_then_false_gawked_at_once

-- Episode13.lean, line 7995
--× theorem the_four_ways_stop_in_one_place :
--×     true_then_false_gawked_at_twice = gawked_at_four_times
--×       ∧ false_then_false_gawked_at_twice = gawked_at_four_times
--×       ∧ called_false_and_gawked_at_three_times = gawked_at_four_times
--×       ∧ the_atreyu_process.gawk_at true_then_false_gawked_at_twice = true_then_false_gawked_at_twice
--×       ∧ the_atreyu_process.gawk_at false_then_false_gawked_at_twice = false_then_false_gawked_at_twice :=
--×   ⟨rfl, rfl, after_one_step_the_two_branches_are_one.2.1, rfl, rfl⟩

-- Episode13.lean, line 8004
--× set_option maxRecDepth 100000 in
--× theorem the_two_new_ways_hold_thirty_eight_and_thirty_nine :
--×     [true_then_false_gawked_at_once, true_then_false_gawked_at_twice, false_then_false_gawked_at_once,
--×       false_then_false_gawked_at_twice].map (fun gawk => gawk.all_the_way_down.length) = [38, 39, 38, 39] := by decide

-- Episode13.lean, line 8017
--× def the_device_of_a_name (step : (Bool × Bool) × (Bool × Bool)) : Option Nat :=
--×   what_a_device_reads (the_device_with step.1.1 step.1.2 step.2.1 step.2.2)

-- Episode13.lean, line 8021
--× theorem the_sixteen_names_are_the_sixteen_devices :
--×     the_sixteen_steps.map the_device_of_a_name = the_sixteen_devices := rfl

-- Episode13.lean, line 8026
--× def what_the_second_mark_reads (mark : Bool × Bool) : Option Nat :=
--×   match mark with
--×   | (true, true) => some the_constant_factor_of_scaling_bullshit
--×   | (true, false) => some (episode8_description.length * all_possible_variables)
--×   | _ => none

-- Episode13.lean, line 8032
--× set_option maxRecDepth 100000 in
--× theorem a_name_reads_what_its_second_mark_reads :
--×     the_sixteen_steps.map the_device_of_a_name = the_sixteen_steps.map (fun step => what_the_second_mark_reads step.2) := by
--×   decide

-- Episode13.lean, line 8051
--× def the_option_a_closure_holds : Closure → Option Prop
--×   | .same _ _ => none
--×   | .different _ _ _ option => option
--×   | .inferred _ _ _ _ option _ => option

-- Episode13.lean, line 8056
--× theorem what_the_four_closures_hold_as_options :
--×     the_option_a_closure_holds the_first_closure = some (gawked_at_once < gawked_at_twice)
--×       ∧ the_option_a_closure_holds the_second_closure = some (gawked_at_twice < gawked_at_three_times)
--×       ∧ the_option_a_closure_holds the_third_closure = some (gawked_at_three_times < gawked_at_four_times)
--×       ∧ the_option_a_closure_holds the_fourth_closure = some (gawked_at_four_times < gawked_at_five_times) :=
--×   ⟨rfl, rfl, rfl, rfl⟩

-- Episode13.lean, line 8066
--× theorem three_of_the_implications_go_and_one_does_not :
--×     Closure.implying_implication (the_option_a_closure_holds the_first_closure) (the_option_a_closure_holds the_first_closure)
--×       ∧ Closure.implying_implication (the_option_a_closure_holds the_second_closure)
--×           (the_option_a_closure_holds the_third_closure)
--×       ∧ Closure.implying_implication (the_option_a_closure_holds the_second_closure)
--×           (the_option_a_closure_holds the_first_closure)
--×       ∧ ¬ Closure.implying_implication (the_option_a_closure_holds the_first_closure)
--×           (the_option_a_closure_holds the_second_closure) :=
--×   ⟨fun held => held,
--×    fun held => the_second_third_and_fourth_closures_store_one_proposition.1 ▸ held,
--×    fun held => absurd held what_three_closures_store_cannot_hold.1,
--×    fun goes => what_three_closures_store_cannot_hold.1 (goes what_the_first_closure_stores_holds)⟩

-- Episode13.lean, line 8081
--× theorem true_on_false_and_false_on_true_are_two_places :
--×     ¬ (Closure.implying_implication (the_option_a_closure_holds the_first_closure)
--×           (the_option_a_closure_holds the_second_closure)
--×         ↔ Closure.implying_implication (the_option_a_closure_holds the_second_closure)
--×           (the_option_a_closure_holds the_first_closure)) :=
--×   fun the_same =>
--×     three_of_the_implications_go_and_one_does_not.2.2.2 (the_same.mpr three_of_the_implications_go_and_one_does_not.2.2.1)

-- Episode13.lean, line 8099
--× theorem the_action_of_the_links_varies_by_its_squares (U : TurnsLattice) (d i j : Bool) (X : Turns) (t : Int) :
--×     ∃ Y₁ Y₂ Y₃ Y₄ : Turns,
--×       the_turns_lattice_action (the_varied_turns_lattice U d i j X t)
--×         = the_turns_lattice_action U
--×           + t * (the_first_variation_of_the_turns (the_turns_square U false false) Y₁
--×                 + the_first_variation_of_the_turns (the_turns_square U false true) Y₂
--×                 + the_first_variation_of_the_turns (the_turns_square U true false) Y₃
--×                 + the_first_variation_of_the_turns (the_turns_square U true true) Y₄)
--×           + t * t * (the_turns_action Y₁ + the_turns_action Y₂ + the_turns_action Y₃ + the_turns_action Y₄) := by
--×   obtain ⟨Y₁, h₁⟩ := each_turns_square_holds_a_link_once U d i j X t false false
--×   obtain ⟨Y₂, h₂⟩ := each_turns_square_holds_a_link_once U d i j X t false true
--×   obtain ⟨Y₃, h₃⟩ := each_turns_square_holds_a_link_once U d i j X t true false
--×   obtain ⟨Y₄, h₄⟩ := each_turns_square_holds_a_link_once U d i j X t true true
--×   refine ⟨Y₁, Y₂, Y₃, Y₄, ?_⟩
--×   simp only [the_turns_lattice_action, h₁, h₂, h₃, h₄, the_turns_action_stops_at_second_order, Int.mul_add]
--×   omega

-- Episode13.lean, line 8117
--× def the_torus_with_one_link_moved {n : Nat} (U : Torus4 n) (way : Direction) (x : Site4 n) (X : Turns) (t : Int) : Torus4 n :=
--×   fun other y => if other = way ∧ y = x then the_varied_turns (U way x) X t else U other y

-- Episode13.lean, line 8126
--× theorem the_state_carried_back_varies_by_the_current {n : Nat} (state : Site4 n → Turns) (U : Torus4 n)
--×     (way : Direction) (x : Site4 n) (X : Turns) (t : Int) :
--×     the_state_carried_back state (the_torus_with_one_link_moved U way x X t) way x
--×       = the_varied_turns (the_state_carried_back state U way x) (the_current_in_the_link state way x X) t := by
--×   simp only [the_state_carried_back, the_torus_with_one_link_moved, the_current_in_the_link, and_self, if_true,
--×     the_product_is_linear_on_the_left, the_product_is_linear_on_the_right]

-- Episode13.lean, line 8134
--× theorem the_state_against_itself_does_not_hold_the_link {n : Nat} (state : Site4 n → Turns) (x : Site4 n) :
--×     the_state_against_itself state x = the_turns_product (the_turns_conjugate (state x)) (state x) := rfl

-- Episode13.lean, line 8147
--× theorem the_square_ahead_with_the_link_moved {n : Nat} (U : Torus4 n) (way other : Direction) (x : Site4 n) (X : Turns)
--×     (t : Int) (another_way : other ≠ way) (the_step_leaves : the_step other x ≠ x) :
--×     the_square4 (the_torus_with_one_link_moved U way x X t) way other x
--×       = the_varied_turns (the_square4 U way other x)
--×           (the_turns_holonomy X (U other (the_step way x)) (U way (the_step other x)) (U other x)) t := by
--×   have bottom : the_torus_with_one_link_moved U way x X t way x = the_varied_turns (U way x) X t := if_pos ⟨rfl, rfl⟩
--×   have right : the_torus_with_one_link_moved U way x X t other (the_step way x) = U other (the_step way x) :=
--×     if_neg (fun both => another_way both.1)
--×   have top : the_torus_with_one_link_moved U way x X t way (the_step other x) = U way (the_step other x) :=
--×     if_neg (fun both => the_step_leaves both.2)
--×   have left : the_torus_with_one_link_moved U way x X t other x = U other x := if_neg (fun both => another_way both.1)
--×   simp only [the_square4, bottom, right, top, left]
--×   exact (the_turns_holonomy_is_linear_in_each_link _ _ _ _ _ _).1

-- Episode13.lean, line 8162
--× theorem the_square_behind_with_the_link_moved {n : Nat} (U : Torus4 n) (way other : Direction) (x behind : Site4 n)
--×     (X : Turns) (t : Int) (another_way : other ≠ way) (one_step_back : the_step other behind = x)
--×     (not_the_site : behind ≠ x) :
--×     the_square4 (the_torus_with_one_link_moved U way x X t) other way behind
--×       = the_varied_turns (the_square4 U other way behind)
--×           (the_turns_holonomy (U other behind) X (U other (the_step way behind)) (U way behind)) t := by
--×   have bottom : the_torus_with_one_link_moved U way x X t other behind = U other behind :=
--×     if_neg (fun both => another_way both.1)
--×   have right : the_torus_with_one_link_moved U way x X t way (the_step other behind) = the_varied_turns (U way x) X t := by
--×     rw [one_step_back]; exact if_pos ⟨rfl, rfl⟩
--×   have top : the_torus_with_one_link_moved U way x X t other (the_step way behind) = U other (the_step way behind) :=
--×     if_neg (fun both => another_way both.1)
--×   have left : the_torus_with_one_link_moved U way x X t way behind = U way behind := if_neg (fun both => not_the_site both.2)
--×   have the_far_side : U way (the_step other behind) = U way x := by rw [one_step_back]
--×   simp only [the_square4, bottom, right, top, left, the_far_side]
--×   exact (the_turns_holonomy_is_linear_in_each_link _ _ _ _ _ _).2.1

-- Episode13.lean, line 8181
--× def the_action_at_the_link {n : Nat} (state : Site4 n → Turns) (U : Torus4 n) (way other : Direction) (x behind : Site4 n) : Int :=
--×   the_turns_action (the_square4 U way other x) + the_turns_action (the_square4 U other way behind)
--×     + (the_state_carried_back state U way x).1

-- Episode13.lean, line 8187
--× def what_multiplies_the_move {n : Nat} (state : Site4 n → Turns) (U : Torus4 n) (way other : Direction) (x behind : Site4 n)
--×     (X : Turns) : Int :=
--×   the_first_variation_of_the_turns (the_square4 U way other x)
--×       (the_turns_holonomy X (U other (the_step way x)) (U way (the_step other x)) (U other x))
--×     + the_first_variation_of_the_turns (the_square4 U other way behind)
--×       (the_turns_holonomy (U other behind) X (U other (the_step way behind)) (U way behind))
--×     + (the_current_in_the_link state way x X).1

-- Episode13.lean, line 8197
--× theorem the_action_at_the_link_with_the_link_moved {n : Nat} (state : Site4 n → Turns) (U : Torus4 n) (way other : Direction)
--×     (x behind : Site4 n) (X : Turns) (t : Int) (another_way : other ≠ way) (the_step_leaves : the_step other x ≠ x)
--×     (one_step_back : the_step other behind = x) (not_the_site : behind ≠ x) :
--×     the_action_at_the_link state (the_torus_with_one_link_moved U way x X t) way other x behind
--×       = the_action_at_the_link state U way other x behind
--×         + t * what_multiplies_the_move state U way other x behind X
--×         + t * t * (the_turns_action (the_turns_holonomy X (U other (the_step way x)) (U way (the_step other x)) (U other x))
--×                   + the_turns_action (the_turns_holonomy (U other behind) X (U other (the_step way behind)) (U way behind))) := by
--×   have ahead := the_turns_action_stops_at_second_order (the_square4 U way other x)
--×     (the_turns_holonomy X (U other (the_step way x)) (U way (the_step other x)) (U other x)) t
--×   have back := the_turns_action_stops_at_second_order (the_square4 U other way behind)
--×     (the_turns_holonomy (U other behind) X (U other (the_step way behind)) (U way behind)) t
--×   have carried : (the_varied_turns (the_state_carried_back state U way x) (the_current_in_the_link state way x X) t).1
--×       = (the_state_carried_back state U way x).1 + t * (the_current_in_the_link state way x X).1 := rfl
--×   show the_turns_action (the_square4 (the_torus_with_one_link_moved U way x X t) way other x)
--×       + the_turns_action (the_square4 (the_torus_with_one_link_moved U way x X t) other way behind)
--×       + (the_state_carried_back state (the_torus_with_one_link_moved U way x X t) way x).1 = _
--×   rw [the_square_ahead_with_the_link_moved U way other x X t another_way the_step_leaves,
--×     the_square_behind_with_the_link_moved U way other x behind X t another_way one_step_back not_the_site,
--×     the_state_carried_back_varies_by_the_current, ahead, back, carried]
--×   simp only [the_action_at_the_link, what_multiplies_the_move, Int.mul_add]
--×   omega

-- Episode13.lean, line 8223
--× def stands_still_in_the_link {n : Nat} (state : Site4 n → Turns) (U : Torus4 n) (way other : Direction) (x behind : Site4 n) : Prop :=
--×   ∀ X : Turns, what_multiplies_the_move state U way other x behind X = 0

-- Episode13.lean, line 8226
--× theorem where_it_stands_still_the_move_enters_only_squared {n : Nat} (state : Site4 n → Turns) (U : Torus4 n)
--×     (way other : Direction) (x behind : Site4 n) (X : Turns) (t : Int) (another_way : other ≠ way)
--×     (the_step_leaves : the_step other x ≠ x) (one_step_back : the_step other behind = x) (not_the_site : behind ≠ x)
--×     (still : stands_still_in_the_link state U way other x behind) :
--×     ∃ squared : Int, the_action_at_the_link state (the_torus_with_one_link_moved U way x X t) way other x behind
--×       = the_action_at_the_link state U way other x behind + t * t * squared := by
--×   refine ⟨the_turns_action (the_turns_holonomy X (U other (the_step way x)) (U way (the_step other x)) (U other x))
--×       + the_turns_action (the_turns_holonomy (U other behind) X (U other (the_step way behind)) (U way behind)), ?_⟩
--×   rw [the_action_at_the_link_with_the_link_moved state U way other x behind X t another_way the_step_leaves one_step_back
--×     not_the_site, still X, Int.mul_zero, Int.add_zero]

-- Episode13.lean, line 8248
--× def the_equation_through_the_area : Prop := type_of% @the_field_equation_on_the_torus
--× def the_equation_through_the_closures : Prop := type_of% @the_action_at_the_link_with_the_link_moved

-- Episode13.lean, line 8252
--× theorem both_equations_hold : the_equation_through_the_area ∧ the_equation_through_the_closures :=
--×   ⟨@the_field_equation_on_the_torus, @the_action_at_the_link_with_the_link_moved⟩

-- Episode13.lean, line 8257
--× theorem asked_only_whether_it_is_true_the_two_equations_are_one :
--×     the_equation_through_the_area = the_equation_through_the_closures :=
--×   propext ⟨fun _ => both_equations_hold.2, fun _ => both_equations_hold.1⟩

-- Episode13.lean, line 8264
--× def the_physics_of_an_equation (it_says : Prop) : Equivalation :=
--×   .one_like it_says the_physics_of_the_turns the_physics_of_the_turns

-- Episode13.lean, line 8267
--× theorem the_reader_returns_the_same_whichever_equation_was_put_in (this_says that_says : Prop) :
--×     (the_physics_of_an_equation this_says).vanish = (the_physics_of_an_equation that_says).vanish
--×       ∧ (the_physics_of_an_equation this_says).vanish.length = 3 := ⟨rfl, rfl⟩

-- Episode13.lean, line 8273
--× theorem read_or_asked_the_two_equations_are_not_told_apart :
--×     (the_physics_of_an_equation the_equation_through_the_area).vanish
--×         = (the_physics_of_an_equation the_equation_through_the_closures).vanish
--×       ∧ the_equation_through_the_area = the_equation_through_the_closures :=
--×   ⟨rfl, asked_only_whether_it_is_true_the_two_equations_are_one⟩

-- Episode13.lean, line 8289
--× theorem the_vacuum_stands_still_in_every_link {n : Nat} (way other : Direction) (x behind : Site4 n) :
--×     stands_still_in_the_link (no_state (n := n)) the_whole_turn_on_every_link way other x behind := by
--×   intro X
--×   have ahead : the_square4 (the_whole_turn_on_every_link (n := n)) way other x = the_whole_turn 1 := rfl
--×   have back : the_square4 (the_whole_turn_on_every_link (n := n)) other way behind = the_whole_turn 1 := rfl
--×   simp only [what_multiplies_the_move, ahead, back, a_whole_turn_is_stationary, the_current_in_the_link, no_state,
--×     the_turns_product, the_turns_conjugate]
--×   simp

-- Episode13.lean, line 8306
--× theorem a_click_is_on_or_off (fact : FACT) : fact.bit = true ∨ fact.bit = false := by
--×   cases fact.bit <;> simp

-- Episode13.lean, line 8309
--× theorem together_and_apart :
--×     the_full_table false true + the_full_table true false = 23
--×       ∧ the_full_table false true - the_full_table true false = 13
--×       ∧ (23 : Int) * 23 - 13 * 13 = the_gap_squared the_full_table
--×       ∧ the_gap_squared the_full_table = 4 * (the_full_table false true * the_full_table true false) := by decide

-- Episode13.lean, line 8322
--× def the_lines_down_a_yarn : YarnTheory → List Nat
--×   | .stokes _ _ _ => [1]
--×   | .fibers _ _ _ _ _ rest => 2 :: the_lines_down_a_yarn rest
--×   | .fabric _ _ _ _ _ _ _ _ first _ => 3 :: the_lines_down_a_yarn first

-- Episode13.lean, line 8328
--× theorem the_coordinate_system_is_three_lines_on_two_on_one :
--×     the_lines_down_a_yarn the_coordinate_system = [3, 2, 1] := rfl

-- Episode13.lean, line 8338
--× theorem twenty_is_in_neither_running_count :
--×     (the_running_count the_lengths_of_the_tapes).contains 20 = false
--×       ∧ (the_running_count the_lengths_of_the_tapes.reverse).contains 20 = false
--×       ∧ ([1, 36, 18, 36, 10] : List Nat).contains 20 = false
--×       ∧ (the_running_count the_lengths_of_the_tapes).contains 19 = true
--×       ∧ (the_running_count the_lengths_of_the_tapes).contains 21 = true
--×       ∧ (the_running_count the_lengths_of_the_tapes.reverse).contains 18 = true
--×       ∧ (the_running_count the_lengths_of_the_tapes.reverse).contains 22 = true := by decide

-- Episode13.lean, line 8354
--× def the_turn_owed (q : Turns) : Turns := (- q.1, - q.2.1, - q.2.2.1, - q.2.2.2)
--× def the_one_machine (a b c : Turns) : Turns := the_cross a (the_cross (the_turn_owed c) b)
--× def the_other_machine (a b c : Turns) : Turns := the_cross (the_turn_owed a) (the_cross c (the_turn_owed b))

-- Episode13.lean, line 8359
--× theorem the_one_machine_is_the_other_owed (a b c : Turns) :
--×     the_one_machine a b c = the_turn_owed (the_other_machine a b c) := by
--×   obtain ⟨a₀, a₁, a₂, a₃⟩ := a
--×   obtain ⟨b₀, b₁, b₂, b₃⟩ := b
--×   obtain ⟨c₀, c₁, c₂, c₃⟩ := c
--×   simp only [the_one_machine, the_other_machine, the_cross, the_turn_owed, Int.neg_mul, Int.mul_neg, Int.neg_neg,
--×     Int.mul_sub, Int.neg_zero]
--×   refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)) <;> simp <;> ac_nf <;> omega

-- Episode13.lean, line 8369
--× theorem read_by_the_action_the_two_machines_are_one (a b c : Turns) :
--×     the_turns_action (the_one_machine a b c) = the_turns_action (the_other_machine a b c) := by
--×   rw [the_one_machine_is_the_other_owed]
--×   simp only [the_turns_action, the_turn_owed, Int.neg_mul_neg]

-- Episode13.lean, line 8379
--× def the_state_with_one_site_moved {n : Nat} (state : Site4 n → Turns) (y : Site4 n) (Y : Turns) (t : Int) : Site4 n → Turns :=
--×   fun z => if z = y then the_varied_turns (state y) Y t else state z

-- Episode13.lean, line 8384
--× theorem moved_at_the_far_end {n : Nat} (state : Site4 n → Turns) (U : Torus4 n) (way : Direction) (x : Site4 n) (Y : Turns)
--×     (t : Int) (the_step_leaves : the_step way x ≠ x) :
--×     the_state_carried_back (the_state_with_one_site_moved state (the_step way x) Y t) U way x
--×       = the_varied_turns (the_state_carried_back state U way x)
--×           (the_turns_product (the_turns_conjugate (state x)) (the_turns_product (U way x) Y)) t := by
--×   have near : the_state_with_one_site_moved state (the_step way x) Y t x = state x :=
--×     if_neg (fun same => the_step_leaves same.symm)
--×   have far : the_state_with_one_site_moved state (the_step way x) Y t (the_step way x)
--×       = the_varied_turns (state (the_step way x)) Y t := if_pos rfl
--×   simp only [the_state_carried_back, near, far, the_product_is_linear_on_the_right]

-- Episode13.lean, line 8396
--× theorem moved_at_the_near_end {n : Nat} (state : Site4 n → Turns) (U : Torus4 n) (way : Direction) (x : Site4 n) (Y : Turns)
--×     (t : Int) (the_step_leaves : the_step way x ≠ x) :
--×     the_state_carried_back (the_state_with_one_site_moved state x Y t) U way x
--×       = the_varied_turns (the_state_carried_back state U way x)
--×           (the_turns_product (the_turns_conjugate Y) (the_turns_product (U way x) (state (the_step way x)))) t := by
--×   have near : the_state_with_one_site_moved state x Y t x = the_varied_turns (state x) Y t := if_pos rfl
--×   have far : the_state_with_one_site_moved state x Y t (the_step way x) = state (the_step way x) :=
--×     if_neg the_step_leaves
--×   simp only [the_state_carried_back, near, far, the_conjugate_is_linear, the_product_is_linear_on_the_left]

-- Episode13.lean, line 8408
--× theorem the_state_against_itself_with_the_state_moved {n : Nat} (state : Site4 n → Turns) (x : Site4 n) (Y : Turns) (t : Int) :
--×     the_state_against_itself (the_state_with_one_site_moved state x Y t) x
--×       = the_varied_turns
--×           (the_varied_turns (the_turns_product (the_turns_conjugate (state x)) (state x))
--×             (the_turns_product (the_turns_conjugate (state x)) Y) t)
--×           (the_varied_turns (the_turns_product (the_turns_conjugate Y) (state x))
--×             (the_turns_product (the_turns_conjugate Y) Y) t) t := by
--×   have here : the_state_with_one_site_moved state x Y t x = the_varied_turns (state x) Y t := if_pos rfl
--×   show the_turns_product (the_turns_conjugate (the_state_with_one_site_moved state x Y t x))
--×       (the_state_with_one_site_moved state x Y t x) = _
--×   rw [here, the_conjugate_is_linear, the_product_is_linear_on_the_left, the_product_is_linear_on_the_right,
--×     the_product_is_linear_on_the_right]

-- Episode13.lean, line 8423
--× theorem where_every_link_is_the_whole_turn_only_the_current_multiplies {n : Nat} (state : Site4 n → Turns)
--×     (way other : Direction) (x behind : Site4 n) (X : Turns) :
--×     what_multiplies_the_move state the_whole_turn_on_every_link way other x behind X
--×       = (the_current_in_the_link state way x X).1 := by
--×   have ahead : the_square4 (the_whole_turn_on_every_link (n := n)) way other x = the_whole_turn 1 := rfl
--×   have back : the_square4 (the_whole_turn_on_every_link (n := n)) other way behind = the_whole_turn 1 := rfl
--×   simp only [what_multiplies_the_move, ahead, back, a_whole_turn_is_stationary]
--×   omega

-- Episode13.lean, line 8438
--× def the_squares_at_the_link {n : Nat} (U : Torus4 n) (way : Direction) (x : Site4 n) : List (Direction × Site4 n) → Int
--×   | [] => 0
--×   | (other, behind) :: rest =>
--×       the_turns_action (the_square4 U way other x) + the_turns_action (the_square4 U other way behind)
--×         + the_squares_at_the_link U way x rest

-- Episode13.lean, line 8454
--× def what_the_squares_hold_of_the_move {n : Nat} (U : Torus4 n) (way : Direction) (x : Site4 n) (X : Turns) :
--×     List (Direction × Site4 n) → Int
--×   | [] => 0
--×   | (other, behind) :: rest =>
--×       the_turns_action (the_turns_holonomy X (U other (the_step way x)) (U way (the_step other x)) (U other x))
--×         + the_turns_action (the_turns_holonomy (U other behind) X (U other (the_step way behind)) (U way behind))
--×         + what_the_squares_hold_of_the_move U way x X rest

-- Episode13.lean, line 8463
--× def are_other_ways {n : Nat} (way : Direction) (x : Site4 n) (others : List (Direction × Site4 n)) : Prop :=
--×   ∀ pair ∈ others, pair.1 ≠ way ∧ the_step pair.1 x ≠ x ∧ the_step pair.1 pair.2 = x ∧ pair.2 ≠ x

-- Episode13.lean, line 8467
--× theorem the_squares_at_the_link_with_the_link_moved {n : Nat} (U : Torus4 n) (way : Direction) (x : Site4 n) (X : Turns)
--×     (t : Int) : ∀ (others : List (Direction × Site4 n)), are_other_ways way x others →
--×     the_squares_at_the_link (the_torus_with_one_link_moved U way x X t) way x others
--×       = the_squares_at_the_link U way x others + t * what_multiplies_the_move_of_the_squares U way x X others
--×         + t * t * what_the_squares_hold_of_the_move U way x X others
--×   | [], _ => by simp [the_squares_at_the_link, what_multiplies_the_move_of_the_squares, what_the_squares_hold_of_the_move]
--×   | (other, behind) :: rest, they_are => by
--×     have this_one := they_are (other, behind) (List.mem_cons_self ..)
--×     have the_rest := the_squares_at_the_link_with_the_link_moved U way x X t rest
--×       (fun pair among => they_are pair (List.mem_cons_of_mem _ among))
--×     have ahead := the_turns_action_stops_at_second_order (the_square4 U way other x)
--×       (the_turns_holonomy X (U other (the_step way x)) (U way (the_step other x)) (U other x)) t
--×     have back := the_turns_action_stops_at_second_order (the_square4 U other way behind)
--×       (the_turns_holonomy (U other behind) X (U other (the_step way behind)) (U way behind)) t
--×     show the_turns_action (the_square4 (the_torus_with_one_link_moved U way x X t) way other x)
--×         + the_turns_action (the_square4 (the_torus_with_one_link_moved U way x X t) other way behind)
--×         + the_squares_at_the_link (the_torus_with_one_link_moved U way x X t) way x rest = _
--×     rw [the_square_ahead_with_the_link_moved U way other x X t this_one.1 this_one.2.1,
--×       the_square_behind_with_the_link_moved U way other x behind X t this_one.1 this_one.2.2.1 this_one.2.2.2,
--×       ahead, back, the_rest]
--×     simp only [the_squares_at_the_link, what_multiplies_the_move_of_the_squares, what_the_squares_hold_of_the_move,
--×       Int.mul_add]
--×     omega

-- Episode13.lean, line 8493
--× theorem the_equation_in_a_link_over_the_other_ways {n : Nat} (state : Site4 n → Turns) (U : Torus4 n) (way : Direction)
--×     (x : Site4 n) (X : Turns) (t : Int) (others : List (Direction × Site4 n)) (they_are : are_other_ways way x others)
--×     (still : ∀ X, what_multiplies_the_move_of_the_squares U way x X others + (the_current_in_the_link state way x X).1 = 0) :
--×     the_squares_at_the_link (the_torus_with_one_link_moved U way x X t) way x others
--×         + (the_state_carried_back state (the_torus_with_one_link_moved U way x X t) way x).1
--×       = the_squares_at_the_link U way x others + (the_state_carried_back state U way x).1
--×         + t * t * what_the_squares_hold_of_the_move U way x X others := by
--×   have carried : (the_varied_turns (the_state_carried_back state U way x) (the_current_in_the_link state way x X) t).1
--×       = (the_state_carried_back state U way x).1 + t * (the_current_in_the_link state way x X).1 := rfl
--×   have nothing := still X
--×   have by_the_move : t * (what_multiplies_the_move_of_the_squares U way x X others
--×       + (the_current_in_the_link state way x X).1) = 0 := by rw [nothing, Int.mul_zero]
--×   rw [the_squares_at_the_link_with_the_link_moved U way x X t others they_are,
--×     the_state_carried_back_varies_by_the_current, carried]
--×   rw [Int.mul_add] at by_the_move
--×   omega

-- Episode13.lean, line 8518
--× theorem the_first_closure_is_not_under_the_second : ¬ (the_first_closure ≤ the_second_closure) := by
--×   intro under
--×   have unfolded : Closure.le the_first_closure the_second_closure := under
--×   have parts : Closure.le (.different (the_first_closure.infer.headD FACT.Truth) gawked_at_once gawked_at_twice
--×         (some (gawked_at_once < gawked_at_twice)))
--×       (.different (the_second_closure.infer.headD FACT.Truth) gawked_at_twice gawked_at_three_times
--×         (some (gawked_at_twice < gawked_at_three_times))) := unfolded
--×   simp only [Closure.le] at parts
--×   exact three_of_the_implications_go_and_one_does_not.2.2.2 parts.2.2.2

-- Episode13.lean, line 8536
--× def the_quantum_as_a_number : Number := Number.zero SAME_DIFFERENCE

-- Episode13.lean, line 8539
--× def the_fact_a_number_stands_on : Number → FACT
--×   | .zero fact => fact
--×   | .one fact _ => fact

-- Episode13.lean, line 8545
--× theorem the_step_five_times_is_the_step_once :
--×     the_first_card.interact_with_the_universe the_quantum_as_a_number = Number.zero FACT.Truth
--×       ∧ the_first_card.interact_with_the_universe (the_first_card.interact_with_the_universe
--×           (the_first_card.interact_with_the_universe (the_first_card.interact_with_the_universe
--×             (the_first_card.interact_with_the_universe the_quantum_as_a_number))))
--×         = the_first_card.interact_with_the_universe the_quantum_as_a_number := ⟨rfl, rfl⟩

-- Episode13.lean, line 8554
--× theorem the_residue_is_what_the_zero_stood_on :
--×     the_fact_a_number_stands_on the_quantum_as_a_number = SAME_DIFFERENCE
--×       ∧ the_fact_a_number_stands_on (the_first_card.interact_with_the_universe the_quantum_as_a_number) = FACT.Truth
--×       ∧ the_quantum_as_a_number.peano.length = 1
--×       ∧ (the_first_card.interact_with_the_universe the_quantum_as_a_number).peano.length = 1 := ⟨rfl, rfl, rfl, rfl⟩

-- Episode13.lean, line 8562
--× theorem asked_only_whether_it_is_true_the_quantum_was_there_already :
--×     the_quantum_as_a_number = the_first_card.interact_with_the_universe the_quantum_as_a_number :=
--×   congrArg Number.zero
--×     (two_facts_that_are_true_are_one_fact SAME_DIFFERENCE FACT.Truth same_difference_clicks
--×       (@of_decide_eq_true _ FACT.Truth.click rfl))

-- Episode13.lean, line 8570
--× theorem the_knowers_alpha_begins_on_what_the_step_repeats :
--×     ∃ low slip slipped the_rest,
--×       the_alpha = .inferred
--×         (the_fact_a_number_stands_on (the_first_card.interact_with_the_universe the_quantum_as_a_number))
--×         (the_fact_a_number_stands_on (the_first_card.interact_with_the_universe the_quantum_as_a_number))
--×         low slip slipped the_rest :=
--×   what_the_first_rung_says_comes_out_at_the_top.2

-- Episode13.lean, line 8587
--× def the_card_three_deep : CarrierProcess (CarrierProcess (CarrierProcess FACT)) :=
--×   { symbol := FACT.Truth, quarter := .zero FACT.Truth }

-- Episode13.lean, line 8592
--× def a_card_with_the_devices_step (box : Type) (symbol : FACT) (quarter : Number) : CarrierProcess box :=
--×   { symbol := symbol, quarter := quarter }

-- Episode13.lean, line 8595
--× theorem the_step_is_keyed_to_its_quarter (box : Type) (symbol fact glue : FACT) (quarter n : Number) :
--×     (a_card_with_the_devices_step box symbol quarter).interact_with_the_universe (.zero fact) = .zero FACT.Truth
--×       ∧ (a_card_with_the_devices_step box symbol quarter).interact_with_the_universe (.one glue n) = .one glue quarter :=
--×   ⟨rfl, rfl⟩

-- Episode13.lean, line 8600
--× theorem with_the_devices_step_twice_is_once (box : Type) (symbol : FACT) (quarter n : Number) :
--×     (a_card_with_the_devices_step box symbol quarter).interact_with_the_universe
--×         ((a_card_with_the_devices_step box symbol quarter).interact_with_the_universe n)
--×       = (a_card_with_the_devices_step box symbol quarter).interact_with_the_universe n := by
--×   cases n <;> rfl

-- Episode13.lean, line 8606
--× theorem every_card_steps_twice_as_once (n : Number) :
--×     elaborated_by_lean.interact_with_the_universe (elaborated_by_lean.interact_with_the_universe n)
--×         = elaborated_by_lean.interact_with_the_universe n
--×       ∧ the_first_card.interact_with_the_universe (the_first_card.interact_with_the_universe n)
--×         = the_first_card.interact_with_the_universe n
--×       ∧ the_card_between.interact_with_the_universe (the_card_between.interact_with_the_universe n)
--×         = the_card_between.interact_with_the_universe n
--×       ∧ the_card_three_deep.interact_with_the_universe (the_card_three_deep.interact_with_the_universe n)
--×         = the_card_three_deep.interact_with_the_universe n
--×       ∧ the_carrier_process.interact_with_the_universe (the_carrier_process.interact_with_the_universe n)
--×         = the_carrier_process.interact_with_the_universe n := by
--×   cases n <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩

-- Episode13.lean, line 8619
--× theorem from_three_deep_five_times_is_once (n : Number) :
--×     the_card_three_deep.interact_with_the_universe (the_card_three_deep.interact_with_the_universe
--×         (the_card_three_deep.interact_with_the_universe (the_card_three_deep.interact_with_the_universe
--×           (the_card_three_deep.interact_with_the_universe n))))
--×       = the_card_three_deep.interact_with_the_universe n := by
--×   cases n <;> rfl

-- Episode13.lean, line 8628
--× def is_a_one : Number → Bool
--×   | .zero _  => false
--×   | .one _ _ => true

-- Episode13.lean, line 8632
--× theorem the_step_keeps_the_kind (box : Type) (symbol : FACT) (quarter n : Number) :
--×     is_a_one ((a_card_with_the_devices_step box symbol quarter).interact_with_the_universe n) = is_a_one n := by
--×   cases n <;> rfl

-- Episode13.lean, line 8637
--× def a_card_that_writes_its_own_step : CarrierProcess FACT :=
--×   { symbol := FACT.Truth, quarter := .zero FACT.Truth, interact_with_the_universe := fun n => .one FACT.Truth n }

-- Episode13.lean, line 8640
--× theorem a_card_of_its_own_need_not_keep_the_kind :
--×     is_a_one (a_card_that_writes_its_own_step.interact_with_the_universe (.zero FACT.Truth)) ≠ is_a_one (.zero FACT.Truth) := by
--×   decide

-- Episode13.lean, line 8652
--× def the_matter_at_the_site {n : Nat} (state : Site4 n → Turns) (U : Torus4 n) (way : Direction) (x : Site4 n) : Int :=
--×   (the_state_carried_back state U way x).1 + (the_state_against_itself state x).1

-- Episode13.lean, line 8662
--× theorem the_matter_at_the_site_with_the_state_moved {n : Nat} (state : Site4 n → Turns) (U : Torus4 n) (way : Direction)
--×     (x : Site4 n) (Y : Turns) (t : Int) (the_step_leaves : the_step way x ≠ x) :
--×     the_matter_at_the_site (the_state_with_one_site_moved state x Y t) U way x
--×       = the_matter_at_the_site state U way x + t * what_multiplies_the_move_of_the_state state U way x Y
--×         + t * t * (the_turns_product (the_turns_conjugate Y) Y).1 := by
--×   show (the_state_carried_back (the_state_with_one_site_moved state x Y t) U way x).1
--×       + (the_state_against_itself (the_state_with_one_site_moved state x Y t) x).1 = _
--×   rw [moved_at_the_near_end state U way x Y t the_step_leaves, the_state_against_itself_with_the_state_moved]
--×   simp only [the_matter_at_the_site, what_multiplies_the_move_of_the_state, the_varied_turns, the_state_carried_back,
--×     the_state_against_itself, Int.mul_add, Int.mul_assoc]
--×   omega

-- Episode13.lean, line 8679
--× theorem no_state_stands_still_on_any_links {n : Nat} (U : Torus4 n) (way : Direction) (x : Site4 n) :
--×     the_state_stands_still_at_the_site (no_state (n := n)) U way x := by
--×   intro Y
--×   simp [what_multiplies_the_move_of_the_state, no_state, the_turns_product, the_turns_conjugate]

-- Episode13.lean, line 8685
--× theorem the_vacuum_meets_the_equation_over_every_other_way {n : Nat} (way : Direction) (x : Site4 n) (X : Turns) :
--×     ∀ others : List (Direction × Site4 n),
--×       what_multiplies_the_move_of_the_squares (the_whole_turn_on_every_link (n := n)) way x X others
--×         + (the_current_in_the_link (no_state (n := n)) way x X).1 = 0
--×   | [] => by simp [what_multiplies_the_move_of_the_squares, the_current_in_the_link, no_state, the_turns_product,
--×       the_turns_conjugate]
--×   | (other, behind) :: rest => by
--×     have the_rest := the_vacuum_meets_the_equation_over_every_other_way way x X rest
--×     have ahead : the_square4 (the_whole_turn_on_every_link (n := n)) way other x = the_whole_turn 1 := rfl
--×     have back : the_square4 (the_whole_turn_on_every_link (n := n)) other way behind = the_whole_turn 1 := rfl
--×     simp only [what_multiplies_the_move_of_the_squares, ahead, back, a_whole_turn_is_stationary]
--×     omega

-- Episode13.lean, line 8706
--× def the_marks_of_the_phrases : List Bool := the_phrases.map fun phrase => phrase.1 == phrase.2
--× def read_as_one_number (marks : List Bool) : Nat := marks.foldl (fun so_far mark => 2 * so_far + (if mark then 1 else 0)) 0

-- Episode13.lean, line 8709
--× theorem thirty_two_marks_sixteen_of_each :
--×     the_marks_of_the_phrases.length = 32 ∧ (the_marks_of_the_phrases.filter id).length = 16 := by decide

-- Episode13.lean, line 8713
--× theorem the_phrases_read_as_one_number :
--×     read_as_one_number the_marks_of_the_phrases = 3946922475
--×       ∧ [read_as_one_number (the_marks_of_the_phrases.take 8),
--×          read_as_one_number ((the_marks_of_the_phrases.drop 8).take 8),
--×          read_as_one_number ((the_marks_of_the_phrases.drop 16).take 8),
--×          read_as_one_number (the_marks_of_the_phrases.drop 24)] = [235, 65, 65, 235] := by decide

-- Episode13.lean, line 8729
--× theorem the_phase_cannot_be_recovered_from_the_norm :
--×     ¬ can_be_recovered (fun _ : Int × Int => True) the_gaussian_norm id :=
--×   the_same_kept_and_two_identifications_cannot_be_recovered _ _ _ (0, 1) (0, -1) trivial trivial (by decide) (by decide)

-- Episode13.lean, line 8733
--× def what_was_carried : Number → Bool
--×   | .zero _ => false
--×   | .one _ carried => is_a_one carried

-- Episode13.lean, line 8737
--× theorem what_was_carried_cannot_be_recovered_after_the_card_betweens_step :
--×     ¬ can_be_recovered (fun _ : Number => True) the_representation.the_card_between.interact_with_the_universe what_was_carried :=
--×   the_same_kept_and_two_identifications_cannot_be_recovered _ _ _
--×     (.one FACT.Truth (.zero FACT.Truth)) (.one FACT.Truth (.one FACT.Truth (.zero FACT.Truth))) trivial trivial rfl (by decide)

-- Episode13.lean, line 8743
--× theorem the_slope_is_the_only_linear_part (y L c : Int)
--×     (bracket : ∀ step : Int, the_residual_at (y + step) - the_residual_at y - L * step = c * (step * step)) :
--×     L = 26 * y - 36 := by
--×   have h1 := bracket 1
--×   have h2 := bracket (-1)
--×   have e1 := the_jacobian_free_difference_is_exact y 1
--×   have e2 := the_jacobian_free_difference_is_exact y (-1)
--×   simp only [Int.mul_one, Int.mul_neg, Int.neg_neg] at h1 h2 e1 e2
--×   omega

-- Episode13.lean, line 8756
--× def the_line_through (v h : Bool → Int) (t : Int) : Bool → Int := fun x => v x + t * h x
--× def the_gateaux_of_the_action (A : Table) (v h : Bool → Int) : Int :=
--×   (h true * the_refine A v true + h false * the_refine A v false)
--×     + (h true * the_refine A v true + h false * the_refine A v false)

-- Episode13.lean, line 8761
--× theorem the_action_along_a_line (A : Table) (sym : A true false = A false true) (v h : Bool → Int) (t : Int) :
--×     the_action_of A (the_line_through v h t) = the_action_of A v + t * the_gateaux_of_the_action A v h + t * t * the_action_of A h := by
--×   simp only [the_action_of, the_refine, the_line_through, the_gateaux_of_the_action, sym, Int.mul_add, Int.add_mul]
--×   ac_nf

-- Episode13.lean, line 8766
--× theorem the_gateaux_derivative_is_one_thing (A : Table) (sym : A true false = A false true) (v h : Bool → Int) (D R : Int)
--×     (line : ∀ t : Int, the_action_of A (the_line_through v h t) = the_action_of A v + t * D + t * t * R) :
--×     D = the_gateaux_of_the_action A v h := by
--×   have l1 := line 1
--×   have l2 := line (-1)
--×   rw [the_action_along_a_line A sym] at l1 l2
--×   simp only [Int.one_mul, Int.neg_mul, Int.neg_neg, Int.mul_one] at l1 l2
--×   omega

-- Episode13.lean, line 8777
--× theorem the_weak_form_is_the_strong_form (r : Bool → Int) :
--×     (∀ h : Bool → Int, h true * r true + h false * r false = 0) ↔ (r true = 0 ∧ r false = 0) := by
--×   constructor
--×   · intro w
--×     have a := w (fun c => if c then 1 else 0)
--×     have b := w (fun c => if c then 0 else 1)
--×     simp at a b
--×     exact ⟨a, b⟩
--×   · intro ⟨a, b⟩ h
--×     rw [a, b, Int.mul_zero, Int.mul_zero, Int.add_zero]

-- Episode13.lean, line 8791
--× theorem at_the_root_the_direction_up_meets_the_weak_form :
--×     ∀ coin, the_surd_product the_outer_radius (the_direction_up coin) = refined_in_pairs the_full_table the_direction_up coin :=
--×   fun coin => (the_table_carries_the_two_directions_exactly.1 coin).symm

-- Episode13.lean, line 8812
--× def Formula.native (env : Nat → Int) : Formula → Int
--×   | .place i => env i
--×   | .whole z => z
--×   | .beside a b => a.native env + b.native env
--×   | .less a b => a.native env - b.native env
--×   | .eachForEach a b => a.native env * b.native env

-- Episode13.lean, line 8819
--× def Formula.onTheDevice (env : Nat → Account) : Formula → Account
--×   | .place i => env i
--×   | .whole z => an_account_of z
--×   | .beside a b => a.onTheDevice env + b.onTheDevice env
--×   | .less a b => a.onTheDevice env - b.onTheDevice env
--×   | .eachForEach a b => a.onTheDevice env * b.onTheDevice env

-- Episode13.lean, line 8826
--× theorem the_device_computes_what_lean_computes (env : Nat → Account) (f : Formula) :
--×     balance (f.onTheDevice env) = f.native (fun i => balance (env i)) := by
--×   induction f with
--×   | place i => rfl
--×   | whole z => exact an_account_of_balances z
--×   | beside a b iha ihb => show balance (_ + _) = _; rw [balance_of_palm_the_middle_card, iha, ihb]; rfl
--×   | less a b iha ihb => show balance (_ - _) = _; rw [balance_of_less, iha, ihb]; rfl
--×   | eachForEach a b iha ihb => show balance (_ * _) = _; rw [balance_of_false_shuffle, iha, ihb]; rfl

-- Episode13.lean, line 8835
--× theorem no_reader_tells_the_native_from_the_device {α : Sort _} (reader : Int → α) (env : Nat → Account) (f : Formula) :
--×     reader (balance (f.onTheDevice env)) = reader (f.native (fun i => balance (env i))) := by
--×   rw [the_device_computes_what_lean_computes]

-- Episode13.lean, line 8844
--× def the_momentum_residual : Formula :=
--×   .less (.beside (.beside (.less (.less (.place 3) (.place 0))
--×       (.eachForEach (.place 7) (.beside (.less (.place 1) (.place 0)) (.less (.place 2) (.place 0)))))
--×       (.eachForEach (.place 0) (.less (.place 1) (.place 2))))
--×       (.less (.place 4) (.place 5)))
--×     (.place 6)

-- Episode13.lean, line 8851
--× def the_response_action : Formula :=
--×   .beside (.eachForEach (.place 8) the_momentum_residual) (.eachForEach (.place 9) (.less (.place 1) (.place 2)))

-- Episode13.lean, line 8854
--× theorem cards_three_action_is_computed_alike_on_the_device (env : Nat → Account) :
--×     balance (the_response_action.onTheDevice env) = the_response_action.native (fun i => balance (env i)) :=
--×   the_device_computes_what_lean_computes env the_response_action

-- Episode13.lean, line 8861
--× def the_native_and_the_device_are_one (env : Nat → Account) : FACT :=
--×   { truth := balance (the_response_action.onTheDevice env) = the_response_action.native (fun i => balance (env i)),
--×     click := inferInstance }

-- Episode13.lean, line 8865
--× theorem the_native_and_the_device_are_the_truth (env : Nat → Account) :
--×     the_native_and_the_device_are_one env = FACT.Truth :=
--×   two_facts_that_are_true_are_one_fact _ _ (cards_three_action_is_computed_alike_on_the_device env)
--×     (@of_decide_eq_true _ FACT.Truth.click rfl)

-- Episode13.lean, line 8884
--× def the_epilogues_quartic (c t x r : Int) : Int := t * t * (c - t) * (x * x) - 2 * c * t * (r * r) * x + c * ((r * r) * (r * r))

-- Episode13.lean, line 8886
--× theorem the_quartic_is_a_residual_of_a_pair (c t x r : Int) :
--×     the_epilogues_quartic c t x r = (c - t) * ((t * x) * (t * x)) - 2 * c * ((t * x) * (r * r)) + c * ((r * r) * (r * r)) := by
--×   unfold the_epilogues_quartic; simp only [Int.mul_sub, Int.sub_mul]; ac_nf

-- Episode13.lean, line 8890
--× theorem at_the_devices_weights_the_quartic_is_the_residual_of_the_pair (x r : Int) :
--×     the_epilogues_quartic 18 5 x r = the_residual_of_the_pair (5 * x) (r * r) := by
--×   rw [the_quartic_is_a_residual_of_a_pair]; unfold the_residual_of_the_pair; ac_nf

-- Episode13.lean, line 8894
--× theorem a_form_varies_by_its_slope (a b c N D k : Int) :
--×     a * ((N + k) * (N + k)) - b * ((N + k) * D) + c * (D * D) - (a * (N * N) - b * (N * D) + c * (D * D))
--×       = k * (a * N + a * N - b * D) + a * (k * k) := by
--×   simp only [Int.mul_add, Int.add_mul, Int.mul_sub]; ac_nf; omega

-- Episode13.lean, line 8899
--× theorem the_determinant_varies_by_the_trace_of_the_adjugate (N D k : Int) :
--×     the_residual_of_the_pair (N + k) D - the_residual_of_the_pair N D
--×       = k * the_table_trace (the_adjugate (the_table_taken_from_the_same N D)) + 13 * (k * k) := by
--×   rw [the_trace_of_its_adjugate_is_the_slope, show 26 * N - 36 * D = 13 * N + 13 * N - 36 * D by omega]
--×   exact a_form_varies_by_its_slope 13 36 18 N D k

-- Episode13.lean, line 8905
--× theorem the_quartic_varies_by_the_trace_of_the_adjugate (x r h : Int) :
--×     the_epilogues_quartic 18 5 (x + h) r - the_epilogues_quartic 18 5 x r
--×       = 5 * h * the_table_trace (the_adjugate (the_table_taken_from_the_same (5 * x) (r * r))) + 325 * (h * h) := by
--×   rw [at_the_devices_weights_the_quartic_is_the_residual_of_the_pair, at_the_devices_weights_the_quartic_is_the_residual_of_the_pair,
--×     show 5 * (x + h) = 5 * x + 5 * h by omega, the_determinant_varies_by_the_trace_of_the_adjugate]
--×   simp only [Int.mul_assoc]; ac_nf

-- Episode13.lean, line 8919
--× theorem the_exact_taylor_series_degree_is_the_bent_card : an_exact_polynomial_description = 13 := by decide

-- Episode13.lean, line 8921
--× theorem the_taylor_series_of_a_cubic (a b c d y h : Int) :
--×     a + b * (y + h) + c * ((y + h) * (y + h)) + d * ((y + h) * (y + h) * (y + h))
--×       = (a + b * y + c * (y * y) + d * (y * y * y))
--×         + (b + (c * y + c * y) + (d * (y * y) + d * (y * y) + d * (y * y))) * h
--×         + (c + (d * y + d * y + d * y)) * (h * h)
--×         + d * (h * h * h) := by
--×   simp only [Int.mul_add, Int.add_mul]; ac_nf

-- Episode13.lean, line 8929
--× theorem the_residuals_taylor_series_stops_at_the_bent_card (y h : Int) :
--×     the_residual_at (y + h) = the_residual_at y + (26 * y - 36) * h + an_exact_polynomial_description * (h * h) := by
--×   rw [the_exact_taylor_series_degree_is_the_bent_card]
--×   have := the_jacobian_free_difference_is_exact y h
--×   omega

-- Episode13.lean, line 8939
--× def the_action_of_the_weighed_table (h : Bool → Int) : Int := the_action_of (weighed_by_its_coin the_full_table) h

-- Episode13.lean, line 8941
--× theorem the_action_of_the_weighed_table_written (h : Bool → Int) :
--×     the_action_of_the_weighed_table h = 324 * (h true * h true) + 90 * (h true * h false) + 90 * (h true * h false) + 90 * (h false * h false) := by
--×   show h true * (18 * 18 * h true + 18 * 5 * h false) + h false * (5 * 18 * h true + 5 * 18 * h false) = _
--×   simp only [Int.mul_add]; ac_nf

-- Episode13.lean, line 8946
--× theorem the_remainder_is_never_negative (h : Bool → Int) : 0 ≤ the_action_of_the_weighed_table h := by
--×   rw [the_action_of_the_weighed_table_written]
--×   exact Meanings.the_form_is_never_negative 324 90 90 _ _ (by decide) (by decide)

-- Episode13.lean, line 8950
--× theorem the_remainder_is_bounded_by_the_norm_in_every_direction (h : Bool → Int) :
--×     the_action_of_the_weighed_table h ≤ 28 * the_weighed_square h := by
--×   have f := Meanings.the_form_is_never_negative 180 (-90) 50 (h true) (h false) (by decide) (by decide)
--×   rw [the_action_of_the_weighed_table_written]; unfold the_weighed_square
--×   omega

-- Episode13.lean, line 8956
--× theorem the_frechet_derivative_is_linear (A : Table) (v h k : Bool → Int) (t : Int) :
--×     the_gateaux_of_the_action A v (fun x => h x + k x) = the_gateaux_of_the_action A v h + the_gateaux_of_the_action A v k
--×       ∧ the_gateaux_of_the_action A v (fun x => t * h x) = t * the_gateaux_of_the_action A v h := by
--×   unfold the_gateaux_of_the_action
--×   constructor
--×   · simp only [Int.add_mul]; omega
--×   · simp only [Int.mul_assoc, Int.mul_add]

-- Episode13.lean, line 8966
--× theorem the_weighed_table_is_the_same_turned_over_as_a_table :
--×     weighed_by_its_coin the_full_table true false = weighed_by_its_coin the_full_table false true :=
--×   the_table_weighed_is_the_same_turned_over.1

-- Episode13.lean, line 8970
--× theorem the_frechet_expansion_of_the_action (v h : Bool → Int) :
--×     the_action_of (weighed_by_its_coin the_full_table) (the_line_through v h 1)
--×         = the_action_of (weighed_by_its_coin the_full_table) v
--×           + the_gateaux_of_the_action (weighed_by_its_coin the_full_table) v h + the_action_of_the_weighed_table h
--×       ∧ 0 ≤ the_action_of_the_weighed_table h ∧ the_action_of_the_weighed_table h ≤ 28 * the_weighed_square h := by
--×   refine ⟨?_, the_remainder_is_never_negative h, the_remainder_is_bounded_by_the_norm_in_every_direction h⟩
--×   rw [the_action_along_a_line _ the_weighed_table_is_the_same_turned_over_as_a_table]
--×   simp only [Int.one_mul]; rfl

-- Episode13.lean, line 8979
--× theorem the_gateaux_is_the_frechet_in_a_direction (v h : Bool → Int) (t : Int) :
--×     the_action_of (weighed_by_its_coin the_full_table) (the_line_through v h t)
--×       = the_action_of (weighed_by_its_coin the_full_table) v
--×         + the_gateaux_of_the_action (weighed_by_its_coin the_full_table) v (fun x => t * h x)
--×         + t * t * the_action_of_the_weighed_table h := by
--×   rw [the_action_along_a_line _ the_weighed_table_is_the_same_turned_over_as_a_table,
--×     (the_frechet_derivative_is_linear _ v h h t).2]; rfl

-- Episode13.lean, line 8991
--× theorem the_action_passes_twenty_seven_somewhere :
--×     27 * the_weighed_square (fun c => if c then 50 else 95) < the_action_of_the_weighed_table (fun c => if c then 50 else 95) := by decide

-- Episode13.lean, line 8994
--× theorem the_least_action_is_reached_in_the_pairs :
--×     the_pairing_in_pairs (refined_in_pairs the_full_table the_direction_up) the_direction_up
--×       = the_surd_product the_outer_radius (the_pairing_in_pairs the_direction_up the_direction_up) := by decide

-- Episode13.lean, line 9004
--× theorem the_table_is_its_covariant_part_and_its_contravariant_part (a b : Bool) :
--×     2 * the_full_table a b = (the_full_table a b + the_full_table b a) + (the_full_table a b - the_full_table b a) := by omega

-- Episode13.lean, line 9020
--× def a_steady_row (start step : Int) : Turns := (0, start, start + step, start + step + step)

-- Episode13.lean, line 9022
--× theorem the_cross_of_two_steady_rows_is_the_second_difference (a d b e : Int) :
--×     (the_turns_product (a_steady_row a d) (a_steady_row b e)).2
--×       = (a * e - b * d, -(a * e - b * d) - (a * e - b * d), a * e - b * d) := by
--×   simp only [the_turns_product, a_steady_row]
--×   refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> dsimp only <;> simp only [Int.mul_add, Int.add_mul, Int.zero_mul, Int.mul_zero] <;> ac_nf <;> omega

-- Episode13.lean, line 9028
--× theorem thirteen_fourteen_fifteen_across_three_four_five :
--×     (the_turns_product (a_steady_row 13 1) (a_steady_row 3 1)).2 = (10, -20, 10) := by decide

-- Episode13.lean, line 9032
--× theorem the_stencil_reads_nothing_on_a_steady_row (a d : Int) : a - 2 * (a + d) + (a + d + d) = 0 := by omega

-- Episode13.lean, line 9034
--× theorem the_second_difference_twice_is_the_fourth (f : Int → Int) (x : Int) :
--×     (f x - 2 * f (x + 1) + f (x + 2)) - 2 * (f (x + 1) - 2 * f (x + 2) + f (x + 3)) + (f (x + 2) - 2 * f (x + 3) + f (x + 4))
--×       = f x - 4 * f (x + 1) + 6 * f (x + 2) - 4 * f (x + 3) + f (x + 4) := by omega

-- Episode13.lean, line 9042
--× theorem the_triple_reads_the_second_difference (f₁ f₂ f₃ a d b e : Int) :
--×     f₁ * (the_turns_product (a_steady_row a d) (a_steady_row b e)).2.1
--×       + f₂ * (the_turns_product (a_steady_row a d) (a_steady_row b e)).2.2.1
--×       + f₃ * (the_turns_product (a_steady_row a d) (a_steady_row b e)).2.2.2
--×       = (a * e - b * d) * (f₁ - f₂ - f₂ + f₃) := by
--×   rw [the_cross_of_two_steady_rows_is_the_second_difference]
--×   dsimp only
--×   generalize a * e - b * d = k
--×   simp only [Int.mul_sub, Int.mul_add, Int.mul_neg]
--×   ac_nf; omega

-- Episode13.lean, line 9053
--× theorem three_first_variations_make_nothing (c s a d b e : Int) :
--×     c * (the_turns_product (a_steady_row a d) (a_steady_row b e)).2.1
--×       + (c + s) * (the_turns_product (a_steady_row a d) (a_steady_row b e)).2.2.1
--×       + (c + s + s) * (the_turns_product (a_steady_row a d) (a_steady_row b e)).2.2.2 = 0 := by
--×   rw [the_triple_reads_the_second_difference]
--×   rw [show c - (c + s) - (c + s) + (c + s + s) = 0 by omega, Int.mul_zero]

-- Episode13.lean, line 9063
--× theorem the_second_variation_summed_is_the_first_at_the_ends (reading : Nat → Int) (steps : Nat) :
--×     summed_along steps (the_difference_along (the_difference_along reading))
--×       = the_difference_along reading steps - the_difference_along reading 0 :=
--×   a_difference_summed_is_the_end_less_the_first (the_difference_along reading) steps

-- Episode13.lean, line 9083
--× def a_turn_of_the_crank_for (c t m : Int) (p : Int × Int) : Int × Int :=
--×   (c * (p.1 * p.1) - m * (p.2 * p.2), (c + c) * (p.1 * p.2) - (t + t) * (p.2 * p.2))

-- Episode13.lean, line 9086
--× def the_distance_up_for (c t : Int) (p : Int × Int) : Int × Int := (c * p.1 - t * p.2, - p.2)
--× def the_distance_down_for (c t : Int) (p : Int × Int) : Int × Int := (c * p.1 - t * p.2, p.2)

-- Episode13.lean, line 9089
--× theorem a_turn_squares_the_distance_for (c t m ρ : Int) (round_trip : ρ = t * t - c * m) (p : Int × Int) :
--×     the_distance_up_for c t (a_turn_of_the_crank_for c t m p)
--×         = ((the_distance_up_for c t p).1 * (the_distance_up_for c t p).1 + ρ * (the_distance_up_for c t p).2 * (the_distance_up_for c t p).2,
--×            (the_distance_up_for c t p).1 * (the_distance_up_for c t p).2 + (the_distance_up_for c t p).2 * (the_distance_up_for c t p).1)
--×       ∧ the_distance_down_for c t (a_turn_of_the_crank_for c t m p)
--×         = ((the_distance_down_for c t p).1 * (the_distance_down_for c t p).1 + ρ * (the_distance_down_for c t p).2 * (the_distance_down_for c t p).2,
--×            (the_distance_down_for c t p).1 * (the_distance_down_for c t p).2 + (the_distance_down_for c t p).2 * (the_distance_down_for c t p).1) := by
--×   obtain ⟨N, D⟩ := p
--×   subst round_trip
--×   simp only [the_distance_up_for, the_distance_down_for, a_turn_of_the_crank_for]
--×   refine ⟨Prod.ext ?_ ?_, Prod.ext ?_ ?_⟩ <;> dsimp only <;>
--×     simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul, Int.neg_mul, Int.mul_neg, Int.neg_neg] <;> ac_nf <;> omega

-- Episode13.lean, line 9102
--× theorem the_round_trip_is_the_trace_half_squared_less_the_coefficient_by_the_memory : the_round_trip = 18 * 18 - 13 * 18 := by decide

-- Episode13.lean, line 9104
--× def a_turn_of_the_crank : Int × Int → Int × Int := a_turn_of_the_crank_for 13 18 18
--× def the_distance_to_the_upper_root : Int × Int → Int × Int := the_distance_up_for 13 18
--× def the_distance_to_the_lower_root : Int × Int → Int × Int := the_distance_down_for 13 18

-- Episode13.lean, line 9108
--× theorem a_turn_squares_the_distance (p : Int × Int) :
--×     the_distance_to_the_upper_root (a_turn_of_the_crank p)
--×         = the_surd_product (the_distance_to_the_upper_root p) (the_distance_to_the_upper_root p)
--×       ∧ the_distance_to_the_lower_root (a_turn_of_the_crank p)
--×         = the_surd_product (the_distance_to_the_lower_root p) (the_distance_to_the_lower_root p) := by
--×   have h := a_turn_squares_the_distance_for 13 18 18 the_round_trip the_round_trip_is_the_trace_half_squared_less_the_coefficient_by_the_memory p
--×   rw [Int.mul_assoc, Int.mul_assoc] at h
--×   simp only [the_surd_product, Int.mul_assoc]
--×   exact h

-- Episode13.lean, line 9118
--× def turns_of_the_crank (start : Int × Int) : Nat → Int × Int
--×   | 0 => start
--×   | k + 1 => a_turn_of_the_crank (turns_of_the_crank start k)

-- Episode13.lean, line 9122
--× def squared_again (z : Int × Int) : Nat → Int × Int
--×   | 0 => z
--×   | k + 1 => the_surd_product (squared_again z k) (squared_again z k)

-- Episode13.lean, line 9126
--× theorem after_any_number_of_turns_the_distance_is_squared_that_many_times (start : Int × Int) (k : Nat) :
--×     the_distance_to_the_upper_root (turns_of_the_crank start k) = squared_again (the_distance_to_the_upper_root start) k
--×       ∧ the_distance_to_the_lower_root (turns_of_the_crank start k) = squared_again (the_distance_to_the_lower_root start) k := by
--×   induction k with
--×   | zero => exact ⟨rfl, rfl⟩
--×   | succ k ih =>
--×     obtain ⟨u, l⟩ := ih
--×     show the_distance_to_the_upper_root (a_turn_of_the_crank _) = the_surd_product _ _
--×       ∧ the_distance_to_the_lower_root (a_turn_of_the_crank _) = the_surd_product _ _
--×     rw [(a_turn_squares_the_distance _).1, (a_turn_squares_the_distance _).2, u, l]
--×     exact ⟨rfl, rfl⟩

-- Episode13.lean, line 9151
--× theorem a_modulus_from_statements (serves : Nat → Nat → Prop) (continuous : ∀ k, ∃ m, serves k m) :
--×     ∃ modulus : Nat → Nat, ∀ k, serves k (modulus k) ∧ ∀ m, m < modulus k → ¬ serves k m :=
--×   Meanings.a_modulus_without_the_click serves continuous

-- Episode13.lean, line 9169
--× def the_residual_for (c t m N D : Int) : Int := c * (N * N) - (t + t) * (N * D) + m * (D * D)

-- Episode13.lean, line 9171
--× theorem a_turn_squares_the_residual_for (c t m : Int) (p : Int × Int) :
--×     the_residual_for c t m (a_turn_of_the_crank_for c t m p).1 (a_turn_of_the_crank_for c t m p).2
--×       = c * (the_residual_for c t m p.1 p.2 * the_residual_for c t m p.1 p.2) := by
--×   obtain ⟨N, D⟩ := p
--×   simp only [the_residual_for, a_turn_of_the_crank_for]
--×   simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul]; ac_nf; omega

-- Episode13.lean, line 9178
--× theorem a_turn_moves_by_the_residual_for (c t m : Int) (p : Int × Int) :
--×     (a_turn_of_the_crank_for c t m p).1 * p.2 - p.1 * (a_turn_of_the_crank_for c t m p).2
--×       = - (p.2 * the_residual_for c t m p.1 p.2) := by
--×   obtain ⟨N, D⟩ := p
--×   simp only [the_residual_for, a_turn_of_the_crank_for]
--×   simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul, Int.neg_add, Int.neg_sub]; ac_nf; omega

-- Episode13.lean, line 9185
--× theorem a_turns_second_is_twice_the_second_by_the_distance_for (c t m : Int) (p : Int × Int) :
--×     (a_turn_of_the_crank_for c t m p).2 = (p.2 + p.2) * (c * p.1 - t * p.2) := by
--×   obtain ⟨N, D⟩ := p
--×   simp only [a_turn_of_the_crank_for]
--×   simp only [Int.add_mul, Int.mul_sub]; ac_nf

-- Episode13.lean, line 9192
--× def on_the_upper_side (p : Int × Int) : Prop := 0 < p.2 ∧ 18 * p.2 < 13 * p.1

-- Episode13.lean, line 9194
--× theorem the_residual_of_the_pair_is_the_residual_for (N D : Int) :
--×     the_residual_of_the_pair N D = the_residual_for 13 18 18 N D := by
--×   unfold the_residual_of_the_pair the_residual_for; omega

-- Episode13.lean, line 9198
--× theorem a_turn_keeps_the_upper_side (p : Int × Int) (side : on_the_upper_side p) :
--×     on_the_upper_side (a_turn_of_the_crank p) := by
--×   obtain ⟨d, a⟩ := side
--×   have second := a_turns_second_is_twice_the_second_by_the_distance_for 13 18 18 p
--×   have sq := congrArg Prod.fst (a_turn_squares_the_distance p).1
--×   simp only [the_distance_to_the_upper_root, the_distance_up_for, the_surd_product] at sq
--×   have rt : the_round_trip = 90 := by decide
--×   rw [rt] at sq
--×   have nn := Meanings.a_square_is_never_negative (13 * p.1 - 18 * p.2)
--×   have dd : 0 < p.2 * p.2 := Int.mul_pos d d
--×   have negneg : 90 * -p.2 * -p.2 = 90 * (p.2 * p.2) := by rw [Int.mul_assoc, Int.neg_mul_neg]
--×   rw [negneg] at sq
--×   refine ⟨?_, ?_⟩
--×   · show 0 < (a_turn_of_the_crank_for 13 18 18 p).2
--×     rw [second]; exact Int.mul_pos (by omega) (by omega)
--×   · show 18 * (a_turn_of_the_crank_for 13 18 18 p).2 < 13 * (a_turn_of_the_crank_for 13 18 18 p).1
--×     have : 13 * (a_turn_of_the_crank_for 13 18 18 p).1 - 18 * (a_turn_of_the_crank_for 13 18 18 p).2
--×         = (13 * p.1 - 18 * p.2) * (13 * p.1 - 18 * p.2) + 90 * (p.2 * p.2) := sq
--×     omega

-- Episode13.lean, line 9218
--× theorem after_a_turn_never_below_the_upper_root (p : Int × Int) :
--×     0 ≤ the_residual_of_the_pair (a_turn_of_the_crank p).1 (a_turn_of_the_crank p).2 := by
--×   rw [the_residual_of_the_pair_is_the_residual_for]
--×   show 0 ≤ the_residual_for 13 18 18 (a_turn_of_the_crank_for 13 18 18 p).1 (a_turn_of_the_crank_for 13 18 18 p).2
--×   rw [a_turn_squares_the_residual_for]
--×   exact Int.mul_nonneg (by decide) (Meanings.a_square_is_never_negative _)

-- Episode13.lean, line 9225
--× theorem above_the_root_a_turn_falls (p : Int × Int) (side : on_the_upper_side p)
--×     (above : 0 ≤ the_residual_of_the_pair p.1 p.2) :
--×     (a_turn_of_the_crank p).1 * p.2 ≤ p.1 * (a_turn_of_the_crank p).2 := by
--×   have mv := a_turn_moves_by_the_residual_for 13 18 18 p
--×   rw [the_residual_of_the_pair_is_the_residual_for] at above
--×   have : 0 ≤ p.2 * the_residual_for 13 18 18 p.1 p.2 := Int.mul_nonneg (Int.le_of_lt side.1) above
--×   show (a_turn_of_the_crank_for 13 18 18 p).1 * p.2 ≤ p.1 * (a_turn_of_the_crank_for 13 18 18 p).2
--×   omega

-- Episode13.lean, line 9235
--× def the_house_as_a_pair : Int × Int := (530, 324)

-- Episode13.lean, line 9237
--× theorem the_house_is_on_the_upper_side_below_the_root :
--×     on_the_upper_side the_house_as_a_pair ∧ the_residual_of_the_pair 530 324 < 0 :=
--×   ⟨⟨by decide, by decide⟩, by decide⟩

-- Episode13.lean, line 9241
--× theorem every_turn_from_the_house_is_on_the_upper_side (k : Nat) :
--×     on_the_upper_side (turns_of_the_crank the_house_as_a_pair k) := by
--×   induction k with
--×   | zero => exact the_house_is_on_the_upper_side_below_the_root.1
--×   | succ k ih => exact a_turn_keeps_the_upper_side _ ih

-- Episode13.lean, line 9247
--× theorem from_the_first_turn_on_it_is_above_the_root_and_falls (k : Nat) :
--×     0 ≤ the_residual_of_the_pair (turns_of_the_crank the_house_as_a_pair (k + 1)).1 (turns_of_the_crank the_house_as_a_pair (k + 1)).2
--×       ∧ (turns_of_the_crank the_house_as_a_pair (k + 2)).1 * (turns_of_the_crank the_house_as_a_pair (k + 1)).2
--×         ≤ (turns_of_the_crank the_house_as_a_pair (k + 1)).1 * (turns_of_the_crank the_house_as_a_pair (k + 2)).2 := by
--×   have above := after_a_turn_never_below_the_upper_root (turns_of_the_crank the_house_as_a_pair k)
--×   exact ⟨above, above_the_root_a_turn_falls _ (every_turn_from_the_house_is_on_the_upper_side (k + 1)) above⟩

-- Episode13.lean, line 9269
--× def the_crank_distance : Nat → Nat × Nat
--×   | 0 => (10567204, 685584)
--×   | k + 1 => ((the_crank_distance k).1 * (the_crank_distance k).1 + 90 * ((the_crank_distance k).2 * (the_crank_distance k).2),
--×              2 * ((the_crank_distance k).1 * (the_crank_distance k).2))

-- Episode13.lean, line 9274
--× theorem the_crank_distance_is_the_cranks (k : Nat) :
--×     the_distance_to_the_upper_root (turns_of_the_crank the_house_as_a_pair (k + 1))
--×       = (((the_crank_distance k).1 : Int), - ((the_crank_distance k).2 : Int)) := by
--×   induction k with
--×   | zero => decide
--×   | succ k ih =>
--×     show the_distance_to_the_upper_root (a_turn_of_the_crank _) = _
--×     rw [(a_turn_squares_the_distance _).1, ih]
--×     have rt : the_round_trip = 90 := by decide
--×     simp only [the_surd_product, the_crank_distance, rt]
--×     refine Prod.ext ?_ ?_ <;> dsimp only
--×     · rw [Int.mul_assoc, Int.neg_mul_neg, Int.natCast_add, Int.natCast_mul, Int.natCast_mul, Int.natCast_mul]; rfl
--×     · rw [Int.mul_neg, Int.neg_mul, ← Int.neg_add, Int.natCast_mul, Int.natCast_mul]
--×       congr 1; rw [Int.mul_comm ((the_crank_distance k).2 : Int)]; omega

-- Episode13.lean, line 9289
--× theorem two_products_under_two_squares (X Y : Nat) : X * Y + X * Y ≤ X * X + Y * Y := by
--×   rcases Nat.le_total X Y with h | h
--×   · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
--×     simp only [Nat.mul_add, Nat.add_mul, Nat.mul_comm d X]; omega
--×   · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
--×     simp only [Nat.mul_add, Nat.add_mul, Nat.mul_comm d Y]; omega

-- Episode13.lean, line 9296
--× theorem a_turn_stays_above (ρ a D : Nat) :
--×     ρ * ((2 * (a * D)) * (2 * (a * D))) ≤ (a * a + ρ * (D * D)) * (a * a + ρ * (D * D)) := by
--×   have h := two_products_under_two_squares (a * a) (ρ * (D * D))
--×   simp only [Nat.two_mul, Nat.mul_add, Nat.add_mul] at h ⊢
--×   simp only [Nat.mul_comm, Nat.mul_left_comm] at h ⊢
--×   omega

-- Episode13.lean, line 9303
--× theorem the_gap_squares (ρ a D g : Nat) (h : a * a = ρ * (D * D) + g) :
--×     (a * a + ρ * (D * D)) * (a * a + ρ * (D * D)) = ρ * ((2 * (a * D)) * (2 * (a * D))) + g * g := by
--×   have e : ρ * ((2 * (a * D)) * (2 * (a * D))) = (a * a) * (ρ * (D * D)) + (a * a) * (ρ * (D * D))
--×       + ((a * a) * (ρ * (D * D)) + (a * a) * (ρ * (D * D))) := by
--×     simp only [Nat.two_mul, Nat.mul_add, Nat.add_mul]
--×     simp only [Nat.mul_comm, Nat.mul_left_comm]
--×   rw [e, h]
--×   simp only [Nat.mul_add, Nat.add_mul]
--×   simp only [Nat.mul_comm, Nat.mul_left_comm]
--×   omega

-- Episode13.lean, line 9314
--× theorem the_gap_halves (ρ a D g : Nat) (h : a * a = ρ * (D * D) + g) :
--×     2 * (g * g) * (D * a) ≤ g * ((2 * (a * D)) * (a * a + ρ * (D * D))) := by
--×   have le : g ≤ a * a + ρ * (D * D) := by omega
--×   have := Nat.mul_le_mul_left (2 * g * (D * a)) le
--×   have e1 : 2 * (g * g) * (D * a) = 2 * g * (D * a) * g := by
--×     simp only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
--×   have e2 : g * ((2 * (a * D)) * (a * a + ρ * (D * D))) = 2 * g * (D * a) * (a * a + ρ * (D * D)) := by
--×     simp only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
--×   rw [e1, e2]; exact this

-- Episode13.lean, line 9324
--× def the_whole_part_at (k : Nat) : Nat := (the_crank_distance k).1
--× def the_part_by_the_root_at (k : Nat) : Nat := (the_crank_distance k).2
--× def the_gap (k : Nat) : Nat := the_whole_part_at k * the_whole_part_at k - 90 * (the_part_by_the_root_at k * the_part_by_the_root_at k)

-- Episode13.lean, line 9328
--× theorem the_crank_distance_stays_above (k : Nat) : 0 < the_whole_part_at k ∧ 0 < the_part_by_the_root_at k ∧ 90 * (the_part_by_the_root_at k * the_part_by_the_root_at k) ≤ the_whole_part_at k * the_whole_part_at k := by
--×   induction k with
--×   | zero => exact ⟨by decide, by decide, by decide⟩
--×   | succ k ih =>
--×     obtain ⟨ha, hd, h⟩ := ih
--×     refine ⟨?_, ?_, ?_⟩
--×     · show 0 < the_whole_part_at k * the_whole_part_at k + 90 * (the_part_by_the_root_at k * the_part_by_the_root_at k); have := Nat.mul_pos ha ha; omega
--×     · show 0 < 2 * (the_whole_part_at k * the_part_by_the_root_at k); have := Nat.mul_pos ha hd; omega
--×     · exact a_turn_stays_above 90 (the_whole_part_at k) (the_part_by_the_root_at k)

-- Episode13.lean, line 9338
--× theorem the_gap_of_the_next (k : Nat) : the_gap (k + 1) = the_gap k * the_gap k := by
--×   have h : the_whole_part_at k * the_whole_part_at k = 90 * (the_part_by_the_root_at k * the_part_by_the_root_at k) + the_gap k := by
--×     have := (the_crank_distance_stays_above k).2.2; unfold the_gap; omega
--×   have sq := the_gap_squares 90 (the_whole_part_at k) (the_part_by_the_root_at k) (the_gap k) h
--×   show (the_whole_part_at k * the_whole_part_at k + 90 * (the_part_by_the_root_at k * the_part_by_the_root_at k)) * (the_whole_part_at k * the_whole_part_at k + 90 * (the_part_by_the_root_at k * the_part_by_the_root_at k)) - 90 * ((2 * (the_whole_part_at k * the_part_by_the_root_at k)) * (2 * (the_whole_part_at k * the_part_by_the_root_at k))) = _
--×   omega

-- Episode13.lean, line 9345
--× theorem the_gap_of_the_next_halves (k : Nat) :
--×     2 * the_gap (k + 1) * (the_part_by_the_root_at k * the_whole_part_at k) ≤ the_gap k * (the_part_by_the_root_at (k + 1) * the_whole_part_at (k + 1)) := by
--×   have h : the_whole_part_at k * the_whole_part_at k = 90 * (the_part_by_the_root_at k * the_part_by_the_root_at k) + the_gap k := by
--×     have := (the_crank_distance_stays_above k).2.2; unfold the_gap; omega
--×   rw [the_gap_of_the_next]
--×   exact the_gap_halves 90 (the_whole_part_at k) (the_part_by_the_root_at k) (the_gap k) h

-- Episode13.lean, line 9352
--× theorem a_telescope_step (g g' g0 Yk Yk1 P X0 : Nat) (half : 2 * g' * Yk ≤ g * Yk1) (ih : g * P * X0 ≤ g0 * Yk)
--×     (pos : 0 < Yk) : g' * (P * 2) * X0 ≤ g0 * Yk1 := by
--×   apply Nat.le_of_mul_le_mul_right _ pos
--×   calc g' * (P * 2) * X0 * Yk = (2 * g' * Yk) * (P * X0) := by simp only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
--×     _ ≤ (g * Yk1) * (P * X0) := Nat.mul_le_mul_right _ half
--×     _ = (g * P * X0) * Yk1 := by simp only [Nat.mul_comm, Nat.mul_left_comm]
--×     _ ≤ (g0 * Yk) * Yk1 := Nat.mul_le_mul_right _ ih
--×     _ = g0 * Yk1 * Yk := by simp only [Nat.mul_comm, Nat.mul_left_comm]

-- Episode13.lean, line 9361
--× theorem the_gap_falls_by_halves (k : Nat) :
--×     the_gap k * 2 ^ k * (the_part_by_the_root_at 0 * the_whole_part_at 0) ≤ the_gap 0 * (the_part_by_the_root_at k * the_whole_part_at k) := by
--×   induction k with
--×   | zero => simp
--×   | succ k ih =>
--×     rw [Nat.pow_succ]
--×     obtain ⟨ha, hd, _⟩ := the_crank_distance_stays_above k
--×     exact a_telescope_step _ _ _ _ _ _ _ (the_gap_of_the_next_halves k) ih (Nat.mul_pos hd ha)

-- Episode13.lean, line 9370
--× theorem the_first_gap_is_under_sixteen : the_gap 0 ≤ 16 * (the_part_by_the_root_at 0 * the_whole_part_at 0) := by decide

-- Episode13.lean, line 9372
--× theorem the_gap_narrows (n : Nat) : the_gap (n + 4) * (n + 1) ≤ the_part_by_the_root_at (n + 4) * the_whole_part_at (n + 4) := by
--×   have tel := the_gap_falls_by_halves (n + 4)
--×   have first := the_first_gap_is_under_sixteen
--×   have two := (Nat.lt_two_pow_self : n < 2 ^ n)
--×   have pos : 0 < 16 * (the_part_by_the_root_at 0 * the_whole_part_at 0) := by decide
--×   apply Nat.le_of_mul_le_mul_right _ pos
--×   rw [Nat.pow_add, show (2 : Nat) ^ 4 = 16 by rfl] at tel
--×   calc the_gap (n + 4) * (n + 1) * (16 * (the_part_by_the_root_at 0 * the_whole_part_at 0))
--×         ≤ the_gap (n + 4) * 2 ^ n * (16 * (the_part_by_the_root_at 0 * the_whole_part_at 0)) :=
--×           Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ two)
--×     _ = the_gap (n + 4) * (2 ^ n * 16) * (the_part_by_the_root_at 0 * the_whole_part_at 0) := by simp only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
--×     _ ≤ the_gap 0 * (the_part_by_the_root_at (n + 4) * the_whole_part_at (n + 4)) := tel
--×     _ ≤ 16 * (the_part_by_the_root_at 0 * the_whole_part_at 0) * (the_part_by_the_root_at (n + 4) * the_whole_part_at (n + 4)) := Nat.mul_le_mul_right _ first
--×     _ = the_part_by_the_root_at (n + 4) * the_whole_part_at (n + 4) * (16 * (the_part_by_the_root_at 0 * the_whole_part_at 0)) := Nat.mul_comm _ _

-- Episode13.lean, line 9387
--× theorem the_low_wall_rises_by_the_crank (ρ a D : Nat) (above : ρ * (D * D) ≤ a * a) :
--×     ρ * D * (a * a + ρ * (D * D)) ≤ ρ * (2 * (a * D)) * a := by
--×   have := Nat.mul_le_mul_left (ρ * D) above
--×   simp only [Nat.two_mul, Nat.mul_add, Nat.add_mul] at this ⊢
--×   simp only [Nat.mul_comm, Nat.mul_left_comm] at this ⊢
--×   omega

-- Episode13.lean, line 9394
--× theorem the_high_wall_falls_by_the_crank (ρ a D : Nat) (above : ρ * (D * D) ≤ a * a) :
--×     (a * a + ρ * (D * D)) * D ≤ a * (2 * (a * D)) := by
--×   have := Nat.mul_le_mul_right D above
--×   simp only [Nat.two_mul, Nat.mul_add, Nat.add_mul] at this ⊢
--×   simp only [Nat.mul_comm, Nat.mul_left_comm] at this ⊢
--×   omega

-- Episode13.lean, line 9402
--× def the_root_by_the_crank : Meanings.Bracketed where
--×   low n := ⟨90 * the_part_by_the_root_at (n + 4), the_whole_part_at (n + 4), (the_crank_distance_stays_above _).1⟩
--×   high n := ⟨the_whole_part_at (n + 4), the_part_by_the_root_at (n + 4), (the_crank_distance_stays_above _).2.1⟩
--×   ordered n := by
--×     show 90 * the_part_by_the_root_at (n + 4) * the_part_by_the_root_at (n + 4) ≤ the_whole_part_at (n + 4) * the_whole_part_at (n + 4)
--×     rw [Nat.mul_assoc]; exact (the_crank_distance_stays_above _).2.2
--×   low_rises n := by
--×     show 90 * the_part_by_the_root_at (n + 4) * the_whole_part_at (n + 1 + 4) ≤ 90 * the_part_by_the_root_at (n + 1 + 4) * the_whole_part_at (n + 4)
--×     rw [show n + 1 + 4 = n + 4 + 1 by omega]
--×     exact the_low_wall_rises_by_the_crank 90 (the_whole_part_at (n + 4)) (the_part_by_the_root_at (n + 4)) (the_crank_distance_stays_above _).2.2
--×   high_falls n := by
--×     show the_whole_part_at (n + 1 + 4) * the_part_by_the_root_at (n + 4) ≤ the_whole_part_at (n + 4) * the_part_by_the_root_at (n + 1 + 4)
--×     rw [show n + 1 + 4 = n + 4 + 1 by omega]
--×     exact the_high_wall_falls_by_the_crank 90 (the_whole_part_at (n + 4)) (the_part_by_the_root_at (n + 4)) (the_crank_distance_stays_above _).2.2
--×   narrows n := by
--×     show the_whole_part_at (n + 4) * the_whole_part_at (n + 4) * (n + 1) ≤ 90 * the_part_by_the_root_at (n + 4) * the_part_by_the_root_at (n + 4) * (n + 1) + the_part_by_the_root_at (n + 4) * the_whole_part_at (n + 4)
--×     have h : the_whole_part_at (n + 4) * the_whole_part_at (n + 4) = 90 * (the_part_by_the_root_at (n + 4) * the_part_by_the_root_at (n + 4)) + the_gap (n + 4) := by
--×       have := (the_crank_distance_stays_above (n + 4)).2.2; unfold the_gap; omega
--×     have g := the_gap_narrows n
--×     rw [h, Nat.add_mul, Nat.mul_assoc 90 (the_part_by_the_root_at (n + 4))]
--×     omega

-- Episode13.lean, line 9424
--× theorem the_crank_and_the_halving_are_one_root :
--×     the_root_by_the_crank.Same Meanings.theRootOfNinety.bracketed := by
--×   intro n m
--×   have above_n := (the_crank_distance_stays_above (n + 4)).2.2
--×   have above_m := (the_crank_distance_stays_above (m + 4)).2.2
--×   have four : ∀ j : Nat, 4 ^ j = 2 ^ j * 2 ^ j := fun j => by rw [← Nat.mul_pow]
--×   have holds_m := Meanings.theRootOfNinety_holds_the_root m
--×   have holds_n := Meanings.theRootOfNinety_holds_the_root n
--×   rw [four] at holds_m holds_n
--×   constructor
--×   · show 90 * the_part_by_the_root_at (n + 4) * 2 ^ m ≤ (Meanings.theRootOfNinety.cut m + 1) * the_whole_part_at (n + 4)
--×     apply Nat.mul_self_le_mul_self_iff.1
--×     have big := Nat.mul_le_mul above_n (Nat.le_of_lt holds_m.2)
--×     calc 90 * the_part_by_the_root_at (n + 4) * 2 ^ m * (90 * the_part_by_the_root_at (n + 4) * 2 ^ m)
--×           = 90 * (the_part_by_the_root_at (n + 4) * the_part_by_the_root_at (n + 4)) * (90 * (2 ^ m * 2 ^ m)) := by
--×             simp only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
--×       _ ≤ the_whole_part_at (n + 4) * the_whole_part_at (n + 4) * ((Meanings.theRootOfNinety.cut m + 1) * (Meanings.theRootOfNinety.cut m + 1)) := big
--×       _ = (Meanings.theRootOfNinety.cut m + 1) * the_whole_part_at (n + 4) * ((Meanings.theRootOfNinety.cut m + 1) * the_whole_part_at (n + 4)) := by
--×             simp only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
--×   · show Meanings.theRootOfNinety.cut n * the_part_by_the_root_at (m + 4) ≤ the_whole_part_at (m + 4) * 2 ^ n
--×     apply Nat.mul_self_le_mul_self_iff.1
--×     have big := Nat.mul_le_mul holds_n.1 (Nat.le_refl (the_part_by_the_root_at (m + 4) * the_part_by_the_root_at (m + 4)))
--×     have big2 := Nat.mul_le_mul_left (2 ^ n * 2 ^ n) above_m
--×     calc Meanings.theRootOfNinety.cut n * the_part_by_the_root_at (m + 4) * (Meanings.theRootOfNinety.cut n * the_part_by_the_root_at (m + 4))
--×           = Meanings.theRootOfNinety.cut n * Meanings.theRootOfNinety.cut n * (the_part_by_the_root_at (m + 4) * the_part_by_the_root_at (m + 4)) := by
--×             simp only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
--×       _ ≤ 90 * (2 ^ n * 2 ^ n) * (the_part_by_the_root_at (m + 4) * the_part_by_the_root_at (m + 4)) := big
--×       _ = 2 ^ n * 2 ^ n * (90 * (the_part_by_the_root_at (m + 4) * the_part_by_the_root_at (m + 4))) := by simp only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
--×       _ ≤ 2 ^ n * 2 ^ n * (the_whole_part_at (m + 4) * the_whole_part_at (m + 4)) := big2
--×       _ = the_whole_part_at (m + 4) * 2 ^ n * (the_whole_part_at (m + 4) * 2 ^ n) := by simp only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

-- Episode13.lean, line 9472
--× def the_printed_number_as_a_real : Meanings.Bracketed :=
--×   (Meanings.Bracketed.ofFraction ⟨324, 65, by decide⟩).mul ((Meanings.Bracketed.ofNat 18).add the_root_by_the_crank)

-- Episode13.lean, line 9476
--× theorem the_printed_number_narrows_at_every_stage (n : Nat) :
--×     (the_printed_number_as_a_real.high n).over * (the_printed_number_as_a_real.low n).under * (n + 1)
--×       ≤ (the_printed_number_as_a_real.low n).over * (the_printed_number_as_a_real.high n).under * (n + 1)
--×         + (the_printed_number_as_a_real.high n).under * (the_printed_number_as_a_real.low n).under :=
--×   the_printed_number_as_a_real.narrows n

-- Episode13.lean, line 9483
--× theorem the_cranks_low_wall_is_past_its_first (j : Nat) : (the_root_by_the_crank.low 0).le (the_root_by_the_crank.low j) := by
--×   have h := the_root_by_the_crank.low_rises_by 0 j
--×   rwa [Nat.zero_add] at h

-- Episode13.lean, line 9487
--× theorem the_cranks_high_wall_is_under_its_first (j : Nat) : (the_root_by_the_crank.high j).le (the_root_by_the_crank.high 0) := by
--×   have h := the_root_by_the_crank.high_falls_by 0 j
--×   rwa [Nat.zero_add] at h

-- Episode13.lean, line 9496
--× theorem at_the_cranks_first_stage_the_walls_are_in_the_jar :
--×     the_jars_low_wall.le ((⟨324, 65, by decide⟩ : Meanings.Fraction).mul ((⟨18, 1, Nat.one_pos⟩ : Meanings.Fraction).add (the_root_by_the_crank.low 0)))
--×       ∧ ((⟨324, 65, by decide⟩ : Meanings.Fraction).mul ((⟨18, 1, Nat.one_pos⟩ : Meanings.Fraction).add (the_root_by_the_crank.high 0))).le the_jars_high_wall := by
--×   decide +kernel

-- Episode13.lean, line 9502
--× theorem the_low_wall_is_never_under_the_jar (n : Nat) : the_jars_low_wall.le (the_printed_number_as_a_real.low n) :=
--×   Meanings.Fraction.le_trans at_the_cranks_first_stage_the_walls_are_in_the_jar.1
--×     (Meanings.Fraction.mul_le_mul (Meanings.Fraction.le_refl _)
--×       (Meanings.Fraction.add_le_add (Meanings.Fraction.le_refl _) (the_cranks_low_wall_is_past_its_first _)))

-- Episode13.lean, line 9508
--× theorem the_high_wall_is_never_over_the_jar (n : Nat) : (the_printed_number_as_a_real.high n).le the_jars_high_wall :=
--×   Meanings.Fraction.le_trans
--×     (Meanings.Fraction.mul_le_mul (Meanings.Fraction.le_refl _)
--×       (Meanings.Fraction.add_le_add (Meanings.Fraction.le_refl _) (the_cranks_high_wall_is_under_its_first _)))
--×     at_the_cranks_first_stage_the_walls_are_in_the_jar.2

-- Episode13.lean, line 9515
--× theorem the_printed_number_is_in_the_jar_and_narrows (n : Nat) :
--×     the_jars_low_wall.le (the_printed_number_as_a_real.low n)
--×       ∧ (the_printed_number_as_a_real.high n).le the_jars_high_wall
--×       ∧ (the_printed_number_as_a_real.high n).over * (the_printed_number_as_a_real.low n).under * (n + 1)
--×           ≤ (the_printed_number_as_a_real.low n).over * (the_printed_number_as_a_real.high n).under * (n + 1)
--×             + (the_printed_number_as_a_real.high n).under * (the_printed_number_as_a_real.low n).under :=
--×   ⟨the_low_wall_is_never_under_the_jar n, the_high_wall_is_never_over_the_jar n, the_printed_number_narrows_at_every_stage n⟩

-- Episode13.lean, line 9526
--× theorem eighteen_beside_the_root_is_the_norm :
--×     ((Meanings.Bracketed.ofNat 18).add Meanings.theRootOfNinety.bracketed).Same Meanings.theNorm.bracketed := by
--×   intro n m
--×   constructor
--×   · have hr := Meanings.theRootOfNinety.bracketed.low_under_high (2 * n + 1) m
--×     unfold Meanings.Fraction.le at hr ⊢
--×     show (18 * 2 ^ (2 * n + 1) + Meanings.theRootOfNinety.cut (2 * n + 1) * 1) * 2 ^ m
--×       ≤ (18 * 2 ^ m + Meanings.theRootOfNinety.cut m + 1) * (1 * 2 ^ (2 * n + 1))
--×     change Meanings.theRootOfNinety.cut (2 * n + 1) * 2 ^ m ≤ (Meanings.theRootOfNinety.cut m + 1) * 2 ^ (2 * n + 1) at hr
--×     generalize 2 ^ (2 * n + 1) = A at *
--×     generalize 2 ^ m = B at *
--×     simp only [Nat.add_mul, Nat.mul_one, Nat.one_mul] at hr ⊢
--×     simp only [Nat.mul_comm, Nat.mul_left_comm] at hr ⊢
--×     omega
--×   · have hr := Meanings.theRootOfNinety.bracketed.low_under_high n (2 * m + 1)
--×     unfold Meanings.Fraction.le at hr ⊢
--×     show (18 * 2 ^ n + Meanings.theRootOfNinety.cut n) * (1 * 2 ^ (2 * m + 1))
--×       ≤ (18 * 2 ^ (2 * m + 1) + (Meanings.theRootOfNinety.cut (2 * m + 1) + 1) * 1) * 2 ^ n
--×     change Meanings.theRootOfNinety.cut n * 2 ^ (2 * m + 1) ≤ (Meanings.theRootOfNinety.cut (2 * m + 1) + 1) * 2 ^ n at hr
--×     generalize 2 ^ (2 * m + 1) = A at *
--×     generalize 2 ^ n = B at *
--×     simp only [Nat.add_mul, Nat.mul_one, Nat.one_mul] at hr ⊢
--×     simp only [Nat.mul_comm, Nat.mul_left_comm] at hr ⊢
--×     omega

-- Episode13.lean, line 9551
--× theorem the_printed_number_is_one_with_the_halvings :
--×     the_printed_number_as_a_real.Same ((Meanings.Bracketed.ofFraction ⟨324, 65, by decide⟩).mul Meanings.theNorm.bracketed) :=
--×   Meanings.Bracketed.mul_same (Meanings.Bracketed.same_refl _)
--×     (Meanings.Bracketed.same_trans
--×       (Meanings.Bracketed.add_same (Meanings.Bracketed.same_refl _) the_crank_and_the_halving_are_one_root)
--×       eighteen_beside_the_root_is_the_norm)

-- Episode13.lean, line 9563
--× theorem the_cranks_low_wall_is_under_any_square_past_ninety (V : Meanings.Fraction)
--×     (hV : 90 * (V.under * V.under) ≤ V.over * V.over) (j : Nat) : (the_root_by_the_crank.low j).le V := by
--×   show 90 * the_part_by_the_root_at (j + 4) * V.under ≤ V.over * the_whole_part_at (j + 4)
--×   apply Nat.mul_self_le_mul_self_iff.1
--×   have s := (the_crank_distance_stays_above (j + 4)).2.2
--×   generalize the_part_by_the_root_at (j + 4) = D at *
--×   generalize the_whole_part_at (j + 4) = a at *
--×   have m1 := Nat.mul_le_mul_right (90 * (V.under * V.under)) s
--×   have m2 := Nat.mul_le_mul_left (a * a) hV
--×   calc 90 * D * V.under * (90 * D * V.under) = 90 * (D * D) * (90 * (V.under * V.under)) := by
--×         simp only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
--×     _ ≤ a * a * (90 * (V.under * V.under)) := m1
--×     _ ≤ a * a * (V.over * V.over) := m2
--×     _ = V.over * a * (V.over * a) := by ac_rfl

-- Episode13.lean, line 9578
--× theorem the_cranks_high_wall_is_past_any_square_under_ninety (W : Meanings.Fraction)
--×     (hW : W.over * W.over ≤ 90 * (W.under * W.under)) (j : Nat) : W.le (the_root_by_the_crank.high j) := by
--×   show W.over * the_part_by_the_root_at (j + 4) ≤ the_whole_part_at (j + 4) * W.under
--×   apply Nat.mul_self_le_mul_self_iff.1
--×   have s := (the_crank_distance_stays_above (j + 4)).2.2
--×   generalize the_part_by_the_root_at (j + 4) = D at *
--×   generalize the_whole_part_at (j + 4) = a at *
--×   have m1 := Nat.mul_le_mul_right (D * D) hW
--×   have m2 := Nat.mul_le_mul_left (W.under * W.under) s
--×   calc W.over * D * (W.over * D) = W.over * W.over * (D * D) := by ac_rfl
--×     _ ≤ 90 * (W.under * W.under) * (D * D) := m1
--×     _ = W.under * W.under * (90 * (D * D)) := by simp only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
--×     _ ≤ W.under * W.under * (a * a) := m2
--×     _ = a * W.under * (a * W.under) := by ac_rfl

-- Episode13.lean, line 9594
--× def the_printed_digits : Meanings.Fraction := ⟨137011290548979457087737300, 10 ^ 24, by decide⟩
--× def the_printed_digits_and_one : Meanings.Fraction :=
--×   ⟨137011290548979457087737301, 10 ^ 24, by decide⟩

-- Episode13.lean, line 9599
--× def the_root_the_digits_and_one_ask : Meanings.Fraction :=
--×   ⟨65 * 137011290548979457087737301 - 18 * 324 * 10 ^ 24, 324 * 10 ^ 24, by decide⟩
--× def the_root_the_digits_ask : Meanings.Fraction :=
--×   ⟨65 * 137011290548979457087737300 - 18 * 324 * 10 ^ 24, 324 * 10 ^ 24, by decide⟩

-- Episode13.lean, line 9604
--× theorem the_digits_ask_a_root_past_and_under_ninety :
--×     90 * (the_root_the_digits_and_one_ask.under * the_root_the_digits_and_one_ask.under)
--×         ≤ the_root_the_digits_and_one_ask.over * the_root_the_digits_and_one_ask.over
--×       ∧ the_root_the_digits_ask.over * the_root_the_digits_ask.over
--×         ≤ 90 * (the_root_the_digits_ask.under * the_root_the_digits_ask.under) := by
--×   decide

-- Episode13.lean, line 9611
--× theorem the_fraction_by_eighteen_and_what_the_digits_ask_is_the_digits :
--×     ((⟨324, 65, by decide⟩ : Meanings.Fraction).mul
--×         ((⟨18, 1, Nat.one_pos⟩ : Meanings.Fraction).add the_root_the_digits_and_one_ask)).le the_printed_digits_and_one
--×       ∧ the_printed_digits.le ((⟨324, 65, by decide⟩ : Meanings.Fraction).mul
--×         ((⟨18, 1, Nat.one_pos⟩ : Meanings.Fraction).add the_root_the_digits_ask)) := by
--×   decide

-- Episode13.lean, line 9619
--× theorem the_printed_digits_are_the_reals_floor (n : Nat) :
--×     the_printed_digits.le (the_printed_number_as_a_real.high n)
--×       ∧ (the_printed_number_as_a_real.low n).le the_printed_digits_and_one :=
--×   ⟨Meanings.Fraction.le_trans the_fraction_by_eighteen_and_what_the_digits_ask_is_the_digits.2
--×     (Meanings.Fraction.mul_le_mul (Meanings.Fraction.le_refl _)
--×       (Meanings.Fraction.add_le_add (Meanings.Fraction.le_refl _)
--×         (the_cranks_high_wall_is_past_any_square_under_ninety _ the_digits_ask_a_root_past_and_under_ninety.2 _))),
--×    Meanings.Fraction.le_trans
--×     (Meanings.Fraction.mul_le_mul (Meanings.Fraction.le_refl _)
--×       (Meanings.Fraction.add_le_add (Meanings.Fraction.le_refl _)
--×         (the_cranks_low_wall_is_under_any_square_past_ninety _ the_digits_ask_a_root_past_and_under_ninety.1 _)))
--×     the_fraction_by_eighteen_and_what_the_digits_ask_is_the_digits.1⟩

-- Episode13.lean, line 9646
--× theorem the_norm_is_past_nothing_at_the_tenth_stage : 0 < (Meanings.theNorm.bracketed.low 10).over := by decide

-- Episode13.lean, line 9648
--× def the_lower_root_as_a_real : Meanings.Bracketed :=
--×   (Meanings.Bracketed.ofNat 234).mul (Meanings.theNorm.bracketed.reciprocal 10 the_norm_is_past_nothing_at_the_tenth_stage)

-- Episode13.lean, line 9652
--× theorem the_two_roots_multiply_to_the_determinant :
--×     (Meanings.theNorm.bracketed.mul the_lower_root_as_a_real).Same (Meanings.Bracketed.ofNat 234) :=
--×   Meanings.Bracketed.same_trans (Meanings.Bracketed.same_symm (Meanings.Bracketed.mul_assoc _ _ _))
--×     (Meanings.Bracketed.same_trans
--×       (Meanings.Bracketed.mul_same (Meanings.Bracketed.mul_comm _ _) (Meanings.Bracketed.same_refl _))
--×       (Meanings.Bracketed.same_trans (Meanings.Bracketed.mul_assoc _ _ _)
--×         (Meanings.Bracketed.same_trans
--×           (Meanings.Bracketed.mul_same (Meanings.Bracketed.same_refl _) (Meanings.Bracketed.mul_reciprocal _ _ _))
--×           (Meanings.Bracketed.mul_one _))))

-- Episode13.lean, line 9663
--× def the_other_printed_root_as_a_real : Meanings.Bracketed :=
--×   (Meanings.Bracketed.ofFraction ⟨324, 65, by decide⟩).mul the_lower_root_as_a_real

-- Episode13.lean, line 9670
--× theorem at_the_tenth_stage_the_other_walls_are_in_the_jar :
--×     the_other_jars_low_wall.le ((⟨324, 65, by decide⟩ : Meanings.Fraction).mul ((⟨234, 1, Nat.one_pos⟩ : Meanings.Fraction).mul
--×         ((Meanings.theNorm.bracketed.high 10).recip
--×           (Meanings.theNorm.bracketed.high_pos 10 the_norm_is_past_nothing_at_the_tenth_stage (Nat.le_refl 10)))))
--×       ∧ ((⟨324, 65, by decide⟩ : Meanings.Fraction).mul ((⟨234, 1, Nat.one_pos⟩ : Meanings.Fraction).mul
--×           ((Meanings.theNorm.bracketed.low 10).recip the_norm_is_past_nothing_at_the_tenth_stage))).le
--×           the_other_jars_high_wall := by
--×   decide +kernel

-- Episode13.lean, line 9679
--× theorem the_other_low_wall_is_never_under_its_jar (n : Nat) :
--×     the_other_jars_low_wall.le (the_other_printed_root_as_a_real.low n) :=
--×   Meanings.Fraction.le_trans at_the_tenth_stage_the_other_walls_are_in_the_jar.1
--×     (Meanings.Fraction.mul_le_mul (Meanings.Fraction.le_refl _)
--×       (Meanings.Fraction.mul_le_mul (Meanings.Fraction.le_refl _) (Meanings.Bracketed.reciprocal_low_is_past _ _ _ _)))

-- Episode13.lean, line 9685
--× theorem the_other_high_wall_is_never_over_its_jar (n : Nat) :
--×     (the_other_printed_root_as_a_real.high n).le the_other_jars_high_wall :=
--×   Meanings.Fraction.le_trans
--×     (Meanings.Fraction.mul_le_mul (Meanings.Fraction.le_refl _)
--×       (Meanings.Fraction.mul_le_mul (Meanings.Fraction.le_refl _) (Meanings.Bracketed.reciprocal_high_is_under _ _ _ _)))
--×     at_the_tenth_stage_the_other_walls_are_in_the_jar.2

-- Episode13.lean, line 9697
--× theorem the_root_is_not_past_eighteen :
--×     (Meanings.theRootOfNinety.bracketed.high 0).le ((Meanings.Bracketed.ofNat 18).low 0) := by decide

-- Episode13.lean, line 9700
--× def eighteen_less_the_root : Meanings.Bracketed :=
--×   (Meanings.Bracketed.ofNat 18).difference Meanings.theRootOfNinety.bracketed 0 the_root_is_not_past_eighteen

-- Episode13.lean, line 9703
--× local infix:50 " ≐ " => Meanings.Bracketed.Same

-- Episode13.lean, line 9705
--× theorem eighteen_less_the_root_by_eighteen_and_the_root_is_the_determinant :
--×     eighteen_less_the_root.mul ((Meanings.Bracketed.ofNat 18).add Meanings.theRootOfNinety.bracketed)
--×       ≐ Meanings.Bracketed.ofNat 234 := by
--×   have rM : Meanings.theRootOfNinety.bracketed.mul ((Meanings.Bracketed.ofNat 18).add Meanings.theRootOfNinety.bracketed)
--×       ≐ ((Meanings.Bracketed.ofNat 18).mul Meanings.theRootOfNinety.bracketed).add (Meanings.Bracketed.ofNat 90) :=
--×     Meanings.Bracketed.same_trans (Meanings.Bracketed.mul_add _ _ _)
--×       (Meanings.Bracketed.add_same (Meanings.Bracketed.mul_comm _ _) Meanings.the_root_by_itself_is_ninety)
--×   have eM : (Meanings.Bracketed.ofNat 18).mul ((Meanings.Bracketed.ofNat 18).add Meanings.theRootOfNinety.bracketed)
--×       ≐ (Meanings.Bracketed.ofNat 234).add
--×           (((Meanings.Bracketed.ofNat 18).mul Meanings.theRootOfNinety.bracketed).add (Meanings.Bracketed.ofNat 90)) :=
--×     calc (Meanings.Bracketed.ofNat 18).mul ((Meanings.Bracketed.ofNat 18).add Meanings.theRootOfNinety.bracketed)
--×         ≐ ((Meanings.Bracketed.ofNat 18).mul (Meanings.Bracketed.ofNat 18)).add
--×             ((Meanings.Bracketed.ofNat 18).mul Meanings.theRootOfNinety.bracketed) := Meanings.Bracketed.mul_add _ _ _
--×       _ ≐ (Meanings.Bracketed.ofNat 324).add ((Meanings.Bracketed.ofNat 18).mul Meanings.theRootOfNinety.bracketed) :=
--×           Meanings.Bracketed.add_same (Meanings.Bracketed.ofNat_mul 18 18) (Meanings.Bracketed.same_refl _)
--×       _ ≐ ((Meanings.Bracketed.ofNat 234).add (Meanings.Bracketed.ofNat 90)).add
--×             ((Meanings.Bracketed.ofNat 18).mul Meanings.theRootOfNinety.bracketed) :=
--×           Meanings.Bracketed.add_same (Meanings.Bracketed.same_symm (Meanings.Bracketed.ofNat_add 234 90))
--×             (Meanings.Bracketed.same_refl _)
--×       _ ≐ (Meanings.Bracketed.ofNat 234).add
--×             ((Meanings.Bracketed.ofNat 90).add ((Meanings.Bracketed.ofNat 18).mul Meanings.theRootOfNinety.bracketed)) :=
--×           Meanings.Bracketed.add_assoc _ _ _
--×       _ ≐ (Meanings.Bracketed.ofNat 234).add
--×             (((Meanings.Bracketed.ofNat 18).mul Meanings.theRootOfNinety.bracketed).add (Meanings.Bracketed.ofNat 90)) :=
--×           Meanings.Bracketed.add_same (Meanings.Bracketed.same_refl _) (Meanings.Bracketed.add_comm _ _)
--×   apply Meanings.Bracketed.add_cancel
--×     (c := ((Meanings.Bracketed.ofNat 18).mul Meanings.theRootOfNinety.bracketed).add (Meanings.Bracketed.ofNat 90))
--×   calc (eighteen_less_the_root.mul ((Meanings.Bracketed.ofNat 18).add Meanings.theRootOfNinety.bracketed)).add
--×           (((Meanings.Bracketed.ofNat 18).mul Meanings.theRootOfNinety.bracketed).add (Meanings.Bracketed.ofNat 90))
--×       ≐ (eighteen_less_the_root.mul ((Meanings.Bracketed.ofNat 18).add Meanings.theRootOfNinety.bracketed)).add
--×           (Meanings.theRootOfNinety.bracketed.mul ((Meanings.Bracketed.ofNat 18).add Meanings.theRootOfNinety.bracketed)) :=
--×         Meanings.Bracketed.add_same (Meanings.Bracketed.same_refl _) (Meanings.Bracketed.same_symm rM)
--×     _ ≐ (eighteen_less_the_root.add Meanings.theRootOfNinety.bracketed).mul
--×           ((Meanings.Bracketed.ofNat 18).add Meanings.theRootOfNinety.bracketed) :=
--×         Meanings.Bracketed.same_symm (Meanings.Bracketed.add_mul _ _ _)
--×     _ ≐ (Meanings.Bracketed.ofNat 18).mul ((Meanings.Bracketed.ofNat 18).add Meanings.theRootOfNinety.bracketed) :=
--×         Meanings.Bracketed.mul_same (Meanings.Bracketed.difference_add _ _ _ _) (Meanings.Bracketed.same_refl _)
--×     _ ≐ _ := eM

-- Episode13.lean, line 9745
--× theorem eighteen_less_the_root_is_the_lower_root : eighteen_less_the_root ≐ the_lower_root_as_a_real :=
--×   calc eighteen_less_the_root
--×       ≐ eighteen_less_the_root.mul (Meanings.Bracketed.ofNat 1) := Meanings.Bracketed.same_symm (Meanings.Bracketed.mul_one _)
--×     _ ≐ eighteen_less_the_root.mul (Meanings.theNorm.bracketed.mul
--×           (Meanings.theNorm.bracketed.reciprocal 10 the_norm_is_past_nothing_at_the_tenth_stage)) :=
--×         Meanings.Bracketed.mul_same (Meanings.Bracketed.same_refl _)
--×           (Meanings.Bracketed.same_symm (Meanings.Bracketed.mul_reciprocal _ _ _))
--×     _ ≐ (eighteen_less_the_root.mul Meanings.theNorm.bracketed).mul
--×           (Meanings.theNorm.bracketed.reciprocal 10 the_norm_is_past_nothing_at_the_tenth_stage) :=
--×         Meanings.Bracketed.same_symm (Meanings.Bracketed.mul_assoc _ _ _)
--×     _ ≐ (eighteen_less_the_root.mul ((Meanings.Bracketed.ofNat 18).add Meanings.theRootOfNinety.bracketed)).mul
--×           (Meanings.theNorm.bracketed.reciprocal 10 the_norm_is_past_nothing_at_the_tenth_stage) :=
--×         Meanings.Bracketed.mul_same
--×           (Meanings.Bracketed.mul_same (Meanings.Bracketed.same_refl _)
--×             (Meanings.Bracketed.same_symm eighteen_beside_the_root_is_the_norm))
--×           (Meanings.Bracketed.same_refl _)
--×     _ ≐ the_lower_root_as_a_real :=
--×         Meanings.Bracketed.mul_same eighteen_less_the_root_by_eighteen_and_the_root_is_the_determinant
--×           (Meanings.Bracketed.same_refl _)

-- Episode13.lean, line 9766
--× theorem the_lower_root_owed_and_over_are_one :
--×     Meanings.theLowerRoot.Same (Meanings.SignedReal.ofReal the_lower_root_as_a_real) :=
--×   Meanings.SignedReal.same_trans (Meanings.theLowerRoot.is_its_difference_held 0 the_root_is_not_past_eighteen)
--×     (Meanings.SignedReal.ofReal_same eighteen_less_the_root_is_the_lower_root)

-- Episode13.lean, line 9782
--× theorem the_turned_roots_norm_squared_is_the_determinant :
--×     Meanings.theTurnedRoot.normSquared.Same (Meanings.SignedReal.ofNat 414) := by
--×   show (Meanings.SignedReal.ofReal (Meanings.Bracketed.ofNat 18) * Meanings.SignedReal.ofReal (Meanings.Bracketed.ofNat 18)
--×       + Meanings.SignedReal.ofReal Meanings.theRootOfNinety.bracketed
--×         * Meanings.SignedReal.ofReal Meanings.theRootOfNinety.bracketed).Same
--×     (Meanings.SignedReal.ofReal (Meanings.Bracketed.ofNat 414))
--×   exact Meanings.SignedReal.same_trans
--×     (Meanings.SignedReal.add_same (Meanings.SignedReal.ofReal_mul _ _) (Meanings.SignedReal.ofReal_mul _ _))
--×     (Meanings.SignedReal.same_trans
--×       (Meanings.SignedReal.add_same (Meanings.SignedReal.ofReal_same (Meanings.Bracketed.ofNat_mul 18 18))
--×         (Meanings.SignedReal.ofReal_same Meanings.the_root_by_itself_is_ninety))
--×       (Meanings.SignedReal.same_trans (Meanings.SignedReal.ofReal_add _ _)
--×         (Meanings.SignedReal.ofReal_same (Meanings.Bracketed.ofNat_add 324 90))))

-- Episode13.lean, line 9797
--× theorem the_turned_roots_multiply_to_the_determinant :
--×     (Meanings.theTurnedRoot * Meanings.theOtherTurnedRoot).Same (Meanings.ComplexReal.ofNat 414) :=
--×   Meanings.ComplexReal.same_trans (Meanings.ComplexReal.mul_conjugate _)
--×     (Meanings.ComplexReal.ofSigned_same the_turned_roots_norm_squared_is_the_determinant)

-- Episode13.lean, line 9802
--× theorem the_turned_roots_norm_squared_is_past_nothing :
--×     (Meanings.theTurnedRoot.normSquared.owed.high 0).lt (Meanings.theTurnedRoot.normSquared.held.low 0) := by
--×   decide +kernel

-- Episode13.lean, line 9806
--× def one_over_the_turned_root : Meanings.ComplexReal :=
--×   Meanings.theTurnedRoot.reciprocal 0 the_turned_roots_norm_squared_is_past_nothing

-- Episode13.lean, line 9809
--× theorem four_hundred_and_fourteen_over_itself :
--×     ((Meanings.Bracketed.ofNat 414).mul (Meanings.Bracketed.ofFraction ⟨1, 414, by decide⟩)).Same (Meanings.Bracketed.ofNat 1) :=
--×   fun _ _ => ⟨Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl⟩

-- Episode13.lean, line 9814
--× theorem one_over_the_turned_root_is_the_other_over_the_determinant :
--×     one_over_the_turned_root.Same (Meanings.theOtherTurnedRoot
--×       * Meanings.ComplexReal.ofSigned (Meanings.SignedReal.ofReal (Meanings.Bracketed.ofFraction ⟨1, 414, by decide⟩))) :=
--×   Meanings.ComplexReal.reciprocal_unique (Meanings.ComplexReal.mul_reciprocal _ _ _)
--×     (Meanings.ComplexReal.same_trans (Meanings.ComplexReal.same_symm (Meanings.ComplexReal.mul_assoc _ _ _))
--×       (Meanings.ComplexReal.same_trans
--×         (Meanings.ComplexReal.mul_same the_turned_roots_multiply_to_the_determinant (Meanings.ComplexReal.same_refl _))
--×         (Meanings.ComplexReal.same_trans (Meanings.ComplexReal.ofSigned_mul (Meanings.SignedReal.ofNat 414) _)
--×           (Meanings.ComplexReal.ofSigned_same (Meanings.SignedReal.same_trans (Meanings.SignedReal.ofReal_mul _ _)
--×             (Meanings.SignedReal.ofReal_same four_hundred_and_fourteen_over_itself))))))

-- Episode13.lean, line 9834
--× theorem i_is_past_nothing : (Meanings.QuaternionReal.i.normSquared.owed.high 0).lt (Meanings.QuaternionReal.i.normSquared.held.low 0) := by
--×   decide +kernel
--× theorem j_is_past_nothing : (Meanings.QuaternionReal.j.normSquared.owed.high 0).lt (Meanings.QuaternionReal.j.normSquared.held.low 0) := by
--×   decide +kernel
--× theorem k_is_past_nothing : (Meanings.QuaternionReal.k.normSquared.owed.high 0).lt (Meanings.QuaternionReal.k.normSquared.held.low 0) := by
--×   decide +kernel

-- Episode13.lean, line 9841
--× theorem one_over_i_is_i_owed : (-Meanings.QuaternionReal.i).Same (Meanings.QuaternionReal.i.reciprocal 0 i_is_past_nothing) := by
--×   have h := Meanings.QuaternionReal.neg_same Meanings.i_twice_is_one_owed
--×   rw [Meanings.QuaternionReal.neg_neg] at h
--×   exact Meanings.QuaternionReal.reciprocal_unique _ _ _
--×     (Meanings.QuaternionReal.same_trans (Meanings.QuaternionReal.mul_neg Meanings.QuaternionReal.i Meanings.QuaternionReal.i) h)

-- Episode13.lean, line 9847
--× theorem one_over_j_is_j_owed : (-Meanings.QuaternionReal.j).Same (Meanings.QuaternionReal.j.reciprocal 0 j_is_past_nothing) := by
--×   have h := Meanings.QuaternionReal.neg_same Meanings.j_twice_is_one_owed
--×   rw [Meanings.QuaternionReal.neg_neg] at h
--×   exact Meanings.QuaternionReal.reciprocal_unique _ _ _
--×     (Meanings.QuaternionReal.same_trans (Meanings.QuaternionReal.mul_neg Meanings.QuaternionReal.j Meanings.QuaternionReal.j) h)

-- Episode13.lean, line 9853
--× theorem one_over_k_is_k_owed : (-Meanings.QuaternionReal.k).Same (Meanings.QuaternionReal.k.reciprocal 0 k_is_past_nothing) := by
--×   have h := Meanings.QuaternionReal.neg_same Meanings.k_twice_is_one_owed
--×   rw [Meanings.QuaternionReal.neg_neg] at h
--×   exact Meanings.QuaternionReal.reciprocal_unique _ _ _
--×     (Meanings.QuaternionReal.same_trans (Meanings.QuaternionReal.mul_neg Meanings.QuaternionReal.k Meanings.QuaternionReal.k) h)

-- Episode13.lean, line 9872
--× def the_step_angle (n : Nat) (hn : 0 < n) : Meanings.Bracketed := Meanings.arctan 1 n hn (by omega)

-- Episode13.lean, line 9875
--× theorem the_step_angle_is_between (n : Nat) (hn : 0 < n) (k : Nat) :
--×     ((Meanings.arctanTerm 1 n hn 0).sub (Meanings.arctanTerm 1 n hn 1)).le ((the_step_angle n hn).low k)
--×       ∧ ((the_step_angle n hn).high k).le (Meanings.arctanTerm 1 n hn 0) :=
--×   ⟨(the_step_angle n hn).low_le_of_le (Nat.zero_le k),
--×    Meanings.Fraction.le_trans ((the_step_angle n hn).high_le_of_le (Nat.zero_le k))
--×      (Meanings.Fraction.sub_then_add_is_not_past _ _ _ (Meanings.arctanTerm_falls 1 n hn (by omega) 1)
--×        (Meanings.arctanTerm_falls 1 n hn (by omega) 0))⟩

-- Episode13.lean, line 9884
--× theorem the_step_and_a_third_of_its_cube (n : Nat) (hn : 0 < n) :
--×     (Meanings.arctanTerm 1 n hn 0).over = 1 ∧ (Meanings.arctanTerm 1 n hn 0).under = n
--×       ∧ (Meanings.arctanTerm 1 n hn 1).over = 1 ∧ (Meanings.arctanTerm 1 n hn 1).under = 3 * (n * n * n) := by
--×   refine ⟨Nat.one_pow _, ?_, Nat.one_pow _, ?_⟩
--×   · show n ^ 1 * 1 = n; simp
--×   · show n ^ 3 * 3 = 3 * (n * n * n); rw [Nat.mul_comm]; simp [Nat.pow_succ]

-- Episode13.lean, line 9893
--× theorem the_step_angle_of_five_is_between (k : Nat) :
--×     ((the_step_angle 5 (by decide)).high k).le ⟨19740, 100000, by decide⟩
--×       ∧ (1 ≤ k → (⟨19739, 100000, by decide⟩ : Meanings.Fraction).le ((the_step_angle 5 (by decide)).low k)) := by
--×   have at0 : ((the_step_angle 5 (by decide)).high 0).le ⟨19740, 100000, by decide⟩ := by decide +kernel
--×   have at1 : (⟨19739, 100000, by decide⟩ : Meanings.Fraction).le ((the_step_angle 5 (by decide)).low 1) := by
--×     decide +kernel
--×   exact ⟨Meanings.Fraction.le_trans ((the_step_angle 5 _).high_le_of_le (Nat.zero_le k)) at0,
--×     fun h => Meanings.Fraction.le_trans at1 ((the_step_angle 5 _).low_le_of_le h)⟩

-- Episode13.lean, line 9903
--× theorem four_steps_of_a_fifth_and_one_back_of_239_are_the_eighth_turn :
--×     the_gaussian_product (the_phase_walk (5, 1) 4) (239, -1) = (114244, 114244) := by decide

-- Episode13.lean, line 9907
--× theorem the_half_turn_is_written_with_the_two_step_angles :
--×     Meanings.sixteenArctanFifth = (the_step_angle 5 (by decide)).scale 16
--×       ∧ Meanings.fourArctan239th = (the_step_angle 239 (by decide)).scale 4 := ⟨rfl, rfl⟩

-- Episode13.lean, line 9924
--× def the_linear_half_turn : Meanings.Fraction := (⟨16, 5, by decide⟩ : Meanings.Fraction).sub ⟨4, 239, by decide⟩

-- Episode13.lean, line 9926
--× theorem the_linear_half_turn_is : the_linear_half_turn.over = 3804 ∧ the_linear_half_turn.under = 1195 := by decide

-- Episode13.lean, line 9928
--× def the_linear_miss_low : Meanings.Fraction := ⟨4167, 100000, by decide⟩
--× def the_linear_miss_high : Meanings.Fraction := ⟨4168, 100000, by decide⟩

-- Episode13.lean, line 9932
--× theorem the_linear_half_turn_misses (n : Nat) :
--×     ((Meanings.theHalfTurn.high n).add the_linear_miss_low).le the_linear_half_turn
--×       ∧ the_linear_half_turn.le ((Meanings.theHalfTurn.low n).add the_linear_miss_high) :=
--×   ⟨Meanings.Fraction.le_trans
--×     (Meanings.Fraction.add_le_add (Meanings.the_half_turn_is_between n).2 (Meanings.Fraction.le_refl _))
--×     (by decide : (Meanings.theHalfTurnsHighWall.add the_linear_miss_low).le the_linear_half_turn),
--×    Meanings.Fraction.le_trans
--×     (by decide : the_linear_half_turn.le (Meanings.theHalfTurnsLowWall.add the_linear_miss_high))
--×     (Meanings.Fraction.add_le_add (Meanings.the_half_turn_is_between n).1 (Meanings.Fraction.le_refl _))⟩

-- Episode13.lean, line 9944
--× theorem the_eighth_turn_read_linearly_is_four_steps_and_one_back :
--×     the_gaussian_product (the_phase_walk (5, 1) 4) (239, -1) = (114244, 114244)
--×       ∧ ((⟨4, 5, by decide⟩ : Meanings.Fraction).sub ⟨1, 239, by decide⟩).over * 4 = the_linear_half_turn.over
--×       ∧ ((⟨4, 5, by decide⟩ : Meanings.Fraction).sub ⟨1, 239, by decide⟩).under = the_linear_half_turn.under := by
--×   decide

-- Episode13.lean, line 9956
--× theorem the_half_turn_is_under_the_linear_half_turn : (Meanings.theHalfTurn.high 0).le
--×     ((Meanings.Bracketed.ofFraction the_linear_half_turn).low 0) :=
--×   Meanings.Fraction.le_trans (Meanings.the_half_turn_is_between 0).2
--×     (by decide : Meanings.theHalfTurnsHighWall.le the_linear_half_turn)

-- Episode13.lean, line 9961
--× def the_linear_miss : Meanings.Bracketed :=
--×   (Meanings.Bracketed.ofFraction the_linear_half_turn).difference Meanings.theHalfTurn 0
--×     the_half_turn_is_under_the_linear_half_turn

-- Episode13.lean, line 9965
--× def the_miss_squared : Meanings.Bracketed := the_linear_miss.mul the_linear_miss

-- Episode13.lean, line 9967
--× def the_miss_at_least : Meanings.Fraction := the_linear_half_turn.sub Meanings.theHalfTurnsHighWall
--× def the_miss_at_most : Meanings.Fraction := the_linear_half_turn.sub Meanings.theHalfTurnsLowWall

-- Episode13.lean, line 9970
--× theorem the_linear_miss_is_between (n : Nat) :
--×     the_miss_at_least.le (the_linear_miss.low n) ∧ (the_linear_miss.high n).le the_miss_at_most :=
--×   ⟨Meanings.Fraction.sub_le_sub (by decide : Meanings.theHalfTurnsHighWall.le the_linear_half_turn)
--×       (Meanings.Fraction.le_trans (Meanings.the_half_turn_is_between _).2
--×         (by decide : Meanings.theHalfTurnsHighWall.le the_linear_half_turn))
--×       (Meanings.Fraction.le_refl _) (Meanings.the_half_turn_is_between _).2,
--×    Meanings.Fraction.sub_le_sub
--×       (Meanings.Fraction.le_trans (Meanings.theHalfTurn.ordered _)
--×         (Meanings.Fraction.le_trans (Meanings.the_half_turn_is_between _).2
--×           (by decide : Meanings.theHalfTurnsHighWall.le the_linear_half_turn)))
--×       (by decide : Meanings.theHalfTurnsLowWall.le the_linear_half_turn)
--×       (Meanings.Fraction.le_refl _) (Meanings.the_half_turn_is_between _).1⟩

-- Episode13.lean, line 9983
--× def the_square_at_least : Meanings.Fraction := ⟨17364676352, 10 ^ 13, by decide⟩
--× def the_square_at_most : Meanings.Fraction := ⟨17364676361, 10 ^ 13, by decide⟩
--× def one_over_576_and_20535_parts : Meanings.Fraction := ⟨100000000 + 20535, 576 * 100000000, by decide⟩
--× def one_over_576_and_20536_parts : Meanings.Fraction := ⟨100000000 + 20536, 576 * 100000000, by decide⟩

-- Episode13.lean, line 9988
--× theorem the_walls_of_the_miss_squared :
--×     the_square_at_least.le (the_miss_at_least.mul the_miss_at_least)
--×       ∧ (the_miss_at_most.mul the_miss_at_most).le the_square_at_most
--×       ∧ one_over_576_and_20535_parts.le (the_miss_at_least.mul the_miss_at_least)
--×       ∧ (the_miss_at_most.mul the_miss_at_most).le one_over_576_and_20536_parts := by decide

-- Episode13.lean, line 9995
--× theorem the_miss_squared_is_just_past_one_over_twenty_four_squared (n : Nat) :
--×     the_square_at_least.le (the_miss_squared.low n) ∧ (the_miss_squared.high n).le the_square_at_most
--×       ∧ one_over_576_and_20535_parts.le (the_miss_squared.low n)
--×       ∧ (the_miss_squared.high n).le one_over_576_and_20536_parts :=
--×   have lo : (the_miss_at_least.mul the_miss_at_least).le (the_miss_squared.low n) :=
--×     Meanings.Fraction.mul_le_mul (the_linear_miss_is_between _).1 (the_linear_miss_is_between _).1
--×   have hi : (the_miss_squared.high n).le (the_miss_at_most.mul the_miss_at_most) :=
--×     Meanings.Fraction.mul_le_mul (the_linear_miss_is_between _).2 (the_linear_miss_is_between _).2
--×   ⟨Meanings.Fraction.le_trans the_walls_of_the_miss_squared.1 lo,
--×    Meanings.Fraction.le_trans hi the_walls_of_the_miss_squared.2.1,
--×    Meanings.Fraction.le_trans the_walls_of_the_miss_squared.2.2.1 lo,
--×    Meanings.Fraction.le_trans hi the_walls_of_the_miss_squared.2.2.2⟩

-- Episode13.lean, line 10012
--× local infix:50 " ≐ " => Meanings.Bracketed.Same

-- Episode13.lean, line 10022
--× def the_branch_at_a_fifth : Meanings.Bracketed := Meanings.theBranchNeverTaken 1 5 (by decide) (by decide)
--× def the_branch_at_239 : Meanings.Bracketed := Meanings.theBranchNeverTaken 1 239 (by decide) (by decide)

-- Episode13.lean, line 10025
--× theorem the_branches_are_apart : ((the_branch_at_239.scale 4).high 0).le ((the_branch_at_a_fifth.scale 16).low 0) := by
--×   decide +kernel

-- Episode13.lean, line 10029
--× def the_branch_of_the_half_turn : Meanings.Bracketed :=
--×   (the_branch_at_a_fifth.scale 16).difference (the_branch_at_239.scale 4) 0 the_branches_are_apart

-- Episode13.lean, line 10032
--× def sixteen_fifths : Meanings.Fraction := ⟨16 * 1 ^ 1, 5 ^ 1 * (2 * 0 + 1), by decide⟩
--× def four_in_239 : Meanings.Fraction := ⟨4 * 1 ^ 1, 239 ^ 1 * (2 * 0 + 1), by decide⟩

-- Episode13.lean, line 10035
--× theorem the_angle_and_the_branch_at_a_fifth_are_sixteen_fifths :
--×     (Meanings.sixteenArctanFifth.add (the_branch_at_a_fifth.scale 16)) ≐ Meanings.Bracketed.ofFraction sixteen_fifths :=
--×   Meanings.Bracketed.same_trans (Meanings.Bracketed.same_symm (Meanings.Bracketed.scale_add 16 _ _))
--×     (Meanings.Bracketed.same_trans
--×       (Meanings.Bracketed.scale_same 16 (Meanings.the_angle_beside_the_branch_never_taken_is_the_step 1 5 (by decide) (by decide)))
--×       (Meanings.Bracketed.scale_ofFraction 16 _))

-- Episode13.lean, line 10042
--× theorem the_angle_and_the_branch_at_239_are_four_in_239 :
--×     (Meanings.fourArctan239th.add (the_branch_at_239.scale 4)) ≐ Meanings.Bracketed.ofFraction four_in_239 :=
--×   Meanings.Bracketed.same_trans (Meanings.Bracketed.same_symm (Meanings.Bracketed.scale_add 4 _ _))
--×     (Meanings.Bracketed.same_trans
--×       (Meanings.Bracketed.scale_same 4 (Meanings.the_angle_beside_the_branch_never_taken_is_the_step 1 239 (by decide) (by decide)))
--×       (Meanings.Bracketed.scale_ofFraction 4 _))

-- Episode13.lean, line 10049
--× theorem the_linear_half_turn_and_four_in_239_are_sixteen_fifths :
--×     ((Meanings.Bracketed.ofFraction the_linear_half_turn).add (Meanings.Bracketed.ofFraction four_in_239))
--×       ≐ Meanings.Bracketed.ofFraction sixteen_fifths :=
--×   Meanings.Bracketed.same_trans (Meanings.Bracketed.ofFraction_add _ _)
--×     (Meanings.Bracketed.ofFraction_same (by decide) (by decide))

-- Episode13.lean, line 10056
--× theorem the_miss_is_the_branch_never_taken : the_linear_miss ≐ the_branch_of_the_half_turn := by
--×   have hM : (the_linear_miss.add Meanings.theHalfTurn) ≐ Meanings.Bracketed.ofFraction the_linear_half_turn :=
--×     Meanings.Bracketed.difference_add _ _ _ _
--×   have hB : (the_branch_of_the_half_turn.add (the_branch_at_239.scale 4)) ≐ (the_branch_at_a_fifth.scale 16) :=
--×     Meanings.Bracketed.difference_add _ _ _ _
--×   have hπ : (Meanings.theHalfTurn.add Meanings.fourArctan239th) ≐ Meanings.sixteenArctanFifth :=
--×     Meanings.Bracketed.difference_add _ _ _ _
--×   -- the linear half turn beside the branch at 239 is the branch at a fifth beside the half turn
--×   have both : ((Meanings.Bracketed.ofFraction the_linear_half_turn).add (the_branch_at_239.scale 4))
--×       ≐ ((the_branch_at_a_fifth.scale 16).add Meanings.theHalfTurn) := by
--×     apply Meanings.Bracketed.add_cancel (c := Meanings.fourArctan239th)
--×     calc ((Meanings.Bracketed.ofFraction the_linear_half_turn).add (the_branch_at_239.scale 4)).add Meanings.fourArctan239th
--×         ≐ (Meanings.Bracketed.ofFraction the_linear_half_turn).add ((the_branch_at_239.scale 4).add Meanings.fourArctan239th) :=
--×           Meanings.Bracketed.add_assoc _ _ _
--×       _ ≐ (Meanings.Bracketed.ofFraction the_linear_half_turn).add (Meanings.fourArctan239th.add (the_branch_at_239.scale 4)) :=
--×           Meanings.Bracketed.add_same (Meanings.Bracketed.same_refl _) (Meanings.Bracketed.add_comm _ _)
--×       _ ≐ (Meanings.Bracketed.ofFraction the_linear_half_turn).add (Meanings.Bracketed.ofFraction four_in_239) :=
--×           Meanings.Bracketed.add_same (Meanings.Bracketed.same_refl _) the_angle_and_the_branch_at_239_are_four_in_239
--×       _ ≐ Meanings.Bracketed.ofFraction sixteen_fifths := the_linear_half_turn_and_four_in_239_are_sixteen_fifths
--×       _ ≐ Meanings.sixteenArctanFifth.add (the_branch_at_a_fifth.scale 16) :=
--×           Meanings.Bracketed.same_symm the_angle_and_the_branch_at_a_fifth_are_sixteen_fifths
--×       _ ≐ (the_branch_at_a_fifth.scale 16).add Meanings.sixteenArctanFifth := Meanings.Bracketed.add_comm _ _
--×       _ ≐ (the_branch_at_a_fifth.scale 16).add (Meanings.theHalfTurn.add Meanings.fourArctan239th) :=
--×           Meanings.Bracketed.add_same (Meanings.Bracketed.same_refl _) (Meanings.Bracketed.same_symm hπ)
--×       _ ≐ ((the_branch_at_a_fifth.scale 16).add Meanings.theHalfTurn).add Meanings.fourArctan239th :=
--×           Meanings.Bracketed.same_symm (Meanings.Bracketed.add_assoc _ _ _)
--×   apply Meanings.Bracketed.add_cancel (c := Meanings.theHalfTurn.add (the_branch_at_239.scale 4))
--×   calc the_linear_miss.add (Meanings.theHalfTurn.add (the_branch_at_239.scale 4))
--×       ≐ (the_linear_miss.add Meanings.theHalfTurn).add (the_branch_at_239.scale 4) :=
--×         Meanings.Bracketed.same_symm (Meanings.Bracketed.add_assoc _ _ _)
--×     _ ≐ (Meanings.Bracketed.ofFraction the_linear_half_turn).add (the_branch_at_239.scale 4) :=
--×         Meanings.Bracketed.add_same hM (Meanings.Bracketed.same_refl _)
--×     _ ≐ (the_branch_at_a_fifth.scale 16).add Meanings.theHalfTurn := both
--×     _ ≐ (the_branch_of_the_half_turn.add (the_branch_at_239.scale 4)).add Meanings.theHalfTurn :=
--×         Meanings.Bracketed.add_same (Meanings.Bracketed.same_symm hB) (Meanings.Bracketed.same_refl _)
--×     _ ≐ the_branch_of_the_half_turn.add ((the_branch_at_239.scale 4).add Meanings.theHalfTurn) :=
--×         Meanings.Bracketed.add_assoc _ _ _
--×     _ ≐ the_branch_of_the_half_turn.add (Meanings.theHalfTurn.add (the_branch_at_239.scale 4)) :=
--×         Meanings.Bracketed.add_same (Meanings.Bracketed.same_refl _) (Meanings.Bracketed.add_comm _ _)

-- Episode13.lean, line 10097
--× theorem the_miss_squared_is_the_branch_squared :
--×     the_miss_squared ≐ the_branch_of_the_half_turn.mul the_branch_of_the_half_turn :=
--×   Meanings.Bracketed.mul_same the_miss_is_the_branch_never_taken the_miss_is_the_branch_never_taken

-- Episode13.lean, line 10108
--× def the_branch_never_taken_compiles : FACT := IT_COMPILES _ the_miss_is_the_branch_never_taken

-- Episode13.lean, line 10110
--× theorem the_branch_never_taken_clicks : the_representation.the_click the_branch_never_taken_compiles = true := rfl

-- Episode13.lean, line 10112
--× theorem the_branch_never_taken_clicks_as_same_difference :
--×     Quot.mk the_representation.same_click the_branch_never_taken_compiles
--×       = Quot.mk the_representation.same_click the_representation.SAME_DIFFERENCE :=
--×   Quot.sound (the_branch_never_taken_clicks.trans same_difference_is_a_click.symm)

-- Episode13.lean, line 10117
--× theorem asked_only_whether_it_is_true_the_branch_is_same_difference :
--×     the_branch_never_taken_compiles = the_representation.SAME_DIFFERENCE :=
--×   two_facts_that_are_true_are_one_fact _ _ ⟨the_miss_is_the_branch_never_taken⟩ the_representation.same_difference_clicks

-- Episode13.lean, line 10121
--× theorem at_the_first_stages_the_miss_and_the_branch_click_alike :
--×     decide (((the_linear_miss.low 0).le (the_branch_of_the_half_turn.high 0))
--×       ∧ ((the_branch_of_the_half_turn.low 0).le (the_linear_miss.high 0))) = true := by decide +kernel

-- Episode13.lean, line 10138
--× def a_fact_that_is_false : FACT := { truth := False, click := Decidable.isFalse id }

-- Episode13.lean, line 10140
--× def a_true_larger_natural : Natural := .number FACT.Truth (.one FACT.Truth (.zero FACT.Truth)) (.zero FACT.Truth)
--× def a_false_smaller_natural : Natural := .number a_fact_that_is_false (.zero FACT.Truth) (.zero FACT.Truth)
--× def a_true_smaller_natural : Natural := .number FACT.Truth (.zero FACT.Truth) (.zero FACT.Truth)

-- Episode13.lean, line 10144
--× theorem the_true_larger_is_under_the_false_smaller : Natural.le a_true_larger_natural a_false_smaller_natural :=
--×   Or.inr ⟨fun h => cast h (rfl : true = true), True.intro⟩

-- Episode13.lean, line 10147
--× theorem the_false_smaller_is_under_the_true_smaller : Natural.le a_false_smaller_natural a_true_smaller_natural :=
--×   Or.inr ⟨fun h => cast h.symm (rfl : true = true), True.intro⟩

-- Episode13.lean, line 10150
--× theorem the_true_larger_is_not_under_the_true_smaller : ¬ Natural.le a_true_larger_natural a_true_smaller_natural := by
--×   intro h
--×   rcases h with ⟨_, h⟩ | ⟨ne, _⟩
--×   · exact h
--×   · exact ne rfl

-- Episode13.lean, line 10157
--× theorem the_order_is_not_transitive_across_two_truths :
--×     ∃ x y z : Natural, Natural.le x y ∧ Natural.le y z ∧ ¬ Natural.le x z :=
--×   ⟨_, _, _, the_true_larger_is_under_the_false_smaller, the_false_smaller_is_under_the_true_smaller,
--×     the_true_larger_is_not_under_the_true_smaller⟩

-- Episode13.lean, line 10174
--× def the_turned_radius : Meanings.Bracketed := Meanings.theRootOf 414 20 (by decide) (by decide)

-- Episode13.lean, line 10176
--× theorem the_turned_radius_by_itself : (the_turned_radius.mul the_turned_radius).Same (Meanings.Bracketed.ofNat 414) :=
--×   Meanings.theRootOf_by_itself _ _ _ _

-- Episode13.lean, line 10179
--× def the_turned_cosine : Meanings.Bracketed :=
--×   (Meanings.Bracketed.ofNat 18).mul (the_turned_radius.reciprocal 0 (by decide))
--× def the_turned_sine : Meanings.Bracketed :=
--×   Meanings.theRootOfNinety.bracketed.mul (the_turned_radius.reciprocal 0 (by decide))

-- Episode13.lean, line 10184
--× theorem the_turned_parts_squared_are_the_norm_squared :
--×     (((Meanings.Bracketed.ofNat 18).mul (Meanings.Bracketed.ofNat 18)).add
--×       (Meanings.theRootOfNinety.bracketed.mul Meanings.theRootOfNinety.bracketed)).Same (Meanings.Bracketed.ofNat 414) :=
--×   Meanings.Bracketed.same_trans
--×     (Meanings.Bracketed.add_same (Meanings.Bracketed.ofNat_mul 18 18) Meanings.the_root_by_itself_is_ninety)
--×     (Meanings.Bracketed.ofNat_add _ _)

-- Episode13.lean, line 10192
--× theorem the_turned_root_is_on_the_circle :
--×     ((the_turned_cosine.mul the_turned_cosine).add (the_turned_sine.mul the_turned_sine)).Same (Meanings.Bracketed.ofNat 1) :=
--×   Meanings.the_turn_through_its_norm_is_on_the_circle _ _ _ 414 0 (by decide)
--×     the_turned_parts_squared_are_the_norm_squared the_turned_radius_by_itself

-- Episode13.lean, line 10198
--× theorem the_turned_cosine_squared_is_eighteen_twenty_thirds :
--×     (the_turned_cosine.mul the_turned_cosine).Same (Meanings.Bracketed.ofFraction ⟨18, 23, by decide⟩) :=
--×   Meanings.Bracketed.same_trans (Meanings.a_whole_part_over_the_radius_squared 18 the_turned_radius_by_itself (by decide))
--×     (Meanings.Bracketed.ofFraction_same (by decide) (by decide))

-- Episode13.lean, line 10203
--× theorem the_turned_sine_squared_is_five_twenty_thirds :
--×     (the_turned_sine.mul the_turned_sine).Same (Meanings.Bracketed.ofFraction ⟨5, 23, by decide⟩) :=
--×   Meanings.Bracketed.same_trans
--×     (Meanings.a_root_part_over_the_radius_squared Meanings.the_root_by_itself_is_ninety the_turned_radius_by_itself (by decide))
--×     (Meanings.Bracketed.ofFraction_same (by decide) (by decide))

-- Episode13.lean, line 10210
--× theorem the_turned_root_is_its_radius_by_its_turn :
--×     (the_turned_radius.mul the_turned_cosine).Same (Meanings.Bracketed.ofNat 18)
--×       ∧ (the_turned_radius.mul the_turned_sine).Same Meanings.theRootOfNinety.bracketed :=
--×   ⟨Meanings.the_radius_by_a_part_over_it _ _ _ _, Meanings.the_radius_by_a_part_over_it _ _ _ _⟩

-- Episode13.lean, line 10217
--× def machins_radius : Meanings.Bracketed :=
--×   Meanings.theRootOf (114244 * 114244 + 114244 * 114244) 161565 (by decide) (by decide)

-- Episode13.lean, line 10220
--× def machins_cosine : Meanings.Bracketed := (Meanings.Bracketed.ofNat 114244).mul (machins_radius.reciprocal 0 (by decide))

-- Episode13.lean, line 10222
--× theorem machins_turn_is_on_the_circle :
--×     ((machins_cosine.mul machins_cosine).add (machins_cosine.mul machins_cosine)).Same (Meanings.Bracketed.ofNat 1) :=
--×   Meanings.the_turn_through_its_norm_is_on_the_circle _ _ _ _ 0 (by decide)
--×     (Meanings.Bracketed.same_trans
--×       (Meanings.Bracketed.add_same (Meanings.Bracketed.ofNat_mul _ _) (Meanings.Bracketed.ofNat_mul _ _))
--×       (Meanings.Bracketed.ofNat_add _ _))
--×     (Meanings.theRootOf_by_itself _ _ _ _)

-- Episode13.lean, line 10230
--× theorem machins_cosine_squared_is_one_half :
--×     (machins_cosine.mul machins_cosine).Same (Meanings.Bracketed.ofFraction ⟨1, 2, by decide⟩) :=
--×   Meanings.Bracketed.same_trans (Meanings.a_whole_part_over_the_radius_squared 114244 (Meanings.theRootOf_by_itself _ _ _ _) (by decide))
--×     (Meanings.Bracketed.ofFraction_same (by decide) (by decide))

-- Episode13.lean, line 10236
--× theorem machins_steps_are_on_the_circle :
--×     (((Meanings.theStepCosine 5 (by decide)).mul (Meanings.theStepCosine 5 (by decide))).add
--×       ((Meanings.theStepSine 5 (by decide)).mul (Meanings.theStepSine 5 (by decide)))).Same (Meanings.Bracketed.ofNat 1)
--×     ∧ (((Meanings.theStepCosine 239 (by decide)).mul (Meanings.theStepCosine 239 (by decide))).add
--×       ((Meanings.theStepSine 239 (by decide)).mul (Meanings.theStepSine 239 (by decide)))).Same (Meanings.Bracketed.ofNat 1) :=
--×   ⟨Meanings.every_step_is_on_the_circle 5 _, Meanings.every_step_is_on_the_circle 239 _⟩

-- Episode13.lean, line 10247
--× def the_doubled_steps_radius : Meanings.Bracketed :=
--×   Meanings.theRootOf ((5 * 5 - 1 * 1) * (5 * 5 - 1 * 1) + (5 * 1 + 1 * 5) * (5 * 1 + 1 * 5)) 26 (by decide) (by decide)

-- Episode13.lean, line 10250
--× theorem the_step_at_a_fifth_doubled :
--×     the_doubled_steps_radius.Same ((Meanings.theStepRadius 5 (by decide)).mul (Meanings.theStepRadius 5 (by decide)))
--×       ∧ (((Meanings.Bracketed.ofNat (5 * 5 - 1 * 1)).mul (the_doubled_steps_radius.reciprocal 0 (by decide))).add
--×           ((Meanings.theStepSine 5 (by decide)).mul (Meanings.theStepSine 5 (by decide)))).Same
--×           ((Meanings.theStepCosine 5 (by decide)).mul (Meanings.theStepCosine 5 (by decide)))
--×       ∧ ((Meanings.Bracketed.ofNat (5 * 1 + 1 * 5)).mul (the_doubled_steps_radius.reciprocal 0 (by decide))).Same
--×           (((Meanings.theStepCosine 5 (by decide)).mul (Meanings.theStepSine 5 (by decide))).add
--×             ((Meanings.theStepSine 5 (by decide)).mul (Meanings.theStepCosine 5 (by decide)))) :=
--×   Meanings.the_turns_add 5 1 5 1 (by decide) _ _ _ 0 0 0 (by decide) (by decide) (by decide)
--×     (Meanings.theRootOf_by_itself _ _ _ _) (Meanings.theRootOf_by_itself _ _ _ _) (Meanings.theRootOf_by_itself _ _ _ _)

-- Episode13.lean, line 10261
--× theorem the_doubled_steps_radius_is_twenty_six : the_doubled_steps_radius.Same (Meanings.Bracketed.ofNat 26) :=
--×   Meanings.Bracketed.same_of_squares_same
--×     (Meanings.Bracketed.same_trans (Meanings.theRootOf_by_itself _ _ _ _) (Meanings.Bracketed.same_symm (Meanings.Bracketed.ofNat_mul 26 26)))

-- Episode13.lean, line 10265
--× theorem one_over_the_doubled_steps_radius :
--×     (the_doubled_steps_radius.reciprocal 0 (by decide)).Same (Meanings.Bracketed.ofFraction ⟨1, 26, by decide⟩) :=
--×   Meanings.Bracketed.reciprocal_unique (the_doubled_steps_radius.mul_reciprocal 0 (by decide))
--×     (Meanings.Bracketed.same_trans (Meanings.Bracketed.mul_same the_doubled_steps_radius_is_twenty_six (Meanings.Bracketed.same_refl _))
--×       (Meanings.Bracketed.ofNat_by_one_over 26 (by decide)))

-- Episode13.lean, line 10272
--× theorem the_step_doubled_is_five_twelve_thirteen :
--×     ((Meanings.Bracketed.ofNat (5 * 5 - 1 * 1)).mul (the_doubled_steps_radius.reciprocal 0 (by decide))).Same
--×         (Meanings.Bracketed.ofFraction ⟨12, 13, by decide⟩)
--×       ∧ ((Meanings.Bracketed.ofNat (5 * 1 + 1 * 5)).mul (the_doubled_steps_radius.reciprocal 0 (by decide))).Same
--×         (Meanings.Bracketed.ofFraction ⟨5, 13, by decide⟩) :=
--×   ⟨Meanings.Bracketed.same_trans (Meanings.Bracketed.mul_same (Meanings.Bracketed.same_refl _) one_over_the_doubled_steps_radius)
--×       (fun _ _ => ⟨Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl⟩),
--×    Meanings.Bracketed.same_trans (Meanings.Bracketed.mul_same (Meanings.Bracketed.same_refl _) one_over_the_doubled_steps_radius)
--×       (fun _ _ => ⟨Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl⟩)⟩

-- Episode13.lean, line 10286
--× theorem four_steps_of_a_fifth : the_phase_walk (5, 1) 4 = (476, 480) := by decide

-- Episode13.lean, line 10288
--× def four_steps_radius : Meanings.Bracketed := Meanings.theRootOf (476 * 476 + 480 * 480) 676 (by decide) (by decide)
--× def four_steps_over : Meanings.Bracketed := four_steps_radius.reciprocal 0 (by decide)
--× def the_step_back_over : Meanings.Bracketed := (Meanings.theStepRadius 239 (by decide)).reciprocal 0 (by decide)

-- Episode13.lean, line 10292
--× def machins_signed_cosine : Meanings.SignedReal :=
--×   Meanings.SignedReal.ofPair ((476 * 239 + 0 * 0) + (480 * 1 + 0 * 0)) ((476 * 0 + 0 * 239) + (480 * 0 + 0 * 1))
--×     * Meanings.SignedReal.ofReal (four_steps_over.mul the_step_back_over)
--× def machins_signed_sine : Meanings.SignedReal :=
--×   Meanings.SignedReal.ofPair ((476 * 0 + 0 * 1) + (480 * 239 + 0 * 0)) ((476 * 1 + 0 * 0) + (480 * 0 + 0 * 239))
--×     * Meanings.SignedReal.ofReal (four_steps_over.mul the_step_back_over)

-- Episode13.lean, line 10299
--× theorem machins_eighth_turn_by_the_signed_law :
--×     machins_signed_cosine.Same
--×       ((Meanings.SignedReal.ofPair 476 0 * Meanings.SignedReal.ofReal four_steps_over)
--×           * (Meanings.SignedReal.ofPair 239 0 * Meanings.SignedReal.ofReal the_step_back_over)
--×         + -((Meanings.SignedReal.ofPair 480 0 * Meanings.SignedReal.ofReal four_steps_over)
--×           * (Meanings.SignedReal.ofPair 0 1 * Meanings.SignedReal.ofReal the_step_back_over)))
--×     ∧ machins_signed_sine.Same
--×       ((Meanings.SignedReal.ofPair 476 0 * Meanings.SignedReal.ofReal four_steps_over)
--×           * (Meanings.SignedReal.ofPair 0 1 * Meanings.SignedReal.ofReal the_step_back_over)
--×         + (Meanings.SignedReal.ofPair 480 0 * Meanings.SignedReal.ofReal four_steps_over)
--×           * (Meanings.SignedReal.ofPair 239 0 * Meanings.SignedReal.ofReal the_step_back_over)) :=
--×   Meanings.the_signed_turns_add 476 0 480 0 239 0 0 1 _ _

-- Episode13.lean, line 10313
--× theorem machins_signed_cosine_is_its_sine : machins_signed_cosine.Same machins_signed_sine :=
--×   Meanings.SignedReal.mul_same_left (Meanings.SignedReal.ofPair_same (by decide)) _

-- Episode13.lean, line 10330
--× def the_power_walk : Nat → Nat × Nat
--×   | 0 => (1, 1)
--×   | k + 1 => let p := the_power_walk k; (18 * p.1 + 5 * p.2, 18 * p.1 + 18 * p.2)

-- Episode13.lean, line 10334
--× theorem the_power_walk_reads_the_table :
--×     the_power_walk 1 = (the_click_table.1.1 + the_click_table.1.2, the_click_table.2.1 + the_click_table.2.2) := rfl

-- Episode13.lean, line 10338
--× theorem two_rows_multiplied (a b c d x y : Nat) :
--×     (a * x + b * y) * (c * x + d * y) = (a * c) * (x * x) + (a * d + b * c) * (x * y) + (b * d) * (y * y) := by
--×   simp only [Nat.add_mul, Nat.mul_add]
--×   simp only [Nat.mul_comm, Nat.mul_left_comm]
--×   omega

-- Episode13.lean, line 10344
--× theorem the_power_identity (x y : Nat) :
--×     18 * ((18 * x + 5 * y) * (18 * x + 5 * y)) + 234 * (5 * (y * y))
--×       = 5 * ((18 * x + 18 * y) * (18 * x + 18 * y)) + 234 * (18 * (x * x)) := by
--×   rw [two_rows_multiplied, two_rows_multiplied]; omega

-- Episode13.lean, line 10350
--× theorem the_power_walk_stays (k : Nat) :
--×     0 < (the_power_walk k).1 ∧ 0 < (the_power_walk k).2
--×       ∧ 5 * ((the_power_walk k).2 * (the_power_walk k).2) ≤ 18 * ((the_power_walk k).1 * (the_power_walk k).1) := by
--×   induction k with
--×   | zero => exact ⟨by decide, by decide, by decide⟩
--×   | succ k ih =>
--×     obtain ⟨hx, hy, h⟩ := ih
--×     show 0 < 18 * (the_power_walk k).1 + 5 * (the_power_walk k).2 ∧ 0 < 18 * (the_power_walk k).1 + 18 * (the_power_walk k).2
--×       ∧ 5 * ((18 * (the_power_walk k).1 + 18 * (the_power_walk k).2) * (18 * (the_power_walk k).1 + 18 * (the_power_walk k).2))
--×         ≤ 18 * ((18 * (the_power_walk k).1 + 5 * (the_power_walk k).2) * (18 * (the_power_walk k).1 + 5 * (the_power_walk k).2))
--×     have e := the_power_identity (the_power_walk k).1 (the_power_walk k).2
--×     refine ⟨by omega, by omega, ?_⟩
--×     have m := Nat.mul_le_mul_left 234 h
--×     omega

-- Episode13.lean, line 10365
--× def the_power_gap (k : Nat) : Nat :=
--×   18 * ((the_power_walk k).1 * (the_power_walk k).1) - 5 * ((the_power_walk k).2 * (the_power_walk k).2)

-- Episode13.lean, line 10368
--× theorem the_power_gap_grows (k : Nat) : the_power_gap (k + 1) = 234 * the_power_gap k := by
--×   have h := (the_power_walk_stays k).2.2
--×   have e := the_power_identity (the_power_walk k).1 (the_power_walk k).2
--×   unfold the_power_gap
--×   show 18 * ((18 * (the_power_walk k).1 + 5 * (the_power_walk k).2) * (18 * (the_power_walk k).1 + 5 * (the_power_walk k).2))
--×       - 5 * ((18 * (the_power_walk k).1 + 18 * (the_power_walk k).2) * (18 * (the_power_walk k).1 + 18 * (the_power_walk k).2))
--×     = 234 * (18 * ((the_power_walk k).1 * (the_power_walk k).1) - 5 * ((the_power_walk k).2 * (the_power_walk k).2))
--×   omega

-- Episode13.lean, line 10377
--× theorem the_power_gap_is (k : Nat) : the_power_gap k = 13 * 234 ^ k := by
--×   induction k with
--×   | zero => rfl
--×   | succ k ih => rw [the_power_gap_grows, ih, Nat.pow_succ]; omega

-- Episode13.lean, line 10382
--× theorem the_power_walk_grows (k : Nat) :
--×     414 * ((the_power_walk k).1 * (the_power_walk k).2) ≤ (the_power_walk (k + 1)).1 * (the_power_walk (k + 1)).2 := by
--×   show 414 * ((the_power_walk k).1 * (the_power_walk k).2)
--×     ≤ (18 * (the_power_walk k).1 + 5 * (the_power_walk k).2) * (18 * (the_power_walk k).1 + 18 * (the_power_walk k).2)
--×   rw [two_rows_multiplied]; omega

-- Episode13.lean, line 10388
--× theorem the_power_walk_is_at_least (k : Nat) : 414 ^ k ≤ (the_power_walk k).1 * (the_power_walk k).2 := by
--×   induction k with
--×   | zero => decide
--×   | succ k ih =>
--×     rw [Nat.pow_succ, Nat.mul_comm]
--×     exact Nat.le_trans (Nat.mul_le_mul_left 414 ih) (the_power_walk_grows k)

-- Episode13.lean, line 10395
--× theorem the_gap_falls_behind (n : Nat) : 13 * 234 ^ (5 + 2 * n) * (n + 1) ≤ 414 ^ (5 + 2 * n) := by
--×   induction n with
--×   | zero => exact Nat.le_of_ble_eq_true rfl
--×   | succ n ih =>
--×     rw [show 5 + 2 * (n + 1) = (5 + 2 * n) + 2 by omega, Nat.pow_add 234 (5 + 2 * n) 2, Nat.pow_add 414 (5 + 2 * n) 2,
--×       show (234 : Nat) ^ 2 = 54756 from rfl, show (414 : Nat) ^ 2 = 171396 from rfl]
--×     generalize 234 ^ (5 + 2 * n) = P at ih ⊢
--×     generalize 414 ^ (5 + 2 * n) = Q at ih ⊢
--×     have k : 54756 * (n + 1 + 1) ≤ 171396 * (n + 1) := by omega
--×     calc 13 * (P * 54756) * (n + 1 + 1) = (13 * P) * (54756 * (n + 1 + 1)) := by ac_rfl
--×       _ ≤ (13 * P) * (171396 * (n + 1)) := Nat.mul_le_mul_left _ k
--×       _ = 13 * P * (n + 1) * 171396 := by ac_rfl
--×       _ ≤ Q * 171396 := Nat.mul_le_mul_right _ ih

-- Episode13.lean, line 10410
--× theorem the_power_walls_turn_one_step (k : Nat) :
--×     (the_power_walk k).2 * (the_power_walk (k + 1)).1 ≤ (the_power_walk (k + 1)).2 * (the_power_walk k).1 := by
--×   have h := (the_power_walk_stays k).2.2
--×   show (the_power_walk k).2 * (18 * (the_power_walk k).1 + 5 * (the_power_walk k).2)
--×     ≤ (18 * (the_power_walk k).1 + 18 * (the_power_walk k).2) * (the_power_walk k).1
--×   generalize (the_power_walk k).1 = x at *
--×   generalize (the_power_walk k).2 = y at *
--×   have e1 : y * (18 * x + 5 * y) = 18 * (x * y) + 5 * (y * y) := by
--×     rw [Nat.mul_add, Nat.mul_left_comm, Nat.mul_left_comm y 5, Nat.mul_comm y x]
--×   have e2 : (18 * x + 18 * y) * x = 18 * (x * x) + 18 * (x * y) := by
--×     rw [Nat.add_mul, Nat.mul_assoc, Nat.mul_assoc, Nat.mul_comm y x]
--×   rw [e1, e2]; omega

-- Episode13.lean, line 10423
--× theorem the_low_step (x y x' y' : Nat) (t : y * x' ≤ y' * x) : (18 * x + 5 * y) * x' ≤ (18 * x' + 5 * y') * x := by
--×   have e1 : (18 * x + 5 * y) * x' = 18 * (x * x') + 5 * (y * x') := by rw [Nat.add_mul, Nat.mul_assoc, Nat.mul_assoc]
--×   have e2 : (18 * x' + 5 * y') * x = 18 * (x * x') + 5 * (y' * x) := by
--×     rw [Nat.add_mul, Nat.mul_assoc, Nat.mul_assoc, Nat.mul_comm x' x]
--×   rw [e1, e2]; omega

-- Episode13.lean, line 10429
--× theorem the_high_step (x y x' y' : Nat) (t : y * x' ≤ y' * x) : (18 * x' + 18 * y') * y ≤ (18 * x + 18 * y) * y' := by
--×   have e1 : (18 * x' + 18 * y') * y = 18 * (y * x') + 18 * (y * y') := by
--×     rw [Nat.add_mul, Nat.mul_assoc, Nat.mul_assoc, Nat.mul_comm x' y, Nat.mul_comm y' y]
--×   have e2 : (18 * x + 18 * y) * y' = 18 * (y' * x) + 18 * (y * y') := by
--×     rw [Nat.add_mul, Nat.mul_assoc, Nat.mul_assoc, Nat.mul_comm x y']
--×   rw [e1, e2]; omega

-- Episode13.lean, line 10438
--× theorem the_power_low_rises (k : Nat) : ∀ d, ((⟨18 * (the_power_walk k).1 + 5 * (the_power_walk k).2, (the_power_walk k).1,
--×       (the_power_walk_stays k).1⟩ : Meanings.Fraction).le ⟨18 * (the_power_walk (k + d)).1 + 5 * (the_power_walk (k + d)).2,
--×       (the_power_walk (k + d)).1, (the_power_walk_stays _).1⟩)
--×   | 0 => Meanings.Fraction.le_refl _
--×   | d + 1 => Meanings.Fraction.le_trans (the_power_low_rises k d)
--×       (the_low_step _ _ _ _ (the_power_walls_turn_one_step (k + d)))

-- Episode13.lean, line 10445
--× theorem the_power_high_falls (k : Nat) : ∀ d, ((⟨18 * (the_power_walk (k + d)).1 + 18 * (the_power_walk (k + d)).2,
--×       (the_power_walk (k + d)).2, (the_power_walk_stays _).2.1⟩ : Meanings.Fraction).le
--×       ⟨18 * (the_power_walk k).1 + 18 * (the_power_walk k).2, (the_power_walk k).2, (the_power_walk_stays k).2.1⟩)
--×   | 0 => Meanings.Fraction.le_refl _
--×   | d + 1 => Meanings.Fraction.le_trans
--×       (q := ⟨18 * (the_power_walk (k + d)).1 + 18 * (the_power_walk (k + d)).2, (the_power_walk (k + d)).2,
--×         (the_power_walk_stays _).2.1⟩)
--×       (the_high_step _ _ _ _ (the_power_walls_turn_one_step (k + d))) (the_power_high_falls k d)

-- Episode13.lean, line 10454
--× theorem the_power_walls_are_ordered (x y : Nat) (h : 5 * (y * y) ≤ 18 * (x * x)) :
--×     (18 * x + 5 * y) * y ≤ (18 * x + 18 * y) * x := by
--×   have e1 : (18 * x + 5 * y) * y = 18 * (x * y) + 5 * (y * y) := by rw [Nat.add_mul, Nat.mul_assoc, Nat.mul_assoc]
--×   have e2 : (18 * x + 18 * y) * x = 18 * (x * x) + 18 * (x * y) := by
--×     rw [Nat.add_mul, Nat.mul_assoc, Nat.mul_assoc, Nat.mul_comm y x]
--×   rw [e1, e2]; omega

-- Episode13.lean, line 10461
--× theorem the_power_walls_narrow (x y G N : Nat) (split : 18 * (x * x) = 5 * (y * y) + G) (gn : G * N ≤ y * x) :
--×     (18 * x + 18 * y) * x * N ≤ (18 * x + 5 * y) * y * N + y * x := by
--×   have e1 : (18 * x + 18 * y) * x * N = 18 * (x * x) * N + 18 * (x * y) * N := by
--×     rw [Nat.add_mul, Nat.add_mul, Nat.mul_assoc 18 x x, Nat.mul_assoc 18 y x, Nat.mul_comm y x]
--×   have e2 : (18 * x + 5 * y) * y * N = 18 * (x * y) * N + 5 * (y * y) * N := by
--×     rw [Nat.add_mul, Nat.add_mul, Nat.mul_assoc 18 x y, Nat.mul_assoc 5 y y]
--×   rw [e1, e2, split, Nat.add_mul]
--×   omega

-- Episode13.lean, line 10471
--× def the_root_by_the_tables_powers : Meanings.Bracketed where
--×   low n := ⟨18 * (the_power_walk (5 + 2 * n)).1 + 5 * (the_power_walk (5 + 2 * n)).2, (the_power_walk (5 + 2 * n)).1,
--×     (the_power_walk_stays _).1⟩
--×   high n := ⟨18 * (the_power_walk (5 + 2 * n)).1 + 18 * (the_power_walk (5 + 2 * n)).2, (the_power_walk (5 + 2 * n)).2,
--×     (the_power_walk_stays _).2.1⟩
--×   ordered n := the_power_walls_are_ordered _ _ (the_power_walk_stays _).2.2
--×   low_rises n := by
--×     have := the_power_low_rises (5 + 2 * n) 2
--×     rwa [show 5 + 2 * n + 2 = 5 + 2 * (n + 1) by omega] at this
--×   high_falls n := by
--×     have := the_power_high_falls (5 + 2 * n) 2
--×     rwa [show 5 + 2 * n + 2 = 5 + 2 * (n + 1) by omega] at this
--×   narrows n := by
--×     have g := the_power_gap_is (5 + 2 * n)
--×     have h := (the_power_walk_stays (5 + 2 * n)).2.2
--×     have grow := the_power_walk_is_at_least (5 + 2 * n)
--×     have behind := the_gap_falls_behind n
--×     unfold the_power_gap at g
--×     show (18 * (the_power_walk (5 + 2 * n)).1 + 18 * (the_power_walk (5 + 2 * n)).2) * (the_power_walk (5 + 2 * n)).1 * (n + 1)
--×       ≤ (18 * (the_power_walk (5 + 2 * n)).1 + 5 * (the_power_walk (5 + 2 * n)).2) * (the_power_walk (5 + 2 * n)).2 * (n + 1)
--×         + (the_power_walk (5 + 2 * n)).2 * (the_power_walk (5 + 2 * n)).1
--×     generalize (the_power_walk (5 + 2 * n)).1 = x at *
--×     generalize (the_power_walk (5 + 2 * n)).2 = y at *
--×     apply the_power_walls_narrow x y (18 * (x * x) - 5 * (y * y)) (n + 1) (by omega)
--×     rw [g, Nat.mul_comm y x]
--×     exact Nat.le_trans behind grow

-- Episode13.lean, line 10500
--× theorem the_tables_powers_and_the_halving_are_one : the_root_by_the_tables_powers.Same Meanings.theNorm.bracketed := by
--×   intro n m
--×   have h := (the_power_walk_stays (5 + 2 * n)).2.2
--×   have h' := (the_power_walk_stays (5 + 2 * m)).2.2
--×   have four : ∀ j : Nat, 4 ^ j = 2 ^ j * 2 ^ j := fun j => by rw [← Nat.mul_pow]
--×   have root_m := Meanings.theRootOfNinety_holds_the_root m
--×   have root_n := Meanings.theRootOfNinety_holds_the_root n
--×   rw [four] at root_m root_n
--×   constructor
--×   · show (18 * (the_power_walk (5 + 2 * n)).1 + 5 * (the_power_walk (5 + 2 * n)).2) * 2 ^ m
--×       ≤ (18 * 2 ^ m + Meanings.theRootOfNinety.cut m + 1) * (the_power_walk (5 + 2 * n)).1
--×     generalize (the_power_walk (5 + 2 * n)).1 = x at *
--×     generalize (the_power_walk (5 + 2 * n)).2 = y at *
--×     generalize Meanings.theRootOfNinety.cut m = c at *
--×     generalize 2 ^ m = t at *
--×     have sq : (5 * y * t) * (5 * y * t) ≤ ((c + 1) * x) * ((c + 1) * x) := by
--×       have m1 := Nat.mul_le_mul_right (5 * (t * t)) h
--×       have m2 := Nat.mul_le_mul_left (18 * 5 * (x * x)) (Nat.le_of_lt root_m.2)
--×       calc (5 * y * t) * (5 * y * t) = 5 * (y * y) * (5 * (t * t)) := by ac_rfl
--×         _ ≤ 18 * (x * x) * (5 * (t * t)) := m1
--×         _ = 18 * 5 * (x * x) * (t * t) := by ac_rfl
--×         _ = 90 * (x * x) * (t * t) := by rw [show 18 * 5 = 90 by rfl]
--×         _ = x * x * (90 * (t * t)) := by ac_rfl
--×         _ ≤ x * x * ((c + 1) * (c + 1)) := Nat.mul_le_mul_left _ (Nat.le_of_lt root_m.2)
--×         _ = ((c + 1) * x) * ((c + 1) * x) := by ac_rfl
--×     have lin := Nat.mul_self_le_mul_self_iff.1 sq
--×     simp only [Nat.add_mul] at lin ⊢
--×     simp only [Nat.mul_comm, Nat.mul_left_comm] at lin ⊢
--×     omega
--×   · show (18 * 2 ^ n + Meanings.theRootOfNinety.cut n) * (the_power_walk (5 + 2 * m)).2
--×       ≤ (18 * (the_power_walk (5 + 2 * m)).1 + 18 * (the_power_walk (5 + 2 * m)).2) * 2 ^ n
--×     generalize (the_power_walk (5 + 2 * m)).1 = x at *
--×     generalize (the_power_walk (5 + 2 * m)).2 = y at *
--×     generalize Meanings.theRootOfNinety.cut n = c at *
--×     generalize 2 ^ n = t at *
--×     have sq : (c * y) * (c * y) ≤ (18 * x * t) * (18 * x * t) := by
--×       calc (c * y) * (c * y) = (c * c) * (y * y) := by ac_rfl
--×         _ ≤ 90 * (t * t) * (y * y) := Nat.mul_le_mul_right _ root_n.1
--×         _ = 18 * (5 * (y * y)) * (t * t) := by ac_rfl
--×         _ ≤ 18 * (18 * (x * x)) * (t * t) := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h')
--×         _ = (18 * x * t) * (18 * x * t) := by ac_rfl
--×     have lin := Nat.mul_self_le_mul_self_iff.1 sq
--×     simp only [Nat.add_mul] at lin ⊢
--×     simp only [Nat.mul_comm, Nat.mul_left_comm] at lin ⊢
--×     omega

-- Episode13.lean, line 10546
--× theorem the_three_models_of_one_root :
--×     the_root_by_the_tables_powers.Same Meanings.theNorm.bracketed
--×       ∧ ((Meanings.Bracketed.ofNat 18).add the_root_by_the_crank).Same Meanings.theNorm.bracketed
--×       ∧ the_root_by_the_tables_powers.Same ((Meanings.Bracketed.ofNat 18).add the_root_by_the_crank) :=
--×   have crank : ((Meanings.Bracketed.ofNat 18).add the_root_by_the_crank).Same Meanings.theNorm.bracketed :=
--×     Meanings.Bracketed.same_trans
--×       (Meanings.Bracketed.add_same (Meanings.Bracketed.same_refl _) the_crank_and_the_halving_are_one_root)
--×       eighteen_beside_the_root_is_the_norm
--×   ⟨the_tables_powers_and_the_halving_are_one, crank,
--×    Meanings.Bracketed.same_trans the_tables_powers_and_the_halving_are_one (Meanings.Bracketed.same_symm crank)⟩

-- Episode13.lean, line 10566
--× def the_turn_by_a_rational_angle (p q : Nat) (hq : 0 < q) (hp : p ≤ q) : Meanings.ComplexReal :=
--×   ⟨Meanings.SignedReal.ofReal (Meanings.cosine p q hq hp), Meanings.SignedReal.ofReal (Meanings.sine p q hq hp)⟩

-- Episode13.lean, line 10569
--× theorem the_turn_by_a_rational_angle_stays_on_the_circle :
--×     ((Meanings.theLowCircle 1 1 (by decide) (by decide) 3).le ⟨1, 1, by decide⟩
--×       ∧ (⟨1, 1, by decide⟩ : Meanings.Fraction).le (Meanings.theHighCircle 1 1 (by decide) (by decide) 3))
--×     ∧ ((Meanings.theLowCircle 1 2 (by decide) (by decide) 3).le ⟨1, 1, by decide⟩
--×       ∧ (⟨1, 1, by decide⟩ : Meanings.Fraction).le (Meanings.theHighCircle 1 2 (by decide) (by decide) 3)) :=
--×   ⟨Meanings.the_circle_at_one_holds_one, Meanings.the_circle_at_a_half_holds_one⟩

-- Episode13.lean, line 10580
--× theorem the_turn_by_a_rational_angle_is_on_the_circle_at_every_stage (p q : Nat) (hq : 0 < q) (hp : p ≤ q) :
--×     (((Meanings.cosine p q hq hp).mul (Meanings.cosine p q hq hp)).add
--×       ((Meanings.sine p q hq hp).mul (Meanings.sine p q hq hp))).Same (Meanings.Bracketed.ofNat 1) :=
--×   Meanings.the_circle_holds_at_every_stage p q hq hp

-- Episode13.lean, line 10592
--× theorem where_the_series_cross_and_what_each_side_misses (n : Nat) :
--×     ((Meanings.EighthTurn.sineBelow.high 5).lt (Meanings.EighthTurn.cosineBelow.low 5)
--×       ∧ (Meanings.EighthTurn.cosineAbove.high 5).lt (Meanings.EighthTurn.sineAbove.low 5))
--×     ∧ (Meanings.EighthTurn.theWindowsLowWall.le (Meanings.theHalfTurn.low n)
--×       ∧ (Meanings.theHalfTurn.high n).le Meanings.EighthTurn.theWindowsHighWall)
--×     ∧ (0 < (Meanings.EighthTurn.theErrorBelow.low n).over ∧ 0 < (Meanings.EighthTurn.theErrorAbove.low n).over) :=
--×   ⟨⟨Meanings.EighthTurn.below_the_crossing_cosine_is_past_sine, Meanings.EighthTurn.above_the_crossing_sine_is_past_cosine⟩,
--×    Meanings.EighthTurn.machins_half_turn_is_in_the_window n, Meanings.EighthTurn.the_errors_are_past_nothing n⟩

-- Episode13.lean, line 10609
--× theorem the_slip_and_the_coin_flip_turned_over (n m : Nat) (h : 4 ≤ n) :
--×     (Meanings.findByLooking Meanings.EighthTurn.partedBelow
--×         ⟨4, Meanings.EighthTurn.below_nothing_until_the_fourth_stage.2⟩).1 = 4
--×     ∧ (Meanings.findByLooking Meanings.EighthTurn.partedAbove
--×         ⟨3, Meanings.EighthTurn.above_nothing_until_the_third_stage.2⟩).1 = 3
--×     ∧ (0 < ((Meanings.EighthTurn.cosineBelow.low n).sub (Meanings.EighthTurn.sineBelow.high n)).over
--×       ∧ ((Meanings.EighthTurn.sineBelow.high n).sub (Meanings.EighthTurn.cosineBelow.low n)).over = 0)
--×     ∧ (0 < ((Meanings.EighthTurn.sineAbove.low n).sub (Meanings.EighthTurn.cosineAbove.high n)).over
--×       ∧ ((Meanings.EighthTurn.cosineAbove.high n).sub (Meanings.EighthTurn.sineAbove.low n)).over = 0)
--×     ∧ (Meanings.EighthTurn.theErrorBelow.high n).lt (Meanings.EighthTurn.theErrorAbove.low m)
--×     ∧ ((Meanings.EighthTurn.borweinSum 6).lt Meanings.EighthTurn.theOne
--×       ∧ Meanings.EighthTurn.theOne.lt (Meanings.EighthTurn.borweinSum 7)) :=
--×   ⟨Meanings.EighthTurn.the_least_stage_found_by_looking.1, Meanings.EighthTurn.the_least_stage_found_by_looking.2,
--×    Meanings.EighthTurn.below_one_way_something_and_the_other_nothing h,
--×    Meanings.EighthTurn.above_one_way_something_and_the_other_nothing (by omega),
--×    Meanings.EighthTurn.the_error_below_is_under_the_error_above n m, Meanings.EighthTurn.the_borwein_threshold⟩

-- Episode13.lean, line 10632
--× theorem halving_and_its_arrow (gap : Meanings.EighthTurn.TheGap) (n c d : Nat) :
--×     (Meanings.EighthTurn.cutOf gap 12).1 = 3216
--×     ∧ (Meanings.EighthTurn.cutOf gap (n + 1)).1 / 2 = (Meanings.EighthTurn.cutOf gap n).1
--×     ∧ (Meanings.EighthTurn.cutOf gap n).1 ≤ (Meanings.EighthTurn.cutOf gap (n + 1)).1
--×     ∧ ((2 * c) / 2 = c ∧ (2 * c + 1) / 2 = c)
--×     ∧ (2 * (c + 2 ^ d)) % 2 ^ (d + 1) = (2 * c) % 2 ^ (d + 1) :=
--×   ⟨Meanings.EighthTurn.the_first_twelve_halvings gap, Meanings.EighthTurn.the_present_halved_is_the_past gap n,
--×    Meanings.EighthTurn.the_record_never_falls gap n, Meanings.EighthTurn.both_futures_halve_to_one_past c,
--×    Meanings.EighthTurn.doubling_forgets_the_top_bit c d⟩

-- Episode13.lean, line 10649
--× theorem the_other_one_the_baker (gap : Meanings.EighthTurn.TheGap) :
--×     ((Meanings.UnitCut.bake (Meanings.EighthTurn.theEighthTurnsRecord gap, Meanings.UnitCut.nothing)).1.cut 11 = 1168
--×       ∧ ∀ n, (Meanings.UnitCut.bake (Meanings.EighthTurn.theEighthTurnsRecord gap, Meanings.UnitCut.nothing)).2.cut (n + 1)
--×         = 2 ^ n)
--×     ∧ Meanings.UnitCut.unbake (Meanings.UnitCut.bake (Meanings.EighthTurn.theEighthTurnsRecord gap, Meanings.UnitCut.nothing))
--×       = (Meanings.EighthTurn.theEighthTurnsRecord gap, Meanings.UnitCut.nothing)
--×     ∧ (Meanings.UnitCut.doubled (Meanings.UnitCut.pushed 0 (by decide)
--×           (Meanings.UnitCut.doubled (Meanings.EighthTurn.theEighthTurnsRecord gap)))
--×         = Meanings.UnitCut.doubled (Meanings.EighthTurn.theEighthTurnsRecord gap)
--×       ∧ Meanings.UnitCut.pushed 0 (by decide) (Meanings.UnitCut.doubled (Meanings.EighthTurn.theEighthTurnsRecord gap))
--×         ≠ Meanings.EighthTurn.theEighthTurnsRecord gap) :=
--×   ⟨Meanings.EighthTurn.the_eighth_turn_baked_once gap, Meanings.EighthTurn.the_eighth_turn_baked_and_back gap,
--×    Meanings.EighthTurn.the_eighth_turn_and_it_less_a_half_double_alike gap⟩

-- Episode13.lean, line 10678
--× def every_way_held_or_owed : List Int → List (Int × Int)
--×   | [] => [(0, 1)]
--×   | w :: ws => (every_way_held_or_owed ws).flatMap fun (b, e) => [(b + w, e), (b - w, -e)]

-- Episode13.lean, line 10683
--× def to_the_power_on_its_side (b : Int) (n : Nat) : Int := if b < 0 then - b ^ n else b ^ n

-- Episode13.lean, line 10685
--× def the_borwein_sum (m : Nat) : Int :=
--×   ((every_way_held_or_owed (the_rational_explanation m).tail).map fun (b, e) =>
--×     e * to_the_power_on_its_side ((the_rational_explanation m).head! + b) ((the_rational_explanation m).length - 1)).sum

-- Episode13.lean, line 10689
--× def the_borwein_scale (m : Nat) : Int :=
--×   2 ^ ((the_rational_explanation m).length - 1) * (Meanings.factorial ((the_rational_explanation m).length - 1) : Int)
--×     * (the_rational_explanation m).tail.foldl (· * ·) 1

-- Episode13.lean, line 10693
--× theorem through_the_bent_card_is_seven_and_twice_around_is_eight :
--×     through_the_bent_card = 7 ∧ twice_around_the_integral = 8 ∧ bent_card = 13 := by decide

-- Episode13.lean, line 10698
--× theorem through_the_bent_card_the_ratio_is_one :
--×     ∀ m, m < through_the_bent_card + 1 → 0 < m → the_borwein_sum m = the_borwein_scale m := by decide +kernel

-- Episode13.lean, line 10703
--× theorem twice_around_it_slips :
--×     the_borwein_scale twice_around_the_integral - the_borwein_sum twice_around_the_integral
--×       = 2 * (- the_slack twice_around_the_integral) ^ 7
--×     ∧ the_slack twice_around_the_integral = -982
--×     ∧ ((every_way_held_or_owed (the_rational_explanation twice_around_the_integral).tail).map
--×         fun p => (the_rational_explanation twice_around_the_integral).head! + p.1).min? = some (the_slack twice_around_the_integral) := by
--×   decide +kernel

-- Episode13.lean, line 10712
--× theorem the_slip_is_between :
--×     14706 * the_borwein_scale twice_around_the_integral
--×       ≤ 10 ^ 15 * (the_borwein_scale twice_around_the_integral - the_borwein_sum twice_around_the_integral)
--×     ∧ 10 ^ 15 * (the_borwein_scale twice_around_the_integral - the_borwein_sum twice_around_the_integral)
--×       < 14707 * the_borwein_scale twice_around_the_integral := by decide +kernel

-- Episode13.lean, line 10721
--× def the_shortfall_ratio : Meanings.Fraction := ⟨1761207029433090695936, 2 * 119758828728402036135746784000000, by decide⟩

-- Episode13.lean, line 10723
--× theorem the_shortfall_ratio_is_the_slip :
--×     (2 * 119758828728402036135746784000000 : Int) = 2 * the_borwein_scale twice_around_the_integral
--×     ∧ (1761207029433090695936 : Int) = the_borwein_scale twice_around_the_integral - the_borwein_sum twice_around_the_integral := by
--×   decide +kernel

-- Episode13.lean, line 10728
--× theorem the_slip_against_the_half_turn :
--×     (⟨231005, 10 ^ 16, by decide⟩ : Meanings.Fraction).le (Meanings.theHalfTurnsLowWall.mul the_shortfall_ratio)
--×     ∧ (Meanings.theHalfTurnsHighWall.mul the_shortfall_ratio).le ⟨231006, 10 ^ 16, by decide⟩ := by decide +kernel

-- Episode13.lean, line 10743
--× theorem a_turn_at_least_squares_the_whole_part (k : Nat) :
--×     the_whole_part_at k * the_whole_part_at k ≤ the_whole_part_at (k + 1) := by
--×   show _ ≤ the_whole_part_at k * the_whole_part_at k + 90 * (the_part_by_the_root_at k * the_part_by_the_root_at k)
--×   exact Nat.le_add_right _ _

-- Episode13.lean, line 10748
--× theorem the_whole_part_grows_as_a_power_of_a_power (k : Nat) : 10567204 ^ (2 ^ k) ≤ the_whole_part_at k := by
--×   induction k with
--×   | zero => exact Nat.le_refl _
--×   | succ k ih =>
--×     rw [Nat.pow_succ 2 k, Nat.pow_mul, Nat.pow_two]
--×     exact Nat.le_trans (Nat.mul_le_mul ih ih) (a_turn_at_least_squares_the_whole_part k)

-- Episode13.lean, line 10756
--× theorem the_symbols_double_with_every_turn (k : Nat) : 2 ^ (23 * 2 ^ k) ≤ the_whole_part_at k := by
--×   rw [Nat.pow_mul]
--×   exact Nat.le_trans (Nat.pow_le_pow_left (by decide : 2 ^ 23 ≤ 10567204) _) (the_whole_part_grows_as_a_power_of_a_power k)

-- Episode13.lean, line 10762
--× theorem cheap_in_length_dear_in_symbols (n : Nat) :
--×     (the_root_by_the_crank.high n).over * (the_root_by_the_crank.low n).under * (n + 1)
--×         ≤ (the_root_by_the_crank.low n).over * (the_root_by_the_crank.high n).under * (n + 1)
--×           + (the_root_by_the_crank.high n).under * (the_root_by_the_crank.low n).under
--×       ∧ 2 ^ (23 * 2 ^ (n + 4)) ≤ (the_root_by_the_crank.low n).under :=
--×   ⟨the_root_by_the_crank.narrows n, the_symbols_double_with_every_turn (n + 4)⟩

-- Episode13.lean, line 10771
--× theorem the_gap_is_closed_only_by_a_choice_handed_in (x y : Meanings.Bracketed) :
--×     ((∃ n m, x.PartedAt y n m) → ¬ x.Same y) ∧ (¬ x.Same y → ∃ n m, x.PartedAt y n m) ∧ (x.Same y ∨ ¬ x.Same y) :=
--×   ⟨Meanings.Bracketed.parted_is_not_same, Meanings.Bracketed.not_same_is_parted, Meanings.Bracketed.same_or_not_by_choice x y⟩

-- Episode13.lean, line 10789
--× theorem the_diagonal_lands_on_a_crossing_and_the_crossings_read_alike (f : Nat → Meanings.Bracketed) (n : Nat) :
--×     (((Meanings.Diagonal.theDiagonal f).high (n + 1)).lt ((f n).low (3 ^ (n + 1)))
--×       ∨ ((f n).high (3 ^ (n + 1))).lt ((Meanings.Diagonal.theDiagonal f).low (n + 1)))
--×     ∧ the_representation.middle_table true false = the_representation.middle_table false true
--×     ∧ ((true = false) = (false = true)) :=
--×   ⟨Meanings.Diagonal.the_diagonal_crosses f n, the_representation.the_click_diagonal.2.2.2.2,
--×    true_on_false_is_false_on_true_and_implies_true_on_true.1⟩

-- Episode13.lean, line 10797
--× def the_diagonal_compiles (f : Nat → Meanings.Bracketed) : FACT :=
--×   IT_COMPILES _ (fun n => Meanings.Diagonal.the_diagonal_is_none_of_them f n)

-- Episode13.lean, line 10800
--× theorem the_diagonal_clicks (f : Nat → Meanings.Bracketed) :
--×     the_representation.the_click (the_diagonal_compiles f) = true := rfl

-- Episode13.lean, line 10803
--× theorem the_diagonal_clicks_as_same_difference (f : Nat → Meanings.Bracketed) :
--×     Quot.mk the_representation.same_click (the_diagonal_compiles f)
--×       = Quot.mk the_representation.same_click the_representation.SAME_DIFFERENCE :=
--×   Quot.sound ((the_diagonal_clicks f).trans same_difference_is_a_click.symm)

-- Episode13.lean, line 10808
--× theorem asked_only_whether_it_is_true_the_diagonal_is_same_difference (f : Nat → Meanings.Bracketed) :
--×     the_diagonal_compiles f = the_representation.SAME_DIFFERENCE :=
--×   two_facts_that_are_true_are_one_fact _ _ ⟨fun n => Meanings.Diagonal.the_diagonal_is_none_of_them f n⟩
--×     the_representation.same_difference_clicks

-- Episode13.lean, line 10837
--× theorem the_two_choices_handed_back :
--×     the_representation.the_click (the_opposite (the_representation.dealt true)) = false
--×       ∧ the_representation.the_click (the_opposite (the_representation.dealt false)) = true := by decide

-- Episode13.lean, line 10842
--× def the_opposite_diagonal (rows : Nat → Nat → FACT) (n : Nat) : FACT := the_opposite (rows n n)

-- Episode13.lean, line 10844
--× theorem the_opposite_diagonal_is_none_of_the_rows (rows : Nat → Nat → FACT) (n : Nat) :
--×     (fun m => the_representation.the_click (the_opposite_diagonal rows m))
--×       ≠ (fun m => the_representation.the_click (rows n m)) := fun h =>
--×   whatever_they_choose_they_get_the_other (rows n n) (congrFun h n)

-- Episode13.lean, line 10850
--× theorem only_true_in_the_machine_and_the_opposite_handed_back (k : FACT) :
--×     the_clicks.all the_representation.the_click = true
--×       ∧ the_inferences.all the_representation.the_click = true
--×       ∧ the_representation.the_click (the_opposite k) = ! the_representation.the_click k :=
--×   ⟨every_rung_clicks, every_inference_clicks, the_opposite_clicks_the_other_way k⟩

-- Episode13.lean, line 10869
--× def posts (a : Area) : Nat := a.riemann_integrate.length
--× def spans (a : Area) : Nat := compute_the_area_of a

-- Episode13.lean, line 10872
--× theorem posts_less_spans_is_the_fencepost (a : Area) : posts a = spans a + the_fencepost_bug :=
--×   the_riemann_sum_is_indistinguisahble_from_the_bent_card_with_an_extra_fencepost_of_blanks a

-- Episode13.lean, line 10875
--× theorem the_fencepost_is_one : the_fencepost_bug = 1 := rfl

-- Episode13.lean, line 10878
--× theorem a_tapes_spans (t : List FACT) : spans (the_number_of_marks t) = t.length :=
--×   the_number_of_marks_the_tapes_length t

-- Episode13.lean, line 10881
--× theorem a_tapes_posts (t : List FACT) : posts (the_number_of_marks t) = t.length + 1 := by
--×   rw [posts_less_spans_is_the_fencepost, a_tapes_spans, the_fencepost_is_one]

-- Episode13.lean, line 10885
--× theorem subdivision_adds_a_span_and_a_post_and_keeps_the_fencepost (t₁ t₂ : List FACT) (f : FACT) :
--×     spans (the_number_of_marks (t₁ ++ f :: t₂)) = spans (the_area_of_a_tape_in_blanks_is (t₁ ++ t₂)) + 1
--×       ∧ posts (the_number_of_marks (t₁ ++ f :: t₂)) = posts (the_area_of_a_tape_in_blanks_is (t₁ ++ t₂)) + 1
--×       ∧ posts (the_number_of_marks (t₁ ++ f :: t₂)) - spans (the_area_of_a_tape_in_blanks_is (t₁ ++ f :: t₂))
--×         = posts (the_number_of_marks (t₁ ++ t₂)) - spans (the_area_of_a_tape_in_blanks_is (t₁ ++ t₂)) := by
--×   simp only [a_tapes_spans, a_tapes_posts, List.length_append, List.length_cons]
--×   exact ⟨by omega, by omega, by omega⟩

-- Episode13.lean, line 10894
--× theorem cutting_at_a_cell_leaves_two_fenceposts (t₁ t₂ : List FACT) :
--×     (posts (the_number_of_marks t₁) + posts (the_area_of_a_tape_in_blanks_is t₂))
--×       - (spans (the_number_of_marks t₁) + spans (the_area_of_a_tape_in_blanks_is t₂)) = 2 := by
--×   simp only [a_tapes_spans, a_tapes_posts]; omega

-- Episode13.lean, line 10900
--× def holes (knots strands pieces : Nat) : Int := (strands : Int) + pieces - knots

-- Episode13.lean, line 10902
--× theorem subdividing_a_strand_keeps_the_holes (v e c : Nat) : holes (v + 1) (e + 1) c = holes v e c := by
--×   unfold holes; push_cast; omega

-- Episode13.lean, line 10905
--× theorem cutting_a_strand_that_keeps_one_piece_takes_a_hole (v e c : Nat) : holes v e c = holes v (e + 1) c - 1 := by
--×   unfold holes; push_cast; omega

-- Episode13.lean, line 10908
--× theorem cutting_a_strand_that_parts_the_net_keeps_the_holes (v e c : Nat) : holes v e (c + 1) = holes v (e + 1) c := by
--×   unfold holes; push_cast; omega
