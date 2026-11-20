/-
Round the torus.

This file stands beside the device and is built apart: `lake build Experiments.RoundTheTorus`.  Nothing in
`Measurement` imports it.  It defines no inductive.

`Experiments.Common` has one action on the four-torus and its first variation, as a sum over the sites.  To do
anything with that sum, a term at the site one step on has to be counted as a term at the site.  That is: summed
round the torus, a count is unmoved by a step.  It is proved here, and used once: with the mass at four owed, a
state that is the same at every site, on the whole turn on every link.
-/
import Experiments.Common

namespace Measurement
open readers_experience readers_interpretation_of_the_experience

section sums

theorem the_sum_of_one_list_after_another (a b : List Int) : the_sum (a ++ b) = the_sum a + the_sum b := by
  induction a with
  | nil => simp only [List.nil_append, the_sum, Int.zero_add]
  | cons x a ih => simp only [List.cons_append, the_sum, ih, Int.add_assoc]

theorem the_sums_agree {α : Type} (l : List α) (f g : α → Int) (each : ∀ a, f a = g a) :
    the_sum (l.map f) = the_sum (l.map g) := congrArg (fun k => the_sum (l.map k)) (funext each)

theorem the_sum_of_two_counts {α : Type} (l : List α) (f g : α → Int) :
    the_sum (l.map fun x => f x + g x) = the_sum (l.map f) + the_sum (l.map g) := by
  induction l with
  | nil => rfl
  | cons _ l ih => simp only [List.map_cons, the_sum, ih]; omega

theorem the_sum_over_a_list_of_lists {α β : Type} (l : List α) (h : α → List β) (f : β → Int) :
    the_sum ((l.flatMap h).map f) = the_sum (l.map fun a => the_sum ((h a).map f)) := by
  induction l with
  | nil => rfl
  | cons _ l ih => simp only [List.flatMap_cons, List.map_append, the_sum_of_one_list_after_another, List.map_cons, the_sum, ih]

end sums

section round_a_ring

--| ROUND A RING.  The places of a ring, each one step on, are the places of the ring: the last steps to the first.
theorem round_a_ring_the_sum_is_unmoved_by_a_step {n : Nat} (g : Fin (n+1) → Int) :
    the_sum ((List.finRange (n+1)).map fun a => g (a + 1)) = the_sum ((List.finRange (n+1)).map g) := by
  have stepped : the_sum ((List.finRange (n+1)).map fun a => g (a + 1))
      = the_sum ((List.finRange n).map fun i => g i.succ) + g 0 := by
    rw [List.finRange_succ_last]
    simp only [List.map_append, List.map_map, List.map_cons, List.map_nil, the_sum_of_one_list_after_another, the_sum,
      Int.add_zero, Function.comp_def, Fin.coeSucc_eq_succ, Fin.last_add_one]
  have as_it_stands : the_sum ((List.finRange (n+1)).map g) = g 0 + the_sum ((List.finRange n).map fun i => g i.succ) := by
    rw [List.finRange_succ]
    simp only [List.map_cons, List.map_map, the_sum, Function.comp_def]
  rw [stepped, as_it_stands, Int.add_comm]

end round_a_ring

section round_the_torus

--| The sites of the torus are four rings, one inside another.
theorem the_sum_over_the_sites_is_four_sums {n : Nat} (f : Site4 n → Int) :
    the_sum ((the_sites4 n).map f)
      = the_sum ((List.finRange (n+1)).map fun a => the_sum ((List.finRange (n+1)).map fun b =>
          the_sum ((List.finRange (n+1)).map fun c => the_sum ((List.finRange (n+1)).map fun d => f ((a, b), (c, d)))))) := by
  simp only [the_sites4, the_sum_over_a_list_of_lists, List.map_map, Function.comp_def]

--| ROUND THE TORUS.  Summed over every site, a count read one step on, any of the four ways, is the count.
theorem round_the_torus_the_sum_is_unmoved_by_a_step {n : Nat} (f : Site4 n → Int) (way : Direction) :
    the_sum ((the_sites4 n).map fun x => f (the_step way x)) = the_sum ((the_sites4 n).map f) := by
  rw [the_sum_over_the_sites_is_four_sums, the_sum_over_the_sites_is_four_sums]
  obtain ⟨first, second⟩ := way
  cases first <;> cases second
  · exact round_a_ring_the_sum_is_unmoved_by_a_step (fun a => the_sum ((List.finRange (n+1)).map fun b =>
      the_sum ((List.finRange (n+1)).map fun c => the_sum ((List.finRange (n+1)).map fun d => f ((a, b), (c, d))))))
  · exact the_sums_agree _ _ _ fun a => round_a_ring_the_sum_is_unmoved_by_a_step (fun b =>
      the_sum ((List.finRange (n+1)).map fun c => the_sum ((List.finRange (n+1)).map fun d => f ((a, b), (c, d)))))
  · exact the_sums_agree _ _ _ fun a => the_sums_agree _ _ _ fun b => round_a_ring_the_sum_is_unmoved_by_a_step (fun c =>
      the_sum ((List.finRange (n+1)).map fun d => f ((a, b), (c, d))))
  · exact the_sums_agree _ _ _ fun a => the_sums_agree _ _ _ fun b => the_sums_agree _ _ _ fun c =>
      round_a_ring_the_sum_is_unmoved_by_a_step (fun d => f ((a, b), (c, d)))

end round_the_torus

section the_same_state_at_every_site

def the_same_state_at_every_site {n : Nat} (s : Turns) : Site4 n → Turns := fun _ => s

theorem the_whole_turn_first_is_the_turn (q : Turns) : the_turns_product (the_whole_turn 1) q = q := by
  simp [the_turns_product, the_whole_turn]

theorem a_turn_by_two_set_together (p a b : Turns) :
    the_turns_product p (set_together a b) = set_together (the_turns_product p a) (the_turns_product p b) := by
  simp only [the_turns_product, set_together, Prod.mk.injEq, Int.mul_add]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

theorem the_whole_part_of_a_turn_between_a_state_and_itself (s X : Turns) :
    (the_turns_product (the_turns_conjugate s) (the_turns_product X s)).1 = the_turns_norm s * X.1 := by
  have kept := the_whole_part_is_kept (the_turns_conjugate s) X
  rw [the_conjugate_returns, the_conjugate_keeps_the_norm, the_product_is_associative] at kept
  exact kept

--| On the whole turn on every link, with one state at every site: what the state carried back moves by.
theorem carried_back_one_state_moves_by_this {n : Nat} (s : Turns) (dstate : Site4 n → Turns) (dU : Torus4 n)
    (way : Direction) (x : Site4 n) :
    (the_carried_back_moved_by (the_same_state_at_every_site s) dstate the_whole_turn_on_every_link dU way x).1
      = ((the_turns_product (the_turns_conjugate (dstate x)) s).1 + the_turns_norm s * (dU way x).1)
        + (the_turns_product (the_turns_conjugate s) (dstate (the_step way x))).1 := by
  show (set_together (the_turns_product (the_turns_conjugate (dstate x)) (the_turns_product (the_whole_turn 1) s))
      (the_turns_product (the_turns_conjugate s) (set_together (the_turns_product (dU way x) s)
        (the_turns_product (the_whole_turn 1) (dstate (the_step way x)))))).1 = _
  rw [the_whole_turn_first_is_the_turn, the_whole_turn_first_is_the_turn, a_turn_by_two_set_together,
    ← the_whole_part_of_a_turn_between_a_state_and_itself]
  simp only [set_together]; omega

theorem against_itself_one_state_moves_by_this {n : Nat} (s : Turns) (dstate : Site4 n → Turns) (x : Site4 n) :
    (the_against_itself_moved_by (the_same_state_at_every_site s) dstate x).1
      = (the_turns_product (the_turns_conjugate (dstate x)) s).1 + (the_turns_product (the_turns_conjugate s) (dstate x)).1 := rfl

--| ONE STATE AT EVERY SITE, AND THE MASS AT FOUR OWED.  On the whole turn on every link.  Move every state and every link, any
--| way at all.  The first variation of the common action is the state's norm by the whole parts of the links' moves, summed.
--| Nothing of the states' moves is left in it: four ways out of every site, and four owed.
theorem one_state_at_every_site_and_four_owed {n : Nat} (s : Turns) (dstate : Site4 n → Turns) (dU : Torus4 n) :
    the_first_variation_of_the_common_action (-4) (the_same_state_at_every_site s) the_whole_turn_on_every_link dstate dU
      = the_turns_norm s * the_sum (the_directions.map fun way => the_sum ((the_sites4 n).map fun x => (dU way x).1)) := by
  have the_squares : ∀ (way other : Direction) (x : Site4 n),
      the_first_variation_of_the_turns (the_square4 (the_whole_turn_on_every_link (n := n)) way other x)
        (the_square_moved_by the_whole_turn_on_every_link dU way other x) = 0 := fun way other x => by
    show the_first_variation_of_the_turns (the_whole_turn 1) _ = 0
    exact a_whole_turn_is_stationary _ _
  have one_step_on : ∀ way : Direction,
      the_sum ((the_sites4 n).map fun x => (the_turns_product (the_turns_conjugate s) (dstate (the_step way x))).1)
        = the_sum ((the_sites4 n).map fun x => (the_turns_product (the_turns_conjugate s) (dstate x)).1) := fun way =>
    round_the_torus_the_sum_is_unmoved_by_a_step (fun y => (the_turns_product (the_turns_conjugate s) (dstate y)).1) way
  have a_norm_of_the_sum : ∀ way : Direction,
      the_sum ((the_sites4 n).map fun x => the_turns_norm s * (dU way x).1)
        = the_turns_norm s * the_sum ((the_sites4 n).map fun x => (dU way x).1) := fun way => by
    induction the_sites4 n with
    | nil => simp only [List.map_nil, the_sum, Int.mul_zero]
    | cons _ l ih => simp only [List.map_cons, the_sum, ih, Int.mul_add]
  simp only [the_first_variation_of_the_common_action, the_squares, carried_back_one_state_moves_by_this,
    against_itself_one_state_moves_by_this, a_sum_of_nothing, the_sum_of_two_counts, one_step_on, a_norm_of_the_sum,
    the_directions, List.map_cons, List.map_nil, the_sum, Int.mul_add, Int.mul_zero, Int.add_zero, Int.zero_add]
  omega

--| So that state stands still against every move of every state, and against every move of the links that has no whole part.
theorem one_state_at_every_site_stands_still_against_these {n : Nat} (s : Turns) (dstate : Site4 n → Turns) (dU : Torus4 n)
    (no_whole_part : ∀ way x, (dU way x).1 = 0) :
    the_first_variation_of_the_common_action (-4) (the_same_state_at_every_site s) the_whole_turn_on_every_link dstate dU = 0 := by
  rw [one_state_at_every_site_and_four_owed]
  simp only [no_whole_part, a_sum_of_nothing, the_directions, List.map_cons, List.map_nil, the_sum, Int.add_zero, Int.mul_zero]

--| And not against a move of the links that has one.  On the torus of one site, the state the whole turn, every link moved by
--| the whole turn: four.
theorem and_not_against_a_move_with_a_whole_part :
    the_first_variation_of_the_common_action (n := 0) (-4) (the_same_state_at_every_site (the_whole_turn 1))
      the_whole_turn_on_every_link no_move_of_the_state (fun _ _ => the_whole_turn 1) = 4 := by
  rw [one_state_at_every_site_and_four_owed]; decide

end the_same_state_at_every_site

section the_equation_at_a_site_out_of_the_action

--| A STEP BACK.  On a ring, a step on and a step back is where one stood.
theorem on_a_ring_a_step_on_and_a_step_back {n : Nat} (a : Fin (n+1)) : a + 1 - 1 = a := by
  cases n with
  | zero => exact Fin.ext (by omega)
  | succ m =>
    obtain ⟨v, under⟩ := a
    apply Fin.ext
    show ((m + 2) - 1 % (m + 2) + (v + 1 % (m + 2)) % (m + 2)) % (m + 2) = v
    have one : 1 % (m + 2) = 1 := Nat.mod_eq_of_lt (by omega)
    rw [one]
    by_cases last : v + 1 < m + 2
    · rw [Nat.mod_eq_of_lt last, show m + 2 - 1 + (v + 1) = v + (m + 2) by omega, Nat.add_mod_right, Nat.mod_eq_of_lt under]
    · have it_is : v + 1 = m + 2 := by omega
      rw [it_is, Nat.mod_self, Nat.add_zero, Nat.mod_eq_of_lt (by omega)]; omega

def the_step_back {n : Nat} (way : Direction) (x : Site4 n) : Site4 n :=
  if way.1 then (if way.2 then (x.1, (x.2.1, x.2.2 - 1)) else (x.1, (x.2.1 - 1, x.2.2)))
  else (if way.2 then ((x.1.1, x.1.2 - 1), x.2) else ((x.1.1 - 1, x.1.2), x.2))

theorem a_step_on_and_a_step_back {n : Nat} (way : Direction) (x : Site4 n) : the_step_back way (the_step way x) = x := by
  obtain ⟨⟨a, b⟩, ⟨c, d⟩⟩ := x
  obtain ⟨first, second⟩ := way
  cases first <;> cases second
  · show ((a + 1 - 1, b), (c, d)) = _; rw [on_a_ring_a_step_on_and_a_step_back]
  · show ((a, b + 1 - 1), (c, d)) = _; rw [on_a_ring_a_step_on_and_a_step_back]
  · show ((a, b), (c + 1 - 1, d)) = _; rw [on_a_ring_a_step_on_and_a_step_back]
  · show ((a, b), (c, d + 1 - 1)) = _; rw [on_a_ring_a_step_on_and_a_step_back]

theorem the_sum_taken_so_many_times {α : Type} (l : List α) (c : Int) (f : α → Int) :
    the_sum (l.map fun x => c * f x) = c * the_sum (l.map f) := by
  induction l with
  | nil => simp only [List.map_nil, the_sum, Int.mul_zero]
  | cons _ l ih => simp only [List.map_cons, the_sum, ih, Int.mul_add]

def no_move_of_the_links {n : Nat} : Torus4 n := fun _ _ => no_turn

theorem no_turn_first_is_no_turn (q : Turns) : the_turns_product no_turn q = no_turn := by
  simp [the_turns_product, no_turn]
theorem no_turn_set_with_a_turn_is_the_turn (q : Turns) : set_together no_turn q = q := by
  simp [set_together, no_turn]

theorem with_no_link_moved_no_square_moves {n : Nat} (U : Torus4 n) (way other : Direction) (x : Site4 n) :
    the_first_variation_of_the_turns (the_square4 U way other x) (the_square_moved_by U no_move_of_the_links way other x) = 0 := by
  have nothing : the_square_moved_by U no_move_of_the_links way other x = no_turn := by
    simp [the_square_moved_by, the_holonomy_moved_by, no_move_of_the_links, no_turn, set_together, the_turns_product,
      the_turns_conjugate]
  rw [nothing]
  simp [the_first_variation_of_the_turns, the_turns_dot, no_turn]

theorem with_no_link_moved_carried_back_moves_by_this {n : Nat} (state dstate : Site4 n → Turns) (U : Torus4 n)
    (way : Direction) (x : Site4 n) :
    (the_carried_back_moved_by state dstate U no_move_of_the_links way x).1
      = (the_turns_product (the_turns_conjugate (dstate x)) (the_turns_product (U way x) (state (the_step way x)))).1
        + (the_turns_product (the_turns_conjugate (state x)) (the_turns_product (U way x) (dstate (the_step way x)))).1 := by
  show (set_together _ (the_turns_product (the_turns_conjugate (state x))
    (set_together (the_turns_product no_turn (state (the_step way x))) _))).1 = _
  rw [no_turn_first_is_no_turn, no_turn_set_with_a_turn_is_the_turn]; rfl

--| WHAT MULTIPLIES THE MOVE OF THE STATE AT A SITE, IN THE WHOLE ACTION.  Along every way out: the move against what the link
--| brings back from the site ahead.  Along every way in: the state behind, brought on by its link, against the move.  And the
--| mass by the move against the state, both ways round.
def what_multiplies_the_states_move_in_the_common_action {n : Nat} (mass : Int) (state : Site4 n → Turns) (U : Torus4 n)
    (x : Site4 n) (Y : Turns) : Int :=
  the_sum (the_directions.map fun way =>
      (the_turns_product (the_turns_conjugate Y) (the_turns_product (U way x) (state (the_step way x)))).1
        + (the_turns_product (the_turns_conjugate (state (the_step_back way x)))
            (the_turns_product (U way (the_step_back way x)) Y)).1)
    + mass * ((the_turns_product (the_turns_conjugate Y) (state x)).1 + (the_turns_product (the_turns_conjugate (state x)) Y).1)

--| THE FIRST VARIATION IN THE STATES IS A SUM OVER THE SITES.  With no link moved, the first variation of the common action is,
--| at every site, what multiplies the move there, on the move there.  The step from one factor to the other is paid for by
--| the sum round the torus.
theorem the_first_variation_in_the_states_is_a_sum_over_the_sites {n : Nat} (mass : Int) (state : Site4 n → Turns)
    (U : Torus4 n) (dstate : Site4 n → Turns) :
    the_first_variation_of_the_common_action mass state U dstate no_move_of_the_links
      = the_sum ((the_sites4 n).map fun x => what_multiplies_the_states_move_in_the_common_action mass state U x (dstate x)) := by
  have brought_back : ∀ way : Direction,
      the_sum ((the_sites4 n).map fun x =>
          (the_turns_product (the_turns_conjugate (state x)) (the_turns_product (U way x) (dstate (the_step way x)))).1)
        = the_sum ((the_sites4 n).map fun x => (the_turns_product (the_turns_conjugate (state (the_step_back way x)))
            (the_turns_product (U way (the_step_back way x)) (dstate x))).1) := fun way => by
    have round := round_the_torus_the_sum_is_unmoved_by_a_step (fun y =>
      (the_turns_product (the_turns_conjugate (state (the_step_back way y)))
        (the_turns_product (U way (the_step_back way y)) (dstate y))).1) way
    simp only [a_step_on_and_a_step_back] at round
    exact round
  have the_weight : ∀ x : Site4 n, (the_against_itself_moved_by state dstate x).1
      = (the_turns_product (the_turns_conjugate (dstate x)) (state x)).1
        + (the_turns_product (the_turns_conjugate (state x)) (dstate x)).1 := fun _ => rfl
  simp only [the_first_variation_of_the_common_action, with_no_link_moved_no_square_moves,
    with_no_link_moved_carried_back_moves_by_this, the_weight, what_multiplies_the_states_move_in_the_common_action,
    a_sum_of_nothing, the_directions, List.map_cons, List.map_nil, the_sum, Int.add_zero, Int.zero_add,
    the_sum_of_two_counts, the_sum_taken_so_many_times, brought_back]

--| So: where what multiplies the move is nothing at every site, for every move, the action stands still against every move of
--| the states.  That is the equation at a site, out of the action.
theorem where_every_site_has_nothing_the_states_stand_still {n : Nat} (mass : Int) (state : Site4 n → Turns) (U : Torus4 n)
    (at_every_site : ∀ x Y, what_multiplies_the_states_move_in_the_common_action mass state U x Y = 0)
    (dstate : Site4 n → Turns) :
    the_first_variation_of_the_common_action mass state U dstate no_move_of_the_links = 0 := by
  rw [the_first_variation_in_the_states_is_a_sum_over_the_sites]
  simp only [at_every_site, a_sum_of_nothing]

--| One state at every site, the whole turn on every link, and four owed: the equation at a site is met at every site.
theorem one_state_at_every_site_meets_the_equation_at_every_site {n : Nat} (s : Turns) (x : Site4 n) (Y : Turns) :
    what_multiplies_the_states_move_in_the_common_action (-4) (the_same_state_at_every_site s)
      the_whole_turn_on_every_link x Y = 0 := by
  show the_sum (the_directions.map fun _ =>
      (the_turns_product (the_turns_conjugate Y) (the_turns_product (the_whole_turn 1) s)).1
        + (the_turns_product (the_turns_conjugate s) (the_turns_product (the_whole_turn 1) Y)).1)
    + -4 * ((the_turns_product (the_turns_conjugate Y) s).1 + (the_turns_product (the_turns_conjugate s) Y).1) = 0
  simp only [the_whole_turn_first_is_the_turn, the_directions, List.map_cons, List.map_nil, the_sum]
  omega

end the_equation_at_a_site_out_of_the_action

--#print axioms round_the_torus_the_sum_is_unmoved_by_a_step
--#print axioms one_state_at_every_site_and_four_owed
--#print axioms and_not_against_a_move_with_a_whole_part
--#print axioms the_first_variation_in_the_states_is_a_sum_over_the_sites
--#print axioms one_state_at_every_site_meets_the_equation_at_every_site

end Measurement
