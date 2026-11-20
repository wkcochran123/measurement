/-
One action on one space of fields.

This file stands beside the device and is built apart: `lake build Experiments.Common`.  Nothing in `Measurement`
imports it.  It defines no inductive.

A reader's note of 19 November 2026 asked for seven bridges.  The first was one action on one space of fields, from
which every equation in a link and in a state is derived.  Episode 12 has the action of the links summed over the
four-torus.  Episode 13 has the state carried back along a link and the state against itself, site by site.  Here
they are one sum, moved in every link and every state at once, and what multiplies the move is written out.

Also here: the second bridge in one square (a presentation of the square's action in which no term is of more than
the third degree), and a cubic in one place whose slope is the device's residual.

What is not here is said at the end.
-/
import Measurement.Episode13

namespace Measurement
open readers_experience readers_interpretation_of_the_experience

section turns_set_together

--| Two turns set together, a turn taken so many times, and no turn.
def no_turn : Turns := (0, 0, 0, 0)
def set_together (p q : Turns) : Turns := (p.1 + q.1, p.2.1 + q.2.1, p.2.2.1 + q.2.2.1, p.2.2.2 + q.2.2.2)
def so_many_of (c : Int) (q : Turns) : Turns := (c * q.1, c * q.2.1, c * q.2.2.1, c * q.2.2.2)

end turns_set_together

section what_it_is_to_move

--| TO MOVE.  A turn that depends on a number moves from a start by a move when, at every number, it is the start, the number
--| of the move, and the number squared of something over.  The move is then what multiplies the number: the first variation.
def moves_from (F : Int → Turns) (start by_this : Turns) : Prop :=
  ∀ t, ∃ over, F t = the_varied_turns (the_varied_turns start by_this t) over (t * t)
def the_count_moves_from (f : Int → Int) (start by_this : Int) : Prop :=
  ∀ t, ∃ over, f t = start + t * by_this + t * t * over

theorem what_stands_moves_by_nothing (a : Turns) : moves_from (fun _ => a) a no_turn := fun t =>
  ⟨no_turn, by simp only [the_varied_turns, no_turn, Int.mul_zero, Int.add_zero]⟩

theorem a_line_moves_by_its_move (a X : Turns) : moves_from (fun t => the_varied_turns a X t) a X := fun t =>
  ⟨no_turn, by simp only [the_varied_turns, no_turn, Int.mul_zero, Int.add_zero]⟩

theorem a_conjugate_moves (F : Int → Turns) (start by_this : Turns) (it_moves : moves_from F start by_this) :
    moves_from (fun t => the_turns_conjugate (F t)) (the_turns_conjugate start) (the_turns_conjugate by_this) := fun t => by
  obtain ⟨over, so⟩ := it_moves t
  exact ⟨the_turns_conjugate over, by show the_turns_conjugate (F t) = _; rw [so, the_conjugate_is_linear, the_conjugate_is_linear]⟩

--| The product rule.  One by the other moves by the one's move by the other, and the one by the other's move, set together.
theorem a_product_moves (F G : Int → Turns) (F₀ dF G₀ dG : Turns)
    (the_one : moves_from F F₀ dF) (the_other : moves_from G G₀ dG) :
    moves_from (fun t => the_turns_product (F t) (G t)) (the_turns_product F₀ G₀)
      (set_together (the_turns_product dF G₀) (the_turns_product F₀ dG)) := fun t => by
  obtain ⟨W, hW⟩ := the_one t
  obtain ⟨V, hV⟩ := the_other t
  refine ⟨set_together (set_together (the_turns_product dF dG) (set_together (the_turns_product F₀ V) (the_turns_product W G₀)))
    (set_together (so_many_of t (set_together (the_turns_product dF V) (the_turns_product W dG)))
      (so_many_of (t * t) (the_turns_product W V))), ?_⟩
  show the_turns_product (F t) (G t) = _
  rw [hW, hV]
  simp only [the_product_is_linear_on_the_left, the_product_is_linear_on_the_right]
  generalize the_turns_product F₀ G₀ = a
  generalize the_turns_product F₀ dG = b
  generalize the_turns_product F₀ V = c
  generalize the_turns_product dF G₀ = d
  generalize the_turns_product dF dG = e
  generalize the_turns_product dF V = f
  generalize the_turns_product W G₀ = g
  generalize the_turns_product W dG = h
  generalize the_turns_product W V = k
  simp only [the_varied_turns, set_together, so_many_of, Prod.mk.injEq, Int.mul_add]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [Int.mul_assoc] <;> omega

--| Read off: the whole part of a turn that moves, and its action.
theorem the_whole_part_moves (F : Int → Turns) (start by_this : Turns) (it_moves : moves_from F start by_this) :
    the_count_moves_from (fun t => (F t).1) start.1 by_this.1 := fun t => by
  obtain ⟨over, so⟩ := it_moves t
  exact ⟨over.1, by show (F t).1 = _; rw [so]; rfl⟩

theorem the_action_of_a_turn_moves (F : Int → Turns) (start by_this : Turns) (it_moves : moves_from F start by_this) :
    the_count_moves_from (fun t => the_turns_action (F t)) (the_turns_action start)
      (the_first_variation_of_the_turns start by_this) := fun t => by
  obtain ⟨over, so⟩ := it_moves t
  refine ⟨the_turns_action by_this + the_first_variation_of_the_turns (the_varied_turns start by_this t) over
    + t * t * the_turns_action over, ?_⟩
  show the_turns_action (F t) = _
  rw [so, the_turns_action_stops_at_second_order, the_turns_action_stops_at_second_order]
  generalize the_first_variation_of_the_turns (the_varied_turns start by_this t) over = a
  generalize the_turns_action over = b
  generalize the_turns_action by_this = c
  generalize the_first_variation_of_the_turns start by_this = d
  simp only [Int.mul_add, Int.mul_assoc]
  omega

--| Counts that move, set together, taken so many times, and summed along a list.
theorem counts_that_move_set_together (f g : Int → Int) (f₀ df g₀ dg : Int)
    (the_one : the_count_moves_from f f₀ df) (the_other : the_count_moves_from g g₀ dg) :
    the_count_moves_from (fun t => f t + g t) (f₀ + g₀) (df + dg) := fun t => by
  obtain ⟨p, hp⟩ := the_one t
  obtain ⟨q, hq⟩ := the_other t
  refine ⟨p + q, ?_⟩
  show f t + g t = _
  rw [hp, hq]; simp only [Int.mul_add]; omega

theorem a_count_that_moves_taken_so_many_times (c : Int) (f : Int → Int) (f₀ df : Int)
    (it_moves : the_count_moves_from f f₀ df) : the_count_moves_from (fun t => c * f t) (c * f₀) (c * df) := fun t => by
  obtain ⟨p, hp⟩ := it_moves t
  refine ⟨c * p, ?_⟩
  show c * f t = _
  rw [hp]
  simp only [Int.mul_add, Int.mul_left_comm c]

theorem the_sums_move {α : Type} (l : List α) (f : α → Int → Int) (start by_this : α → Int)
    (each_moves : ∀ x, the_count_moves_from (f x) (start x) (by_this x)) :
    the_count_moves_from (fun t => the_sum (l.map fun x => f x t)) (the_sum (l.map start)) (the_sum (l.map by_this)) := fun t => by
  induction l with
  | nil => exact ⟨0, by simp only [List.map_nil, the_sum, Int.mul_zero, Int.add_zero]⟩
  | cons a l ih =>
    obtain ⟨p, hp⟩ := each_moves a t
    obtain ⟨q, hq⟩ := ih
    refine ⟨p + q, ?_⟩
    simp only [List.map_cons, the_sum] at hq ⊢
    rw [hp, hq]; simp only [Int.mul_add]; omega

--| THE MOVE IS ONE THING.  If a count moves from a start by this and also by that, this is that.  So what multiplies the move
--| is fixed by the count, and may be called its first variation.
theorem what_multiplies_the_move_is_one_thing (f : Int → Int) (start this that : Int)
    (by_this : the_count_moves_from f start this) (by_that : the_count_moves_from f start that) : this = that := by
  obtain ⟨p, hp⟩ := by_this (3 * (this - that))
  obtain ⟨q, hq⟩ := by_that (3 * (this - that))
  rw [hp] at hq
  generalize hd : this - that = d at hq
  have this_is : this = that + d := by omega
  subst this_is
  have squared : 3 * d * (3 * d) = 9 * (d * d) := by
    rw [Int.mul_assoc, Int.mul_left_comm d, ← Int.mul_assoc]; rfl
  rw [squared, Int.mul_add, Int.mul_assoc 3 d d, Int.mul_assoc 9 (d * d) p, Int.mul_assoc 9 (d * d) q] at hq
  generalize he : d * d = e at hq
  generalize 3 * d * that = u at hq
  have key : e * (1 - 3 * (q - p)) = 0 := by
    rw [Int.mul_sub, Int.mul_one, Int.mul_left_comm, Int.mul_sub]; omega
  rcases Int.mul_eq_zero.mp key with zero | impossible
  · rw [zero] at he
    rcases Int.mul_eq_zero.mp he with nothing | nothing <;> omega
  · omega

end what_it_is_to_move

section the_common_action

--| THE FIELDS, AND THE FIELDS MOVED.  A turn on every link and a turn at every site.  A direction in that space is a turn on
--| every link and a turn at every site again.
def the_links_moved {n : Nat} (U dU : Torus4 n) (t : Int) : Torus4 n := fun way x => the_varied_turns (U way x) (dU way x) t
def the_state_moved {n : Nat} (state dstate : Site4 n → Turns) (t : Int) : Site4 n → Turns :=
  fun x => the_varied_turns (state x) (dstate x) t

--| THE ACTION.  Episode 12's action of the links over every square of the torus; the whole part of the state carried back
--| along every link; and the whole part of the state against itself at every site, taken by a number called the mass.
def the_common_action {n : Nat} (mass : Int) (state : Site4 n → Turns) (U : Torus4 n) : Int :=
  the_action4 U
    + the_sum (the_directions.map fun way => the_sum ((the_sites4 n).map fun x => (the_state_carried_back state U way x).1))
    + mass * the_sum ((the_sites4 n).map fun x => (the_state_against_itself state x).1)

--| A turn of length one at every site, of the links and the state together, leaves it.
theorem the_common_action_is_left_by_a_turn_at_every_site {n : Nat} (mass : Int) (state : Site4 n → Turns) (U : Torus4 n)
    (g : Site4 n → Turns) (unit : ∀ x, the_turns_norm (g x) = 1) :
    the_common_action mass (the_gauged_state state g) (the_gauged_torus4 U g) = the_common_action mass state U := by
  simp only [the_common_action, every_four_torus_is_gauge_invariant U g unit,
    the_state_carried_back_is_gauge_invariant state U g unit, the_state_against_itself_is_gauge_invariant state g unit]

--| WHAT MULTIPLIES THE MOVE.  A square's four links each moved; the state carried back with both states and the link moved;
--| the state against itself.
def the_holonomy_moved_by (B R T L dB dR dT dL : Turns) : Turns :=
  set_together
    (the_turns_product
      (set_together
        (the_turns_product (set_together (the_turns_product dB R) (the_turns_product B dR)) (the_turns_conjugate T))
        (the_turns_product (the_turns_product B R) (the_turns_conjugate dT)))
      (the_turns_conjugate L))
    (the_turns_product (the_turns_product (the_turns_product B R) (the_turns_conjugate T)) (the_turns_conjugate dL))

theorem a_holonomy_moves (B R T L : Int → Turns) (B₀ R₀ T₀ L₀ dB dR dT dL : Turns)
    (bottom : moves_from B B₀ dB) (right : moves_from R R₀ dR) (top : moves_from T T₀ dT) (left : moves_from L L₀ dL) :
    moves_from (fun t => the_turns_holonomy (B t) (R t) (T t) (L t)) (the_turns_holonomy B₀ R₀ T₀ L₀)
      (the_holonomy_moved_by B₀ R₀ T₀ L₀ dB dR dT dL) :=
  a_product_moves _ _ _ _ _ _
    (a_product_moves _ _ _ _ _ _ (a_product_moves _ _ _ _ _ _ bottom right) (a_conjugate_moves _ _ _ top))
    (a_conjugate_moves _ _ _ left)

def the_square_moved_by {n : Nat} (U dU : Torus4 n) (way other : Direction) (x : Site4 n) : Turns :=
  the_holonomy_moved_by (U way x) (U other (the_step way x)) (U way (the_step other x)) (U other x)
    (dU way x) (dU other (the_step way x)) (dU way (the_step other x)) (dU other x)

def the_carried_back_moved_by {n : Nat} (state dstate : Site4 n → Turns) (U dU : Torus4 n) (way : Direction) (x : Site4 n) : Turns :=
  set_together
    (the_turns_product (the_turns_conjugate (dstate x)) (the_turns_product (U way x) (state (the_step way x))))
    (the_turns_product (the_turns_conjugate (state x))
      (set_together (the_turns_product (dU way x) (state (the_step way x))) (the_turns_product (U way x) (dstate (the_step way x)))))

def the_against_itself_moved_by {n : Nat} (state dstate : Site4 n → Turns) (x : Site4 n) : Turns :=
  set_together (the_turns_product (the_turns_conjugate (dstate x)) (state x))
    (the_turns_product (the_turns_conjugate (state x)) (dstate x))

def the_first_variation_of_the_common_action {n : Nat} (mass : Int) (state : Site4 n → Turns) (U : Torus4 n)
    (dstate : Site4 n → Turns) (dU : Torus4 n) : Int :=
  the_sum (the_directions.map fun way => the_sum (the_directions.map fun other => the_sum ((the_sites4 n).map fun x =>
      the_first_variation_of_the_turns (the_square4 U way other x) (the_square_moved_by U dU way other x))))
    + the_sum (the_directions.map fun way => the_sum ((the_sites4 n).map fun x =>
        (the_carried_back_moved_by state dstate U dU way x).1))
    + mass * the_sum ((the_sites4 n).map fun x => (the_against_itself_moved_by state dstate x).1)

--| THE ACTION, MOVED.  Move every link and every state at once, along any direction.  The action is what it was, the number
--| of the move by the first variation, and the number squared by something over.  On every torus, whatever its size.
theorem the_common_action_moves_by_its_first_variation {n : Nat} (mass : Int) (state : Site4 n → Turns) (U : Torus4 n)
    (dstate : Site4 n → Turns) (dU : Torus4 n) :
    the_count_moves_from (fun t => the_common_action mass (the_state_moved state dstate t) (the_links_moved U dU t))
      (the_common_action mass state U) (the_first_variation_of_the_common_action mass state U dstate dU) := by
  have the_light : the_count_moves_from (fun t => the_action4 (the_links_moved U dU t)) (the_action4 U)
      (the_sum (the_directions.map fun way => the_sum (the_directions.map fun other => the_sum ((the_sites4 n).map fun x =>
        the_first_variation_of_the_turns (the_square4 U way other x) (the_square_moved_by U dU way other x))))) :=
    the_sums_move the_directions
      (fun way t => the_sum (the_directions.map fun other => the_sum ((the_sites4 n).map fun x =>
        the_turns_action (the_square4 (the_links_moved U dU t) way other x)))) _ _
      fun way => the_sums_move the_directions
        (fun other t => the_sum ((the_sites4 n).map fun x =>
          the_turns_action (the_square4 (the_links_moved U dU t) way other x))) _ _
        fun other => the_sums_move (the_sites4 n)
          (fun x t => the_turns_action (the_square4 (the_links_moved U dU t) way other x)) _ _
          fun x => the_action_of_a_turn_moves _ _ _
            (a_holonomy_moves _ _ _ _ _ _ _ _ _ _ _ _ (a_line_moves_by_its_move _ _) (a_line_moves_by_its_move _ _)
              (a_line_moves_by_its_move _ _) (a_line_moves_by_its_move _ _))
  have the_carrying : the_count_moves_from
      (fun t => the_sum (the_directions.map fun way => the_sum ((the_sites4 n).map fun x =>
        (the_state_carried_back (the_state_moved state dstate t) (the_links_moved U dU t) way x).1)))
      (the_sum (the_directions.map fun way => the_sum ((the_sites4 n).map fun x => (the_state_carried_back state U way x).1)))
      (the_sum (the_directions.map fun way => the_sum ((the_sites4 n).map fun x =>
        (the_carried_back_moved_by state dstate U dU way x).1))) :=
    the_sums_move the_directions
      (fun way t => the_sum ((the_sites4 n).map fun x =>
        (the_state_carried_back (the_state_moved state dstate t) (the_links_moved U dU t) way x).1)) _ _
      fun way => the_sums_move (the_sites4 n)
        (fun x t => (the_state_carried_back (the_state_moved state dstate t) (the_links_moved U dU t) way x).1) _ _
        fun x => the_whole_part_moves _ _ _
          (a_product_moves _ _ _ _ _ _ (a_conjugate_moves _ _ _ (a_line_moves_by_its_move _ _))
            (a_product_moves _ _ _ _ _ _ (a_line_moves_by_its_move _ _) (a_line_moves_by_its_move _ _)))
  have the_weight : the_count_moves_from
      (fun t => the_sum ((the_sites4 n).map fun x => (the_state_against_itself (the_state_moved state dstate t) x).1))
      (the_sum ((the_sites4 n).map fun x => (the_state_against_itself state x).1))
      (the_sum ((the_sites4 n).map fun x => (the_against_itself_moved_by state dstate x).1)) :=
    the_sums_move (the_sites4 n) (fun x t => (the_state_against_itself (the_state_moved state dstate t) x).1) _ _
      fun x => the_whole_part_moves _ _ _
        (a_product_moves _ _ _ _ _ _ (a_conjugate_moves _ _ _ (a_line_moves_by_its_move _ _)) (a_line_moves_by_its_move _ _))
  exact counts_that_move_set_together _ _ _ _ _ _
    (counts_that_move_set_together _ _ _ _ _ _ the_light the_carrying)
    (a_count_that_moves_taken_so_many_times mass _ _ _ the_weight)

--| TO STAND STILL.  The first variation is nothing along every direction: every link and every state, all at once.
def the_common_action_stands_still {n : Nat} (mass : Int) (state : Site4 n → Turns) (U : Torus4 n) : Prop :=
  ∀ (dstate : Site4 n → Turns) (dU : Torus4 n), the_first_variation_of_the_common_action mass state U dstate dU = 0

end the_common_action

section what_stands_still

theorem a_sum_of_nothing {α : Type} (l : List α) : the_sum (l.map fun _ => (0 : Int)) = 0 := by
  induction l with
  | nil => rfl
  | cons _ l ih => simp only [List.map_cons, the_sum, ih, Int.add_zero]

--| A turn by its conjugate is whole, and a whole turn passes through a product.
theorem a_turn_by_its_conjugate_is_whole (q : Turns) :
    the_turns_product q (the_turns_conjugate q) = the_whole_turn (the_turns_norm q) := by
  simp only [the_turns_product, the_turns_conjugate, the_whole_turn, the_turns_norm, Prod.mk.injEq, Int.mul_neg]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ac_nf <;> omega

theorem a_whole_turn_in_the_middle (p q : Turns) (c : Int) :
    the_turns_product (the_turns_product p (the_whole_turn c)) q = so_many_of c (the_turns_product p q) := by
  simp only [the_turns_product, the_whole_turn, so_many_of, Prod.mk.injEq, Int.mul_zero, Int.add_zero,
    Int.sub_zero, Int.zero_add, Int.mul_add, Int.mul_sub]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ac_nf <;> omega

--| One turn on every link.  Round any square it comes back whole: the norm by the norm.
theorem one_turn_round_a_square_is_whole (q : Turns) :
    the_turns_holonomy q q q q = the_whole_turn (the_turns_norm q * the_turns_norm q) := by
  show the_turns_product (the_turns_product (the_turns_product q q) (the_turns_conjugate q)) (the_turns_conjugate q) = _
  rw [the_product_is_associative q q, a_turn_by_its_conjugate_is_whole, a_whole_turn_in_the_middle,
    a_turn_by_its_conjugate_is_whole]
  simp only [so_many_of, the_whole_turn, Int.mul_zero]

def the_same_turn_on_every_link {n : Nat} (q : Turns) : Torus4 n := fun _ _ => q

--| So one turn on every link and no state stands still: against every move of every link and every state, on every torus,
--| for every mass.  The turn need not be of length one, and need not be whole.
theorem one_turn_on_every_link_and_no_state_stands_still {n : Nat} (mass : Int) (q : Turns) :
    the_common_action_stands_still mass (no_state (n := n)) (the_same_turn_on_every_link q) := by
  intro dstate dU
  have the_squares : ∀ (way other : Direction) (x : Site4 n),
      the_first_variation_of_the_turns (the_square4 (the_same_turn_on_every_link (n := n) q) way other x)
        (the_square_moved_by (the_same_turn_on_every_link q) dU way other x) = 0 := fun way other x => by
    show the_first_variation_of_the_turns (the_turns_holonomy q q q q) _ = 0
    rw [one_turn_round_a_square_is_whole]; exact a_whole_turn_is_stationary _ _
  have the_carrying : ∀ (way : Direction) (x : Site4 n),
      (the_carried_back_moved_by (no_state (n := n)) dstate (the_same_turn_on_every_link q) dU way x).1 = 0 := fun way x => by
    simp [the_carried_back_moved_by, no_state, the_turns_product, the_turns_conjugate, set_together]
  have the_weight : ∀ x : Site4 n, (the_against_itself_moved_by (no_state (n := n)) dstate x).1 = 0 := fun x => by
    simp [the_against_itself_moved_by, no_state, the_turns_product, the_turns_conjugate, set_together]
  simp only [the_first_variation_of_the_common_action, the_squares, the_carrying, the_weight, a_sum_of_nothing,
    Int.mul_zero, Int.add_zero]

--| THE VACUUM, AGAIN.  The whole turn on every link is one such.
theorem the_vacuum_stands_still_in_the_common_action {n : Nat} (mass : Int) :
    the_common_action_stands_still mass (no_state (n := n)) the_whole_turn_on_every_link :=
  one_turn_on_every_link_and_no_state_stands_still mass (the_whole_turn 1)

--| THE TABLE ON EVERY LINK.  Episode 12: twice the table is thirty-six of the same, twenty-three of the swap and thirteen of
--| the quarter turn.  As a turn it is not whole and not of length one.  On every link, with no state, it stands still.
def twice_the_table_as_a_turn : Turns := (36, 23, 13, 0)

theorem twice_the_table_is_not_whole_and_not_of_length_one :
    the_turns_norm twice_the_table_as_a_turn = 1994 ∧ the_turns_action twice_the_table_as_a_turn = 698 := by decide

theorem twice_the_table_on_every_link_stands_still {n : Nat} (mass : Int) :
    the_common_action_stands_still mass (no_state (n := n)) (the_same_turn_on_every_link twice_the_table_as_a_turn) :=
  one_turn_on_every_link_and_no_state_stands_still mass twice_the_table_as_a_turn

end what_stands_still

section the_current_out_of_the_common_action

--| THE CURRENT.  Leave every state where it is and move the links.  What the state carried back moves by is Episode 13's
--| current in the link, on the link's own move.  So the current is not put beside the action: it is what multiplies a link's
--| move in the part of the common action that holds the state.
def no_move_of_the_state {n : Nat} : Site4 n → Turns := fun _ => no_turn

theorem with_no_state_moved_what_is_carried_back_moves_by_the_current {n : Nat} (state : Site4 n → Turns) (U dU : Torus4 n)
    (way : Direction) (x : Site4 n) :
    the_carried_back_moved_by state no_move_of_the_state U dU way x = the_current_in_the_link state way x (dU way x) := by
  simp [the_carried_back_moved_by, the_current_in_the_link, no_move_of_the_state, no_turn, set_together, the_turns_product,
    the_turns_conjugate]

theorem with_no_state_moved_the_weight_does_not_move {n : Nat} (state : Site4 n → Turns) (x : Site4 n) :
    the_against_itself_moved_by state no_move_of_the_state x = no_turn := by
  simp [the_against_itself_moved_by, no_move_of_the_state, no_turn, set_together, the_turns_product, the_turns_conjugate]

end the_current_out_of_the_common_action

section a_square_presented_in_the_third_degree

--| THE SECOND BRIDGE, IN ONE SQUARE.  The action of a square is of the eighth degree in its four links.  Hand in three turns
--| more, the bottom by the right, the left by the top, and the one by the other turned over, and a multiplier for each.  Then
--| no term is a product of more than three.
def one_turn_against_another (p q : Turns) : Int := p.1 * q.1 + p.2.1 * q.2.1 + p.2.2.1 * q.2.2.1 + p.2.2.2 * q.2.2.2
def the_one_less_the_other (p q : Turns) : Turns := (p.1 - q.1, p.2.1 - q.2.1, p.2.2.1 - q.2.2.1, p.2.2.2 - q.2.2.2)

def a_multiplier_term (multiplier handed_in one other : Turns) : Int :=
  one_turn_against_another multiplier (the_one_less_the_other handed_in (the_turns_product one other))

def the_square_presented (B R T L P Q H l₁ l₂ l₃ : Turns) : Int :=
  the_turns_action H + a_multiplier_term l₁ P B R + a_multiplier_term l₂ Q L T + a_multiplier_term l₃ H P (the_turns_conjugate Q)

theorem a_turn_less_itself_is_against_nothing (multiplier a : Turns) :
    one_turn_against_another multiplier (the_one_less_the_other a a) = 0 := by
  simp only [one_turn_against_another, the_one_less_the_other, Int.sub_self, Int.mul_zero, Int.add_zero]

--| Where the three handed in are what they say, it is the square's action.
theorem where_the_three_are_what_they_say_it_is_the_squares_action (B R T L l₁ l₂ l₃ : Turns) :
    the_square_presented B R T L (the_turns_product B R) (the_turns_product L T)
        (the_turns_product (the_turns_product B R) (the_turns_conjugate (the_turns_product L T))) l₁ l₂ l₃
      = the_turns_action (the_turns_holonomy B R T L) := by
  simp only [the_square_presented, a_multiplier_term, a_turn_less_itself_is_against_nothing, Int.add_zero,
    the_turns_holonomy, the_conjugate_reverses_the_product, the_product_is_associative]

--| A multiplier term with everything in it moved is a cubic in the number of the move, and these are its four parts.
def the_part_at_nothing (l a x y : Turns) : Int := a_multiplier_term l a x y
def the_part_at_one (l dl a da x dx y dy : Turns) : Int :=
  a_multiplier_term dl a x y
    + one_turn_against_another l (the_one_less_the_other da (set_together (the_turns_product dx y) (the_turns_product x dy)))
def the_part_at_two (l dl da x dx y dy : Turns) : Int :=
  one_turn_against_another dl (the_one_less_the_other da (set_together (the_turns_product dx y) (the_turns_product x dy)))
    - one_turn_against_another l (the_turns_product dx dy)
def the_part_at_three (dl dx dy : Turns) : Int := - one_turn_against_another dl (the_turns_product dx dy)

theorem a_multiplier_term_moved_is_a_cubic (l dl a da x dx y dy : Turns) (t : Int) :
    a_multiplier_term (the_varied_turns l dl t) (the_varied_turns a da t) (the_varied_turns x dx t) (the_varied_turns y dy t)
      = the_part_at_nothing l a x y + t * the_part_at_one l dl a da x dx y dy
        + t * t * the_part_at_two l dl da x dx y dy + t * t * t * the_part_at_three dl dx dy := by
  simp only [a_multiplier_term, the_part_at_nothing, the_part_at_one, the_part_at_two, the_part_at_three,
    the_product_is_linear_on_the_left, the_product_is_linear_on_the_right]
  generalize the_turns_product x y = p
  generalize the_turns_product x dy = q
  generalize the_turns_product dx y = r
  generalize the_turns_product dx dy = s
  simp only [one_turn_against_another, the_one_less_the_other, the_varied_turns, set_together, Int.mul_add, Int.add_mul,
    Int.mul_sub, Int.mul_neg]
  simp only [Int.mul_assoc, Int.mul_left_comm t]
  omega

--| THE SQUARE PRESENTED IS A CUBIC ALONG EVERY LINE.  Move all ten turns at once.  There are three numbers such that, at every
--| number of the move, the presented action is what it was, and the number, its square and its cube by those three.
theorem the_square_presented_is_a_cubic_along_every_line
    (B R T L P Q H l₁ l₂ l₃ dB dR dT dL dP dQ dH dl₁ dl₂ dl₃ : Turns) :
    ∃ first second third : Int, ∀ t : Int,
      the_square_presented (the_varied_turns B dB t) (the_varied_turns R dR t) (the_varied_turns T dT t)
          (the_varied_turns L dL t) (the_varied_turns P dP t) (the_varied_turns Q dQ t) (the_varied_turns H dH t)
          (the_varied_turns l₁ dl₁ t) (the_varied_turns l₂ dl₂ t) (the_varied_turns l₃ dl₃ t)
        = the_square_presented B R T L P Q H l₁ l₂ l₃ + t * first + t * t * second + t * t * t * third := by
  refine ⟨the_first_variation_of_the_turns H dH + the_part_at_one l₁ dl₁ P dP B dB R dR + the_part_at_one l₂ dl₂ Q dQ L dL T dT
      + the_part_at_one l₃ dl₃ H dH P dP (the_turns_conjugate Q) (the_turns_conjugate dQ),
    the_turns_action dH + the_part_at_two l₁ dl₁ dP B dB R dR + the_part_at_two l₂ dl₂ dQ L dL T dT
      + the_part_at_two l₃ dl₃ dH P dP (the_turns_conjugate Q) (the_turns_conjugate dQ),
    the_part_at_three dl₁ dB dR + the_part_at_three dl₂ dL dT + the_part_at_three dl₃ dP (the_turns_conjugate dQ), fun t => ?_⟩
  simp only [the_square_presented, the_conjugate_is_linear, a_multiplier_term_moved_is_a_cubic,
    the_turns_action_stops_at_second_order, the_part_at_nothing]
  simp only [Int.mul_add]
  omega

--| The multipliers hand back what they multiply: against every turn nothing, only where the one less the other is no turn.
theorem against_every_turn_nothing_is_no_turn (c : Turns)
    (nothing : ∀ X : Turns, one_turn_against_another X c = 0) : c = no_turn := by
  have h1 := nothing (1, 0, 0, 0)
  have h2 := nothing (0, 1, 0, 0)
  have h3 := nothing (0, 0, 1, 0)
  have h4 := nothing (0, 0, 0, 1)
  simp only [one_turn_against_another, Int.one_mul, Int.zero_mul, Int.add_zero, Int.zero_add] at h1 h2 h3 h4
  obtain ⟨a, b, c, d⟩ := c
  simp only at h1 h2 h3 h4
  simp only [no_turn, h1, h2, h3, h4]

end a_square_presented_in_the_third_degree

section a_cubic_whose_slope_is_the_residual

--| THE CRANK'S ACTION, IN ONE PLACE.  A cubic in the place, written to have three of Episode 12's residual as its slope.  Moved,
--| it is what it was, the move by three of the residual, the move squared by thirty-nine of the place less fifty-four, and the
--| move cubed by thirteen.  It stops there.  It was written to do this; any such residual has such a cubic.
def three_of_the_cranks_action (y : Int) : Int := 13 * y * y * y - 54 * y * y + 54 * y

theorem the_cranks_action_moved (y t : Int) :
    three_of_the_cranks_action (y + t)
      = three_of_the_cranks_action y + t * (3 * the_residual_at y) + t * t * (39 * y - 54) + t * t * t * 13 := by
  simp only [three_of_the_cranks_action, the_residual_at, Int.mul_add, Int.add_mul, Int.mul_sub]
  ac_nf; simp only [← Int.mul_assoc]; omega

end a_cubic_whose_slope_is_the_residual

--#print axioms the_common_action_moves_by_its_first_variation
--#print axioms what_multiplies_the_move_is_one_thing
--#print axioms one_turn_on_every_link_and_no_state_stands_still
--#print axioms the_square_presented_is_a_cubic_along_every_line
--#print axioms where_the_three_are_what_they_say_it_is_the_squares_action
--#print axioms the_cranks_action_moved
--#print axioms with_no_state_moved_what_is_carried_back_moves_by_the_current
--#print axioms the_common_action_is_left_by_a_turn_at_every_site

end Measurement
