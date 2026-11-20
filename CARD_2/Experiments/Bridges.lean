/-
The bridges.

This file stands beside the device and is built apart: `lake build Experiments.Bridges`.  Nothing in `Measurement`
imports it.  It defines no inductive.  It is the part that could be made at once of a reader's list of bridges between
the things left open, 19 November 2026: an obstruction to a state that stands still; twenty numbers that fix a
curvature on the pairs of arms; the knower's four bits read back out of the word; what a hexagon of the pairs can and
cannot keep; what one state set beside another reads; and a table that will not be raised twice.

Each is on the device's own turns, tables, pairs and Areas.  What is supplied here and is not the device's is said
where it stands.
-/
import Experiments.TheWord

namespace Measurement
open readers_experience the_area readers_interpretation_of_the_experience

--| THE OBSTRUCTION.  Where the state stands still at a site, the link carries the far state to twice the near one, owed.
theorem where_the_state_stands_still_the_link_carries_the_far_state_to_twice_the_near_owed {n : Nat}
    (state : Site4 n → Turns) (U : Torus4 n) (way : Direction) (x : Site4 n)
    (still : the_state_stands_still_at_the_site state U way x) :
    the_turns_product (U way x) (state (the_step way x))
      = (-2 * (state x).1, -2 * (state x).2.1, -2 * (state x).2.2.1, -2 * (state x).2.2.2) := by
  have h1 := still (1, 0, 0, 0)
  have h2 := still (0, 1, 0, 0)
  have h3 := still (0, 0, 1, 0)
  have h4 := still (0, 0, 0, 1)
  simp only [what_multiplies_the_move_of_the_state] at h1 h2 h3 h4
  generalize the_turns_product (U way x) (state (the_step way x)) = far at *
  generalize state x = near at *
  obtain ⟨f1, f2, f3, f4⟩ := far
  obtain ⟨s1, s2, s3, s4⟩ := near
  simp only [the_turns_product, the_turns_conjugate, Int.mul_zero, Int.zero_mul, Int.mul_one, Int.one_mul, Int.neg_zero,
    Int.sub_zero, Int.add_zero, Int.zero_add, Int.neg_mul, Int.sub_neg] at h1 h2 h3 h4
  simp only [Prod.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

theorem twice_owed_is_four_of_the_norm (q : Turns) :
    the_turns_norm (-2 * q.1, -2 * q.2.1, -2 * q.2.2.1, -2 * q.2.2.2) = 4 * the_turns_norm q := by
  simp only [the_turns_norm]; ac_nf; omega

--| So the norms: the link's by the far state's is four of the near state's.
theorem the_links_norm_by_the_far_states_is_four_of_the_near_states {n : Nat}
    (state : Site4 n → Turns) (U : Torus4 n) (way : Direction) (x : Site4 n)
    (still : the_state_stands_still_at_the_site state U way x) :
    the_turns_norm (U way x) * the_turns_norm (state (the_step way x)) = 4 * the_turns_norm (state x) := by
  rw [← the_norm_is_multiplicative,
    where_the_state_stands_still_the_link_carries_the_far_state_to_twice_the_near_owed state U way x still,
    twice_owed_is_four_of_the_norm]

theorem a_square_is_not_owed (a : Int) : 0 ≤ a * a := by
  rcases Int.le_total 0 a with h | h
  · exact Int.mul_nonneg h h
  · have := Int.mul_nonneg (Int.neg_nonneg_of_nonpos h) (Int.neg_nonneg_of_nonpos h)
    rwa [Int.neg_mul_neg] at this

theorem a_norm_is_not_owed (q : Turns) : 0 ≤ the_turns_norm q := by
  have a := a_square_is_not_owed q.1
  have b := a_square_is_not_owed q.2.1
  have c := a_square_is_not_owed q.2.2.1
  have d := a_square_is_not_owed q.2.2.2
  simp only [the_turns_norm]; omega

theorem a_turn_of_no_norm_is_nothing (q : Turns) (nothing : the_turns_norm q = 0) : q = (0, 0, 0, 0) := by
  obtain ⟨a, b, c, d⟩ := q
  simp only [the_turns_norm] at nothing
  have ha := a_square_is_not_owed a
  have hb := a_square_is_not_owed b
  have hc := a_square_is_not_owed c
  have hd := a_square_is_not_owed d
  have a0 : a * a = 0 := by omega
  have b0 : b * b = 0 := by omega
  have c0 : c * c = 0 := by omega
  have d0 : d * d = 0 := by omega
  have a1 : a = 0 := (Int.mul_eq_zero.mp a0).elim id id
  have b1 : b = 0 := (Int.mul_eq_zero.mp b0).elim id id
  have c1 : c = 0 := (Int.mul_eq_zero.mp c0).elim id id
  have d1 : d = 0 := (Int.mul_eq_zero.mp d0).elim id id
  subst a1 b1 c1 d1; rfl

--| So many steps one way.
def so_many_steps {n : Nat} (way : Direction) : Nat → Site4 n → Site4 n
  | 0, x => x
  | steps + 1, x => the_step way (so_many_steps way steps x)

--| Along links of length one, where the state stands still at every site: after any steps at all, the state's norm is at
--| least four of what it was.
theorem along_links_of_length_one_the_norm_is_at_least_four_times {n : Nat}
    (state : Site4 n → Turns) (U : Torus4 n) (way : Direction)
    (still : ∀ y, the_state_stands_still_at_the_site state U way y)
    (of_length_one : ∀ y, the_turns_norm (U way y) = 1) (x : Site4 n) :
    ∀ steps, 4 * the_turns_norm (state x) ≤ the_turns_norm (state (so_many_steps way (steps + 1) x))
  | 0 => by
      have one := the_links_norm_by_the_far_states_is_four_of_the_near_states state U way x (still x)
      rw [of_length_one x, Int.one_mul] at one
      show _ ≤ the_turns_norm (state (the_step way x))
      omega
  | steps + 1 => by
      have before := along_links_of_length_one_the_norm_is_at_least_four_times state U way still of_length_one x steps
      have one := the_links_norm_by_the_far_states_is_four_of_the_near_states state U way
        (so_many_steps way (steps + 1) x) (still _)
      rw [of_length_one _, Int.one_mul] at one
      have not_owed := a_norm_is_not_owed (state x)
      show _ ≤ the_turns_norm (state (the_step way (so_many_steps way (steps + 1) x)))
      omega

--| THE OBSTRUCTION, WHOLE.  Around any walk one way that comes back, along links of length one: a state that stands still
--| at every site is no state there.
theorem around_a_walk_that_comes_back_no_state_stands_still {n : Nat}
    (state : Site4 n → Turns) (U : Torus4 n) (way : Direction)
    (still : ∀ y, the_state_stands_still_at_the_site state U way y)
    (of_length_one : ∀ y, the_turns_norm (U way y) = 1) (x : Site4 n) (steps : Nat)
    (it_comes_back : so_many_steps way (steps + 1) x = x) :
    state x = (0, 0, 0, 0) := by
  have grown := along_links_of_length_one_the_norm_is_at_least_four_times state U way still of_length_one x steps
  rw [it_comes_back] at grown
  have not_owed := a_norm_is_not_owed (state x)
  exact a_turn_of_no_norm_is_nothing _ (by omega)

--| WHERE THE LENGTH IS NOT ONE.  Put the whole turn of two, owed, on every link, and the whole turn of one at every site.
--| That state is not nothing, and it stands still at every site.  So the length of the links is doing the work above.
def two_owed_on_every_link {n : Nat} : Torus4 n := fun _ _ => the_whole_turn (-2)
def one_at_every_site {n : Nat} : Site4 n → Turns := fun _ => the_whole_turn 1

theorem on_links_of_two_owed_a_state_stands_still {n : Nat} (way : Direction) (x : Site4 n) :
    the_state_stands_still_at_the_site (one_at_every_site (n := n)) two_owed_on_every_link way x := by
  intro Y
  simp [what_multiplies_the_move_of_the_state, one_at_every_site, two_owed_on_every_link, the_whole_turn,
    the_turns_product, the_turns_conjugate]
  omega

--| And there the link's equation is not met.  With no squares counted, what multiplies the link's move is the current,
--| and the current against a whole move is the move.
theorem and_there_the_links_equation_is_not_met {n : Nat} (way : Direction) (x : Site4 n) :
    what_multiplies_the_move_of_the_squares (two_owed_on_every_link (n := n)) way x (the_whole_turn 1) []
        + (the_current_in_the_link (one_at_every_site (n := n)) way x (the_whole_turn 1)).1 = 1 := by
  simp [what_multiplies_the_move_of_the_squares, the_current_in_the_link, one_at_every_site, the_whole_turn,
    the_turns_product, the_turns_conjugate]

--| TWENTY NUMBERS.  A curvature on the six pairs of arms is a table of a pair by a pair: the same when the pairs change
--| places, and bound once, among the three that share no arm.  Number the pairs nought to five as the device lists them.
--| Taken once there are twenty-one places; leave out the one that is bound, and twenty are left.
def the_twenty_places : List (Nat × Nat) :=
  ((List.range 6).flatMap fun this => (List.range 6).map fun that => (this, that)).filter
    fun place => decide (place.1 ≤ place.2) && place != (2, 3)

theorem there_are_twenty : the_twenty_places.length = 20 := by decide

def changes_places_freely (table : Nat → Nat → Int) : Prop := ∀ this that, table this that = table that this
def is_bound_once (table : Nat → Nat → Int) : Prop := table 2 3 = table 1 4 - table 0 5

--| They are free: whatever twenty numbers are wanted, there is such a table that holds them.
def the_table_built_from (wanted : Nat → Nat → Int) : Nat → Nat → Int := fun this that =>
  if (min this that, max this that) = (2, 3) then wanted 1 4 - wanted 0 5 else wanted (min this that) (max this that)

theorem the_twenty_are_free (wanted : Nat → Nat → Int) :
    changes_places_freely (the_table_built_from wanted) ∧ is_bound_once (the_table_built_from wanted)
      ∧ ∀ place ∈ the_twenty_places, the_table_built_from wanted place.1 place.2 = wanted place.1 place.2 := by
  refine ⟨fun this that => ?_, ?_, ?_⟩
  · simp only [the_table_built_from, Nat.min_comm this that, Nat.max_comm this that]
  · simp [is_bound_once, the_table_built_from]
  · intro place among
    simp only [the_twenty_places, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at among
    obtain ⟨_, in_order, not_the_bound⟩ := among
    simp only [the_table_built_from, Nat.min_eq_left in_order, Nat.max_eq_right in_order]
    rw [if_neg not_the_bound]

--| And they are all: two such tables that agree on the twenty agree everywhere on the six by six.
theorem the_twenty_are_all (one other : Nat → Nat → Int)
    (one_changes : changes_places_freely one) (other_changes : changes_places_freely other)
    (one_bound : is_bound_once one) (other_bound : is_bound_once other)
    (agree : ∀ place ∈ the_twenty_places, one place.1 place.2 = other place.1 place.2) :
    ∀ this that, this < 6 → that < 6 → one this that = other this that := by
  have in_order : ∀ low high, low ≤ high → high < 6 → one low high = other low high := by
    intro low high ordered small
    by_cases the_bound : (low, high) = (2, 3)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj the_bound
      rw [one_bound, other_bound, agree (1, 4) (by decide), agree (0, 5) (by decide)]
    · apply agree (low, high)
      simp only [the_twenty_places, List.mem_filter, List.mem_flatMap, List.mem_map, List.mem_range, Bool.and_eq_true,
        decide_eq_true_eq, bne_iff_ne, ne_eq]
      exact ⟨⟨low, by omega, high, small, rfl⟩, ordered, the_bound⟩
  intro this that this_small that_small
  rcases Nat.le_total this that with ordered | ordered
  · exact in_order this that ordered that_small
  · rw [one_changes this that, other_changes this that]; exact in_order that this ordered this_small

--| THE WORD, READ BACK.  The knower's four bits went into the word as four cells.  Read the word's clicks, and read the
--| four places where a cell that says no can stand: the bits come back, for every one of the sixteen.
def the_bits_read_back (word : Area) : Bool × Bool × Bool × Bool :=
  let clicks := word.riemann_integrate.map FACT.bit
  (clicks.getD 8 true, clicks.getD 17 true, clicks.getD 26 true, clicks.getD 27 true)

theorem the_knowers_bits_come_back_out_of_the_word :
    ∀ a c b the_fourth : Bool, the_bits_read_back (the_word a c b the_fourth) = (a, c, b, the_fourth) := by decide

--| THE HEXAGON, AND ITS LIMIT.  Every pair of arms shares an arm with four others.  Round a hexagon a place has two
--| neighbours.  So no way round keeps every sharing as standing next to; the way round the device has keeps one walk of
--| six, each sharing with the next, and the parity.
theorem every_pair_shares_an_arm_with_four_others :
    the_pairs_of_arms.map (fun this => (the_pairs_of_arms.filter fun that => this != that && share_an_arm this that).length)
      = [4, 4, 4, 4, 4, 4] := by decide

--| ONE STATE SET BESIDE ANOTHER.  The norm of two turns together is each one's norm and twice the whole part of the one
--| turned over by the other.  Nothing here says what a norm is the chance of.
theorem together_is_each_and_twice_the_one_against_the_other (p q : Turns) :
    the_turns_norm (p.1 + q.1, p.2.1 + q.2.1, p.2.2.1 + q.2.2.1, p.2.2.2 + q.2.2.2)
      = the_turns_norm p + the_turns_norm q + 2 * (the_turns_product (the_turns_conjugate p) q).1 := by
  simp only [the_turns_norm, the_turns_product, the_turns_conjugate, Int.add_mul, Int.mul_add, Int.neg_mul]
  ac_nf; omega

--| NOT TWICE.  This is supplied, and is not found in the device: a table on the two coins that raises false to true and
--| has nothing else in it, and the same turned over, which lowers.  Raise twice and there is nothing.  Lower twice and
--| there is nothing.  And raise then lower, beside lower then raise, is every coin left as it was.
def the_table_that_raises : Table := fun a b => if a = true ∧ b = false then 1 else 0
def the_table_that_lowers : Table := fun a b => the_table_that_raises b a

theorem not_twice :
    (∀ a b, the_table_product the_table_that_raises the_table_that_raises a b = 0)
      ∧ (∀ a b, the_table_product the_table_that_lowers the_table_that_lowers a b = 0)
      ∧ (∀ a b, the_table_product the_table_that_raises the_table_that_lowers a b
          + the_table_product the_table_that_lowers the_table_that_raises a b = if a = b then 1 else 0) := by decide

end Measurement
