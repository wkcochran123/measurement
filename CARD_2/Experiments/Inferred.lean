/-
Eighteen and five, inferred.

This file stands beside the device and is built apart: `lake build Experiments.Inferred`.  Nothing in `Measurement`
imports it.  It defines no inductive.

The device reaches eighteen and five twice by counting something written: the lengths of Episode 8's tapes, and what
the lowest processes of the last machine hold.  Experiment 017 found those to be two constructions, neither built
from the other.  The author's, 21 November 2026 (declared): one more trip is needed, wholly inferred, the contravariant
argument against the covariant clock, the carrier of an arm turned over and the other way round; and, shown that the
readings leave only one answer, "the fact that this is the only way to do this step means that this is an unavoidable
inference."

Here is that trip.  Nothing is counted.  Three things are taken as read.  The shape: three arms carry one weight and
one arm another, which Episode 13 proves of any two truth values with an order.  The stay: the table's trace.  The
round trip: the product of the two crossings, which is all the clock keeps of them.  From those the two weights are
eighteen and five and nothing else.  Why the trace is thirty-six and the round trip ninety is not shown here.
-/
import Measurement.Episode13

namespace Measurement
open readers_experience

--| THE CLOCK ALONE DOES NOT GIVE THEM.  Eighteen and five, nine and ten, two and forty-five, one and ninety: one round trip.
theorem one_round_trip_and_many_pairs : (18 : Int) * 5 = 90 ∧ (9 : Int) * 10 = 90 ∧ (2 : Int) * 45 = 90 ∧ (1 : Int) * 90 = 90 := by
  decide

--| THE TABLE OF THREE AND ONE.  A weight on the three arms that can click and another on the one that cannot.
def the_table_of_three_and_one (on_the_three on_the_one : Int) : Table :=
  fun a b => if the_arm_stores_a_fact_that_can_click a b then on_the_three else on_the_one

--| The device's table is one of these.
theorem the_devices_table_is_a_table_of_three_and_one :
    ∀ a b, the_full_table a b = the_table_of_three_and_one (the_arm_weight true true) (the_arm_weight true false) a b := by
  intro a b; cases a <;> cases b <;> rfl

--| Its trace is twice the weight on the three, and its round trip is the one weight by the other.
theorem the_trace_and_the_round_trip_of_three_and_one (on_the_three on_the_one : Int) :
    the_table_trace (the_table_of_three_and_one on_the_three on_the_one) = 2 * on_the_three
      ∧ the_table_of_three_and_one on_the_three on_the_one true false
          * the_table_of_three_and_one on_the_three on_the_one false true = on_the_one * on_the_three := by
  refine ⟨?_, rfl⟩
  show on_the_three + on_the_three = 2 * on_the_three
  omega

--| THE INFERENCE.  Any table of three and one that has the device's trace and the device's round trip has the device's two
--| weights.  There is no other.
theorem the_stay_and_the_round_trip_leave_one_pair_of_weights (on_the_three on_the_one : Int)
    (the_stay : the_table_trace (the_table_of_three_and_one on_the_three on_the_one) = the_table_trace the_full_table)
    (the_trip : the_table_of_three_and_one on_the_three on_the_one true false
        * the_table_of_three_and_one on_the_three on_the_one false true = the_round_trip) :
    on_the_three = 18 ∧ on_the_one = 5 := by
  have trace := (the_trace_and_the_round_trip_of_three_and_one on_the_three on_the_one).1
  have trip := (the_trace_and_the_round_trip_of_three_and_one on_the_three on_the_one).2
  rw [trace, show the_table_trace the_full_table = 36 from rfl] at the_stay
  rw [trip, the_round_trip_is_ninety] at the_trip
  have three : on_the_three = 18 := by omega
  subst three
  exact ⟨rfl, by omega⟩

--| And they are the device's own.
theorem the_inferred_weights_are_the_devices :
    ((18 : Int) = (the_arm_weight true true : Int)) ∧ ((5 : Int) = (the_arm_weight true false : Int)) := ⟨rfl, rfl⟩

--| THE CARRIER OF AN ARM TURNED OVER, AND THE OTHER WAY ROUND.  On the two crossings the table reads five and eighteen.  They
--| are the only two entries the clock keeps, and the five is on one of them and nowhere else.
theorem the_two_crossings_read_five_and_eighteen :
    the_full_table true false = 5 ∧ the_full_table false true = 18
      ∧ the_clock_table true false = 5 ∧ the_clock_table false true = 18
      ∧ the_clock_table true true = 0 ∧ the_clock_table false false = 0 := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

--#print axioms the_stay_and_the_round_trip_leave_one_pair_of_weights
--#print axioms the_devices_table_is_a_table_of_three_and_one

end Measurement
