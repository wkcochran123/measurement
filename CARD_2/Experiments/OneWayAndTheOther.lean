/-
One way, and then the other.

This file stands beside the device and is built apart: `lake build Experiments.OneWayAndTheOther`.  Nothing in
`Measurement` imports it.  It defines no inductive, and it does not change the device.

One theorem in the built episodes bills `Classical.choice`: `compatibility_form` in Episode 12, an if-and-only-if
between two equations, closed by the arithmetic tactic in one step, and used by nothing.  Here is the same statement,
word for word, with the same first three lines of proof, and then proved one direction at a time.  It bills
`propext` and `Quot.sound` and no choice.

So the mathematics of that statement never needed choice.  The bill came from handing the tactic the two directions
joined as one.  The author's (declared): the theorem is a proof, joined to a proof; the daisy is the one classical
axiom the prover has, read as a call with the current continuation; and fixing the bill in the device is the knower's
to decide.  This file does not fix it.  It shows that it can be fixed.
-/
import Measurement.Episode13

namespace Measurement
open readers_interpretation_of_the_experience readers_experience the_representation

theorem the_same_statement_one_way_and_then_the_other (N D : Nat) (h : D ≤ N) :
    (readers_experience.the_macguffin * ((N - D) * (N - D)) = the_dimensions_of_universe * (N * N)) ↔
    (bent_card * (N * N) + readers_experience.the_macguffin * (D * D)
      = the_basis.the_reading.length * readers_experience.the_macguffin * (N * D)) := by
  have e := sub_sq N D h
  rw [show readers_experience.the_macguffin = 18 from rfl, show the_dimensions_of_universe = 5 from rfl,
      show bent_card = 13 from rfl, show the_basis.the_reading.length = 2 from rfl]
  constructor
  · intro one_way; omega
  · intro the_other_way; omega

--#print axioms compatibility_form
--#print axioms the_same_statement_one_way_and_then_the_other

end Measurement
