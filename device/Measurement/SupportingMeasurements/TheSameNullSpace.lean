-- TheSameNullSpace.lean
--
-- Built on the operator's GO (2026-08-23): "all theoretical descriptions of
-- the electron have the same null space -- the same null space IN THE DEVICE,
-- anyway", and "read the code, YOU_the_READER needs to describe this."
--
-- So this reads the code rather than the slogan.  Episode 4's reader structure
-- carries `you_the_reader`, a floor `TRUE := .zero`, an output rung
-- `a_constant`, and the certificate `the_constant_is_at_least_true : TRUE <=
-- a_constant`.  Whatever rung a description lands on, it is admitted by being
-- ABOVE THE SAME FLOOR.  That shared floor is the null space this leaf
-- exhibits, and the exhibit is two decided facts about `Bullshit.le`.
--
-- WHAT IS CLAIMED: the device's own descriptions share a null direction --
-- the ordering that admits them cannot separate them by rung, only by ledger.
-- WHAT IS NOT CLAIMED: anything about the world's theories of the electron.
-- The operator narrowed that himself in his second line and the narrowing is
-- kept here.  No physics name appears in any statement below.

import Measurement.Episode4

namespace Measurement.TheSameNullSpace

/-- THE FLOOR ADMITS EVERY RUNG, and it does so for free.  Whatever a
description reports -- a threshold reading or a full response, carrying any
payload at all -- the origin sits below it, and the witness is `trivial`
because `Bullshit.le` sends `.zero` against anything to `True`.  This is why
`the_constant_is_at_least_true` can be discharged for every instance no matter
which rung it lands on: the certificate says nothing about the rung. -/
theorem the_floor_admits_every_threshold
    (l f : Fact) (n : Number) (t1 t2 : CompilerTape) (b : Bullshit) :
    Bullshit.le (.zero l) (.one f n t1 t2 b) := trivial

theorem the_floor_admits_every_response
    (l f g : Fact) (p : Prop) (n1 n2 n3 : Number)
    (t1 t2 : CompilerTape) (b1 b2 : Bullshit) :
    Bullshit.le (.zero l) (.rest_call f g p n1 n2 n3 t1 t2 b1 b2) := trivial

/-- THE NULL DIRECTION, NAMED.  Against the floor, the rung carries no
information: the ordering's verdict is `True` for a threshold and `True` for a
response alike, so nothing about WHICH description was given survives the
comparison.  That is the sense in which every description has the same null
space here -- they are all admitted the same way, by the same floor, and the
admission does not distinguish them. -/
theorem the_rung_is_in_the_null_direction
    (l f : Fact) (n : Number) (t1 t2 : CompilerTape) (b : Bullshit)
    (g : Fact) (p : Prop) (n1 n2 n3 : Number) (b1 b2 : Bullshit) :
    Bullshit.le (.zero l) (.one f n t1 t2 b)
      ∧ Bullshit.le (.zero l) (.rest_call f g p n1 n2 n3 t1 t2 b1 b2) :=
  ⟨trivial, trivial⟩

/-- AND WHAT IS *NOT* IN THE NULL SPACE, which is what keeps the leaf from
being vacuous.  Two origins are NOT compared trivially: there the ordering
reads the LEDGER, and the verdict is an equality of truths.  So the floor is
blind to the rung and sighted about the ledger -- the null direction is exactly
one direction, not everything. -/
theorem the_ledger_is_not_in_the_null_direction (l l' : Fact) :
    Bullshit.le (.zero l) (.zero l') = (l.truth = l'.truth) := rfl

end Measurement.TheSameNullSpace

#print axioms Measurement.TheSameNullSpace.the_floor_admits_every_threshold
#print axioms Measurement.TheSameNullSpace.the_floor_admits_every_response
#print axioms Measurement.TheSameNullSpace.the_rung_is_in_the_null_direction
#print axioms Measurement.TheSameNullSpace.the_ledger_is_not_in_the_null_direction
