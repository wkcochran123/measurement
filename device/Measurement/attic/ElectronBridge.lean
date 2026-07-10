import Measurement.Episode85
import Measurement.Agent.Positron

/- D2 -- THE TWO-ELECTRON BRIDGE (ep17-loop). BRIDGE, NOT MERGE.

The corpus carries the electron in two separate branches, and this file relates them
with a single named theorem -- it does NOT merge them; each stays in its own branch.

  * Episode52: `electron : Int := ... pairKick` -- the SECOND-VARIATION residual, a
    signed scalar, proved `= -1` (`electron_charge`). Charge as an Int.
  * Agent.Positron: `electron : Reading := fun _ => true` -- the ALL-FUNGE reading,
    pure matter, the distance-0 corner. Charge as a bit-vector, read through the gauge.

THE HONEST SHAPE (graded off the code -- the sketch "popcount = charge" is NOT the
truth). popcount / positronCount are Nats (>= 0); the Int charge is -1: they cannot be
literally equal. Worse for a naive numeric bridge: the all-funge electron's funge count
is POSITIVE (|Gate.all| funges, 0 positrons), and `orientationOfSign` of a positive
count would read POSITRON, not electron -- so there is NO numeric identity between the
two, and forcing one would invert the sign. The two branches use ORTHOGONAL invariants:
the Int signs the SECOND VARIATION (negative = matter), the bit-vector counts the
POSITRON DEVIATION (zero = pure matter). What IS true, and decidable, is that both
invariants CLASSIFY the object as the electron:

  * the Int charge (-1) reads as `Orientation.electron` through the sign gate
    (`orientationOfSign`: negative -> electron);
  * the bit-vector electron carries ZERO positrons (`positronCount electron electron
    = 0`) -- pure matter, the electron.

The bridge is the shared CLASSIFICATION, one side by sign, the other by count -- a
proved agreement, not a forced number. -/

namespace Measurement

/-- The Episode52 Int charge electron (`= -1`) reads as the electron orientation through
the sign gate: negative delta-squared is matter. -/
theorem intCharge_reads_electron :
    orientationOfSign electron = some Orientation.electron := by decide

/-- The Agent.Positron bit-vector electron (all-funge) carries zero positrons -- pure
matter, the electron read through the gauge. -/
theorem bitvector_electron_pure_matter :
    Agent.positronCount Agent.electron Agent.electron = 0 := by decide

/-- D2 THE BRIDGE (bridge, not merge): the two electron representations name one
particle. The Episode52 Int charge classifies as the electron by its NEGATIVE SIGN; the
Agent.Positron bit-vector electron classifies as the electron by its ZERO POSITRON
COUNT. Both are the electron -- tied by the shared classification, one side by sign, the
other by count. This is NOT `popcount = charge` (a Nat cannot equal Int -1); it is the
honest agreement the code actually carries. The two branches stay separate; this theorem
is the only tie. -/
theorem two_electrons_are_one_particle :
    orientationOfSign electron = some Orientation.electron
    ∧ Agent.positronCount Agent.electron Agent.electron = 0 :=
  ⟨intCharge_reads_electron, bitvector_electron_pure_matter⟩

end Measurement
