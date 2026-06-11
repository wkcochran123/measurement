import Measurement.Episode45

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000
set_option allowUnsafeReducibility true

namespace Measurement

/-
__EPISODE 46__: _The Boundary Is a Build Artifact_

The localization of choice is not something we merely know; the build enforces
it.  Two mechanisms make the constructive/classical boundary mechanical:

1. `#eval`.  Lean will not run code that touches `Classical.choice` -- a
   successful evaluation is itself a certificate that the evaluated term, and
   everything it computes from, is choice-free.  The integrator runs and prints
   a number, so the entire gauge path (carrier, ladder base, EKG comparison,
   `coupledCubicDifference`) is constructive.

2. `#print axioms`.  It traverses the full dependency, proofs included, and
   lists the axioms used.  The constructive rungs list no `Classical.choice`;
   `rung3Inferred` lists it.  The needle is at `INFERRED_TRUE` -- reached only
   through `SAME`'s single classical decision `Classical.propDecidable (s ≠ Prop)`
   (the diagonal) -- and at no other rung.

Recall the structural half is also build-enforced: every constructive rung
(`rung3Counting … rung3Numeric`, `rung3Comparable`, the middle, `gaugeReading`)
is a plain `def`/`instance`.  Lean would reject any of them that used
`Classical.choice` in its data unless marked `noncomputable`; only
`rung3Inferred` needed that mark.

The `#eval`/`#print axioms` outputs below are the standing record.  Expected
results are noted inline.
-/

-- (1) The constructive path RUNS -- hence is choice-free.

-- Bulletproof: a pure-`Nat` residual that becomes 0.
#eval sampleResidual 0          -- expect: 1
#eval sampleResidual 7          -- expect: 0

-- The integrator itself: y = x reads 0 on-shell, the kicked path reads 2.
-- A successful run certifies the whole gauge path is constructive.
#eval identityGaugeReading  -- expect: 0
#eval kickedGaugeReading    -- expect: 2

-- (2) `#print axioms`: the constructive rungs are choice-free; the needle is
-- isolated at `rung3Inferred`.

-- Constructive rungs -- expect NO `Classical.choice`:
#print axioms gaugeReading        -- the integrator
#print axioms rung3Numeric         -- top of the constructive base
#print axioms rung3Comparable      -- COMPARABLE, grounded by the EKG
#print axioms sample_tendsToZero   -- Weierstrass by instantiation (Episode45)

-- The needle -- expect `Classical.choice` (via INFERRED_TRUE / SAME), and only
-- here:
#print axioms rung3Inferred

end Measurement
