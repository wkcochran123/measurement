import Measurement.Episode83

set_option maxHeartbeats 4000000

namespace Measurement

/-
__EPISODE 84__: _Positron Detection as a Holonomy Sign_

OPERATOR / HONESTY GATE (inherited from Episodes 82-83, non-negotiable):
This episode reads positron detection as the SIGN of a gauge HOLONOMY.  It does NOT claim a real
Aharonov-Bohm measurement, a real SQUID/Cooper-pair interferometer, real QED, or real antimatter;
WHICH sign counts as "positron" is the convention fixed by the baseline/flux (Episode73's tally),
not derived here.  Claim ceiling: "a positron is read as the POSITIVE sign of the gauge holonomy a
pair accumulates around a loop; that holonomy is the both-legs commutator residue (zero on any
single-leg/open path) and is positive only over an asymmetric flux; MEASURED, not derived."

----
The HOLONOMY FACE of Episode83's trial (the ANNIHILATION face lives in the experiments,
`Experiments/ThePositronAnnihilationEffect`).  Episode82 located the single `Quot.sound`; Episode83
ran the pairwise SIGN trial and showed the flip is baseline-relative.  Here the SAME delta-squared
is read as a HOLONOMY -- the signed residue a pair accumulates transported around a gauge loop:

  * delta-squared = `secondVariation` = `mixedCubicCoupling` (definitionally, Episode31) = the
    gauge commutator residue (Episode64).  A commutator residue around a loop IS a holonomy.

  * THE HOLONOMY SIGNATURE: the residue is ZERO on any OPEN path (one leg held at the loop's own
    `middleRight` -- a single-coordinate kick; `mixedCoupling_needs_the_pair`, Episode52) and
    NONZERO only around the genuine pair-LOOP (both legs moved -- the commutator).  That
    open-vs-loop split is exactly what makes it a holonomy, not a pointwise reading.

  * DETECTION: a positron detector reads the SIGN of the holonomy.  It fires (+) only over a
    TILTED/asymmetric flux; over a flat/symmetric flux the SAME loop reads an electron (-).
    Detection is FRAME-RELATIVE (the convention of Episode83's flip; Chapter 17's "doesn't matter").

All axiom-free over the trial (`decide` over the concrete finite paths; the signed values cite
Episode83's `baseline_relative_flip`).
-/

open CubicGaugeVariation

/-- THE HOLONOMY: the signed residue a pair `v` accumulates around the gauge loop `path` is its
delta-squared (`pairDelta2` = `secondVariation` = `mixedCubicCoupling`, the commutator residue of
Episode64).  The path is the connection/flux; the pair is the loop. -/
def holonomy (path : CubicGaugePath0) (v : CubicGaugeVariation0) : Int :=
  pairDelta2 path v

/-- A positron detector reads the SIGN of the holonomy: positive ⇒ positron. -/
def detectsPositron (path : CubicGaugePath0) (v : CubicGaugeVariation0) : Prop :=
  orientationOfSign (holonomy path v) = some Orientation.positron

-- ----------------------------------------------------------------
-- THE HOLONOMY SIGNATURE: trivial on the open path, charged around the loop.
-- ----------------------------------------------------------------

/-- The OPEN path carries no holonomy.  `pairVariation node2 node1` over `tiltedPath` moves only
the LEFT leg (the right slip `node1` already equals `tiltedPath.middleRight`): a single-coordinate
kick, read as zero -- the residue is invisible to one-leg instruments
(`mixedCoupling_needs_the_pair_left`, Episode52). -/
theorem holonomy_open_is_trivial :
    holonomy tiltedPath (pairVariation node2 node1) = 0 := by decide

/-- The LOOP carries a charged holonomy.  `pairVariation node1 node2` moves BOTH legs -- the genuine
pair, the commutator -- and reads ±1: `+1` (positron) over the tilted flux, `-1` (electron) over the
flat flux.  Cites Episode83's `baseline_relative_flip`. -/
theorem holonomy_loop_is_charged :
    holonomy tiltedPath (pairVariation node1 node2) = 1
      ∧ holonomy flatPath (pairVariation node1 node2) = -1 :=
  ⟨baseline_relative_flip.2, baseline_relative_flip.1⟩

-- ----------------------------------------------------------------
-- DETECTION: the sign of the holonomy, frame-relative.
-- ----------------------------------------------------------------

/-- The detector reads a POSITRON over the tilted (asymmetric) flux. -/
theorem detects_positron_over_tilt :
    detectsPositron tiltedPath (pairVariation node1 node2) := by
  unfold detectsPositron holonomy; decide

/-- ...and reads NO positron over the flat (symmetric) flux -- the same loop is an electron there. -/
theorem no_positron_over_flat :
    ¬ detectsPositron flatPath (pairVariation node1 node2) := by
  unfold detectsPositron holonomy; decide

/-- POSITRON DETECTION IS FRAME-RELATIVE: the SAME loop reads opposite holonomy signs over the two
baselines.  Which sign is "positron" is the flux convention, not an absolute. -/
theorem detection_is_frame_relative :
    holonomy flatPath (pairVariation node1 node2)
      = - holonomy tiltedPath (pairVariation node1 node2) := by decide

-- ----------------------------------------------------------------
-- The standing record.
-- ----------------------------------------------------------------

#eval holonomy flatPath (pairVariation node1 node2)     -- expect: -1   (electron, flat flux)
#eval holonomy tiltedPath (pairVariation node1 node2)   -- expect:  1   (positron, tilted flux)
#eval holonomy tiltedPath (pairVariation node2 node1)   -- expect:  0   (open path, no holonomy)
#print axioms detects_positron_over_tilt
#print axioms holonomy_open_is_trivial

end Measurement
