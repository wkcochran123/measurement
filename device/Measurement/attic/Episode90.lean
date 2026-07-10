import Measurement.Agent.Positron

namespace Measurement

/-
__EPISODE 90__ (fixed): _The Superconducting Pair -- read THROUGH THE GAUGE_

The pair is no longer read by re-deriving δ² arithmetic (the old `pairDelta2` reading -- the
continuity).  It is read by CALLING THE GATES (`Measurement.Agent`): each gate answers funge (matter)
or tange.  The superconducting pair funges every gate except MAGNITUDE, where `whelmed?` flips -- the
admitted positron.  Discrete: the pigeonhole, no continuity, every gate accounted for.

This re-exports the gauge reading at the episode level; the count itself lives in the light, episode-
free `Agent` subtree (the gauge), so the device reads itself without the δ² tar pit.
-/

open Agent

/-- The superconducting pair, read through the gauge, admits exactly ONE positron -- at MAGNITUDE,
where `whelmed?` flips. -/
theorem superconducting_pair_admits_one_positron :
    positronCount electron superconductingPair = 1 :=
  pair_admits_one_positron

/-- The pure native pair carries none -- matter all the way down. -/
theorem native_pair_pure_matter :
    positronCount electron electron = 0 :=
  Agent.native_pair_pure_matter

/-- Every gate is matter or positron: the pigeonhole closes, no rung left over. -/
theorem gauge_closes :
    matterReading electron superconductingPair + positronCount electron superconductingPair
      = Gate.all.length :=
  gauge_partition

#eval positronCount electron superconductingPair    -- 1, off the gauge

end Measurement
