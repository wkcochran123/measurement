import Measurement.Agent.Positron

namespace Measurement

/-
__EPISODE 88__ (fixed): _Matter and antimatter, read THROUGH THE GAUGE_

The matter and antimatter counts are no longer the δ²-derived orientation tallies (`matterCount` /
`antimatterCount` over `flatEvents` -- reading the device by re-deriving its arithmetic, the
continuity).  They are read off the GAUGE: matter is the gates that funge, antimatter is the gates
that tange.  To read the device you call the gates.

  matter    = matterReading  electron number   -- the funged gates
  antimatter = positronCount  electron number   -- the tanged gates

The two tally the whole gauge -- the pigeonhole, no continuity.
-/

open Agent

/-- THE MATTER READING, off the gauge: the gates the superconducting pair funges (35 of 36). -/
theorem matter_off_the_gauge :
    matterReading electron superconductingPair = 35 := by decide

/-- THE ANTIMATTER READING, off the gauge: the gates the pair tanges -- one, at MAGNITUDE
(`whelmed?`). -/
theorem antimatter_off_the_gauge :
    positronCount electron superconductingPair = 1 := by decide

/-- The native pure pair: all matter, no antimatter -- read off the gauge. -/
theorem native_pure_matter_off_the_gauge :
    positronCount electron electron = 0 := by decide

/-- Matter and antimatter together are the whole gauge: every gate is one or the other.  No δ², no
limit, no rung left over. -/
theorem split_tallies_the_gauge :
    matterReading electron superconductingPair + positronCount electron superconductingPair
      = Gate.all.length := by decide

end Measurement
