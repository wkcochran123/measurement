-- TheDepthLadder.lean
--
-- WHAT THE DEVICE ALREADY KNOWS, exhibited rather than described.
--
-- Episode 10 takes its crossing at one bracket depth and prints the reciprocal
-- there.  That depth is a REAL parameter -- refine it and the crossing moves,
-- because the crossing comes through a floor -- so the printed reading is
-- depth-relative.  This leaf runs the SAME construction at increasing depth
-- and prints what comes back, so the depth-relativity is a reading anyone can
-- regenerate instead of a claim in a message.
--
-- NOTHING HERE CHANGES THE STORY'S READOUT.  Episode 10 still reads at its own
-- depth and prints exactly what it printed before; this file only exhibits the
-- ladder alongside it.  What depth the device SHOULD publish at is a
-- whole-artifact question, not a leaf's to decide, and this leaf decides
-- nothing.
--
-- BLIND, in the file's own habit: no target is written here, no expected
-- value, no bracket, and no comparison to any recorded number.  The readings
-- are printed and whatever comes up comes up.  Reading them against the record
-- is the reader's business and the gate's, not this file's.

import Measurement.Episode10

namespace Measurement.TheDepthLadder

/-- The scale at a given depth: ten to the depth, the same shape Episode 10
uses at its own. -/
def scaleAt (d : Nat) : Nat := 10 ^ d

/-- The crossing at a given depth, by the same proven integer square root the
story uses -- `√(C/T)`, scaled.  No reals, nothing imported. -/
def crossingAt (d : Nat) : Nat :=
  Measurement.FloorSqrt.floorSqrt (cardC * scaleAt d * scaleAt d / cardT)

/-- The reciprocal at a given depth, as an exact ratio of whole numbers: the
same `d*·R² / ((d*−1)·T)` the story forms, at this depth's scale. -/
def ratioAt (d : Nat) : Int × Int :=
  ((crossingAt d * cardR * cardR : Nat), ((crossingAt d - scaleAt d) * cardT : Nat))

/-- The depths this ladder walks. -/
def theDepths : List Nat := [9, 12, 15, 18, 21, 24]

#eval ("the crossing, by depth", theDepths.map crossingAt)
#eval ("the reading, by depth", theDepths.map (fun d => decimalOf (ratioAt d) 18))

/-- The truncated-subtraction hazard, checked at every depth the ladder walks
and not only at the story's own: the scale never exceeds the crossing, so no
denominator here is a silently truncated zero. -/
theorem no_depth_truncates :
    theDepths.all (fun d => decide (scaleAt d ≤ crossingAt d)) = true := by decide

end Measurement.TheDepthLadder

#print axioms Measurement.TheDepthLadder.no_depth_truncates
