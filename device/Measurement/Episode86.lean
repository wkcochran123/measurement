import Measurement.Agent.Positron

namespace Measurement

/-
__EPISODE 86__ (gauge): _The Funge Hypercube -- How Close to the Electron_

THE ELECTRON is the all-funge corner of the gauge: every gate reads matter.  A reading is a corner of
the hypercube {funge, tange}^36 -- one bit per gate, read THROUGH THE GATES (the reader's verdict), not
off δ²-flattened device Facts.  HOW CLOSE a reading is to the electron is the HYPERCUBE (Hamming)
DISTANCE to the all-funge corner: the count of tanges = the gates that flipped = the positron count.

The hypercube is no longer built on the flattened Facts of the old apparatus; it IS the gauge.  The
electron sits on its own corner at distance 0; a real reading -- the superconducting pair -- sits one
tange off the corner, at MAGNITUDE (where `whelmed?` flips).
-/

open Agent

/-- HYPERCUBE DISTANCE to the electron: the Hamming distance from a reading to the all-funge corner =
the gates that tange = the positron count. -/
def hypercubeDistance (number : Reading) : Nat := positronCount electron number

/-- How close to the electron: the gates that funge with it. -/
def electronCloseness (number : Reading) : Nat := matterReading electron number

/-- THE ELECTRON sits ON its own corner -- distance 0, the trivial reading. -/
theorem electron_is_trivial_distance : hypercubeDistance electron = 0 := by decide

/-- A REAL reading -- the superconducting pair -- sits one tange off the corner, at MAGNITUDE. -/
theorem pair_distance_is_one : hypercubeDistance superconductingPair = 1 := by decide

/-- ...and its closeness is the complement: 35 funged gates of 36. -/
theorem pair_closeness_is_thirtyfive : electronCloseness superconductingPair = 35 := by decide

/-- A reading IS the electron exactly when its hypercube distance is zero (no tanges). -/
def isElectron (number : Reading) : Prop := hypercubeDistance number = 0

theorem electron_reads_electron : isElectron electron := by
  unfold isElectron; decide
theorem pair_is_not_electron : ¬ isElectron superconductingPair := by
  unfold isElectron; decide

#eval hypercubeDistance electron              -- 0  (the electron, on its own corner)
#eval hypercubeDistance superconductingPair    -- 1  (a real distance off the corner, at MAGNITUDE)

end Measurement
