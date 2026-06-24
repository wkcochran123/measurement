import Measurement.Agent.Positron

namespace Measurement

/-
__EPISODE 87__ (gauge): _The Funge Counter -- the machine that counts the funges_

Counting funges is the name of the game.  Read THROUGH THE GATES: a FUNGE is a gate that reads matter
(the reader's verdict holds in order); a TANGE is a gate that flipped (the reading inverts) -- a
positron.

THE TANGES TURN THE CRANK: the machine takes one step per tange while the funges accumulate.  The
MEASUREMENT is the funge count = the gauge's matter reading.  THE CRANK count is the tange count = the
positron count.  THE ELECTRON is the gauge the crank never turns: all funges, zero tanges.
-/

open Agent

/-- THE FUNGE COUNT (the measurement): the gates that funge against the electron = the matter reading. -/
def gaugeFungeCount (number : Reading) : Nat := matterReading electron number

/-- THE CRANK (the tanges that turn the machine): the gates that flipped = the positron count. -/
def gaugeCrank (number : Reading) : Nat := positronCount electron number

/-- THE ELECTRON: the gauge the crank never turns -- all funges, zero tanges. -/
theorem electron_never_cranks : gaugeCrank electron = 0 := by decide
theorem electron_is_all_funge : gaugeFungeCount electron = Gate.all.length := by decide

/-- A real reading off the electron -- the superconducting pair -- turns the crank once (one positron,
at MAGNITUDE) while 35 gates funge. -/
theorem pair_cranks_once : gaugeCrank superconductingPair = 1 := by decide
theorem pair_funges_thirtyfive : gaugeFungeCount superconductingPair = 35 := by decide

/-- Funges and cranks partition the whole gauge: every gate is one or the other, none left over. -/
theorem gauge_funge_crank_partition :
    gaugeFungeCount superconductingPair + gaugeCrank superconductingPair = Gate.all.length := by decide

#eval (gaugeFungeCount electron, gaugeCrank electron)                       -- (36, 0): the electron
#eval (gaugeFungeCount superconductingPair, gaugeCrank superconductingPair)  -- (35, 1): 35 funges, one crank

end Measurement
