import Measurement.Episode13
set_option maxHeartbeats 0
set_option Elab.async false
open Lean Elab Command Measurement
elab "cold" : command => do
  let (_, beats) ← withHeartbeats (Command.elabCommand (← `(command| theorem probe_receipt : the_borwein_scale 8 - the_borwein_sum 8 = 1761207029433090695936 := by decide +kernel)))
  logInfo m!"READ kind=kernel m=8 beats={beats}"
cold

