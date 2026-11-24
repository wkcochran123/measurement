import Measurement.Episode13
set_option maxHeartbeats 0
set_option Elab.async false
open Lean Elab Command Measurement
elab "cold" : command => do
  let (_, beats) ← withHeartbeats (Command.elabCommand (← `(command| theorem probe_receipt : the_borwein_scale 6 - the_borwein_sum 6 = 0 := by decide)))
  logInfo m!"READ kind=elaborator m=6 beats={beats}"
cold

