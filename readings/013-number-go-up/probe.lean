import Measurement.Episode08
open Lean Elab Term Meta Measurement readers_experience
-- Experiment 013, number go up.  The timer is in the code.  One evaluation: the device's truth, one cell, clicked once,
-- elaborated and reduced to weak head normal form.  The clock (nanoseconds) and the heartbeats are read before and after
-- one evaluation, and before and after ten, a hundred and a thousand of the same evaluation, all in one compile.
def evaluated (times : Nat) : TermElabM (Nat × Nat) := do
  let one_cell_clicked ← `(([FACT.Truth]).all (fun fact : FACT => (@decide fact.truth fact.click) || !(@decide fact.truth fact.click)))
  let before ← IO.monoNanosNow
  let (_, beats) ← withHeartbeats do
    for _ in [0:times] do
      let e ← elabTerm one_cell_clicked none; let _ ← whnf e; pure ()
  let after ← IO.monoNanosNow
  pure (beats, after - before)
elab "number_go_up" : command => do
  Command.liftTermElabM do
    for times in [1, 10, 100, 1000] do
      let (beats, nanoseconds) ← evaluated times
      logInfo m!"READ evaluations={times} beats={beats} nanoseconds={nanoseconds}"
number_go_up
