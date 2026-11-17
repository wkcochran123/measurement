import Measurement.Episode08
open Lean Elab Term Meta Measurement readers_experience
-- Experiment 010. One tape, every cell clicked once, on the EKG's own procedure (elaborate, then weak head normal form),
-- with a clock read before and after. One fresh process per reading.
elab "read_the_tape" : command => do
  Command.liftTermElabM do
    let tape ← `(([FACT.Truth]).all (fun fact : FACT => (@decide fact.truth fact.click) || !(@decide fact.truth fact.click)))
    let t0 ← IO.monoNanosNow
    let (_, beat) ← withHeartbeats do
      let e ← elabTerm tape none; let _ ← whnf e; pure ()
    let t1 ← IO.monoNanosNow
    logInfo m!"READ one_blank hb={beat} ns={t1 - t0}"
read_the_tape
