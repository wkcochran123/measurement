import Measurement.Episode08
open Lean Elab Term Meta Measurement
-- Experiment 009, the arm.  The device's first order, Number.le, on the one arm FT: a blank, the arm, the arm again.
def the_false : FACT := { truth := False, click := .isFalse id }
elab "read_the_arms" : command => do
  Command.liftTermElabM do
    let mut out := ""
    let (_, hb) ← withHeartbeats (pure ())
    out := out ++ s!"BLANK 0 {hb}\n"
    let (beat, blank) ← the_ekg_reads (← `(Number.le (Number.one the_false (Number.zero FACT.Truth)) (Number.one FACT.Truth (Number.zero FACT.Truth))))
    out := out ++ s!"READ 1 FT {beat} {blank}\n"
    let (beat, blank) ← the_ekg_reads (← `(Number.le (Number.one the_false (Number.zero FACT.Truth)) (Number.one FACT.Truth (Number.zero FACT.Truth))))
    out := out ++ s!"READ 2 FT {beat} {blank}\n"
    logInfo out
read_the_arms
