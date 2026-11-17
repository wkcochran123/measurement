import Measurement.Episode08
open Lean Elab Term Meta Measurement
-- Experiment 009, the arm.  Number.le on all four arms in the order FF FT TF TT, twice over.
def the_false : FACT := { truth := False, click := .isFalse id }
elab "read_the_arms" : command => do
  Command.liftTermElabM do
    let mut out := ""
    let (_, hb) ← withHeartbeats (pure ())
    out := out ++ s!"BLANK 0 {hb}\n"
    let (beat, blank) ← the_ekg_reads (← `(Number.le (Number.one the_false (Number.zero FACT.Truth)) (Number.one the_false (Number.zero FACT.Truth))))
    out := out ++ s!"READ 1 FF {beat} {blank}\n"
    let (beat, blank) ← the_ekg_reads (← `(Number.le (Number.one the_false (Number.zero FACT.Truth)) (Number.one FACT.Truth (Number.zero FACT.Truth))))
    out := out ++ s!"READ 1 FT {beat} {blank}\n"
    let (beat, blank) ← the_ekg_reads (← `(Number.le (Number.one FACT.Truth (Number.zero FACT.Truth)) (Number.one the_false (Number.zero FACT.Truth))))
    out := out ++ s!"READ 1 TF {beat} {blank}\n"
    let (beat, blank) ← the_ekg_reads (← `(Number.le (Number.one FACT.Truth (Number.zero FACT.Truth)) (Number.one FACT.Truth (Number.zero FACT.Truth))))
    out := out ++ s!"READ 1 TT {beat} {blank}\n"
    let (beat, blank) ← the_ekg_reads (← `(Number.le (Number.one the_false (Number.zero FACT.Truth)) (Number.one the_false (Number.zero FACT.Truth))))
    out := out ++ s!"READ 2 FF {beat} {blank}\n"
    let (beat, blank) ← the_ekg_reads (← `(Number.le (Number.one the_false (Number.zero FACT.Truth)) (Number.one FACT.Truth (Number.zero FACT.Truth))))
    out := out ++ s!"READ 2 FT {beat} {blank}\n"
    let (beat, blank) ← the_ekg_reads (← `(Number.le (Number.one FACT.Truth (Number.zero FACT.Truth)) (Number.one the_false (Number.zero FACT.Truth))))
    out := out ++ s!"READ 2 TF {beat} {blank}\n"
    let (beat, blank) ← the_ekg_reads (← `(Number.le (Number.one FACT.Truth (Number.zero FACT.Truth)) (Number.one FACT.Truth (Number.zero FACT.Truth))))
    out := out ++ s!"READ 2 TT {beat} {blank}\n"
    logInfo out
read_the_arms
