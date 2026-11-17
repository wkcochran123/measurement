import Measurement.Episode08
open Lean Elab Term Meta Measurement
-- Experiment 009b, true from false.  Number.le on the arm T0,F1: a blank, the arm, the arm again.
-- T0 is the device's own truth (Episode 1): its statement is the boolean true, its click is isTrue rfl.
-- F1 is a false built the same way: its statement is the boolean false.
-- F0 is the false of Experiment 009: its statement is False.  T1 is a true built the same way: its statement is True.
def the_true_built_plainly : FACT := { truth := True, click := .isTrue trivial }
def the_false_built_plainly : FACT := { truth := False, click := .isFalse id }
def the_false_built_as_the_truth : FACT := { truth := false, click := .isFalse (fun h => Bool.noConfusion h) }
elab "read_the_meter" : command => do
  Command.liftTermElabM do
    let mut out := ""
    let (_, hb) ← withHeartbeats (pure ())
    out := out ++ s!"BLANK 0 {hb}\n"
    let (beat, blank) ← the_ekg_reads (← `(Number.le (Number.one FACT.Truth (Number.zero FACT.Truth)) (Number.one the_false_built_as_the_truth (Number.zero FACT.Truth))))
    out := out ++ s!"READ 1 T0,F1 {beat} {blank}\n"
    let (beat, blank) ← the_ekg_reads (← `(Number.le (Number.one FACT.Truth (Number.zero FACT.Truth)) (Number.one the_false_built_as_the_truth (Number.zero FACT.Truth))))
    out := out ++ s!"READ 2 T0,F1 {beat} {blank}\n"
    logInfo out
read_the_meter
