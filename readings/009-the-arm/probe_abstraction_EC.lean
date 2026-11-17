import Measurement.Episode08
open Lean Elab Term Meta Measurement
-- Experiment 009, the arm.  Abstraction.le on the one pair EC: a blank, the pair, the pair again.
def the_false : FACT := { truth := False, click := .isFalse id }
elab "read_the_arms" : command => do
  Command.liftTermElabM do
    let mut out := ""
    let (_, hb) ← withHeartbeats (pure ())
    out := out ++ s!"BLANK 0 {hb}\n"
    let (beat, blank) ← the_ekg_reads (← `(Abstraction.le (Abstraction.execute FACT.Truth δδxᵢ carefully_chosen_variable_names) (Abstraction.compile FACT.Truth δδxᵢ carefully_chosen_variable_names)))
    out := out ++ s!"READ 1 EC {beat} {blank}\n"
    let (beat, blank) ← the_ekg_reads (← `(Abstraction.le (Abstraction.execute FACT.Truth δδxᵢ carefully_chosen_variable_names) (Abstraction.compile FACT.Truth δδxᵢ carefully_chosen_variable_names)))
    out := out ++ s!"READ 2 EC {beat} {blank}\n"
    logInfo out
read_the_arms
