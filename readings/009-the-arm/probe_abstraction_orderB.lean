import Measurement.Episode08
open Lean Elab Term Meta Measurement
-- Experiment 009, the arm.  Abstraction.le on all four pairs in the order EE EC CE CC, twice over.
def the_false : FACT := { truth := False, click := .isFalse id }
elab "read_the_arms" : command => do
  Command.liftTermElabM do
    let mut out := ""
    let (_, hb) ← withHeartbeats (pure ())
    out := out ++ s!"BLANK 0 {hb}\n"
    let (beat, blank) ← the_ekg_reads (← `(Abstraction.le (Abstraction.execute FACT.Truth δδxᵢ carefully_chosen_variable_names) (Abstraction.execute FACT.Truth δδxᵢ carefully_chosen_variable_names)))
    out := out ++ s!"READ 1 EE {beat} {blank}\n"
    let (beat, blank) ← the_ekg_reads (← `(Abstraction.le (Abstraction.execute FACT.Truth δδxᵢ carefully_chosen_variable_names) (Abstraction.compile FACT.Truth δδxᵢ carefully_chosen_variable_names)))
    out := out ++ s!"READ 1 EC {beat} {blank}\n"
    let (beat, blank) ← the_ekg_reads (← `(Abstraction.le (Abstraction.compile FACT.Truth δδxᵢ carefully_chosen_variable_names) (Abstraction.execute FACT.Truth δδxᵢ carefully_chosen_variable_names)))
    out := out ++ s!"READ 1 CE {beat} {blank}\n"
    let (beat, blank) ← the_ekg_reads (← `(Abstraction.le (Abstraction.compile FACT.Truth δδxᵢ carefully_chosen_variable_names) (Abstraction.compile FACT.Truth δδxᵢ carefully_chosen_variable_names)))
    out := out ++ s!"READ 1 CC {beat} {blank}\n"
    let (beat, blank) ← the_ekg_reads (← `(Abstraction.le (Abstraction.execute FACT.Truth δδxᵢ carefully_chosen_variable_names) (Abstraction.execute FACT.Truth δδxᵢ carefully_chosen_variable_names)))
    out := out ++ s!"READ 2 EE {beat} {blank}\n"
    let (beat, blank) ← the_ekg_reads (← `(Abstraction.le (Abstraction.execute FACT.Truth δδxᵢ carefully_chosen_variable_names) (Abstraction.compile FACT.Truth δδxᵢ carefully_chosen_variable_names)))
    out := out ++ s!"READ 2 EC {beat} {blank}\n"
    let (beat, blank) ← the_ekg_reads (← `(Abstraction.le (Abstraction.compile FACT.Truth δδxᵢ carefully_chosen_variable_names) (Abstraction.execute FACT.Truth δδxᵢ carefully_chosen_variable_names)))
    out := out ++ s!"READ 2 CE {beat} {blank}\n"
    let (beat, blank) ← the_ekg_reads (← `(Abstraction.le (Abstraction.compile FACT.Truth δδxᵢ carefully_chosen_variable_names) (Abstraction.compile FACT.Truth δδxᵢ carefully_chosen_variable_names)))
    out := out ++ s!"READ 2 CC {beat} {blank}\n"
    logInfo out
read_the_arms
