import Measurement.Episode08
open Lean Elab Term Meta Measurement readers_experience
-- Experiment 011, the throw.  the other axiom thrown: propext, on the truth of the device's truth.  Read twice in one process, each beside its blank.
elab "read_the_meter" : command => do
  Command.liftTermElabM do
    let mut out := ""
    let (_, hb) ← withHeartbeats (pure ())
    out := out ++ s!"BLANK 0 {hb}\n"
    let (beat, blank) ← the_ekg_reads (← `((propext (Iff.intro id id) : (FACT.Truth.truth) = (FACT.Truth.truth))))
    out := out ++ s!"READ 1 propext {beat} {blank}\n"
    let (beat, blank) ← the_ekg_reads (← `((propext (Iff.intro id id) : (FACT.Truth.truth) = (FACT.Truth.truth))))
    out := out ++ s!"READ 2 propext {beat} {blank}\n"
    logInfo out
read_the_meter
