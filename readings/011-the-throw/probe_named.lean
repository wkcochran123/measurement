import Measurement.Episode08
open Lean Elab Term Meta Measurement readers_experience
-- Experiment 011, the throw.  Episode 8's own throw, read by its name.  Read twice in one process, each beside its blank.
elab "read_the_meter" : command => do
  Command.liftTermElabM do
    let mut out := ""
    let (_, hb) ← withHeartbeats (pure ())
    out := out ++ s!"BLANK 0 {hb}\n"
    let (beat, blank) ← the_ekg_reads (← `(a_partitioning_of_quotients 1 1))
    out := out ++ s!"READ 1 named {beat} {blank}\n"
    let (beat, blank) ← the_ekg_reads (← `(a_partitioning_of_quotients 1 1))
    out := out ++ s!"READ 2 named {beat} {blank}\n"
    logInfo out
read_the_meter
