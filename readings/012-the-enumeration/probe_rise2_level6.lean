import Measurement.Episode08
open Lean Elab Term Meta Measurement readers_experience
-- Experiment 012, the enumeration.  Rise 2, level 6: a tape of 2 * 6(6+1)/2 = 42 cells of the device's truth, every cell
-- clicked once, read once on Episode 8's meter beside its blank.  One fresh process per reading.
elab "read_the_meter" : command => do
  Command.liftTermElabM do
    let (beat, blank) ← the_ekg_reads (← `((List.replicate 42 FACT.Truth).all (fun fact : FACT => (@decide fact.truth fact.click) || !(@decide fact.truth fact.click))))
    logInfo m!"READ rise=2 level=6 cells=42 beat={beat} blank={blank}"
read_the_meter
