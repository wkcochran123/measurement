import Measurement.Episode08
open Lean Elab Term Meta Measurement readers_experience
-- Experiment 012, the enumeration.  Rise 2, level 3: a tape of 2 * 3(3+1)/2 = 12 cells of the device's truth, every cell
-- clicked once, read once on Episode 8's meter beside its blank.  One fresh process per reading.
elab "read_the_meter" : command => do
  Command.liftTermElabM do
    let (beat, blank) ← the_ekg_reads (← `((List.replicate 12 FACT.Truth).all (fun fact : FACT => (@decide fact.truth fact.click) || !(@decide fact.truth fact.click))))
    logInfo m!"READ rise=2 level=3 cells=12 beat={beat} blank={blank}"
read_the_meter
