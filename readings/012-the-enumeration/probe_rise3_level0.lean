import Measurement.Episode08
open Lean Elab Term Meta Measurement readers_experience
-- Experiment 012, the enumeration.  Rise 3, level 0: a tape of 3 * 0(0+1)/2 = 0 cells of the device's truth, every cell
-- clicked once, read once on Episode 8's meter beside its blank.  One fresh process per reading.
elab "read_the_meter" : command => do
  Command.liftTermElabM do
    let (beat, blank) ← the_ekg_reads (← `((List.replicate 0 FACT.Truth).all (fun fact : FACT => (@decide fact.truth fact.click) || !(@decide fact.truth fact.click))))
    logInfo m!"READ rise=3 level=0 cells=0 beat={beat} blank={blank}"
read_the_meter
