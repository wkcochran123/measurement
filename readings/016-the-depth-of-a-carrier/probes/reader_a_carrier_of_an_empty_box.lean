import Experiments.Carriers
open Lean Elab Term Meta Measurement
open «springer-verlag» THE_GOSPEL assembly_instructions the_representation readers_experience
elab "cold" : command => do
  Command.liftTermElabM do
    let stx ← `(decide (read_past_the_quarter_of a_carrier_of_an_empty_box [FACT.Truth, FACT.Truth, FACT.Truth, FACT.Truth] = 4))
    let (_, beats) ← withHeartbeats do
      let e ← elabTerm stx none; let _ ← whnf e; pure ()
    logInfo m!"READ kind=reader which=a_carrier_of_an_empty_box beats={beats}"
cold

