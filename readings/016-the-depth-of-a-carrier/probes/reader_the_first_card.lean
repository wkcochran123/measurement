import Experiments.Carriers
open Lean Elab Term Meta Measurement
open «springer-verlag» THE_GOSPEL assembly_instructions the_representation readers_experience
elab "cold" : command => do
  Command.liftTermElabM do
    let stx ← `(decide (read_past_the_quarter_of the_first_card [FACT.Truth, FACT.Truth, FACT.Truth, FACT.Truth] = 4))
    let (_, beats) ← withHeartbeats do
      let e ← elabTerm stx none; let _ ← whnf e; pure ()
    logInfo m!"READ kind=reader which=the_first_card beats={beats}"
cold

