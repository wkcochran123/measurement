import Experiments.Carriers
open Lean Elab Term Meta Measurement
open «springer-verlag» THE_GOSPEL assembly_instructions the_representation readers_experience
elab "cold" : command => do
  Command.liftTermElabM do
    let stx ← `(STEP1_NAME_THE_LEDGER_AND_MARK_IT_WITH_THE_SYMBOL_OF_THE_NOWTRINO Prop elaborated_by_lean the_first_card FACT.Truth)
    let (_, beats) ← withHeartbeats do
      let e ← elabTerm stx none; let _ ← whnf e; pure ()
    logInfo m!"READ kind=rung which=one beats={beats}"
cold

