import sys
# usage: probe.py <kind> <which>    kind: reader | rung
kind, which = sys.argv[1], sys.argv[2]
if kind == 'reader':
    term = f'decide (read_past_the_quarter_of {which} [FACT.Truth, FACT.Truth, FACT.Truth, FACT.Truth] = 4)'
else:
    term = {
     'one':   'STEP1_NAME_THE_LEDGER_AND_MARK_IT_WITH_THE_SYMBOL_OF_THE_NOWTRINO Prop elaborated_by_lean the_first_card FACT.Truth',
     'two':   'STEP1_NAME_THE_LEDGER_AND_MARK_IT_WITH_THE_SYMBOL_OF_THE_NOWTRINO (CarrierProcess FACT) the_card_between the_first_card FACT.Truth',
     'three': 'STEP1_NAME_THE_LEDGER_AND_MARK_IT_WITH_THE_SYMBOL_OF_THE_NOWTRINO (CarrierProcess (CarrierProcess FACT)) the_card_on_the_card_between the_first_card FACT.Truth',
    }[which]
print(f'''import Experiments.Carriers
open Lean Elab Term Meta Measurement
open «springer-verlag» THE_GOSPEL assembly_instructions the_representation readers_experience
elab "cold" : command => do
  Command.liftTermElabM do
    let stx ← `({term})
    let (_, beats) ← withHeartbeats do
      let e ← elabTerm stx none; let _ ← whnf e; pure ()
    logInfo m!"READ kind={kind} which={which} beats={{beats}}"
cold
''')
