import sys
# usage: probe.py <kind> <depth>    kind: reader | step | check ; depth: 1..5
kind, depth = sys.argv[1], int(sys.argv[2])
cards = {1: 'card1', 2: 'card2', 3: 'card3', 4: 'card4', 5: 'card5'}
card = cards[depth]
if kind == 'reader':
    term = f'decide (past_the_quarter {card} [FACT.Truth, FACT.Truth, FACT.Truth, FACT.Truth] = 4)'
elif kind == 'step':
    term = (f'(rfl : {card}.interact_with_the_universe ({card}.interact_with_the_universe (.one FACT.Truth (.zero FACT.Truth)))'
            f' = {card}.interact_with_the_universe (.one FACT.Truth (.zero FACT.Truth)))')
else:
    term = 'True'
print(f'''import Measurement.Episode12
open Lean Elab Term Meta Measurement
-- The five cards, written alike, one more wrapper each.  Every probe carries all five, so only the term read differs.
def card1 : CarrierProcess FACT := {{ symbol := FACT.Truth, quarter := .zero FACT.Truth }}
def card2 : CarrierProcess (CarrierProcess FACT) := {{ symbol := FACT.Truth, quarter := .zero FACT.Truth }}
def card3 : CarrierProcess (CarrierProcess (CarrierProcess FACT)) := {{ symbol := FACT.Truth, quarter := .zero FACT.Truth }}
def card4 : CarrierProcess (CarrierProcess (CarrierProcess (CarrierProcess FACT))) :=
  {{ symbol := FACT.Truth, quarter := .zero FACT.Truth }}
def card5 : CarrierProcess (CarrierProcess (CarrierProcess (CarrierProcess (CarrierProcess FACT)))) :=
  {{ symbol := FACT.Truth, quarter := .zero FACT.Truth }}
-- The reader past the quarter, for any box (as in Experiments/Carriers.lean).
def past_the_quarter {{Box : Type}} (card : CarrierProcess Box) (tape : List FACT) : Nat :=
  (tape.foldr Number.one card.quarter).peano.length - card.quarter.peano.length
elab "cold" : command => do
  Command.liftTermElabM do
    let stx ← `({term})
    let (_, beats) ← withHeartbeats do
      let e ← elabTerm stx none; let _ ← whnf e; pure ()
    logInfo m!"READ kind={kind} depth={depth} beats={{beats}}"
cold
''')
