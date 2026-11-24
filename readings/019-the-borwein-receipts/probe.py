import sys
# usage: probe.py <kind> <m>    kind: kernel | elaborator | blank | check ;  m: 1..8 (sincs after the first)
kind, m = sys.argv[1], int(sys.argv[2])
# What the sum falls short of the scale by: nothing through the bent card, twice the slack owed to the seventh at eight.
short = {1: 0, 2: 0, 3: 0, 4: 0, 5: 0, 6: 0, 7: 0, 8: 1761207029433090695936}[m]
statement = f'the_borwein_scale {m} - the_borwein_sum {m} = {short}'
if kind == 'kernel':
    cmd = f'theorem probe_receipt : {statement} := by decide +kernel'
elif kind == 'elaborator':
    cmd = f'theorem probe_receipt : {statement} := by decide'
elif kind == 'blank':
    cmd = 'theorem probe_receipt : True := trivial'
else:
    cmd = None
head = '''import Measurement.Episode13
set_option maxHeartbeats 0
open Lean Elab Command Measurement
'''
if cmd is None:
    print(head + '#check the_borwein_sum\n#check the_borwein_scale\n')
else:
    print(head + f'''elab "cold" : command => do
  let (_, beats) ← withHeartbeats (Command.elabCommand (← `(command| {cmd})))
  logInfo m!"READ kind={kind} m={m} beats={{beats}}"
cold
''')
