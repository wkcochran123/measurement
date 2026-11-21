import sys
# usage: gen.py <workload> <n>      workloads: w0 (Experiment 001's), w1, w2, w3, ctrl
w, n = sys.argv[1], int(sys.argv[2])
truth = {
 'w0': 'the_representation.outer_table (cellA i.val) (cellB i.val) = the_representation.middle_table (cellA i.val) (cellB i.val)',
 'w1': 'the_representation.outer_table (cellA i.val) (cellB i.val) = the_representation.outer_table (cellB i.val) (cellA i.val)',
 'w2': 'the_representation.middle_table (cellA i.val) (cellB i.val) = the_representation.middle_table (cellB i.val) (cellA i.val)',
 'w3': 'the_arm_weight (cellA i.val) (cellB i.val) = the_arm_weight (cellA i.val) (cellB i.val)',
 'ctrl': 'True',
}[w]
print(f'''import Measurement.Episode12
open Lean Elab Term Meta Measurement
def cellA (i : Nat) : Bool := i % 2 == 0
def cellB (i : Nat) : Bool := (i / 2) % 2 == 0
def probe : FACT :=
  {{ truth := ∀ i : Fin {n}, {truth}
    click := inferInstance }}
elab "cold" : command => do
  Command.liftTermElabM do
    let (h, b) ← the_ekg_reads (← `(probe.click))
    let w ← whnf (← elabTerm (← `(probe.click)) none)
    logInfo m!"READ work={w} n={n} raw={{h}} blank={{b}} net={{(h:Int)-b}} head={{w.getAppFn}}"
cold
''')
