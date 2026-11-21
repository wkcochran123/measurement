import Measurement.Episode12
open Lean Elab Term Meta Measurement
def cellA (i : Nat) : Bool := i % 2 == 0
def cellB (i : Nat) : Bool := (i / 2) % 2 == 0
def probe : FACT :=
  { truth := ∀ i : Fin 8, the_representation.outer_table (cellA i.val) (cellB i.val) = the_representation.middle_table (cellA i.val) (cellB i.val)
    click := inferInstance }
elab "cold" : command => do
  Command.liftTermElabM do
    let (h, b) ← the_ekg_reads (← `(probe.click))
    let w ← whnf (← elabTerm (← `(probe.click)) none)
    logInfo m!"READ work=w0 n=8 raw={h} blank={b} net={(h:Int)-b} head={w.getAppFn}"
cold

