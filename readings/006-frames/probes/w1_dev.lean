import Measurement.Episode12
open Lean Elab Term Meta Measurement
def cellA (i : Nat) : Bool := i % 2 == 0
def cellB (i : Nat) : Bool := (i / 2) % 2 == 0
def probe : FACT :=
  { truth := ∀ i : Fin 64, the_representation.outer_table (cellA i.val) (cellB i.val)
                           = the_representation.middle_table (cellA i.val) (cellB i.val)
    click := inferInstance }
elab "cold" : command => do
  Command.liftTermElabM do
    let t0 ← IO.monoNanosNow
    let (h, b) ← the_ekg_reads (← `(probe.click))
    let t1 ← IO.monoNanosNow
    logInfo m!"TIMED n=64 ctrl=false raw={h} blank={b} net={(h:Int)-b} ns={t1-t0}"
cold

