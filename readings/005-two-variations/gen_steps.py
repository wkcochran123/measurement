import sys
# usage: gen_steps.py K  -> step k = 0..K-1 decides k+1 cells of the device's table, shifted by k so every term is new
# (cold), logged on Episode 8's meter with wall time: "STEP k cells raw blank ns".
K=int(sys.argv[1])
print(f'''import Measurement.Episode12
open Lean Elab Term Meta Measurement
def cellA (i : Nat) : Bool := i % 2 == 0
def cellB (i : Nat) : Bool := (i / 2) % 2 == 0
elab "steps" : command => do
  Command.liftTermElabM do
    let mut out := ""
    for k in [0:{K}] do
      let kk := Lean.quote k
      let cc := Lean.quote (k + 1)
      let stx ← `((({{ truth := ∀ i : Fin $cc,
                          the_representation.outer_table (cellA (i.val + $kk)) (cellB (i.val + $kk))
                        = the_representation.middle_table (cellA (i.val + $kk)) (cellB (i.val + $kk)),
                      click := inferInstance }} : FACT)).click)
      let t0 ← IO.monoNanosNow
      let (h, b) ← the_ekg_reads stx
      let t1 ← IO.monoNanosNow
      out := out ++ s!"STEP {{k}} {{k + 1}} {{h}} {{b}} {{t1 - t0}}\\n"
    logInfo out
steps
''')
