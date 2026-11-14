import sys
# usage: gen_beats.py K CELLS   -> a Lean file logging, for k = 0..K-1, one cold device decision of CELLS cells,
# shifted by k so that every term is new: "k raw blank ns" per line.
K=int(sys.argv[1]); C=int(sys.argv[2]) if len(sys.argv)>2 else 8
print(f'''import Measurement.Episode12
open Lean Elab Term Meta Measurement
def cellA (i : Nat) : Bool := i % 2 == 0
def cellB (i : Nat) : Bool := (i / 2) % 2 == 0
elab "beats" : command => do
  Command.liftTermElabM do
    let mut out := ""
    for k in [0:{K}] do
      let kk := Lean.quote k
      let stx ← `((({{ truth := ∀ i : Fin {C},
                          the_representation.outer_table (cellA (i.val + $kk)) (cellB (i.val + $kk))
                        = the_representation.middle_table (cellA (i.val + $kk)) (cellB (i.val + $kk)),
                      click := inferInstance }} : FACT)).click)
      let t0 ← IO.monoNanosNow
      let (h, b) ← the_ekg_reads stx
      let t1 ← IO.monoNanosNow
      out := out ++ s!"BEAT {{k}} {{h}} {{b}} {{t1 - t0}}\\n"
    logInfo out
beats
''')
