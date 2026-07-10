import Measurement.Episode1

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000
set_option allowUnsafeReducibility true

namespace Measurement

/-
__FUNGE__: the grounded funge/tange primitives.

The funge bit and the crank/measurement counts, grounded on `Fact` (Episode1) and
core `List`/`decide` alone. They live here -- early, off Episode1 -- so the loop's
forward walk (the Ep17 recast) and the parity obstruction (Episode41) can both rest
on the one partition. Relocated verbatim from Episode41; no logic change.
-/

/-- A funge bit: the truth read forward (the funge, `true`) or reversed (the tange, `false`). -/
def fungeBit (f : Fact) : Bool := @decide f.truth f.decTruth

/-- THE CRANK: how many times the tanges turn it -- the residue count, the engine. -/
def crankTurns (tape : List Fact) : Nat :=
  (tape.map fungeBit).countP (fun b => b == false)

/-- THE MEASUREMENT: count the funges -- the matter the machine reads. -/
def countFunges (tape : List Fact) : Nat :=
  (tape.map fungeBit).countP (fun b => b == true)

/-- Every fact is read exactly once: counted (a funge) or turning the crank (a tange). -/
theorem funges_and_cranks_partition (tape : List Fact) :
    countFunges tape + crankTurns tape = tape.length := by
  unfold countFunges crankTurns
  induction tape with
  | nil => rfl
  | cons f rest ih =>
    simp only [List.map_cons, List.countP_cons, List.length_cons]
    cases fungeBit f <;> simp_all <;> omega

end Measurement
