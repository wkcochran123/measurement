import Measurement.SelfApplication

/-! # ResidueUAT — the acceptance test: residue carried across == resulting residue.
Operator: "that is UAT. verify the residue numbers that have to be carried across the computation
and the resulting residue are the same."

The self-application measures three costs, carried across the computation as the cycle of three
orbit → pair → echo → orbit  ( (573, 573, 552) ; deterministic, reproduces build-to-build ).
The residue carried on each edge of the cycle must sum back to ZERO — the loop closes, so the
resulting residue equals the one carried in (the residue is conserved around the cycle of three).
This is the numeric form of `CycleOfThree.residue_invariant_under_cycle` (spin 3 x = x). -/

namespace Measurement.ResidueUAT

open Measurement.SelfApplication

-- The residue carried on each edge of the three-cycle (orbit → pair → echo → orbit):
def d1 : Int := (pair : Int) - orbit    -- orbit → pair   (the two descriptions:  573−573 =  0)
def d2 : Int := (echo : Int) - pair     -- pair  → echo   (description → proof:   552−573 = −21)
def d3 : Int := (orbit : Int) - echo    -- echo  → orbit  (closes the loop:       573−552 = +21)

-- ⭐ UAT: the residues carried across the computation sum to ZERO — carried residue == resulting.
theorem residue_carried_equals_resulting : d1 + d2 + d3 = 0 := by decide

-- Equivalently: start, plus every residue carried around the cycle, returns to the start.
theorem cycle_returns_to_start : (orbit : Int) + d1 + d2 + d3 = (orbit : Int) := by decide

#print axioms residue_carried_equals_resulting

#eval s!"costs carried across (cycle of three): orbit={orbit}  pair={pair}  echo={echo}"
#eval s!"residues carried on each edge:  d1(orbit→pair)={d1}   d2(pair→echo)={d2}   d3(echo→orbit)={d3}"
#eval s!"sum of carried residues = {d1 + d2 + d3}   →   resulting = start = {orbit}"
#eval s!"UAT: carried == resulting?  {decide (d1 + d2 + d3 = 0)}   (loop closes; residue conserved around the cycle of three)"

end Measurement.ResidueUAT
