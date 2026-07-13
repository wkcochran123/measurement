import Measurement.SelfApplication

/-! # AlphaSelfEnergyFixpoint — Point 1 / Point 9 fix probe (operator "go for fixing", 2026-07-11).

External review, Point 1: the book's chain (two descriptions → elaboration residual → calibrated
self-energy → α) is asserted in prose, but the residual never feeds α, and the raw residual
(`self_residual = echo − orbit = −21` on this build) is a plain heartbeat DIFFERENCE.
Point 9: raw Lean heartbeats are machine/version-dependent — not an invariant — so a raw difference
is not a legitimate physical reading.

Operator's fix ("get them on the first run and put them back in"): the calibration must be
BOOTSTRAPPED from the machine's own first-run measurement, not an external constant (an external
constant would be a tuning knob = the crank's move); and the reading must be a scale-INVARIANT ratio,
so the machine's unknown scale factor cancels and the reading is intrinsic.

This probe forms the self-energy reading as the self-application OVERHEAD over the machine's own
DESCRIPTION cost — both measured in the SAME first run, so they share the machine's scale factor —
and PROVES the reading is invariant under that scale factor. Blind: report the raw numbers, aim at
nothing, do NOT wire it to 137. It fixes the INTRINSIC-NESS (P9) and the anti-tuning bootstrap (P1);
it does NOT by itself replace the distance/slip α driver — that wiring is a separate, principled step.
-/

namespace Measurement.AlphaSelfEnergyFixpoint

open Measurement.SelfApplication

-- First-run measurement, baked at elaboration by `register_cost` (machine-dependent raw heartbeats):
--   orbit, pair, echo : Nat   ( (573, 573, 552) on this build ).
#eval s!"raw first-run costs (machine-dependent, P9): orbit={orbit} pair={pair} echo={echo}"

/-- The self-application OVERHEAD, as a function of the raw costs: proving the two descriptions are
    one (`e`) against merely stating one (`o`). The self-energy residual (numerator of the reading). -/
def overhead (o e : Int) : Int := o - e

/-- The bootstrapped calibration (denominator of the reading): the machine's OWN description cost `o`,
    from the same run — NOT an external constant. "Put it back in": the run calibrates itself. -/
def descriptionCost (o : Int) : Int := o

-- ⭐ THE INTRINSIC PROPERTY (the P9 fix, and the point of the two-pass bootstrap): under any machine
-- scale factor `k`, every raw cost scales by `k`, and the reading `overhead / descriptionCost` is
-- UNCHANGED — stated as the cross-multiplication equality of the two rationals. A raw DIFFERENCE
-- (`self_residual = echo − orbit`) has no such invariance; this RATIO does. That is what makes it a
-- legitimate reading rather than a machine artifact.
theorem selfEnergy_scale_invariant (k o e : Int) :
    overhead (k * o) (k * e) * descriptionCost o
      = overhead o e * descriptionCost (k * o) := by
  simp only [overhead, descriptionCost]
  rw [← Int.mul_sub, Int.mul_comm k (o - e), Int.mul_assoc]
#print axioms selfEnergy_scale_invariant

-- The intrinsic reading on THIS run (blind — reported, not aimed at any target):
#eval s!"self-energy overhead (orbit−echo) = {overhead orbit echo}; bootstrapped calibration (orbit) = {descriptionCost orbit}"
#eval s!"descriptions_residual (orbit−pair) = {(orbit : Int) - pair}  → 0 means the two descriptions cost the SAME (the echo, at the level of cost, not just type)"
#eval s!"intrinsic reading overhead/description = {overhead orbit echo}/{descriptionCost orbit} (dimensionless; scale-invariant by the theorem above)"

end Measurement.AlphaSelfEnergyFixpoint
