import Measurement.Episode84
import Measurement.Calibration.EKGBounded
import Lean.Util.Heartbeats
import Lean.Elab.Command

/-! # AlphaLoopProbe — Phase 0c ITERATION 2 (FINAL): the closed-LOOP holonomy, division needle (blind)

Per Kodo Turn 86 + the operator's ITERATION-2 design (SPEC.md 0c). 0c-i1 (`AlphaFoldProbe`, `4c43954`) read the
OPEN path: flat, δ²≈0 = gauge-fixed serial α=0 (Ep84 open=0); the −1/137 warmup coincidence was REFUSED. The real α
= the closed-LOOP holonomy (Ep84 loop≠0). The trick: the BINARY needle (`Quot.sound`, identify-iff-null) is flat;
replace it with a **DIVISION ALGORITHM (`abbrev` = reducible)** — the **REMAINDER around the loop = the holonomy**
(quantitative, axiom-free by `rfl`; the elaboration cost of unfolding IS the α measurement, self-fenced by
`withHeartbeats`). **LAST instrument. BLIND: target absent; WIP α-named outputs quarantined (zero import).**

TWO readings: (A) the term-level loop holonomy = ±1 (Ep84, PROVED, choice-free — the STRUCTURE of α = the
matter/antimatter (−i)² sign); (B) the division needle's elaboration cost + remainder (the quantitative meta). -/

namespace Measurement.AlphaLoopProbe
open Lean Measurement

/-! ## (A) THE STRUCTURE — the loop holonomy is ±1, PROVED, choice-free (Ep84 loop≠0 vs open=0). -/
open CubicGaugeVariation in
example : holonomy tiltedPath (pairVariation node1 node2) = 1
    ∧ holonomy flatPath (pairVariation node1 node2) = -1 := holonomy_loop_is_charged
open CubicGaugeVariation in
example : holonomy tiltedPath (pairVariation node2 node1) = 0 := holonomy_open_is_trivial   -- open = 0

/-! ## (B) THE DIVISION NEEDLE — quantitative, axiom-free (abbrev, unfolds by `rfl`).
The remainder of long-dividing around the loop: at depth k, `rem(base,k)` = the residue `1` leaves after k
digit-steps in `base` — how much does NOT close (the holonomy). `abbrev` ⇒ reducible ⇒ computed at elaboration. -/

/-- one long-division digit-step: bring down a digit (×base... here the residue evolves ×2, binary) mod the base. -/
abbrev divStep (base r : Nat) : Nat := (r * 2) % base

/-- the loop remainder at depth k: iterate the division needle around the loop from the seed residue 1. -/
def loopRem (base : Nat) : Nat → Nat
  | 0     => 1
  | (k+1) => divStep base (loopRem base k)

-- THE RAW HOLONOMY REMAINDERS (blind) — over the construction's own bases (boxCount=2, roots=4, rank=36); report
-- whatever they are, aim at nothing. A remainder that returns to 0 = the loop CLOSES (holonomy null, quantized);
-- a non-closing cycle = a live holonomy.
#eval (loopRem 2 1,  loopRem 2 2,  loopRem 2 3,  loopRem 2 4)      -- base 2 (the binary/boxCount base)
#eval (loopRem 4 1,  loopRem 4 2,  loopRem 4 3,  loopRem 4 4)      -- base 4 (the (−i)⁴ four-roots period)
#eval (loopRem 36 1, loopRem 36 2, loopRem 36 3, loopRem 36 4, loopRem 36 5, loopRem 36 6)   -- base 36 (the rank/tower)

-- (B) THE ELABORATION COST of the division needle = the α measurement (needle+ruler unified; withHeartbeats-fenced).
elab "register_cost" name:ident " => " t:term : command => do
  let hb ← Lean.Elab.Command.liftTermElabM do
    let (_, hb) ← Lean.withHeartbeats do
      let e ← Lean.Elab.Term.elabTerm t none
      let _ ← Lean.Meta.whnf e
      pure ()
    pure hb
  let cmd ← `(def $name:ident : Nat := $(Lean.quote hb))
  Lean.Elab.Command.elabCommand cmd

register_cost blank => (Fact.Truth.decTruth)
register_cost c1 => (loopRem 36 4)
register_cost c2 => (loopRem 36 8)
register_cost c3 => (loopRem 36 12)
register_cost c4 => (loopRem 36 16)
register_cost c5 => (loopRem 36 20)

-- THE RAW RUN-LOG (full, in order — not the flattering run):
#eval (blank, c1, c2, c3, c4, c5)                                 -- blank + the division-needle cost sweep
def dc1 : Int := (c2:Int)-c1
def dc2 : Int := (c3:Int)-c2
def dc3 : Int := (c4:Int)-c3
def dc4 : Int := (c5:Int)-c4
#eval (dc1, dc2, dc3, dc4)                                        -- δ¹ (first differences of the division cost)
#eval ((dc2-dc1), (dc3-dc2), (dc4-dc3))                           -- δ² (curvature = α candidate)

end Measurement.AlphaLoopProbe
