-- TheNonsenseLadder.lean
--
-- Steps one and two of the operator's program (2026-08-23 20:43): "1. start
-- from absolute nonsense  2. measure it in elab  3. demonstrate
-- superconvergence  4. compute richardson of the first variation."
--
-- ABSOLUTE NONSENSE: a tower of `ULift`s over `Nat`, k deep.  It says nothing,
-- computes nothing, and is discarded the moment it is elaborated.  Its only
-- content is that the elaborator must do work to accept it.
--
-- MEASURED IN ELAB, and in the elaborator's own currency: HEARTBEATS, read off
-- `IO.getNumHeartbeats` on either side of the elaboration.  Not wall-clock -- I
-- measured that first and it was noisy enough at small depths to INVERT the
-- ordering (depth 16 came back cheaper than depth 8), which would have made any
-- extrapolation an artifact of the machine rather than of the work.  Heartbeats
-- are the elaborator counting itself, which is the bullshit meter's own unit.
--
-- THIS FILE ONLY MEASURES.  It draws no conclusion about superconvergence and
-- computes no extrapolation; those are steps three and four and they depend on
-- what the numbers turn out to do.  The numbers print into the build log so
-- anyone can regenerate them rather than quote me.

import Lean

open Lean Elab Command Term in
/-- Elaborate a k-deep tower of nonsense and report what it cost the
elaborator, in heartbeats. -/
elab "nonsense_costs " n:num : command => do
  let k := n.getNat
  let mut stx ← `(Nat)
  for _ in [0:k] do
    stx ← `(ULift $stx)
  liftTermElabM do
    let h0 ← IO.getNumHeartbeats
    let _ ← Term.elabTerm stx none
    Term.synthesizeSyntheticMVars
    let h1 ← IO.getNumHeartbeats
    logInfo s!"nonsense depth {k}: {h1 - h0} heartbeats"

nonsense_costs 4
nonsense_costs 8
nonsense_costs 16
nonsense_costs 32
nonsense_costs 64
nonsense_costs 128
