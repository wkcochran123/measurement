import Measurement.CalibrationTwoPaths

/-! # Measurement.Gauge.LockResonance — the Pound–Rebka companion (Q5 rider, turn 546).

The lock criterion of the de-selection program's (ii-b) gate, finished the way the
operator pointed (2026-07-24 11:26 "pound rebka should finish this for you"): not by
comparing endpoints but by DRIVING the source through the count ladder and reading
the resonance. Pound–Rebka measured the tower shift by moving the emitter until
resonance nulled — the compensation is the reading, and the resonance WIDTH is the
floor, measured not asserted.

Here: the stepped path's count is the drivable source. `fringeAt n` = the two-path
disagreement with the stepped descent run to count `n`. The resonance curve is
`fringeAt 2, 3, 4`; LOCK = the successive fringes CONTRACT at the fencepost — the
Weierstrass squeeze realized as the count ladder (count-to-FENCEPOST, the operator's
ruling: a standing state approached by construction, never an achieved endpoint).
The (ii-b) floor becomes a MEASURED contraction width.

DISCIPLINE (Kodo's constraint, turn 546): a leaf DISPLAY — this module READS
(CalibrationTwoPaths, AlphaBFGS) and FEEDS NOTHING; zero edits inside any measured
file; nothing imports this module. -/

namespace Measurement.Gauge.LockResonance
open Measurement

/-- The fringe with the stepped path driven to count `n` (the compensation ladder). -/
def fringeAt (n : Nat) : Nat :=
  let stepped := AlphaBFGS.invAlphaAt (AlphaBFGS.bfgsAt n AlphaBFGS.d0)
  let direct  := CalibrationTwoPaths.direct_1to3
  if direct ≥ stepped then direct - stepped else stepped - direct

#eval s!"[LOCK RESONANCE — the Pound–Rebka ladder] fringe at count 2 = {fringeAt 2}"
#eval s!"[LOCK RESONANCE] fringe at count 3 = {fringeAt 3}   (the (ii-b) reference reading)"
#eval s!"[LOCK RESONANCE] fringe at count 4 = {fringeAt 4}"
#eval s!"[LOCK RESONANCE] contraction 2→3 = {if fringeAt 2 ≥ fringeAt 3 then fringeAt 2 - fringeAt 3 else 0} ; contraction 3→4 = {if fringeAt 3 ≥ fringeAt 4 then fringeAt 3 - fringeAt 4 else 0} — LOCK = the ladder contracts at the fencepost; the floor is the measured width, not an asserted epsilon"

end Measurement.Gauge.LockResonance
