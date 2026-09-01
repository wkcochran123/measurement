/-
__Measurement: The Tragedy of John Henry__
__A Satire in Look Ahead Backus-Naur Form__

_This is a gentle reminder that an instrument which has not been zeroed is a rumour._

(c) 2026

__EPISODE 12__: _MONTE PRACTICE_

-/

--| Episode 8 closed the short way with a polynomial: write down a residual whose root is
--| the constant, seed it with the strip, turn the crank.  That is sufficiency, and it is
--| honest as far as it goes, but a formula will always be a formula somebody wrote.
--|
--| This is the practice run for the long way.  Here nobody writes the number down.  The
--| coin is what the elaborator actually spent, and the only move allowed is to read the
--| meter.  The device cannot read its own meter -- probe and tolerance are the same act --
--| so the reading lives out here, in a command, and hands its answer back in as an
--| ordinary def.  That is the one shape that works, and Calibration has been demonstrating
--| it since `register_noise_floor`.
--|
--| And there is one thing the meter may never do, which took me three tries to see.
import Measurement.Episode08
import Measurement.Episode11

open Lean Elab Command Term Meta

namespace Measurement

/-!
### YOU CANNOT GO ALL THE WAY

`.same` is the arm the spec always marked _converged, which is exact in logic_.  Exact in
LOGIC.  Episode 8 reaches it, and reaches it honestly, by `rfl` on the ground floor where
both stanzas are `theOriginFact` and `decTruth` is `isTrue rfl`.  Nothing was measured.

A meter can never get there.  A meter has a floor, and the floor is the slip -- the same
slip Episode 11 pays climbing past OBSERVED, the `projection` with no upstream source that
whoever climbs must supply.  Below the floor the instrument is not reading the world, it is
reading itself.  So the metered turn stops one arm short, on this side of the slip, and
what it stops at is `.different` -- which is not a failure to converge, it is the shape the
answer actually has.  Look at what `Closure.le` calls that constructor's two `Bullshit`
slots and the device has been saying so since Episode 5:

    .different stanza lower_bound slip_bound _

Lower bound and SLIP bound.  A bracket, and the far wall is named after the thing that
stops you reaching it.  `.same` collapses a bracket to a point; only logic may do that.
-/

--| THE FROZEN OPERATOR, AND THE BRACKET IT CARRIES.  Episode 8 showed the jar's two walls
--| are Newton iterates 0 and 1: from 1296/10 the step is exactly -8.1, and 81 is tange to
--| the fourth.  Frozen, it stops the iteration chasing its own tail -- a preconditioner may
--| change the iteration, never the answer.
def jarLo    := theSlipAtTwo * theRadius * theRadius
def jarHi    := jarLo + tange * tange * tange * tange
def jarSpan  := jarHi - jarLo
def jarRef   := jarLo * theBase
def jarReach := jarSpan * theBase

--| THE SLIP, IN THE ONLY UNITS THAT MATTER.  The bracket is eight hundred and ten wide at
--| the meter's scale.  The floor is three thousand and seventeen.  The bracket is already
--| finer than the instrument that would narrow it, so there is nothing left to do: you are
--| on this side of the slip point, and you stop.  Not because the crank converged.  Because
--| turning it again would be reading the noise and calling it a digit.
def bracketed_at_the_slip : Bool := jarReach < Calibration.measuredFloor

--| THE BLANK.  The meter drifts.  Elaborate the same term twice and the second reading is
--| the larger, because the environment it was measured in grew in between.  An uncorrected
--| ladder therefore "converges" by warming up, which is a measurement of nothing at all.
--| So every sample is drawn against a blank taken in the same breath and the reading is the
--| difference.  Oldest trick in the lab, and the only reason the numbers below mean
--| anything -- the blank sits flat while the sample climbs, which is how you learn the
--| climb was structure and not the apparatus.
private def blank : TermElabM Nat := do
  let stx ← `(Fact.Truth.decTruth)
  let (_, hb) ← withHeartbeats do
    let e ← elabTerm stx none; let _ ← Meta.whnf e; pure ()
  pure hb

private def sample (s : TSyntax `term) : TermElabM Nat := do
  let (_, hb) ← withHeartbeats do
    let e ← elabTerm s none; let _ ← Meta.whnf e; pure ()
  pure hb

--| READ THE NUMBER OFF THE JAR.  Episode 8 seeded the strip and turned the crank once per
--| cell of it -- a hundred and one folds for an answer that lands in seven, which is to say
--| it went all the way.  It could: it was working in logic, where going all the way is
--| free.  Out here you cannot.  You seed the JAR, whose low wall Episode 8 showed is Newton
--| iterate zero, and you turn the crank SLIP-many times -- four, `theSlipAtTwo`, the card
--| named after the thing that stops you -- and then you stop, on this side of the slip
--| point, with the bracket still open.  Nobody chose four.  Four is the slip.
def jarSeed := jarLo * theScale / theBase

def jarReadingScaled :=
  (List.replicate theSlipAtTwo ()).foldl
    (fun x _ => (quadA * x * x - quadC * theScale * theScale)
                  / (funge * quadA * x - quadB * theScale))
    jarSeed

def jarReading :=
  let s := (toString jarReadingScaled).toList
  String.ofList (s.take (s.length - thePlaces)) ++ "." ++
  String.ofList (s.drop (s.length - thePlaces))

--| THE TURN, DRIVEN BY THE METER.  Three arms, not four.  And what it reads is the
--| PRESS VERDICT -- the seam's exit -- not the closure we built on the short way.  That
--| was our own artifact; measuring it only ever told us about us.  `pressCheck` reads the
--| head once and reports whether it SLIPPED, which is not the same as getting through the
--| mountain, and its two Numbers are the two bounds.  `PressVerdict` IS the bracket: that
--| is why `.different` carries two slots and the far one is called `slip_bound`.
--|
--| The stopping test needs no reference anybody chose.  Two readings of the same verdict
--| that agree to within the floor ARE the bracket -- there is nothing finer to see, so you
--| stop.  Wider than the floor and the seam is still moving.  Narrower is not available:
--| below the floor the instrument is reading itself.
elab "practice_turn " nm:ident " after " prev:term : command => do
  let (b, h, before) ← liftTermElabM do
    let b ← blank
    let h ← sample (← `(Measurement.pressCheck))
    --| the turn before spliced its reading in as a def; read it back out
    let p ← Meta.whnf (← elabTerm prev none)
    pure (b, h, p.rawNatLit?.getD 0)
  let reading := if h > b then h - b else 0        --| the blank comes off the sample
  let floor   := Calibration.measuredFloor
  let drift   := if reading > before then reading - before else before - reading
  let arm := if before == 0 then "inferred" else if drift <= floor then "different" else "inferred"
  logInfo s!"blank {b}  verdict {h}  reading {reading}  previous {before}  drift {drift}  floor {floor}  -> {arm}"
  let body ← match arm with
    | "different" => `(Closure.different theOriginFact theBullshit theBullshit (some True))
    | _           => `(Closure.inferred theOriginFact theOriginFact theBullshit theBullshit
                         (some True) theClosure)
  let rd := Lean.mkIdent (Lean.Name.mkSimple (nm.getId.toString ++ "_reading"))
  elabCommand (← `(def $rd : Nat := $(Lean.quote reading)))
  elabCommand (← `(noncomputable def $nm :
    Closure.{0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0} := $body))

--| THE PRACTICE.  Each turn reads the verdict again and compares it with the last reading,
--| which the turn before spliced in.  Nothing here is a number anybody typed.
practice_turn practice1 after 0
practice_turn practice2 after practice1_reading
practice_turn practice3 after practice2_reading
practice_turn practice4 after practice3_reading

end Measurement

--| THE PRACTICE READOUT.  The bracket, the slip, and the verdict on whether there is any
--| point turning the crank again.
--| THE TWO READINGS, SIDE BY SIDE.  The short way went all the way and got a point.  The
--| long way stopped at the slip and got almost, but not quite, the same point -- which is
--| the honest answer, because the bracket was never a point to begin with.
#eval "short way, all the way  : " ++ Measurement.theReading
#eval "off the jar, at the slip: " ++ Measurement.jarReading

#eval s!"jar [{Measurement.jarLo}..{Measurement.jarHi}] span {Measurement.jarSpan} " ++
      s!"reach {Measurement.jarReach} floor {Measurement.Calibration.measuredFloor} " ++
      s!"bracketed_at_the_slip {Measurement.bracketed_at_the_slip}"
