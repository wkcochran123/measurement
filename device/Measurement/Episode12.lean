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

--| THE LAGRANGE READING.  UNIVERSAL says the train of thought is not Newton's calculus but
--| Lagrange's: a non-linear relation between the function, the derivative and the SECOND
--| derivative -- and that the operator is a derivation in the language of algebra.  That is
--| the whole story, because D is a derivation and D-squared is NOT: its Leibniz defect is
--| the cross term, two times Da times Db.  That is the higher-order term that refuses to
--| cancel, and the two in it is the slip at two.
--|
--| So read the jar again carrying `once_around` AND `twice_around` -- f, f' and f''.  For a
--| quadratic f'' is exactly funge times quadA, constant, so the second derivative costs
--| nothing to know.  Newton needs five turns to land.  This needs three.  The slip allows
--| four.  Carrying the second derivative is precisely what fits the whole reading inside
--| the slip; dropping it is what leaves you almost, but not quite.
--| FOR THE WRITING: "the number 4 is a path THROUGH the number 3", measured in Lean, not simulated.  Fold this crank from the jar and watch:
--|
--|     lagrange x2  137.011290527013905233309938      newton x3  137.011290807319124540443729
--|     lagrange x3  137.011290548979457087737301      newton x4  137.011290548979457793403451
--|     lagrange x4  137.011290548979457087737301      newton x5  137.011290548979457087737300
--|
--| Carrying f'' the answer arrives at THREE and the fourth turn passes straight through it without moving -- the slip allows four, and four is
--| the path through three.  Drop f'' and there is nothing at three to pass through: at four Newton is still en route, which is Euler-Lagrange
--| flopping exactly as advertised.  The residue is one unit in the last place, and that much is OBSERVED and not explained.
def lagrangeReadingScaled : Int :=
  (List.replicate theSlipAtTwo ()).foldl
    (fun x _ =>
      let s   := (theScale : Int)
      let f   := (quadA : Int) * x * x - (quadB : Int) * x * s + (quadC : Int) * s * s
      let fp  := (funge : Int) * (quadA : Int) * x - (quadB : Int) * s
      let fpp := (funge : Int) * (quadA : Int)
      x - ((funge : Int) * f * fp) / ((funge : Int) * fp * fp - f * fpp))
    (jarSeed : Int)

def lagrangeReading :=
  let s := (toString lagrangeReadingScaled).toList
  String.ofList (s.take (s.length - thePlaces)) ++ "." ++
  String.ofList (s.drop (s.length - thePlaces))

--| THE JAR, FROM EPISODE EIGHT.  The previous probe sampled `ULift` stacked n deep on
--| `Number` -- a TYPE, and nothing besides.  That is a control, and I named it too
--| generously: a type expression carries no evidence, while the ladder's rungs carry
--| `register_value`, `universe_id` and a `galley`.  Measuring the container of one field's
--| type is not measuring the record.  Two further things that comment got wrong: `ULift`
--| is `ULift.{r,s} (α : Type s) : Type (max s r)`, so wrapping it does NOT force a
--| successor universe unless the levels are pinned -- the controlled axis was nesting
--| DEPTH, not universe level -- and agreeing totals do not make agreeing profiles.
--|
--| So the sample starts where Episode 8 already started, from the jar it built:
--|
--|     theJar = .superposition theOriginFact (.bang _ (.color _ theArea)) (.color _ theArea)
--|
--| A constructor tree with Facts in it: the superposition's two roots, one branch a step
--| deeper than the other.  And `Jar.le` must WALK it, including the arm that returns
--| `¬ le j1' j2'` when both decisions come back false.  Comparing jars is work on
--| evidence.  Elaborating `ULift` was work on notation.
private def jarAt (n : Nat) : TermElabM (TSyntax `term) := do
  let mut s ← `(Measurement.theJar)
  for _ in [0:n] do
    s ← `(Measurement.Jar.bang Measurement.theOriginFact $s)
  pure s

--| ONE RUNG, RAW.  Blank and sample both kept, unsubtracted and unclipped.  `Nat`
--| subtraction truncates at zero, so doing the arithmetic here silently erases every
--| decrease -- and a decrease is precisely what this experiment exists to detect.  The old
--| `if h > b then h - b else 0` reported three leading zeros and threw away how far below
--| the blank they sat.  Store what was read; derive the differences later, in `Int`.
private def jarPair (n : Nat) : TermElabM (Nat × Nat) := do
  let b ← blank
  let h ← sample (← `(Measurement.Jar.le $(← jarAt n) Measurement.theJar))
  pure (b, h)

--| BOTH WALKS, THEN PUBLISH.  Up and down inside ONE command, with nothing emitted in
--| between.  The previous version published two declarations before the descending pass
--| began, so the second walk ran in a larger environment and the two passes differed by
--| more than their order.  Now they differ by their order and by nothing else.
elab "monte_walk " up:ident upb:ident dn:ident dnb:ident : command => do
  let (ub, uh, db, dh) ← liftTermElabM do
    let mut ub : Array Nat := #[]
    let mut uh : Array Nat := #[]
    for n in [0:36] do
      let (b, h) ← jarPair n
      ub := ub.push b
      uh := uh.push h
    let mut db : Array Nat := #[]
    let mut dh : Array Nat := #[]
    for i in [0:36] do
      let (b, h) ← jarPair (35 - i)
      db := db.push b
      dh := dh.push h
    pure (ub, uh, db.reverse, dh.reverse)
  elabCommand (← `(def $up  : List Nat := $(Lean.quote uh.toList)))
  elabCommand (← `(def $upb : List Nat := $(Lean.quote ub.toList)))
  elabCommand (← `(def $dn  : List Nat := $(Lean.quote dh.toList)))
  elabCommand (← `(def $dnb : List Nat := $(Lean.quote db.toList)))

monte_walk theRawUp theBlankUp theRawDown theBlankDown

--| EVERYTHING DERIVED, IN `Int`, WHERE A DECREASE IS ALLOWED TO BE ONE.
def corrected (h b : List Nat) : List Int :=
  (h.zip b).map (fun p => (p.1 : Int) - (p.2 : Int))
def signedSteps (xs : List Int) : List Int :=
  (xs.zip xs.tail).map (fun p => p.2 - p.1)

def theSizesUp   : List Int := corrected theRawUp   theBlankUp
def theSizesDown : List Int := corrected theRawDown theBlankDown

--| THE COLUMN THE NESTING DOES NOT FORCE.  A deeper jar contains a shallower one, so a
--| rising total is forced by the construction and demonstrates nothing at all.  Whether
--| the INCREMENT rises is not forced, and that is the reading.
def theStepsUp   : List Int := signedSteps theSizesUp
def theStepsDown : List Int := signedSteps theSizesDown

--| THE EXPERIMENT -- and it is NOT the totals.  Two different profiles can share a total:
--| [100,200,300] and [110,180,310] both sum to six hundred and disagree at every rung.
--| This is the rung-by-rung disagreement between the two walks, and it is the apparatus.
def thePassGap : List Int :=
  (theSizesUp.zip theSizesDown).map (fun p => p.1 - p.2)


--| ============================================================================
--| THE SECOND LADDER.  The jar walk measured nesting depth on a type whose `le`
--| has a `¬ le` arm -- work on evidence.  This one measures a DERIVATIVE ORDER.
--| `Variation` has three constructors and Episode 4 never says why three.  Write
--| the residual as a quadratic, D(u) = Lu + B(u,u) - f with B bilinear:
--|
--|     D D(u)[h]   = Lh + B(h,u) + B(u,h)    one direction   -- .the_gateaux
--|     D²D(u)[h,k] = B(h,k) + B(k,h)         two directions  -- .the_frechet
--|     D³D         = 0                       nothing left    -- no fourth constructor
--|
--| The hierarchy terminates at three because the operator is quadratic.  That is a
--| claim about COST, so the meter is what adjudicates it.
--| ============================================================================

def theNewtonRung : Variation := .the_newton theGospel True

--| THE CONTROL.  No second derivative anywhere.  `Variation.newton` and
--| `Variation.krylov` are the SAME function on this ladder -- their `.the_gateaux`
--| arms agree (Episode08) -- so any cost difference between the two readings below
--| is the meter measuring a name, and there should not be one.
def gateauxAt : Nat → Variation
  | 0     => theNewtonRung
  | n + 1 => .the_gateaux theGospel True True (gateauxAt n)

--| THE EXPERIMENT.  One second derivative per rung, and the two arguments of the
--| bilinear map are made DIFFERENT on purpose: `before` continues the frechet
--| chain, `after` is the gateaux chain of the same depth.  `Variation.newton` takes
--| `before` and drops `after`; `Variation.krylov` takes both.  The gap between the
--| readings is the cost of the second slot of B -- the argument a Jacobian-vector
--| product never supplies and a matrix-free Krylov step does.
def frechetAt : Nat → Variation
  | 0     => theNewtonRung
  | n + 1 => .the_frechet theGospel True True True (frechetAt n) (gateauxAt n)

--| WHY THE LENGTHS ARE WRITTEN OUT.  `Variation.le` carries `termination_by`
--| (Episode04), so it is well-founded, compiles through `WellFounded.fix`, and does
--| NOT reduce under `whnf` -- sampling it would read the blank.  `newton` and
--| `krylov` are structural and do reduce, but `whnf` on a list stops at the head
--| cons.  So the forcing is Episode 13's: `decide` on a decidable Prop, which must
--| run its instance to a Bool.  `Nat.decEq` bails the moment one spine ends, so the
--| literal has to be the EXACT length or the walk is only partly forced.  Those
--| literals are the ladder's own arithmetic -- spine n+1, branch krylov
--| 1 + n(n+3)/2 -- bookkeeping, not the measurement.  The measurement is heartbeats.
elab "variation_walk " a:ident ab:ident b:ident bb:ident c:ident cb:ident d:ident db:ident
    : command => do
  let (sn, snb, sk, skb, bn, bnb, bk, bkb) ← liftTermElabM do
    let mut sn : Array Nat := #[]; let mut snb : Array Nat := #[]
    let mut sk : Array Nat := #[]; let mut skb : Array Nat := #[]
    let mut bn : Array Nat := #[]; let mut bnb : Array Nat := #[]
    let mut bk : Array Nat := #[]; let mut bkb : Array Nat := #[]
    for n in [0:12] do
      let spine := n + 1
      let branch := 1 + n * (n + 3) / 2
      let b0 ← blank
      let h0 ← sample (← `(decide ((Measurement.Variation.newton
                    (Measurement.gateauxAt $(Lean.quote n))).length = $(Lean.quote spine))))
      snb := snb.push b0; sn := sn.push h0
      let b1 ← blank
      let h1 ← sample (← `(decide ((Measurement.Variation.krylov
                    (Measurement.gateauxAt $(Lean.quote n))).length = $(Lean.quote spine))))
      skb := skb.push b1; sk := sk.push h1
      let b2 ← blank
      let h2 ← sample (← `(decide ((Measurement.Variation.newton
                    (Measurement.frechetAt $(Lean.quote n))).length = $(Lean.quote spine))))
      bnb := bnb.push b2; bn := bn.push h2
      let b3 ← blank
      let h3 ← sample (← `(decide ((Measurement.Variation.krylov
                    (Measurement.frechetAt $(Lean.quote n))).length = $(Lean.quote branch))))
      bkb := bkb.push b3; bk := bk.push h3
    pure (sn, snb, sk, skb, bn, bnb, bk, bkb)
  elabCommand (← `(def $a  : List Nat := $(Lean.quote sn.toList)))
  elabCommand (← `(def $ab : List Nat := $(Lean.quote snb.toList)))
  elabCommand (← `(def $b  : List Nat := $(Lean.quote sk.toList)))
  elabCommand (← `(def $bb : List Nat := $(Lean.quote skb.toList)))
  elabCommand (← `(def $c  : List Nat := $(Lean.quote bn.toList)))
  elabCommand (← `(def $cb : List Nat := $(Lean.quote bnb.toList)))
  elabCommand (← `(def $d  : List Nat := $(Lean.quote bk.toList)))
  elabCommand (← `(def $db : List Nat := $(Lean.quote bkb.toList)))

variation_walk theRawSpineN theBlankSpineN theRawSpineK theBlankSpineK
               theRawBranchN theBlankBranchN theRawBranchK theBlankBranchK

--| DERIVED IN `Int`, WHERE A DECREASE IS ALLOWED TO BE ONE.  `corrected` and
--| `signedSteps` are the jar walk's, unchanged.
def theSpineN  : List Int := corrected theRawSpineN  theBlankSpineN
def theSpineK  : List Int := corrected theRawSpineK  theBlankSpineK
def theBranchN : List Int := corrected theRawBranchN theBlankBranchN
def theBranchK : List Int := corrected theRawBranchK theBlankBranchK

--| THE CONTROL COLUMN.  Same ladder, same walk, two names.  If this is not flat the
--| instrument is reading the identifier and nothing below is worth anything.
def theNameGap : List Int :=
  (theSpineK.zip theSpineN).map (fun p => p.1 - p.2)

--| THE SECOND SLOT OF B.  Rung by rung, what keeping `after` costs over dropping it.
def theBilinearGap : List Int :=
  (theBranchK.zip theBranchN).map (fun p => p.1 - p.2)

--| THE READING.  Not the totals -- a deeper ladder contains a shallower one, so a
--| rising total is forced by construction and demonstrates nothing.  The INCREMENT
--| is not forced.  If the operator is quadratic the second derivative is constant,
--| so the branch increment should SETTLE rather than climb, and no rung should show
--| a third order of cost arriving.
def theBranchSteps : List Int := signedSteps theBranchK
def theGapSteps    : List Int := signedSteps theBilinearGap


end Measurement

--| THE PRACTICE READOUT.  The bracket, the slip, and the verdict on whether there is any
--| point turning the crank again.
--| WHAT `lake_build` SEES, AND WHAT IT CANNOT.  UNIVERSAL carries `once_around` and
--| `twice_around`, and then hands them to a function that throws them both away:
--|
--|     lake_build : SpaceTimePath → SpaceTimePath → Prop := fun _ _ => ...
--|
--| `fun _ _`.  It never looks at the paths.  In logic the two routes are not distinguished
--| at all -- the quarter is glued down, you look under the middle card, and it is the same
--| fact whichever way you went round.  That is what lets you use either calculus like
--| algebra: D or D squared, Newton or Lagrange, one answer.  Boolean algebra, at that --
--| the device's own.  Episode 5 line 30 is `A = NOT (NOT X AND Y)`, which is implication,
--| and implication is exactly how `Closure.branch_and_compare` orders one slip against
--| another: `| some p, some q => p → q`.  The calculus comes back down to the one gate.
--|
--| The meter is not so easily fooled.  Once around, stopped at the slip, parts company at
--| the nineteenth character.  Twice around, stopped at the same slip, agrees to
--| twenty-three decimals and differs in the twenty-fourth by exactly one.  `lake_build`
--| says those are the same fact and it is right; the readings say they are not the same
--| number and they are also right.  The gap between a constant function and a reading is
--| not an error.  It is the slip, and a function that discards its arguments was never
--| going to be able to see it.

--| THE THREE READINGS, SIDE BY SIDE.  The short way went all the way and got a point.  The
--| long way stopped at the slip and got almost, but not quite, the same point -- which is
--| the honest answer, because the bracket was never a point to begin with.
/-#eval "short way, all the way  : " ++ Measurement.theReading
#eval "off the jar, newton   : " ++ Measurement.jarReading
#eval "off the jar, lagrange : " ++ Measurement.lagrangeReading

#eval s!"jar [{Measurement.jarLo}..{Measurement.jarHi}] span {Measurement.jarSpan} " ++
      s!"reach {Measurement.jarReach} floor {Measurement.Calibration.measuredFloor} " ++
      s!"bracketed_at_the_slip {Measurement.bracketed_at_the_slip}"

--| THE SIZE READOUT.  Thirty-six rungs, each measured against its own blank, and the sum.
--| This is the first number in the file that no formula produced: the strip, the jar, the
--| coefficients and the folds are all structural, but these are what the elaborator spent.
#eval Measurement.theSizesUp
#eval Measurement.theSizesDown
#eval Measurement.theStepsUp
#eval Measurement.theStepsDown
#eval Measurement.thePassGap
-/
