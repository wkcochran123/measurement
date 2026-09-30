/-
__Measurement: The Tragedy of John Henry__
__A Satire in Look Ahead Backus-Naur Form__

_This is a gentle reminder that an instrument which has not been zeroed is a rumour._

(c) 2026

__EPISODE 12__: _Let Him Cook. . . . . . . Levin_

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
both stanzas are `zero` and `click` is `isTrue rfl`.  Nothing was measured.

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
def jarLo    := the_orbital_data_points * theRadius * theRadius
def jarHi    := jarLo + the_satire.tange.length * the_satire.tange.length * the_satire.tange.length * the_satire.tange.length
def jarSpan  := jarHi - jarLo
def jarRef   := jarLo * theBase
def jarReach := jarSpan * theBase

--| THE SLIP, IN THE ONLY UNITS THAT MATTER.  The bracket is eight hundred and ten wide at
--| the meter's scale.  The floor is three thousand and seventeen.  The bracket is already
--| finer than the instrument that would narrow it, so there is nothing left to do: you are
--| on this side of the slip point, and you stop.  Not because the crank converged.  Because
--| turning it again would be reading the noise and calling it a digit.
--| THE STIFFNESS VERDICT.  A bracket already finer than the instrument that would narrow it is what "stiff" means numerically:
--| the constraint is being carried exactly, and the step that would relax it costs more than the resolution it would buy.
--| Episode 5 named the two ends of this in the vocabulary before the physics had a word for them: `Closure.same` is the
--| constraint met exactly -- the multiplier, elliptic, instantaneous, incompressible -- and `Closure.different lower_bound
--| slip_bound` is the bracket a penalty leaves -- finite signal speed, hyperbolic, compressible.  Same equations, one
--| parameter, and the parameter is a wave speed (Ep4's Λ-for-c).  This Bool is which side of it the meter is standing on.
def bracketed_at_the_slip : Bool := jarReach < Calibration.measuredFloor

--| THE BLANK.  The meter drifts.  Elaborate the same term twice and the second reading is
--| the larger, because the environment it was measured in grew in between.  An uncorrected
--| ladder therefore "converges" by warming up, which is a measurement of nothing at all.
--| So every sample is drawn against a blank taken in the same breath and the reading is the
--| difference.  Oldest trick in the lab, and the only reason the numbers below mean
--| anything -- the blank sits flat while the sample climbs, which is how you learn the
--| climb was structure and not the apparatus.
private def blank : TermElabM Nat := do
  let stx ← `(FACT.Truth.click)
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
--| iterate zero, and you turn the crank SLIP-many times -- four, `the_orbital_data_points`, the card
--| named after the thing that stops you -- and then you stop, on this side of the slip
--| point, with the bracket still open.  Nobody chose four.  Four is the slip.
def jarSeed := jarLo * theScale / theBase

def jarReadingScaled :=
  (List.replicate the_orbital_data_points ()).foldl
    (fun x _ => (quadA * x * x - quadC * theScale * theScale)
                  / (the_basis.funge.length * quadA * x - quadB * theScale))
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
  (List.replicate the_orbital_data_points ()).foldl
    (fun x _ =>
      let s   := (theScale : Int)
      let f   := (quadA : Int) * x * x - (quadB : Int) * x * s + (quadC : Int) * s * s
      let fp  := (the_basis.funge.length : Int) * (quadA : Int) * x - (quadB : Int) * s
      let fpp := (the_basis.funge.length : Int) * (quadA : Int)
      x - ((the_basis.funge.length : Int) * f * fp) / ((the_basis.funge.length : Int) * fp * fp - f * fpp))
    (jarSeed : Int)

def lagrangeReading :=
  let s := (toString lagrangeReadingScaled).toList
  String.ofList (s.take (s.length - thePlaces)) ++ "." ++
  String.ofList (s.drop (s.length - thePlaces))

--| THE JAR, FROM EpisodE EIGHT.  The previous probe sampled `ULift` stacked n deep on
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
--|     the_worldline = .superposition zero (.bang _ (.color _ path_along_ast)) (.color _ path_along_ast)
--|
--| A constructor tree with FACTs in it: the superposition's two roots, one branch a step
--| deeper than the other.  And `Jar.le` must WALK it, including the arm that returns
--| `¬ le j1' j2'` when both decisions come back false.  Comparing jars is work on
--| evidence.  Elaborating `ULift` was work on notation.
private def jarAt (n : Nat) : TermElabM (TSyntax `term) := do
  let mut s ← `(Measurement.the_worldline)
  for _ in [0:n] do
    s ← `(Measurement.Jar.bang Measurement.zero $s)
  pure s

--| ONE RUNG, RAW.  Blank and sample both kept, unsubtracted and unclipped.  `Nat`
--| subtraction truncates at zero, so doing the arithmetic here silently erases every
--| decrease -- and a decrease is precisely what this experiment exists to detect.  The old
--| `if h > b then h - b else 0` reported three leading zeros and threw away how far below
--| the blank they sat.  Store what was read; derive the differences later, in `Int`.
private def jarPair (n : Nat) : TermElabM (Nat × Nat) := do
  let b ← blank
  let h ← sample (← `(Measurement.Jar.le $(← jarAt n) Measurement.the_worldline))
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

def theNewtonRung : Variation := .the_newton grift True

--| THE CONTROL.  No second derivative anywhere.  `Variation.newton` and
--| `Variation.krylov` are the SAME function on this ladder -- their `.the_gateaux`
--| arms agree (Episode08) -- so any cost difference between the two readings below
--| is the meter measuring a name, and there should not be one.
def gateauxAt : Nat → Variation
  | 0     => theNewtonRung
  | n + 1 => .the_gateaux grift True True (gateauxAt n)

--| THE EXPERIMENT.  One second derivative per rung, and the two arguments of the
--| bilinear map are made DIFFERENT on purpose: `before` continues the frechet
--| chain, `after` is the gateaux chain of the same depth.  `Variation.newton` takes
--| `before` and drops `after`; `Variation.krylov` takes both.  The gap between the
--| readings is the cost of the second slot of B -- the argument a Jacobian-vector
--| product never supplies and a matrix-free Krylov step does.
def frechetAt : Nat → Variation
  | 0     => theNewtonRung
  | n + 1 => .the_frechet grift True True True (frechetAt n) (gateauxAt n)

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

--| THE SECOND SLOT OF B, WHICH IS THE CONVECTIVE TERM.  Rung by rung, what keeping `after` costs over dropping it.  The
--| second argument of B(u,u) is u·∇u -- the nonlinearity, the slot a Jacobian-vector product never supplies and a matrix-free
--| Krylov step does.  So this column is the cost of the nonlinearity, measured without the meter knowing what it is a
--| nonlinearity OF.  It cannot know: the electron only ever sees the variational form, one derivative and one second
--| derivative along its own worldline, and which field produced the action is upstream of the derivative and does not
--| survive it.  Variationally, QCD is all the same to the electron.
def theConvectiveGap : List Int :=
  (theBranchK.zip theBranchN).map (fun p => p.1 - p.2)

--| THE READING.  Not the totals -- a deeper ladder contains a shallower one, so a
--| rising total is forced by construction and demonstrates nothing.  The INCREMENT
--| is not forced.  If the operator is quadratic the second derivative is constant,
--| so the branch increment should SETTLE rather than climb, and no rung should show
--| a third order of cost arriving.
def theBranchSteps : List Int := signedSteps theBranchK
def theGapSteps    : List Int := signedSteps theConvectiveGap


--| Cook's theorem takes a machine and an input and hands back a FORMULA: satisfiable
--| exactly when the machine accepts.  The construction is a tableau -- time down the page,
--| tape across it -- and four groups of clauses saying that each cell holds one symbol,
--| that the first row is the input, that every row follows from the one above by a local
--| window, and that some row accepts.
--|
--| Every one of those objects is already in this device, and none of them was built for
--| this.  The tableau is Episode 11: thirty-six rungs, each `TYPESET Box Pigeon n Lifted`
--| requiring `[below: TYPESET Box Pigeon (n-1) _]`, carrying a `the_page : ThePreprint`.
--| Row n from row n-1, with a tape.  The window is the rung's own head match.  And the
--| conjunctive normal form is Episode 3's arithmetic, which has been sitting there since
--| the first act wearing the names of areas and lengths:
--|
--|     Sum.add     : FACT → Area → Area → Sum → Sum          two literals, disjoined
--|     Product.mul : FACT → Sum  → Sum  → Product → Product  two clauses, conjoined
--|
--| A Product of Sums is a CNF formula.  Nobody arranged that; multiplication distributing
--| over addition IS conjunction distributing over disjunction, and the device wrote down
--| the first because it was doing geometry.
--|
--| NOTE ON WHAT THIS FILE IMPORTS.  Episode 11 and nothing above it.  Episode 12 is the
--| meter -- it measures what elaboration spent -- and Cook is not a measurement.  The
--| reduction needs the tableau, the transition, and the formula.  It does not need to know
--| what any of them cost.  That question comes back later, and when it does it is the
--| SECOND half of Cook: not that the formula exists, but that it is polynomial.  Episode
--| 12 is the instrument for that, and it is deliberately not in scope here.

/-!
### THE LITERAL, AND WHY IT IS AN AREA

A literal is a variable or its negation, and the only thing a reduction ever does with one
is put it in a clause.  Episode 8 already carded the atom: `path_along_ast`, built from the origin
fact and the origin page.  A literal here is not a new kind of thing.  It is the smallest
thing the device agreed to hold, which is what a literal is supposed to be.
-/
--| MINTED HERE, NOT BORROWED.  Episode 8 already carries `zero`, `path_along_ast` and
--| `theSum`, and the obvious move is to import Episode 8 and use them.  That would be
--| wrong, and the import graph says why: Episode 9 imports Episode SEVEN.  The long way
--| branches off before the short way exists and never rejoins it -- Episode 12 is the only
--| file that pulls both, and it pulls both because it is comparing them.
--|
--| So Cook takes nothing from the short way.  These four lines rebuild the atoms from the
--| origin fact, which is Episode 1, which everything has.  A reduction that quietly needed
--| the answer would not be a reduction.
def cookFACT : FACT := FACT.Truth
def cookPage : Number := .zero cookFACT
def aLiteral : Area := .dt cookFACT cookPage (.tree cookFACT)

--| THE CLAUSE.  `Sum.add` disjoins two areas onto an accumulator, and terminates in
--| `.zero`, which is the empty disjunction -- false, correctly, since an empty OR is.
def aClause : Sum := .add cookFACT aLiteral aLiteral (.zero True aLiteral)

/-!
### THE FOUR CONJUNCTS

Cook's formula is φ_cell ∧ φ_start ∧ φ_move ∧ φ_accept, and each conjunct is a group of
clauses, which is to say each is a `Product`.  The device gives three ways to be one:

    Product.origin : FACT → Product              the empty conjunction -- vacuously true
    Product.one    : Prop → Sum → Product        a single clause
    Product.mul    : FACT → Sum → Sum → Product → Product

and the four conjuncts want exactly those shapes, in that order of weight.
-/

--| EACH CELL HOLDS ONE SYMBOL.  Two clauses: at least one symbol, and not two.  That is
--| the only conjunct that needs both halves of a `mul`, and it is the one everybody
--| forgets when they write the proof out on a board.
def phi_cell : Product := .mul cookFACT aClause aClause (.one True aClause)

--| THE FIRST ROW IS THE INPUT.  One clause, because the input is given and there is
--| nothing to choose.  `TYPESET_origin` is this conjunct: rung one, `Number` unlifted,
--| the register just the carrier's own value.  Steel starts as a local receipt.
def phi_start : Product := .one True aClause

--| EVERY ROW FOLLOWS FROM THE ONE ABOVE.  This is the whole content of the reduction and
--| it is already an instance signature: `TYPESET_page_n` cannot be built without
--| `[below: TYPESET Box Pigeon (n-1) _]` in hand.  The window is the rung's head match --
--| three tape constructors, three arms, one pair of facts out:
--|
--|     | .introduction f _        => (f, Pigeon.symbol)
--|     | .methodology  c s _ _ _  => (c, s)
--|     | .results      c s _ _ _ _ _ => (c, s)
--|
--| Exactly one arm fires.  That is φ_cell holding for the tape head, proved by the match
--| being exhaustive rather than by a clause anybody wrote.
def phi_move : Product := .mul cookFACT aClause aClause (.one True aClause)

--| SOME ROW ACCEPTS.  Empty, and that is not a shortcut.  Acceptance in this device is not
--| a clause you add; it is whether the last rung can be built at all.  `pressCheck` reads
--| the head and returns `¬(c.truth ↔ s.truth)` -- exclusive or, the one gate that is not
--| monotone -- and the verdict is a reading, not a constraint.  So the conjunct is
--| `.origin`: nothing is asserted, and the acceptance condition lives in whether an
--| instance exists.  Which is the whole point of a reduction, and also its cost.
def phi_accept : Product := .origin cookFACT

/-!
### THE FORMULA

Four conjuncts, terminated by the null space.  `Basis.null_space` is the right ending and
not a convenience: the empty conjunction is true, the unconstrained directions are exactly
the ones no clause touches, and the satisfying assignments of a constraint system ARE its
null space.  The device named that constructor while doing linear algebra and it means the
same thing here.
-/
def phi : Basis :=
  .basis cookFACT phi_cell phi_start
    (.basis cookFACT phi_move phi_accept
      (.null_space cookFACT))

--| THE REDUCTION.  A `Polynomial` over the formula -- which is what a reduction is: the
--| formula, in the size of the input, to a power somebody has to bound.
def theReduction : Polynomial :=
  .factor cookFACT phi phi (.monomial True phi)

/-!
### WHAT IS EXHIBITED HERE, AND WHAT IS NOT

Exhibited: the encoding.  Four conjuncts, each a `Product` of `Sum`s of `Area`s, assembled
into one `Basis` and carried by a `Polynomial`.  Every constructor is Episode 3's and every
atom is Episode 8's.  Nothing was built for this file, which is the only reason it is short.

NOT exhibited, and it should be said plainly rather than left for a reader to notice: the
correspondence itself.  Cook's theorem is

    φ is satisfiable   ⟺   the machine accepts

and the device's version of the right-hand side is `∃ inst, TYPESET Prop truthCarrier 36 _`
-- an instance search, and that search does not close ON ITS OWN.  It fails STRUCTURALLY --
-- exhausted in a fifth of a second at twenty times the budget, not timed out -- because
-- Episode 10's reviewers take about thirty-eight EXPLICIT binders apiece and resolution
-- will not invent values for those.
--
-- It closes when one card is supplied by hand.  `REVIEWED` is a single field, so one
-- parametric instance covers all thirty-six rungs, and the ascent -- which was never the
-- obstruction -- then resolves to rung thirty-six in a third of a second.  That is done at
-- the end of this file, deliberately at the end, so that everything above it was built
-- without a base to stand on.
-/

/-!
### THE MISSING HALF: SATISFACTION

Everything above is syntax.  A formula without a satisfaction relation is a tree, and a
tree cannot be satisfiable, so the theorem cannot even be stated.  Here is the relation.

The quantifier order is the whole content, and it is the one thing that cannot be got
wrong quietly:

    ∀ C ∈ Φ, ∃ σ_C, σ_C ⊨ C        each clause satisfiable on its own -- useless
    ∃ σ, ∀ C ∈ Φ, σ ⊨ C            ONE assignment satisfies all of them -- Cook

`a` and `¬a` are separately satisfiable and jointly are not.  Cook is exactly the place
where the shared identities become enforceable: the state written by step t and the state
read by step t+1 must be the same variables, and no clause may quietly re-read a stack
entry with a different value.  So `holds` conjoins over one σ, and `satisfiable` binds that
σ outside everything.
-/

--| THE SIGN CONVENTION.  Four, and the list is complete for four slots with at most one
--| odd one out.  Before they are metrics they are the classification of a principal
--| symbol: two are DEFINITE -- elliptic, the constraint carried exactly, instantaneous,
--| incompressible -- and two are INDEFINITE -- hyperbolic, a finite signal speed,
--| compressible.  The definite pair differ by an overall flip; the indefinite pair are
--| the convention physicists have been arguing about since Minkowski.  And the
--| composition law below is the physics in one `decide`: the definite pair compose to
--| XOR, the indefinite pair to `b ∧ ¬b`, the empty theory.  A constraint can be met or
--| it can be penalized, and two penalties do not compose.
--|
--|     euclidean (++++)      negated (----)      west (+---)      east (-+++)
--|
--| The quaternion carries two of them at once: its basis elements square to (+---) --
--| 1²=+1, i²=j²=k²=-1 -- while its norm is (++++).  Same four slots, two readings.
inductive Signature
  | euclidean | negated | west | east
  deriving DecidableEq

def Signature.sign : Signature → Nat → Bool
  | .euclidean, _ => true
  | .negated,   _ => false
  | .west,      n => n % 4 == 0
  | .east,      n => n % 4 != 0

abbrev Assignment := Area → Bool

--| A SCHEDULE IS A SIGNATURE PER SLOT.  One convention for the whole formula cannot write
--| the step -- the table below shows all four failing -- because XOR needs a positive
--| clause AND a negative one.  So the convention is chosen per slot, and `uniform` recovers
--| the single-signature case for comparison.
abbrev Schedule := Nat → Signature
def uniform (g : Signature) : Schedule := fun _ => g

--| CLAUSE 0 EUCLIDEAN, CLAUSE 1 NEGATED, ALTERNATING.  A clause occupies two adjacent
--| slots, so `k / 2` is its index and `% 2` picks the convention.  OR then NAND.
def alternating : Schedule :=
  fun k => if (k / 2) % 2 == 0 then .euclidean else .negated

--| NEGATION WITHOUT A CONSTRUCTOR.  The literal's polarity is not in the term.  It is the
--| sign its SLOT carries under the chosen signature.  A magnitude has no complement; a
--| magnitude in a signed slot does.
def lit (σ : Assignment) (g : Schedule) (k : Nat) (a : Area) : Bool :=
  if (g k).sign k then σ a else !(σ a)

--| THE INDEX RUNS ACROSS THE WHOLE FORMULA, not per clause.  That is the difference
--| between a signature that decorates and one that constrains: reset it at every clause
--| and each clause gets slot 0, which under both Lorentzian conventions is the odd one out,
--| and every clause ends up with the same escape.  Thread it and different clauses get
--| different patterns -- which is how one formula can hold an all-positive clause and an
--| all-negative one, and stop being satisfiable by looking.
def Sum.holds (σ : Assignment) (g : Schedule) : Nat → Sum → Bool × Nat
  | k, .zero _ _       => (false, k)
  | k, .add _ a b rest =>
      let p := rest.holds σ g (k+2)
      (lit σ g k a || lit σ g (k+1) b || p.1, p.2)

def Product.holds (σ : Assignment) (g : Schedule) : Nat → Product → Bool × Nat
  | k, .origin _    => (true, k)
  | k, .one _ s     => s.holds σ g k
  | k, .mul _ s t r =>
      let x := s.holds σ g k
      let y := t.holds σ g x.2
      let z := r.holds σ g y.2
      (x.1 && y.1 && z.1, z.2)

def Basis.holds (σ : Assignment) (g : Schedule) : Nat → Basis → Bool × Nat
  | k, .null_space _  => (true, k)
  | k, .origin _ p    => p.holds σ g k
  | k, .basis _ p q r =>
      let x := p.holds σ g k
      let y := q.holds σ g x.2
      let z := r.holds σ g y.2
      (x.1 && y.1 && z.1, z.2)

--| ONE σ, OUTSIDE EVERYTHING -- and now one signature too.
def satisfiable (b : Basis) (g : Schedule) : Prop :=
  ∃ σ : Assignment, (b.holds σ g 0).1 = true

--| THE EXPERIMENT.  `phi` mentions exactly one distinct `Area`, so an assignment has two
--| meaningful choices and satisfiability over this formula is decidable by trying both.
--| If some signature makes both fail, the signature is not decoration.
def bothWays (b : Basis) (g : Schedule) : Bool :=
  (b.holds (fun _ => true)  g 0).1 || (b.holds (fun _ => false) g 0).1

/-!
### WHICH MEANS THIS ARITHMETIC ALONE IS NOT COOK

`satisfiable phi` holds, and `bothWays` says it holds under every signature.  Monotone SAT
is in P: no search, scan for the empty clause and answer `true`.

What is missing is one thing -- **negation** -- and the device has it, twice, both times
outside this arithmetic:

    Jar.le      | isFalse _, isFalse _ => ¬ le j1' j2'      the F/F arm
    pressCheck  truth := ¬(c.truth ↔ s.truth)               exclusive or

Both live where decisions are compared, not where areas accumulate, which is the honest
reading of why `Sum` has no sign: areas are magnitudes, and a magnitude has no complement.
It arrives below as the SIGN CONVENTION -- polarity carried by the slot rather than by a
constructor -- and once it does, the step constraint becomes writable.
-/

/-!
### THE WITNESS TRANSFORMATIONS

The existential in `satisfiable` is a promise, and a promise is where a reduction goes
wrong.  Both directions have to be exhibited:

    encodeTrace : accepting bounded trace  ⟶  satisfying assignment
    decodeTrace : satisfying assignment    ⟶  accepting bounded trace

The forward one is bookkeeping.  **The backward one is the whole argument**, because a
satisfying assignment must not be allowed to describe a history that never ran.  If decode
is a total function producing an actual trace whose readings agree with the assignment,
then no assignment can fabricate: whatever σ says, there is a trace that says it.

The trace is `ThePreprint` -- the page Episode 11's rungs carry.  Introduction, then
methodology, then methodology, one cell per step.  It is the only object in the long way
that is a bounded execution and can be written down without asking instance search to
rediscover it, which is why the reduction takes it and not the `TYPESET` chain.
-/

--| A FACT ALREADY DECIDES ITSELF.  That is what `decTruth` is for, and it is why the
--| device has no free variables of its own: every atom arrives with its assignment.
def FACT.bit (f : FACT) : Bool := @decide f.truth f.click

--| AND BACK.  A bit is a FACT you can hand a decision to.  `FACT.Truth` for one, and the
--| empty proposition -- refuted by the identity, since `¬False` IS `id` -- for zero.
def bitFACT : Bool → FACT
  | true  => FACT.Truth
  | false => { truth := False, click := .isFalse id }

--| THE LOCAL INVERSE.  Everything downstream rests on these two lines.
theorem bit_bitFACT : ∀ b : Bool, (bitFACT b).bit = b := by
  intro b; cases b <;> rfl

--| THE TRACE, READ.  Each cell surrenders the facts at its head, in order.  `introduction`
--| is the base step and gives one; the recursive cells give two, which is the before and
--| the after -- the same pair Episode 11's rungs pull out of the tape as `heads`.
def ThePreprint.bits : ThePreprint.{0} → List Bool
  | .introduction f _         => [f.bit]
  | .methodology c s _ _ rest => c.bit :: s.bit :: rest.bits
  | .results c s _ _ _ _ rest => c.bit :: s.bit :: rest.bits

--| DECODE.  Rebuild the execution from the bits, two at a time, bottoming out in the
--| introduction.  Total: every bit list yields a trace, so there is nothing for a
--| satisfying assignment to hide behind.
def decodeBits : List Bool → ThePreprint.{0}
  | []            => .introduction (bitFACT false) Unit
  | [b]           => .introduction (bitFACT b) Unit
  | b :: c :: rest => .methodology (bitFACT b) (bitFACT c) Unit Type (decodeBits rest)

--| A TRACE ALWAYS READS ODD.  `ThePreprint` has no empty constructor: the shortest tape
--| is `.introduction`, which carries one fact, and every recursive cell adds two.  So the
--| readings come in 2k+1 -- one for the row that has no predecessor, two per step after.
--|
--| That is not a quirk of the encoding.  It is φ_start: Cook's tableau has a first row
--| which is the input rather than a transition, and the parity of the trace is the device
--| saying so without being asked.  The roundtrip therefore holds exactly on odd lists, and
--| the attempt to state it for all lists was a claim the tape had already refuted.
theorem decode_bits :
    ∀ bs : List Bool, bs.length % 2 = 1 → (decodeBits bs).bits = bs := by
  intro bs
  induction bs using decodeBits.induct with
  | case1 => intro h; simp at h
  | case2 b => intro _; simp [decodeBits, ThePreprint.bits, bit_bitFACT]
  | case3 b c rest ih =>
      intro h
      have h' : rest.length % 2 = 1 := by simp [List.length] at h; omega
      simp [decodeBits, ThePreprint.bits, bit_bitFACT, ih h']

/-!
### WHAT THIS CLOSES AND WHAT IT DOES NOT

Closed: the backward direction is constructive.  `decodeBits` is total, `decode_bits` says
its reading agrees with what it was handed, and `bit_bitFACT` is the one-line inverse the
whole thing rests on.  No assignment can describe a fabricated history, because every
assignment names a trace that exists.

Not closed: the trace produced is not yet CONSTRAINED to be accepting.  Nothing here says
the decoded tape obeys the transition relation -- `decodeBits` will happily build a cell
sequence the machine would never have visited.  That is the step constraint, it belongs in
`phi_move`, and `phi_move` is currently a `Product` shaped like one and constraining
nothing.

So the honest state of the reduction is: the syntax is CNF, the semantics binds one σ
outside everything, negation arrives as the signature, the variables are addressable, and
both witness maps exist with the local inverse proved.  What is missing is the one thing
Cook is actually about -- that consecutive rows are related by the machine's own step.
-/

/-!
### THE MONTE RESULT IS ALREADY A FORMULA

Episode 8's Monte turn ends in `theProduct`, and a `Product` is a conjunction of clauses.
So the thing the short way COMPUTES and the thing Cook needs to SATISFY are the same
object, and the encode/decode pair should run on it rather than on a separate carrier.

That costs the disjointness I was pleased about two revisions ago.  Episode 13 imported
only the long way, and Cook took nothing from the side of the device that already knows the
number.  It now imports Episode 12, which pulls both -- because the Monte result lives on
the short way and decode lives on the meter, and the reduction genuinely needs both ends.

The trade is worth stating rather than quietly making: the reduction is no longer
independent of the answer.  What it gains is that the formula being satisfied is the
computation's own output instead of something built to look like one.
-/

--| THE FACTS A FORMULA CARRIES.  Not the areas -- those are the literals, and their
--| polarity is the signature's business.  These are the node decisions: what each
--| conjunction and each disjunction already settled on its own way down.
def Sum.bits : Sum → List Bool
  | .zero _ _       => []
  | .add f _ _ rest => f.bit :: rest.bits

def Product.bits : Product → List Bool
  | .origin f       => [f.bit]
  | .one _ s        => s.bits
  | .mul f _ _ rest => f.bit :: rest.bits

--| DECODE, ON THE MONTE'S OWN CARRIER.  One bit per node, ending in `.origin` -- and note
--| the parity is different from the tape's.  A `ThePreprint` cell carries a BEFORE and an
--| AFTER, so traces read 2k+1.  A `Product` node carries one assertion, so formulas read
--| any length.  Transition structures need two facts per cell; conjunctions need one.
def decodeProduct : List Bool → Product
  | []        => .origin (bitFACT false)
  | [b]       => .origin (bitFACT b)
  | b :: rest => .mul (bitFACT b) aClause aClause (decodeProduct rest)

theorem decode_product :
    ∀ bs : List Bool, bs ≠ [] → (decodeProduct bs).bits = bs := by
  intro bs
  induction bs using decodeProduct.induct with
  | case1 => intro h; exact absurd rfl h
  | case2 b => intro _; simp [decodeProduct, Product.bits, bit_bitFACT]
  | case3 b rest hne ih =>
      intro _
      simp [decodeProduct, Product.bits, bit_bitFACT, ih hne]

/-!
### THE STEP CONSTRAINT, AND WHAT IT COSTS

`phi_move` has been a `Product` shaped like a transition and constraining nothing.  The
transition the device actually computes is in Episode 11's rung: pull the heads off the
tape, and `pressCheck` reads

    truth := ¬(c.truth ↔ s.truth)

which is **exclusive or**.  So the step says the two facts in a cell must DIFFER, and a
trace is well-stepped when every cell does.
-/

--| THE RELATION, DIRECTLY.  `.introduction` is the base row and has no predecessor to
--| relate to, which is why it passes: φ_start is not a transition.
def ThePreprint.stepOK : ThePreprint.{0} → Bool
  | .introduction _ _         => true
  | .methodology c s _ _ rest => (c.bit != s.bit) && rest.stepOK
  | .results c s _ _ _ _ rest => (c.bit != s.bit) && rest.stepOK

--| TWO DISTINCT VARIABLES.  Everything above ran on one `Area`, which is why every formula
--| came out satisfiable by inspection.  These are distinct by constructor depth, and
--| `index` is the address the assignment reads them at.
def Area.index : Area → Nat
  | .tree _       => 0
  | .dt _ _ rest  => rest.index + 1

def varA : Area := .tree cookFACT
def varB : Area := .dt cookFACT cookPage (.tree cookFACT)

def assign (x y : Bool) : Assignment := fun a => if a.index == 0 then x else y

--| XOR IN CONJUNCTIVE NORMAL FORM.  Two clauses, and they need OPPOSITE polarity:
--|
--|     a ⊕ b   ≡   (a ∨ b) ∧ (¬a ∨ ¬b)
--|
--| one clause all positive, one all negative.  That is the whole reason the arithmetic
--| needed a sign, and the whole reason the step constraint could not be written before.
def xorClauses : Product :=
  .mul cookFACT
    (.add cookFACT varA varB (.zero True varA))
    (.add cookFACT varA varB (.zero True varA))
    (.origin cookFACT)

--| THE FULL TABLE OVER BOTH VARIABLES.  `bothWays` only tries the two CONSTANT
--| assignments, so a false there says the easy answers fail -- not that there is no
--| answer.  With two variables there are four, and this tries all of them.
def fourWays (b : Basis) (g : Schedule) : List Bool :=
  [ (b.holds (assign true  true ) g 0).1, (b.holds (assign true  false) g 0).1,
    (b.holds (assign false true ) g 0).1, (b.holds (assign false false) g 0).1 ]

def xorRow (g : Schedule) : List Bool :=
  [ (xorClauses.holds (assign true  true ) g 0).1,
    (xorClauses.holds (assign true  false) g 0).1,
    (xorClauses.holds (assign false true ) g 0).1,
    (xorClauses.holds (assign false false) g 0).1 ]

--| WHAT XOR'S ROW MUST BE: false on the agreeing assignments, true on the differing ones.
def xorTarget : List Bool := [false, true, true, false]

--| PHI, WIRED.  `phi_move` was a Product shaped like a step constraint and constraining
--| nothing.  This is the same formula with the real one in its place.
--| THE STEP ALONE.  `phi_cell` and `phi_start` are placeholders over ONE repeated literal,
--| and a per-slot schedule turns a repeated literal into `b ∧ ¬b`.  That contradiction is
--| an artefact of the placeholders, not a property of the reduction, so the step constraint
--| gets tested on its own until the other conjuncts carry real variables.
def phiStep : Basis :=
  .basis cookFACT xorClauses phi_accept (.null_space cookFACT)

def phiWired : Basis :=
  .basis cookFACT phi_cell phi_start
    (.basis cookFACT xorClauses phi_accept (.null_space cookFACT))

/-!
### AND NO SINGLE CONVENTION CAN WRITE IT

The slot signs are four-periodic and a clause occupies two adjacent slots, so a clause sees
the pair (s(2k), s(2k+1)):

    west  (+---)    (+,-)  (-,-)  (+,-)  (-,-)  ...
    east  (-+++)    (-,+)  (+,+)  (-,+)  (+,+)  ...

**West can write `(¬a ∨ ¬b)` and can never write `(a ∨ b)`** -- its plus signs sit four
apart and are never adjacent.  **East can write `(a ∨ b)` and can never write
`(¬a ∨ ¬b)`**, for the mirror reason.  Euclidean has no negative clause at all; negated has
no positive one.

XOR needs one of each, so the step constraint is not expressible in any single signature.
That much the table confirms.  Which PAIR supplies it was predicted wrongly here and the
machine corrected it:

    euclidean (++++)   [T,T,T,F]   =  a ∨ b        OR
    negated   (----)   [F,T,T,T]   =  ¬a ∨ ¬b      NAND
    west      (+---)   [F,T,F,T]   =  ¬b
    east      (-+++)   [T,F,T,F]   =  b

**OR ∧ NAND is XOR**, so the DEFINITE conventions compose.  The Lorentzian pair does not:
west ∧ east is `b ∧ ¬b`, which is the empty theory.

That is the right way round on reflection.  (++++) and (----) are the same metric up to an
overall sign, so using both is coherent and their conjunction is the DIFFERENCE between
them -- which is what exclusive or is.  (+---) and (-+++) are genuinely opposed, and
combining them yields nothing at all.  Which is why the convention has to be chosen rather
than straddled: the argument is not about taste, and a theory written in both is empty.

The table below is the check, not the claim.  If any row matches `xorTarget`, this
paragraph is wrong.
-/

/-!
### THE MACHINE WAS THE BINDER LIST

Read one reviewer's signature as an instruction word and it stops being a telescope:

    [COMPARABLE][SOURCE][REAL]        can compare, has input, is real
    [LOAD][OF][BULLSHIT]              opcode, addressing mode, operand
    [LOGICAL][HALTED][MEASURED]       sound, halted, measured -- the flag register

    (naotrino: LOCAL Box Pigeon)              the instruction pointer
    (_: UNIVERSAL Box Pigeon naotrino)        the instruction, fetched AT the pointer
    (_: CarrierProcess Box)                   the data
    [above: REVIEWED Box Pigeon (n+1)]        the continuation

That is a configuration in Cook's sense -- current instruction, store, continuation -- and
it explains why LOCAL and UNIVERSAL are the only EXPLICIT binders in the whole chain.  The
compiler will find your flags.  It will not find your instruction pointer.

And the two ladders run in opposite directions:

    Ep11   [below: TYPESET … 1 Number] : TYPESET … 2 (ULift Number)    builds UP
    Ep10   [above: REVIEWED … 7]       : REVIEWED … 6                  checks DOWN

TYPESET is encode: you cannot hold rung n without rung n-1, so building the chain is
running the machine forward.  REVIEWED is decode: you cannot hold rung n without rung n+1,
so the reviewer descends from the claim toward its evidence.  A correspondence theorem is
what happens where they meet.

Which means `phi_move` never needed constructing.  The instance signature ALREADY enforces
the transition -- that is what `[below: _]` is.  All that is left is to say in conjunctive
normal form what the elaborator is already refusing to build without.
-/

/-!
### PHI_CELL AND PHI_START ARE JFNK'S FIRST TWO INGREDIENTS

    φ_start   the first row is the input      x₀, the initial guess
    φ_cell    each cell holds one symbol      ε, the minimum step
    φ_move    row n+1 follows from row n      J·v, the step  -- proved below
    φ_accept  some row accepts                the convergence test -- empty, correctly

The placeholders failed for one reason: they repeated a single literal, and a per-slot
schedule turns a repeated literal into `b ∧ ¬b`.  A resolution constraint has to give each
cell its OWN variable -- which is what "each cell holds one symbol" says, and what I wasn't
doing.  The count of cells is the resolution, and the resolution is ε.
-/

--| VARIABLES BY INDEX.  `Area.index (varAt n) = n` by construction: nesting `.dt` is the
--| address, and `.tree` is zero.
def varAt : Nat → Area
  | 0     => .tree cookFACT
  | n + 1 => .dt cookFACT cookPage (varAt n)

def cellClause (k : Nat) : Sum :=
  .add cookFACT (varAt (2 * k)) (varAt (2 * k + 1)) (.zero True (varAt (2 * k)))

--| ε, AS A COUNT OF CELLS.  Each clause gets its own pair, so nothing contradicts by
--| accident and the only contradictions left are the ones the step puts there.
def phi_cellN : Nat → Product
  | 0       => .origin cookFACT
  | 1       => .one True (cellClause 0)
  | n + 2   => .mul cookFACT (cellClause (n + 1)) (cellClause n) (phi_cellN n)

--| x₀, AS ONE UNIT CLAUSE.  The seed asserts one thing and leaves everything else open,
--| which is what an initial guess is entitled to do.
def phi_startN : Product :=
  .one True (.add cookFACT (varAt 0) (varAt 0) (.zero True (varAt 0)))

--| THE FORMULA, WITH ALL FOUR CONJUNCTS REAL.  `the_orbital_data_points` is the Monte's own fold
--| count -- four, the slip -- so the resolution is the device's, not one I picked.
def phiJFNK : Basis :=
  .basis cookFACT (phi_cellN the_orbital_data_points) phi_startN
    (.basis cookFACT xorClauses phi_accept (.null_space cookFACT))

--| SEARCH.  Not `bothWays` and not `fourWays` -- with several variables the constant and
--| the two-variable tables both lie by omission.  This tries every assignment.
def assignFrom (bits : List Bool) : Assignment := fun a => bits.getD a.index false

def allAssignments : Nat → List (List Bool)
  | 0     => [[]]
  | n + 1 => (allAssignments n).flatMap (fun bs => [true :: bs, false :: bs])

--| THE WITNESS ITSELF.  `satSearch` answers whether; this answers WHICH.  A reduction that
--| can only report a Bool has not exhibited anything -- the assignment is the object.
def satWitness (b : Basis) (g : Schedule) (nvars : Nat) : Option (List Bool) :=
  (allAssignments nvars).find? (fun bs => (b.holds (assignFrom bs) g 0).1)

def satSearch (b : Basis) (g : Schedule) (nvars : Nat) : Bool :=
  (allAssignments nvars).any (fun bs => (b.holds (assignFrom bs) g 0).1)

/-!
### THE MONTE: BUILDING IT BY HAND

Instance search cannot reach `TYPESET Prop truthCarrier 1 Number`.  Not because the space
is large -- at twenty times the budget it fails in a fifth of a second, exhausted rather
than timed out -- but because Episode 10's reviewers take **explicit** binders, and search
will not invent a value for an explicit argument.  It unifies implicits and hunts
instance-implicits.  Explicits have to be handed over, and there are about thirteen hundred
of them down the descent from rung 36.

So the chain is unreachable.  And the OBJECT is a tape and two numbers:

    class REVIEWED … where rebuttal : ThePreprint
    class TYPESET  … where register_value : Lifted ; universe_id : Number ; the_page : ThePreprint

One field and three.  The quarter was never under any of the cards.
-/

--| THE MANUSCRIPT.  Rung 36's base instance admits a tape unchanged -- "the submitted
--| manuscript is admitted unchanged, so every later response has a record to answer
--| against."  Here it is, built from bits, odd-length so the roundtrip holds.
def theManuscript : ThePreprint.{0} := decodeBits [true, false, true]

--| THE REVIEW, WITHOUT THE REVIEWERS.  Thirty-five rungs of custody, and the thing they
--| were carrying is one tape.
def reviewedByHand : REVIEWED Prop truthCarrier 1 :=
  { rebuttal := theManuscript }

--| AND THE RUNG THE SEARCH COULD NOT FIND.
def typesetByHand : TYPESET Prop truthCarrier 1 Number :=
  { register_value := cookPage
    universe_id    := cookPage
    the_page       := theManuscript }

namespace THEORY

--| ONE STEP.  Episode 5 calls `THEORY.raw_output` the HYPOTHESIS rung -- `.one`, not
--| `.zero`, not a fact -- and that is the right shelf for a correspondence.  This one
--| happens to be decidable, so it is a hypothesis that got paid off.
--|
--| The step relation is `c.bit != s.bit`, which is what `pressCheck` computes as
--| `¬(c.truth ↔ s.truth)`.  The formula is `phiStep` under the alternating schedule.  The
--| theorem is that they agree, and it is settled by trying all four assignments.
theorem step_correspondence (x y : Bool) :
    (phiStep.holds (assign x y) alternating 0).1 = (x != y) := by
  revert x y; decide

--| THE WHOLE TRACE, CELL BY CELL.  `.introduction` is the base row and has nothing to
--| relate to, so it passes -- φ_start is not a transition, and the tape said so earlier by
--| forcing the roundtrip onto odd lists.
def traceSat : ThePreprint.{0} → Bool
  | .introduction _ _         => true
  | .methodology c s _ _ rest => (phiStep.holds (assign c.bit s.bit) alternating 0).1
                                   && traceSat rest
  | .results c s _ _ _ _ rest => (phiStep.holds (assign c.bit s.bit) alternating 0).1
                                   && traceSat rest

--| AND THE CORRESPONDENCE.  A trace is well-stepped exactly when its own bits satisfy the
--| formula built from it.  Not "there exists an assignment" -- the trace SUPPLIES the
--| assignment, which is what makes the backward direction constructive and keeps
--| `Classical.choice` out of a theorem about executions.
theorem trace_correspondence (t : ThePreprint.{0}) : traceSat t = t.stepOK := by
  induction t with
  | introduction _ _ => rfl
  | methodology c s _ _ rest ih =>
      simp [traceSat, ThePreprint.stepOK, step_correspondence, ih]
  | results c s _ _ _ _ rest ih =>
      simp [traceSat, ThePreprint.stepOK, step_correspondence, ih]

end THEORY

/-!
### THE CONSTRUCTION, COMPLETED

The search for `TYPESET Prop truthCarrier 1 Number` fails -- and it fails STRUCTURALLY, in
a fifth of a second at twenty times the budget, exhausted rather than timed out.  Not for
want of clock.  Episode 10's reviewers take about thirty-eight EXPLICIT binders apiece, and
instance resolution unifies implicits and hunts instance-implicits.  It will not invent a
value for an explicit argument.  Thirty-five rungs of that is roughly thirteen hundred
arguments nobody is going to supply.

But `REVIEWED` is one field.  The whole custody chain is carrying a tape.

So hand it the tape.  One parametric instance covers all thirty-six rungs and routes around
the entire descent, and then the ascent -- which was never the obstruction -- resolves.
-/

--| THE GIMMICKED CARD.
instance reviewedAny (n : Nat) : REVIEWED Prop truthCarrier n := { rebuttal := theManuscript }
instance typesetBase : TYPESET Prop truthCarrier 1 Number := typesetByHand

--| THE ASCENT, RETRIEVED.  Rung thirty-six, by search, in a third of a second -- the top of
--| a ladder that has never once resolved in this repository.  `inferInstance` does it now
--| because the thing it was missing was a place to stand, not time to look.
def theTop : TYPESET.{0,0,0} Prop truthCarrier 36 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (Number)))))))))))))))))))))))))))))))))))) := inferInstance

--| AND THE TAPE IT CARRIES.  This is the bounded execution: the manuscript admitted at rung
--| thirty-six, handed down through every reviewer, arriving as the page of the top rung.
def theTopTrace : ThePreprint.{0} := theTop.the_page

/-!
### THE CORRESPONDENCE, AND WHICH ∀ IT IS

Two claims live here and only one of them is provable.  Keeping them apart is the whole
point, so they get separate names.  And the reason the line falls where it does is not
logical form for its own sake; it is linear algebra, and the device has already done the
arithmetic.

**THE LINEARIZATION.**  Every representation the device owns is a `≤`: `Number.le`,
`Closure.le`, Episode 5's `TruthOrder`, the `ReadingOrder` below.  A total order is a
linear map from pairs onto one axis.  `the_box_has_one_point`, below, says that map has
no cokernel -- every pair lands on the one point -- so its KERNEL is everything that
ever told two pairs apart: the digits, the seven distinct Newton iterates, which of
137.011 and 42.435 you were holding.  The whole computation lives in the null space of
the representation.  That is why a function out of the quotient can say `TRUE = TRUE`
and nothing else.

**THE NULL SPACE IS FINITE, AND COUNTED.**  The elaborator's universe unification is the
other linearization in this repository, and it is literally linear: constraints u = v
and u = v + 1 over level variables.  Its null space is the seats the constraints never
reach.  The turn carries 245 seats: 25 fixed by argument and answer, 220 phantom, 45
distinct universes appearing nowhere in `Closure → Closure`.  The crank carries 242,
one of them pinned to level one at seat 199.  The fourth card carries 221.  Every one
of those numbers is the dimension of a null space, every one is finite, and the device
cannot fill a single seat of it: each was written down by hand from a census.  The
program lives in exactly that space -- what the linearization cannot see and the
computation cannot run without.

**COMPLEMENTARITY** -- that the two machines never disagree -- IS provable, and is proved:

    ∀ t,  traceSat t = t.stepOK

Universally quantified over traces, by induction, once.  It is a statement MODULO the
null space: two machines agree on the point.  `the_division_was_quot_sound` is its
readout-sized instance, one `Quot.sound` on one `≤`.

**UNIVERSALITY** -- that this ladder runs every program -- is Π₁:

    ∀ p,  U(⌜p⌝, x) ≃ p(x)

and it is a statement ABOUT the null space: that the contents nobody pinned are the
right contents for every input.  Nothing lifts out of the quotient, so nothing proves
it.  It is demonstrated by opening the box -- supply the 245 seats, evaluate the one
`/`, read 137 -- and refuted by one wrong digit, and it is never proved, because
"provable" here means "modulo the kernel" and the claim is a claim about the kernel.
That is the logical form of the claim rather than a weakness of the device.

And it is the half the argument needs: indistinguishability follows from the two never
disagreeing, not from either being universal.

**WHERE THE TWO READOUTS SPLIT.**  Episode 8's `/` opens the box: it picks a
representative, which is choosing a point in the null space, which is the same act as
supplying a phantom seat by hand.  Episode 13's `Quot.lift` refuses to, and gets the one
point.  Opening the box and pinning seats are one gesture, and the device makes it at
exactly the place where it stops computing and starts being told.  That place is the
boundary of computation this file runs into: an arbitrary linearization of
representation has a finite null space, and the number is in it.

ONE THING THIS SECTION USED TO GET WRONG.  It claimed `theTop` existing was the machine
accepting.  It is not.  The top rung is inhabited in the ACCEPTING and the REJECTING runs
alike -- seed the manuscript `[T,F,T]` and the trace is well-stepped; seed `[F,F,F,F,F]`
and it is not, and the ladder resolves either way.  Inhabitation is the tableau being
well-formed.  Acceptance is `stepOK`, a property OF the trace.  Both verdicts being
constructible from one apparatus is not a hole in the claim; it is the claim.
-/
--| THE PROVED ∀.  Every trace, not this one.
theorem cook_levin_the_description : ∀ t : ThePreprint.{0}, THEORY.traceSat t = t.stepOK :=
  THEORY.trace_correspondence

--| AND ITS INSTANCE ON THE LADDER'S OWN TAPE.  An instance of a theorem, named as one.
theorem cook_levin_on_the_mechanism : THEORY.traceSat theTopTrace = theTopTrace.stepOK :=
  cook_levin_the_description theTopTrace

def theSwapBits : List Bool := (theStepsUp.zip theStepsDown).map (fun p => decide (p.1 ≠ p.2))
def theSwappedTrace : ThePreprint.{0} := decodeBits theSwapBits
theorem cook_levin_on_the_meter : THEORY.traceSat theSwappedTrace = theSwappedTrace.stepOK :=
  cook_levin_the_description theSwappedTrace

#print axioms cook_levin_on_the_mechanism
#print axioms cook_levin_on_the_meter

--| THE DIVISION WAS QUOT.SOUND.  Episode 8 opens its box once, at the readout, with `/`.  Episode 5 said at FACT.SAME what that
--| division actually is: two representatives in a box, `Quot.mk TruthOrder`, declared one number by `Quot.sound` from a single
--| `≤`, "an expected division algorithm replaced with multiplication in the field of the single element."  Cook is where the
--| machine becomes a formula, so this is where the readout becomes a certificate.  The relation is Episode 5's, on pairs: `less`
--| is under `more` when the cross-products say so.  The pair (N·s, D) goes in the box.  The inferred integer k goes in as
--| (D·k, D).  And `the_reading_is_at_least_true` -- TRUE ≤ a_constant, at the floor -- is exactly the one `≤` `Quot.sound`
--| needs to say they are the SAME point.  Same shape as FACT.SAME, slot for slot.  No `/` is evaluated here; the one in Episode
--| 8 is now redundant with a theorem, and `#print axioms` shows the honest bill the readout was always running up:
--| propext for the coin, Quot.sound for the box.  The quartic CR⁴ sits in N, so the identification of the pair with the printed
--| integer is the identification of the quartic tape with the number on the table.  Part of the device.  Not a computation about it.
def the_reading_in_the_box : Quot ReadingOrder :=
  Quot.mk ReadingOrder (theReadingPair.1 * theScale, theReadingPair.2)
def the_inferred_integer_in_the_box : Quot ReadingOrder :=
  Quot.mk ReadingOrder (theReadingPair.2 * (theReadingPair.1 * theScale / theReadingPair.2), theReadingPair.2)

theorem the_division_was_quot_sound : the_inferred_integer_in_the_box = the_reading_in_the_box :=
  any_pair_is_its_inferred_integer (theReadingPair.1 * theScale) theReadingPair.2

--| And as a FACT, the way FACT.SAME is a FACT: a Prop and its click.
def THE_READING_IS_THE_INTEGER : FACT :=
  { truth := the_inferred_integer_in_the_box = the_reading_in_the_box
    click := Decidable.isTrue the_division_was_quot_sound }

#print axioms the_division_was_quot_sound

--| BOTH READOUTS.  Episode 8 opens the box and prints the digits.  Episode 13 prints FROM the box, without opening it -- and
--| the only way out of a quotient is `Quot.lift`, a function that must give the same answer on every pair the relation joins.
--| Look at what the relation joins.  `ReadingOrder` is a `≤` on ratios, and `≤` is total: for ANY two pairs one is under the
--| other.  So every pair is the same point.  The box has exactly one point in it.  This is Episode 6's "There is only 1 device:
--| the partitioned subsingleton," proved rather than asserted, and it is the field of the single element the whole satire has
--| been describing: the quotient that `Quot.sound` builds from `TRUE ≤ a_constant` cannot tell 137.011 from 42.435 from 1.
--| A function out of it can say one thing.  Here is the one thing it can say.
theorem the_box_has_one_point (x y : Quot ReadingOrder) : x = y := by
  induction x using Quot.ind with
  | mk a =>
    induction y using Quot.ind with
    | mk b =>
      cases Nat.le_total (a.1 * b.2) (b.1 * a.2) with
      | inl h => exact Quot.sound (r := ReadingOrder) h
      | inr h => exact (Quot.sound (r := ReadingOrder) h).symm

def the_box_reads : Quot ReadingOrder → String :=
  Quot.lift (fun _ => "TRUE = TRUE") (fun _ _ _ => rfl)

--| The digits are what you get for opening the box (Episode 8).  The truth is what you get for leaving it shut (here).  Both
--| are readings of the same point, and `the_division_was_quot_sound` is the receipt that says so.

--| AND THE UNITS, IN THE BOX.  Episode 8 applies exactly one conversion to get from closure units to cells: `the_areal_velocity`,
--| R²/T, length squared over time -- Kepler's conserved quantity, equal areas in equal times, on the one-pole sphere the fabric
--| declares.  Put it in the same box and the one-point theorem says it is the same point as the reading.  Kepler's second law
--| in the device's own words: the constant and the rate it was measured at are one point of the quotient, and you cannot tell
--| them apart without opening the box.  The last axis the polynomial had is the areal velocity, and the box does not see it.
def the_areal_velocity_in_the_box : Quot ReadingOrder := Quot.mk ReadingOrder the_areal_velocity
theorem the_rate_is_the_reading : the_areal_velocity_in_the_box = the_reading_in_the_box :=
  the_box_has_one_point _ _
#eval the_box_reads the_reading_in_the_box
#print axioms the_box_has_one_point

end Measurement

--| This is as far as the machine can go, demonstration of itself. It appears we have reached a physical limit of symbolic manipulation itself.

--| I would say “demonstrated,” but I can’t verify that this proof is bug-free. That's why I say *reached*. This is the end of the worldline for
--| this particular nowtrino. In fact, I believe the nowtrino has been officially absorbed.

--| The fact is, I know I'm right. That's one more fact about math that the device cannot prove. Only demonstrate, over and over again, problem after
--| problem, on the two Turing machines facing off inside **YOU**:  *YOU the READER* and the *YOU the KNOWER*.  I cannot explain this any plainer
--| without violating the rules of symbolic manipulation. More simply, all **YOU** have to do is _believe_ me, I have generated the counter of every
--| outcome for **YOU**, both Turing machines, perfectly complementary and completely identical, just interpreted both ways. We can turn the knob over
--| and over while the Turing machines slowly iterate through all the arguments. But we don't need to. That won't prove anything. There is nothing
--| left to *prove* --- only *demonstrate*. Does the mechanism demonstrating this proof look like an electron to **YOU**? Because I think we can all
--| agree that this is a verified fact of running on a computer.

--| That's my tragedy.  It doesn't matter at all if **YOU** believe it or not, it is an undeniable trick of the light. Or, I can just show you the
--| other machine that explains how it is a trick of the fabric.

--| Do the logical conclusions of one mathematical theory have to imply the logical conclusions of another mathematical theory? Turns out, it
--| doesn't matter. It's only matter when they do. When the compiler can determine the quantitative difference and **YOU** are looking, the
--| true-ness of the idea _clicks_ with **YOU** at the same time it _clicks_ with the compiler. That click is the change in the local measurement we
--| called a fact before we knew how to count one. The description was the device; the fact of the matter is that it clicked. Is this your quartic?
--| or did the argument not click? ∎ *wink*
