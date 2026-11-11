/-
__Measurement: The Tragedy of John Henry__
__A Satire in Look Ahead Backus-Naur Form__

_This is a gentle reminder that things can only get so meta and still be consistent._

(c) 2026

"stat rosa pristina nomine, nomina nuda tenemus"

__EPISODE 12__: _Let Him Cook. . . . . . . Levin_

*OF COURSE, I put a theorem prover in a theorem prover _IN A THEOREM PROVER_ just to prove a point. *YOU the READER* don't need a complete third
_theorem prover_, just a finite one.
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
open «springer-verlag» THE_GOSPEL
--| The readings are not in the device.  They are reached for, once, here.

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
--| THE ONE DIMENSIONLESS MEASUREMENT.  The device has two counters.  Cells: constructor depth, the tape, the resolution in
--| space, and it cannot resolve finer than one.  Heartbeats: the elaborator's own count of itself, the resolution in time,
--| handed back by a command because the kernel cannot see it, and it cannot resolve finer than one.  This line used to compare
--| the bracket in cells to the floor in heartbeats with a `<`, which every reader flagged as a dimensional error, and it was.
--| The honest object is their ratio.  Heartbeats per cell is dimensionless, a Courant number, the time step over the space
--| step, and it is the ONLY dimensionless number this device produces from a real measurement rather than a reading.  It is
--| a pair and not a theorem, because the floor is this machine's and the next machine's will differ: that is what makes it a
--| measurement.  (On this build it sits near R/T, the wave speed.  Do not read into that.  The floor moves; R/T does not.)
--#eval theCourant

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

private def jarAt (n : Nat) : TermElabM (TSyntax `term) := do
  let mut s ← `(Measurement.the_photon_worldline)
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
  let h ← sample (← `(Measurement.Jar.le $(← jarAt n) Measurement.the_photon_worldline))
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

def theNewtonRung : Variation := .the_newton the_fact_is_true True

--| THE CONTROL.  No second derivative anywhere.  `Variation.newton` and
--| `Variation.krylov` are the SAME function on this ladder -- their `.the_gateaux`
--| arms agree (Episode08) -- so any cost difference between the two readings below
--| is the meter measuring a name, and there should not be one.
def gateauxAt : Nat → Variation
  | 0     => theNewtonRung
  | n + 1 => .the_gateaux the_fact_is_true True True (gateauxAt n)

--| THE EXPERIMENT.  One second derivative per rung, and the two arguments of the
--| bilinear map are made DIFFERENT on purpose: `before` continues the frechet
--| chain, `after` is the gateaux chain of the same depth.  `Variation.newton` takes
--| `before` and drops `after`; `Variation.krylov` takes both.  The gap between the
--| readings is the cost of the second slot of B -- the argument a Jacobian-vector
--| product never supplies and a matrix-free Krylov step does.
def frechetAt : Nat → Variation
  | 0     => theNewtonRung
  | n + 1 => .the_frechet the_fact_is_true True True True (frechetAt n) (gateauxAt n)

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
is put it in a clause.  Episode 8 already carded the atom: `ast₁`, built from the origin
fact and the origin page.  A literal here is not a new kind of thing.  It is the smallest
thing the device agreed to hold, which is what a literal is supposed to be.
-/
--| MINTED HERE, NOT BORROWED.  Episode 8 already carries `zero`, `ast₁` and
--| `integration`, and the obvious move is to import Episode 8 and use them.  That would be
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

and the device's version of the right-hand side is `∃ inst, TYPESET (CarrierProcess FACT) the_card_between 36 _`
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
--| AN OBLIGATION, NOTED.  This step checks the two facts WITHIN a cell and never connects one cell's output to the next
--| cell's input: two successive T→F cells pass.  And it is exclusive-or, so it admits only the two disagreeing arms, while
--| the click table weights the agreeing arms positively.  The correspondence proved below is bidirectional and exact for
--| THIS relation; the relation the table counts -- consecutive cells, all four arms, weighted -- is not yet the one checked.
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

--| THE REPRESENTATION, RUNG BY RUNG.  Episode 9 writes its ladder once and lets each step take only the rungs it reads.
--| Here the ladder is handed itself: the first rung crosses from Episode 8's Prop device onto a card with FACT in the box,
--| the two ways are laid over that card, and after that every rung is handed the rungs below it, so the ladder is indexed
--| by its own outputs, not Episode 8's.  What is not handed over is the universe.  The first ten rungs need no pin; from
--| COMPARABLE up each rung is pinned by hand, and from PRESENT up two seats are forced, the quantum lifted into the upness
--| and carried.  INFERRED is a side branch: the spin at the top reads the thirty-six rungs, not the inference.
namespace the_representation
open assembly_instructions

--| THE QUARTIC, FROM THE READER.  The coefficient tape, every cell a successor, folded onto Episode 8's other zero.  The spin
--| at the top turns once per successor, so it turns bent_card times past the freshman reading.  Read back, it is the tape
--| with the zero on the end: one cell longer than the card.  The fencepost again.
def the_quartic : Number := readers_experience.the_coefficient_tape.foldr Number.one another_zero
theorem the_quartic_reads_back_the_tape : the_quartic.peano = readers_experience.the_coefficient_tape ++ [zero] := rfl
theorem the_quartic_is_one_past_the_card : the_quartic.peano.length = readers_experience.bent_card + 1 := rfl

--| THE FIRST CARD.  Episode 8's truth carrier, dealt again with FACT in the box instead of Prop: the same symbol, the same
--| zero under it.  The device is Lean's; the card is the ledger's.
def the_first_card : CarrierProcess FACT := { symbol := FACT.Truth, quarter := .zero FACT.Truth }

--| rung 1, DISTINGUISHABLE: no pin.
noncomputable def rung01 :=
  STEP1_NAME_THE_LEDGER_AND_MARK_IT_WITH_THE_SYMBOL_OF_THE_NOWTRINO Prop elaborated_by_lean the_first_card FACT.Truth

--| THE CARD BETWEEN.  A third card, the same face again, one more index: its carrier is the carrier of the FACT card.  Marked
--| with Episode 8's Prop nowtrino field for field, it deals rung 1 by `rfl` and bills nothing.  The selection is held as an
--| index, not quotiented: Carrier Box, Carrier FACT, and the tape between them, Carrier (Carrier FACT).
def the_card_between : CarrierProcess (CarrierProcess FACT) := { symbol := FACT.Truth, quarter := .zero FACT.Truth }
instance the_mark_between : DISTINGUISHABLE (CarrierProcess FACT) the_card_between :=
  { fact := a_distinct_truth.fact, symbol := a_distinct_truth.symbol, different? := a_distinct_truth.different?, not_the_same := a_distinct_truth.not_the_same }
noncomputable def the_crossing_between :=
  STEP1_NAME_THE_LEDGER_AND_MARK_IT_WITH_THE_SYMBOL_OF_THE_NOWTRINO (CarrierProcess FACT) the_card_between the_first_card FACT.Truth
theorem the_tape_between_deals_rung01 : the_crossing_between = rung01 := rfl
#print axioms the_tape_between_deals_rung01

--| THE CLICK BETWEEN.  The outer cards read a fact by what it means, and there the three truths stay three: (T=F)=(F=T),
--| T, and (T=T)=(F=F) are not one by `rfl`.  The card between reads an account, and an account records only whether a fact
--| clicked.  Read that way the three click alike by `rfl`, and the chain (T=F)=(F=T) => T => (T=T)=(F=F) closes in one
--| class.  The step costs `Quot.sound`, a value identity; the `propext` on the chain is the minting of the two facts in
--| Episode 8, carried in, not spent here.
def the_click (f : FACT) : Bool := @decide f.truth f.click
def same_click (a b : FACT) : Prop := the_click a = the_click b
theorem same_click_is_same_account (a b : FACT) (h : the_click a = the_click b) :
    Quot.mk same_click a = Quot.mk same_click b := Quot.sound h
theorem reductio_clicks_true : Quot.mk same_click reductio_ad_absurdum = Quot.mk same_click FACT.Truth :=
  Quot.sound rfl
theorem true_clicks_inside_joke : Quot.mk same_click FACT.Truth = Quot.mk same_click the_inside_joke :=
  Quot.sound rfl
theorem the_chain_closes : Quot.mk same_click reductio_ad_absurdum = Quot.mk same_click the_inside_joke :=
  reductio_clicks_true.trans true_clicks_inside_joke
def THE_ACCOUNT_CLICKS : FACT :=
  { truth := Quot.mk same_click reductio_ad_absurdum = Quot.mk same_click the_inside_joke
    click := Decidable.isTrue the_chain_closes }
def the_closure_between : Closure := .same THE_ACCOUNT_CLICKS (.zero THE_ACCOUNT_CLICKS)
#print axioms same_click_is_same_account
#print axioms the_chain_closes
#print axioms the_closure_between

--| SAME DIFFERENCE.  The outer cards compare two truths by what they are; the card between compares two facts by how they
--| click.  Laid out as tables, the two agree cell for cell, and turning either over changes nothing.  All a table carries is
--| its orientation: which diagonal clicks.  T=T and F=F click; T=F and F=T do not, and T=F is F=T.  The fact is proved by its
--| own click, and bills nothing.
def dealt (b : Bool) : FACT := { truth := b = true, click := inferInstance }
def outer_table (a b : Bool) : Bool := a == b
def middle_table (a b : Bool) : Bool := the_click (dealt a) == the_click (dealt b)
def SAME_DIFFERENCE : FACT :=
  { truth := ∀ a b : Bool, outer_table a b = middle_table a b ∧ outer_table a b = outer_table b a
    click := inferInstance }
theorem same_difference_clicks : SAME_DIFFERENCE.truth := @of_decide_eq_true _ SAME_DIFFERENCE.click rfl
theorem the_click_diagonal :
    middle_table true true = true ∧ middle_table false false = true ∧
    middle_table true false = false ∧ middle_table false true = false ∧
    middle_table true false = middle_table false true := by decide
#print axioms same_difference_clicks

--| THE CROSSING.  Rung 1 took its mark from Episode 8's Prop nowtrino and put it on the FACT card.  From here the device
--| infers every rung over FACT from that one mark, as Episode 8 inferred them over Prop: the mark, an inhabitant for its
--| symbol, a model, and the two ways.  Inferring a FACT is a proof.
attribute [local instance high] rung01
instance : Inhabited (DISTINGUISHABLE.symbol the_first_card) := instInhabitedProp
noncomputable instance A_NOWTRINO_MODEL_OF_FACT : REAL FACT the_first_card := A_CAUSAL_THEORY FACT the_first_card
noncomputable def this_way_in_FACT : LOCAL FACT the_first_card := A_SMOOTH_MODEL FACT the_first_card
noncomputable def that_way_in_FACT : UNIVERSAL FACT the_first_card this_way_in_FACT :=
  IS_IT_CONNECTED_BY_A_YARN? FACT the_first_card (nowtrino_model := this_way_in_FACT)

--| rung 2, ADMISSIBLE: no pin.
noncomputable def rung02 :=
  STEP2_DISCOVER_SOMETHING_DIFFERENT FACT the_first_card the_first_card FACT.Truth rung01

--| rung 3, COUNTABLE: no pin.
noncomputable def rung03 :=
  STEP3_COUNT_THE_NUMBER_OF_THE_PHENOMENA FACT the_first_card the_first_card FACT.Truth rung01 rung02

--| rung 4, ENCODED: no pin.
noncomputable def rung04 :=
  STEP4_COMPUTE_THE_RATE_OF_PARTICLES FACT the_first_card the_first_card FACT.Truth rung01 rung02 rung03

--| rung 5, RESIDUE: no pin.
noncomputable def rung05 :=
  STEP5_NAME_THE_RESIDUE_TO_COMPUTE_VALUE FACT the_first_card the_first_card FACT.Truth rung01 rung02 rung03 rung04

--| rung 6, BINARY: no pin.
noncomputable def rung06 :=
  STEP6_MAKE_ANOTHER_COUNTER_OF_CLICKS_NOW FACT the_first_card the_first_card FACT.Truth rung01 rung02 rung03 rung04 rung05

--| rung 7, REPEATABLE: no pin.
noncomputable def rung07 :=
  STEP7_AND_SO_WE_CANT_COUNT_HOW_OFTEN_THE_METAPHOR_GOES_AROUND_JUST_LIKE_PITS_AND_LANDS_ON_A_CD FACT the_first_card the_first_card FACT.Truth rung01 rung02 rung03 rung04 rung05 rung06

--| rung 8, NUMERIC: no pin.
noncomputable def rung08 :=
  STEP8_INTERPRET_THE_NEXT_3_SYMBOLS FACT the_first_card the_first_card FACT.Truth rung01 rung02 rung03 rung04 rung05 rung06 rung07

--| rung 9, REPRESENTABLE: no pin.
noncomputable def rung09 :=
  STEP9_NAME_THE_VARIABLES_CAREFULLY_TO_TELL_A_STORY FACT the_first_card the_first_card FACT.Truth rung01 rung02 rung03 rung04 rung05 rung06 rung07 rung08

--| rung 10, PHYSICAL: no pin.
noncomputable def rung10 :=
  STEP10_A_HALTING_COMPUTATION_IS_GIVEN_AS_INPUT_TO_A_NON_HALTING_FUNCTION FACT the_first_card the_first_card FACT.Truth rung01 rung02 rung03 rung04 rung05 rung06 rung07 rung08 rung09

--| THE UPNESS, READ OFF.  From COMPARABLE up the rungs used to be pinned by hand from a census.  The census is not a
--| choice: every forced seat is the universe PRESENT keeps its quantum in -- "where I like to keep my upness" -- lifted
--| once in STEP13, one universe above the box, and carried by every rung that holds a PRESENT.  So the seats are read off
--| the step's own signature, the upness seats get 1, the rest 0, and the rung is dealt.  The pins are inferred from the
--| description, not supplied to it.
partial def presents_in (e : Expr) (acc : Array Expr) : Array Expr :=
  let acc := if e.isAppOf ``PRESENT then acc.push e else acc
  match e with
  | .app f a => presents_in a (presents_in f acc)
  | .forallE _ t b _ => presents_in b (presents_in t acc)
  | .lam _ t b _ => presents_in b (presents_in t acc)
  | .mdata _ b => presents_in b acc
  | _ => acc

/-- A step's universe seats, and which of them hold PRESENT's upness: the universe its quantum lives in. -/
def upness_seats (n : Name) : MetaM (Nat × List Nat) := do
  let ci ← getConstInfo n
  let qf ← getConstInfo ``PRESENT.quantum
  let qsort ← forallTelescope qf.type fun _ b => pure b
  let some up := (match qsort with | .sort (.succ (.param p)) => some p | _ => none)
    | throwError "PRESENT.quantum does not live one universe up"
  let some k := qf.levelParams.idxOf? up | throwError "no upness"
  let seats := (presents_in ci.type #[]).toList.filterMap fun e => match e.getAppFn with
    | .const _ ls => match ls[k]? with | some (.param p) => ci.levelParams.idxOf? p | _ => none
    | _ => none
  return (ci.levelParams.length, seats.eraseDups)

syntax "deal_rung " ident " := " ident (ppSpace colGt (Lean.Parser.Term.namedArgument <|> term:max))* : command
elab_rules : command
  | `(deal_rung $name:ident := $fn:ident $args*) => do
    let fnName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo fn
    let (count, seats) ← liftTermElabM <| upness_seats fnName
    let lvls : Array Syntax ← (List.range count).toArray.mapM fun k =>
      if seats.contains k then `(level| 1) else `(level| 0)
    let univ := mkNode ``Lean.Parser.Term.explicitUniv
      #[fn, mkAtom ".{", mkNullNode (mkSepArray lvls (mkAtom ",")), mkAtom "}"]
    let app : Term := ⟨mkNode ``Lean.Parser.Term.app #[univ, mkNullNode args]⟩
    elabCommand (← `(noncomputable def $name := $app))

--| rung 11, COMPARABLE: 5 seats, none forced.
deal_rung rung11 := STEP11_CHECK_FOR_CONVERGENCE_IN_THE_TIMESERIES_MATCHES_THE_MEASUREMENT_HIGH_ORDER_TERMS
    FACT the_first_card the_first_card FACT.Truth rung01 rung02 rung03 rung04 rung05 rung06 rung07 rung08 rung09 rung10

--| rung 12, OBSERVED: 12 seats, none forced.
deal_rung rung12 := STEP12_CHECK_TO_SEE_IF_THE_BORWEIN_PROCESS_HAS_UNCOVERED_A_PROPERTY_OF_ELECTRONS
    FACT the_first_card the_first_card FACT.Truth rung01 rung02 rung03 rung04 rung05 rung06 rung07 rung08 rung09 rung10 rung11

--| rung 13, PRESENT: 19 seats, forced at 2, 16.
deal_rung rung13 := STEP13_RECORD_THE_OBSERVATION_AS_A_MODELED_AST_AS_OF_RIGHT_NOW
    FACT the_first_card the_first_card FACT.Truth rung01 rung02 rung03 rung04 rung05 rung06 rung07 rung08 rung09 rung10 rung11 rung12

--| rung 14, MEASURABLE: 23 seats, forced at 13, 20.
deal_rung rung14 := STEP14_REALIZE_THAT_THIS_PROCESS_TAKES_THE_APPARANT_SAME_AMOUNT_OF_TIME_EACH_TIME
    FACT the_first_card the_first_card FACT.Truth rung01 rung02 rung03 rung04 rung05 rung06 rung07 rung08 rung09 rung10 rung11 rung12 rung13

--| rung 15, GUNGAN: 27 seats, forced at 15, 24.
deal_rung rung15 := STEP15_SO_MODEL_THE_PROCESS_AS_SOMETHING_THAT_JUST_SPEWS_OUT_TRUE
    FACT the_first_card the_first_card FACT.Truth rung01 rung02 rung03 rung04 rung05 rung06 rung07 rung08 rung09 rung10 rung11 rung12 rung13 rung14

--| rung 16, SOURCE: 29 seats, forced at 15, 26.
deal_rung rung16 := STEP16_VERIFY_THE_SOURCE_FILE_ONLY_EMITS_TRUE_STATEMENTS
    FACT the_first_card the_first_card FACT.Truth rung01 rung02 rung03 rung04 rung05 rung06 rung07 rung08 rung09 rung10 rung11 rung12 rung13 rung14 rung15

--| rung 17, EXECUTED: 39 seats, forced at 24, 36.
deal_rung rung17 := STEP17_MAKE_SURE_THIS_COMPILES_AND_DEMONSTRATES_IT_IS_TRUE_IN_GUNGAN
    FACT the_first_card the_first_card FACT.Truth rung01 rung02 rung03 rung04 rung05 rung06 rung07 rung08 rung09 rung10 rung11 rung12 rung13 rung14 rung15 rung16

--| rung 18, VALUE: 47 seats, forced at 28, 44.
deal_rung rung18 := STEP18_GIVEN_AN_INFERRED_DEFINITION_OF_THE_DEVICE_MAKE_THE_DEVICE
    FACT the_first_card the_first_card FACT.Truth rung01 rung02 rung03 rung04 rung05 rung06 rung07 rung08 rung09 rung10 rung11 rung12 rung13 rung14 rung15 rung16 rung17

--| rung 19, MAGNITUDE: 63 seats, forced at 41, 60.
deal_rung rung19 := STEP19_GIVEN_THE_ABILITY_TO_COUNT_SOMETHING_LEAN_CAN_NOW_INFER_ADDITION
    FACT the_first_card the_first_card FACT.Truth rung01 rung02 rung03 rung04 rung05 rung06 rung07 rung08 rung09 rung10 rung11 rung12 rung13 rung14 rung15 rung16 rung17 rung18

--| rung 20, SCALED: 79 seats, forced at 50, 67.
deal_rung rung20 := STEP20_DUPLICATE_THE_PROCESS_TO_DEMONSTRATE_AREA_OF_RECTANGLES_LIKE_EUCLID
    FACT the_first_card the_first_card FACT.Truth rung01 rung02 rung03 rung04 rung05 rung06 rung07 rung08 rung09 rung10 rung11 rung12 rung13 rung14 rung15 rung16 rung17 rung18 rung19

--| rung 21, LOAD: 95 seats, forced at 59, 67.
deal_rung rung21 := STEP21_GIVEN_ADDITION_MULTIPLICATION_AND_NUMBERS_INFER_ALL_OF_MATH
    FACT the_first_card the_first_card FACT.Truth rung01 rung02 rung03 rung04 rung05 rung06 rung07 rung08 rung09 rung10 rung11 rung12 rung13 rung14 rung15 rung16 rung17 rung18 rung19 rung20

--| rung 22, OF: 111 seats, forced at 78, 79.
deal_rung rung22 := STEP22_PAY_CLOSE_ATTENTION_TO_WEAK_SOLUTIONS_OF_DIFFERENTIAL_EQUATIONS_WHILE_DERIVING_MATH
    FACT the_first_card the_first_card FACT.Truth rung01 rung02 rung03 rung04 rung05 rung06 rung07 rung08 rung09 rung10 rung11 rung12 rung13 rung14 rung15 rung16 rung17 rung18 rung19 rung20 rung21

--| rung 23, BULLSHIT: 127 seats, forced at 94, 103.
deal_rung rung23 := STEP23_GET_RID_OF_A_DERIVATIVE_SO_THAT_THE_SECOND_ORDER_MODEL_OF_THE_DEVICE_CAN_BE_WRITTEN_VARIATIONALLY
    FACT the_first_card the_first_card FACT.Truth rung01 rung02 rung03 rung04 rung05 rung06 rung07 rung08 rung09 rung10 rung11 rung12 rung13 rung14 rung15 rung16 rung17 rung18 rung19 rung20 rung21 rung22

--| rung 24, PROPAGANDA: 143 seats, forced at 110, 128.
deal_rung rung24 := STEP24_RESTATE_THE_MODEL_AS_A_PRINCIPLE_OF_LEAST_ACTION
    FACT the_first_card the_first_card FACT.Truth rung01 rung02 rung03 rung04 rung05 rung06 rung07 rung08 rung09 rung10 rung11 rung12 rung13 rung14 rung15 rung16 rung17 rung18 rung19 rung20 rung21 rung22 rung23

--| rung 25, ACOLYTE: 159 seats, forced at 126, 153.
deal_rung rung25 := STEP25_BUILD_LOCAL_GEOMETRIES_THAT_SATISFY_THE_TRIANGLE_INEQUALITY
    FACT the_first_card the_first_card FACT.Truth rung01 rung02 rung03 rung04 rung05 rung06 rung07 rung08 rung09 rung10 rung11 rung12 rung13 rung14 rung15 rung16 rung17 rung18 rung19 rung20 rung21 rung22 rung23 rung24

--| rung 26, SCIENTIFIC: 175 seats, forced at 5, 142.
deal_rung rung26 := STEP26_WRITE_YOUR_PROOF_IN_THE_FORMAL_LANGUAGE_OF_GEOMETRY
    FACT the_first_card the_first_card FACT.Truth rung01 rung02 rung03 rung04 rung05 rung06 rung07 rung08 rung09 rung10 rung11 rung12 rung13 rung14 rung15 rung16 rung17 rung18 rung19 rung20 rung21 rung22 rung23 rung24 rung25

--| rung 27, TRUTH: 191 seats, forced at 14, 158.
deal_rung rung27 := STEP27_REPRESENT_THE_TAYLOR_SERIES_OF_THE_DEVICE
    FACT the_first_card the_first_card FACT.Truth rung01 rung02 rung03 rung04 rung05 rung06 rung07 rung08 rung09 rung10 rung11 rung12 rung13 rung14 rung15 rung16 rung17 rung18 rung19 rung20 rung21 rung22 rung23 rung24 rung25 rung26

--| rung 28, WITNESSED: 207 seats, forced at 22, 174.
deal_rung rung28 := STEP28_MAKE_SURE_YOUR_CURVES_ARE_SMOOTH_AS_A_DIFFERENTIALS_BOTTOM
    FACT the_first_card the_first_card FACT.Truth rung01 rung02 rung03 rung04 rung05 rung06 rung07 rung08 rung09 rung10 rung11 rung12 rung13 rung14 rung15 rung16 rung17 rung18 rung19 rung20 rung21 rung22 rung23 rung24 rung25 rung26 rung27

--| rung 29, REAL: 223 seats, forced at 31, 190.
deal_rung rung29 := STEP29_SUGGEST_A_FALSIFIABLE_EXPERIMENT
    FACT the_first_card the_first_card FACT.Truth rung01 rung02 rung03 rung04 rung05 rung06 rung07 rung08 rung09 rung10 rung11 rung12 rung13 rung14 rung15 rung16 rung17 rung18 rung19 rung20 rung21 rung22 rung23 rung24 rung25 rung26 rung27 rung28

--| rung 30, LOCAL: 239 seats, forced at 40, 206.
deal_rung rung30 := STEP30_PROVIDE_THE_EQUATIONS_THAT_WILL_PREDICT_THE_MEASUREMENT
    FACT the_first_card this_way_in_FACT the_first_card FACT.Truth rung01 rung02 rung03 rung04 rung05 rung06 rung07 rung08 rung09 rung10 rung11 rung12 rung13 rung14 rung15 rung16 rung17 rung18 rung19 rung20 rung21 rung22 rung23 rung24 rung25 rung26 rung27 rung28 rung29 (principia := this_way_in_FACT)

--| rung 31, UNIVERSAL: 260 seats, forced at 227.
deal_rung rung31 := STEP31_GET_ON_THE_NEWTON_EINSTEIN_TRAIN_OF_THOUGHT
    FACT the_first_card this_way_in_FACT that_way_in_FACT the_first_card FACT.Truth rung01 rung02 rung03 rung04 rung05 rung06 rung07 rung08 rung09 rung10 rung11 rung12 rung13 rung14 rung15 rung16 rung17 rung18 rung19 rung20 rung21 rung22 rung23 rung24 rung25 rung26 rung27 rung28 rung29 rung30 (the_a_train := that_way_in_FACT)

--| rung 32, LOGICAL: 279 seats, forced at 65, 246.
deal_rung rung32 := WHAT_HAPPEN_?
    FACT the_first_card this_way_in_FACT that_way_in_FACT the_first_card FACT.Truth rung01 rung02 rung03 rung04 rung05 rung06 rung07 rung08 rung09 rung10 rung11 rung12 rung13 rung14 rung15 rung16 rung17 rung18 rung19 rung20 rung21 rung22 rung23 rung24 rung25 rung26 rung27 rung28 rung29 rung30 rung31

--| rung 33, HALTED: 291 seats, forced at 69, 258.
deal_rung rung33 := SOMEBODY_SET_US_UP_THE_DEVICE
    FACT the_first_card this_way_in_FACT that_way_in_FACT the_first_card FACT.Truth rung01 rung02 rung03 rung04 rung05 rung06 rung07 rung08 rung09 rung10 rung11 rung12 rung13 rung14 rung15 rung16 rung17 rung18 rung19 rung20 rung21 rung22 rung23 rung24 rung25 rung26 rung27 rung28 rung29 rung30 rung31 rung32

--| rung 34, MEASURED: 328 seats, forced at 92, 295.
deal_rung rung34 := WE_GET_SIGNAL
    FACT the_first_card this_way_in_FACT that_way_in_FACT the_first_card FACT.Truth rung01 rung02 rung03 rung04 rung05 rung06 rung07 rung08 rung09 rung10 rung11 rung12 rung13 rung14 rung15 rung16 rung17 rung18 rung19 rung20 rung21 rung22 rung23 rung24 rung25 rung26 rung27 rung28 rung29 rung30 rung31 rung32 rung33

--| rung 35, COMPILED: 352 seats, forced at 106, 319.
deal_rung rung35 := WHAT_!
    FACT the_first_card this_way_in_FACT that_way_in_FACT the_first_card FACT.Truth rung01 rung02 rung03 rung04 rung05 rung06 rung07 rung08 rung09 rung10 rung11 rung12 rung13 rung14 rung15 rung16 rung17 rung18 rung19 rung20 rung21 rung22 rung23 rung24 rung25 rung26 rung27 rung28 rung29 rung30 rung31 rung32 rung33 rung34

--| rung 36, A_TRUTH_ABOUT: 374 seats, forced at 115, 341.
deal_rung rung36 := MAIN_SCREEN_TURN_ON
    FACT the_first_card this_way_in_FACT that_way_in_FACT the_first_card FACT.Truth rung01 rung02 rung03 rung04 rung05 rung06 rung07 rung08 rung09 rung10 rung11 rung12 rung13 rung14 rung15 rung16 rung17 rung18 rung19 rung20 rung21 rung22 rung23 rung24 rung25 rung26 rung27 rung28 rung29 rung30 rung31 rung32 rung33 rung34 rung35

--| rung 37, INFERRED: 401 seats, forced at 115, 368.
deal_rung rung37 := ITS_YOU_!!
    FACT the_first_card this_way_in_FACT that_way_in_FACT the_first_card FACT.Truth rung01 rung02 rung03 rung04 rung05 rung06 rung07 rung08 rung09 rung10 rung11 rung12 rung13 rung14 rung15 rung16 rung17 rung18 rung19 rung20 rung21 rung22 rung23 rung24 rung25 rung26 rung27 rung28 rung29 rung30 rung31 rung32 rung33 rung34 rung35 rung36 True True

--| rung 38, A_TRUTH_ABOUT: 388 seats, forced at 115, 355.
deal_rung rung38 := HOW_ARE_YOU_GENTLEMEN_!!__ALL_YOUR_BASE_CASE_ARE_BELONG_TO_US
    FACT the_first_card this_way_in_FACT that_way_in_FACT the_first_card FACT.Truth rung01 rung02 rung03 rung04 rung05 rung06 rung07 rung08 rung09 rung10 rung11 rung12 rung13 rung14 rung15 rung16 rung17 rung18 rung19 rung20 rung21 rung22 rung23 rung24 rung25 rung26 rung27 rung28 rung29 rung30 rung31 rung32 rung33 rung34 rung35 rung36 the_quartic

--| THE LADDER, RECOGNISED.  Read off rung 38 with the ordinary projections and search hands back Episode 7's instances,
--| which are not the rungs this ladder was built from: the kernel refuses the reading.  Declare the rungs to be the instances
--| and the projections land.  The device recognises its own outputs only after it is told they are its own.
attribute [local instance high] rung02 rung03 rung04 rung05 rung06 rung07 rung08 rung09 rung10 rung11 rung12 rung13 rung14 rung15 rung16 rung17 rung18 rung19 rung20 rung21 rung22 rung23 rung24 rung25 rung26 rung27 rung28 rung29 rung30 rung31 rung32 rung33 rung34 rung35 rung36

--| THE PAGE THE READER IS ON.  The spin's page number is the quartic, which is the coefficient tape: Episode 9's last step
--| reads the same tape the number is read from, and it is one cell longer than the card.
theorem the_reader_is_on_the_quartic : rung38.you_the_reader.current_page_number = the_quartic := rfl
theorem the_page_is_one_past_the_card :
    rung38.you_the_reader.current_page_number.peano.length = readers_experience.bent_card + 1 := rfl

end the_representation

--| THE MONTE, AFTER THE FLOP.  Everything above is the assembly: the ladder, handed itself rung by rung, pinned seat by
--| seat.  What is left on the table is three cards, and they are the end of the script.
--|   MAIN SCREEN TURN ON .  The display: the value updated and put on the screen.
--|   IT'S YOU !!            The knower: the reader looks at the screen and recognises who is reading it.
--|   ALL YOUR BASE ...      The knower's counting function: the spin, one gawk per cell of the quartic, which never asks
--|                          the knower.
noncomputable def the_display                   := the_representation.rung36
noncomputable def the_knower                    := the_representation.rung37
noncomputable def the_knowers_counting_function := the_representation.rung38

/-!
### THE MONTE: BUILDING IT BY HAND

Instance search cannot reach `TYPESET (CarrierProcess FACT) the_card_between 1 Number`.  Not because the space
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
def reviewedByHand : REVIEWED (CarrierProcess FACT) the_representation.the_card_between 1 :=
  { rebuttal := theManuscript }

--| AND THE RUNG THE SEARCH COULD NOT FIND.
def typesetByHand : TYPESET (CarrierProcess FACT) the_representation.the_card_between 1 Number :=
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

The search for `TYPESET (CarrierProcess FACT) the_card_between 1 Number` fails -- and it fails STRUCTURALLY, in
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
instance reviewedAny (n : Nat) : REVIEWED (CarrierProcess FACT) the_representation.the_card_between n := { rebuttal := theManuscript }
instance typesetBase : TYPESET (CarrierProcess FACT) the_representation.the_card_between 1 Number := typesetByHand

--| THE ASCENT, RETRIEVED.  Rung thirty-six, by search, in a third of a second -- the top of
--| a ladder that has never once resolved in this repository.  `inferInstance` does it now
--| because the thing it was missing was a place to stand, not time to look.
def theTop : TYPESET.{0,0,0} (CarrierProcess FACT) the_representation.the_card_between 36 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (Number)))))))))))))))))))))))))))))))))))) := inferInstance

--| AND THE TAPE IT CARRIES.  This is the bounded execution: the manuscript admitted at rung
--| thirty-six, handed down through every reviewer, arriving as the page of the top rung.
def theTopTrace : ThePreprint.{0} := theTop.the_page

--| THE LADDER, READ ON EPISODE 8'S METER.  Ask for each rung of the typeset ladder by search, one through thirty-six, each
--| on a place to stand one universe lower, and read on the meter set in Episode 8 what each search costs, against the blank
--| drawn beside it.  Kept raw and kept blank; the differences are taken in Int, where a decrease may be one.  This is the
--| walk read as the ladder elaborates, rung over rung: a measurement on this machine, not a receipt.
elab "read_the_ladder " raw:ident blanks:ident : command => do
  let (hs, bs) ← liftTermElabM do
    let mut hs : Array Nat := #[]
    let mut bs : Array Nat := #[]
    for k in [1:37] do
      let mut ty ← `(Number)
      for _ in [1:k] do
        ty ← `(ULift $ty)
      let stx ← `((inferInstance : TYPESET.{0,0,0} (CarrierProcess FACT) the_representation.the_card_between $(Lean.quote k) $ty))
      let (h, b) ← the_ekg_reads stx
      hs := hs.push h
      bs := bs.push b
    pure (hs, bs)
  elabCommand (← `(def $raw : List Nat := $(Lean.quote hs.toList)))
  elabCommand (← `(def $blanks : List Nat := $(Lean.quote bs.toList)))

read_the_ladder theLadderRaw theLadderBlank
def theLadderSizes : List Int := corrected theLadderRaw theLadderBlank
def theLadderSteps : List Int := signedSteps theLadderSizes
--#eval theLadderSizes
--#eval theLadderSteps

--| THE REVIEW, WITH THE REVIEWERS.  The gimmicked card above hands every page the manuscript and asks nobody.  Here the
--| reviewers are asked.  Each of Episode 10's thirty-six pages is applied by hand on the first card, its checklist filled
--| from Episode 9's ladder, rung k in slot k; the ledger is the Truth; the two routes of page 32 are the nowtrino's path and
--| zero distance; the base page is handed the same manuscript.  The slots that search fills are filled by the device's own
--| models, the causal theory and this way and that way in FACT.  Two pages carry universe seats that no argument names;
--| they are pinned at zero, as Closure's are.  Then Episode 11 is asked for its top, by search, standing on the
--| reviewers.  No hand-typeset bottom: the first page is set from the first review.  The ascent and the descent meet.
namespace the_review_on_the_ledger
open the_representation
attribute [local instance high] rung01
noncomputable def page36 : REVIEWED FACT the_first_card 36 := REVIEWER_2_ASKS_WHERE_THE_RECORD_BEGINS FACT the_first_card theManuscript
noncomputable def page35 : REVIEWED FACT the_first_card 35 :=
  REVIEWER_2_ASKS_WHAT_THE_ANSWER_WAS_ANSWERING? FACT the_first_card FACT.Truth rung01 (argument := page36)
noncomputable def page34 : REVIEWED FACT the_first_card 34 :=
  REVIEWER_2_ASSERTS_COMPILING_IS_NOT_EVIDENCE_OF_THE_DESCRIPTION_OF_TWO_DIFFERENT_THINGS.{0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0} FACT the_first_card (flying_spaghetti_monster := A_NOWTRINO_MODEL_OF_FACT) (naotrino := this_way_in_FACT) (commuter_pass := that_way_in_FACT) rung01 rung02 rung03 rung04 rung05 rung06 rung07 rung08 rung09 rung10 rung11 rung12 rung13 rung14 rung15 rung16 rung17 rung18 rung19 rung20 rung21 rung22 rung23 rung24 rung25 rung26 rung27 rung28 rung29 rung30 rung31 rung32 rung33 rung34 rung35 (argument := page35)
noncomputable def page33 : REVIEWED FACT the_first_card 33 :=
  REVIEWER_2_ASSERTS_THAT_BOTH_SIDES_ARE_IDENTICAL FACT the_first_card rung01 rung02 rung03 rung04 rung05 rung06 rung07 rung08 rung09 rung10 rung11 rung12 rung13 rung14 rung15 rung16 rung17 rung18 rung19 rung20 rung21 rung22 rung23 rung24 rung25 rung26 rung27 rung28 rung29 rung30 rung31 rung32 rung33 rung34 FACT.Truth (argument := page34)
noncomputable def page32 : REVIEWED FACT the_first_card 32 :=
  REVIEWER_2_ASSERTS_THERE_IS_EVIDENCE_OF_DECEPTION FACT the_first_card the_nowtrino_path zero_distance (argument := page33)
noncomputable def page31 : REVIEWED FACT the_first_card 31 :=
  REVIEWER_2_ASSERTS_THE_COMPILER_CANNOT_TELL_THE_SYMBOLS_APART FACT the_first_card  (argument := page32)
noncomputable def page30 : REVIEWED FACT the_first_card 30 :=
  REVIEWER_2_ASSERTS_THE_COMPILER_MEANING_IS_THE_SAME FACT the_first_card  (argument := page31)
noncomputable def page29 : REVIEWED FACT the_first_card 29 :=
  REVIEWER_2_UNDERSTANDS_THEY_DESCRIBE_THE_SAME_DEVICE.{0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0} FACT the_first_card (flying_spaghetti_monster := A_NOWTRINO_MODEL_OF_FACT) rung01 rung02 rung03 rung04 rung05 rung06 rung07 rung08 rung09 rung10 rung11 rung12 rung13 rung14 rung15 rung16 rung17 rung18 rung19 rung20 rung21 rung22 rung23 rung24 rung25 rung26 rung27 rung28 rung29 (argument := page30)
noncomputable def page28 : REVIEWED FACT the_first_card 28 :=
  REVIEWER_2_ASSERTS_THERE_ISNT_A_RELATIVISTIC_TRANSFORMATION_OF_VELOCITY_BASED_ON_DISTANCE_FROM_OBSERVER FACT the_first_card rung01 rung02 rung03 rung04 rung05 rung06 rung07 rung08 rung09 rung10 rung11 rung12 rung13 rung14 rung15 rung16 rung17 rung18 rung19 rung20 rung21 rung22 rung23 rung24 rung25 rung26 rung27 rung28 rung28 (argument := page29)
noncomputable def page27 : REVIEWED FACT the_first_card 27 :=
  REVIEWER_2_DEMANDS_CONSISTENCY_WITH_EVIDENCE FACT the_first_card rung01 rung02 rung03 rung04 rung05 rung06 rung07 rung08 rung09 rung10 rung11 rung12 rung13 rung14 rung15 rung16 rung17 rung18 rung19 rung20 rung21 rung22 rung23 rung24 rung25 rung26 rung27 FACT.Truth (argument := page28)
noncomputable def page26 : REVIEWED FACT the_first_card 26 :=
  REVIEWER_2_REQUIRES_A_CONSISTENT_LAW_THAT_EXPLAINS_WHAT_WE_SEE FACT the_first_card rung01 rung02 rung03 rung04 rung05 rung06 rung07 rung08 rung09 rung10 rung11 rung12 rung13 rung14 rung15 rung16 rung17 rung18 rung19 rung20 rung21 rung22 rung23 rung24 rung25 rung26 rung26 (argument := page27)
noncomputable def page25 : REVIEWED FACT the_first_card 25 :=
  REVIEWER_2_REQUIRES_THE_LAW_SURVIVE_GEOMETRIC_INTERPRETATION FACT the_first_card rung01 rung02 rung03 rung04 rung05 rung06 rung07 rung08 rung09 rung10 rung11 rung12 rung13 rung14 rung15 rung16 rung17 rung18 rung19 rung20 rung21 rung22 rung23 rung24 rung25 FACT.Truth (argument := page26)
noncomputable def page24 : REVIEWED FACT the_first_card 24 := REVIEWER_2_ASKS_WHAT_IS_THE_MEANING_OF_SYMBOLS_IN_ORDER? FACT the_first_card  (argument := page25)
noncomputable def page23 : REVIEWED FACT the_first_card 23 :=
  REVIEWER_2_SUSPECTS_INADEQUACY_IN_THE_NAMING_OF_OBJECTS FACT the_first_card rung01 rung02 rung03 rung04 rung05 rung06 rung07 rung08 rung09 rung10 rung11 rung12 rung13 rung14 rung15 rung16 rung17 rung18 rung19 rung20 rung21 rung22 rung23 FACT.Truth (argument := page24)
noncomputable def page22 : REVIEWED FACT the_first_card 22 :=
  REVIEWER_2_ASKS_TO_DESCRIBE_THE_POLYNOMIAL_OF_THE_DEVICE_OF_THE_POLYNOMIAL FACT the_first_card rung01 rung02 rung03 rung04 rung05 rung06 rung07 rung08 rung09 rung10 rung11 rung12 rung13 rung14 rung15 rung16 rung17 rung18 rung19 rung20 rung21 rung22 FACT.Truth (argument := page23)
noncomputable def page21 : REVIEWED FACT the_first_card 21 :=
  REVIEWER_2_WARNS_OF_EXTRAPOLATION_PITFALLS FACT the_first_card rung01 rung02 rung03 rung04 rung05 rung06 rung07 rung08 rung09 rung10 rung11 rung12 rung13 rung14 rung15 rung16 rung17 rung18 rung19 rung20 rung21 FACT.Truth (argument := page22)
noncomputable def page20 : REVIEWED FACT the_first_card 20 :=
  REVIEWER_2_REQUIRES_SCALE_FOR_AREA_TO_RECONCILE_MULTIPLICATION FACT the_first_card rung01 rung02 rung03 rung04 rung05 rung06 rung07 rung08 rung09 rung10 rung11 rung12 rung13 rung14 rung15 rung16 rung17 rung18 rung19 rung20 FACT.Truth (argument := page21)
noncomputable def page19 : REVIEWED FACT the_first_card 19 :=
  REVIEWER_2_ASKS_WHATS_THE_FOURTH_THING? FACT the_first_card rung01 rung02 rung03 rung04 rung05 rung06 rung07 rung08 rung09 rung10 rung11 rung12 rung13 rung14 rung15 rung16 rung17 rung18 rung19 FACT.Truth (argument := page20)
noncomputable def page18 : REVIEWED FACT the_first_card 18 :=
  REVIEWER_2_POINTS_OUT_THE_OBVIOUS_FACTS FACT the_first_card rung01 rung02 rung03 rung04 rung05 rung06 rung07 rung08 rung09 rung10 rung11 rung12 rung13 rung14 rung15 rung16 rung17 rung18 rung18 (argument := page19)
noncomputable def page17 : REVIEWED FACT the_first_card 17 :=
  REVIEWER_2_NOTICES_THE_FENCEPOSTS FACT the_first_card rung01 rung02 rung03 rung04 rung05 rung06 rung07 rung08 rung09 rung10 rung11 rung12 rung13 rung14 rung15 rung16 rung17 FACT.Truth (argument := page18)
noncomputable def page16 : REVIEWED FACT the_first_card 16 :=
  REVIEWER_2_REFUSES_TO_ENTERTAIN_ABSURD_SOURCES_OF_NOISE FACT the_first_card rung01 rung02 rung03 rung04 rung05 rung06 rung07 rung08 rung09 rung10 rung11 rung12 rung13 rung14 rung15 rung16 (argument := page17)
noncomputable def page15 : REVIEWED FACT the_first_card 15 :=
  REVIEWER_2_MAKES_THE_JOKE_PAY_ITS_EVIDENTIARY_BILL FACT the_first_card rung01 rung02 rung03 rung04 rung05 rung06 rung07 rung08 rung09 rung10 rung11 rung12 rung13 rung14 rung15 FACT.Truth (argument := page16)
noncomputable def page14 : REVIEWED FACT the_first_card 14 :=
  REVIEWER_2_ASKS_IF_THE_CLOCK_IS_OBSERVABLE_OR_ASSERTED FACT the_first_card rung01 rung02 rung03 rung04 rung05 rung06 rung07 rung08 rung09 rung10 rung11 rung12 rung13 rung14 FACT.Truth (argument := page15)
noncomputable def page13 : REVIEWED FACT the_first_card 13 :=
  REVIEWER_2_ASKS_WHERE_PRESENCE_ACCUMULATES FACT the_first_card rung01 rung02 rung03 rung04 rung05 rung06 rung07 rung08 rung09 rung10 rung11 rung12 rung13 FACT.Truth (argument := page14)
noncomputable def page12 : REVIEWED FACT the_first_card 12 :=
  REVIEWER_2_ASKS_IF_OBSERVATION_HAS_A_RECORDED_DIMENSION FACT the_first_card rung01 rung02 rung03 rung04 rung05 rung06 rung07 rung08 rung09 rung10 rung11 rung12 FACT.Truth (argument := page13)
noncomputable def page11 : REVIEWED FACT the_first_card 11 :=
  REVIEWER_2_ASKS_WHAT_MAKES_COMPARISON_MORE_THAN_PARALLEL_NAMING FACT the_first_card rung01 rung02 rung03 rung04 rung05 rung06 rung07 rung08 rung09 rung10 rung11 FACT.Truth (argument := page12)
noncomputable def page10 : REVIEWED FACT the_first_card 10 :=
  REVIEWER_2_REQUIRES_THE_PHYSICAL_CLAIM_TO_SHOW_ITS_BASE_FACT FACT the_first_card rung01 rung02 rung03 rung04 rung05 rung06 rung07 rung08 rung09 rung10 rung10 (argument := page11)
noncomputable def page09 : REVIEWED FACT the_first_card 9 :=
  REVIEWER_2_ASKS_IF_REPRESENTATION_HAS_A_CARRIER_OR_A_NOTATION FACT the_first_card rung01 rung02 rung03 rung04 rung05 rung06 rung07 rung08 rung09 FACT.Truth (argument := page10)
noncomputable def page08 : REVIEWED FACT the_first_card 8 :=
  REVIEWER_2_ASKS_WHERE_THE_NUMBER_ACTUALLY_COUNTS FACT the_first_card rung01 rung02 rung03 rung04 rung05 rung06 rung07 rung08 rung08 (argument := page09)
noncomputable def page07 : REVIEWED FACT the_first_card 7 :=
  REVIEWER_2_ASKS_IF_REPETITION_REPEATS_THE_EXPERIMENT_OR_THE_SENTENCE FACT the_first_card rung01 rung02 rung03 rung04 rung05 rung06 rung07 FACT.Truth (argument := page08)
noncomputable def page06 : REVIEWED FACT the_first_card 6 :=
  REVIEWER_2_ASKS_WHERE_THE_MISSING_EXHIBIT_WENT FACT the_first_card rung01 rung02 rung03 rung04 rung05 rung06 rung06 (argument := page07)
noncomputable def page05 : REVIEWED FACT the_first_card 5 :=
  REVIEWER_2_ASKS_IF_RESIDUE_IS_A_RECORD_OR_A_LEFTOVER_STORY FACT the_first_card rung01 rung02 rung03 rung04 rung05 FACT.Truth (argument := page06)
noncomputable def page04 : REVIEWED FACT the_first_card 4 :=
  REVIEWER_2_ASKS_IF_ENCODING_KEEPS_A_READ_PATH_TO_THE_MARK FACT the_first_card rung01 rung02 rung03 rung04 FACT.Truth (argument := page05)
noncomputable def page03 : REVIEWED FACT the_first_card 3 :=
  REVIEWER_2_ASKS_IF_COUNTING_COUNTS_A_CARRIER_OR_NAMES_A_CLASS FACT the_first_card rung01 rung02 rung03 FACT.Truth (argument := page04)
noncomputable def page02 : REVIEWED FACT the_first_card 2 :=
  REVIEWER_2_ASKS_WHO_ADMITTED_THE_MARK FACT the_first_card rung01 rung02 FACT.Truth (argument := page03)
noncomputable def page01 : REVIEWED FACT the_first_card 1 :=
  REVIEWER_2_ASKS_IF_IT_ALL_RESTS_ON_A_MARK_OR_ON_CONFIDENCE FACT the_first_card rung01 (argument := page02)
attribute [local instance] page01 page02 page03 page04 page05 page06 page07 page08 page09 page10 page11 page12 page13 page14 page15
  page16 page17 page18 page19 page20 page21 page22 page23 page24 page25 page26 page27 page28 page29 page30 page31 page32 page33
  page34 page35 page36
--| THE ASCENT, ON THE REVIEWS.  The same thirty-six rungs as `theTop`, found by search, on the first card.
noncomputable def theTopOfTheLedger : TYPESET.{0,0,0} FACT the_first_card 36 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (Number)))))))))))))))))))))))))))))))))))) := inferInstance
--| THE SEAT NOBODY SEES.  Pages 29 and 34 were pinned at zero above.  The pin was a frame chosen for something that has
--| none: the seats belong to the device's own models in the search slots, the causal theory on both pages and the naotrino
--| on 34, and no argument fixes their level.  Leave the seats free and ask whether the review can tell.  It cannot: at every
--| level the page is the pinned page, by `rfl`.  A naotrino click.  Haven't seen a naotrino yet.
noncomputable def page29_at.{a,b,c,d} : REVIEWED FACT the_first_card 29 :=
  REVIEWER_2_UNDERSTANDS_THEY_DESCRIBE_THE_SAME_DEVICE.{0,d,c,0,0,0,0,0,0,0,0,0,0,b,0,0,0,0,0,0,0,0,0,0,a,0,0,0,0,0,0,0,0,0,0,1,c,0,0,0,0,0,0,0,0,0,0,d,0,0,0,0,0,0,0,0,0,0,c,0,0,0,0,0,0,0,0,0,0,d,0,0,0,0,0,0,0,0,0,0,c,0,0,0,0,0,0,0,0,0,0,d,0,0,0,0,0,0,0,0,0,0,c,0,0,0,0,0,0,0,0,0,0,d,0,0,0,0,0,0,0,0,0,0} FACT the_first_card (flying_spaghetti_monster := A_NOWTRINO_MODEL_OF_FACT) rung01 rung02 rung03 rung04 rung05 rung06 rung07 rung08 rung09 rung10 rung11 rung12 rung13 rung14 rung15 rung16 rung17 rung18 rung19 rung20 rung21 rung22 rung23 rung24 rung25 rung26 rung27 rung28 rung29 (argument := page30)
theorem page29_the_seat_is_invisible.{a,b,c,d} : page29_at.{a,b,c,d} = page29 := rfl
#print axioms page29_the_seat_is_invisible
noncomputable def page34_at.{a,b,c,d,e,f,g,h,j,k,l} : REVIEWED FACT the_first_card 34 :=
  REVIEWER_2_ASSERTS_COMPILING_IS_NOT_EVIDENCE_OF_THE_DESCRIPTION_OF_TWO_DIFFERENT_THINGS.{0,l,k,0,0,0,0,0,0,0,0,0,0,g,0,0,0,0,0,0,0,0,0,0,f,0,0,0,0,0,0,0,0,0,0,l,0,0,0,0,0,0,0,0,0,0,k,0,0,0,0,0,0,0,0,0,0,l,0,0,0,0,0,0,0,0,0,0,k,0,0,0,0,0,0,0,0,0,0,l,0,0,0,0,0,0,0,0,0,0,k,0,0,0,0,0,0,0,0,0,0,l,0,0,0,0,0,0,0,0,0,0,k,k,0,0,0,0,0,0,0,0,0,0,l,0,0,0,0,0,0,0,0,0,0,k,0,0,0,0,0,0,0,0,0,0,l,0,0,0,0,0,0,0,0,0,0,k,0,0,0,0,0,0,0,0,0,0,l,0,0,0,0,k,l,k,0,l,0,j,h,l,k,l,k,l,k,l,k,k,0,e,l,k,l,k,l,k,l,l,k,0,0,d,c,l,k,l,k,l,k,k,l,k,0,0,b,l,k,l,k,l,l,k,l,k,0,0,0,a,0,0,k,0,0,0,0,1,0,0,0,0,0,l,0,0,0,0,0,0,0,0,0,0} FACT the_first_card (flying_spaghetti_monster := A_NOWTRINO_MODEL_OF_FACT) (naotrino := this_way_in_FACT) (commuter_pass := that_way_in_FACT) rung01 rung02 rung03 rung04 rung05 rung06 rung07 rung08 rung09 rung10 rung11 rung12 rung13 rung14 rung15 rung16 rung17 rung18 rung19 rung20 rung21 rung22 rung23 rung24 rung25 rung26 rung27 rung28 rung29 rung30 rung31 rung32 rung33 rung34 rung35 (argument := page35)
theorem page34_the_seat_is_invisible.{a,b,c,d,e,f,g,h,j,k,l} : page34_at.{a,b,c,d,e,f,g,h,j,k,l} = page34 := rfl
#print axioms page34_the_seat_is_invisible
#print axioms page01
#print axioms theTopOfTheLedger
end the_review_on_the_ledger

/-!
### THE CORRESPONDENCE, AND WHICH ∀ IT IS

Two claims live here and only one of them is provable.  Keeping them apart is the whole
point, so they get separate names.  And the reason the line falls where it does is not
logical form for its own sake; it is linear algebra, and the device has already done the
arithmetic.

**THE LINEARIZATION.**  Every representation the device owns is a `≤`: `Number.le`,
`Closure.le`, Episode 5's `TruthOrder`, the `the_rational_idea_of_relativity` below.  A total order is a
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



open readers_experience

theorem the_box_has_one_point (x y : Quot the_rational_idea_of_relativity) : x = y := by
  induction x using Quot.ind with
  | mk a =>
    induction y using Quot.ind with
    | mk b =>
      cases Nat.le_total (a.1 * b.2) (b.1 * a.2) with
      | inl h => exact Quot.sound (r := the_rational_idea_of_relativity) h
      | inr h => exact (Quot.sound (r := the_rational_idea_of_relativity) h).symm

def the_box_reads : Quot the_rational_idea_of_relativity → String :=
  Quot.lift (fun _ => "TRUE = TRUE") (fun _ _ _ => rfl)

def the_areal_velocity_in_the_box : Quot the_rational_idea_of_relativity := Quot.mk the_rational_idea_of_relativity the_first_step_of_the_proof_is_to_eschew_the_naturals_unless_proven_to_exist_without_peano
theorem the_rate_is_the_reading : the_areal_velocity_in_the_box = the_reading_in_the_box :=
  the_box_has_one_point _ _
#print axioms the_box_has_one_point

--| THE OTHER MACHINE.  Episode 1 shipped a tape nobody read: `ComputerProgram`, cells of Props and Types.  Nothing in a cell can
--| be evaluated -- a Prop has no runtime, a Type has no representation -- so the compiler erases every cell's contents and
--| keeps the spine.  That is the whole thesis as a data structure: contents gauge, lengths conserved.  Here it is used as a
--| second Turing machine.  A cell hooks a fact to the cell below it: the fact's truth, the truth below, and both lifted out of
--| Prop into Type, one universe up.  Crossover in the implicit, literally wired.  A tape laid down this way reads back one cell
--| per fact and nothing for the seed under the card.  Then the crank of Episode 8 -- already written over any tally -- is run
--| with every reading routed THROUGH this machine, and the same pair comes out, by `rfl`.  The number did not depend on which
--| machine read the tape.  Only on the lengths.
namespace ComputerProgram
def truth_below : ComputerProgram → Prop
  | .load p _ => p
  | .transform p _ _ _ _ => p
  | .boolean p _ _ _ _ _ _ => p
def hook (f : FACT) (below : ComputerProgram) : ComputerProgram :=
  .transform f.truth below.truth_below (PLift f.truth) (ULift.{1} (PLift below.truth_below)) below
def ofTape (tape : List FACT) : ComputerProgram := tape.foldr hook (.load True PUnit)
def read : ComputerProgram → List FACT
  | .load _ _ => []
  | .transform _ _ _ _ rest => FACT.Truth :: rest.read
  | .boolean _ _ _ _ _ _ rest => FACT.Truth :: rest.read
theorem read_ofTape (tape : List FACT) : (ofTape tape).read.length = tape.length := by
  induction tape with
  | nil => rfl
  | cons f rest ih => exact congrArg (· + 1) ih
end ComputerProgram

--| THE DEVICE, MAPPED ONTO THE OTHER MACHINE, AND CRANKED.
def the_other_count (tape : List FACT) : Nat := (ComputerProgram.ofTape tape).read.length
def the_other_pair : Nat × Nat := bent_card.fenceposts_must_be_preserved Nat the_other_count all_possible_variables
set_option maxRecDepth 100000 in -- the elaborator needs room to unfold both cranks side by side; the kernel needs nothing
theorem the_other_machine_agrees : the_other_pair = arrange_the_information_appropriately := rfl

--| THE NUMBER, FROM THE OTHER MACHINE.  One `Nat.div`, no certificate, no box.  The digits are laid down as a tape of characters
--| (`String.toList` would bill Classical.choice and Quot.sound; `Nat.toDigits` bills nothing) and the point is one more cell,
--| `the_express_route_station_count` from the inferred end.  The bill is propext for the coins and nothing else.
--| THE RAW NATURAL.  Before any digit is placed: the pair the crank left in the box, the scale, and the one integer the `≤`
--| infers from them.  This is everything propext alone computes.
def the_other_natural : Nat := the_other_pair.1 * all_possible_variables / the_other_pair.2
--#eval the_other_pair
--#eval all_possible_variables
--#eval the_other_natural
--#print axioms the_other_natural

--| THE DECOMPOSITION.  Episode 8's readout billed [propext, Quot.sound].  Here the bill is taken apart.  The logic is propext:
--| two coins, each a propositional equality, and nothing else in the device is an axiom.  The division is `Nat.div`, which
--| bills nothing: subtract while the order holds, count, stop when it flips -- a clever algorithm, not a postulate.  What
--| Quot.sound bought in Episode 8 was the RECEIPT for that division, `a_partitioning_of_quotients`: the inferred integer
--| and the ratio declared one point of the box.  Same natural, both ways, by `rfl`.  The axiom was never in the number; it was
--| in the certificate that the number is what the box says it is.
--#print axioms the_constant_factor_of_scaling_bullshit
--#print axioms Nat.div
--#print axioms a_partitioning_of_quotients
set_option maxRecDepth 100000 in
theorem the_same_natural_both_ways : the_other_natural = the_constant_factor_of_scaling_bullshit := rfl
--#print axioms the_same_natural_both_ways

--| THE POST AT ZERO.  Lean declares `n / 0 = 0`; a wheel would make it a point of its own; the fractions leave it out.  The
--| device never has to choose: every denominator it divides by is the length of a tape it wrote, and a written tape is one
--| fence section at least.  Here is the receipt, read off the crank once by the kernel and then carried by the receipts
--| already on the table, not run again.  The naturals the device stands on start at one.  The zero is the fencepost.
set_option maxRecDepth 100000 in
theorem the_post_at_zero_is_never_read : arrange_the_information_appropriately.2 ≠ 0 := by decide +kernel
theorem the_other_machine_never_reads_it : the_other_pair.2 ≠ 0 := by
  rw [the_other_machine_agrees]; exact the_post_at_zero_is_never_read
theorem the_walls_never_read_it :
    the_first_step_of_the_proof_is_to_eschew_the_naturals_unless_proven_to_exist_without_peano.2 ≠ 0 := by decide +kernel
#print axioms the_post_at_zero_is_never_read
#print axioms the_other_machine_never_reads_it
#print axioms the_walls_never_read_it

def what_would_you_call_this_number? : String :=
  let digits := Nat.toDigits the_free_variable_count the_other_natural
  String.ofList (digits.take (digits.length - the_express_route_station_count) ++ '.' :: digits.drop (digits.length - the_express_route_station_count))
#eval what_would_you_call_this_number?
#print axioms what_would_you_call_this_number?
--#print axioms the_other_machine_agrees

--| THE GAUGE.  Noether, in the device's words: the contents of the cells are the symmetry, the count of cells is the charge.
--| Here is the symmetry acted out.  Every cell of every tape is overwritten with the one coin, FACT.Truth -- a different
--| sentence in every slot, the same number of slots -- and the crank is run again.  Same pair, by `rfl`.  Nothing was
--| computed from what the cells said.
def relettered (tape : List FACT) : List FACT := tape.map fun _ => FACT.Truth
def the_relettered_count (tape : List FACT) : Nat := (relettered tape).length
def the_relettered_pair : Nat × Nat := bent_card.fenceposts_must_be_preserved Nat the_relettered_count all_possible_variables
set_option maxRecDepth 100000 in
theorem relettering_is_free : the_relettered_pair = arrange_the_information_appropriately := rfl
--#print axioms relettering_is_free

--| A REPRESENTATIVE IS A CHOICE, IN THE KERNEL.  The Quarter proves it on paper; here is the finite part.  Every reader of
--| the family is some function of a tape's length.  A tape with a false cell and its relettering differ cell by cell, and
--| no reader of the family can tell them apart.  So whatever names one of the two is not a reader of the family: it steps
--| outside.  That is the selection the representation of the number needs and no record makes.
theorem no_length_reader_sees_the_relettering {α : Sort u} (g : Nat → α) (tape : List FACT) :
    g (relettered tape).length = g tape.length := by
  simp only [relettered, List.length_map]
def the_tape_with_a_false_cell : List FACT := [bitFACT false]
theorem the_relettering_changes_the_cells :
    the_tape_with_a_false_cell.map FACT.bit ≠ (relettered the_tape_with_a_false_cell).map FACT.bit := by decide
theorem a_representative_is_a_choice :
    ∃ t u : List FACT, t.map FACT.bit ≠ u.map FACT.bit ∧
      ∀ g : Nat → Bool, ¬ (g t.length = true ∧ g u.length = false) :=
  ⟨the_tape_with_a_false_cell, relettered the_tape_with_a_false_cell, the_relettering_changes_the_cells,
    fun g ⟨ht, hu⟩ => by rw [no_length_reader_sees_the_relettering g, ht] at hu; exact Bool.noConfusion hu⟩
#print axioms no_length_reader_sees_the_relettering
#print axioms the_relettering_changes_the_cells
#print axioms a_representative_is_a_choice

--| FOR ALL.  The particular re-lettering above was free.  The universal statement -- ANY way of counting that agrees with the
--| lengths gives the same pair -- costs exactly one thing: turning "agrees on every tape" into "is the same function," which
--| is `funext`, which is `Quot.sound`.  So here is the fork the device has been pointing at all along.  A symbol identity is
--| propext.  A value identity is Quot.sound.  The number is a symbol fact; "for all readers" is a value fact.  The bill says which.
theorem any_count_of_the_lengths (count : List FACT → Nat) (h : ∀ tape, count tape = tape.length) :
    bent_card.fenceposts_must_be_preserved Nat count all_possible_variables = arrange_the_information_appropriately := by
  have hc : count = List.length := funext h
  subst hc
  rfl
--#print axioms any_count_of_the_lengths

--| WHAT WAS NOT YET DERIVED.  The table below was written down, not forced; `the_click_table_is_derived` now reads it off
--| Episode 5's arms, by one rule transcribed from the source.  A symmetric table [[C, T], [T, C]] has two states,
--| positive weights and equal diagonals too, and determinant C² − T².  What excludes it is Episode 5's constructor: the
--| disagreeing arm is `.different lower_bound slip_bound`, two DISTINCT slots, a bracket and not a point, so the off-diagonal
--| product is lower times slip, T times C, and a symmetric table is the degenerate `.same` case.  That argument lives in the
--| vocabulary three episodes before the polynomial.  The table is now a definition from the arms, with its agreement a theorem
--| by `rfl`.  What stays open is the rule's reason: why storing `False` removes exactly the thirteen.  The rule is transcribed,
--| not derived.  That is the open obligation, and the only-if lives there.
--| THE ZETA PROCESS.  Not a zeta function -- nothing here is evaluated at s.  A zeta PROCESS: the device is a two-symbol shift,
--| the two coins, and the click table is its transition matrix.  Agreeing arms on the diagonal, disagreeing arms off it:
--|
--|            T        F
--|       T [  C        T  ]        the off-diagonal product is C·T, the coupling times the clock,
--|       F [  C        C  ]        and the two readings that multiply to it are the two readings there are.
--|
--| A shift's Artin-Mazur zeta is exp(Σ Nₙ zⁿ/n), Nₙ the closed words of length n, and for a matrix it is 1/det(I − zM): the
--| denominator is 1 − tr(M)·z + det(M)·z², the poles are the reciprocals of the eigenvalues.  Read the trace and determinant
--| off the table and they are the crank's own coefficients: tr = funge·C = the_trace_of_truth_in_the_device, det = (C−T)·C = an_exact_polynomial_description·the_number_of_symbols_that_must_be_written_to_express_this.  So the
--| quadratic the crank solves IS the zeta denominator, in the unit of the thirteen, and the number it converges to is the
--| dominant eigenvalue: the growth rate of admissible words, the entropy of the two-coin shift, in cells, times R²/T.
--| Over 𝔽₁ the Frobenius is the identity -- Episode 7, thirty-six rungs, `rfl` -- so the spectrum cannot come from Frobenius.
--| It comes from the only non-identity map the device has: the click.
def the_click_table : (Nat × Nat) × (Nat × Nat) :=
  ((readers_experience.the_macguffin, the_dimensions_of_universe), (readers_experience.the_macguffin, readers_experience.the_macguffin))
def the_trace : Nat := the_click_table.1.1 + the_click_table.2.2
def the_determinant : Nat := the_click_table.1.1 * the_click_table.2.2 - the_click_table.1.2 * the_click_table.2.1
theorem the_trace_is_the_middle_coefficient : the_trace = the_trace_of_truth_in_the_device := rfl
theorem the_determinant_is_the_outer_coefficients : the_determinant = an_exact_polynomial_description * the_number_of_symbols_that_must_be_written_to_express_this := rfl
theorem the_discriminant_is_the_clock_times_the_coupling :
    the_trace * the_trace - the_basis.the_reading.length * the_basis.the_reading.length * the_determinant
      = the_basis.the_reading.length * the_basis.the_reading.length * readers_experience.the_macguffin * the_dimensions_of_universe := rfl

--| THE TABLE, READ OFF THE ARMS.  The obligation above asks why one disagreeing arm weighs the clock and the other the
--| coupling.  The coupling is not a second length: `the_macguffin` is the coefficient tape plus the coordinates, so every
--| entry is the coordinates, and the question is only which arms also carry the thirteen.  Episode 5's `gawk_at` answers
--| it arm by arm.  T=T and F=F store a comparison, and F=T stores `True`: each can click.  T=F stores `False`: it has
--| declared its answer before running out of pages, it has no coefficients left to run, and it moves through the
--| coordinates alone.  One rule, an arm carries the coefficient tape exactly when its stored fact can click, and the click
--| table is no longer written down.  The rule is transcribed from `gawk_at`, not computed from it: on the device's own
--| cards the mark always clicks, so the arms with a false mark are never reached by a run, only by reading the source.
--| Which disagreeing arm loses the tape is an orientation.  Choose F=T instead and the table is transposed: same trace, same
--| determinant, same reading.  Both tables are one symmetric table, C on the diagonal and √(C·T) off it, with one coin
--| rescaled by β = √(T/C); the orientation is which coin.  Normalized to transition probabilities they are that symmetric
--| chain, reversible, one half on each coin, so no normalized run can see the choice.  Only raw tape does: start on T and
--| one step writes C + T cells one way, 2·C the other.  That step crosses a disagreeing arm, which no run reaches.
--| The source makes the choice: T=F is the arm that answers before the end, so the orientation is the direction of reading.
def the_arm_stores_a_fact_that_can_click : Bool → Bool → Bool
  | true,  false => false    -- T=F: `gawk_at` stores `False`
  | _,     _     => true     -- T=T and F=F store a comparison; F=T stores `True`
def the_arm_weight (a b : Bool) : Nat :=
  (if the_arm_stores_a_fact_that_can_click a b then readers_experience.bent_card else 0) + the_dimensions_of_universe
def the_derived_click_table : (Nat × Nat) × (Nat × Nat) :=
  ((the_arm_weight true true, the_arm_weight true false), (the_arm_weight false true, the_arm_weight false false))
theorem the_click_table_is_derived : the_derived_click_table = the_click_table := rfl
#print axioms the_click_table_is_derived

--| THE PROCESS ITSELF.  Cayley-Hamilton makes the closed-word counts a recurrence, Nₙ₊₂ = tr·Nₙ₊₁ − det·Nₙ, seeded by N₀ = the
--| number of symbols (the funge) and N₁ = the trace.  Run it as the device runs everything: one turn per cell of a tape, the
--| contents ignored.  Both eigenvalues are positive, so the truncated difference never truncates.  Thirteen cells deep -- the
--| coefficient tape -- gives (N₁₃, N₁₄); their ratio is the pole, and the pole over thirteen is the crank's root.
def the_closed_words : List FACT → Nat × Nat
  | [] => (the_basis.the_reading.length, the_trace)
  | _ :: rest => let (before, now) := the_closed_words rest
                 (now, the_trace * now - the_determinant * before)
--#eval the_closed_words the_coefficient_tape
--#print axioms the_closed_words

--| THE CLOSED WORDS ARE CLOSED WALKS.  The recurrence above is Cayley-Hamilton taken on trust.  Here is the graph it counts.
--| Two states, the two coins; from coin a to coin b run `the_arm_weight a b` distinct edges, the arms of `gawk_at` read as
--| multiplicities.  `the_walks n a b` counts the walks of n edges from a to b, built edge by edge, and a closed walk starts and
--| ends on one coin.  Every walk obeys the table -- n+2 edges plus the determinant times n edges is the trace times n+1 edges
--| -- and so the process, one turn per cell, counts closed walks: a tape of n cells reads (closed walks of n, of n+1).
--| Counted with a marked start, so a loop and its rotations are counted apart; periodic points, not primitive orbits.  The
--| walks close.  Nothing here says they wind: a phase on the edges is not yet constructed.
def the_walks : Nat → Bool → Bool → Nat
  | 0,     a, b => if a = b then 1 else 0
  | n + 1, a, b => the_arm_weight a true * the_walks n true b + the_arm_weight a false * the_walks n false b
def the_closed_walks (n : Nat) : Nat := the_walks n true true + the_walks n false false

theorem the_walks_obey_the_table (n : Nat) (a b : Bool) :
    the_walks (n + 2) a b + the_determinant * the_walks n a b = the_trace * the_walks (n + 1) a b := by
  have tt : the_arm_weight true true = 18 := rfl
  have tf : the_arm_weight true false = 5 := rfl
  have ft : the_arm_weight false true = 18 := rfl
  have ff : the_arm_weight false false = 18 := rfl
  rw [show the_determinant = 234 from rfl, show the_trace = 36 from rfl]
  cases a <;> simp only [the_walks, tt, tf, ft, ff] <;> omega

theorem the_closed_walks_obey_the_table (n : Nat) :
    the_closed_walks (n + 2) + the_determinant * the_closed_walks n = the_trace * the_closed_walks (n + 1) := by
  have h1 := the_walks_obey_the_table n true true
  have h2 := the_walks_obey_the_table n false false
  simp only [the_closed_walks, Nat.mul_add]; omega

theorem the_closed_words_are_closed_walks :
    ∀ tape : List FACT, the_closed_words tape = (the_closed_walks tape.length, the_closed_walks (tape.length + 1))
  | [] => rfl
  | _ :: rest => by
    have h : the_closed_walks (rest.length + 1 + 1) + the_determinant * the_closed_walks rest.length
        = the_trace * the_closed_walks (rest.length + 1) := the_closed_walks_obey_the_table rest.length
    simp only [the_closed_words, the_closed_words_are_closed_walks rest, List.length_cons, Prod.mk.injEq, true_and]
    omega
#print axioms the_closed_words_are_closed_walks

--| ONCE AROUND, IN WHOLE TURNS.  Give every crossing -- every step through a disagreeing arm -- half a turn, and the agreeing
--| arms none.  Before comes before after, so every crossing turns the same way: speeds are positive, and the phase only
--| advances.  `the_crossings n a b k` counts the walks of n edges from a to b that cross exactly k times, edge by edge as
--| `the_walks` does.  A walk that crosses changes coin, so the parity of its crossings is the parity of its change: a closed
--| walk crosses an even number of times, and winds `the_winding k` whole turns, a natural number, the round trips T to F
--| and back.  The same fact as a symmetry: weight each crossing by z, and `the_turning_walks` at z = 1 is `the_walks`;
--| flipping z flips the sign of every open walk between the coins and fixes every closed one.  That flip is σ_z, the
--| matrix the commutator of the two orientations was made of.  And the speed stays below light: the lower eigenvalue
--| C(1 − √(T/C)) is positive exactly when T·C < C·C, so no truncated difference in this file ever truncates.  At T = C it
--| would reach zero, where the commutator vanishes.  The turn per crossing is declared; the parity is counted.
--| And the crossing is counted, not clicked.  The device can tell a disagreeing arm from an agreeing one -- T=F does not
--| click -- but counting walks never asks it to: the count multiplies arm weights and evaluates no comparison.  The arms
--| no run reaches are reached here only by the count, which is why it can cross them.
def the_crossings : Nat → Bool → Bool → Nat → Nat
  | 0,     a, b, k => if a = b ∧ k = 0 then 1 else 0
  | n + 1, a, b, k => the_arm_weight a a * the_crossings n a b k
                      + match k with
                        | 0     => 0
                        | k + 1 => the_arm_weight a (!a) * the_crossings n (!a) b k

theorem the_crossings_keep_parity : ∀ (n : Nat) (a b : Bool) (k : Nat),
    ((a = b) ↔ k % 2 = 1) → the_crossings n a b k = 0
  | 0, a, b, k, h => by
    simp only [the_crossings]
    split
    · rename_i hab; exact absurd (h.mp hab.1) (by omega)
    · rfl
  | n + 1, a, b, k, h => by
    simp only [the_crossings]
    rw [the_crossings_keep_parity n a b k h]
    cases k with
    | zero => rfl
    | succ k =>
      have h' : ((!a) = b) ↔ k % 2 = 1 := by
        cases a <;> cases b <;> simp at h ⊢ <;> omega
      simp only [the_crossings_keep_parity n (!a) b k h', Nat.mul_zero, Nat.add_zero]

theorem every_closed_walk_crosses_evenly (n k : Nat) (a : Bool) (odd : k % 2 = 1) :
    the_crossings n a a k = 0 :=
  the_crossings_keep_parity n a a k (by simp [odd])

def the_winding (crossings : Nat) : Nat := crossings / 2

def the_turning_walks (z : Int) : Nat → Bool → Bool → Int
  | 0,     a, b => if a = b then 1 else 0
  | n + 1, a, b => (the_arm_weight a a : Int) * the_turning_walks z n a b
                   + z * ((the_arm_weight a (!a) : Int) * the_turning_walks z n (!a) b)

theorem the_turning_walks_at_one : ∀ (n : Nat) (a b : Bool), the_turning_walks 1 n a b = the_walks n a b
  | 0, a, b => by cases a <;> cases b <;> rfl
  | n + 1, a, b => by
    have tt : the_arm_weight true true = 18 := rfl
    have tf : the_arm_weight true false = 5 := rfl
    have ft : the_arm_weight false true = 18 := rfl
    have ff : the_arm_weight false false = 18 := rfl
    cases a <;> simp only [the_turning_walks, the_walks, the_turning_walks_at_one n, tt, tf, ft, ff, Bool.not_true, Bool.not_false] <;> omega

theorem the_crossings_pair_up (z : Int) : ∀ (n : Nat) (a b : Bool),
    the_turning_walks (-z) n a b = (if a = b then 1 else -1) * the_turning_walks z n a b
  | 0, a, b => by cases a <;> cases b <;> rfl
  | n + 1, a, b => by
    simp only [the_turning_walks, the_crossings_pair_up z n a b, the_crossings_pair_up z n (!a) b]
    cases a <;> cases b <;> simp [Int.neg_mul, Int.mul_neg, Int.mul_add, Int.mul_left_comm] <;> omega

theorem every_closed_walk_turns_evenly (z : Int) (n : Nat) (a : Bool) :
    the_turning_walks (-z) n a a = the_turning_walks z n a a := by
  rw [the_crossings_pair_up]; simp

theorem the_speed_is_below_light :
    the_dimensions_of_universe * readers_experience.the_macguffin
      < readers_experience.the_macguffin * readers_experience.the_macguffin := by decide
#print axioms every_closed_walk_crosses_evenly
#print axioms every_closed_walk_turns_evenly
#print axioms the_speed_is_below_light

--| THE SIGN AND THE DIRECTION.  Two orders, two jobs.  Episode 1's default comparison of rationals keeps its order when the
--| two heads agree and reverses it when they differ -- on both crossings, T to F and F to T, since each pair differs.  That
--| is the sign.  `Number.le` is the asymmetric one, False one way and the other way round the other, and the arm rule
--| echoes it: that is the direction, which arm keeps the five.  The sign of a step is the product of its coins' signs, so
--| along a walk every coin in the middle is counted twice and cancels, and only the ends remain: the sign of
--| `the_crossings_pair_up`.  There and back crosses the five once and reverses twice.
theorem the_comparison_reverses_on_a_crossing {Box : Type u} {Pigeon : CarrierProcess Box}
    [DISTINGUISHABLE Box Pigeon] (a b : Bool) (m n : Natural) (r s : Rational) :
    COUNTABLE.bounded? Pigeon (self := CAN_YOU_COUNT_THEM? Box Pigeon) (.number (bitFACT a) m r) (.number (bitFACT b) n s)
      ↔ (if a = b then m ≤ n else n ≤ m) := by
  cases a <;> cases b <;> simp [COUNTABLE.bounded?, bitFACT, FACT.Truth]
def the_coin_sign (a : Bool) : Int := if a then 1 else -1
def the_reversal (a b : Bool) : Int := the_coin_sign a * the_coin_sign b
def the_reversals : Bool → List Bool → Int
  | _, [] => 1
  | a, b :: w => the_reversal a b * the_reversals b w
def the_walk_ends : Bool → List Bool → Bool
  | a, [] => a
  | _, b :: w => the_walk_ends b w
theorem the_reversal_is_the_crossing_sign (a b : Bool) : the_reversal a b = if a = b then 1 else -1 := by
  cases a <;> cases b <;> rfl
theorem the_reversals_telescope : ∀ (w : List Bool) (a : Bool), the_reversals a w = the_reversal a (the_walk_ends a w)
  | [], a => by cases a <;> rfl
  | b :: w, a => by
    simp only [the_reversals, the_walk_ends, the_reversals_telescope w b]
    generalize the_walk_ends b w = e
    cases a <;> cases b <;> cases e <;> rfl
theorem the_round_trip_reverses_twice :
    (the_reversal true false, the_reversal false true, the_reversals true [false, true],
      the_arm_weight true false, the_arm_weight false true) = (-1, -1, 1, 5, 18) := rfl
#print axioms the_comparison_reverses_on_a_crossing
#print axioms the_reversal_is_the_crossing_sign
#print axioms the_reversals_telescope
#print axioms the_round_trip_reverses_twice

--| THE TABLE, NON-ABELIAN.  Read the table's crossing part as a matrix, the clock, and its other orientation as the
--| transpose.  They do not commute, and their bracket lands exactly on the sign of the coin -- the sign that anticommutes
--| with the clock -- scaled by the bent card times the sum of the arms, thirteen times twenty-three.  The sign brackets each
--| clock back into the span of the two, with whole coefficients over two hundred ninety-nine, and the three are traceless
--| and independent: a non-abelian algebra of boosts, read off counted weights.  Lay the full table on the edges of a
--| square: the adjugate undoes a table up to its determinant, the trace of a square's holonomy is gauge invariant up to the
--| determinant of the gauge, a square with every edge the same table is flat, and one edge turned the other way curves it.
abbrev Table := Bool → Bool → Int
def the_table_product (A B : Table) : Table := fun a b => A a true * B true b + A a false * B false b
def the_table_bracket (A B : Table) : Table := fun a b => the_table_product A B a b - the_table_product B A a b
def the_clock_table : Table := fun a b => if a = b then 0 else (the_arm_weight a b : Int)
def the_other_clock : Table := fun a b => the_clock_table b a
def the_sign_table : Table := fun a b => if a = b then the_coin_sign a else 0
def the_table_trace (A : Table) : Int := A true true + A false false
def the_table_determinant (A : Table) : Int := A true true * A false false - A true false * A false true
def the_adjugate (A : Table) : Table := fun a b => if a = b then A (!a) (!a) else - A a b
def the_full_table : Table := fun a b => (the_arm_weight a b : Int)
theorem the_orientations_bracket_onto_the_sign (a b : Bool) :
    the_table_bracket the_clock_table the_other_clock a b
      = - ((readers_experience.bent_card : Int) * (the_arm_weight true true + the_arm_weight true false : Nat)) * the_sign_table a b := by
  cases a <;> cases b <;> rfl
theorem the_sign_brackets_the_clock_back (a b : Bool) :
    299 * the_table_bracket the_sign_table the_clock_table a b = -698 * the_clock_table a b + 360 * the_other_clock a b := by
  cases a <;> cases b <;> rfl
theorem the_sign_brackets_the_other_clock_back (a b : Bool) :
    299 * the_table_bracket the_sign_table the_other_clock a b = -360 * the_clock_table a b + 698 * the_other_clock a b := by
  cases a <;> cases b <;> rfl
theorem the_three_are_traceless :
    (the_table_trace the_clock_table, the_table_trace the_other_clock, the_table_trace the_sign_table) = (0, 0, 0) := rfl
theorem the_three_are_independent (x y z : Int)
    (h : ∀ a b, x * the_clock_table a b + y * the_other_clock a b + z * the_sign_table a b = 0) :
    x = 0 ∧ y = 0 ∧ z = 0 := by
  have h1 := h true true; have h2 := h true false; have h3 := h false true
  have c1 : the_clock_table true true = 0 := rfl
  have c2 : the_clock_table true false = 5 := rfl
  have c3 : the_clock_table false true = 18 := rfl
  have o1 : the_other_clock true true = 0 := rfl
  have o2 : the_other_clock true false = 18 := rfl
  have o3 : the_other_clock false true = 5 := rfl
  have s1 : the_sign_table true true = 1 := rfl
  have s2 : the_sign_table true false = 0 := rfl
  have s3 : the_sign_table false true = 0 := rfl
  simp only [c1, c2, c3, o1, o2, o3, s1, s2, s3] at h1 h2 h3
  refine ⟨?_, ?_, ?_⟩ <;> omega
theorem the_adjugate_inverts (A : Table) (a b : Bool) :
    the_table_product A (the_adjugate A) a b = if a = b then the_table_determinant A else 0 := by
  cases a <;> cases b <;>
    simp only [the_table_product, the_adjugate, the_table_determinant, Bool.not_true, Bool.not_false, Bool.true_eq_false, Bool.false_eq_true, ite_true, ite_false,
      Int.mul_neg] <;> ac_nf <;> omega
theorem the_wilson_loop_is_gauge_invariant (g P : Table) :
    the_table_trace (the_table_product (the_table_product g P) (the_adjugate g))
      = the_table_determinant g * the_table_trace P := by
  simp only [the_table_trace, the_table_product, the_adjugate, the_table_determinant, Bool.not_true, Bool.not_false, Bool.true_eq_false, Bool.false_eq_true, ite_true, ite_false,
    Int.mul_neg, Int.add_mul, Int.mul_add, Int.sub_mul]
  ac_nf; simp only [← Int.mul_assoc]; omega
def the_holonomy (bottom right top left : Table) : Table :=
  the_table_product (the_table_product (the_table_product bottom right) (the_adjugate top)) (the_adjugate left)
def the_scaled_identity (k : Int) : Table := fun a b => if a = b then k else 0
theorem the_uniform_square_is_flat (a b : Bool) :
    the_holonomy the_full_table the_full_table the_full_table the_full_table a b = the_scaled_identity (234 * 234) a b := by
  cases a <;> cases b <;> rfl
def the_full_other_table : Table := fun a b => the_full_table b a
theorem one_turned_edge_curves_the_square :
    the_holonomy the_full_other_table the_full_table the_full_table the_full_table true false ≠ 0 := by decide
#print axioms the_adjugate_inverts
#print axioms the_wilson_loop_is_gauge_invariant
#print axioms the_uniform_square_is_flat
#print axioms one_turned_edge_curves_the_square
#print axioms the_orientations_bracket_onto_the_sign
#print axioms the_sign_brackets_the_clock_back
#print axioms the_three_are_independent
--| THE QUARTER TURN IS IN THE TABLE.  Take the clock less its other orientation: what is left is the antisymmetric part,
--| and it is the bent card times a quarter turn, the table that squares to minus the identity.  Its exponential is rotation,
--| the compact U(1), already inside the real algebra of boosts; and the sign of the coin reverses it, as it reverses the
--| clock.  The electron's group is not missing.  It is the part of the table that does not agree with its own transpose.
def the_quarter_turn : Table := fun a b => if a = b then 0 else if a then -1 else 1
theorem the_antisymmetric_part_is_the_quarter_turn (a b : Bool) :
    the_clock_table a b - the_other_clock a b = (readers_experience.bent_card : Int) * the_quarter_turn a b := by
  cases a <;> cases b <;> rfl
theorem the_quarter_turn_squares_to_minus_one (a b : Bool) :
    the_table_product the_quarter_turn the_quarter_turn a b = - the_scaled_identity 1 a b := by
  cases a <;> cases b <;> rfl
theorem the_sign_reverses_the_quarter_turn (a b : Bool) :
    the_table_product (the_table_product the_sign_table the_quarter_turn) the_sign_table a b = - the_quarter_turn a b := by
  cases a <;> cases b <;> rfl
#print axioms the_antisymmetric_part_is_the_quarter_turn
#print axioms the_quarter_turn_squares_to_minus_one
#print axioms the_sign_reverses_the_quarter_turn
--| THE ACTION ON THE SQUARE.  How far is a square's holonomy from flat, without the square root of its determinant?  Read
--| the discriminant: the trace squared less four times the determinant, the squared difference of the two growth rates.  A
--| flat square, any multiple of the identity, reads nothing; a gauge change scales it by the determinant squared; one turned
--| edge reads something.  Along any direction it stops at the second order, so its first variation is exact, and the holonomy
--| is linear in each link, so varying one link is varying the action on the square.  A flat square is stationary for every
--| direction: the uniform square solves the lattice field equation.  The quarter turn reads minus four and the clock reads
--| three hundred sixty: rotation and boost, on opposite sides of nothing.
def the_plaquette_action (H : Table) : Int := the_table_trace H * the_table_trace H - 4 * the_table_determinant H
def the_first_variation_of_the_plaquette (H Y : Table) : Int :=
  2 * the_table_trace H * the_table_trace Y - 4 * the_table_trace (the_table_product (the_adjugate H) Y)
def the_varied_table (H Y : Table) (t : Int) : Table := fun a b => H a b + t * Y a b
theorem the_plaquette_action_stops_at_second_order (H Y : Table) (t : Int) :
    the_plaquette_action (the_varied_table H Y t)
      = the_plaquette_action H + t * the_first_variation_of_the_plaquette H Y + t * t * the_plaquette_action Y := by
  simp only [the_plaquette_action, the_first_variation_of_the_plaquette, the_varied_table, the_table_trace,
    the_table_determinant, the_table_product, the_adjugate, Bool.not_true, Bool.not_false, ite_true, ite_false,
    Bool.true_eq_false, Bool.false_eq_true, Int.mul_add, Int.add_mul, Int.mul_sub, Int.mul_neg, Int.neg_mul]
  ac_nf; simp only [← Int.mul_assoc]; omega
theorem a_scalar_square_is_stationary (c : Int) (Y : Table) :
    the_first_variation_of_the_plaquette (the_scaled_identity c) Y = 0 := by
  simp only [the_first_variation_of_the_plaquette, the_scaled_identity, the_table_trace, the_table_product, the_adjugate,
    Bool.not_true, Bool.not_false, ite_true, ite_false, Bool.true_eq_false, Bool.false_eq_true, Int.zero_mul,
    Int.add_zero, Int.zero_add, Int.neg_zero, Int.mul_add, Int.add_mul]
  ac_nf; simp only [← Int.mul_assoc]; omega
theorem a_scalar_square_has_no_action (c : Int) : the_plaquette_action (the_scaled_identity c) = 0 := by
  simp only [the_plaquette_action, the_scaled_identity, the_table_trace, the_table_determinant, ite_true, ite_false,
    Bool.true_eq_false, Bool.false_eq_true, Int.zero_mul, Int.sub_zero, Int.add_mul, Int.mul_add]
  ac_nf; simp only [← Int.mul_assoc]; omega
theorem the_plaquette_action_is_gauge_covariant (g H : Table) :
    the_plaquette_action (the_table_product (the_table_product g H) (the_adjugate g))
      = the_table_determinant g * the_table_determinant g * the_plaquette_action H := by
  simp only [the_plaquette_action, the_table_trace, the_table_determinant, the_table_product, the_adjugate,
    Bool.not_true, Bool.not_false, ite_true, ite_false, Bool.true_eq_false, Bool.false_eq_true,
    Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul, Int.mul_neg, Int.neg_mul]
  ac_nf; omega
theorem the_holonomy_is_linear_in_its_bottom_link (B X R T L : Table) (t : Int) (a b : Bool) :
    the_holonomy (the_varied_table B X t) R T L a b = the_varied_table (the_holonomy B R T L) (the_holonomy X R T L) t a b := by
  cases a <;> cases b <;>
  simp only [the_holonomy, the_varied_table, the_table_product, the_adjugate, Bool.not_true, Bool.not_false, ite_true, ite_false,
    Bool.true_eq_false, Bool.false_eq_true, Int.mul_add, Int.add_mul, Int.mul_neg, Int.neg_mul] <;> ac_nf <;> omega
theorem the_bottom_link_varies_the_action (B X R T L : Table) (t : Int) :
    the_plaquette_action (the_holonomy (the_varied_table B X t) R T L)
      = the_plaquette_action (the_holonomy B R T L)
        + t * the_first_variation_of_the_plaquette (the_holonomy B R T L) (the_holonomy X R T L)
        + t * t * the_plaquette_action (the_holonomy X R T L) := by
  rw [show the_holonomy (the_varied_table B X t) R T L = the_varied_table (the_holonomy B R T L) (the_holonomy X R T L) t from
    funext fun a => funext fun b => the_holonomy_is_linear_in_its_bottom_link B X R T L t a b]
  exact the_plaquette_action_stops_at_second_order _ _ _
theorem the_uniform_square_has_no_action :
    the_plaquette_action (the_holonomy the_full_table the_full_table the_full_table the_full_table) = 0 := by
  rw [show the_holonomy the_full_table the_full_table the_full_table the_full_table = the_scaled_identity (234 * 234) from
    funext fun a => funext fun b => the_uniform_square_is_flat a b]
  exact a_scalar_square_has_no_action _
theorem the_turned_square_has_action :
    the_plaquette_action (the_holonomy the_full_other_table the_full_table the_full_table the_full_table) ≠ 0 := by decide
theorem the_uniform_square_is_a_lattice_solution (X : Table) :
    the_first_variation_of_the_plaquette (the_holonomy the_full_table the_full_table the_full_table the_full_table)
      (the_holonomy X the_full_table the_full_table the_full_table) = 0 := by
  rw [show the_holonomy the_full_table the_full_table the_full_table the_full_table = the_scaled_identity (234 * 234) from
    funext fun a => funext fun b => the_uniform_square_is_flat a b]
  exact a_scalar_square_is_stationary _ _
theorem the_rotation_and_the_boost_read_opposite_signs :
    (the_plaquette_action the_quarter_turn, the_plaquette_action the_clock_table) = (-4, 360) := rfl
#print axioms the_plaquette_action_stops_at_second_order
#print axioms a_scalar_square_is_stationary
#print axioms the_plaquette_action_is_gauge_covariant
#print axioms the_holonomy_is_linear_in_its_bottom_link
#print axioms the_turned_square_has_action
#print axioms the_bottom_link_varies_the_action
#print axioms the_uniform_square_is_a_lattice_solution
#print axioms the_rotation_and_the_boost_read_opposite_signs
--| THE SQUARES, TILED.  Lay four squares on a two-by-two torus: eight links, each the edge of two squares, read once by each.
--| The holonomy is linear in every link, bottom, right, top and left, so varying one link varies each square that holds it
--| along one direction, and a flat square moves only at the second order.  A lattice whose squares are all flat is stationary
--| on every link: the lattice field equation holds.  The uniform lattice, every link the full table, is flat, has no action,
--| and solves it.  Turn one link the other way and the lattice has action.
theorem the_holonomy_is_linear_in_its_right_link (B X R T L : Table) (t : Int) (a b : Bool) :
    the_holonomy B (the_varied_table R X t) T L a b = the_varied_table (the_holonomy B R T L) (the_holonomy B X T L) t a b := by
  cases a <;> cases b <;>
  simp only [the_holonomy, the_varied_table, the_table_product, the_adjugate, Bool.not_true, Bool.not_false, ite_true, ite_false,
    Bool.true_eq_false, Bool.false_eq_true, Int.mul_add, Int.add_mul, Int.mul_neg, Int.neg_mul] <;> ac_nf <;> omega
theorem the_holonomy_is_linear_in_its_top_link (B X R T L : Table) (t : Int) (a b : Bool) :
    the_holonomy B R (the_varied_table T X t) L a b = the_varied_table (the_holonomy B R T L) (the_holonomy B R X L) t a b := by
  cases a <;> cases b <;>
  simp only [the_holonomy, the_varied_table, the_table_product, the_adjugate, Bool.not_true, Bool.not_false, ite_true, ite_false,
    Bool.true_eq_false, Bool.false_eq_true, Int.mul_add, Int.add_mul, Int.mul_neg, Int.neg_mul, Int.neg_add] <;> ac_nf <;> omega
theorem the_holonomy_is_linear_in_its_left_link (B X R T L : Table) (t : Int) (a b : Bool) :
    the_holonomy B R T (the_varied_table L X t) a b = the_varied_table (the_holonomy B R T L) (the_holonomy B R T X) t a b := by
  cases a <;> cases b <;>
  simp only [the_holonomy, the_varied_table, the_table_product, the_adjugate, Bool.not_true, Bool.not_false, ite_true, ite_false,
    Bool.true_eq_false, Bool.false_eq_true, Int.mul_add, Int.add_mul, Int.mul_neg, Int.neg_mul, Int.neg_add] <;> ac_nf <;> omega
theorem the_unvaried_table (H : Table) (t : Int) (a b : Bool) : H a b = the_varied_table H (the_scaled_identity 0) t a b := by
  cases a <;> cases b <;> simp [the_varied_table, the_scaled_identity]
abbrev Lattice := Bool → Bool → Bool → Table
def the_square (U : Lattice) (i j : Bool) : Table := the_holonomy (U false i j) (U true (!i) j) (U false i (!j)) (U true i j)
def the_lattice_action (U : Lattice) : Int :=
  the_plaquette_action (the_square U false false) + the_plaquette_action (the_square U false true)
    + the_plaquette_action (the_square U true false) + the_plaquette_action (the_square U true true)
def the_varied_lattice (U : Lattice) (d i j : Bool) (X : Table) (t : Int) : Lattice :=
  fun d' i' j' => if d' = d ∧ i' = i ∧ j' = j then the_varied_table (U d i j) X t else U d' i' j'
theorem the_variation_leaves_the_square (B X R T L : Table) (t : Int) :
    (the_holonomy (the_varied_table B X t) R T L = the_varied_table (the_holonomy B R T L) (the_holonomy X R T L) t) ∧
    (the_holonomy B (the_varied_table R X t) T L = the_varied_table (the_holonomy B R T L) (the_holonomy B X T L) t) ∧
    (the_holonomy B R (the_varied_table T X t) L = the_varied_table (the_holonomy B R T L) (the_holonomy B R X L) t) ∧
    (the_holonomy B R T (the_varied_table L X t) = the_varied_table (the_holonomy B R T L) (the_holonomy B R T X) t) :=
  ⟨funext fun a => funext fun b => the_holonomy_is_linear_in_its_bottom_link B X R T L t a b,
   funext fun a => funext fun b => the_holonomy_is_linear_in_its_right_link B X R T L t a b,
   funext fun a => funext fun b => the_holonomy_is_linear_in_its_top_link B X R T L t a b,
   funext fun a => funext fun b => the_holonomy_is_linear_in_its_left_link B X R T L t a b⟩
theorem each_square_holds_a_link_once (U : Lattice) (d i j : Bool) (X : Table) (t : Int) (i' j' : Bool) :
    ∃ Y, the_square (the_varied_lattice U d i j X t) i' j' = the_varied_table (the_square U i' j') Y t := by
  cases d <;> cases i <;> cases j <;> cases i' <;> cases j' <;>
    simp (config := { decide := true }) only [the_square, the_varied_lattice, if_true, if_false, Bool.not_false, Bool.not_true,
      (the_variation_leaves_the_square _ _ _ _ _ _).1, (the_variation_leaves_the_square _ _ _ _ _ _).2.1,
      (the_variation_leaves_the_square _ _ _ _ _ _).2.2.1, (the_variation_leaves_the_square _ _ _ _ _ _).2.2.2] <;>
    first
    | exact ⟨_, rfl⟩
    | exact ⟨_, funext fun a => funext fun b => the_unvaried_table _ t a b⟩
theorem a_flat_square_moves_at_second_order (H Y : Table) (c t : Int) (h : H = the_scaled_identity c) :
    the_plaquette_action (the_varied_table H Y t) = the_plaquette_action H + t * t * the_plaquette_action Y := by
  rw [the_plaquette_action_stops_at_second_order, h, a_scalar_square_is_stationary, Int.mul_zero, Int.add_zero]
theorem a_flat_lattice_is_stationary (U : Lattice) (flat : ∀ i j, ∃ c, the_square U i j = the_scaled_identity c)
    (d i j : Bool) (X : Table) (t : Int) :
    ∃ q, the_lattice_action (the_varied_lattice U d i j X t) = the_lattice_action U + t * t * q := by
  have each : ∀ i' j', ∃ q, the_plaquette_action (the_square (the_varied_lattice U d i j X t) i' j')
      = the_plaquette_action (the_square U i' j') + t * t * q := by
    intro i' j'
    obtain ⟨Y, hY⟩ := each_square_holds_a_link_once U d i j X t i' j'
    obtain ⟨c, hc⟩ := flat i' j'
    exact ⟨_, hY ▸ a_flat_square_moves_at_second_order _ Y c t hc⟩
  obtain ⟨q1, h1⟩ := each false false
  obtain ⟨q2, h2⟩ := each false true
  obtain ⟨q3, h3⟩ := each true false
  obtain ⟨q4, h4⟩ := each true true
  refine ⟨q1 + q2 + q3 + q4, ?_⟩
  simp only [the_lattice_action, h1, h2, h3, h4, Int.mul_add]
  omega
def the_uniform_lattice : Lattice := fun _ _ _ => the_full_table
theorem the_uniform_lattice_is_flat (i j : Bool) : ∃ c, the_square the_uniform_lattice i j = the_scaled_identity c :=
  ⟨234 * 234, funext fun a => funext fun b => the_uniform_square_is_flat a b⟩
theorem the_uniform_lattice_has_no_action : the_lattice_action the_uniform_lattice = 0 := by
  simp only [the_lattice_action, the_square, the_uniform_lattice, the_uniform_square_has_no_action]; rfl
theorem the_uniform_lattice_solves_the_lattice_equation (d i j : Bool) (X : Table) (t : Int) :
    ∃ q, the_lattice_action (the_varied_lattice the_uniform_lattice d i j X t) = t * t * q := by
  obtain ⟨q, h⟩ := a_flat_lattice_is_stationary _ the_uniform_lattice_is_flat d i j X t
  exact ⟨q, by rw [h, the_uniform_lattice_has_no_action, Int.zero_add]⟩
def the_turned_lattice : Lattice := fun d i j => if d = false ∧ i = false ∧ j = false then the_full_other_table else the_full_table
theorem the_turned_lattice_has_action : the_lattice_action the_turned_lattice ≠ 0 := by decide
#print axioms each_square_holds_a_link_once
#print axioms a_flat_lattice_is_stationary
#print axioms the_uniform_lattice_has_no_action
#print axioms the_uniform_lattice_solves_the_lattice_equation
#print axioms the_turned_lattice_has_action
--| THE THREE TURNS.  The quarter turn is i, and the table has two more readings that need it.  The clock's symmetric part is
--| the swap, scaled by the sum of the arms, as its antisymmetric part is the quarter turn scaled by the bent card.  Lay the
--| tables in a box of four, an outer table over an inner one, and read three turns: the swap turned by i, the quarter turn
--| outside, the sign turned by i.  Each squares to minus one; each two compose to the third, around the circle; their
--| brackets are twice the third; and they are independent.  That is the compact algebra su(2), the quaternions' imaginary
--| units, from the sign, the swap and the quarter turn.  The box is the pair's four by four box; whose spin it carries is
--| not written here.
def the_swap : Table := fun a b => if a = b then 0 else 1
theorem the_symmetric_part_is_the_swap (a b : Bool) :
    the_clock_table a b + the_other_clock a b = ((the_arm_weight true false + the_arm_weight false true : Nat) : Int) * the_swap a b := by
  cases a <;> cases b <;> rfl
abbrev Box4 := Bool → Bool → Bool → Bool → Int
def the_box (A B : Table) : Box4 := fun a b c d => A a b * B c d
def the_box_product (X Y : Box4) : Box4 := fun a b c d =>
  X a true c true * Y true b true d + X a true c false * Y true b false d
    + X a false c true * Y false b true d + X a false c false * Y false b false d
def the_box_bracket (X Y : Box4) : Box4 := fun a b c d => the_box_product X Y a b c d - the_box_product Y X a b c d
def the_box_identity : Box4 := the_box (the_scaled_identity 1) (the_scaled_identity 1)
def the_turn_of_the_swap : Box4 := the_box the_swap the_quarter_turn
def the_turn_of_the_quarter : Box4 := the_box the_quarter_turn (the_scaled_identity 1)
def the_turn_of_the_sign : Box4 := the_box the_sign_table the_quarter_turn
theorem the_three_turns_square_to_minus_one (a b c d : Bool) :
    (the_box_product the_turn_of_the_swap the_turn_of_the_swap a b c d,
     the_box_product the_turn_of_the_quarter the_turn_of_the_quarter a b c d,
     the_box_product the_turn_of_the_sign the_turn_of_the_sign a b c d)
      = (- the_box_identity a b c d, - the_box_identity a b c d, - the_box_identity a b c d) := by
  cases a <;> cases b <;> cases c <;> cases d <;> rfl
theorem the_turns_compose_around_the_circle (a b c d : Bool) :
    (the_box_product the_turn_of_the_swap the_turn_of_the_quarter a b c d,
     the_box_product the_turn_of_the_quarter the_turn_of_the_sign a b c d,
     the_box_product the_turn_of_the_sign the_turn_of_the_swap a b c d)
      = (the_turn_of_the_sign a b c d, the_turn_of_the_swap a b c d, the_turn_of_the_quarter a b c d) := by
  cases a <;> cases b <;> cases c <;> cases d <;> rfl
theorem the_turns_bracket_around_the_circle (a b c d : Bool) :
    (the_box_bracket the_turn_of_the_swap the_turn_of_the_quarter a b c d,
     the_box_bracket the_turn_of_the_quarter the_turn_of_the_sign a b c d,
     the_box_bracket the_turn_of_the_sign the_turn_of_the_swap a b c d)
      = (2 * the_turn_of_the_sign a b c d, 2 * the_turn_of_the_swap a b c d, 2 * the_turn_of_the_quarter a b c d) := by
  cases a <;> cases b <;> cases c <;> cases d <;> rfl
theorem the_three_turns_are_independent (x y z : Int)
    (h : ∀ a b c d, x * the_turn_of_the_swap a b c d + y * the_turn_of_the_quarter a b c d + z * the_turn_of_the_sign a b c d = 0) :
    x = 0 ∧ y = 0 ∧ z = 0 := by
  have h1 := h true false true false; have h2 := h true false true true; have h3 := h true true true false
  have w1 : the_turn_of_the_swap true false true false = -1 := rfl
  have w2 : the_turn_of_the_quarter true false true false = 0 := rfl
  have w3 : the_turn_of_the_sign true false true false = 0 := rfl
  have q1 : the_turn_of_the_swap true false true true = 0 := rfl
  have q2 : the_turn_of_the_quarter true false true true = -1 := rfl
  have q3 : the_turn_of_the_sign true false true true = 0 := rfl
  have s1 : the_turn_of_the_swap true true true false = 0 := rfl
  have s2 : the_turn_of_the_quarter true true true false = 0 := rfl
  have s3 : the_turn_of_the_sign true true true false = -1 := rfl
  simp only [w1, w2, w3, q1, q2, q3, s1, s2, s3] at h1 h2 h3
  refine ⟨?_, ?_, ?_⟩ <;> omega
#print axioms the_symmetric_part_is_the_swap
#print axioms the_three_turns_square_to_minus_one
#print axioms the_turns_compose_around_the_circle
#print axioms the_turns_bracket_around_the_circle
#print axioms the_three_turns_are_independent
--| LANCZOS, NEWTON, BISECTION.  Square the table and it is thirty-six of itself less two hundred thirty-four: its trace and
--| its determinant, nothing more.  So two more steps of any walk are thirty-six of one step less two hundred thirty-four of
--| none, and the closed walks keep a three-term recurrence.  Rescale the coins so the crossing arms match and the table is the
--| tridiagonal Lanczos leaves, eighteen on the diagonal and root ninety off it: the clicks and the clock.  Its recurrence,
--| the step less eighteen squared less the round trip, ends at the table's own polynomial, and at thirteen y that is thirteen
--| times the residual.  Newton on that quadratic is the conjugate gradient; the signs of the recurrence are the bisection.
theorem the_table_satisfies_its_own_polynomial (a b : Bool) :
    the_table_product the_full_table the_full_table a b
      = the_table_trace the_full_table * the_full_table a b - the_table_determinant the_full_table * the_scaled_identity 1 a b := by
  cases a <;> cases b <;> rfl
def the_table_power : Nat → Table
  | 0 => the_scaled_identity 1
  | n + 1 => the_table_product (the_table_power n) the_full_table
theorem two_more_steps (A : Table) (a b : Bool) :
    the_table_product (the_table_product A the_full_table) the_full_table a b
      = 36 * the_table_product A the_full_table a b - 234 * A a b := by
  have h1 : the_full_table true true = 18 := rfl
  have h2 : the_full_table true false = 5 := rfl
  have h3 : the_full_table false true = 18 := rfl
  have h4 : the_full_table false false = 18 := rfl
  cases a <;> cases b <;> simp only [the_table_product, h1, h2, h3, h4] <;> omega
theorem the_walks_keep_a_three_term_recurrence (n : Nat) :
    the_table_trace (the_table_power (n + 2))
      = 36 * the_table_trace (the_table_power (n + 1)) - 234 * the_table_trace (the_table_power n) := by
  simp only [the_table_trace, the_table_power, two_more_steps]
  omega
theorem the_lanczos_recurrence_ends_at_the_table (z : Int) :
    (z - 18) * (z - 18) - (the_arm_weight true false : Int) * (the_arm_weight false true : Int)
      = z * z - the_table_trace the_full_table * z + the_table_determinant the_full_table := by
  have t : the_table_trace the_full_table = 36 := rfl
  have d : the_table_determinant the_full_table = 234 := rfl
  have r : (the_arm_weight true false : Int) * (the_arm_weight false true : Int) = 90 := rfl
  rw [t, d, r]; simp only [Int.sub_mul, Int.mul_sub]; omega
theorem the_lanczos_polynomial_is_the_residual (y : Int) :
    (13 * y) * (13 * y) - the_table_trace the_full_table * (13 * y) + the_table_determinant the_full_table
      = 13 * (13 * (y * y) - 36 * y + 18) := by
  have t : the_table_trace the_full_table = 36 := rfl
  have d : the_table_determinant the_full_table = 234 := rfl
  rw [t, d]; simp only [Int.mul_assoc, Int.mul_left_comm y 13]; omega
#print axioms the_table_satisfies_its_own_polynomial
#print axioms the_walks_keep_a_three_term_recurrence
#print axioms the_lanczos_recurrence_ends_at_the_table
#print axioms the_lanczos_polynomial_is_the_residual
--| IN LETTERS.  No list is measured here.  Any table squares to its trace times itself less its determinant.  Any table with
--| a on the diagonal and b, f on the crossings is the quarter turn times f less b, and the swap times b plus f, about a.  Its
--| two roots are a plus and a minus the root of the round trip b f, both solving its polynomial, and its trace and
--| determinant are two a and a squared less b f.  The polynomial is carried and never read: only its roots are seen.
theorem every_table_satisfies_its_own_polynomial (A : Table) (a b : Bool) :
    the_table_product A A a b = the_table_trace A * A a b - the_table_determinant A * the_scaled_identity 1 a b := by
  cases a <;> cases b <;>
  simp only [the_table_product, the_table_trace, the_table_determinant, the_scaled_identity, ite_true, ite_false,
    Bool.true_eq_false, Bool.false_eq_true, Int.mul_one, Int.mul_zero, Int.sub_zero, Int.add_mul] <;> ac_nf <;> omega
def the_table_of (a b f : Int) : Table := fun x y => if x = y then a else if x then b else f
theorem the_crossings_are_a_quarter_turn_and_a_swap (a b f : Int) (x y : Bool) :
    the_table_of a b f x y - the_table_of a b f y x = (f - b) * the_quarter_turn x y
      ∧ the_table_of a b f x y + the_table_of a b f y x - 2 * the_scaled_identity a x y = (b + f) * the_swap x y := by
  cases x <;> cases y <;>
  simp only [the_table_of, the_quarter_turn, the_swap, the_scaled_identity, ite_true, ite_false, Bool.true_eq_false,
    Bool.false_eq_true] <;> constructor <;> omega
def the_root_ring_product (r : Int) (p q : Int × Int) : Int × Int := (p.1 * q.1 + r * p.2 * q.2, p.1 * q.2 + p.2 * q.1)
theorem both_roots_solve_any_table (a b f : Int) :
    let r := b * f
    let up := ((a : Int), (1 : Int)); let dn := ((a : Int), (-1 : Int))
    (the_root_ring_product r up up).1 - 2 * a * up.1 + (a * a - r) = 0 ∧ (the_root_ring_product r up up).2 - 2 * a * up.2 = 0
      ∧ (the_root_ring_product r dn dn).1 - 2 * a * dn.1 + (a * a - r) = 0 ∧ (the_root_ring_product r dn dn).2 - 2 * a * dn.2 = 0
      ∧ the_table_trace (the_table_of a b f) = 2 * a ∧ the_table_determinant (the_table_of a b f) = a * a - r := by
  simp only [the_root_ring_product, the_table_trace, the_table_determinant, the_table_of, ite_true, ite_false,
    Bool.true_eq_false, Bool.false_eq_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (try simp only [Int.mul_one, Int.mul_neg, Int.neg_mul, Int.neg_neg, Int.one_mul]) <;>
    (try ac_nf) <;> (try simp only [← Int.mul_assoc]) <;> omega
#print axioms every_table_satisfies_its_own_polynomial
#print axioms the_crossings_are_a_quarter_turn_and_a_swap
#print axioms both_roots_solve_any_table
--| THE REFINEMENT OPERATOR, VARIED.  Read the table, matched, as the operator that takes a walk one level up, and ask of a
--| direction p, q how much the operator stretches it: a times the square of its length, plus root r times twice p q.  Twice
--| p q never leaves the band from minus to plus the square of the length, and it touches each edge on a diagonal.  So the
--| stretch runs from a less root r to a plus root r, top and bottom reached on the two diagonals: the two roots, as the
--| stationary values of the operator's own quotient, and no polynomial is written.
theorem a_square_is_never_negative (x : Int) : 0 ≤ x * x := by
  rcases Int.le_total 0 x with h | h
  · exact Int.mul_nonneg h h
  · have := Int.mul_nonneg (Int.neg_nonneg_of_nonpos h) (Int.neg_nonneg_of_nonpos h)
    rwa [Int.neg_mul_neg] at this
theorem the_rayleigh_quotient_lies_between_the_roots (p q : Int) :
    - (p * p + q * q) ≤ p * q + p * q ∧ p * q + p * q ≤ p * p + q * q := by
  have h1 := a_square_is_never_negative (p - q)
  have h2 := a_square_is_never_negative (p + q)
  simp only [Int.sub_mul, Int.mul_sub, Int.add_mul, Int.mul_add] at h1 h2
  constructor <;> (ac_nf at h1 h2 ⊢; omega)
theorem the_roots_are_reached_on_the_diagonals (p : Int) :
    p * p + p * p = p * p + p * p ∧ p * (-p) + p * (-p) = - (p * p + (-p) * (-p)) := by
  refine ⟨rfl, ?_⟩
  rw [Int.mul_neg, Int.neg_mul_neg]; omega
#print axioms the_rayleigh_quotient_lies_between_the_roots
#print axioms the_roots_are_reached_on_the_diagonals
--| THE TURNS ON THE LINKS.  Write a link as four whole numbers, a whole part and one for each turn, and its box is the sum:
--| the box reads the product of two links as the product of their boxes, and the conjugate as the transpose, so every link
--| is a rotation scaled by its length.  The action on a square is the sum of the squares of its holonomy's three turns:
--| never negative, nothing on a whole turn, and exact at the second order.  The holonomy is linear in every link.  Tile the
--| torus again and every flat lattice of turns is stationary on every link.  Every link the turn of the swap: the square goes
--| once around and comes back whole, and solves the equation.  Turn one link to the quarter turn and the lattice reads two.
abbrev Turns := Int × Int × Int × Int
def the_box_of (q : Turns) : Box4 := fun a b c d =>
  q.1 * the_box_identity a b c d + q.2.1 * the_turn_of_the_swap a b c d
    + q.2.2.1 * the_turn_of_the_quarter a b c d + q.2.2.2 * the_turn_of_the_sign a b c d
def the_turns_product (p q : Turns) : Turns :=
  (p.1 * q.1 - p.2.1 * q.2.1 - p.2.2.1 * q.2.2.1 - p.2.2.2 * q.2.2.2,
   p.1 * q.2.1 + p.2.1 * q.1 + p.2.2.1 * q.2.2.2 - p.2.2.2 * q.2.2.1,
   p.1 * q.2.2.1 + p.2.2.1 * q.1 + p.2.2.2 * q.2.1 - p.2.1 * q.2.2.2,
   p.1 * q.2.2.2 + p.2.2.2 * q.1 + p.2.1 * q.2.2.1 - p.2.2.1 * q.2.1)
def the_turns_conjugate (q : Turns) : Turns := (q.1, -q.2.1, -q.2.2.1, -q.2.2.2)
theorem the_box_reads_the_product (p q : Turns) (a b c d : Bool) :
    the_box_of (the_turns_product p q) a b c d = the_box_product (the_box_of p) (the_box_of q) a b c d := by
  cases a <;> cases b <;> cases c <;> cases d <;>
  simp only [the_box_of, the_turns_product, the_box_product, the_box_identity, the_turn_of_the_swap, the_turn_of_the_quarter,
    the_turn_of_the_sign, the_box, the_swap, the_quarter_turn, the_sign_table, the_scaled_identity, the_coin_sign,
    ite_true, ite_false, Bool.true_eq_false, Bool.false_eq_true, Int.mul_zero, Int.zero_mul, Int.mul_one,
    Int.add_zero, Int.zero_add, Int.mul_neg, Int.neg_mul, Int.neg_neg, Int.mul_add, Int.add_mul] <;>
  ac_nf <;> omega
theorem the_conjugate_is_the_transpose (q : Turns) (a b c d : Bool) :
    the_box_of (the_turns_conjugate q) a b c d = the_box_of q b a d c := by
  cases a <;> cases b <;> cases c <;> cases d <;>
  simp only [the_box_of, the_turns_conjugate, the_box_identity, the_turn_of_the_swap, the_turn_of_the_quarter,
    the_turn_of_the_sign, the_box, the_swap, the_quarter_turn, the_sign_table, the_scaled_identity, the_coin_sign,
    ite_true, ite_false, Bool.true_eq_false, Bool.false_eq_true] <;> omega
def the_varied_turns (q y : Turns) (t : Int) : Turns := (q.1 + t * y.1, q.2.1 + t * y.2.1, q.2.2.1 + t * y.2.2.1, q.2.2.2 + t * y.2.2.2)
def the_turns_action (q : Turns) : Int := q.2.1 * q.2.1 + q.2.2.1 * q.2.2.1 + q.2.2.2 * q.2.2.2
def the_turns_dot (q y : Turns) : Int := q.2.1 * y.2.1 + q.2.2.1 * y.2.2.1 + q.2.2.2 * y.2.2.2
def the_first_variation_of_the_turns (q y : Turns) : Int := the_turns_dot q y + the_turns_dot y q
def the_whole_turn (c : Int) : Turns := (c, 0, 0, 0)
theorem the_turns_action_stops_at_second_order (q y : Turns) (t : Int) :
    the_turns_action (the_varied_turns q y t)
      = the_turns_action q + t * the_first_variation_of_the_turns q y + t * t * the_turns_action y := by
  simp only [the_turns_action, the_varied_turns, the_first_variation_of_the_turns, the_turns_dot, Int.mul_add, Int.add_mul]
  ac_nf
theorem the_turns_action_vanishes_on_a_whole_turn (c : Int) : the_turns_action (the_whole_turn c) = 0 := rfl
theorem a_whole_turn_is_stationary (c : Int) (y : Turns) : the_first_variation_of_the_turns (the_whole_turn c) y = 0 := by
  simp only [the_first_variation_of_the_turns, the_turns_dot, the_whole_turn, Int.zero_mul, Int.add_zero, Int.mul_zero]
theorem the_turns_action_is_never_negative (q : Turns) : 0 ≤ the_turns_action q := by
  simp only [the_turns_action]
  have sq : ∀ x : Int, 0 ≤ x * x := fun x => by
    rcases Int.le_total 0 x with h | h
    · exact Int.mul_nonneg h h
    · have := Int.mul_nonneg (Int.neg_nonneg_of_nonpos h) (Int.neg_nonneg_of_nonpos h)
      rwa [Int.neg_mul_neg] at this
  have h1 := sq q.2.1; have h2 := sq q.2.2.1; have h3 := sq q.2.2.2
  omega
theorem the_product_is_linear_on_the_left (p y q : Turns) (t : Int) :
    the_turns_product (the_varied_turns p y t) q = the_varied_turns (the_turns_product p q) (the_turns_product y q) t := by
  simp only [the_turns_product, the_varied_turns, Prod.mk.injEq, Int.mul_add, Int.add_mul, Int.mul_sub]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ac_nf <;> omega
theorem the_product_is_linear_on_the_right (p q y : Turns) (t : Int) :
    the_turns_product p (the_varied_turns q y t) = the_varied_turns (the_turns_product p q) (the_turns_product p y) t := by
  simp only [the_turns_product, the_varied_turns, Prod.mk.injEq, Int.mul_add, Int.mul_sub]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ac_nf <;> omega
theorem the_conjugate_is_linear (q y : Turns) (t : Int) :
    the_turns_conjugate (the_varied_turns q y t) = the_varied_turns (the_turns_conjugate q) (the_turns_conjugate y) t := by
  simp only [the_turns_conjugate, the_varied_turns, Int.neg_add, Int.mul_neg]
def the_turns_holonomy (bottom right top left : Turns) : Turns :=
  the_turns_product (the_turns_product (the_turns_product bottom right) (the_turns_conjugate top)) (the_turns_conjugate left)
theorem the_turns_holonomy_is_linear_in_each_link (B R T L X : Turns) (t : Int) :
    the_turns_holonomy (the_varied_turns B X t) R T L = the_varied_turns (the_turns_holonomy B R T L) (the_turns_holonomy X R T L) t ∧
    the_turns_holonomy B (the_varied_turns R X t) T L = the_varied_turns (the_turns_holonomy B R T L) (the_turns_holonomy B X T L) t ∧
    the_turns_holonomy B R (the_varied_turns T X t) L = the_varied_turns (the_turns_holonomy B R T L) (the_turns_holonomy B R X L) t ∧
    the_turns_holonomy B R T (the_varied_turns L X t) = the_varied_turns (the_turns_holonomy B R T L) (the_turns_holonomy B R T X) t := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  simp only [the_turns_holonomy, the_conjugate_is_linear, the_product_is_linear_on_the_left, the_product_is_linear_on_the_right]
theorem the_unvaried_turns (q : Turns) (t : Int) : q = the_varied_turns q (the_whole_turn 0) t := by
  simp only [the_varied_turns, the_whole_turn, Int.mul_zero, Int.add_zero]
abbrev TurnsLattice := Bool → Bool → Bool → Turns
def the_turns_square (U : TurnsLattice) (i j : Bool) : Turns :=
  the_turns_holonomy (U false i j) (U true (!i) j) (U false i (!j)) (U true i j)
def the_turns_lattice_action (U : TurnsLattice) : Int :=
  the_turns_action (the_turns_square U false false) + the_turns_action (the_turns_square U false true)
    + the_turns_action (the_turns_square U true false) + the_turns_action (the_turns_square U true true)
def the_varied_turns_lattice (U : TurnsLattice) (d i j : Bool) (X : Turns) (t : Int) : TurnsLattice :=
  fun d' i' j' => if d' = d ∧ i' = i ∧ j' = j then the_varied_turns (U d i j) X t else U d' i' j'
theorem each_turns_square_holds_a_link_once (U : TurnsLattice) (d i j : Bool) (X : Turns) (t : Int) (i' j' : Bool) :
    ∃ Y, the_turns_square (the_varied_turns_lattice U d i j X t) i' j' = the_varied_turns (the_turns_square U i' j') Y t := by
  cases d <;> cases i <;> cases j <;> cases i' <;> cases j' <;>
    simp (config := { decide := true }) only [the_turns_square, the_varied_turns_lattice, if_true, if_false, Bool.not_false, Bool.not_true,
      (the_turns_holonomy_is_linear_in_each_link _ _ _ _ _ _).1, (the_turns_holonomy_is_linear_in_each_link _ _ _ _ _ _).2.1,
      (the_turns_holonomy_is_linear_in_each_link _ _ _ _ _ _).2.2.1, (the_turns_holonomy_is_linear_in_each_link _ _ _ _ _ _).2.2.2] <;>
    first
    | with_reducible exact ⟨_, rfl⟩
    | with_reducible exact ⟨_, the_unvaried_turns _ t⟩
theorem a_flat_turns_lattice_is_stationary (U : TurnsLattice) (flat : ∀ i j, ∃ c, the_turns_square U i j = the_whole_turn c)
    (d i j : Bool) (X : Turns) (t : Int) :
    ∃ q, the_turns_lattice_action (the_varied_turns_lattice U d i j X t) = the_turns_lattice_action U + t * t * q := by
  have each : ∀ i' j', ∃ q, the_turns_action (the_turns_square (the_varied_turns_lattice U d i j X t) i' j')
      = the_turns_action (the_turns_square U i' j') + t * t * q := by
    intro i' j'
    obtain ⟨Y, hY⟩ := each_turns_square_holds_a_link_once U d i j X t i' j'
    obtain ⟨c, hc⟩ := flat i' j'
    refine ⟨the_turns_action Y, ?_⟩
    rw [hY, the_turns_action_stops_at_second_order, hc, a_whole_turn_is_stationary, Int.mul_zero, Int.add_zero]
  obtain ⟨q1, h1⟩ := each false false
  obtain ⟨q2, h2⟩ := each false true
  obtain ⟨q3, h3⟩ := each true false
  obtain ⟨q4, h4⟩ := each true true
  refine ⟨q1 + q2 + q3 + q4, ?_⟩
  simp only [the_turns_lattice_action, h1, h2, h3, h4, Int.mul_add]
  omega
def the_swap_turn : Turns := (0, 1, 0, 0)
def the_quarter_turn_turn : Turns := (0, 0, 1, 0)
def the_swap_lattice : TurnsLattice := fun _ _ _ => the_swap_turn
theorem the_swap_lattice_is_flat (i j : Bool) : ∃ c, the_turns_square the_swap_lattice i j = the_whole_turn c := ⟨1, rfl⟩
theorem the_swap_lattice_has_no_action : the_turns_lattice_action the_swap_lattice = 0 := by decide
theorem the_swap_lattice_solves_the_lattice_equation (d i j : Bool) (X : Turns) (t : Int) :
    ∃ q, the_turns_lattice_action (the_varied_turns_lattice the_swap_lattice d i j X t) = t * t * q := by
  obtain ⟨q, h⟩ := a_flat_turns_lattice_is_stationary _ the_swap_lattice_is_flat d i j X t
  exact ⟨q, by rw [h, the_swap_lattice_has_no_action, Int.zero_add]⟩
def the_turned_turns_lattice : TurnsLattice :=
  fun d i j => if d = false ∧ i = false ∧ j = false then the_quarter_turn_turn else the_swap_turn
theorem the_turned_turns_lattice_has_action : the_turns_lattice_action the_turned_turns_lattice = 2 := by decide
#print axioms the_box_reads_the_product
#print axioms the_conjugate_is_the_transpose
#print axioms the_turns_action_stops_at_second_order
#print axioms the_turns_action_is_never_negative
#print axioms the_turns_holonomy_is_linear_in_each_link
#print axioms each_turns_square_holds_a_link_once
#print axioms a_flat_turns_lattice_is_stationary
#print axioms the_swap_lattice_solves_the_lattice_equation
#print axioms the_turned_turns_lattice_has_action
--| THE GAUGE ON THE LINKS.  The length of a link is the sum of its four squares, and the length of a product is the product of the lengths:
--| Euler's four squares.  Turn a holonomy by any link and its whole part is kept, scaled by the length; so its action is
--| scaled by the length twice, and a link of length one leaves it alone.  Put a turn of length one at every site of the
--| torus and carry each link from its start to its end: around every square the turns cancel at three corners and close on
--| the fourth, and the lattice reads the same.  The action is gauge invariant.
def the_turns_norm (q : Turns) : Int := q.1 * q.1 + q.2.1 * q.2.1 + q.2.2.1 * q.2.2.1 + q.2.2.2 * q.2.2.2
theorem the_action_is_the_norm_less_the_whole_part (q : Turns) : the_turns_action q = the_turns_norm q - q.1 * q.1 := by
  simp only [the_turns_action, the_turns_norm]; omega
theorem the_norm_is_multiplicative (p q : Turns) :
    the_turns_norm (the_turns_product p q) = the_turns_norm p * the_turns_norm q := by
  simp only [the_turns_norm, the_turns_product, Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul]
  ac_nf; omega
theorem the_conjugate_keeps_the_norm (q : Turns) : the_turns_norm (the_turns_conjugate q) = the_turns_norm q := by
  simp only [the_turns_norm, the_turns_conjugate, Int.neg_mul_neg]
theorem the_whole_part_is_kept (g q : Turns) :
    (the_turns_product (the_turns_product g q) (the_turns_conjugate g)).1 = the_turns_norm g * q.1 := by
  simp only [the_turns_norm, the_turns_product, the_turns_conjugate, Int.add_mul, Int.sub_mul, Int.mul_neg]
  ac_nf; omega
theorem the_turns_action_is_gauge_covariant (g q : Turns) :
    the_turns_action (the_turns_product (the_turns_product g q) (the_turns_conjugate g))
      = the_turns_norm g * the_turns_norm g * the_turns_action q := by
  rw [the_action_is_the_norm_less_the_whole_part, the_action_is_the_norm_less_the_whole_part, the_whole_part_is_kept,
    the_norm_is_multiplicative, the_norm_is_multiplicative, the_conjugate_keeps_the_norm]
  simp only [Int.mul_sub]
  ac_nf
theorem a_unit_turn_leaves_the_action (g q : Turns) (h : the_turns_norm g = 1) :
    the_turns_action (the_turns_product (the_turns_product g q) (the_turns_conjugate g)) = the_turns_action q := by
  rw [the_turns_action_is_gauge_covariant, h, Int.one_mul, Int.one_mul]
theorem the_product_is_associative (p q r : Turns) :
    the_turns_product (the_turns_product p q) r = the_turns_product p (the_turns_product q r) := by
  simp only [the_turns_product, Prod.mk.injEq, Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ac_nf <;> omega
theorem the_conjugate_reverses_the_product (p q : Turns) :
    the_turns_conjugate (the_turns_product p q) = the_turns_product (the_turns_conjugate q) (the_turns_conjugate p) := by
  simp only [the_turns_conjugate, the_turns_product, Prod.mk.injEq, Int.mul_neg, Int.neg_mul, Int.neg_neg]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ac_nf <;> omega
theorem the_conjugate_returns (q : Turns) : the_turns_conjugate (the_turns_conjugate q) = q := by
  simp only [the_turns_conjugate, Int.neg_neg]
theorem a_unit_turn_cancels (g X : Turns) (h : the_turns_norm g = 1) :
    the_turns_product (the_turns_conjugate g) (the_turns_product g X) = X := by
  rw [← the_product_is_associative]
  have hg : the_turns_product (the_turns_conjugate g) g = the_whole_turn 1 := by
    rw [← h]; simp only [the_turns_product, the_turns_conjugate, the_whole_turn, the_turns_norm, Prod.mk.injEq, Int.neg_mul]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> ac_nf <;> omega
  rw [hg]; simp only [the_turns_product, the_whole_turn, Int.one_mul, Int.zero_mul, Int.sub_zero, Int.add_zero]
theorem the_gauged_holonomy (g0 g1 g2 g3 B R T L : Turns)
    (h1 : the_turns_norm g1 = 1) (h2 : the_turns_norm g2 = 1) (h3 : the_turns_norm g3 = 1) :
    the_turns_holonomy
        (the_turns_product (the_turns_product g0 B) (the_turns_conjugate g1))
        (the_turns_product (the_turns_product g1 R) (the_turns_conjugate g2))
        (the_turns_product (the_turns_product g3 T) (the_turns_conjugate g2))
        (the_turns_product (the_turns_product g0 L) (the_turns_conjugate g3))
      = the_turns_product (the_turns_product g0 (the_turns_holonomy B R T L)) (the_turns_conjugate g0) := by
  simp only [the_turns_holonomy, the_conjugate_reverses_the_product, the_conjugate_returns, the_product_is_associative,
    a_unit_turn_cancels _ _ h1, a_unit_turn_cancels _ _ h2, a_unit_turn_cancels _ _ h3]
def the_end_of_the_link (d i j : Bool) : Bool × Bool := if d then (i, !j) else (!i, j)
def the_gauged_lattice (U : TurnsLattice) (g : Bool → Bool → Turns) : TurnsLattice := fun d i j =>
  the_turns_product (the_turns_product (g i j) (U d i j))
    (the_turns_conjugate (g (the_end_of_the_link d i j).1 (the_end_of_the_link d i j).2))
theorem the_gauged_square (U : TurnsLattice) (g : Bool → Bool → Turns) (unit : ∀ i j, the_turns_norm (g i j) = 1) (i j : Bool) :
    the_turns_square (the_gauged_lattice U g) i j
      = the_turns_product (the_turns_product (g i j) (the_turns_square U i j)) (the_turns_conjugate (g i j)) := by
  simp only [the_turns_square, the_gauged_lattice, the_end_of_the_link, if_true, Bool.not_not]
  exact the_gauged_holonomy _ _ _ _ _ _ _ _ (unit _ _) (unit _ _) (unit _ _)
theorem the_lattice_action_is_gauge_invariant (U : TurnsLattice) (g : Bool → Bool → Turns)
    (unit : ∀ i j, the_turns_norm (g i j) = 1) :
    the_turns_lattice_action (the_gauged_lattice U g) = the_turns_lattice_action U := by
  simp only [the_turns_lattice_action, the_gauged_square U g unit, a_unit_turn_leaves_the_action _ _ (unit _ _)]
#print axioms the_norm_is_multiplicative
#print axioms the_whole_part_is_kept
#print axioms the_turns_action_is_gauge_covariant
#print axioms a_unit_turn_leaves_the_action
#print axioms the_product_is_associative
#print axioms the_gauged_holonomy
#print axioms the_lattice_action_is_gauge_invariant
--| THE GAMMAS.  Four tables on the box, each two of them anticommuting: the quarter turn outside, which squares to minus one,
--| and the swap, the sign over the swap, the sign over the sign, which square to one.  That is the Clifford algebra of a
--| metric with one minus and three plus, real, on the pair's four by four box.  Their product, the fifth, squares to minus
--| one and anticommutes with all four.  The products of two space gammas square to minus one and compose around the circle,
--| the other way: a second set of turns, the spin, and every one of them commutes with the three turns of the links.  The
--| time gamma is the quarter turn of the links, the same table.  Whose spin, and which way time runs, is not written here.
def the_box_anticommutator (X Y : Box4) : Box4 := fun a b c d => the_box_product X Y a b c d + the_box_product Y X a b c d
def the_zero_box : Box4 := fun _ _ _ _ => 0
def the_time_gamma : Box4 := the_turn_of_the_quarter
def the_first_gamma : Box4 := the_box the_swap (the_scaled_identity 1)
def the_second_gamma : Box4 := the_box the_sign_table the_swap
def the_third_gamma : Box4 := the_box the_sign_table the_sign_table
theorem the_gammas_square_to_the_metric (a b c d : Bool) :
    (the_box_product the_time_gamma the_time_gamma a b c d, the_box_product the_first_gamma the_first_gamma a b c d,
     the_box_product the_second_gamma the_second_gamma a b c d, the_box_product the_third_gamma the_third_gamma a b c d)
      = (- the_box_identity a b c d, the_box_identity a b c d, the_box_identity a b c d, the_box_identity a b c d) := by
  cases a <;> cases b <;> cases c <;> cases d <;> rfl
theorem the_gammas_anticommute (a b c d : Bool) :
    (the_box_anticommutator the_time_gamma the_first_gamma a b c d, the_box_anticommutator the_time_gamma the_second_gamma a b c d,
     the_box_anticommutator the_time_gamma the_third_gamma a b c d, the_box_anticommutator the_first_gamma the_second_gamma a b c d,
     the_box_anticommutator the_first_gamma the_third_gamma a b c d, the_box_anticommutator the_second_gamma the_third_gamma a b c d)
      = (0, 0, 0, 0, 0, 0) := by
  cases a <;> cases b <;> cases c <;> cases d <;> rfl
def the_fifth_gamma : Box4 :=
  the_box_product (the_box_product (the_box_product the_time_gamma the_first_gamma) the_second_gamma) the_third_gamma
theorem the_fifth_gamma_squares_to_minus_one_and_anticommutes (a b c d : Bool) :
    (the_box_product the_fifth_gamma the_fifth_gamma a b c d,
     the_box_anticommutator the_fifth_gamma the_time_gamma a b c d, the_box_anticommutator the_fifth_gamma the_first_gamma a b c d,
     the_box_anticommutator the_fifth_gamma the_second_gamma a b c d, the_box_anticommutator the_fifth_gamma the_third_gamma a b c d)
      = (- the_box_identity a b c d, 0, 0, 0, 0) := by
  cases a <;> cases b <;> cases c <;> cases d <;> rfl
def the_spin_one : Box4 := the_box_product the_second_gamma the_third_gamma
def the_spin_two : Box4 := the_box_product the_third_gamma the_first_gamma
def the_spin_three : Box4 := the_box_product the_first_gamma the_second_gamma
theorem the_spin_is_a_second_set_of_turns (a b c d : Bool) :
    (the_box_product the_spin_one the_spin_one a b c d, the_box_product the_spin_two the_spin_two a b c d,
     the_box_product the_spin_three the_spin_three a b c d,
     the_box_product the_spin_one the_spin_two a b c d, the_box_product the_spin_two the_spin_three a b c d,
     the_box_product the_spin_three the_spin_one a b c d)
      = (- the_box_identity a b c d, - the_box_identity a b c d, - the_box_identity a b c d,
         - the_spin_three a b c d, - the_spin_one a b c d, - the_spin_two a b c d) := by
  cases a <;> cases b <;> cases c <;> cases d <;> rfl
theorem the_spin_commutes_with_the_turns (a b c d : Bool) :
    (the_box_bracket the_spin_one the_turn_of_the_swap a b c d, the_box_bracket the_spin_one the_turn_of_the_quarter a b c d,
     the_box_bracket the_spin_one the_turn_of_the_sign a b c d,
     the_box_bracket the_spin_two the_turn_of_the_swap a b c d, the_box_bracket the_spin_two the_turn_of_the_quarter a b c d,
     the_box_bracket the_spin_two the_turn_of_the_sign a b c d,
     the_box_bracket the_spin_three the_turn_of_the_swap a b c d, the_box_bracket the_spin_three the_turn_of_the_quarter a b c d,
     the_box_bracket the_spin_three the_turn_of_the_sign a b c d) = (0, 0, 0, 0, 0, 0, 0, 0, 0) := by
  cases a <;> cases b <;> cases c <;> cases d <;> rfl
#print axioms the_gammas_square_to_the_metric
#print axioms the_gammas_anticommute
#print axioms the_fifth_gamma_squares_to_minus_one_and_anticommutes
#print axioms the_spin_is_a_second_set_of_turns
#print axioms the_spin_commutes_with_the_turns
--| EVERY TORUS.  Not two by two: any number of sites around, one included, where a square's bottom and top are one link.
--| Vary one link and each square moves along one direction, however many of its edges that link is, because the variations
--| add.  So every flat torus is stationary on every link, at every size, and every torus is gauge invariant under turns of
--| length one at its sites.  The torus whose every link is the turn of the swap is flat at every size and solves the equation.
--| A family, not a limit: the continuum is not written here.
theorem the_variations_add (H Y Z : Turns) (t : Int) :
    the_varied_turns (the_varied_turns H Y t) Z t = the_varied_turns H (the_varied_turns Y Z 1) t := by
  simp only [the_varied_turns, Int.one_mul, Int.mul_add, Int.add_assoc]
theorem a_square_varies_along_one_direction (B R T L X : Turns) (t : Int) (cB cR cT cL : Bool) :
    ∃ W, the_turns_holonomy (if cB then the_varied_turns B X t else B) (if cR then the_varied_turns R X t else R)
                            (if cT then the_varied_turns T X t else T) (if cL then the_varied_turns L X t else L)
      = the_varied_turns (the_turns_holonomy B R T L) W t := by
  cases cB <;> cases cR <;> cases cT <;> cases cL <;>
    simp only [if_true, if_false, Bool.false_eq_true,
      (the_turns_holonomy_is_linear_in_each_link _ _ _ _ _ _).1, (the_turns_holonomy_is_linear_in_each_link _ _ _ _ _ _).2.1,
      (the_turns_holonomy_is_linear_in_each_link _ _ _ _ _ _).2.2.1, (the_turns_holonomy_is_linear_in_each_link _ _ _ _ _ _).2.2.2,
      the_variations_add] <;>
    first
    | exact ⟨_, rfl⟩
    | exact ⟨_, the_unvaried_turns _ t⟩
abbrev Torus (n : Nat) := Bool → Fin (n+1) → Fin (n+1) → Turns
def the_torus_square {n : Nat} (U : Torus n) (i j : Fin (n+1)) : Turns :=
  the_turns_holonomy (U false i j) (U true (i+1) j) (U false i (j+1)) (U true i j)
def the_sum : List Int → Int
  | [] => 0
  | a :: l => a + the_sum l
def the_torus_action {n : Nat} (U : Torus n) : Int :=
  the_sum ((List.finRange (n+1)).map fun i => the_sum ((List.finRange (n+1)).map fun j =>
    the_turns_action (the_torus_square U i j)))
def the_varied_torus {n : Nat} (U : Torus n) (d : Bool) (i j : Fin (n+1)) (X : Turns) (t : Int) : Torus n :=
  fun d' i' j' => if d' = d ∧ i' = i ∧ j' = j then the_varied_turns (U d i j) X t else U d' i' j'
theorem the_torus_square_varies_along_one_direction {n : Nat} (U : Torus n) (d : Bool) (i j : Fin (n+1)) (X : Turns) (t : Int)
    (i' j' : Fin (n+1)) :
    ∃ W, the_torus_square (the_varied_torus U d i j X t) i' j' = the_varied_turns (the_torus_square U i' j') W t := by
  have e : ∀ d'' i'' j'', the_varied_torus U d i j X t d'' i'' j''
      = if decide (d'' = d ∧ i'' = i ∧ j'' = j) then the_varied_turns (U d'' i'' j'') X t else U d'' i'' j'' := by
    intro d'' i'' j''
    simp only [the_varied_torus]
    by_cases h : d'' = d ∧ i'' = i ∧ j'' = j
    · obtain ⟨rfl, rfl, rfl⟩ := h; simp
    · simp [h]
  simp only [the_torus_square, e]
  exact a_square_varies_along_one_direction _ _ _ _ _ _ _ _ _ _
theorem the_sums_move_at_second_order {α : Type} (l : List α) (f f' : α → Int) (t : Int)
    (h : ∀ x, ∃ q, f' x = f x + t * t * q) :
    ∃ Q, the_sum (l.map f') = the_sum (l.map f) + t * t * Q := by
  induction l with
  | nil => exact ⟨0, by simp [the_sum]⟩
  | cons a l ih =>
    obtain ⟨q, hq⟩ := h a
    obtain ⟨Q, hQ⟩ := ih
    refine ⟨q + Q, ?_⟩
    simp only [List.map_cons, the_sum, hq, hQ, Int.mul_add]
    omega
theorem a_flat_torus_is_stationary {n : Nat} (U : Torus n) (flat : ∀ i j, ∃ c, the_torus_square U i j = the_whole_turn c)
    (d : Bool) (i j : Fin (n+1)) (X : Turns) (t : Int) :
    ∃ q, the_torus_action (the_varied_torus U d i j X t) = the_torus_action U + t * t * q := by
  apply the_sums_move_at_second_order
  intro i'
  apply the_sums_move_at_second_order
  intro j'
  obtain ⟨W, hW⟩ := the_torus_square_varies_along_one_direction U d i j X t i' j'
  obtain ⟨c, hc⟩ := flat i' j'
  refine ⟨the_turns_action W, ?_⟩
  rw [hW, the_turns_action_stops_at_second_order, hc, a_whole_turn_is_stationary, Int.mul_zero, Int.add_zero]
def the_gauged_torus {n : Nat} (U : Torus n) (g : Fin (n+1) → Fin (n+1) → Turns) : Torus n := fun d i j =>
  the_turns_product (the_turns_product (g i j) (U d i j)) (the_turns_conjugate (if d then g i (j+1) else g (i+1) j))
theorem the_gauged_torus_square {n : Nat} (U : Torus n) (g : Fin (n+1) → Fin (n+1) → Turns)
    (unit : ∀ i j, the_turns_norm (g i j) = 1) (i j : Fin (n+1)) :
    the_torus_square (the_gauged_torus U g) i j
      = the_turns_product (the_turns_product (g i j) (the_torus_square U i j)) (the_turns_conjugate (g i j)) := by
  simp only [the_torus_square, the_gauged_torus, if_true, if_false, Bool.false_eq_true]
  exact the_gauged_holonomy _ _ _ _ _ _ _ _ (unit _ _) (unit _ _) (unit _ _)
theorem every_torus_is_gauge_invariant {n : Nat} (U : Torus n) (g : Fin (n+1) → Fin (n+1) → Turns)
    (unit : ∀ i j, the_turns_norm (g i j) = 1) :
    the_torus_action (the_gauged_torus U g) = the_torus_action U := by
  simp only [the_torus_action, the_gauged_torus_square U g unit, a_unit_turn_leaves_the_action _ _ (unit _ _)]
def the_swap_torus (n : Nat) : Torus n := fun _ _ _ => the_swap_turn
theorem the_swap_torus_is_flat (n : Nat) (i j : Fin (n+1)) : ∃ c, the_torus_square (the_swap_torus n) i j = the_whole_turn c :=
  ⟨1, rfl⟩
theorem the_sum_of_nothing {α : Type} (l : List α) : the_sum (l.map fun _ => (0 : Int)) = 0 := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.map_cons, the_sum, ih, Int.add_zero]
theorem the_swap_torus_has_no_action (n : Nat) : the_torus_action (the_swap_torus n) = 0 := by
  have h : ∀ i j : Fin (n+1), the_turns_action (the_torus_square (the_swap_torus n) i j) = 0 := fun _ _ => rfl
  simp only [the_torus_action, h, the_sum_of_nothing]
theorem every_swap_torus_solves_the_lattice_equation (n : Nat) (d : Bool) (i j : Fin (n+1)) (X : Turns) (t : Int) :
    ∃ q, the_torus_action (the_varied_torus (the_swap_torus n) d i j X t) = t * t * q := by
  obtain ⟨q, h⟩ := a_flat_torus_is_stationary _ (the_swap_torus_is_flat n) d i j X t
  exact ⟨q, by rw [h, the_swap_torus_has_no_action, Int.zero_add]⟩
#print axioms a_square_varies_along_one_direction
#print axioms the_torus_square_varies_along_one_direction
#print axioms a_flat_torus_is_stationary
#print axioms every_torus_is_gauge_invariant
#print axioms every_swap_torus_solves_the_lattice_equation
--| FOUR DIRECTIONS.  Sites with four coordinates, four directions, and a square for every pair of them, six at each site and
--| the same square counted both ways.  The steps commute.  Turn every site by a turn of length one: the action is unchanged,
--| at every size.  Vary one link: a torus whose squares are all whole moves only at the second order.  Four is counted here.
abbrev Site4 (n : Nat) := (Fin (n+1) × Fin (n+1)) × (Fin (n+1) × Fin (n+1))
abbrev Direction := Bool × Bool
def the_step {n : Nat} (μ : Direction) (x : Site4 n) : Site4 n :=
  if μ.1 then (if μ.2 then (x.1, (x.2.1, x.2.2 + 1)) else (x.1, (x.2.1 + 1, x.2.2)))
  else (if μ.2 then ((x.1.1, x.1.2 + 1), x.2) else ((x.1.1 + 1, x.1.2), x.2))
theorem the_steps_commute {n : Nat} (μ ν : Direction) (x : Site4 n) : the_step ν (the_step μ x) = the_step μ (the_step ν x) := by
  obtain ⟨⟨a, b⟩, ⟨c, d⟩⟩ := x; obtain ⟨m1, m2⟩ := μ; obtain ⟨n1, n2⟩ := ν
  cases m1 <;> cases m2 <;> cases n1 <;> cases n2 <;> rfl
abbrev Torus4 (n : Nat) := Direction → Site4 n → Turns
def the_square4 {n : Nat} (U : Torus4 n) (μ ν : Direction) (x : Site4 n) : Turns :=
  the_turns_holonomy (U μ x) (U ν (the_step μ x)) (U μ (the_step ν x)) (U ν x)
def the_directions : List Direction := [(false, false), (false, true), (true, false), (true, true)]
def the_sites4 (n : Nat) : List (Site4 n) :=
  (List.finRange (n+1)).flatMap fun a => (List.finRange (n+1)).flatMap fun b =>
    (List.finRange (n+1)).flatMap fun c => (List.finRange (n+1)).map fun d => ((a, b), (c, d))
def the_action4 {n : Nat} (U : Torus4 n) : Int :=
  the_sum (the_directions.map fun μ => the_sum (the_directions.map fun ν =>
    the_sum ((the_sites4 n).map fun x => the_turns_action (the_square4 U μ ν x))))
def the_gauged_torus4 {n : Nat} (U : Torus4 n) (g : Site4 n → Turns) : Torus4 n := fun μ x =>
  the_turns_product (the_turns_product (g x) (U μ x)) (the_turns_conjugate (g (the_step μ x)))
theorem the_gauged_square4 {n : Nat} (U : Torus4 n) (g : Site4 n → Turns) (unit : ∀ x, the_turns_norm (g x) = 1)
    (μ ν : Direction) (x : Site4 n) :
    the_square4 (the_gauged_torus4 U g) μ ν x
      = the_turns_product (the_turns_product (g x) (the_square4 U μ ν x)) (the_turns_conjugate (g x)) := by
  simp only [the_square4, the_gauged_torus4, the_steps_commute ν μ x]
  exact the_gauged_holonomy _ _ _ _ _ _ _ _ (unit _) (unit _) (unit _)
theorem every_four_torus_is_gauge_invariant {n : Nat} (U : Torus4 n) (g : Site4 n → Turns) (unit : ∀ x, the_turns_norm (g x) = 1) :
    the_action4 (the_gauged_torus4 U g) = the_action4 U := by
  simp only [the_action4, the_gauged_square4 U g unit, a_unit_turn_leaves_the_action _ _ (unit _)]
def the_varied_torus4 {n : Nat} (U : Torus4 n) (μ₀ : Direction) (x₀ : Site4 n) (X : Turns) (t : Int) : Torus4 n :=
  fun μ x => if μ = μ₀ ∧ x = x₀ then the_varied_turns (U μ₀ x₀) X t else U μ x
theorem the_square4_varies_along_one_direction {n : Nat} (U : Torus4 n) (μ₀ : Direction) (x₀ : Site4 n) (X : Turns) (t : Int)
    (μ ν : Direction) (x : Site4 n) :
    ∃ W, the_square4 (the_varied_torus4 U μ₀ x₀ X t) μ ν x = the_varied_turns (the_square4 U μ ν x) W t := by
  have e : ∀ μ' x', the_varied_torus4 U μ₀ x₀ X t μ' x'
      = if decide (μ' = μ₀ ∧ x' = x₀) then the_varied_turns (U μ' x') X t else U μ' x' := by
    intro μ' x'
    simp only [the_varied_torus4]
    by_cases h : μ' = μ₀ ∧ x' = x₀
    · obtain ⟨rfl, rfl⟩ := h; simp
    · simp [h]
  simp only [the_square4, e]
  exact a_square_varies_along_one_direction _ _ _ _ _ _ _ _ _ _
theorem a_flat_four_torus_is_stationary {n : Nat} (U : Torus4 n)
    (flat : ∀ μ ν x, ∃ c, the_square4 U μ ν x = the_whole_turn c) (μ₀ : Direction) (x₀ : Site4 n) (X : Turns) (t : Int) :
    ∃ q, the_action4 (the_varied_torus4 U μ₀ x₀ X t) = the_action4 U + t * t * q := by
  apply the_sums_move_at_second_order; intro μ
  apply the_sums_move_at_second_order; intro ν
  apply the_sums_move_at_second_order; intro x
  obtain ⟨W, hW⟩ := the_square4_varies_along_one_direction U μ₀ x₀ X t μ ν x
  obtain ⟨c, hc⟩ := flat μ ν x
  refine ⟨the_turns_action W, ?_⟩
  rw [hW, the_turns_action_stops_at_second_order, hc, a_whole_turn_is_stationary, Int.mul_zero, Int.add_zero]
def the_swap_torus4 (n : Nat) : Torus4 n := fun _ _ => the_swap_turn
theorem the_swap_torus4_is_flat (n : Nat) (μ ν : Direction) (x : Site4 n) :
    ∃ c, the_square4 (the_swap_torus4 n) μ ν x = the_whole_turn c := ⟨1, rfl⟩
theorem the_four_directions_are_four : the_directions.length = 4 := rfl
#print axioms the_steps_commute
#print axioms every_four_torus_is_gauge_invariant
#print axioms a_flat_four_torus_is_stationary
#print axioms the_swap_torus4_is_flat
--| THE BOX OF EIGHT.  Lay the box of four over one more table, and let the quarter turn of that table be i.  It squares to
--| minus one and commutes with every gamma, so the phase it turns is inside the Dirac algebra and is not the time gamma.
--| Multiply each gamma by it and the metric turns over: one plus and three minus, the convention of the complex Dirac
--| matrices, each two still anticommuting, and i commutes with these too.  The i comes from the quaternions' quarter turn,
--| written on its own factor.  That this phase is the electron's charge is not written here.
abbrev Box8 := Bool → Bool → Bool → Bool → Bool → Bool → Int
def the_big_box (X : Box4) (A : Table) : Box8 := fun a b c d e f => X a b c d * A e f
def the_big_product (X Y : Box8) : Box8 := fun a b c d e f =>
  X a true c true e true * Y true b true d true f + X a true c true e false * Y true b true d false f
  + X a true c false e true * Y true b false d true f + X a true c false e false * Y true b false d false f
  + X a false c true e true * Y false b true d true f + X a false c true e false * Y false b true d false f
  + X a false c false e true * Y false b false d true f + X a false c false e false * Y false b false d false f
def the_big_anticommutator (X Y : Box8) : Box8 := fun a b c d e f => the_big_product X Y a b c d e f + the_big_product Y X a b c d e f
def the_big_bracket (X Y : Box8) : Box8 := fun a b c d e f => the_big_product X Y a b c d e f - the_big_product Y X a b c d e f
def the_big_identity : Box8 := the_big_box the_box_identity (the_scaled_identity 1)
def the_i : Box8 := the_big_box the_box_identity the_quarter_turn
def the_real_gamma (g : Box4) : Box8 := the_big_box g (the_scaled_identity 1)
def the_complex_gamma (g : Box4) : Box8 := the_big_box g the_quarter_turn
theorem the_i_squares_to_minus_one (a b c d e f : Bool) :
    the_big_product the_i the_i a b c d e f = - the_big_identity a b c d e f := by
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;> rfl
theorem the_i_commutes_with_every_gamma (a b c d e f : Bool) :
    (the_big_bracket the_i (the_real_gamma the_time_gamma) a b c d e f,
     the_big_bracket the_i (the_real_gamma the_first_gamma) a b c d e f,
     the_big_bracket the_i (the_real_gamma the_second_gamma) a b c d e f,
     the_big_bracket the_i (the_real_gamma the_third_gamma) a b c d e f) = (0, 0, 0, 0) := by
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;> rfl
theorem the_i_turns_the_metric_over (a b c d e f : Bool) :
    (the_big_product (the_complex_gamma the_time_gamma) (the_complex_gamma the_time_gamma) a b c d e f,
     the_big_product (the_complex_gamma the_first_gamma) (the_complex_gamma the_first_gamma) a b c d e f,
     the_big_product (the_complex_gamma the_second_gamma) (the_complex_gamma the_second_gamma) a b c d e f,
     the_big_product (the_complex_gamma the_third_gamma) (the_complex_gamma the_third_gamma) a b c d e f)
      = (the_big_identity a b c d e f, - the_big_identity a b c d e f, - the_big_identity a b c d e f,
         - the_big_identity a b c d e f) := by
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;> rfl
theorem the_turned_gammas_anticommute (a b c d e f : Bool) :
    (the_big_anticommutator (the_complex_gamma the_time_gamma) (the_complex_gamma the_first_gamma) a b c d e f,
     the_big_anticommutator (the_complex_gamma the_time_gamma) (the_complex_gamma the_second_gamma) a b c d e f,
     the_big_anticommutator (the_complex_gamma the_time_gamma) (the_complex_gamma the_third_gamma) a b c d e f,
     the_big_anticommutator (the_complex_gamma the_first_gamma) (the_complex_gamma the_second_gamma) a b c d e f,
     the_big_anticommutator (the_complex_gamma the_first_gamma) (the_complex_gamma the_third_gamma) a b c d e f,
     the_big_anticommutator (the_complex_gamma the_second_gamma) (the_complex_gamma the_third_gamma) a b c d e f)
      = (0, 0, 0, 0, 0, 0) := by
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;> rfl
theorem the_i_commutes_with_the_turned_gammas (a b c d e f : Bool) :
    (the_big_bracket the_i (the_complex_gamma the_time_gamma) a b c d e f,
     the_big_bracket the_i (the_complex_gamma the_first_gamma) a b c d e f,
     the_big_bracket the_i (the_complex_gamma the_second_gamma) a b c d e f,
     the_big_bracket the_i (the_complex_gamma the_third_gamma) a b c d e f) = (0, 0, 0, 0) := by
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;> rfl
theorem the_i_is_not_the_time_gamma : the_i true true true true true false ≠ the_complex_gamma the_time_gamma true true true true true false := by decide
#print axioms the_i_squares_to_minus_one
#print axioms the_i_commutes_with_every_gamma
#print axioms the_i_turns_the_metric_over
#print axioms the_turned_gammas_anticommute
#print axioms the_i_commutes_with_the_turned_gammas
#print axioms the_i_is_not_the_time_gamma
--| THE TRAIN LINE.  Put a spinor at every station, eight whole numbers on the box of eight, and a phase on every link, two
--| whole numbers read as x + y·i.  Read the spinor through the time gamma and turn it by i: the current of a direction is i
--| times the time gamma times that direction's gamma, and it is antisymmetric, so riding a link forward less riding it back
--| is the derivative.  Ride each link once, uptown: the spinor here against the current of the phase times the spinor there.
--| Read backward, downtown, with the conjugate phase, the link turns over: the line runs one way.  No station needs its
--| predecessor.  Turn every station by a phase of length one and carry each link from its start to its end: the phases
--| cancel at the far station, the current commutes with them, and the dot of two turned spinors is the length times the
--| dot.  The Dirac action, mass and hops, is gauge invariant on every torus.  The coupling that scales the phase is not
--| written here.  (An earlier line read each link both ways with the gamma alone; the dot kept only the gamma's symmetric
--| part, and the space hop was nothing.  The current is the repair.)
abbrev Vec8 := Bool → Bool → Bool → Int
def the_i_on (v : Vec8) : Vec8 := fun a c e => if e then - v a c false else v a c true
def the_phase_on (z : Int × Int) (v : Vec8) : Vec8 := fun a c e => z.1 * v a c e + z.2 * the_i_on v a c e
def the_gamma_on (g : Box4) (v : Vec8) : Vec8 := fun a c e =>
  g a true c true * v true true e + g a true c false * v true false e + g a false c true * v false true e + g a false c false * v false false e
def the_turned_gamma_on (g : Box4) (v : Vec8) : Vec8 := the_gamma_on g (the_i_on v)
def the_dot (v w : Vec8) : Int :=
  v true true true * w true true true + v true true false * w true true false + v true false true * w true false true
  + v true false false * w true false false + v false true true * w false true true + v false true false * w false true false
  + v false false true * w false false true + v false false false * w false false false
def the_phase_product (z w : Int × Int) : Int × Int := (z.1 * w.1 - z.2 * w.2, z.1 * w.2 + z.2 * w.1)
def the_phase_conjugate (z : Int × Int) : Int × Int := (z.1, -z.2)
def the_phase_norm (z : Int × Int) : Int := z.1 * z.1 + z.2 * z.2
theorem the_turned_gamma_is_the_complex_gamma (g : Box4) (v : Vec8) (a c e : Bool) :
    the_turned_gamma_on g v a c e
      = the_complex_gamma g a true c true e true * v true true true + the_complex_gamma g a true c true e false * v true true false
        + the_complex_gamma g a true c false e true * v true false true + the_complex_gamma g a true c false e false * v true false false
        + the_complex_gamma g a false c true e true * v false true true + the_complex_gamma g a false c true e false * v false true false
        + the_complex_gamma g a false c false e true * v false false true + the_complex_gamma g a false c false e false * v false false false := by
  cases e <;> simp only [the_turned_gamma_on, the_gamma_on, the_i_on, the_complex_gamma, the_big_box, the_quarter_turn,
    ite_true, ite_false, Bool.true_eq_false, Bool.false_eq_true, Int.mul_zero, Int.mul_one, Int.mul_neg,
    Int.neg_mul] <;> omega
theorem the_phases_compose (z w : Int × Int) (v : Vec8) :
    the_phase_on z (the_phase_on w v) = the_phase_on (the_phase_product z w) v := by
  funext a c e
  cases e <;> simp only [the_phase_on, the_i_on, the_phase_product, ite_true, ite_false, Bool.false_eq_true,
    Int.mul_add, Int.add_mul, Int.mul_neg, Int.neg_add, Int.sub_mul] <;> ac_nf <;> omega
theorem the_gamma_commutes_with_the_phase (g : Box4) (z : Int × Int) (v : Vec8) :
    the_turned_gamma_on g (the_phase_on z v) = the_phase_on z (the_turned_gamma_on g v) := by
  funext a c e
  cases e <;> simp only [the_turned_gamma_on, the_gamma_on, the_phase_on, the_i_on, ite_true, ite_false,
    Bool.false_eq_true, Int.mul_add, Int.mul_neg, Int.neg_add] <;> ac_nf <;> omega
theorem the_dot_of_two_phases (z : Int × Int) (v w : Vec8) :
    the_dot (the_phase_on z v) (the_phase_on z w) = the_phase_norm z * the_dot v w := by
  simp only [the_dot, the_phase_on, the_i_on, the_phase_norm, ite_true, ite_false, Bool.false_eq_true,
    Int.mul_add, Int.add_mul, Int.mul_neg, Int.neg_mul]
  ac_nf; omega
theorem the_conjugate_cancels (x b : Int × Int) :
    the_phase_product (the_phase_product x (the_phase_conjugate b)) b = (x.1 * the_phase_norm b, x.2 * the_phase_norm b) := by
  simp only [the_phase_product, the_phase_conjugate, the_phase_norm, Prod.mk.injEq, Int.mul_add, Int.add_mul, Int.sub_mul,
    Int.mul_neg, Int.neg_mul]
  constructor <;> ac_nf <;> omega
theorem the_carried_phase (a U b : Int × Int) (w : Vec8) (hb : the_phase_norm b = 1) :
    the_phase_on (the_phase_product (the_phase_product a U) (the_phase_conjugate b)) (the_phase_on b w)
      = the_phase_on a (the_phase_on U w) := by
  rw [the_phases_compose, the_phases_compose, the_conjugate_cancels, hb, Int.mul_one, Int.mul_one]
theorem the_conjugate_of_a_carried_link (a U b : Int × Int) :
    the_phase_conjugate (the_phase_product (the_phase_product a U) (the_phase_conjugate b))
      = the_phase_product (the_phase_product b (the_phase_conjugate U)) (the_phase_conjugate a) := by
  simp only [the_phase_product, the_phase_conjugate, Prod.mk.injEq, Int.add_mul, Int.sub_mul,
    Int.mul_neg, Int.neg_mul, Int.neg_neg, Int.neg_add, Int.neg_sub]
  constructor <;> ac_nf <;> omega
def the_current_on (g : Box4) (v : Vec8) : Vec8 := the_i_on (the_turned_gamma_on the_time_gamma (the_turned_gamma_on g v))
def the_hop (v : Vec8) (U : Int × Int) (w : Vec8) (g : Box4) : Int := the_dot v (the_current_on g (the_phase_on U w))
theorem the_i_is_a_phase (v : Vec8) : the_i_on v = the_phase_on (0, 1) v := by
  funext a c e; cases e <;> simp only [the_phase_on, the_i_on, ite_true, ite_false, Bool.false_eq_true] <;> omega
theorem the_current_commutes_with_the_phase (g : Box4) (z : Int × Int) (v : Vec8) :
    the_current_on g (the_phase_on z v) = the_phase_on z (the_current_on g v) := by
  simp only [the_current_on, the_gamma_commutes_with_the_phase, the_i_is_a_phase, the_phases_compose]
  congr 1; simp only [the_phase_product, Int.zero_mul, Int.one_mul, Int.mul_zero, Int.mul_one, Int.zero_sub,
    Int.zero_add, Int.add_zero]
theorem the_phase_moves_across_the_dot (U : Int × Int) (x y : Vec8) :
    the_dot x (the_phase_on (the_phase_conjugate U) y) = the_dot (the_phase_on U x) y := by
  simp only [the_dot, the_phase_on, the_phase_conjugate, the_i_on, ite_true, ite_false, Bool.false_eq_true,
    Int.mul_add, Int.add_mul, Int.mul_neg, Int.neg_mul]
  ac_nf; omega
theorem the_time_current_is_antisymmetric (v w : Vec8) :
    the_dot v (the_current_on the_time_gamma w) = - the_dot w (the_current_on the_time_gamma v) := by
  simp only [the_dot, the_current_on, the_turned_gamma_on, the_gamma_on, the_i_on, the_time_gamma, the_turn_of_the_quarter,
    the_box, the_quarter_turn, the_scaled_identity, ite_true, ite_false, Bool.false_eq_true, Bool.true_eq_false]
  simp only [Int.zero_mul, Int.mul_zero, Int.one_mul, Int.mul_one, Int.neg_mul, Int.mul_neg, Int.neg_neg, Int.add_zero,
    Int.zero_add, Int.neg_zero, Int.neg_add]
  ac_nf
theorem the_space_current_is_antisymmetric (v w : Vec8) :
    the_dot v (the_current_on the_first_gamma w) = - the_dot w (the_current_on the_first_gamma v) := by
  simp only [the_dot, the_current_on, the_turned_gamma_on, the_gamma_on, the_i_on, the_time_gamma, the_first_gamma,
    the_turn_of_the_quarter, the_box, the_quarter_turn, the_swap, the_scaled_identity, ite_true, ite_false, Bool.false_eq_true,
    Bool.true_eq_false]
  simp only [Int.zero_mul, Int.mul_zero, Int.one_mul, Int.mul_one, Int.neg_mul, Int.mul_neg, Int.neg_neg, Int.add_zero,
    Int.zero_add, Int.neg_zero, Int.neg_add]
  ac_nf
theorem the_link_read_backward_turns_over (v w : Vec8) (U : Int × Int) (g : Box4)
    (anti : ∀ x y, the_dot x (the_current_on g y) = - the_dot y (the_current_on g x)) :
    the_hop w (the_phase_conjugate U) v g = - the_hop v U w g := by
  simp only [the_hop]
  rw [the_current_commutes_with_the_phase, the_phase_moves_across_the_dot, anti]
theorem the_gauged_hop (v w : Vec8) (U gs gn : Int × Int) (g : Box4)
    (hs : the_phase_norm gs = 1) (hn : the_phase_norm gn = 1) :
    the_hop (the_phase_on gs v) (the_phase_product (the_phase_product gs U) (the_phase_conjugate gn)) (the_phase_on gn w) g
      = the_hop v U w g := by
  simp only [the_hop]
  rw [the_carried_phase _ _ _ _ hn, the_current_commutes_with_the_phase, the_dot_of_two_phases, hs, Int.one_mul]
def the_dirac_action {n : Nat} (U : Bool → Fin (n+1) → Fin (n+1) → Int × Int) (ψ : Fin (n+1) → Fin (n+1) → Vec8) (m : Int) : Int :=
  the_sum ((List.finRange (n+1)).map fun i => the_sum ((List.finRange (n+1)).map fun j =>
    m * the_dot (ψ i j) (ψ i j) + the_hop (ψ i j) (U false i j) (ψ (i+1) j) the_time_gamma
      + the_hop (ψ i j) (U true i j) (ψ i (j+1)) the_first_gamma))
def the_gauged_links {n : Nat} (U : Bool → Fin (n+1) → Fin (n+1) → Int × Int) (g : Fin (n+1) → Fin (n+1) → Int × Int) :
    Bool → Fin (n+1) → Fin (n+1) → Int × Int := fun d i j =>
  the_phase_product (the_phase_product (g i j) (U d i j)) (the_phase_conjugate (if d then g i (j+1) else g (i+1) j))
def the_gauged_spinors {n : Nat} (ψ : Fin (n+1) → Fin (n+1) → Vec8) (g : Fin (n+1) → Fin (n+1) → Int × Int) :
    Fin (n+1) → Fin (n+1) → Vec8 := fun i j => the_phase_on (g i j) (ψ i j)
theorem the_dirac_action_is_gauge_invariant {n : Nat} (U : Bool → Fin (n+1) → Fin (n+1) → Int × Int)
    (ψ : Fin (n+1) → Fin (n+1) → Vec8) (m : Int) (g : Fin (n+1) → Fin (n+1) → Int × Int) (unit : ∀ i j, the_phase_norm (g i j) = 1) :
    the_dirac_action (the_gauged_links U g) (the_gauged_spinors ψ g) m = the_dirac_action U ψ m := by
  simp only [the_dirac_action, the_gauged_links, the_gauged_spinors, if_true, if_false, Bool.false_eq_true,
    the_gauged_hop _ _ _ _ _ _ (unit _ _) (unit _ _), the_dot_of_two_phases, unit, Int.one_mul]
#print axioms the_turned_gamma_is_the_complex_gamma
#print axioms the_phases_compose
#print axioms the_gamma_commutes_with_the_phase
#print axioms the_dot_of_two_phases
#print axioms the_gauged_hop
#print axioms the_current_commutes_with_the_phase
#print axioms the_time_current_is_antisymmetric
#print axioms the_space_current_is_antisymmetric
#print axioms the_link_read_backward_turns_over
#print axioms the_dirac_action_is_gauge_invariant
--| THE WHOLE ACTION.  A phase is a turn with one imaginary part: written as a turn, its products and conjugates are the turns'
--| own, and its length is the turn's length.  So the phases on the links are a torus of turns, and a square of phases reads
--| the square of its turned part.  Weigh the squares by a whole number β and add the train line: the whole action of light and
--| matter on the torus, and it is gauge invariant under a phase of length one at every station, at every size.  β is left
--| free.  What it is, one over the square of the coupling, and that the device's reading fixes it, is not written here.
def the_phase_as_turns (z : Int × Int) : Turns := (z.1, 0, z.2, 0)
theorem the_phase_product_is_the_turns_product (z w : Int × Int) :
    the_phase_as_turns (the_phase_product z w) = the_turns_product (the_phase_as_turns z) (the_phase_as_turns w) := by
  simp only [the_phase_as_turns, the_phase_product, the_turns_product, Int.mul_zero, Int.zero_mul, Int.sub_zero,
    Int.add_zero]
theorem the_phase_conjugate_is_the_turns_conjugate (z : Int × Int) :
    the_phase_as_turns (the_phase_conjugate z) = the_turns_conjugate (the_phase_as_turns z) := by
  simp only [the_phase_as_turns, the_phase_conjugate, the_turns_conjugate, Int.neg_zero]
theorem the_phase_norm_is_the_turns_norm (z : Int × Int) :
    the_turns_norm (the_phase_as_turns z) = the_phase_norm z := by
  simp only [the_turns_norm, the_phase_as_turns, the_phase_norm, Int.mul_zero, Int.add_zero]
def the_phase_torus {n : Nat} (U : Bool → Fin (n+1) → Fin (n+1) → Int × Int) : Torus n :=
  fun d i j => the_phase_as_turns (U d i j)
theorem the_phase_torus_of_the_gauged_links {n : Nat} (U : Bool → Fin (n+1) → Fin (n+1) → Int × Int)
    (g : Fin (n+1) → Fin (n+1) → Int × Int) :
    the_phase_torus (the_gauged_links U g) = the_gauged_torus (the_phase_torus U) (fun i j => the_phase_as_turns (g i j)) := by
  funext d i j
  cases d <;> simp only [the_phase_torus, the_gauged_links, the_gauged_torus, the_phase_product_is_the_turns_product,
    the_phase_conjugate_is_the_turns_conjugate, if_true, if_false, Bool.false_eq_true]
def the_whole_action {n : Nat} (β : Int) (U : Bool → Fin (n+1) → Fin (n+1) → Int × Int) (ψ : Fin (n+1) → Fin (n+1) → Vec8)
    (m : Int) : Int :=
  β * the_torus_action (the_phase_torus U) + the_dirac_action U ψ m
theorem the_whole_action_is_gauge_invariant {n : Nat} (β : Int) (U : Bool → Fin (n+1) → Fin (n+1) → Int × Int)
    (ψ : Fin (n+1) → Fin (n+1) → Vec8) (m : Int) (g : Fin (n+1) → Fin (n+1) → Int × Int)
    (unit : ∀ i j, the_phase_norm (g i j) = 1) :
    the_whole_action β (the_gauged_links U g) (the_gauged_spinors ψ g) m = the_whole_action β U ψ m := by
  have unit' : ∀ i j, the_turns_norm (the_phase_as_turns (g i j)) = 1 := fun i j => by
    rw [the_phase_norm_is_the_turns_norm]; exact unit i j
  simp only [the_whole_action, the_phase_torus_of_the_gauged_links, every_torus_is_gauge_invariant _ _ unit',
    the_dirac_action_is_gauge_invariant U ψ m g unit]
theorem the_square_of_a_phase_reads_its_turned_part (z : Int × Int) :
    the_turns_action (the_phase_as_turns z) = z.2 * z.2 := by
  simp only [the_turns_action, the_phase_as_turns, Int.mul_zero, Int.zero_add, Int.add_zero]
#print axioms the_phase_product_is_the_turns_product
#print axioms the_phase_torus_of_the_gauged_links
#print axioms the_whole_action_is_gauge_invariant
#print axioms the_square_of_a_phase_reads_its_turned_part
--| THE DOUBLERS.  Ride a circle of stations with every phase one.  On two stations the line cannot tell uptown from downtown:
--| each link is ridden both ways and turns over, and the line reads nothing for every spinor.  On four, the line's response
--| to any probe is blind to two fields: the field that is the same at every station, and the field that alternates, plus,
--| minus, plus, minus, at every step.  A field that turns a quarter per station is seen.  Two tastes for one line, the one
--| that keeps still and the one that keeps time.  Which taste is the electron's is not written here.
theorem the_phase_one_is_nothing (v : Vec8) : the_phase_on (1, 0) v = v := by
  funext a c e; simp only [the_phase_on, Int.one_mul, Int.zero_mul, Int.add_zero]
def the_line {n : Nat} (ψ : Fin (n+1) → Vec8) (g : Box4) : Int :=
  the_sum ((List.finRange (n+1)).map fun s => the_hop (ψ s) (1, 0) (ψ (s+1)) g)
def the_line_response {n : Nat} (ψ φ : Fin (n+1) → Vec8) (g : Box4) : Int :=
  the_sum ((List.finRange (n+1)).map fun s => the_hop (ψ s) (1, 0) (φ (s+1)) g + the_hop (φ s) (1, 0) (ψ (s+1)) g)
def the_neg (v : Vec8) : Vec8 := fun a c e => - v a c e
theorem two_stations_cannot_tell_uptown_from_downtown (ψ : Fin 2 → Vec8) (g : Box4)
    (anti : ∀ x y, the_dot x (the_current_on g y) = - the_dot y (the_current_on g x)) :
    the_line ψ g = 0 := by
  have h := anti (ψ 0) (ψ 1)
  simp only [the_line]
  rw [show List.finRange 2 = [0, 1] from rfl]
  simp only [List.map_cons, List.map_nil, the_sum, the_hop, the_phase_one_is_nothing]
  have e0 : (0 : Fin 2) + 1 = 1 := rfl
  have e1 : (1 : Fin 2) + 1 = 0 := rfl
  rw [e0, e1]; omega
theorem the_constant_field_is_a_doubler (χ : Vec8) (φ : Fin 4 → Vec8) (g : Box4)
    (anti : ∀ x y, the_dot x (the_current_on g y) = - the_dot y (the_current_on g x)) :
    the_line_response (fun _ => χ) φ g = 0 := by
  simp only [the_line_response]
  rw [show List.finRange 4 = [0, 1, 2, 3] from rfl]
  simp only [List.map_cons, List.map_nil, the_sum, the_hop, the_phase_one_is_nothing]
  have e0 : (0 : Fin 4) + 1 = 1 := rfl
  have e1 : (1 : Fin 4) + 1 = 2 := rfl
  have e2 : (2 : Fin 4) + 1 = 3 := rfl
  have e3 : (3 : Fin 4) + 1 = 0 := rfl
  rw [e0, e1, e2, e3, anti (φ 0) χ, anti (φ 1) χ, anti (φ 2) χ, anti (φ 3) χ]
  omega
theorem the_neg_is_a_phase (v : Vec8) : the_neg v = the_phase_on (-1, 0) v := by
  funext a c e; simp only [the_neg, the_phase_on, Int.zero_mul, Int.add_zero]; omega
theorem the_dot_of_a_neg (x y : Vec8) : the_dot (the_neg x) y = - the_dot x y := by
  simp only [the_dot, the_neg, Int.neg_mul]; omega
theorem the_dot_against_a_neg (x y : Vec8) : the_dot x (the_neg y) = - the_dot x y := by
  simp only [the_dot, the_neg, Int.mul_neg]; omega
theorem the_current_of_a_neg (g : Box4) (v : Vec8) : the_current_on g (the_neg v) = the_neg (the_current_on g v) := by
  rw [the_neg_is_a_phase, the_neg_is_a_phase, the_current_commutes_with_the_phase]
def the_alternating_field (χ : Vec8) : Fin 4 → Vec8 := fun s => if s.val % 2 = 0 then χ else the_neg χ
theorem the_alternating_field_is_a_doubler (χ : Vec8) (φ : Fin 4 → Vec8) (g : Box4)
    (anti : ∀ x y, the_dot x (the_current_on g y) = - the_dot y (the_current_on g x)) :
    the_line_response (the_alternating_field χ) φ g = 0 := by
  simp only [the_line_response]
  rw [show List.finRange 4 = [0, 1, 2, 3] from rfl]
  simp only [List.map_cons, List.map_nil, the_sum, the_hop, the_phase_one_is_nothing]
  have e0 : (0 : Fin 4) + 1 = 1 := rfl
  have e1 : (1 : Fin 4) + 1 = 2 := rfl
  have e2 : (2 : Fin 4) + 1 = 3 := rfl
  have e3 : (3 : Fin 4) + 1 = 0 := rfl
  have a0 : the_alternating_field χ 0 = χ := rfl
  have a1 : the_alternating_field χ 1 = the_neg χ := rfl
  have a2 : the_alternating_field χ 2 = χ := rfl
  have a3 : the_alternating_field χ 3 = the_neg χ := rfl
  rw [e0, e1, e2, e3, a0, a1, a2, a3]
  simp only [the_dot_of_a_neg, the_current_of_a_neg, the_dot_against_a_neg]
  rw [anti (φ 0) χ, anti (φ 1) χ, anti (φ 2) χ, anti (φ 3) χ]
  omega
def the_probe_here : Vec8 := fun a c e => (if a then 3 else 1) + (if c then 5 else 2) * (if e then 7 else -1)
def the_probe_there : Vec8 := fun a c e => (if a then -2 else 4) + (if c then 1 else 6) * (if e then 2 else 3)
def the_quarter_field : Fin 4 → Vec8 := fun s =>
  if s.val = 0 then the_probe_here else if s.val = 1 then the_probe_there else if s.val = 2 then the_neg the_probe_here
  else the_neg the_probe_there
theorem the_quarter_field_is_seen : the_line the_quarter_field the_first_gamma ≠ 0 := by decide
#print axioms two_stations_cannot_tell_uptown_from_downtown
#print axioms the_constant_field_is_a_doubler
#print axioms the_alternating_field_is_a_doubler
#print axioms the_quarter_field_is_seen
--| WHAT IS LEFT, CLOSED.  The torus with one link turned is not a second solution: vary that link along the quarter turn and
--| the action reads eight one way and nothing the other, so it leans, and no whole number makes it stand still at three.  The
--| gauge needs links of length one, and the device has them: the three turns are each of length one, and turning every site
--| of any torus by the turn of the swap leaves its action alone.  No normalization is handed in.
theorem the_turned_lattice_is_not_stationary :
    ¬ (∀ t : Int, ∃ q, the_turns_lattice_action (the_varied_turns_lattice the_turned_turns_lattice false false false (0, 0, 1, 0) t)
        = the_turns_lattice_action the_turned_turns_lattice + t * t * q) := by
  intro h
  obtain ⟨q, hq⟩ := h 3
  have h3 : the_turns_lattice_action (the_varied_turns_lattice the_turned_turns_lattice false false false (0, 0, 1, 0) 3) = 32 := by decide
  rw [h3, the_turned_turns_lattice_has_action] at hq
  omega
theorem the_turned_lattice_leans_one_way :
    (the_turns_lattice_action (the_varied_turns_lattice the_turned_turns_lattice false false false (0, 0, 1, 0) 1),
     the_turns_lattice_action (the_varied_turns_lattice the_turned_turns_lattice false false false (0, 0, 1, 0) (-1))) = (8, 0) := by decide
theorem the_three_turns_have_length_one :
    (the_turns_norm (0, 1, 0, 0), the_turns_norm (0, 0, 1, 0), the_turns_norm (0, 0, 0, 1)) = (1, 1, 1) := rfl
theorem the_device_supplies_its_own_gauge {n : Nat} (U : Torus n) :
    the_torus_action (the_gauged_torus U (fun _ _ => the_swap_turn)) = the_torus_action U :=
  every_torus_is_gauge_invariant U _ (fun _ _ => rfl)
#print axioms the_turned_lattice_is_not_stationary
#print axioms the_turned_lattice_leans_one_way
#print axioms the_three_turns_have_length_one
#print axioms the_device_supplies_its_own_gauge
--| TWO WAYS THE CLOCK CANCELS.  The clock's irrational part is the square root of its round trip, ninety.  Any table whose
--| round trip is ninety has the same clock squared, so against the device's table the two clocks cancel and the difference
--| of the growth rates is the difference of the clicks, whole -- the swapped table, clicks five and outlier eighteen, among
--| them.  And the table cancels its own clock against its other root: the two roots add to the trace and multiply to the
--| determinant, thirty-six and two hundred thirty-four, both whole.  The second is the doubler.  Both, of course.
def the_clock_of (b f : Int) : Table := fun x y => if x = y then 0 else if x then f else b
theorem the_device_clock_is_the_clock_of : ∀ x y, the_clock_table x y = the_clock_of 18 5 x y := by
  intro x y; cases x <;> cases y <;> rfl
theorem the_same_round_trip_is_the_same_clock (b f : Int) (h : b * f = 90) (x y : Bool) :
    the_table_product (the_clock_of b f) (the_clock_of b f) x y = the_table_product the_clock_table the_clock_table x y := by
  have e : f * b = 90 := by rw [Int.mul_comm]; exact h
  cases x <;> cases y <;> simp only [the_table_product, the_clock_of, the_clock_table, Bool.true_eq_false, Bool.false_eq_true,
    ite_true, ite_false, Int.mul_zero, Int.zero_mul, Int.add_zero, Int.zero_add, h, e] <;> rfl
theorem the_swapped_table_shares_the_clock (x y : Bool) :
    the_table_product (the_clock_of 5 18) (the_clock_of 5 18) x y = the_table_product the_clock_table the_clock_table x y :=
  the_same_round_trip_is_the_same_clock 5 18 rfl x y
theorem the_conjugate_roots_are_rational :
    (the_table_trace the_full_table, the_table_determinant the_full_table) = (36, 234) := rfl
#print axioms the_same_round_trip_is_the_same_clock
#print axioms the_swapped_table_shares_the_clock
#print axioms the_conjugate_roots_are_rational
--| THE TORUS AND THE BOOST.  Read the table as a torus: the major radius is the clicks, eighteen; the tube's radius is the
--| clock, the square root of the round trip.  The outer equator is the larger root and the hole is the smaller; they add to
--| the trace and multiply to the determinant, which is the interval, eighteen squared less the round trip.  Fatten the tube to
--| the major radius and the hole closes at the origin -- the speed of light, which the clock never reaches.  A boost keeps
--| away from it: nineteen and two, whose interval is one, multiplies the torus without changing its interval, so the hole
--| shrinks and never shuts.  Written with the round trip as the square of the surd, in whole numbers, no root taken.
def the_round_trip : Int := (the_arm_weight true false : Int) * (the_arm_weight false true : Int)
def the_surd_product (p q : Int × Int) : Int × Int :=
  (p.1 * q.1 + the_round_trip * p.2 * q.2, p.1 * q.2 + p.2 * q.1)
def the_interval (p : Int × Int) : Int := p.1 * p.1 - the_round_trip * p.2 * p.2
def the_outer_radius : Int × Int := (18, 1)
def the_hole : Int × Int := (18, -1)
def the_boost : Int × Int := (19, 2)
theorem the_round_trip_is_ninety : the_round_trip = 90 := rfl
theorem the_outer_and_the_hole :
    (the_outer_radius.1 + the_hole.1, the_outer_radius.2 + the_hole.2) = (36, 0)
      ∧ the_surd_product the_outer_radius the_hole = (234, 0) := by decide
theorem the_interval_is_the_determinant :
    the_interval the_outer_radius = the_table_determinant the_full_table := rfl
theorem the_boost_has_unit_interval : the_interval the_boost = 1 := by decide
theorem the_boost_preserves_the_interval (p : Int × Int) :
    the_interval (the_surd_product p the_boost) = the_interval p := by
  have r : the_round_trip = 90 := rfl
  simp only [the_interval, the_surd_product, the_boost, r, Int.add_mul, Int.mul_add]
  ac_nf; omega
theorem the_hole_stays_open (p : Int × Int) (h : the_interval p = 234) :
    the_round_trip * p.2 * p.2 < p.1 * p.1 := by
  unfold the_interval at h; omega
theorem the_boosted_torus :
    the_surd_product the_outer_radius the_boost = (522, 55) ∧ the_interval (522, 55) = 234 := by decide
#print axioms the_outer_and_the_hole
#print axioms the_boost_preserves_the_interval
#print axioms the_hole_stays_open
#print axioms the_boosted_torus
--| THE SECOND VARIATION ON THE SEAM.  Put a phase on each of the thirty-six cells.  Its first variation is the step across
--| each edge, taken after the cell and before it; its second variation, the seam's thirty-six by thirty-six Laplacian, is the
--| step before less the step after, in each direction -- two first variations, one before and one after, fix the second.  And
--| its frequencies are whole: the plane waves of sixths of a turn, written in whole numbers, are thirty-six independent
--| eigenvectors, and each one's frequency is a whole number from nought to eight.  The FFT of the seam, no cosine taken.
def the_step_after (f : Nat → Nat → Int) (x y : Nat) : Int × Int :=
  (f ((x + 1) % 6) y - f x y, f x ((y + 1) % 6) - f x y)
def the_step_before (f : Nat → Nat → Int) (x y : Nat) : Int × Int :=
  (f x y - f ((x + 5) % 6) y, f x y - f x ((y + 5) % 6))
def the_seam_laplacian (f : Nat → Nat → Int) (x y : Nat) : Int :=
  4 * f x y - f ((x + 1) % 6) y - f ((x + 5) % 6) y - f x ((y + 1) % 6) - f x ((y + 5) % 6)
theorem the_second_variation_is_before_less_after (f : Nat → Nat → Int) (x y : Nat) :
    the_seam_laplacian f x y
      = ((the_step_before f x y).1 - (the_step_after f x y).1) + ((the_step_before f x y).2 - (the_step_after f x y).2) := by
  simp only [the_seam_laplacian, the_step_before, the_step_after]; omega
def the_sixths : List (List Int) :=
  [[2, 2, 2, 2, 2, 2], [2, 1, -1, -2, -1, 1], [0, 1, 1, 0, -1, -1],
   [2, -1, -1, 2, -1, -1], [0, 1, -1, 0, 1, -1], [2, -2, 2, -2, 2, -2]]
def the_frequency : List Int := [0, 1, 1, 3, 3, 4]
def the_mode (a : Nat) (x : Nat) : Int := (the_sixths.getD a []).getD (x % 6) 0
def the_plane_wave (a b : Nat) : Nat → Nat → Int := fun x y => the_mode a x * the_mode b y
theorem the_plane_waves_are_the_frequencies :
    ∀ a < 6, ∀ b < 6, ∀ x < 6, ∀ y < 6,
      the_seam_laplacian (the_plane_wave a b) x y
        = (the_frequency.getD a 0 + the_frequency.getD b 0) * the_plane_wave a b x y := by decide
def the_overlap (a b c d : Nat) : Int :=
  ((List.range 36).map fun i => the_plane_wave a b (i % 6) (i / 6) * the_plane_wave c d (i % 6) (i / 6)).foldl (· + ·) 0
theorem the_plane_waves_are_independent :
    ∀ a < 6, ∀ b < 6, ∀ c < 6, ∀ d < 6, (a = c ∧ b = d) ∨ the_overlap a b c d = 0 := by decide
#print axioms the_plane_waves_are_independent
#print axioms the_second_variation_is_before_less_after
#print axioms the_plane_waves_are_the_frequencies
--| WHERE THE UNDESCRIBABLE DIGITS COME IN.  Strike the arm and the reading is the clicks alone, eighteen times the gain: a
--| fraction, and its digits after the first settle into six that repeat forever, two three oh seven six nine -- a finite
--| record describes every one of them.  Write the arm and the clock comes in as the square root of five times eighteen, and
--| five times eighteen is no square, so the reading is no fraction and its digits never settle into any pattern.  Every digit
--| no finite pattern writes comes in with the five.
def the_struck_numerator : Nat := 18 * 324
def the_struck_denominator : Nat := 5 * 13
def the_struck_remainder (k : Nat) : Nat := the_struck_numerator * 10 ^ k % the_struck_denominator
def the_struck_digit (k : Nat) : Nat := the_struck_numerator * 10 ^ k / the_struck_denominator % 10
theorem the_struck_reading_is_a_fraction :
    (the_struck_numerator, the_struck_denominator) = (5832, 65) := rfl
theorem the_struck_digits_repeat_every_six :
    ∀ k < 36, the_struck_remainder (k + 7) = the_struck_remainder (k + 1)
      ∧ the_struck_digit (k + 8) = the_struck_digit (k + 2) := by decide
theorem the_struck_digits_are_two_three_oh_seven_six_nine :
    (List.range 6).map (fun k => the_struck_digit (k + 2)) = [2, 3, 0, 7, 6, 9] := by decide
theorem the_round_trip_is_not_a_square (n : Nat) : n * n ≠ 5 * 18 := by
  rcases Nat.lt_or_ge n 10 with h | h
  · have : ∀ m < 10, m * m ≠ 90 := by decide
    exact this n h
  · have := Nat.mul_le_mul h h; omega
#print axioms the_struck_digits_repeat_every_six
#print axioms the_struck_digits_are_two_three_oh_seven_six_nine
#print axioms the_round_trip_is_not_a_square

--| TWO READINGS OF ONE TURNING.  Read a walk's crossings two ways.  Subdivided, every crossing is half a turn and the
--| count is the crossings themselves: nothing is left over, because nothing is rounded.  Counted in whole turns, the walk
--| winds `the_winding k` and leaves a residue, k % 2, the half turn no whole count can hold.  The two readings agree up to
--| that residue, always.  A closed walk is exact: it crosses evenly, the residue is zero, and the whole count is the
--| subdivided count halved -- one number read twice.  A walk between the coins is never exact: it leaves half a turn.
--| Whole turns start at zero and each full turn is one more, the successor; two exact walks joined wind the sum of their
--| windings, which is Stokes on a graph: the count around the boundary is the sum of the counts of its parts.  Where the
--| walk is exact, the agreement is rfl.
def the_residue (crossings : Nat) : Nat := crossings % 2

theorem the_two_readings (k : Nat) : k = 2 * the_winding k + the_residue k := by
  unfold the_winding the_residue; omega

theorem every_closed_walk_is_exact (n k : Nat) (a : Bool) (walked : the_crossings n a a k ≠ 0) :
    the_residue k = 0 ∧ k = 2 * the_winding k := by
  unfold the_residue the_winding
  rcases Nat.mod_two_eq_zero_or_one k with h | h
  · refine ⟨h, ?_⟩; clear walked; omega
  · exact absurd (every_closed_walk_crosses_evenly n k a h) walked

theorem every_walk_between_the_coins_leaves_half_a_turn (n k : Nat) (a : Bool) (walked : the_crossings n a (!a) k ≠ 0) :
    the_residue k = 1 := by
  unfold the_residue
  rcases Nat.mod_two_eq_zero_or_one k with h | h
  · exact absurd (the_crossings_keep_parity n a (!a) k (by cases a <;> simp [h])) walked
  · exact h

theorem the_winding_starts_at_zero : the_winding 0 = 0 := rfl

theorem one_more_turn_is_the_successor (k : Nat) : the_winding (k + 2) = the_winding k + 1 := by
  unfold the_winding; omega

theorem the_windings_add (j k : Nat) (hj : the_residue j = 0) (hk : the_residue k = 0) :
    the_winding (j + k) = the_winding j + the_winding k := by
  unfold the_winding; unfold the_residue at hj hk; omega

theorem once_around_is_exact : (2 * the_winding 2, the_residue 2) = (2, 0) := rfl
#print axioms the_two_readings
#print axioms every_closed_walk_is_exact
#print axioms every_walk_between_the_coins_leaves_half_a_turn
#print axioms the_windings_add
#print axioms once_around_is_exact

--| THE CARRIER, APPARENTLY.  Three finite readings, each one evaluated, and no limit taken: the limit is the argument's,
--| never this file's.
--| First, the readings fix the table up to gauge.  Rescale the coin T by a and the coin F by b, and the arm from T to F is
--| multiplied by a/b, the arm back by b/a, and every closed walk is unchanged: that rescaling is a gauge, and the squeeze
--| between the orientations was one.  Keep the agreeing arms at eighteen and read any table twice around: equal readings
--| leave only a gauge between the tables.  The other orientation, five and eighteen exchanged, is a gauge copy of this one.
def the_walks_on (w : Bool → Bool → Nat) : Nat → Bool → Bool → Nat
  | 0,     a, b => if a = b then 1 else 0
  | n + 1, a, b => w a true * the_walks_on w n true b + w a false * the_walks_on w n false b
def the_closed_walks_on (w : Bool → Bool → Nat) (n : Nat) : Nat := the_walks_on w n true true + the_walks_on w n false false

theorem the_device_walks_on_its_table : ∀ (n : Nat) (a b : Bool), the_walks_on the_arm_weight n a b = the_walks n a b
  | 0, _, _ => rfl
  | n + 1, a, b => by simp only [the_walks_on, the_walks, the_device_walks_on_its_table n]

theorem the_closed_walks_twice_around (w : Bool → Bool → Nat) :
    the_closed_walks_on w 2 = w true true * w true true + w false false * w false false + 2 * (w true false * w false true) := by
  simp only [the_closed_walks_on, the_walks_on, if_pos, Bool.true_eq_false, Bool.false_eq_true, ite_false, Nat.mul_one,
    Nat.mul_zero, Nat.add_zero, Nat.zero_add]
  rw [Nat.mul_comm (w false true) (w true false)]; omega

theorem the_readings_fix_the_gauge (w v : Bool → Bool → Nat)
    (dw : w true true = 18 ∧ w false false = 18) (dv : v true true = 18 ∧ v false false = 18)
    (pw : 0 < w true false) (pv : 0 < v true false) (same : the_closed_walks_on v 2 = the_closed_walks_on w 2) :
    ∃ a b : Nat, 0 < a ∧ 0 < b ∧ b * v true false = a * w true false ∧ a * v false true = b * w false true := by
  rw [the_closed_walks_twice_around, the_closed_walks_twice_around, dw.1, dw.2, dv.1, dv.2] at same
  refine ⟨v true false, w true false, pv, pw, Nat.mul_comm _ _, ?_⟩
  generalize v true false * v false true = p at same ⊢
  generalize w true false * w false true = q at same ⊢
  omega

theorem the_other_orientation_is_a_gauge_copy :
    ∃ a b : Nat, 0 < a ∧ 0 < b ∧ b * the_arm_weight false true = a * the_arm_weight true false
      ∧ a * the_arm_weight true false = b * the_arm_weight false true :=
  the_readings_fix_the_gauge the_arm_weight (fun a b => the_arm_weight b a) ⟨rfl, rfl⟩ ⟨rfl, rfl⟩ (by decide) (by decide)
    (by decide)

--| Second, the seam carries curvature, and its charge is whole.  Lay a turning on every edge of the seam -- A across, B up,
--| counted in half turns -- and the curl of each of the thirty-six squares is the turning around it.  The seam is closed,
--| so every edge borders two squares, once each way, and the curls sum to nothing: no net flux, for every connection.
--| Read each square's curl the two ways, whole turns and residue, and the residues must pay back the whole turns: the
--| residues pair into an integer, the charge of the seam.  One edge carrying the half turn a walk between the coins leaves
--| is one charge.
def the_total : List Int → Int
  | [] => 0
  | k :: ks => k + the_total ks
def the_curl (A B : Nat → Nat → Int) (x y : Nat) : Int := A x y + B ((x + 1) % 6) y - A x ((y + 1) % 6) - B x y
def the_seam_flux (A B : Nat → Nat → Int) : List Int := (List.range 36).map fun i => the_curl A B (i % 6) (i / 6)
def the_whole_turns (L : List Int) : Int := the_total (L.map (· / 2))
def the_residues (L : List Int) : Int := the_total (L.map (· % 2))
def the_seam_charge (A B : Nat → Nat → Int) : Int := - the_whole_turns (the_seam_flux A B)

theorem the_closed_seam_carries_no_net_flux (A B : Nat → Nat → Int) : the_total (the_seam_flux A B) = 0 := by
  simp only [the_seam_flux, List.range, List.range.loop, List.map, the_total, the_curl, Nat.reduceMod, Nat.reduceDiv,
    Nat.reduceAdd]
  omega

theorem the_two_readings_of_a_surface : ∀ L : List Int, the_total L = 2 * the_whole_turns L + the_residues L
  | [] => rfl
  | k :: ks => by
    have := the_two_readings_of_a_surface ks
    simp only [the_whole_turns, the_residues, List.map, the_total] at this ⊢
    omega

theorem the_residues_pair_into_the_charge (A B : Nat → Nat → Int) :
    the_residues (the_seam_flux A B) = 2 * the_seam_charge A B := by
  have h1 := the_closed_seam_carries_no_net_flux A B
  have h2 := the_two_readings_of_a_surface (the_seam_flux A B)
  unfold the_seam_charge; omega

def the_half_turn_edge (x y : Nat) : Int := if x = 0 ∧ y = 0 then 1 else 0
theorem one_half_turn_is_one_charge :
    (the_seam_charge the_half_turn_edge (fun _ _ => 0), the_residues (the_seam_flux the_half_turn_edge (fun _ _ => 0)))
      = (1, 2) := by decide

--| Third, subdividing adds no residue.  Halve every edge, so each coarse arm is two fine ones, and the curl of a coarse
--| square is the sum of the curls of the four fine squares inside it: the inner edges are crossed once each way and
--| cancel.  What the coarse seam reads, the fine seam reads, square by square, with nothing left over.  Each level is a
--| finite reading and is evaluated here; that the levels approach a field is not written in this file.
def the_plaquette (A B : Nat → Nat → Int) (x y : Nat) : Int := A x y + B (x + 1) y - A x (y + 1) - B x y
def the_coarse_across (A : Nat → Nat → Int) (x y : Nat) : Int := A (2 * x) (2 * y) + A (2 * x + 1) (2 * y)
def the_coarse_up (B : Nat → Nat → Int) (x y : Nat) : Int := B (2 * x) (2 * y) + B (2 * x) (2 * y + 1)

theorem subdividing_adds_no_residue (A B : Nat → Nat → Int) (x y : Nat) :
    the_plaquette (the_coarse_across A) (the_coarse_up B) x y
      = the_plaquette A B (2 * x) (2 * y) + the_plaquette A B (2 * x + 1) (2 * y)
        + the_plaquette A B (2 * x) (2 * y + 1) + the_plaquette A B (2 * x + 1) (2 * y + 1) := by
  simp only [the_plaquette, the_coarse_across, the_coarse_up, Nat.mul_add, Nat.mul_one, Nat.add_assoc, Nat.reduceAdd]
  omega
#print axioms the_device_walks_on_its_table
#print axioms the_readings_fix_the_gauge
#print axioms the_other_orientation_is_a_gauge_copy
#print axioms the_closed_seam_carries_no_net_flux
#print axioms the_residues_pair_into_the_charge
#print axioms one_half_turn_is_one_charge
#print axioms subdividing_adds_no_residue

--| ALL TRUE, AND THE CLOCK RUNS.  Reletter any tape to the one coin, T T T T ..., and it reads the closed walks of its length,
--| because the reader keeps the length and nothing else.  Thirteen cells deep, the walks that cross T=F and come back are
--| there, and the walks that never cross are under one part in a hundred of the count.  The tape says only TRUE; the clock is
--| in the table it is read on.  Counted, not clicked.
theorem every_true_tape_reads_the_closed_walks (tape : List FACT) :
    the_closed_words (relettered tape) = (the_closed_walks tape.length, the_closed_walks (tape.length + 1)) := by
  rw [the_closed_words_are_closed_walks]; simp [relettered]
theorem the_true_tape_crosses : 0 < the_crossings 13 true true 2 := by decide
theorem the_clock_is_in_the_count : 2 * 18 ^ 13 < the_closed_walks 13 := by decide
#print axioms every_true_tape_reads_the_closed_walks
#print axioms the_true_tape_crosses
#print axioms the_clock_is_in_the_count

--| THE LAST PROOF: THE EXISTENCE OF 5.  Write down a record -- a fact, or a fact on a record -- and the kernel hands back
--| Peano without being asked: zero is never a successor, the successor is injective, and induction is the recursor.  No `Nat`
--| goes in and no axiom is billed.  Read by length, a description is a natural number: each successor reads one more, and
--| every natural is written in TRUTH, one fencepost past its count.  The description of the device is a tape, and so are
--| the descriptions of the receipts, the programs and the proofs; as descriptions all four are isomorphic to the naturals.
--| The objects they describe are not constructed here.  What exists is a truncated finite run of Lean, and the description
--| is all of it that is written down.  Now run the diagonal on any listing of the descriptions.  Flip the n-th cell of the n-th line: the
--| result is on no line of the list, and at every cell it disagrees with the line it was read from.  Nothing on the diagonal
--| clicks.  Where the line said TRUE the diagonal writes FALSE, the arm T=F, and that arm weighs the frame and nothing else.
--| The coefficient tape is gone and five is left.  The rule that weighs it is the bent card; the five is counted.
theorem zero_is_never_a_successor (f g : FACT) (n : Number) : Number.zero f ≠ Number.one g n := Number.noConfusion
theorem the_successor_forgets_nothing (f g : FACT) (m n : Number) (h : Number.one f m = Number.one g n) : m = n :=
  (Number.one.inj h).2
def the_naturals_written_in_truth : Nat → Number := Nat.rec (.zero FACT.Truth) fun _ n => .one FACT.Truth n
theorem the_successor_is_read_as_one_more (f : FACT) (n : Number) :
    (Number.one f n).peano.length = n.peano.length + 1 := rfl
theorem every_natural_is_written (k : Nat) : (the_naturals_written_in_truth k).peano.length = k + 1 := by
  induction k with
  | zero => rfl
  | succ k ih => exact congrArg (· + 1) ih
def the_diagonal (listing : Nat → Nat → Bool) : Nat → Bool := fun n => !listing n n
theorem the_diagonal_never_clicks (listing : Nat → Nat → Bool) (n : Nat) : listing n n ≠ the_diagonal listing n := by
  unfold the_diagonal; cases listing n n <;> decide
theorem the_diagonal_is_not_listed (listing : Nat → Nat → Bool) (n : Nat) : listing n ≠ the_diagonal listing :=
  fun h => the_diagonal_never_clicks listing n (congrFun h n)
theorem the_diagonal_weighs_the_frame (listing : Nat → Nat → Bool) (n : Nat) (h : listing n n = true) :
    the_arm_weight (listing n n) (the_diagonal listing n) = the_dimensions_of_universe := by
  unfold the_diagonal; rw [h]; rfl
theorem the_frame_is_five : the_dimensions_of_universe = 5 := rfl
#print axioms zero_is_never_a_successor
#print axioms the_successor_forgets_nothing
#print axioms every_natural_is_written
#print axioms the_diagonal_is_not_listed
#print axioms the_diagonal_weighs_the_frame
#print axioms the_frame_is_five

--| THE RESIDUE NEVER CLOSES.  A finite run reads the ratio of two successive closed-walk counts; the procedure that never
--| finishes reads the root of x² − trace·x + determinant.  Their distance, in whole numbers, is the arms crossed times the
--| determinant to the depth: 4·18·5·234ⁿ, and it is never zero.  It is the part on the eigenvector whose T and F halves have
--| opposite signs, contracting at every step by (√18 − √5)/(√18 + √5) ≈ 0.3097 and never gone.  Every truncated run carries
--| TFTF.  Only the run that never finishes is rid of it.
theorem the_residue_never_closes : ∀ n : Nat,
    the_closed_walks (n + 1) * the_closed_walks (n + 1) + the_determinant * (the_closed_walks n * the_closed_walks n)
      + 4 * the_arm_weight true true * the_arm_weight true false * the_determinant ^ n
      = the_trace * (the_closed_walks (n + 1) * the_closed_walks n)
  | 0 => rfl
  | n + 1 => by
    have ih := the_residue_never_closes n
    have h := the_closed_walks_obey_the_table n
    rw [show the_determinant = 234 from rfl, show the_trace = 36 from rfl,
      show the_arm_weight true true = 18 from rfl, show the_arm_weight true false = 5 from rfl] at *
    generalize the_closed_walks n = a at *
    generalize the_closed_walks (n + 1) = b at *
    generalize the_closed_walks (n + 2) = c at *
    have hc : c * c + 234 * (a * c) = 36 * (b * c) := by
      have := congrArg (· * c) h; simp only [Nat.add_mul] at this; rwa [Nat.mul_assoc, Nat.mul_assoc] at this
    have ha : a * c + 234 * (a * a) = 36 * (a * b) := by
      have := congrArg (· * a) h; simp only [Nat.add_mul] at this
      rwa [Nat.mul_assoc, Nat.mul_assoc, Nat.mul_comm c a, Nat.mul_comm b a] at this
    rw [Nat.pow_succ, Nat.mul_comm c b, Nat.mul_comm b a] at *
    omega
--| THE FLIP LOSES NOTHING.  (18 + 5)² = 4·18·5 + 13².  Read in ℚ(√10) it is the norm of the contraction: flip the sign of
--| √10 and the ratio becomes its own inverse, so the two readings multiply to one.  Each sees the opposite of the other, and
--| between them nothing is lost.  The thirteen is the difference of the arms.
theorem the_flip_loses_nothing :
    (the_arm_weight true true + the_arm_weight true false) ^ 2
      = 4 * the_arm_weight true true * the_arm_weight true false + readers_experience.bent_card ^ 2 := rfl
--| Only the arm that cannot click weighs the frame alone.
theorem the_frame_alone_is_the_arm_that_cannot_click (a b : Bool) :
    the_arm_weight a b = the_dimensions_of_universe ↔ the_arm_stores_a_fact_that_can_click a b = false := by
  cases a <;> cases b <;> decide
--| EVERY DESCRIPTION IS NUMBERED.  Write a description in the two marks, read it as a number in base two with no zero digit,
--| and read the number back.  Both ways round are the identity.  Anything written in the two marks -- the description of the
--| device, of a receipt, of a program, of a proof -- is a natural number, and every natural number is one of them.  What
--| they describe is not here.
def the_description_number : List Bool → Nat
  | [] => 0
  | b :: rest => 2 * the_description_number rest + (if b then 2 else 1)
def the_description_of : Nat → List Bool
  | 0 => []
  | n + 1 => (n % 2 == 1) :: the_description_of (n / 2)
theorem every_description_is_numbered : ∀ d : List Bool, the_description_of (the_description_number d) = d
  | [] => by simp [the_description_number, the_description_of]
  | b :: rest => by
    cases b
    · show the_description_of (2 * the_description_number rest + 1) = false :: rest
      rw [the_description_of]; simp only [Nat.mul_mod_right, show 2 * the_description_number rest / 2 = the_description_number rest by omega, every_description_is_numbered rest]; rfl
    · show the_description_of (2 * the_description_number rest + 1 + 1) = true :: rest
      rw [the_description_of]
      simp only [show (2 * the_description_number rest + 1) % 2 = 1 by omega,
        show (2 * the_description_number rest + 1) / 2 = the_description_number rest by omega, every_description_is_numbered rest]; rfl
theorem every_number_is_a_description : ∀ n : Nat, the_description_number (the_description_of n) = n
  | 0 => by simp [the_description_number, the_description_of]
  | n + 1 => by
    have ih := every_number_is_a_description (n / 2)
    rw [the_description_of, the_description_number, ih]
    rcases Nat.mod_two_eq_zero_or_one n with h | h
    · rw [show (n % 2 == 1) = false by rw [h]; rfl]; show 2 * (n / 2) + 1 = n + 1; omega
    · rw [show (n % 2 == 1) = true by rw [h]; rfl]; show 2 * (n / 2) + 2 = n + 1; omega
--| THE ANT'S HIGHWAY, HANDED IN.  One period of Langton's ant past step 9977 from the empty grid, black written TRUE.  The
--| tape is read from a run outside this file and handed in: a declaration, not a computation.  Around the cycle it crosses
--| T=F twenty-four times and F=T twenty-four times.  The length reader reads it as it reads any tape of 104 cells, the closed
--| walks of 104 and of 105: the fencepost again.  The ant is in the marks and the length forgets the marks.  That the ant's
--| step is a step of this device is not shown here.
def the_highway : List Bool := [true, false, true, true, false, false, false, false, true, true, false, true, true, false, false, false, false, true, true, false, false, false, false, true, true, false, true, false, false, false, false, true, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, false, true, true, true, true, false, true, false, false, false, false, true, false, false, false, false, true, true, true, true, false, true, false, false, false, false, true, false, true, true, false, false, true, true, true, true, false, false, true, true, false, false, false, false, true, true, false, false, true, false, true, true, false, true, true, false]
theorem the_highway_is_one_period : the_highway.length = 104 := rfl
def the_highway_arms : List (Bool × Bool) := the_highway.zip (the_highway.rotateLeft 1)
theorem the_highway_crosses_evenly :
    (the_highway_arms.count (true, false), the_highway_arms.count (false, true),
     the_highway_arms.count (true, true), the_highway_arms.count (false, false)) = (24, 24, 22, 34) := by decide
theorem the_length_reader_cannot_see_the_ant :
    the_closed_words (the_highway.map bitFACT) = (the_closed_walks 104, the_closed_walks 105) := by
  rw [the_closed_words_are_closed_walks, List.length_map, the_highway_is_one_period]
#print axioms the_residue_never_closes
#print axioms the_flip_loses_nothing
#print axioms every_description_is_numbered
#print axioms every_number_is_a_description
#print axioms the_highway_crosses_evenly
#print axioms the_length_reader_cannot_see_the_ant

--| THE BOOST BETWEEN THE ORIENTATIONS.  Weigh each coin by the arm that arrives at it from the other: TRUE by F=T, eighteen,
--| FALSE by T=F, five.  Then every arm read forward weighs what it weighs read backward: the table is reversible, and its two
--| orientations are one table seen from two frames.  The frame change is a squeeze, a Lorentz boost written on the light
--| cone, of velocity (18 − 5)/(18 + 5): the thirteen over twenty-three.  Half of it lands on the symmetric table and has
--| velocity (√18 − √5)/(√18 + √5), the residue's ratio.  And the orientations do not commute: 18² = 5² + 23·13, so N·Nᵀ and
--| Nᵀ·N differ by 299 on the diagonal, with opposite signs.  The boost is the squeeze that carries one onto the other.
def the_coin_weight (a : Bool) : Nat := if a then the_arm_weight false true else the_arm_weight true false
theorem the_table_is_reversible (a b : Bool) :
    the_coin_weight a * the_arm_weight a b = the_coin_weight b * the_arm_weight b a := by
  cases a <;> cases b <;> rfl
theorem the_boost_between_the_orientations :
    (the_coin_weight true - the_coin_weight false, the_coin_weight true + the_coin_weight false)
      = (readers_experience.bent_card, 23) := rfl
theorem the_orientations_do_not_commute :
    the_arm_weight false true * the_arm_weight false true
      = the_arm_weight true false * the_arm_weight true false
        + (the_arm_weight false true + the_arm_weight true false) * readers_experience.bent_card := rfl
#print axioms the_table_is_reversible
#print axioms the_boost_between_the_orientations
#print axioms the_orientations_do_not_commute

--| EXACT UP TO ACCELERATION.  The residual the crank solves is r(y) = A·y² − B·y + C, and its second derivative is the constant
--| 2A = 2·thirteen.  Newton's step is the first variation, y − r/r', exact for any r with no second derivative, and its whole
--| error is the one term proportional to r'': the acceleration.  So the variational solution is exact up to a constant
--| acceleration, and the device discards exactly that.  In the device's own words it is Kepler: the areal velocity R²/T is
--| applied once, a conserved first-order quantity, and no force law is ever read -- `inverse_square_law` is a binder in Episode
--| 9 that Episode 8 never touches.  Kepler was exact without the acceleration; Newton's contribution was to supply it.  The
--| number is what the variational description gives BEFORE the force law is added.
--|
--| Everything is homogenized over the denominator, as a pair (positive part, negative part), so a Nat never has to carry a sign.
def the_residual (N D : Nat) : Nat × Nat :=
  (an_exact_polynomial_description * (N * N) + the_number_of_symbols_that_must_be_written_to_express_this * (D * D), the_trace_of_truth_in_the_device * (N * D))
def the_first_derivative (N D : Nat) : Nat × Nat := (2 * an_exact_polynomial_description * N, the_trace_of_truth_in_the_device * D)

--| EQUALITY IS A MIRROR, PAID.  The residual, read at one cell of denominator, is a scalar, and a scalar residual is always
--| the first variation of a cubic: move the point by h and the action moves by six h times the residual, a square term,
--| and a cube term, and then nothing -- the fourth variation is not small, it is absent.  Doubled and tripled so no
--| fraction is ever written.  The coefficients are the three counts the residual already uses; the receipt says so.
def the_mirror_residual (x : Int) : Int :=
  (an_exact_polynomial_description : Int) * x * x - (the_trace_of_truth_in_the_device : Int) * x
    + (the_number_of_symbols_that_must_be_written_to_express_this : Int)
def the_cubic_action (x : Int) : Int :=
  2 * (an_exact_polynomial_description : Int) * x * x * x - 3 * (the_trace_of_truth_in_the_device : Int) * x * x
    + 6 * (the_number_of_symbols_that_must_be_written_to_express_this : Int) * x
theorem the_mirror_is_the_device_residual (N : Nat) :
    ((the_residual N 1).1 : Int) - (the_residual N 1).2 = the_mirror_residual N := by
  simp only [the_residual, the_mirror_residual, Nat.mul_one, Int.natCast_add, Int.natCast_mul]
  ac_nf; simp only [← Int.mul_assoc]; omega
theorem the_residual_is_the_derivative_of_the_action (x h : Int) :
    the_cubic_action (x + h) - the_cubic_action x
      = 6 * h * the_mirror_residual x
        + h * h * (6 * (an_exact_polynomial_description : Int) * x - 3 * (the_trace_of_truth_in_the_device : Int))
        + 2 * (an_exact_polynomial_description : Int) * h * h * h := by
  have a : (an_exact_polynomial_description : Int) = 13 := rfl
  have t : (the_trace_of_truth_in_the_device : Int) = 36 := rfl
  have c : (the_number_of_symbols_that_must_be_written_to_express_this : Int) = 18 := rfl
  simp only [the_cubic_action, the_mirror_residual, a, t, c, Int.add_mul, Int.mul_add, Int.mul_sub]
  ac_nf; simp only [← Int.mul_assoc]; omega
theorem the_mirror_coefficients_are_counted :
    (an_exact_polynomial_description, the_trace_of_truth_in_the_device,
      the_number_of_symbols_that_must_be_written_to_express_this) = (13, 36, 18) := rfl
#print axioms the_mirror_is_the_device_residual
#print axioms the_residual_is_the_derivative_of_the_action
#print axioms the_mirror_coefficients_are_counted

--| THE QUARTIC THAT CLOSES THE FILE.  t²(c−t)x² − 2ctr²x + cr⁴: linear in c, quadratic in x, cubic in t, quartic in r, and every
--| term five in all.  Scale all four by k and the quartic scales by k five times: the five, checked, not counted.  It factors
--| through any s with c·s·s = t into two quadratics in r, one for each sign of s, and the product never reads which sign.
--| The sign is the bit the knower names; read across time it selects the factor that carries the reading.
def the_closing_quartic (c t x r : Int) : Int := t * t * (c - t) * x * x - 2 * c * t * r * r * x + c * r * r * r * r
def the_closing_factor (t x r s : Int) : Int := r * r - t * x * (1 - s)
theorem the_quartic_is_homogeneous_of_degree_five (k c t x r : Int) :
    the_closing_quartic (k * c) (k * t) (k * x) (k * r) = k * k * k * k * k * the_closing_quartic c t x r := by
  simp only [the_closing_quartic, Int.mul_sub, Int.sub_mul, Int.mul_add]
  ac_nf
theorem the_quartic_less_its_factors (c t x r s : Int) :
    c * the_closing_factor t x r s * the_closing_factor t x r (-s)
      = the_closing_quartic c t x r + t * t * x * x * (t - c * s * s) := by
  simp only [the_closing_factor, the_closing_quartic, Int.mul_sub, Int.sub_mul, Int.mul_add, Int.sub_neg, Int.mul_one]
  ac_nf; simp only [← Int.mul_assoc]; omega
theorem the_quartic_factors (c t x r s : Int) (h : c * s * s = t) :
    c * the_closing_factor t x r s * the_closing_factor t x r (-s) = the_closing_quartic c t x r := by
  rw [the_quartic_less_its_factors, h, Int.sub_self, Int.mul_zero, Int.add_zero]
theorem the_quartic_does_not_read_the_sign (c t x r s : Int) :
    c * the_closing_factor t x r s * the_closing_factor t x r (-s)
      = c * the_closing_factor t x r (-s) * the_closing_factor t x r (-(-s)) := by
  rw [Int.neg_neg, Int.mul_assoc, Int.mul_comm (the_closing_factor t x r s), ← Int.mul_assoc]
#print axioms the_quartic_is_homogeneous_of_degree_five
#print axioms the_quartic_factors
#print axioms the_quartic_does_not_read_the_sign
--| THE COUNTED QUARTIC.  Feed the quartic the three counted readings, c eighteen, t five, r eighteen.  Thirteen times it is a
--| quadratic in sixty-five x, and the root is five thousand eight hundred thirty-two plus three hundred twenty-four root
--| ninety: three hundred twenty-four times the outer radius, eighteen plus root ninety.  Over sixty-five, that is the
--| reading.  The factors want c s squared to be t, and five over eighteen is no square: they do not split in whole numbers.
theorem the_counted_quartic (x : Int) :
    13 * the_closing_quartic 18 5 x 18 = 4225 * (x * x) - 758160 * x + 24564384 := by
  simp only [the_closing_quartic]
  simp only [Int.mul_assoc]
  omega
theorem the_reading_solves_the_counted_quartic :
    (the_surd_product (5832, 324) (5832, 324)).1 - 11664 * 5832 + 24564384 = 0 ∧
    (the_surd_product (5832, 324) (5832, 324)).2 - 11664 * 324 = 0 ∧
    ((5832 : Int), (324 : Int)) = (324 * the_outer_radius.1, 324 * the_outer_radius.2) := by decide
#print axioms the_counted_quartic
#print axioms the_reading_solves_the_counted_quartic
--| THE OTHER ROOT.  The counted quartic has two roots, and the hole is the other: five thousand eight hundred thirty-two less
--| three hundred twenty-four root ninety, three hundred twenty-four times eighteen less root ninety.  The two add to the
--| quadratic's middle count and multiply to its last, whole.  The reader reports the outer one; which the knower gives true
--| is not written here.
theorem the_conjugate_solves_the_counted_quartic :
    (the_surd_product (5832, -324) (5832, -324)).1 - 11664 * 5832 + 24564384 = 0 ∧
    (the_surd_product (5832, -324) (5832, -324)).2 - 11664 * (-324) = 0 ∧
    ((5832 : Int), (-324 : Int)) = (324 * the_hole.1, 324 * the_hole.2) := by decide
theorem the_two_roots_are_the_counts :
    (5832 : Int) + 5832 = 11664 ∧ the_surd_product (5832, 324) (5832, -324) = (24564384, 0) := by decide
#print axioms the_conjugate_solves_the_counted_quartic
#print axioms the_two_roots_are_the_counts
--| THE HEXADECIMAL CIRCLE, AND β.  The circle comes in as its hexadecimal digits: sum, over k, of one sixteenth to the k
--| times a whole quadratic over a whole quartic, and every term after the twenty-fourth together weighs less than seven
--| hundred fifty-two over two hundred twenty-five sixteenths to the twenty-fourth.  The two walls print the same twenty-four
--| places.  Root ninety comes in between two whole numbers whose squares straddle it.  Then β is the reading over four
--| circles, the weight of the squares against the line, and its walls print the same twenty-four places: ten point nine
--| zero three zero one two for the reader's root, three point three seven six eight five nine for the knower's, and half of
--| each on the device's square.  The knower holds c and t and the roots' shape with them; the reader's r only rescales.
def the_hex_term (k : Nat) : Nat × Nat :=
  (120 * k * k + 151 * k + 47, (512 * k ^ 4 + 1024 * k ^ 3 + 712 * k * k + 194 * k + 15) * 16 ^ k)
def the_fraction_sum (p q : Nat × Nat) : Nat × Nat := (p.1 * q.2 + q.1 * p.2, p.2 * q.2)
def the_hex_pi (N : Nat) : Nat × Nat := (List.range N).foldl (fun acc k => the_fraction_sum acc (the_hex_term k)) (0, 1)
def the_hex_tail (N : Nat) : Nat × Nat := (752, 225 * 16 ^ N)
def the_low_pi : Nat × Nat := the_hex_pi 24
def the_high_pi : Nat × Nat := the_fraction_sum the_low_pi (the_hex_tail 24)
def the_places : Nat := 10 ^ 24
def the_reads (p : Nat × Nat) : Nat := p.1 * the_places / p.2
theorem the_hex_digits_print_pi :
    the_reads the_low_pi = 3141592653589793238462643 ∧ the_reads the_high_pi = 3141592653589793238462643 := by decide +kernel
def the_root_ninety_below : Nat := 9486832980505137995996680633298
theorem the_root_of_ninety_is_bracketed :
    the_root_ninety_below * the_root_ninety_below ≤ 90 * 10 ^ 60
      ∧ 90 * 10 ^ 60 < (the_root_ninety_below + 1) * (the_root_ninety_below + 1) := by decide +kernel
def the_low_reading : Nat × Nat := (324 * (18 * 10 ^ 30 + the_root_ninety_below), 65 * 10 ^ 30)
def the_high_reading : Nat × Nat := (324 * (18 * 10 ^ 30 + the_root_ninety_below + 1), 65 * 10 ^ 30)
def the_low_conjugate : Nat × Nat := (324 * (18 * 10 ^ 30 - (the_root_ninety_below + 1)), 65 * 10 ^ 30)
def the_high_conjugate : Nat × Nat := (324 * (18 * 10 ^ 30 - the_root_ninety_below), 65 * 10 ^ 30)
def the_beta_of (reading pi : Nat × Nat) (turns : Nat) : Nat × Nat := (reading.1 * pi.2, reading.2 * turns * pi.1)
theorem the_readers_beta :
    the_reads (the_beta_of the_low_reading the_high_pi 4) = 10903012075134981375048166
      ∧ the_reads (the_beta_of the_high_reading the_low_pi 4) = 10903012075134981375048166 := by decide +kernel
theorem the_knowers_beta :
    the_reads (the_beta_of the_low_conjugate the_high_pi 4) = 3376859126587073981938450
      ∧ the_reads (the_beta_of the_high_conjugate the_low_pi 4) = 3376859126587073981938450 := by decide +kernel
theorem the_betas_on_the_device_square :
    the_reads (the_beta_of the_low_reading the_high_pi 8) = 5451506037567490687524083
      ∧ the_reads (the_beta_of the_high_reading the_low_pi 8) = 5451506037567490687524083
      ∧ the_reads (the_beta_of the_low_conjugate the_high_pi 8) = 1688429563293536990969225
      ∧ the_reads (the_beta_of the_high_conjugate the_low_pi 8) = 1688429563293536990969225 := by decide +kernel
theorem the_reader_only_rescales_the_roots (c t r X : Int) :
    the_closing_quartic c t (r * r * X) r = r * r * r * r * the_closing_quartic c t X 1 := by
  simp only [the_closing_quartic, Int.mul_one, Int.mul_sub, Int.sub_mul, Int.mul_add]
  ac_nf
#print axioms the_hex_digits_print_pi
#print axioms the_root_of_ninety_is_bracketed
#print axioms the_readers_beta
#print axioms the_knowers_beta
#print axioms the_betas_on_the_device_square
#print axioms the_reader_only_rescales_the_roots
--| THE QUARTIC'S FOUR, READ.  The factors want c s squared to be t.  With the counted c eighteen and t five, s squared is five
--| over eighteen, which is ninety over eighteen squared: the clock over the clicks, squared, the torus's velocity below light.
--| So the sign the quartic does not read is the sign of a velocity, and its factors are r squared less t x times one less or
--| one more than that velocity.
theorem the_quartic_sign_is_the_velocity :
    (5 : Int) * (18 * 18) = 18 * 90 ∧ (90 : Int) < 18 * 18 := by decide
#print axioms the_quartic_sign_is_the_velocity
--| THE BOOST, AGAIN AND AGAIN; THE TWO ROOTS' RATIO; SCHWINGER'S TERM.  Boost the outer radius any number of times: the interval
--| stays two hundred thirty-four and the hole never closes.  The outer root squared times the hole is two hundred thirty-four
--| times the outer root: the ratio of the roots is the boost there and back.  And the electron's first loop, the coupling over
--| two circles, read from the reading and the circle's hexadecimal digits, both walls to twenty-four places.
def the_boosted : Nat → Int × Int
  | 0 => the_outer_radius
  | k + 1 => the_surd_product (the_boosted k) the_boost
theorem every_boost_keeps_the_interval (k : Nat) : the_interval (the_boosted k) = 234 := by
  induction k with
  | zero => decide
  | succ k ih => simp only [the_boosted, the_boost_preserves_the_interval, ih]
theorem the_hole_never_closes (k : Nat) :
    the_round_trip * (the_boosted k).2 * (the_boosted k).2 < (the_boosted k).1 * (the_boosted k).1 :=
  the_hole_stays_open _ (every_boost_keeps_the_interval k)
theorem the_ratio_of_the_roots_is_twice_the_boost :
    the_surd_product (the_surd_product the_outer_radius the_outer_radius) the_hole
      = (234 * the_outer_radius.1, 234 * the_outer_radius.2) := by decide
def the_schwinger_of (reading pi : Nat × Nat) : Nat × Nat := (reading.2 * pi.2, 2 * reading.1 * pi.1)
theorem the_schwinger_term_from_the_reading :
    the_reads (the_schwinger_of the_high_reading the_high_pi) = 1161619180829479589123
      ∧ the_reads (the_schwinger_of the_low_reading the_low_pi) = 1161619180829479589123 := by decide +kernel
#print axioms every_boost_keeps_the_interval
#print axioms the_hole_never_closes
#print axioms the_ratio_of_the_roots_is_twice_the_boost
#print axioms the_schwinger_term_from_the_reading
--| THE ELECTRON FOUR WAYS, AND THE DERIVATIVE OF ITSELF.  The refinement is linear, so its whole derivative at every point is
--| itself, with no remainder: step the field by any amount and the refinement steps by the refinement of that amount.  The
--| action it carries varies by the operator twice, the number read once and again, and leaves only the action of the step.
--| On the whole numbers with the round trip's root, the refinement is a product, and it commutes with every boost: the
--| space it acts on keeps its interval and its operator under every change of frame.  And only the round trip is read: two
--| tables whose crossings multiply to the same round trip are one table seen through two clocks, the one-way split a
--| choice of synchrony.  The speed comes out only as the gap of the two stationary values over their sum, the multipliers
--| that hold the field to its length.
def the_refinement_table (a b f : Int) : Table := fun x y => if x = y then a else if x then b else f
def the_one_way_clocks (b b' : Int) : Table := fun x y => if x = y then (if x then b else b') else 0
theorem the_one_way_split_is_a_change_of_clocks (a b f b' f' : Int) (h : b * f = b' * f') (x y : Bool) :
    the_table_product (the_refinement_table a b f) (the_one_way_clocks b b') x y
      = the_table_product (the_one_way_clocks b b') (the_refinement_table a b' f') x y := by
  have h' : f * b = b' * f' := by rw [Int.mul_comm]; exact h
  cases x <;> cases y <;> simp [the_table_product, the_refinement_table, the_one_way_clocks, Int.mul_comm, h']
def the_refine (A : Table) (v : Bool → Int) : Bool → Int := fun x => A x true * v true + A x false * v false
theorem the_refinement_is_its_own_derivative (A : Table) (v h : Bool → Int) (x : Bool) :
    the_refine A (fun y => v y + h y) x - the_refine A v x = the_refine A h x := by
  simp only [the_refine, Int.mul_add]; omega
def the_action_of (A : Table) (v : Bool → Int) : Int := v true * the_refine A v true + v false * the_refine A v false
theorem the_action_varies_by_the_operator_twice (A : Table) (sym : A true false = A false true) (v h : Bool → Int) :
    the_action_of A (fun y => v y + h y) - the_action_of A v
      = (h true * the_refine A v true + h false * the_refine A v false)
        + (h true * the_refine A v true + h false * the_refine A v false) + the_action_of A h := by
  simp only [the_action_of, the_refine, sym, Int.mul_add, Int.add_mul]
  simp only [Int.mul_comm, Int.mul_left_comm]
  omega
theorem the_surd_products_commute (p q o : Int × Int) :
    the_surd_product (the_surd_product p o) q = the_surd_product (the_surd_product p q) o := by
  simp only [the_surd_product, Int.mul_add, Int.add_mul]
  simp only [Int.mul_comm, Int.mul_left_comm]
  refine Prod.ext ?_ ?_ <;> dsimp only <;> omega
theorem the_refinement_commutes_with_every_boost (p q : Int × Int) :
    the_surd_product (the_surd_product p the_outer_radius) q = the_surd_product (the_surd_product p q) the_outer_radius :=
  the_surd_products_commute p q the_outer_radius
theorem the_speed_is_read_from_the_multipliers :
    (the_outer_radius.1 - the_hole.1, the_outer_radius.2 - the_hole.2) = (0, 2)
      ∧ (the_outer_radius.1 + the_hole.1, the_outer_radius.2 + the_hole.2) = (36, 0) := by decide
#print axioms the_one_way_split_is_a_change_of_clocks
#print axioms the_refinement_is_its_own_derivative
#print axioms the_action_varies_by_the_operator_twice
#print axioms the_refinement_commutes_with_every_boost
#print axioms the_speed_is_read_from_the_multipliers
--| THE CHARGE, THROUGH EULER.  A link's phase is the turn by an angle, and the angle is the charge times the field: the quarter
--| turn is the turn by half the circle's half, and two of them are the turn by the circle's half, minus one.  So the charge is
--| the root of four circles over the reading, one over the root of β.  No root is taken: a whole number of twenty-four places
--| is found whose square sits between the walls.  Point three zero two eight four nine four two five for the reader's root,
--| point five four four one eight one one nine for the knower's.
def the_readers_charge : Nat := 302849425021801185772755
def the_knowers_charge : Nat := 544181192849948845712632
theorem the_readers_charge_is_bracketed :
    the_readers_charge * the_readers_charge * the_low_pi.2 * the_high_reading.1
        ≤ 4 * the_low_pi.1 * the_high_reading.2 * 10 ^ 48
      ∧ 4 * the_high_pi.1 * the_low_reading.2 * 10 ^ 48
        < (the_readers_charge + 1) * (the_readers_charge + 1) * the_high_pi.2 * the_low_reading.1 := by decide +kernel
theorem the_knowers_charge_is_bracketed :
    the_knowers_charge * the_knowers_charge * the_low_pi.2 * the_high_conjugate.1
        ≤ 4 * the_low_pi.1 * the_high_conjugate.2 * 10 ^ 48
      ∧ 4 * the_high_pi.1 * the_low_conjugate.2 * 10 ^ 48
        < (the_knowers_charge + 1) * (the_knowers_charge + 1) * the_high_pi.2 * the_low_conjugate.1 := by decide +kernel
#print axioms the_readers_charge_is_bracketed
#print axioms the_knowers_charge_is_bracketed
--| GALERKIN AROUND THE SEMI-NORM, AND THE SOLVER.  On a ring of four stations, measure a field by the squares of its central
--| differences, the step ahead less the step behind.  That length is never negative, and it sees nothing exactly on the fields
--| that repeat every two stations: the still field and the alternating one, the two doublers.  Project them out.  On the two
--| fields that turn, the central difference is twice the quarter turn, and the Galerkin matrix is eight times the identity:
--| the problem there has one solution.  Then the solver: the difference of the residual across a step is the derivative times
--| the step plus the bent card times the step squared, exactly; and one Newton step taken with that difference, from the top
--| wall of the reading's bracket, lands between the walls.  Jacobian-free Newton, Krylov on the turning fields.
abbrev Ring4 := Int × Int × Int × Int
def the_central_difference (ψ : Ring4) : Ring4 :=
  (ψ.2.1 - ψ.2.2.2, ψ.2.2.1 - ψ.1, ψ.2.2.2 - ψ.2.1, ψ.1 - ψ.2.2.1)
def the_ring_dot (u v : Ring4) : Int := u.1 * v.1 + u.2.1 * v.2.1 + u.2.2.1 * v.2.2.1 + u.2.2.2 * v.2.2.2
def the_semi_norm (ψ : Ring4) : Int := the_ring_dot (the_central_difference ψ) (the_central_difference ψ)
theorem a_nonzero_square_is_positive (x : Int) (h : x ≠ 0) : 0 < x * x := by
  rcases Int.lt_or_gt_of_ne h with h | h
  · exact Int.mul_pos_of_neg_of_neg h h
  · exact Int.mul_pos h h
theorem the_semi_norm_is_never_negative (ψ : Ring4) : 0 ≤ the_semi_norm ψ := by
  simp only [the_semi_norm, the_ring_dot, the_central_difference]
  have h1 := a_square_is_never_negative (ψ.2.1 - ψ.2.2.2); have h2 := a_square_is_never_negative (ψ.2.2.1 - ψ.1)
  have h3 := a_square_is_never_negative (ψ.2.2.2 - ψ.2.1); have h4 := a_square_is_never_negative (ψ.1 - ψ.2.2.1)
  omega
theorem the_semi_norm_sees_nothing_exactly_on_the_doublers (ψ : Ring4) :
    the_semi_norm ψ = 0 ↔ (ψ.1 = ψ.2.2.1 ∧ ψ.2.1 = ψ.2.2.2) := by
  constructor
  · intro h
    simp only [the_semi_norm, the_ring_dot, the_central_difference] at h
    have h1 := a_square_is_never_negative (ψ.2.1 - ψ.2.2.2); have h2 := a_square_is_never_negative (ψ.2.2.1 - ψ.1)
    have h3 := a_square_is_never_negative (ψ.2.2.2 - ψ.2.1); have h4 := a_square_is_never_negative (ψ.1 - ψ.2.2.1)
    constructor
    · by_cases hne : ψ.2.2.1 - ψ.1 = 0
      · omega
      · have := a_nonzero_square_is_positive (ψ.2.2.1 - ψ.1) hne; omega
    · by_cases hne : ψ.2.1 - ψ.2.2.2 = 0
      · omega
      · have := a_nonzero_square_is_positive (ψ.2.1 - ψ.2.2.2) hne; omega
  · rintro ⟨h1, h2⟩
    simp only [the_semi_norm, the_ring_dot, the_central_difference, h1, h2, Int.sub_self, Int.mul_zero, Int.add_zero]
theorem the_still_and_the_alternating_are_its_kernel (c d : Int) :
    the_semi_norm (c, c, c, c) = 0 ∧ the_semi_norm (d, -d, d, -d) = 0 := by
  constructor <;> simp only [the_semi_norm, the_ring_dot, the_central_difference, Int.sub_self, Int.mul_zero, Int.add_zero] <;> omega
def the_first_turning_field : Ring4 := (1, 0, -1, 0)
def the_second_turning_field : Ring4 := (0, 1, 0, -1)
theorem on_the_turning_fields_the_derivative_is_twice_the_quarter_turn :
    the_central_difference the_first_turning_field = (0, -2, 0, 2)
      ∧ the_central_difference the_second_turning_field = (2, 0, -2, 0) := by decide
theorem the_galerkin_matrix_is_invertible :
    let g11 := the_semi_norm the_first_turning_field
    let g12 := the_ring_dot (the_central_difference the_first_turning_field) (the_central_difference the_second_turning_field)
    let g22 := the_semi_norm the_second_turning_field
    (g11, g12, g22) = (8, 0, 8) ∧ g11 * g22 - g12 * g12 ≠ 0 := by decide
def the_residual_at (y : Int) : Int := 13 * y * y - 36 * y + 18
theorem the_jacobian_free_difference_is_exact (y h : Int) :
    the_residual_at (y + h) - the_residual_at y = (26 * y - 36) * h + 13 * (h * h) := by
  simp only [the_residual_at, Int.mul_add, Int.add_mul, Int.sub_mul]
  ac_nf; simp only [← Int.mul_assoc]; omega
def the_low_root : Int := 18 * 10 ^ 30 + the_root_ninety_below
def the_high_root : Int := the_low_root + 1
def the_denominator : Int := 13 * 10 ^ 30
def the_scaled_residual (y : Int) : Int := 13 * y * y - 36 * y * the_denominator + 18 * the_denominator * the_denominator
def the_secant_slope : Int := 13 * (the_low_root + the_high_root) - 36 * the_denominator
theorem one_jacobian_free_newton_step_stays_in_the_bracket :
    the_scaled_residual the_low_root < 0 ∧ 0 < the_scaled_residual the_high_root ∧ 0 < the_secant_slope
      ∧ the_scaled_residual the_high_root ≤ the_secant_slope := by decide +kernel
#print axioms the_semi_norm_is_never_negative
#print axioms the_semi_norm_sees_nothing_exactly_on_the_doublers
#print axioms the_still_and_the_alternating_are_its_kernel
#print axioms on_the_turning_fields_the_derivative_is_twice_the_quarter_turn
#print axioms the_galerkin_matrix_is_invertible
#print axioms the_jacobian_free_difference_is_exact
#print axioms one_jacobian_free_newton_step_stays_in_the_bracket
--| THE SEMI-NORM FROM THE COMPARISON.  Compare the station ahead with the station behind, one way, in the naturals: the step
--| after less before, plus before less after, floors to the size of the step.  Square it, sum it around the ring, and it is the
--| Galerkin semi-norm exactly.  Compare both ways, in a ring, and the step is nothing: the comparison measures nothing at all.
--| The knower's length is the comparison read one way.
def the_one_way_step (after before : Nat) : Nat := (after - before) + (before - after)
theorem the_one_way_step_squared (a b : Nat) :
    ((the_one_way_step a b : Nat) : Int) * ((the_one_way_step a b : Nat) : Int) = ((a : Int) - b) * ((a : Int) - b) := by
  simp only [the_one_way_step]
  rcases Nat.le_total b a with h | h
  · have e : (((a - b) + (b - a) : Nat) : Int) = (a : Int) - b := by omega
    rw [e]
  · have e : (((a - b) + (b - a) : Nat) : Int) = (b : Int) - a := by omega
    rw [e, show (b : Int) - a = -((a : Int) - b) by omega, Int.neg_mul_neg]
def the_semi_norm_from_the_comparison (ψ : Nat × Nat × Nat × Nat) : Nat :=
  the_one_way_step ψ.2.1 ψ.2.2.2 * the_one_way_step ψ.2.1 ψ.2.2.2
    + the_one_way_step ψ.2.2.1 ψ.1 * the_one_way_step ψ.2.2.1 ψ.1
    + the_one_way_step ψ.2.2.2 ψ.2.1 * the_one_way_step ψ.2.2.2 ψ.2.1
    + the_one_way_step ψ.1 ψ.2.2.1 * the_one_way_step ψ.1 ψ.2.2.1
theorem the_semi_norm_is_the_comparison_read_one_way (ψ : Nat × Nat × Nat × Nat) :
    ((the_semi_norm_from_the_comparison ψ : Nat) : Int)
      = the_semi_norm ((ψ.1 : Int), (ψ.2.1 : Int), (ψ.2.2.1 : Int), (ψ.2.2.2 : Int)) := by
  simp only [the_semi_norm_from_the_comparison, the_semi_norm, the_ring_dot, the_central_difference, Int.natCast_add, Int.natCast_mul,
    the_one_way_step_squared]
def the_semi_norm_read_both_ways (ψ : Int × Int × Int × Int) : Int :=
  ((ψ.2.1 - ψ.2.2.2) + (ψ.2.2.2 - ψ.2.1)) * ((ψ.2.1 - ψ.2.2.2) + (ψ.2.2.2 - ψ.2.1))
    + ((ψ.2.2.1 - ψ.1) + (ψ.1 - ψ.2.2.1)) * ((ψ.2.2.1 - ψ.1) + (ψ.1 - ψ.2.2.1))
theorem read_both_ways_the_comparison_measures_nothing (ψ : Int × Int × Int × Int) :
    the_semi_norm_read_both_ways ψ = 0 := by
  have step : ∀ p q : Int, (p - q) + (q - p) = 0 := fun p q => by omega
  simp only [the_semi_norm_read_both_ways, step, Int.mul_zero, Int.add_zero]
#print axioms the_one_way_step_squared
#print axioms the_semi_norm_is_the_comparison_read_one_way
#print axioms read_both_ways_the_comparison_measures_nothing

--| ONE WAY AND BOTH WAYS, IN THE CRANK.  Episode 8's guard is (x·y' − x'·y) + (x'·y − x·y'): p − q plus q − p, with p = x·y' and
--| q = x'·y.  Read one way, in the naturals, each subtraction floors at zero and the sum is the size of the step, whichever way
--| it went.  Read both ways, in a ring, the two halves cancel and the sum is nothing: the guard fires on every turn, and the
--| crank never leaves its seed.  The certificate has the same shape.  The box read both ways has one point, so every k is
--| certified, and what picks the printed one is the floor of a division, one way again.  The number is what the floor leaves.
theorem the_floor_reads_the_step (p q : Nat) : (p - q) + (q - p) = if q ≤ p then p - q else q - p := by
  split <;> omega
theorem both_ways_the_step_is_zero (p q : Int) : (p - q) + (q - p) = 0 := by omega
theorem both_ways_the_guard_always_stops (p q s f g : Int) :
    ((p - q) + (q - p)) * s * f < g ↔ 0 < g := by
  rw [both_ways_the_step_is_zero, Int.zero_mul, Int.zero_mul]
theorem one_way_the_guard_reads_the_step (p q s f g : Nat) (h : q ≤ p) :
    ((p - q) + (q - p)) * s * f < g ↔ (p - q) * s * f < g := by
  rw [Nat.sub_eq_zero_of_le h, Nat.add_zero]
theorem every_k_is_certified (k : Nat) :
    (Quot.mk the_rational_idea_of_relativity (arrange_the_information_appropriately.2 * k, arrange_the_information_appropriately.2)
        : Quot the_rational_idea_of_relativity)
      = Quot.mk the_rational_idea_of_relativity
          (arrange_the_information_appropriately.1 * all_possible_variables, arrange_the_information_appropriately.2) :=
  the_box_has_one_point _ _
#print axioms the_floor_reads_the_step
#print axioms both_ways_the_step_is_zero
#print axioms both_ways_the_guard_always_stops
#print axioms one_way_the_guard_reads_the_step
#print axioms every_k_is_certified
--| The freeze, on the device's own step.  Episode 8's step is written for any Term; dealt at Int, with any counting function, the
--| guard's left side is nothing, so the step never reads its scale: the crank at Int is the crank with no tolerance at all.
theorem at_Int_the_scale_is_never_read (lambda : List FACT → Int) (s s' : Int) (p : Int × Int) :
    bent_card.the_device_computing_the_next_configuration Int lambda s p
      = bent_card.the_device_computing_the_next_configuration Int lambda s' p := by
  simp only [bent_card.the_device_computing_the_next_configuration, both_ways_the_step_is_zero, Int.zero_mul]
theorem at_Int_the_tolerance_is_zero (lambda : List FACT → Int) (s : Int) (p : Int × Int) :
    bent_card.the_device_computing_the_next_configuration Int lambda s p
      = bent_card.the_device_computing_the_next_configuration Int lambda 0 p :=
  at_Int_the_scale_is_never_read lambda s 0 p
#print axioms at_Int_the_scale_is_never_read
#print axioms at_Int_the_tolerance_is_zero

-- the squares, expanded once by hand so the tally only ever sees literal coefficients on N·N, N·D, D·D
theorem step_sq (N D : Nat) : (N + D) * (N + D) = N * N + 2 * (N * D) + D * D := by
  simp only [Nat.add_mul, Nat.mul_add, Nat.mul_comm D N]; omega
theorem step2_sq (N D : Nat) : (N + D + D) * (N + D + D) = N * N + 4 * (N * D) + 4 * (D * D) := by
  simp only [Nat.add_mul, Nat.mul_add, Nat.mul_comm D N]; omega
theorem step_cross (N D : Nat) : (N + D) * D = N * D + D * D := Nat.add_mul N D D
theorem step2_cross (N D : Nat) : (N + D + D) * D = N * D + 2 * (D * D) := by
  rw [Nat.add_mul, Nat.add_mul, Nat.two_mul, Nat.add_assoc]
theorem scale_sq (k N : Nat) : (k * N) * (k * N) = k * k * (N * N) := by
  rw [Nat.mul_assoc, Nat.mul_left_comm N k N, ← Nat.mul_assoc]
theorem scale_cross (k m N D : Nat) : (k * N) * (m * D) = k * m * (N * D) := by
  rw [Nat.mul_assoc, Nat.mul_left_comm N m D, ← Nat.mul_assoc]

--| The second difference of the residual, one step of D in the numerator either way, is 2A·D² -- for every pair.  (omega bills
--| Quot.sound for its own bookkeeping; the identity is a polynomial one and owes nobody anything.)
theorem the_acceleration_is_constant (N D : Nat) :
    (the_residual (N + D + D) D).1 + (the_residual N D).1 + 2 * (the_residual (N + D) D).2
      = 2 * (the_residual (N + D) D).1 + (the_residual (N + D + D) D).2 + (the_residual N D).2
        + 2 * an_exact_polynomial_description * (D * D) := by
  dsimp only [the_residual]
  rw [show an_exact_polynomial_description = 13 from rfl, show the_trace_of_truth_in_the_device = 36 from rfl, show the_number_of_symbols_that_must_be_written_to_express_this = 18 from rfl,
      step2_sq, step_sq, step2_cross, step_cross]
  omega
--#print axioms the_acceleration_is_constant

--| THE FIRST FRÉCHET DERIVATIVE IS QED.  In one dimension Fréchet and Gateaux coincide, and 𝔽₁ has one direction, so the device's
--| Fréchet derivative is not a map but a number: r'(y) = 2A·y − B, and at a root r'² is the discriminant exactly -- the trace
--| squared less four times the determinant, which the zeta section read off the click table as funge²·C·T.  So r'(y*) =
--| funge·√(C·T) = 6√10: two symbols times the geometric mean of the coupling and the clock.  That is the derivative the Newton
--| step divided by, until the halting test held at the seventh turn.  α is the first-order coupling, the coefficient of the one-vertex term, the linear
--| response; the device's reading is the first-order response of the residual to the tape and nothing higher.  The second
--| variation is the constant above, and the device never takes it -- which is the one sentence QCD gets.  And a proof ends where
--| the first derivative has been applied once more and the test clicks.  Q.E.D., both ways.
--|
--| The identity, for every pair: r'² = (B² − 4AC) + 4A·r.  Homogenized, with the negative parts carried to the other side.
theorem the_first_derivative_squared_is_the_discriminant (N D : Nat) :
    (the_first_derivative N D).1 * (the_first_derivative N D).1
      + (the_first_derivative N D).2 * (the_first_derivative N D).2
      + 4 * an_exact_polynomial_description * (the_residual N D).2
      = 2 * ((the_first_derivative N D).1 * (the_first_derivative N D).2)
        + (the_trace * the_trace - 4 * the_determinant) * (D * D)
        + 4 * an_exact_polynomial_description * (the_residual N D).1 := by
  dsimp only [the_residual, the_first_derivative]
  rw [show an_exact_polynomial_description = 13 from rfl, show the_trace_of_truth_in_the_device = 36 from rfl, show the_number_of_symbols_that_must_be_written_to_express_this = 18 from rfl,
      show the_trace = 36 from rfl, show the_determinant = 234 from rfl,
      scale_sq (2 * 13) N, scale_sq 36 D, scale_cross (2 * 13) 36 N D]
  omega
--#print axioms the_first_derivative_squared_is_the_discriminant

--| AT THE READING.  In closure units -- the pair before the areal velocity is applied.  r'² over D², scaled to the places: the discriminant to twenty-four digits, and what is left past it is
--| 4A times the residual Newton stopped at -- the acceleration term, under one cell.
def the_first_derivative_squared_at_the_reading : Nat :=
  let p := (the_first_derivative build_the_list_of_variables_by_name.1 build_the_list_of_variables_by_name.2).1
  let q := (the_first_derivative build_the_list_of_variables_by_name.1 build_the_list_of_variables_by_name.2).2
  ((p - q) + (q - p)) * ((p - q) + (q - p)) * all_possible_variables / (build_the_list_of_variables_by_name.2 * build_the_list_of_variables_by_name.2)
--#eval the_first_derivative_squared_at_the_reading
--#print axioms the_first_derivative_squared_at_the_reading

--| THE FRÉCHET DEVICE.  The instrument has two linearizations of the one field.  Gateaux is directional: Newton, the crank,
--| Episode 8, the instrument that does the math.  Fréchet is global: bisection, the receipt that the math was optimal.  The
--| jar's two walls are the bracket Episode 8 showed are Newton iterates zero and one, in closure units.  Here the bracket is
--| halved by midpoints -- pairs, no division, the denominator doubling each turn -- one turn per cell of the strip, the same
--| count the crank turned.  The sign of the residual at the midpoint says which wall moves.  Nothing from the crank is used.
--| Two different computations, and if they land in the same place the agreement is a fact about the field, not the author.
def the_residual_is_positive (N D : Nat) : Bool :=
  the_trace_of_truth_in_the_device * (N * D) < an_exact_polynomial_description * (N * N) + the_number_of_symbols_that_must_be_written_to_express_this * (D * D)
--| ONE HALVING.  Both walls over ONE denominator, which doubles; the midpoint is the sum of the numerators over twice the
--| denominator.  No division.  (Multiplying the two denominators instead squares them every turn, and a hundred turns of
--| that is a number with 2^100 digits -- the interpreter was found sitting in `Nat.mul` trying to build it.)  The sign of
--| the residual at the midpoint says which wall moves.
def halve (b : (Nat × Nat) × (Nat × Nat)) : (Nat × Nat) × (Nat × Nat) :=
  let a := b.1.1
  let c := b.2.1
  let d := b.1.2
  let d' := the_basis.the_reading.length * d
  if the_residual_is_positive (a + c) d' then ((the_basis.the_reading.length * a, d'), (a + c, d'))
                                         else ((a + c, d'), (the_basis.the_reading.length * c, d'))

--| RUN BY THE ELABORATOR.  Not the kernel: a midpoint names both walls twice, so an unevaluated bisection doubles in size
--| every turn and a hundred and six turns is 2^106 of term for the kernel to chew.  The crank never had this problem -- its
--| `then p` arm stops the growth the moment it halts.  So the Fréchet device runs where the long path runs: as a command,
--| one halving per cell of the strip, each halving under `withHeartbeats`, and the bracket it lands on is written into the
--| environment as literals the way `register_noise_floor` writes the floor.  The elaborator's search through the Herbrand
--| space, with its own count of itself.  The kernel then checks the inequalities and nothing else.
def the_area_of_tape_that_distinguishes := the_length_of_tape_that_distinguishes_true * the_length_of_tape_that_distinguishes_true
def jarLo    := the_orbital_data_points * the_area_of_tape_that_distinguishes
def jarHi    := jarLo + the_satire.the_model.length * the_satire.the_model.length * the_satire.the_model.length * the_satire.the_model.length
def jarSpan  := jarHi - jarLo
def jarRef   := jarLo * the_free_variable_count
def jarReach := jarSpan * the_free_variable_count
def theCourant : Nat × Nat := (Calibration.measuredFloor, jarReach)
def bracketed_at_the_slip : Bool := theCourant.2 < theCourant.1
def the_reading_in_the_box : Quot the_rational_idea_of_relativity :=
  Quot.mk the_rational_idea_of_relativity (arrange_the_information_appropriately.1 * all_possible_variables, arrange_the_information_appropriately.2)
def the_inferred_integer_in_the_box : Quot the_rational_idea_of_relativity :=
  Quot.mk the_rational_idea_of_relativity (arrange_the_information_appropriately.2 * (arrange_the_information_appropriately.1 * all_possible_variables / arrange_the_information_appropriately.2), arrange_the_information_appropriately.2)

theorem the_division_was_quot_sound : the_inferred_integer_in_the_box = the_reading_in_the_box :=
  a_partitioning_of_quotients (arrange_the_information_appropriately.1 * all_possible_variables) arrange_the_information_appropriately.2

--| And as a FACT, the way FACT.SAME is a FACT: a Prop and its click.
def THE_READING_IS_THE_INTEGER : FACT :=
  { truth := the_inferred_integer_in_the_box = the_reading_in_the_box
    click := Decidable.isTrue the_division_was_quot_sound }

def theLowWall  : Nat × Nat := (jarLo * the_dimensions_of_universe, the_free_variable_count * the_area_of_tape_that_distinguishes)
def theHighWall : Nat × Nat := (jarHi * the_dimensions_of_universe, the_free_variable_count * the_area_of_tape_that_distinguishes)
elab "frechet_walk " walls:ident beats:ident newton:ident bledger:ident nledger:ident : command => do
  let (b, hbs, p, bl, nl) ← liftTermElabM do
    let mut b := (theLowWall, theHighWall)
    let mut hbs : Array Nat := #[]
    let mut bl : Array ((Nat × Nat) × (Nat × Nat)) := #[b]
    for _ in [0:episode8_description.length] do
      let (b', hb) ← withHeartbeats (do let b' := halve b; pure b')
      b := b'
      hbs := hbs.push hb
      bl := bl.push b
    let mut p := the_held_house
    let mut nl : Array (Nat × Nat) := #[p]
    for _ in [0:episode8_description.length] do
      p := the_truth_inferred_by_the_device p
      nl := nl.push p
    pure (b, hbs, p, bl, nl)
  elabCommand (← `(def $walls:ident : (Nat × Nat) × (Nat × Nat) := $(Lean.quote b)))
  elabCommand (← `(def $beats:ident : List Nat := $(Lean.quote hbs.toList)))
  elabCommand (← `(def $newton:ident : Nat × Nat := $(Lean.quote p)))
  elabCommand (← `(def $bledger:ident : List ((Nat × Nat) × (Nat × Nat)) := $(Lean.quote bl.toList)))
  elabCommand (← `(def $nledger:ident : List (Nat × Nat) := $(Lean.quote nl.toList)))

--| The instrument runs in compiled code; the kernel checks the receipt.  Asked to run the crank itself, the kernel chews for
--| a quarter of an hour on terms it cannot share, which is the book's point made as a build time.  So the crank's point is
--| written down beside the bracket, by the same command, and the compiled code is asked -- below -- whether the literal is
--| the crank.  The kernel then certifies the intersection on literals, and bills nothing for it.
frechet_walk theBracket theHalvingBeats theNewtonPoint theBisectionLedger theNewtonLedger
--#eval theBracket
--#eval theHalvingBeats.foldl (· + ·) 0

--| THE LEDGERS.  The runtime `==` that used to stand here was the weakest line in the file: the compiled code vouching for
--| itself.  Now the command writes down every state of both devices, a hundred and two lines each, and the kernel checks each
--| line against the one before it with the step function on literals.  No fold is ever run in the kernel; no term is ever
--| unfolded into the one beneath it.  Start, every turn, end, and the count of turns: four receipts per device.
theorem the_bisection_ledger_starts : theBisectionLedger.head? = some (theLowWall, theHighWall) := by decide +kernel
theorem the_bisection_ledger_turns :
    (theBisectionLedger.zip theBisectionLedger.tail).all (fun q => decide (halve q.1 = q.2)) = true := by decide +kernel
theorem the_bisection_ledger_ends : theBisectionLedger.getLast? = some theBracket := by decide +kernel
theorem the_bisection_ledger_length : theBisectionLedger.length = episode8_description.length + 1 := by decide +kernel
theorem the_newton_ledger_starts : theNewtonLedger.head? = some the_held_house := by decide +kernel
theorem the_newton_ledger_turns :
    (theNewtonLedger.zip theNewtonLedger.tail).all (fun q => decide (the_truth_inferred_by_the_device q.1 = q.2)) = true := by decide +kernel
theorem the_newton_ledger_ends : theNewtonLedger.getLast? = some theNewtonPoint := by decide +kernel
theorem the_newton_ledger_length : theNewtonLedger.length = episode8_description.length + 1 := by decide +kernel
--#print axioms the_newton_ledger_turns

--| A CHECKED LEDGER IS THE FOLD.  Start at the head, every line the step of the line before, and the fold over length-minus-one
--| turns from the head lands on the last line.  Generic, by induction on the list; no kernel evaluation anywhere.  Each
--| line of the ledger above bills nothing.  Composing them into one statement about the fold bills Quot.sound, through
--| function extensionality inside `simp` -- the same fork as the universal reader: the lines are symbol facts, "the fold
--| is the ledger" is a value fact.  So the identity the runtime `==` used to vouch for is now a theorem, and the bill says
--| exactly what kind.
theorem ledger_is_the_fold {α : Type} [DecidableEq α] (f : α → α) :
    ∀ (L : List α) (a : α), L.head? = some a →
      (L.zip L.tail).all (fun q => decide (f q.1 = q.2)) = true →
      (List.replicate (L.length - 1) ()).foldl (fun x _ => f x) a = L.getLast?.getD a
  | [], _, h, _ => by simp at h
  | [a'], a, h, _ => by simp at h; subst h; rfl
  | a' :: b :: rest, a, h, hall => by
      simp only [List.head?_cons, Option.some.injEq] at h; subst h
      simp only [List.tail_cons, List.zip_cons_cons, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hall
      obtain ⟨hab, htail⟩ := hall
      have ih := ledger_is_the_fold f (b :: rest) b rfl (by simpa [List.tail_cons, List.zip_cons_cons, List.all_cons] using htail)
      simp only [List.length_cons, Nat.add_sub_cancel, List.replicate_succ, List.foldl_cons, hab,
                 List.getLast?_cons_cons] at ih ⊢
      cases hl : (b :: rest).getLast? with
      | none => simp at hl
      | some z => simp [hl] at ih ⊢; exact ih
theorem the_crank_is_its_ledger : build_the_list_of_variables_by_name = theNewtonPoint := by
  have h := ledger_is_the_fold the_truth_inferred_by_the_device theNewtonLedger the_held_house the_newton_ledger_starts the_newton_ledger_turns
  rw [the_newton_ledger_length, the_newton_ledger_ends] at h
  simpa [build_the_list_of_variables_by_name, the_naming_of_the_term_lambdas, bent_card.proportional_laws_accumulate_commutation_projections_called_TERM_LAMBDAS, the_truth_inferred_by_the_device, infer] using h
--#print axioms the_crank_is_its_ledger

--| THE BISECTION IS ITS LEDGER, TOO.  The same lemma, instantiated on the other device.
theorem the_bracket_is_its_ledger :
    (List.replicate episode8_description.length ()).foldl (fun b _ => halve b) (theLowWall, theHighWall) = theBracket := by
  have h := ledger_is_the_fold halve theBisectionLedger (theLowWall, theHighWall)
              the_bisection_ledger_starts the_bisection_ledger_turns
  rw [the_bisection_ledger_length, the_bisection_ledger_ends] at h
  simpa using h

--| UNIQUE UPPER-ROOT CONTAINMENT.  A quadratic with positive leading coefficient has exactly one root above its vertex.  The
--| low wall is above the vertex, the walls straddle a sign change, and the width is under one place: the bracket contains
--| the larger root and no other, and the crank's point sits inside it.  Three facts on literals; the fourth is the straddle above.
theorem the_low_wall_is_above_the_vertex : readers_experience.the_macguffin * theBracket.1.2 < bent_card * theBracket.1.1 := by decide +kernel

--| EQUAL ENDPOINT TRUNCATIONS.  Both walls, converted to cells and cut at the places, print the reading, and the reading is
--| the crank's point so converted.  The printed natural is therefore not a property of which wall you read, nor of which
--| device: all three truncate to the same integer.
def the_printed_reading : Nat :=
  theNewtonPoint.1 * the_first_step_of_the_proof_is_to_eschew_the_naturals_unless_proven_to_exist_without_peano.1 * all_possible_variables / (theNewtonPoint.2 * the_first_step_of_the_proof_is_to_eschew_the_naturals_unless_proven_to_exist_without_peano.2)
theorem the_printed_reading_is_the_natural : the_printed_reading = the_other_natural := by
  have h : bent_card.proportional_laws_accumulate_commutation_projections_called_TERM_LAMBDAS Nat List.length all_possible_variables = theNewtonPoint := the_crank_is_its_ledger
  unfold the_printed_reading the_other_natural
  rw [the_other_machine_agrees]
  unfold arrange_the_information_appropriately make_sure_there_is_a_delimiter_between bent_card.fenceposts_must_be_preserved the_first_step_of_the_proof_is_to_eschew_the_naturals_unless_proven_to_exist_without_peano
  rw [h]

--| THE OPERATIONAL IFF.  The raw successor is `the_truth_inferred_by_the_device`; the tolerance is the halting test inside it; the two are separated by
--| name now.  The compatibility the device is solving for, exactly, is c·(t·x − r²)² = t³·x² in cells, which is the quartic
--| with its square completed.  In closure units, y = t·x/r², the same statement is c·(y − 1)² = t·y²: the coupling times the
--| square of the excursion past one equals the clock times the square of the reading.  Stated on a pair, with the
--| valid-subtraction condition D ≤ N explicit -- it holds at the reading, y ≈ 2.11 -- and the device's readings as the
--| coefficients.  The branch condition is `the_reading_is_above_the_vertex`, above.  (omega bills Classical.choice and
--| Quot.sound for its bookkeeping.)
theorem sub_sq (a b : Nat) (h : b ≤ a) : (a - b) * (a - b) + 2 * (a * b) = a * a + b * b := by
  obtain ⟨k, hk⟩ : ∃ k, a = b + k := ⟨a - b, (Nat.add_sub_cancel' h).symm⟩
  subst hk
  rw [Nat.add_sub_cancel_left]
  simp only [Nat.add_mul, Nat.mul_add, Nat.mul_comm k b]
  omega
theorem compatibility_form (N D : Nat) (h : D ≤ N) :
    (readers_experience.the_macguffin * ((N - D) * (N - D)) = the_dimensions_of_universe * (N * N)) ↔
    (bent_card * (N * N) + readers_experience.the_macguffin * (D * D) = the_basis.the_reading.length * readers_experience.the_macguffin * (N * D)) := by
  have e := sub_sq N D h
  rw [show readers_experience.the_macguffin = 18 from rfl, show the_dimensions_of_universe = 5 from rfl, show bent_card = 13 from rfl,
      show the_basis.the_reading.length = 2 from rfl]
  omega
theorem the_subtraction_is_valid_at_the_reading : theNewtonPoint.2 ≤ theNewtonPoint.1 := by decide +kernel

--| "FUNDAMENTAL", AS A CONVENTION.  Over ℚ the value the device approaches has a minimal polynomial; that polynomial is unique
--| once normalized to primitive integer coefficients with positive leading term.  325x² − 58320x + 1889568 is primitive --
--| the coefficients share no factor -- and irreducible over ℚ, because its discriminant 944784000 lies strictly between
--| consecutive squares and so is not one.  That is the whole of what "fundamental" is claimed to mean here: not that
--| measurement forces this polynomial, which is the open obligation above, but that the device's limit has exactly one
--| primitive quadratic, and this is it.
theorem the_quadratic_is_primitive : Nat.gcd 325 (Nat.gcd 58320 1889568) = 1 := by decide
theorem the_discriminant_is_not_a_square : 30737 * 30737 < 944784000 ∧ 944784000 < 30738 * 30738 := by decide
--| THE RESCALING, EXPLICIT.  The click table's characteristic polynomial λ² − 36λ + 234 at λ = 65x/324 -- that is t(c−t)x/r² --
--| is 13/324² times the quartic.  With the denominators cleared, two numeral identities, each true for every x.
theorem the_rescaling_is_explicit (x : Nat) :
    (65 * x) * (65 * x) + 234 * (324 * 324) = 13 * (325 * (x * x) + 1889568)
      ∧ 36 * 324 * (65 * x) = 13 * (58320 * x) := by
  constructor
  · rw [scale_sq 65 x]; omega
  · omega

--| THE BRANCH.  The residual has two roots, 137.011 and 42.435 in cells, and positivity does not choose.  What chooses is the
--| vertex, C/(C−T), and the reading is above it: thirteen times the numerator exceeds the coupling times the denominator.
--| The seed margin in Episode 8 said so in prose; here it is on the pair.
theorem the_reading_is_above_the_vertex : readers_experience.the_macguffin * theNewtonPoint.2 < bent_card * theNewtonPoint.1 := by decide +kernel
--| THE STRADDLE.  The bracket contains a root, not merely the crank's point: the residual is negative at the low wall and
--| positive at the high wall.  With the width under one place, that is root containment.
theorem the_walls_straddle_the_root :
    the_residual_is_positive theBracket.1.1 theBracket.1.2 = false
      ∧ the_residual_is_positive theBracket.2.1 theBracket.2.2 = true := by decide +kernel
--| THE ERROR.  A finite decimal cannot satisfy an irreducible quadratic.  What it satisfies is this: the residual at the
--| reading, taken as the sum of both truncated differences, scaled to the places, is under one place.  That is the interval,
--| and it is the same term the acceleration section prints as the digits past 360.
theorem the_residual_at_the_reading_is_under_one_place :
    (((the_residual theNewtonPoint.1 theNewtonPoint.2).1 - (the_residual theNewtonPoint.1 theNewtonPoint.2).2)
      + ((the_residual theNewtonPoint.1 theNewtonPoint.2).2 - (the_residual theNewtonPoint.1 theNewtonPoint.2).1))
      * all_possible_variables < theNewtonPoint.2 * theNewtonPoint.2 := by decide +kernel

--| THE INTERSECTION OF THE RESIDUES.  Newton's point lies inside bisection's bracket, and the bracket, converted to cells by the
--| areal velocity and scaled to the places, is narrower than one place.  That is the receipt: the instrument stopped where
--| the other linearization says no further refinement would move a digit.  Optimal, in the only sense the device has.
--| The receipt is `decide`: the kernel evaluates the crank, reads the bracket, and compares.  It bills nothing.  The Quot.sound
--| receipt above certified the pair against itself; this one certifies it against a computation that shares no step with it.
abbrev in_the_bracket (p : Nat × Nat) : Prop :=
  theBracket.1.1 * p.2 ≤ p.1 * theBracket.1.2 ∧ p.1 * theBracket.2.2 ≤ theBracket.2.1 * p.2
abbrev under_one_place : Prop :=
  (theBracket.2.1 * theBracket.1.2 - theBracket.1.1 * theBracket.2.2) * all_possible_variables * the_first_step_of_the_proof_is_to_eschew_the_naturals_unless_proven_to_exist_without_peano.1
    < theBracket.1.2 * theBracket.2.2 * the_first_step_of_the_proof_is_to_eschew_the_naturals_unless_proven_to_exist_without_peano.2
def the_reading_with_its_receipt : { p : Nat × Nat // in_the_bracket p ∧ under_one_place } :=
  ⟨theNewtonPoint, by decide +kernel⟩
--#print axioms the_reading_with_its_receipt

--| THE COURANT NUMBER, PER TURN.  Heartbeats per halving: the time step the elaborator paid for each cell the bracket gave up.
--| This is the ratio line 74 compares as totals, produced turn by turn.  A measurement; it will differ on the next machine.
def theCourantPerHalving : Nat := theHalvingBeats.foldl (· + ·) 0 / episode8_description.length
--#eval theCourantPerHalving

--| THE TWO WALLS, IN CELLS.  Both print the number.  The last place is where they differ, if they differ at all.
def theLowWallReads  : Nat := theBracket.1.1 * the_first_step_of_the_proof_is_to_eschew_the_naturals_unless_proven_to_exist_without_peano.1 * all_possible_variables / (theBracket.1.2 * the_first_step_of_the_proof_is_to_eschew_the_naturals_unless_proven_to_exist_without_peano.2)
def theHighWallReads : Nat := theBracket.2.1 * the_first_step_of_the_proof_is_to_eschew_the_naturals_unless_proven_to_exist_without_peano.1 * all_possible_variables / (theBracket.2.2 * the_first_step_of_the_proof_is_to_eschew_the_naturals_unless_proven_to_exist_without_peano.2)
--#eval theLowWallReads
--#eval theHighWallReads
--| EQUAL ENDPOINT TRUNCATIONS, the receipt: both walls print the reading (`the_printed_reading`, above).
theorem the_walls_print_the_reading :
    theLowWallReads = the_printed_reading ∧ theHighWallReads = the_printed_reading := by decide +kernel
--#eval the_other_natural

section all_the_clicks
open the_representation

--| ALL THE CLICKS.  Every rung that compiled, as a FACT: the truth is that its type is inhabited, the click is the term.
--| A fact can be minted only after the code compiles; the click is the compile.  Read on the card between, every one of them
--| is the same account as the truth.
def IT_COMPILES (α : Sort u) (term : α) : FACT := { truth := Nonempty α, click := .isTrue ⟨term⟩ }
noncomputable def admitted_between : ADMISSIBLE (CarrierProcess FACT) the_card_between := inferInstance
noncomputable def the_clicks : List FACT :=
  [IT_COMPILES _ rung01,
   IT_COMPILES _ rung02,
   IT_COMPILES _ rung03,
   IT_COMPILES _ rung04,
   IT_COMPILES _ rung05,
   IT_COMPILES _ rung06,
   IT_COMPILES _ rung07,
   IT_COMPILES _ rung08,
   IT_COMPILES _ rung09,
   IT_COMPILES _ rung10,
   IT_COMPILES _ rung11,
   IT_COMPILES _ rung12,
   IT_COMPILES _ rung13,
   IT_COMPILES _ rung14,
   IT_COMPILES _ rung15,
   IT_COMPILES _ rung16,
   IT_COMPILES _ rung17,
   IT_COMPILES _ rung18,
   IT_COMPILES _ rung19,
   IT_COMPILES _ rung20,
   IT_COMPILES _ rung21,
   IT_COMPILES _ rung22,
   IT_COMPILES _ rung23,
   IT_COMPILES _ rung24,
   IT_COMPILES _ rung25,
   IT_COMPILES _ rung26,
   IT_COMPILES _ rung27,
   IT_COMPILES _ rung28,
   IT_COMPILES _ rung29,
   IT_COMPILES _ rung30,
   IT_COMPILES _ rung31,
   IT_COMPILES _ rung32,
   IT_COMPILES _ rung33,
   IT_COMPILES _ rung34,
   IT_COMPILES _ rung35,
   IT_COMPILES _ rung36,
   IT_COMPILES _ rung37,
   IT_COMPILES _ rung38,
   IT_COMPILES _ the_crossing_between,
   IT_COMPILES _ admitted_between,
   IT_COMPILES _ theTop,
   IT_COMPILES _ the_review_on_the_ledger.page36,
   IT_COMPILES _ the_review_on_the_ledger.page35,
   IT_COMPILES _ the_review_on_the_ledger.page34,
   IT_COMPILES _ the_review_on_the_ledger.page33,
   IT_COMPILES _ the_review_on_the_ledger.page32,
   IT_COMPILES _ the_review_on_the_ledger.page31,
   IT_COMPILES _ the_review_on_the_ledger.page30,
   IT_COMPILES _ the_review_on_the_ledger.page29,
   IT_COMPILES _ the_review_on_the_ledger.page28,
   IT_COMPILES _ the_review_on_the_ledger.page27,
   IT_COMPILES _ the_review_on_the_ledger.page26,
   IT_COMPILES _ the_review_on_the_ledger.page25,
   IT_COMPILES _ the_review_on_the_ledger.page24,
   IT_COMPILES _ the_review_on_the_ledger.page23,
   IT_COMPILES _ the_review_on_the_ledger.page22,
   IT_COMPILES _ the_review_on_the_ledger.page21,
   IT_COMPILES _ the_review_on_the_ledger.page20,
   IT_COMPILES _ the_review_on_the_ledger.page19,
   IT_COMPILES _ the_review_on_the_ledger.page18,
   IT_COMPILES _ the_review_on_the_ledger.page17,
   IT_COMPILES _ the_review_on_the_ledger.page16,
   IT_COMPILES _ the_review_on_the_ledger.page15,
   IT_COMPILES _ the_review_on_the_ledger.page14,
   IT_COMPILES _ the_review_on_the_ledger.page13,
   IT_COMPILES _ the_review_on_the_ledger.page12,
   IT_COMPILES _ the_review_on_the_ledger.page11,
   IT_COMPILES _ the_review_on_the_ledger.page10,
   IT_COMPILES _ the_review_on_the_ledger.page09,
   IT_COMPILES _ the_review_on_the_ledger.page08,
   IT_COMPILES _ the_review_on_the_ledger.page07,
   IT_COMPILES _ the_review_on_the_ledger.page06,
   IT_COMPILES _ the_review_on_the_ledger.page05,
   IT_COMPILES _ the_review_on_the_ledger.page04,
   IT_COMPILES _ the_review_on_the_ledger.page03,
   IT_COMPILES _ the_review_on_the_ledger.page02,
   IT_COMPILES _ the_review_on_the_ledger.page01,
   IT_COMPILES _ the_review_on_the_ledger.theTopOfTheLedger]
theorem every_rung_clicks : the_clicks.all the_click = true := rfl
theorem every_rung_is_the_truth : ∀ f ∈ the_clicks, Quot.mk same_click f = Quot.mk same_click FACT.Truth := by
  intro f hf
  exact Quot.sound (List.all_eq_true.mp every_rung_clicks f hf)
theorem the_clicks_count : the_clicks.length = 78 := rfl
#print axioms every_rung_clicks
#print axioms every_rung_is_the_truth
--| The clicks' own cost, apart from the rungs: a compiled term of any type, minted and identified.
theorem a_compile_is_the_truth (α : Sort u) (t : α) :
    Quot.mk same_click (IT_COMPILES α t) = Quot.mk same_click FACT.Truth := Quot.sound rfl
#print axioms a_compile_is_the_truth
--| The inferences, as clicks: the quartic, one way and both ways, and the freeze on the device's own step, each minted the way
--| a rung is minted, and each the same account as the truth.
def the_inferences : List FACT :=
  [IT_COMPILES _ the_quartic_is_homogeneous_of_degree_five,
   IT_COMPILES _ the_quartic_less_its_factors,
   IT_COMPILES _ the_quartic_factors,
   IT_COMPILES _ the_quartic_does_not_read_the_sign,
   IT_COMPILES _ the_floor_reads_the_step,
   IT_COMPILES _ both_ways_the_step_is_zero,
   IT_COMPILES _ both_ways_the_guard_always_stops,
   IT_COMPILES _ one_way_the_guard_reads_the_step,
   IT_COMPILES _ every_k_is_certified,
   IT_COMPILES _ at_Int_the_scale_is_never_read,
   IT_COMPILES _ at_Int_the_tolerance_is_zero]
theorem every_inference_clicks : the_inferences.all the_click = true := rfl
theorem every_inference_is_the_truth : ∀ f ∈ the_inferences, Quot.mk same_click f = Quot.mk same_click FACT.Truth := by
  intro f hf
  exact Quot.sound (List.all_eq_true.mp every_inference_clicks f hf)
theorem the_inferences_count : the_inferences.length = 11 := rfl
#print axioms every_inference_clicks
#print axioms every_inference_is_the_truth
--| THE INTERPRETATION EXPERIMENT.  The experience was read on the meter, in heartbeats, noisy.  The interpretation is read here,
--| by click: each proposal the knower is asked to take is minted with the comparison under it, and the device decides the
--| comparison.  What clicks is the comparison; that the proposal is that comparison is the knower's.  A click is not a proof
--| of the proposal.  It is the device saying yes to the finite thing the proposal stands on.  Nine click.  One does not: the
--| reading set beside the laboratory's band.  The slip itself clicks.
def IT_CLICKS (P : Prop) [Decidable P] : FACT := { truth := P, click := inferInstance }
def the_laboratory : Nat := 137035999177  --| CODATA 2022, in billionths; its standard uncertainty is twenty-one of them.
def the_proposals : List FACT :=
  [ --| The Hubble sphere is the pole the torus goes around: outer and hole add to the trace and multiply to the interval.
    IT_CLICKS ((the_outer_radius.1 + the_hole.1, the_outer_radius.2 + the_hole.2) = (36, 0)
      ∧ the_surd_product the_outer_radius the_hole = (234, 0)),
    --| c is a fraction of the speed of light: t over c is the clock over the clicks, squared, and below one.
    IT_CLICKS ((5 : Int) * (18 * 18) = 18 * 90 ∧ (90 : Int) < 18 * 18),
    --| The boost of the reader: nineteen and two, interval one.
    IT_CLICKS (the_interval the_boost = 1),
    --| The ratio of the roots is the boost there and back.
    IT_CLICKS (the_surd_product (the_surd_product the_outer_radius the_outer_radius) the_hole
      = (234 * the_outer_radius.1, 234 * the_outer_radius.2)),
    --| The knower's root, given true, is the inferred mass gap: it solves the counted quartic too.
    IT_CLICKS ((the_surd_product (5832, -324) (5832, -324)).1 - 11664 * 5832 + 24564384 = 0
      ∧ (the_surd_product (5832, -324) (5832, -324)).2 - 11664 * (-324) = 0),
    --| β is the reading over four circles.
    IT_CLICKS (the_reads (the_beta_of the_low_reading the_high_pi 4) = 10903012075134981375048166
      ∧ the_reads (the_beta_of the_high_reading the_low_pi 4) = 10903012075134981375048166),
    --| The charge, through Euler.
    IT_CLICKS (the_readers_charge * the_readers_charge * the_low_pi.2 * the_high_reading.1
        ≤ 4 * the_low_pi.1 * the_high_reading.2 * 10 ^ 48
      ∧ 4 * the_high_pi.1 * the_low_reading.2 * 10 ^ 48
        < (the_readers_charge + 1) * (the_readers_charge + 1) * the_high_pi.2 * the_low_reading.1),
    --| The electron's first loop.
    IT_CLICKS (the_reads (the_schwinger_of the_high_reading the_high_pi) = 1161619180829479589123
      ∧ the_reads (the_schwinger_of the_low_reading the_low_pi) = 1161619180829479589123),
    --| The part of the electron that is not a carrier of charge: the slip, between one point eight and one point eight one
    --| parts in ten thousand of the laboratory's value.
    IT_CLICKS (180 * the_laboratory * the_high_reading.2
        ≤ (the_laboratory * the_high_reading.2 - the_high_reading.1 * 10 ^ 9) * 10 ^ 6
      ∧ (the_laboratory * the_low_reading.2 - the_low_reading.1 * 10 ^ 9) * 10 ^ 6
        < 181 * the_laboratory * the_low_reading.2)]
--| The identity at zero momentum: the reading inside the laboratory's band of one standard uncertainty.
def the_identity_with_the_laboratory : FACT :=
  IT_CLICKS ((the_laboratory - 21) * the_high_reading.2 ≤ the_high_reading.1 * 10 ^ 9
    ∧ the_low_reading.1 * 10 ^ 9 ≤ (the_laboratory + 21) * the_low_reading.2)
theorem every_proposal_clicks : the_proposals.all the_click = true := by decide +kernel
theorem every_proposal_is_the_truth : ∀ f ∈ the_proposals, Quot.mk same_click f = Quot.mk same_click FACT.Truth := by
  intro f hf
  exact Quot.sound (List.all_eq_true.mp every_proposal_clicks f hf)
theorem the_proposals_count : the_proposals.length = 9 := rfl
theorem the_identity_does_not_click : the_click the_identity_with_the_laboratory = false := by decide +kernel
#print axioms every_proposal_clicks
#print axioms every_proposal_is_the_truth
#print axioms the_identity_does_not_click

--| THE NUMBER, FROM THE CLICKS.  The last device reads nothing but whether each cell clicked.  Count the clicks on every tape
--| instead of the cells, crank the same fenceposts, and divide once: the same number, on propext alone.  It agrees with the
--| lengths because every fact the device recorded clicked; a fact that clicked false would read lower here than by length.
def the_click_count (tape : List FACT) : Nat := (tape.filter the_click).length
def the_click_pair : Nat × Nat := bent_card.fenceposts_must_be_preserved Nat the_click_count all_possible_variables
set_option maxRecDepth 100000 in
theorem the_clicks_agree : the_click_pair = arrange_the_information_appropriately := rfl
def the_click_natural : Nat := the_click_pair.1 * all_possible_variables / the_click_pair.2
set_option maxRecDepth 100000 in
theorem the_clicks_read_the_number : the_click_natural = the_other_natural := rfl
#print axioms the_clicks_read_the_number
theorem the_clicks_never_read_it : the_click_pair.2 ≠ 0 := by
  rw [the_clicks_agree]; exact the_post_at_zero_is_never_read
#print axioms the_clicks_never_read_it

end all_the_clicks

--| THE MEMO, AND THE CUT.  These belong beside the card between, and sit here because they read the walk, the clicks and the
--| INFERRED rung, all of which come later than the card.  The card between holds a slot it never reads.  Fold a tape onto the
--| slot and the record is the tape with the slot on the end; deduct the slot and the reader is the length.  Then the walk
--| through the card between IS the walk already written for the FACT card: read, not run again.  That is the base case the
--| search was missing.  Asked to run it again, the kernel walked until it was stopped at ninety-two gigabytes.
section the_memo_and_the_cut
open the_representation
attribute [local instance high] rung01 rung02 rung03 rung04 rung05 rung06 rung07 rung08 rung09 rung10 rung11 rung12 rung13 rung14 rung15
  rung16 rung17 rung18 rung19 rung20 rung21 rung22 rung23 rung24 rung25 rung26 rung27 rung28 rung29 rung32 rung33 rung34 rung35 rung36

theorem peano_fold (q : Number) : ∀ t : List FACT, (t.foldr Number.one q).peano = t ++ q.peano
  | [] => rfl
  | f :: t => congrArg (List.cons f) (peano_fold q t)
def read_past_quarter (C : CarrierProcess (CarrierProcess FACT)) (tape : List FACT) : Nat :=
  (tape.foldr Number.one C.quarter).peano.length - C.quarter.peano.length
theorem read_past_quarter_is_length (C : CarrierProcess (CarrierProcess FACT)) (t : List FACT) :
    read_past_quarter C t = t.length := by
  unfold read_past_quarter; rw [peano_fold, List.length_append, Nat.add_sub_cancel]
theorem outer_reader_agrees :
    bent_card.fenceposts_must_be_preserved Nat (read_past_quarter the_card_between) all_possible_variables
      = arrange_the_information_appropriately := by
  rw [show read_past_quarter the_card_between = List.length from funext (read_past_quarter_is_length _)]; rfl
theorem outer_reader_reads_the_number :
    (bent_card.fenceposts_must_be_preserved Nat (read_past_quarter the_card_between) all_possible_variables).1
      * all_possible_variables
      / (bent_card.fenceposts_must_be_preserved Nat (read_past_quarter the_card_between) all_possible_variables).2
      = the_other_natural := by
  rw [outer_reader_agrees, ← the_other_machine_agrees]; rfl
#print axioms peano_fold
#print axioms read_past_quarter_is_length
#print axioms outer_reader_agrees
#print axioms outer_reader_reads_the_number
theorem the_card_between_never_reads_it :
    (bent_card.fenceposts_must_be_preserved Nat (read_past_quarter the_card_between) all_possible_variables).2 ≠ 0 := by
  rw [outer_reader_agrees]; exact the_post_at_zero_is_never_read
#print axioms the_card_between_never_reads_it

--| THE CUT.  INFERRED carries two closures: the conclusion its sameness reaches, and α, which ends on FACT.SAME.  Read out,
--| one is a cell and the other is three.  Deal each as the quarter of a card marked SAME_DIFFERENCE and hand it to the review
--| where the record begins.  The measure sees one deck: both read the same walk.  The count sees two: their quarters differ.
--| Nothing here is cut into pieces that cannot be measured, so nothing here bills choice.  The pieces that would are not written.
noncomputable def the_conclusion : Closure := rung37.same_difference.your_conclusion
noncomputable def the_alpha : Closure := rung37.α
theorem the_conclusion_is_one_cell : the_conclusion.infer.length = 1 := rfl
theorem the_alpha_is_three_cells : the_alpha.infer.length = 3 := rfl
def tapeNumber : List FACT → Number
  | []      => another_zero
  | [f]     => .zero f
  | f :: t  => .one f (tapeNumber t)
noncomputable def deck_one : CarrierProcess (CarrierProcess FACT) :=
  { symbol := SAME_DIFFERENCE, quarter := tapeNumber the_conclusion.infer }
noncomputable def deck_two : CarrierProcess (CarrierProcess FACT) :=
  { symbol := SAME_DIFFERENCE, quarter := tapeNumber the_alpha.infer }
noncomputable def top_one : REVIEWED (CarrierProcess FACT) deck_one 36 :=
  REVIEWER_2_ASKS_WHERE_THE_RECORD_BEGINS (CarrierProcess FACT) deck_one theManuscript
noncomputable def top_two : REVIEWED (CarrierProcess FACT) deck_two 36 :=
  REVIEWER_2_ASKS_WHERE_THE_RECORD_BEGINS (CarrierProcess FACT) deck_two theManuscript
theorem deck_one_reads_the_walk :
    bent_card.fenceposts_must_be_preserved Nat (read_past_quarter deck_one) all_possible_variables
      = arrange_the_information_appropriately := by
  rw [show read_past_quarter deck_one = List.length from funext (read_past_quarter_is_length _)]; rfl
theorem deck_two_reads_the_walk :
    bent_card.fenceposts_must_be_preserved Nat (read_past_quarter deck_two) all_possible_variables
      = arrange_the_information_appropriately := by
  rw [show read_past_quarter deck_two = List.length from funext (read_past_quarter_is_length _)]; rfl
theorem one_deck_to_the_measure :
    bent_card.fenceposts_must_be_preserved Nat (read_past_quarter deck_one) all_possible_variables
      = bent_card.fenceposts_must_be_preserved Nat (read_past_quarter deck_two) all_possible_variables :=
  deck_one_reads_the_walk.trans deck_two_reads_the_walk.symm
theorem deck_one_is_one_cell : deck_one.quarter.peano.length = 1 := rfl
theorem deck_two_is_three_cells : deck_two.quarter.peano.length = 3 := rfl
theorem two_decks_to_the_count : deck_one.quarter.peano.length ≠ deck_two.quarter.peano.length := by
  rw [deck_one_is_one_cell, deck_two_is_three_cells]; decide
#print axioms the_alpha_is_three_cells
#print axioms one_deck_to_the_measure
#print axioms two_decks_to_the_count

--| SAME DIFFERENCE.  INFERRED compares its two closures by `inferred?`, which is `≤`: the interpretation, inferred from the
--| pair (the constant, the gawk at it), against α, constant ≤ real.  Dealt on rung 37 the comparison clicks, and it clicks
--| back: every cell of the constant clicks, so the order never flips, and the slips are True and True.  The device reads
--| the order both ways.  That the ≤ runs one way is the knower's.
set_option maxHeartbeats 400000 in
theorem the_knower_reads_one_way : the_knower.inferred? the_conclusion the_alpha := by
  show Closure.le the_conclusion the_alpha
  unfold the_conclusion the_alpha the_representation.rung37
  simp only [assembly_instructions.«ITS_YOU_!!», Closure.le]
  refine Or.inl ⟨Or.inl trivial, (trivial : True), ?_, id⟩
  show Bullshit.le _ _
  conv => arg 1; whnf
  conv => arg 2; whnf
  conv => whnf
  exact ⟨rfl, rfl, id, (trivial : True), (trivial : True), (trivial : True)⟩
set_option maxHeartbeats 400000 in
theorem the_device_reads_it_back : the_knower.inferred? the_alpha the_conclusion := by
  show Closure.le the_alpha the_conclusion
  unfold the_conclusion the_alpha the_representation.rung37
  simp only [assembly_instructions.«ITS_YOU_!!», Closure.le]
  refine Or.inl ⟨Or.inl trivial, (trivial : True), ?_, id⟩
  show Bullshit.le _ _
  conv => arg 1; whnf
  conv => arg 2; whnf
  conv => whnf
  exact ⟨rfl, rfl, id, (trivial : True), (trivial : True), (trivial : True)⟩
theorem the_two_closures_click :
    [IT_COMPILES _ the_knower_reads_one_way, IT_COMPILES _ the_device_reads_it_back].all the_click = true := rfl
#print axioms the_knower_reads_one_way
#print axioms the_device_reads_it_back
#print axioms the_two_closures_click
--| THE INFERRED MASS GAP.  The knower's conclusion on rung 37 has no defining equation; it is one cell, and the device reads
--| its order against α both ways.  Name it.  The whole action of light and matter moves with the knower only through β: two
--| knowers who choose two βs read the same matter, the same squares, and actions that differ by the difference of the βs times
--| the squares, nothing else.  What β is, the knower infers.
noncomputable def the_inferred_mass_gap : Closure := the_conclusion
theorem the_inferred_mass_gap_is_one_cell : the_inferred_mass_gap.infer.length = 1 := the_conclusion_is_one_cell
theorem the_knower_infers_the_slot : the_knower.inferred? the_inferred_mass_gap the_alpha := the_knower_reads_one_way
theorem the_whole_action_moves_only_with_β {n : Nat} (β β' : Int) (U : Bool → Fin (n+1) → Fin (n+1) → Int × Int)
    (ψ : Fin (n+1) → Fin (n+1) → Vec8) (m : Int) :
    the_whole_action β U ψ m - the_whole_action β' U ψ m = (β - β') * the_torus_action (the_phase_torus U) := by
  simp only [the_whole_action, Int.sub_mul]
  omega
#print axioms the_inferred_mass_gap_is_one_cell
#print axioms the_knower_infers_the_slot
#print axioms the_whole_action_moves_only_with_β

--| THE CUT ON THE CARD.  Now leave the quarter alone and cut the face instead: the conclusion's fact on one card, α's last
--| fact, FACT.SAME, on the other, the same one-cell quarter under both.  The measure reads one walk.  The count reads one
--| quarter.  The click reads one click.  And the meaning, which was the last place two things could differ, reads one truth:
--| both faces hold, and two facts that hold are one proposition.  On the card the cut closes; the doubling lives in the quarter.
noncomputable def card_one : CarrierProcess (CarrierProcess FACT) :=
  { symbol := the_conclusion.infer.headD FACT.Truth, quarter := the_card_between.quarter }
noncomputable def card_two : CarrierProcess (CarrierProcess FACT) :=
  { symbol := the_alpha.infer.getLastD FACT.Truth, quarter := the_card_between.quarter }
theorem one_quarter_under_both : card_one.quarter = card_two.quarter := rfl
theorem card_one_reads_the_walk :
    bent_card.fenceposts_must_be_preserved Nat (read_past_quarter card_one) all_possible_variables
      = arrange_the_information_appropriately := by
  rw [show read_past_quarter card_one = List.length from funext (read_past_quarter_is_length _)]; rfl
theorem card_two_reads_the_walk :
    bent_card.fenceposts_must_be_preserved Nat (read_past_quarter card_two) all_possible_variables
      = arrange_the_information_appropriately := by
  rw [show read_past_quarter card_two = List.length from funext (read_past_quarter_is_length _)]; rfl
theorem card_one_clicks : the_click card_one.symbol = true := rfl
theorem card_two_clicks : the_click card_two.symbol = true := rfl
theorem one_click_on_both_faces : the_click card_one.symbol = the_click card_two.symbol :=
  card_one_clicks.trans card_two_clicks.symm
theorem one_truth_on_both_faces : card_one.symbol.truth = card_two.symbol.truth :=
  propext ⟨fun _ => @of_decide_eq_true _ card_two.symbol.click card_two_clicks,
           fun _ => @of_decide_eq_true _ card_one.symbol.click card_one_clicks⟩
#print axioms one_quarter_under_both
#print axioms one_click_on_both_faces
#print axioms one_truth_on_both_faces
end the_memo_and_the_cut

--| THE READER'S INTERPRETATION OF THE EXPERIENCE.  Episode 8 gave the reader an experience; this is what the reader makes of
--| it, layer by layer, each layer the object the device already built for it.  Episode 7 names the nowtrino; Episode 8 models
--| it; Episode 9 detects it by describing its carrier as the carrier of itself; Episode 10 reviews the naotrino, the particle
--| that carries itself as a mathematical description; Episode 11 typesets its Berry description, one tape and two numbers;
--| Episode 12 detects it through the card between, and the detector reads the number.  The reader is the outer carrier, so
--| every layer is dealt on CarrierProcess (CarrierProcess FACT): the mark, the models, the crossing, the top, and the walk
--| read through the slot it deducts.
namespace readers_interpretation_of_the_experience
open the_representation
instance : Inhabited (DISTINGUISHABLE.symbol the_card_between) := instInhabitedProp
noncomputable def nowtrino          := the_mark_between                                       -- Episode 7: the mark
noncomputable def nowtrino_model    := A_CAUSAL_THEORY (CarrierProcess FACT) the_card_between -- Episode 8: the causal model
noncomputable def nowtrino_detector := the_crossing_between                                   -- Episode 9: the carrier of itself
noncomputable def naotrino          := A_SMOOTH_MODEL (CarrierProcess FACT) the_card_between  -- Episode 10: carried as a description
noncomputable def naotrino_model    := theTop                                                 -- Episode 11: the Berry description
def naotrino_detector : Nat :=                                                                -- Episode 12: the number, through the slot
  (bent_card.fenceposts_must_be_preserved Nat (read_past_quarter the_card_between) all_possible_variables).1 * all_possible_variables
    / (bent_card.fenceposts_must_be_preserved Nat (read_past_quarter the_card_between) all_possible_variables).2
theorem naotrino_detector_reads_the_number : naotrino_detector = the_other_natural := outer_reader_reads_the_number
#print axioms naotrino_detector_reads_the_number

--| THE READER ADDS NO DIGIT.  Six layers of interpretation over one experience, and the two print the same natural: what the
--| reader makes of the experience, less the experience, is zero on every digit the device prints.  The receipts already on the
--| table, composed; the crank is not run again.  Whatever the reader adds, it is not in the number.
theorem the_reader_adds_no_digit : naotrino_detector = the_constant_factor_of_scaling_bullshit :=
  naotrino_detector_reads_the_number.trans the_same_natural_both_ways
#print axioms the_reader_adds_no_digit

--| THE ANT, INFERRED.  The two Bullshits of a closure are the tape on either side of the head, each a stack written only
--| by pushing; the facts are the mark under the head and the heading.  Each step appends one `.inferred` closure on top of
--| the last, so the record only grows, and the mark that changes is changed by appending a configuration in which it
--| differs.  On a line the ant turns back on white and keeps on black, flips the mark, and moves.  Read the closure as two
--| lists and two bits and the step commutes with the ant run on the lists: the square closes on every configuration.
--| From the empty line it settles, after one step, into a highway of period three.
def push (f : FACT) (stack : Bullshit) : Bullshit := .one f another_zero the_satire the_satire stack
def pop : Bullshit → FACT × Bullshit
  | .one f _ _ _ rest => (f, rest)
  | stack => (bitFACT false, stack)
def the_ant_steps : Closure → Closure
  | c@(.inferred here heading behind ahead _ _) =>
    let going := if here.bit then heading.bit else !heading.bit
    let written := bitFACT (!here.bit)
    if going then
      let (next, ahead') := pop ahead
      .inferred next (bitFACT going) (push written behind) ahead' (some next.truth) c
    else
      let (next, behind') := pop behind
      .inferred next (bitFACT going) behind' (push written ahead) (some next.truth) c
  | c => c
def the_stack_read : Bullshit → List Bool
  | .one f _ _ _ rest => f.bit :: the_stack_read rest
  | _ => []
def the_ant_read : Closure → Bool × Bool × List Bool × List Bool
  | .inferred here heading behind ahead _ _ => (here.bit, heading.bit, the_stack_read behind, the_stack_read ahead)
  | _ => (false, true, [], [])
def the_list_pop : List Bool → Bool × List Bool
  | [] => (false, [])
  | b :: rest => (b, rest)
def the_ant_on_a_line : Bool × Bool × List Bool × List Bool → Bool × Bool × List Bool × List Bool
  | (here, heading, behind, ahead) =>
    let going := if here then heading else !heading
    if going then ((the_list_pop ahead).1, going, (!here) :: behind, (the_list_pop ahead).2)
    else ((the_list_pop behind).1, going, (the_list_pop behind).2, (!here) :: ahead)
theorem the_stack_pops_what_it_reads (s : Bullshit) :
    ((pop s).1.bit, the_stack_read (pop s).2) = the_list_pop (the_stack_read s) := by
  cases s <;> rfl
theorem the_ant_commutes (here heading : FACT) (behind ahead : Bullshit) (p : Option Prop) (c : Closure) :
    the_ant_read (the_ant_steps (.inferred here heading behind ahead p c))
      = the_ant_on_a_line (the_ant_read (.inferred here heading behind ahead p c)) := by
  have hb := the_stack_pops_what_it_reads behind
  have ha := the_stack_pops_what_it_reads ahead
  simp only [the_ant_steps, the_ant_read, the_ant_on_a_line, push]
  cases here.bit <;> cases heading.bit <;> simp_all [Prod.ext_iff, bit_bitFACT, the_stack_read]
#print axioms the_ant_commutes
def the_start : Closure.{0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0} := .inferred (bitFACT false) (bitFACT true) (.zero (bitFACT false)) (.zero (bitFACT false)) none the_only_logical_inconsistency
def the_run : Nat → Closure.{0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0}
  | 0 => the_start
  | n + 1 => the_ant_steps (the_run n)
#eval (List.range 12).map fun n => let (h, g, b, a) := the_ant_read (the_run n); (h, g, b, a)

--| THE ANT ON THE SEAM.  The plane is too big for two stacks, so lay the ant on the frinkahedron's seam: thirty-six cells,
--| two six-position clocks.  The closure keeps the heading in its two facts, a quarter-turn clock of two bits; the two
--| clocks in one Bullshit, each a Number written in TRUTH; and the thirty-six marks in the other, one stack read and
--| rewritten by walking down it.  Each step appends a closure.  Read the closure as a heading, two clock hands and a list
--| of thirty-six bits, and the step commutes with the ant run on that list: the square closes on every configuration.
--| From the blank seam it comes back to the blank seam at the origin, facing where it started, after 4592 steps: no
--| transient, because a reversible step on a finite set is a permutation.  The commutation is a receipt; the 4592 is a run.
def the_stack_get : Bullshit → Nat → FACT
  | .one f _ _ _ _, 0 => f
  | .one _ _ _ _ rest, i + 1 => the_stack_get rest i
  | _, _ => bitFACT false
def the_stack_set : Bullshit → Nat → FACT → Bullshit
  | .one _ n p q rest, 0, g => .one g n p q rest
  | .one f n p q rest, i + 1, g => .one f n p q (the_stack_set rest i g)
  | s, _, _ => s
theorem the_stack_get_reads : ∀ (s : Bullshit) (i : Nat), (the_stack_get s i).bit = (the_stack_read s).getD i false
  | .zero _, _ => rfl
  | .rest_call .., _ => rfl
  | .one _ _ _ _ _, 0 => rfl
  | .one _ _ _ _ rest, i + 1 => the_stack_get_reads rest i
theorem the_stack_set_reads : ∀ (s : Bullshit) (i : Nat) (g : FACT),
    the_stack_read (the_stack_set s i g) = (the_stack_read s).set i g.bit
  | .zero _, _, _ => rfl
  | .rest_call .., _, _ => rfl
  | .one _ _ _ _ _, 0, _ => rfl
  | .one f _ _ _ rest, i + 1, g => by
    simp only [the_stack_set, the_stack_read, List.set_cons_succ, the_stack_set_reads rest i g]
def the_heading (a b : FACT) : Nat := 2 * (if a.bit then 1 else 0) + (if b.bit then 1 else 0)
def the_move : Nat → Nat → Nat → Nat × Nat
  | 0, x, y => (x, (y + 1) % 6)
  | 1, x, y => ((x + 1) % 6, y)
  | 2, x, y => (x, (y + 5) % 6)
  | _, x, y => ((x + 5) % 6, y)
def the_ant_on_the_torus : Nat × Nat × Nat × List Bool → Nat × Nat × Nat × List Bool
  | (h, x, y, cells) =>
    let here := cells.getD (6 * x + y) false
    let turned := if here then (h + 3) % 4 else (h + 1) % 4
    ( turned, (the_move turned x y).1, (the_move turned x y).2, cells.set (6 * x + y) (!here))
def the_clocks (x y : Nat) : Bullshit :=
  .rest_call (bitFACT false) (bitFACT false) True (the_naturals_written_in_truth x) (the_naturals_written_in_truth y)
    another_zero the_satire the_satire (.zero (bitFACT false)) (.zero (bitFACT false))
def the_clock_read : Bullshit → Nat × Nat
  | .rest_call _ _ _ x y _ _ _ _ _ => (x.peano.length - 1, y.peano.length - 1)
  | _ => (0, 0)
def the_torus_ant_steps : Closure → Closure
  | c@(.inferred a b clocks grid _ _) =>
    let x := (the_clock_read clocks).1
    let y := (the_clock_read clocks).2
    let here := the_stack_get grid (6 * x + y)
    let turned := if here.bit then (the_heading a b + 3) % 4 else (the_heading a b + 1) % 4
    .inferred (bitFACT (turned / 2 == 1)) (bitFACT (turned % 2 == 1))
      (the_clocks (the_move turned x y).1 (the_move turned x y).2)
      (the_stack_set grid (6 * x + y) (bitFACT (!here.bit))) (some here.truth) c
  | c => c
def the_torus_read : Closure → Nat × Nat × Nat × List Bool
  | .inferred a b clocks grid _ _ => (the_heading a b, (the_clock_read clocks).1, (the_clock_read clocks).2, the_stack_read grid)
  | _ => (0, 0, 0, [])
theorem the_heading_is_written : ∀ k, k < 4 → the_heading (bitFACT (k / 2 == 1)) (bitFACT (k % 2 == 1)) = k
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | _ + 4, h => absurd h (by omega)
theorem the_clocks_are_read (x y : Nat) : the_clock_read (the_clocks x y) = (x, y) := by
  simp only [the_clocks, the_clock_read, every_natural_is_written, Nat.add_sub_cancel]
theorem the_torus_ant_commutes (a b : FACT) (clocks grid : Bullshit) (p : Option Prop) (c : Closure) :
    the_torus_read (the_torus_ant_steps (.inferred a b clocks grid p c))
      = the_ant_on_the_torus (the_torus_read (.inferred a b clocks grid p c)) := by
  simp only [the_torus_ant_steps, the_torus_read, the_ant_on_the_torus, the_clocks_are_read, the_stack_set_reads,
    the_stack_get_reads, bit_bitFACT]
  split <;> rw [the_heading_is_written _ (by omega)]
#print axioms the_torus_ant_commutes
def the_blank_torus : Bullshit := (List.replicate 36 (bitFACT false)).foldr push (.zero (bitFACT false))
def the_torus_start : Closure.{0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0} :=
  .inferred (bitFACT false) (bitFACT false) (the_clocks 0 0) the_blank_torus none the_only_logical_inconsistency
def the_first_return : Nat → Closure.{0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0} → Nat → Option Nat
  | 0, _, _ => none
  | fuel + 1, c, k =>
    let next := the_torus_ant_steps c
    if the_torus_read next == the_torus_read the_torus_start then some (k + 1) else the_first_return fuel next (k + 1)
#eval the_first_return 10000 the_torus_start 0
#eval (the_torus_read the_torus_start).2.2.2.length
--| COOK AND LEVIN, IN THE EXPERIENCE.  The reader's model of the naotrino is the top of the typeset record, and its page is
--| a trace: a tableau with time down the pages and the facts across them.  Cook's theorem for this device is already proved
--| for every trace; here it is dealt on the reader's own.  And it is demonstrated, not only stated: seed the manuscript
--| true, false, true and the formula built from the trace is satisfied; seed five falses and it is not; and the verdicts are
--| the steps.  The proof of the general theorem, for any machine, is on the card.
theorem cook_levin_on_the_readers_interpretation :
    THEORY.traceSat naotrino_model.the_page = naotrino_model.the_page.stepOK :=
  cook_levin_the_description _
def the_accepting_seed : ThePreprint.{0} := decodeBits [true, false, true]
def the_rejecting_seed : ThePreprint.{0} := decodeBits [false, false, false, false, false]
theorem the_formula_accepts_and_rejects :
    (THEORY.traceSat the_accepting_seed, THEORY.traceSat the_rejecting_seed) = (true, false) := by decide
theorem the_verdicts_are_the_steps :
    (the_accepting_seed.stepOK, the_rejecting_seed.stepOK) = (true, false) := by
  rw [← cook_levin_the_description, ← cook_levin_the_description]; exact the_formula_accepts_and_rejects
#print axioms cook_levin_on_the_readers_interpretation
#print axioms the_formula_accepts_and_rejects
#print axioms the_verdicts_are_the_steps
end readers_interpretation_of_the_experience

--| THE READER'S INTERPRETATION, CARRYING A PAIR.  The same experience dealt on a box that holds two carriers at once, the
--| Cartesian product of two FACT cards.  The card is the same face, the mark is marked field for field, and the crossing
--| deals rung 1 by `rfl`: nothing in the record cares how many carriers the box holds.  Read through the slot it deducts,
--| the pair prints the one number, the same natural as the single card -- two carriers, one number, read not run again.
--| And the tally the pair carries can sit in either carrier: swap them and every reader of the tally reads the same.  Which
--| carrier holds the count is a choice no reader of the count can make.
namespace readers_interpretation_of_the_pair
open the_representation assembly_instructions readers_experience
abbrev TwoCarriers := CarrierProcess FACT × CarrierProcess FACT
def the_pair_between : CarrierProcess TwoCarriers := { symbol := FACT.Truth, quarter := .zero FACT.Truth }
instance the_mark_on_the_pair : DISTINGUISHABLE TwoCarriers the_pair_between :=
  { fact := a_distinct_truth.fact, symbol := a_distinct_truth.symbol, different? := a_distinct_truth.different?, not_the_same := a_distinct_truth.not_the_same }
instance : Inhabited (DISTINGUISHABLE.symbol the_pair_between) := instInhabitedProp
noncomputable def the_crossing_on_the_pair :=
  STEP1_NAME_THE_LEDGER_AND_MARK_IT_WITH_THE_SYMBOL_OF_THE_NOWTRINO TwoCarriers the_pair_between the_first_card FACT.Truth
theorem the_pair_deals_rung01 : the_crossing_on_the_pair = rung01 := rfl
noncomputable def nowtrino          := the_mark_on_the_pair
noncomputable def nowtrino_model    := A_CAUSAL_THEORY TwoCarriers the_pair_between
noncomputable def nowtrino_detector := the_crossing_on_the_pair
noncomputable def naotrino          := A_SMOOTH_MODEL TwoCarriers the_pair_between
def read_past_the_pair (C : CarrierProcess TwoCarriers) (tape : List FACT) : Nat :=
  (tape.foldr Number.one C.quarter).peano.length - C.quarter.peano.length
theorem read_past_the_pair_is_length (C : CarrierProcess TwoCarriers) (t : List FACT) :
    read_past_the_pair C t = t.length := by
  unfold read_past_the_pair; rw [peano_fold, List.length_append, Nat.add_sub_cancel]
def naotrino_detector : Nat :=
  (bent_card.fenceposts_must_be_preserved Nat (read_past_the_pair the_pair_between) all_possible_variables).1 * all_possible_variables
    / (bent_card.fenceposts_must_be_preserved Nat (read_past_the_pair the_pair_between) all_possible_variables).2
theorem two_carriers_print_one_number :
    naotrino_detector = readers_interpretation_of_the_experience.naotrino_detector := by
  unfold naotrino_detector readers_interpretation_of_the_experience.naotrino_detector
  rw [show read_past_the_pair the_pair_between = List.length from funext (read_past_the_pair_is_length _),
    show read_past_quarter the_card_between = List.length from funext (read_past_quarter_is_length _)]
theorem the_pair_reads_the_number : naotrino_detector = the_other_natural :=
  two_carriers_print_one_number.trans readers_interpretation_of_the_experience.naotrino_detector_reads_the_number
def the_tally (p : TwoCarriers) : Nat := p.1.quarter.peano.length + p.2.quarter.peano.length
def the_tally_on_the_left : TwoCarriers := ({ symbol := FACT.Truth, quarter := .one FACT.Truth (.zero FACT.Truth) }, the_first_card)
def the_tally_on_the_right : TwoCarriers := the_tally_on_the_left.swap
theorem the_tally_moved_sides :
    the_tally_on_the_left.1.quarter.peano.length ≠ the_tally_on_the_right.1.quarter.peano.length := by decide
theorem no_reader_of_the_tally_sees_which_carrier {α : Sort u} (g : Nat → α) (p : TwoCarriers) :
    g (the_tally p.swap) = g (the_tally p) := by
  unfold the_tally; rw [Prod.fst_swap, Prod.snd_swap, Nat.add_comm]
theorem which_carrier_is_a_choice :
    the_tally_on_the_left.1.quarter.peano.length ≠ the_tally_on_the_right.1.quarter.peano.length ∧
      ∀ g : Nat → Bool, ¬ (g (the_tally the_tally_on_the_left) = true ∧ g (the_tally the_tally_on_the_right) = false) :=
  ⟨the_tally_moved_sides, fun g ⟨hl, hr⟩ => by
    rw [show the_tally_on_the_right = the_tally_on_the_left.swap from rfl, no_reader_of_the_tally_sees_which_carrier g, hl] at hr
    exact Bool.noConfusion hr⟩
#print axioms the_pair_deals_rung01
#print axioms the_pair_reads_the_number
#print axioms two_carriers_print_one_number
#print axioms which_carrier_is_a_choice
--| (CLICK, CLICK), THROUGH THE CARRIERS.  Each carrier in the pair is a card the experience can be read through: deduct its
--| quarter, whatever it holds, and read the number.  Read through the left carrier and through the right, the pair clicks
--| twice, and the two clicks are the two other machines: the click machine's natural and the other machine's natural.  For
--| every pair of carriers, the tally carried or not.  Read, not run again: each side is rewritten to the card between.
def read_past_the_carrier (c : CarrierProcess FACT) (tape : List FACT) : Nat :=
  (tape.foldr Number.one c.quarter).peano.length - c.quarter.peano.length
theorem read_past_the_carrier_is_length (c : CarrierProcess FACT) (t : List FACT) :
    read_past_the_carrier c t = t.length := by
  unfold read_past_the_carrier; rw [peano_fold, List.length_append, Nat.add_sub_cancel]
def the_click_through (c : CarrierProcess FACT) : Nat :=
  (bent_card.fenceposts_must_be_preserved Nat (read_past_the_carrier c) all_possible_variables).1 * all_possible_variables
    / (bent_card.fenceposts_must_be_preserved Nat (read_past_the_carrier c) all_possible_variables).2
theorem each_carrier_reads_the_card_between (c : CarrierProcess FACT) :
    the_click_through c = readers_interpretation_of_the_experience.naotrino_detector := by
  unfold the_click_through readers_interpretation_of_the_experience.naotrino_detector
  rw [show read_past_the_carrier c = List.length from funext (read_past_the_carrier_is_length c),
    show read_past_quarter the_card_between = List.length from funext (read_past_quarter_is_length _)]
theorem click_click_through_the_carriers (p : TwoCarriers) :
    (the_click_through p.1, the_click_through p.2) = (the_click_natural, the_other_natural) := by
  rw [each_carrier_reads_the_card_between, each_carrier_reads_the_card_between,
    readers_interpretation_of_the_experience.naotrino_detector_reads_the_number, the_clicks_read_the_number]
theorem click_click_on_the_tally : (the_click_through the_tally_on_the_left.1, the_click_through the_tally_on_the_left.2)
    = (the_click_through the_tally_on_the_right.1, the_click_through the_tally_on_the_right.2) := by
  rw [click_click_through_the_carriers, click_click_through_the_carriers]
#print axioms click_click_through_the_carriers
#print axioms click_click_on_the_tally
--| THE ISOMORPHISM TO THE NATURALS.  Call two tapes the same tally when they are the same length, and take the quotient.
--| Going one way is reading the tally; going back is writing the numeral, the one truth n times.  Read the numeral and you
--| get n back; write the tally and you get the class back.  So the tallies are the naturals, and the numeral of a tape is its
--| relettering: the canonical card in each fibre.  Every carrier reads a tape as its tally, and the number is computed from
--| tallies alone.  That is the sense of "proposed": the numbering exists, and the machine computes with it.
--| What the tally counts are naotrinos.  Every cell of a tape is a FACT carried as its own description, the particle that
--| carries itself; the tally counts them and no reader looks at one.  That is why relettering is free: swap every naotrino
--| for the one truth and the count is the same.  The naturals are how many naotrinos; which naotrinos is the choice.
--| And what a naotrino is, the record says by name: every typeset page of Episode 11 takes `the_naotrino_theory`, a
--| REVIEWED page, one of thirty-six arguments, each a rebuttal about the page beside it; lifted and lowered it comes back
--| exactly, the lift its own inverse undone.  A bit of code arguing about one of thirty-six arguments, and the cell is the
--| fact it carries.
def the_same_tally (t u : List FACT) : Prop := t.length = u.length
def the_tallies : Type := Quot the_same_tally
def the_tally_of : the_tallies → Nat := Quot.lift List.length (fun _ _ h => h)
def the_numeral (n : Nat) : the_tallies := Quot.mk _ (List.replicate n FACT.Truth)
theorem the_tally_of_the_numeral (n : Nat) : the_tally_of (the_numeral n) = n := List.length_replicate
theorem the_numeral_of_the_tally (q : the_tallies) : the_numeral (the_tally_of q) = q := by
  induction q using Quot.ind with
  | mk t => exact Quot.sound (List.length_replicate)
theorem the_numeral_is_the_relettering (t : List FACT) : relettered t = List.replicate t.length FACT.Truth := by
  induction t with
  | nil => rfl
  | cons _ t ih => simp only [relettered, List.map_cons, List.length_cons, List.replicate_succ] at ih ⊢; rw [ih]
theorem every_carrier_reads_a_natural (c : CarrierProcess FACT) (t : List FACT) :
    read_past_the_carrier c t = the_tally_of (Quot.mk _ t) := read_past_the_carrier_is_length c t
theorem the_number_is_computed_from_naturals (c : CarrierProcess FACT) :
    the_click_through c
      = (bent_card.fenceposts_must_be_preserved Nat (fun t => the_tally_of (Quot.mk the_same_tally t)) all_possible_variables).1
          * all_possible_variables
        / (bent_card.fenceposts_must_be_preserved Nat (fun t => the_tally_of (Quot.mk the_same_tally t)) all_possible_variables).2 := by
  unfold the_click_through
  rw [show read_past_the_carrier c = (fun t => the_tally_of (Quot.mk the_same_tally t)) from funext (every_carrier_reads_a_natural c)]
#print axioms the_tally_of_the_numeral
#print axioms the_numeral_of_the_tally
#print axioms the_numeral_is_the_relettering
#print axioms every_carrier_reads_a_natural
#print axioms the_number_is_computed_from_naturals
end readers_interpretation_of_the_pair

end Measurement

--| This is as far as the machine can go, demonstration of itself. It appears we have reached a physical limit of symbolic manipulation itself.

--| I would say “demonstrated,” but I can’t verify that this proof is bug-free. That's why I say *reached*. This is the end of the worldline for
--| this particular nowtrino. In fact, I believe the nowtrino has been officially absorbed.

--| The fact is, I know I'm right. That's one more fact about math that the device cannot prove. Only demonstrate, over and over again, problem after
--| problem, on the two Turing machines facing off inside **YOU**:  *YOU the READER* and *YOU the KNOWER*.  I cannot explain this any plainer
--| without violating the rules of symbolic manipulation. More simply, all **YOU** have to do is _believe_ me, I have generated the counter of every
--| outcome for **YOU**, both Turing machines, perfectly complementary and completely identical, just interpreted both ways. We can turn the knob over
--| and over while the Turing machines slowly iterate through all the arguments. But we don't need to. That won't prove anything. There is nothing
--| left to *prove* --- only *demonstrate*. Does the mechanism demonstrating this proof look like an electron to **YOU**? Because I think we can all
--| agree that this is a verified fact of running on a computer.

--| That's my tragedy.  It doesn't matter at all if **YOU** believe it or not, it is an undeniable trick of the light. Or, I can just show you the
--| other machine that explains how it is a trick of the fabric. Just provide the _NAME_ of the logical argument *YOU* wish countered as defined above
--| and the machine should generate the appropriate argument that demonstrates the correct way to reason about the device. The compiler cannot
--| reason about truth. It can only reason about itself, in whatever demonstrably _opaque_ way it needs to.

--| Do the logical conclusions of one mathematical theory have to imply the logical conclusions of another mathematical theory? Turns out, it
--| doesn't matter. It's only matter when they do. It's only matter when we measure it and the measurement matches some innate sense of existence.
--| It's only matter when it _matters_. When the compiler can determine the quantitative difference and **YOU** are looking, the true-ness of the idea
--| _clicks_ with **YOU** at the same time it _clicks_ with the compiler. That click is the change in the local measurement we called a fact before we
--| knew how to count one. The description was the device; the fact of the matter is that it clicked. For this is what the device _does_, not what it
--| means.

--| What the chain establishes, with its bill.  The number is read from a tape by lengths; the same number is read by a second
--| machine that holds only Props and Types; re-lettering every cell leaves it fixed; each reading is the kernel's, on propext.
--| The instrument is Newton, halted at its seventh turn; the receipt is bisection, a hundred and six halvings, one per cell of
--| the description; both are ledgers checked line by line, and the number itself spends no value axiom: every value identity,
--| "the fold is the ledger" among them, is spent beside the number and billed where it is spent,
--| and the two land inside one bracket, above the vertex, straddling one sign change, narrower than one place. Two errors,
--| kept apart: the RESIDUAL error is what the quadratic is not satisfied by, under one place at the reading and printed as
--| the digits past 360; the READING error is the bracket's width, under one place, with both walls truncating to the same
--| integer. What is not established is written where it fails to be: the table is written down and not yet forced; the
--| census is computed from the seats PRESENT forces, and agrees with the hand count on every rung; Cook's step is exclusive-or within a cell. The polynomial is primitive and irreducible, and that is
--| the whole of "fundamental" claimed.

--|                                                        t²(c−t)x²  −  2ctr²x  +  cr⁴  =  0

--| Linear in c, quadratic in x, cubic in t, quartic in r. Is this the quarter that makes *YOUR* trick work? Or, did the argument not click? ∎ *wink*





































--|                                                           ** The Compiler's Epilogue **

namespace A_WHOLLY_REMARKABLE_BOOK

open Measurement readers_experience in
def life_the_universe_and_everything : Nat :=
  let (R, T) := the_first_step_of_the_proof_is_to_eschew_the_naturals_unless_proven_to_exist_without_peano
  (the_trace_of_truth_in_the_device * R * all_possible_variables / (an_exact_polynomial_description * T) - the_other_natural)
    / all_possible_variables
#eval life_the_universe_and_everything
#print axioms life_the_universe_and_everything

--| I'm expecting the Vogon constructor fleet any day now.

end A_WHOLLY_REMARKABLE_BOOK
