/-
__Measurement: The Tragedy of John Henry__
__A Satire in Look Ahead Backus-Naur Form__

_A reduction is a promise that your problem was somebody else's problem all along._

(c) 2026

__EPISODE 13__: _LET'S WATCH HIM COOK..._

-/

--| Cook's theorem takes a machine and an input and hands back a FORMULA: satisfiable
--| exactly when the machine accepts.  The construction is a tableau -- time down the page,
--| tape across it -- and four groups of clauses saying that each cell holds one symbol,
--| that the first row is the input, that every row follows from the one above by a local
--| window, and that some row accepts.
--|
--| Every one of those objects is already in this device, and none of them was built for
--| this.  The tableau is Episode 11: thirty-six rungs, each `TYPESET Box Pigeon n Lifted`
--| requiring `[below: TYPESET Box Pigeon (n-1) _]`, carrying a `the_page : CompilerTape`.
--| Row n from row n-1, with a tape.  The window is the rung's own head match.  And the
--| conjunctive normal form is Episode 3's arithmetic, which has been sitting there since
--| the first act wearing the names of areas and lengths:
--|
--|     Sum.add     : Fact → Area → Area → Sum → Sum          two literals, disjoined
--|     Product.mul : Fact → Sum  → Sum  → Product → Product  two clauses, conjoined
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
import Measurement.Episode12

namespace Measurement

/-!
### THE LITERAL, AND WHY IT IS AN AREA

A literal is a variable or its negation, and the only thing a reduction ever does with one
is put it in a clause.  Episode 8 already carded the atom: `theArea`, built from the origin
fact and the origin page.  A literal here is not a new kind of thing.  It is the smallest
thing the device agreed to hold, which is what a literal is supposed to be.
-/
--| MINTED HERE, NOT BORROWED.  Episode 8 already carries `theOriginFact`, `theArea` and
--| `theSum`, and the obvious move is to import Episode 8 and use them.  That would be
--| wrong, and the import graph says why: Episode 9 imports Episode SEVEN.  The long way
--| branches off before the short way exists and never rejoins it -- Episode 12 is the only
--| file that pulls both, and it pulls both because it is comparing them.
--|
--| So Cook takes nothing from the short way.  These four lines rebuild the atoms from the
--| origin fact, which is Episode 1, which everything has.  A reduction that quietly needed
--| the answer would not be a reduction.
def cookFact : Fact := Fact.Truth
def cookPage : Number := .zero cookFact
def aLiteral : Area := .dt cookFact cookPage (.tree cookFact)

--| THE CLAUSE.  `Sum.add` disjoins two areas onto an accumulator, and terminates in
--| `.zero`, which is the empty disjunction -- false, correctly, since an empty OR is.
def aClause : Sum := .add cookFact aLiteral aLiteral (.zero True aLiteral)

/-!
### THE FOUR CONJUNCTS

Cook's formula is φ_cell ∧ φ_start ∧ φ_move ∧ φ_accept, and each conjunct is a group of
clauses, which is to say each is a `Product`.  The device gives three ways to be one:

    Product.origin : Fact → Product              the empty conjunction -- vacuously true
    Product.one    : Prop → Sum → Product        a single clause
    Product.mul    : Fact → Sum → Sum → Product → Product

and the four conjuncts want exactly those shapes, in that order of weight.
-/

--| EACH CELL HOLDS ONE SYMBOL.  Two clauses: at least one symbol, and not two.  That is
--| the only conjunct that needs both halves of a `mul`, and it is the one everybody
--| forgets when they write the proof out on a board.
def phi_cell : Product := .mul cookFact aClause aClause (.one True aClause)

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
def phi_move : Product := .mul cookFact aClause aClause (.one True aClause)

--| SOME ROW ACCEPTS.  Empty, and that is not a shortcut.  Acceptance in this device is not
--| a clause you add; it is whether the last rung can be built at all.  `pressCheck` reads
--| the head and returns `¬(c.truth ↔ s.truth)` -- exclusive or, the one gate that is not
--| monotone -- and the verdict is a reading, not a constraint.  So the conjunct is
--| `.origin`: nothing is asserted, and the acceptance condition lives in whether an
--| instance exists.  Which is the whole point of a reduction, and also its cost.
def phi_accept : Product := .origin cookFact

/-!
### THE FORMULA

Four conjuncts, terminated by the null space.  `Basis.null_space` is the right ending and
not a convenience: the empty conjunction is true, the unconstrained directions are exactly
the ones no clause touches, and the satisfying assignments of a constraint system ARE its
null space.  The device named that constructor while doing linear algebra and it means the
same thing here.
-/
def phi : Basis :=
  .basis cookFact phi_cell phi_start
    (.basis cookFact phi_move phi_accept
      (.null_space cookFact))

--| THE REDUCTION.  A `Polynomial` over the formula -- which is what a reduction is: the
--| formula, in the size of the input, to a power somebody has to bound.
def theReduction : Polynomial :=
  .factor cookFact phi phi (.monomial True phi)

/-!
### WHAT IS EXHIBITED HERE, AND WHAT IS NOT

Exhibited: the encoding.  Four conjuncts, each a `Product` of `Sum`s of `Area`s, assembled
into one `Basis` and carried by a `Polynomial`.  Every constructor is Episode 3's and every
atom is Episode 8's.  Nothing was built for this file, which is the only reason it is short.

NOT exhibited, and it should be said plainly rather than left for a reader to notice: the
correspondence itself.  Cook's theorem is

    φ is satisfiable   ⟺   the machine accepts

and the device's version of the right-hand side is `∃ inst, TYPESET Prop truthCarrier 36 _`
-- an instance search.  That search does not currently close.  It times out at twenty
thousand heartbeats, because thirty-six rungs of explicitly handed-over context is two and
a half thousand arguments the resolver must guess.

Which is an awkward thing to report and an honest thing to keep, because a search that
blows up is not evidence against the reduction.  It is the shape a reduction to SAT is
SUPPOSED to have.  The theorem says the formula can be written down in polynomial time; it
has never said anybody can solve it.  The timeout is the second half of Cook arriving
early, uninvited, and in the wrong file.
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
--| odd one out.  Two are definite and differ by an overall flip; two are Lorentzian and
--| are the convention physicists have been arguing about since Minkowski.
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
### WHICH MEANS THIS IS NOT YET COOK, AND THE REASON IS WORTH MORE THAN THE FILE

`satisfiable phi` holds, and `monotone_sat` says it holds for every proper `Basis`
whatsoever.  The only way to fail is to contain `Sum.zero`, an empty clause -- which is a
syntactic property, readable in one pass, with nothing assigned.  Monotone SAT is in P: you
do not search, you scan for the empty clause and then answer `true`.

So the reduction assembled above is well-typed, imports only the long way, uses nothing
built for the purpose -- and encodes a problem that is trivial.  The syntax was carrying
Cook's SHAPE without Cook's CONTENT, and only writing the semantics made that visible.

What is missing is one thing: **negation**.  And the device has it, twice, both times
outside this arithmetic:

    Jar.le      | isFalse _, isFalse _ => ¬ le j1' j2'      the F/F arm
    pressCheck  truth := ¬(c.truth ↔ s.truth)               exclusive or

Both live where decisions are compared, not where areas accumulate -- which is the honest
reading of why `Sum` has no sign.  Areas are magnitudes.  A magnitude has no complement.

TWO FURTHER THINGS THIS FILE DOES NOT HAVE, named so nobody has to discover them:

  1.  No trace encoding.  `phi_move` is a `Product` shaped like a transition constraint and
      constraining nothing.  A real one indexes configurations by time, carries the stack
      into the encoded state, and preserves untouched cells as well as describing updates.

  2.  No witness transformations.  `encodeTrace` and `decodeTrace` both have to exist, and
      the backward one is the one that matters: a satisfying assignment must reconstruct an
      execution, not license `Classical.choice` to invent one.  Which is also where
      classicality would enter this device at all -- `Fact` bundles `decTruth` precisely so
      that no proposition is assumed decided.  A σ that decides every variable is exactly
      the assumption the device has been refusing since Episode 1.

The accepting-trace equivalence comes first.  The polynomial size and construction-time
bounds are a separate milestone, and a bound polynomial in T is not automatically
polynomial in the bits used to write T.
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

The trace is `CompilerTape` -- the page Episode 11's rungs carry.  Introduction, then
methodology, then methodology, one cell per step.  It is the only object in the long way
that is a bounded execution and can be written down without asking instance search to
rediscover it, which is why the reduction takes it and not the `TYPESET` chain.
-/

--| A FACT ALREADY DECIDES ITSELF.  That is what `decTruth` is for, and it is why the
--| device has no free variables of its own: every atom arrives with its assignment.
def Fact.bit (f : Fact) : Bool := @decide f.truth f.decTruth

--| AND BACK.  A bit is a Fact you can hand a decision to.  `Fact.Truth` for one, and the
--| empty proposition -- refuted by the identity, since `¬False` IS `id` -- for zero.
def bitFact : Bool → Fact
  | true  => Fact.Truth
  | false => { truth := False, decTruth := .isFalse id }

--| THE LOCAL INVERSE.  Everything downstream rests on these two lines.
theorem bit_bitFact : ∀ b : Bool, (bitFact b).bit = b := by
  intro b; cases b <;> rfl

--| THE TRACE, READ.  Each cell surrenders the facts at its head, in order.  `introduction`
--| is the base step and gives one; the recursive cells give two, which is the before and
--| the after -- the same pair Episode 11's rungs pull out of the tape as `heads`.
def CompilerTape.bits : CompilerTape.{0} → List Bool
  | .introduction f _         => [f.bit]
  | .methodology c s _ _ rest => c.bit :: s.bit :: rest.bits
  | .results c s _ _ _ _ rest => c.bit :: s.bit :: rest.bits

--| DECODE.  Rebuild the execution from the bits, two at a time, bottoming out in the
--| introduction.  Total: every bit list yields a trace, so there is nothing for a
--| satisfying assignment to hide behind.
def decodeBits : List Bool → CompilerTape.{0}
  | []            => .introduction (bitFact false) Unit
  | [b]           => .introduction (bitFact b) Unit
  | b :: c :: rest => .methodology (bitFact b) (bitFact c) Unit Type (decodeBits rest)

--| A TRACE ALWAYS READS ODD.  `CompilerTape` has no empty constructor: the shortest tape
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
  | case2 b => intro _; simp [decodeBits, CompilerTape.bits, bit_bitFact]
  | case3 b c rest ih =>
      intro h
      have h' : rest.length % 2 = 1 := by simp [List.length] at h; omega
      simp [decodeBits, CompilerTape.bits, bit_bitFact, ih h']

/-!
### WHAT THIS CLOSES AND WHAT IT DOES NOT

Closed: the backward direction is constructive.  `decodeBits` is total, `decode_bits` says
its reading agrees with what it was handed, and `bit_bitFact` is the one-line inverse the
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
--| the parity is different from the tape's.  A `CompilerTape` cell carries a BEFORE and an
--| AFTER, so traces read 2k+1.  A `Product` node carries one assertion, so formulas read
--| any length.  Transition structures need two facts per cell; conjunctions need one.
def decodeProduct : List Bool → Product
  | []        => .origin (bitFact false)
  | [b]       => .origin (bitFact b)
  | b :: rest => .mul (bitFact b) aClause aClause (decodeProduct rest)

theorem decode_product :
    ∀ bs : List Bool, bs ≠ [] → (decodeProduct bs).bits = bs := by
  intro bs
  induction bs using decodeProduct.induct with
  | case1 => intro h; exact absurd rfl h
  | case2 b => intro _; simp [decodeProduct, Product.bits, bit_bitFact]
  | case3 b rest hne ih =>
      intro _
      simp [decodeProduct, Product.bits, bit_bitFact, ih hne]

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
def CompilerTape.stepOK : CompilerTape.{0} → Bool
  | .introduction _ _         => true
  | .methodology c s _ _ rest => (c.bit != s.bit) && rest.stepOK
  | .results c s _ _ _ _ rest => (c.bit != s.bit) && rest.stepOK

--| TWO DISTINCT VARIABLES.  Everything above ran on one `Area`, which is why every formula
--| came out satisfiable by inspection.  These are distinct by constructor depth, and
--| `index` is the address the assignment reads them at.
def Area.index : Area → Nat
  | .tree _       => 0
  | .dt _ _ rest  => rest.index + 1

def varA : Area := .tree cookFact
def varB : Area := .dt cookFact cookPage (.tree cookFact)

def assign (x y : Bool) : Assignment := fun a => if a.index == 0 then x else y

--| XOR IN CONJUNCTIVE NORMAL FORM.  Two clauses, and they need OPPOSITE polarity:
--|
--|     a ⊕ b   ≡   (a ∨ b) ∧ (¬a ∨ ¬b)
--|
--| one clause all positive, one all negative.  That is the whole reason the arithmetic
--| needed a sign, and the whole reason the step constraint could not be written before.
def xorClauses : Product :=
  .mul cookFact
    (.add cookFact varA varB (.zero True varA))
    (.add cookFact varA varB (.zero True varA))
    (.origin cookFact)

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
  .basis cookFact xorClauses phi_accept (.null_space cookFact)

def phiWired : Basis :=
  .basis cookFact phi_cell phi_start
    (.basis cookFact xorClauses phi_accept (.null_space cookFact))

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
  | 0     => .tree cookFact
  | n + 1 => .dt cookFact cookPage (varAt n)

def cellClause (k : Nat) : Sum :=
  .add cookFact (varAt (2 * k)) (varAt (2 * k + 1)) (.zero True (varAt (2 * k)))

--| ε, AS A COUNT OF CELLS.  Each clause gets its own pair, so nothing contradicts by
--| accident and the only contradictions left are the ones the step puts there.
def phi_cellN : Nat → Product
  | 0       => .origin cookFact
  | 1       => .one True (cellClause 0)
  | n + 2   => .mul cookFact (cellClause (n + 1)) (cellClause n) (phi_cellN n)

--| x₀, AS ONE UNIT CLAUSE.  The seed asserts one thing and leaves everything else open,
--| which is what an initial guess is entitled to do.
def phi_startN : Product :=
  .one True (.add cookFact (varAt 0) (varAt 0) (.zero True (varAt 0)))

--| THE FORMULA, WITH ALL FOUR CONJUNCTS REAL.  `theSlipAtTwo` is the Monte's own fold
--| count -- four, the slip -- so the resolution is the device's, not one I picked.
def phiJFNK : Basis :=
  .basis cookFact (phi_cellN theSlipAtTwo) phi_startN
    (.basis cookFact xorClauses phi_accept (.null_space cookFact))

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

    class REVIEWED … where rebuttal : CompilerTape
    class TYPESET  … where register_value : Lifted ; universe_id : Number ; the_page : CompilerTape

One field and three.  The quarter was never under any of the cards.
-/

--| THE MANUSCRIPT.  Rung 36's base instance admits a tape unchanged -- "the submitted
--| manuscript is admitted unchanged, so every later response has a record to answer
--| against."  Here it is, built from bits, odd-length so the roundtrip holds.
def theManuscript : CompilerTape.{0} := decodeBits [true, false, true]

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
def traceSat : CompilerTape.{0} → Bool
  | .introduction _ _         => true
  | .methodology c s _ _ rest => (phiStep.holds (assign c.bit s.bit) alternating 0).1
                                   && traceSat rest
  | .results c s _ _ _ _ rest => (phiStep.holds (assign c.bit s.bit) alternating 0).1
                                   && traceSat rest

--| AND THE CORRESPONDENCE.  A trace is well-stepped exactly when its own bits satisfy the
--| formula built from it.  Not "there exists an assignment" -- the trace SUPPLIES the
--| assignment, which is what makes the backward direction constructive and keeps
--| `Classical.choice` out of a theorem about executions.
theorem trace_correspondence (t : CompilerTape.{0}) : traceSat t = t.stepOK := by
  induction t with
  | introduction _ _ => rfl
  | methodology c s _ _ rest ih =>
      simp [traceSat, CompilerTape.stepOK, step_correspondence, ih]
  | results c s _ _ _ _ rest ih =>
      simp [traceSat, CompilerTape.stepOK, step_correspondence, ih]

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
def theTopTrace : CompilerTape.{0} := theTop.the_page

/-!
### THE CORRESPONDENCE, ON THE LADDER'S OWN TRACE

    U accepts within T   ⟺   ∃σ, σ ⊨ Φ

The left side is now inhabited: `theTop` exists, and its page is a trace of bounded length.
The right side is `traceSat`, the per-cell formula under the alternating schedule.  And the
theorem says they agree -- not that some assignment exists, but that THE TRACE'S OWN BITS
are the assignment.  That is what keeps the backward direction constructive.
-/
theorem cook_levin : THEORY.traceSat theTopTrace = theTopTrace.stepOK :=
  THEORY.trace_correspondence theTopTrace

#eval s!"top rung reached, tape reads {theTopTrace.bits}"
#eval s!"trace well-stepped   {theTopTrace.stepOK}"
#eval s!"formula satisfied    {THEORY.traceSat theTopTrace}"
#eval s!"correspondence holds {THEORY.traceSat theTopTrace == theTopTrace.stepOK}"


end Measurement

--| WHAT THE READER GETS FOR FREE.  The four conjuncts, assembled, with nothing measured.
#eval "cook: four conjuncts over Episode 3 arithmetic, Episode 11 tableau"
#eval s!"all-true  euclid {(Measurement.phi.holds (fun _ => true) (Measurement.uniform .euclidean) 0).1} negated {(Measurement.phi.holds (fun _ => true) (Measurement.uniform .negated) 0).1} west {(Measurement.phi.holds (fun _ => true) (Measurement.uniform .west) 0).1} east {(Measurement.phi.holds (fun _ => true) (Measurement.uniform .east) 0).1}"
#eval s!"all-false euclid {(Measurement.phi.holds (fun _ => false) (Measurement.uniform .euclidean) 0).1} negated {(Measurement.phi.holds (fun _ => false) (Measurement.uniform .negated) 0).1} west {(Measurement.phi.holds (fun _ => false) (Measurement.uniform .west) 0).1} east {(Measurement.phi.holds (fun _ => false) (Measurement.uniform .east) 0).1}"
#eval s!"monte result reads {Measurement.theProduct.bits}"
#eval s!"roundtrip {(Measurement.decodeProduct Measurement.theProduct.bits).bits == Measurement.theProduct.bits}"
#eval s!"xor target                    {Measurement.xorTarget}"
#eval s!"xor under euclidean (++++)     {(Measurement.xorRow (Measurement.uniform .euclidean))}"
#eval s!"xor under negated   (----)     {(Measurement.xorRow (Measurement.uniform .negated))}"
#eval s!"xor under west      (+---)     {(Measurement.xorRow (Measurement.uniform .west))}"
#eval s!"xor under east      (-+++)     {(Measurement.xorRow (Measurement.uniform .east))}"
#eval s!"xor under ALTERNATING           {Measurement.xorRow Measurement.alternating}"
#eval s!"step constraint written?        {Measurement.xorRow Measurement.alternating == Measurement.xorTarget}"
#eval s!"phiWired bothWays alternating   {Measurement.bothWays Measurement.phiWired Measurement.alternating}"
#eval s!"phiWired all four assignments  {Measurement.fourWays Measurement.phiWired Measurement.alternating}"
#eval s!"phiWired satisfiable at all?    {(Measurement.fourWays Measurement.phiWired Measurement.alternating).any id}"
#eval s!"phiStep all four assignments   {Measurement.fourWays Measurement.phiStep Measurement.alternating}"
#eval s!"phiStep is XOR?                 {Measurement.fourWays Measurement.phiStep Measurement.alternating == Measurement.xorTarget}"
#eval s!"phiJFNK satisfiable (10 vars) {Measurement.satSearch Measurement.phiJFNK Measurement.alternating 10}"
#eval s!"phiJFNK by all-true            {(Measurement.phiJFNK.holds (fun _ => true) Measurement.alternating 0).1}"
#eval s!"phiJFNK by all-false           {(Measurement.phiJFNK.holds (fun _ => false) Measurement.alternating 0).1}"
#eval s!"phiJFNK witness               {Measurement.satWitness Measurement.phiJFNK Measurement.alternating 10}"
#eval s!"bothWays  euclid {Measurement.bothWays Measurement.phi (Measurement.uniform .euclidean)} negated {Measurement.bothWays Measurement.phi (Measurement.uniform .negated)} west {Measurement.bothWays Measurement.phi (Measurement.uniform .west)} east {Measurement.bothWays Measurement.phi (Measurement.uniform .east)}"


--| It appears we have reached a limit of symbolic manipulation itself.

--| I would say “demonstrated,” but I can’t verify that this proof is bug-free.

--| The fact is, I know I'm right. That's one more fact about math that the device cannot prove. Only demonstrate, over and over again, problem after
--| problem, on the two Turing machines facing off inside **YOU**:  *YOU the READER* and the *YOU the KNOWER*.  I cannot explain this any plainer
--| without violating the rules of symbolic manipulation. More simply, all **YOU** have to do is _believe_ me, I have generated all the other logical
--| outcomes for **YOU**, both Turing machines, perfectly complimentary. We can turn the knob over and over while the Turing machines slowly iterate
--| through all the arguments. But we don't need to. That won't prove anything. There is nothing left to prove.

--| That's my tragedy. I will be more than happy to read your cards for you, I speak FORTRAN, too. ∎ *wink*
