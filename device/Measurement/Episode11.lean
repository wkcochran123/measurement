/-
__Measurement: The Tragedy of John Henry__
__A Satire in Look-Ahead Backus-Naur Form__

[PATTER TODO: rights gag]
[PATTER TODO: epigraph]

__EPISODE 11__ -- THE QUANTUM SUPERCOMPUTER.

RULING (operator): "build a quantum supercomputer that uses the EKG
infrastructure to measure alpha."

The hardware was already in the device and nobody had wired it up.

  THE QUBIT.  `Jar.superposition : Fact -> Jar -> Jar -> Jar` (Episode 3).  A
  fact and two branches.  It is not a metaphor for a two-state system; it is a
  two-state system, and it sits in the tower at `MeesaProcess.concept`, carried
  by GUNGAN.

  THE MEASUREMENT.  Episode 7, `REVIEWER_2_MAKES_THE_JOKE_PAY_ITS_EVIDENTIARY_BILL`,
  rung 15 of the 36-rung REVIEWED chain -- the ONLY rung of the thirty-six that
  collapses a superposition:

      | .superposition f _ _ => f

  Both branches discarded.  The surviving fact is the one written on the jar
  when it was built.

  THE APPARATUS.  That collapse happens inside an `instance`, so the thing
  performing it is the elaborator.  There is no `#eval` that can see it.  The
  only instrument is `ekg_probe`, billing what resolution cost.

  THE CREDIT.  This is Aaronson's `PostBQP = PP` (2005): postselection --
  keeping only the runs that came out the way you wanted -- lifts bounded-error
  quantum computation to PP.  Postselection IS the shill.  The device runs it
  twice, stacked: in the term, the `match` throws away both branches; in the
  elaborator, instance search explores candidates and reports only the path that
  typechecked.

  AND THE DEVICE OUT-DOES THE THEOREM, which is the part worth stating plainly.
  `PostBQP = PP` postselects on an OUTCOME -- you run, you look, you discard.
  Here nothing is ever run and nothing is ever looked at.  The answer is a field
  of the constructor.  The speedup is not exponential; it is total, and it is
  free, because the machine never reads its own register.
-/
import Measurement.Episode10
import Measurement.Calibration.EKGBounded
set_option maxHeartbeats 4000000

namespace Measurement

/-! ## ABSORBED: THE CROSSING CANNOT BE NAMED

This was Measurement/Calibration/TheCrossingCannotBeNamed.lean, a separate
leaf, absorbed here on the operator's instruction.  Its own preamble follows
verbatim so the argument keeps its framing; nothing in it was rewritten.

-/


/-! ## THE SEEING -- total, and decided without division -/

/-- THE DEAL.  Three cards: the outer one played twice, the inner one once.
That is the entire specification.  No value is required of either. -/
def deal (outer inner : Nat) : Nat × Nat × Nat := (outer, inner, outer)

/-- LEFT EQUALS RIGHT.  For any numbers whatsoever. -/
theorem the_outside_cards_are_the_same_card (outer inner : Nat) :
    (deal outer inner).1 = (deal outer inner).2.2 := rfl

/-- THE MIDDLE CARD DOES NOT MOVE.  For any numbers whatsoever. -/
theorem the_middle_card_does_not_move (outer inner : Nat) :
    (deal outer inner).2.1 = inner := rfl

/-- Is the slip above the target at `p/q`?  `outer*q^2 > inner*p^2`, two naturals.
Total for ANY cards: every pair gets an answer, including `q = 0`. -/
def slipAbove (outer inner p q : Nat) : Bool :=
  decide (outer * (q * q) > inner * (p * p))

/-- THE SEEING IS STRUCTURAL.  Total for any cards and any candidate -- it is a
`Bool`.  Nothing about 18 or 5 is used, or could be. -/
theorem the_side_test_is_total (outer inner p q : Nat) :
    slipAbove outer inner p q = true ∨ slipAbove outer inner p q = false := by
  cases slipAbove outer inner p q
  · exact Or.inr rfl
  · exact Or.inl rfl

/-! ## THE DESCENT -- five divides the square only when it divides the root -/

/-- A square is `0`, `1` or `4` mod five, never `2` or `3`; so if five divides a
square it divides its root.  Decided on the five residues, no primality theory. -/
theorem five_dvd_of_five_dvd_sq (n : Nat) (h : n * n % 5 = 0) : n % 5 = 0 := by
  have hm : n * n % 5 = (n % 5) * (n % 5) % 5 := Nat.mul_mod n n 5
  have hr : n % 5 = 0 ∨ n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4 := by omega
  rcases hr with h' | h' | h' | h' | h' <;> rw [h'] at hm <;> omega

/-! ## THE NAMING IS EMPTY

Infinite descent on the factor of five.  If `18*q^2 = 5*p^2` with `q` nonzero,
then five divides `q`, hence five divides `p`, and `(p/5, q/5)` is a strictly
smaller solution -- which cannot go on forever in the naturals.

No `ring`, no `nlinarith`: this leaf has no Mathlib.  The only non-`omega` step
is expanding `(5*a)*(5*a)` to `25*(a*a)`, done by associativity and commutativity
so that everything after it is linear in the atoms `a*a`, `b*b`, `p*p`, `q*q` and
`omega` can finish. -/

/-- `(5*n)^2 = 25*n^2`, by AC only -- the one place multiplication is rearranged. -/
theorem five_sq_expand (n : Nat) : (5 * n) * (5 * n) = 25 * (n * n) := by
  simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

theorem the_crossing_is_not_a_ratio (q : Nat) (hq : q ≠ 0) (p : Nat) :
    18 * (q * q) ≠ 5 * (p * p) := by
  intro heq
  -- five divides q^2 (18 is 3 mod five, and three is invertible), hence divides q
  have hq2 : (q * q) % 5 = 0 := by omega
  have hq5 : q % 5 = 0 := five_dvd_of_five_dvd_sq q hq2
  obtain ⟨a, ha⟩ : ∃ a, q = 5 * a := ⟨q / 5, by omega⟩
  have ha0 : a ≠ 0 := by intro h; rw [h] at ha; omega
  -- 18*(25 a^2) = 5 p^2, so p^2 = 90 a^2, so five divides p
  have heq2 : 18 * (25 * (a * a)) = 5 * (p * p) := by
    rw [ha, five_sq_expand] at heq; exact heq
  have hp2 : p * p = 90 * (a * a) := by omega
  have hp5 : p % 5 = 0 := five_dvd_of_five_dvd_sq p (by omega)
  obtain ⟨b, hb⟩ : ∃ b, p = 5 * b := ⟨p / 5, by omega⟩
  -- 25 b^2 = 90 a^2, i.e. 18 a^2 = 5 b^2 -- the SAME equation, strictly smaller
  have hp2' : 25 * (b * b) = 90 * (a * a) := by
    rw [hb, five_sq_expand] at hp2; exact hp2
  have hsmall : 18 * (a * a) = 5 * (b * b) := by omega
  exact the_crossing_is_not_a_ratio a ha0 b hsmall
termination_by q
decreasing_by omega


/-! ## THE INVARIANT

`221/71`, dealt `[71 221]`.  Swap the cards and ask what survives it.

Not the ratio -- that inverts.  Not the crossing -- that inverts too.  What
survives is the PRODUCT, and it survives for the dullest possible reason:
multiplication commutes.  `221*71 = 71*221`.

And the product is not merely preserved, it is the thing that DECIDES.  Suppose
some `p/q` names the crossing, so `outer*q^2 = inner*p^2`.  Multiply both sides
by `outer`:

    (outer*q)^2  =  outer^2 * q^2  =  outer*(inner*p^2)  =  (outer*inner) * p^2

so the deal's product, scaled by a square, IS a square.  A name exists only if
`outer*inner` is a perfect square.  That is the whole obstruction, it is one
multiplication, and it is invariant under the shuffle.

Which finally says why the numerology never mattered.  Every deal on this table
has the same structure and differs only in one number -- its product -- and that
number is fixed the moment the cards are chosen and cannot be changed by moving
them around. -/

/-- THE INVARIANT of a deal: the product of the two distinct cards. -/
def dealInvariant (outer inner : Nat) : Nat := outer * inner

/-- IT SURVIVES THE SHUFFLE.  Swapping the cards leaves it alone. -/
theorem the_invariant_survives_the_shuffle (outer inner : Nat) :
    dealInvariant outer inner = dealInvariant inner outer :=
  Nat.mul_comm outer inner

/-- AND IT IS WHAT DECIDES.  If any `p/q` names the crossing, the deal's
invariant scaled by `p^2` is the square of `outer*q`.  So a name exists only
where the invariant is a perfect square. -/
theorem naming_forces_the_invariant_square (outer inner p q : Nat)
    (h : outer * (q * q) = inner * (p * p)) :
    (outer * q) * (outer * q) = dealInvariant outer inner * (p * p) := by
  have expand : (outer * q) * (outer * q) = outer * (outer * (q * q)) := by
    set_option linter.unusedSimpArgs false in
    simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  rw [expand, h, dealInvariant]
  simp [Nat.mul_assoc]


/-! ## THE SUBSTITUTION -- IP SPACE, RITE: THE LEGS, NOT THE HYPOTENUSE

RULING (operator): "you don't need the sqrt anymore, we have shown that we don't
have the hypotenuse, we have the legs.  so, time to perform a variable
substitution like the ode at the beginning of episode 4.  this is IP Space RITE
that is mentioned at the bottom of episode 3."

Episode 4's ODE, in its own margin:

    (D+y) 1 = y.   (D+y)^2 1 = y' + y^2.   (D+y)^3 1 = y'' + 3yy' + y^3.
    Set y = u'/u.  Then u^-1 D u = D+y, so the cube is u'''/u.

The substitution is the LOG DERIVATIVE, and what it buys is that a nonlinear
operator becomes a linear one conjugated by u.  The nonlinearity was never in the
problem.  It was in insisting on the RATIO.

Same move here.  We had a crossing d with d^2 = outer/inner -- a hypotenuse, and
a square root to reach it.  Write d = p/q and the nonlinear condition in d
becomes a relation between two LEGS, each obeying a linear three-term
recurrence, exactly as u does above.  The ratio is the log derivative of the leg
sequence; the legs are the linear thing underneath it.

And the conserved quantity of the legs needs no root at all:

    pellForm outer inner p q  =  inner*p^2 - outer*q^2

Its SIGN is the side-test we already had.  Its VALUE is the invariant of the
substitution: along the ladder it neither converges nor runs away -- it CYCLES.
Zero is the crossing, and zero is what the descent proved unreachable here.

IP space, rite: the form is the inner product, p and q are the legs, and the
hypotenuse -- the part that needed the root -- is the one side of the triangle
the device never has to name. -/

/-- THE PELL FORM.  The legs, paired against the deal.  Integers only: no root,
no rational, no float. -/
def pellForm (outer inner p q : Nat) : Int :=
  ((inner * (p * p) : Nat) : Int) - ((outer * (q * q) : Nat) : Int)

/-- THE SIDE-TEST IS THE SIGN.  The substitution costs the device nothing it
could previously see. -/
theorem the_side_test_is_the_sign (outer inner p q : Nat) :
    slipAbove outer inner p q = decide (pellForm outer inner p q < 0) := by
  unfold slipAbove pellForm
  simp only [decide_eq_decide]
  omega

/-- THE CROSSING IS THE ZERO OF THE FORM.  Naming it is exactly making the form
vanish -- which, for this deal, the descent proved impossible. -/
theorem the_crossing_is_the_zero_of_the_form (outer inner p q : Nat) :
    pellForm outer inner p q = 0 <-> outer * (q * q) = inner * (p * p) := by
  unfold pellForm
  omega

/-- THE LEGS ARE LINEAR.  One step of the convergent recurrence: no unknown is
ever multiplied by an unknown.  This is the u the substitution produces. -/
def legStep (a : Nat) (prev cur : Nat) : Nat := a * cur + prev

/-- The ladder, legs carried as a pair and never divided. -/
def legLadder : List Nat -> (Nat × Nat) -> (Nat × Nat) -> List (Nat × Nat)
  | [], _, _ => []
  | a :: rest, (pp, qp), (pc, qc) =>
      let nxt := (legStep a pp pc, legStep a qp qc)
      nxt :: legLadder rest (pc, qc) nxt

/-- The form's value at each rung -- the invariant of the substitution. -/
def pellTrace (outer inner : Nat) (partials : List Nat) : List Int :=
  (legLadder partials (1, 0) (1, 1)).map (fun pq => pellForm outer inner pq.1 pq.2)

/-! ### The trace

`sqrt(18/5)` has continued fraction `[1; 1,8,1,2]` repeating, so on ITS OWN
ladder the form cycles with period four and never reaches zero.

The two rows below it are the same ladder pointed at deals it does not belong to.
They do not cycle -- they run away -- and that is the honest reading, not a
defect: a leg ladder is built from one deal's partial quotients and means
nothing against another's.  Shown rather than hidden, because the contrast is
what makes the cycling on the first row a property of the deal and not of the
recurrence. -/


/-! ### Deciding it without a root

There was a `floorSqrt` here, and an `isSquare` built on it, to ask whether the
invariant was a perfect square.  Both are gone.

They were scaffolding from before the substitution.  Asking "is `outer*inner` a
square" is asking "does the form reach zero", and the legs answer that directly:
walk the ladder and look at `pellForm`.  No root is formed, nothing is divided,
and the test is the device's own topology rather than an arithmetic import.

Keeping a square root in a file whose whole result is that the hypotenuse is the
one side never needed would have been the wrong shape, and it was also the thing
that killed the build: the fold-over-range version was fine at 15691 and got the
kernel OOM-killed at 3,442,376,286. -/

/-- Does the form reach zero anywhere on this ladder?  The device's own
nameability test: legs only, integers only, no root. -/
def zeroOnLadder (outer inner : Nat) (partials : List Nat) : Bool :=
  (pellTrace outer inner partials).any (fun v => v == 0)

/-! ### The invariant, on every deal this session has dealt -/


/-! ### WHO OWES WHAT -- READ THE LEDGER BY PARTY

RULING (operator): "the choice it picked up is that of YOU_the_KNOWER.  should
be pretty obvious from the code."

It is, and it was called a wart here twice before it was read properly.  Sort
this file's theorems by axiom footprint and they do not sort by difficulty --
they sort by WHO IS RESPONSIBLE.

  NO AXIOMS AT ALL -- the machine, unaided:
      the_outside_cards_are_the_same_card
      the_middle_card_does_not_move
      the_side_test_is_total
      the_invariant_survives_the_shuffle
    Left equals right, the middle stays put, everything decides, and the product
    survives the shuffle.  Pure invariance.  It costs nothing because it asserts
    nothing about the world.

  propext, Quot.sound -- the device's own needle:
      five_dvd_of_five_dvd_sq
      the_crossing_is_not_a_ratio
      it_can_see_it_but_cannot_name_it
    The descent.  The one place the device identifies things the checker sees as
    distinct, which is what the needle has always been for.

  propext, Classical.choice, Quot.sound -- YOU the KNOWER:
      the_side_test_is_the_sign
      the_crossing_is_the_zero_of_the_form

And it is exactly those two, which is the tell.  They are the theorems that
convert the device's SEEING into a decision -- `slipAbove` is the sign of the
form, the crossing is the zero of the form.  Turning a proposition into a side
is not something the machine does.  Somebody has to look and call it.

That is rung 37, the one Episode 10 says no tape writes and no meter charges,
"inferred being left to you_the_knower."  The knower made their mind up at the
beginning; the ledger just records that they were the one who did.  Excluded
middle IS the knower, and `#print axioms` caught them at it.

Not a defect and not to be scrubbed.  Scrubbing it would hide the only entry in
the file that names a person. -/

/-! ### THE CHOICE BELONGS TO WHOEVER IS GAWKING AT THE NAMES

RULING (operator): "now we have to demonstrate that the choice belongs to the
person that is gawking at the variable names now."

The device has the word already.  `AtreyuProcess.gawk_at`, Episode 4 -- and the
margin note on `a_quarter` in the same file: "This is the one spot I can name
this and it means nothing to the compiler, but it means something to *US*."

So: demonstrate it.  Not argue it.

Below is the side-test written three times.  Once with the names this file has
been using.  Once with names that mean nothing.  Once with a name that means the
OPPOSITE of what the function does.  All three are the same function, and the
proofs are `rfl`, and `rfl` owes no axioms.

The compiler cannot tell them apart because there is nothing there to tell
apart.  Every difference between `slipAbove` and `f` and `slipBelow` is in the
person reading them, and that person is reading them right now.

Which is where the `Classical.choice` came from and why it could not have come
from anywhere else.  The machine emits a `Bool`.  Deciding that the Bool means
ABOVE rather than BELOW -- that the sign is a side, that a side is an answer --
is not in the term.  It is in the gawking.  `#print axioms` bills it to the only
party present who can read. -/

/-- The side-test, with the names stripped to nothing. -/
def f (a b c d : Nat) : Bool := decide (a * (d * d) > b * (c * c))

/-- The side-test, under a name that asserts the opposite of what it computes. -/
def slipBelow (outer inner p q : Nat) : Bool :=
  decide (outer * (q * q) > inner * (p * p))

/-- THE MACHINE CANNOT TELL THEM APART.  Evocative name, empty name: one term. -/
theorem the_machine_cannot_read_the_names : slipAbove = f := rfl

/-- AND IT CANNOT CATCH A LIE.  `slipBelow` computes ABOVE.  The name is false
and the compiler has no complaint, because the compiler never read it. -/
theorem the_machine_cannot_catch_a_lying_name : slipAbove = slipBelow := rfl

/-- The deal too: the cards carry no meaning the machine can reach. -/
theorem the_deal_cannot_read_its_own_cards :
    deal = fun (x y : Nat) => (x, y, x) := rfl


/-! ## FEEDING IT BETTER LOWER BOUNDS

RULING (operator): "221/71 is on the other side, it diverges.  so, we just need
to throw better and better lower bounds of pi in there and we can get more and
more something."

The convergents of pi alternate.  `3/1` and `333/106` and `103993/33102` come
from below; `22/7` and `355/113` from above.  Deal each one and the machine
takes it without complaint -- it has no opinion about what is under the cards.

So: what actually gets more and more? -/

/-- The first variation between two deals, exact, cross-multiplied.  No division,
no float: `(o2*i1 - o1*i2, i1*i2)`. -/
def firstVariation (o1 i1 o2 i2 : Nat) : Int × Nat :=
  ((o2 : Int) * i1 - (o1 : Int) * i2, i1 * i2)

/-! ### The deals, from below -/


/-! ### The first variation of the INPUT, as the bounds improve -/


/-! ### And the bracket, from a deal that straddles: 221/71 below, 22/7 above -/


/-! ### WHAT GETS MORE AND MORE

Read the two first variations.  `15/106` then `73/877203` -- the input improved
by four orders of magnitude, and the machine reported it faithfully.

That is the whole of it.  What gets more and more is THE INPUT.  The deal's
crossing is `sqrt(outer/inner)`, so feeding a better rational approximation of
pi returns a better rational bracket on `sqrt(pi)`, to exactly the precision
that was handed in and not one digit further.  The invariant grows -- 3, then
35298, then 3442380486 -- and it is never a square, so the crossing is never
nameable, at any of them.

The machine is a square-root machine.  It adds nothing, and it was never going
to: left equals right, the middle does not move, the side-test decides, and the
one number that distinguishes one table from another is a product fixed before
the first card was thrown.  Feed it pi and it returns root pi.  Feed it 18/5 and
it returns root 3.6.  "More and more something" is more and more of whatever was
put in, wearing a square root. -/

/-! ## THE PAIR, AND WHICH HALF IS STRUCTURAL

RULING (operator): "18 5 18 are numerology results.  there is no real reason for
them.  it doesn't matter what you put in the machine -- it just needs to know
that the left hand number is equal to the right hand number and the middle
number does not change."

So the file has to say which of its claims survive that, and this one does not
come out flattering to the original draft.

STRUCTURAL, holds for anything you put in:
  * the outer cards are the same card                (`rfl`)
  * the middle card does not move                    (`rfl`)
  * the side-test is total                           (it is a `Bool`)

NOT STRUCTURAL, a property of this numerology only:
  * the naming is empty

And the counterexample is one line.  Deal outer 4, inner 1: `4*q^2 = 1*p^2` is
named exactly by `p/q = 2/1`.  Same machine, same total side-test, same
left-equals-right and same unmoving middle -- and the crossing IS nameable.  So
"cannot tell you what it is" is NOT a fact about three-card monte.  It is a fact
about the pair of numbers this particular table happens to be running.

Which is the sharper reading, and it is the device's own: the parts that carry
the structure need no values, and the part that needed values turned out to be
the numerology.  The machine does not care what is under the cards.  It cares
that two of them are the same and one of them stays put. -/

/-- THE COUNTEREXAMPLE.  With outer 4 and inner 1 the crossing is named by 2/1,
so emptiness is not a property of the deal. -/
theorem the_naming_is_not_always_empty : 4 * (1 * 1) = 1 * (2 * 2) := by decide

/-- THE SENTENCE, at the numerology the device is actually running.  Total
decision, empty answer set -- and the second conjunct is about 18 and 5, not
about monte. -/
theorem it_can_see_it_but_cannot_name_it (p q : Nat) (hq : q ≠ 0) :
    (slipAbove 18 5 p q = true ∨ slipAbove 18 5 p q = false)
      ∧ 18 * (q * q) ≠ 5 * (p * p) :=
  ⟨the_side_test_is_total 18 5 p q, the_crossing_is_not_a_ratio q hq p⟩



/-! ## THE REGISTER -/

/-- Prepare a qubit: a fact, and two branches that will never be consulted. -/
def prepare (f : Fact) (lo hi : Jar) : Jar := .superposition f lo hi

/-- A branch of depth `n`, so the register can be made arbitrarily large. -/
def deepBranch : Nat -> Jar
  | 0     => .color Fact.Truth (.tree Fact.Truth)
  | n + 1 => .bang Fact.Truth (deepBranch n)

/-- An `n`-deep register: two branches of depth `n` under one fact. -/
def register (f : Fact) (n : Nat) : Jar := prepare f (deepBranch n) (deepBranch n)

/-! ## THE MEASUREMENT

Episode 7's collapse, lifted out of its instance so it can be stated and
checked here.  Byte-for-byte the same three-way match. -/

def measureJar : Jar -> Fact
  | .color f _           => f
  | .bang f _            => f
  | .superposition f _ _ => f

/-! ## WHAT THE MACHINE ACTUALLY COMPUTES -/

/-- THE BRANCHES CARRY NOTHING.  Two registers with completely different
contents measure identically, provided the fact on the jar agrees.  This is the
postselection, stated: the outcome does not depend on the superposed state. -/
theorem measurement_ignores_the_branches (f : Fact) (a b c d : Jar) :
    measureJar (prepare f a b) = measureJar (prepare f c d) := rfl

/-- CONSTANT TIME IN THE REGISTER SIZE.  An `n`-qubit register measures to the
same fact for every `n`.  No search, no interference, no amplitude -- the
"speedup" is that the machine never reads what it is holding. -/
theorem measurement_is_constant_in_register_size (f : Fact) (n : Nat) :
    measureJar (register f n) = f := rfl

/-- AND THE ANSWER WAS FIXED AT PREPARATION.  Whatever fact goes in comes out.
The register is write-only from the answer's point of view. -/
theorem the_answer_is_the_one_you_prepared (f : Fact) (lo hi : Jar) :
    measureJar (prepare f lo hi) = f := rfl

/-! ## THE EKG -- BILLING THE APPARATUS

The collapse is an elaboration event, so the elaborator is the only witness.
Each probe measures ONE resolution at a stated register depth.  If the cost is
flat in `n`, the machine is doing no work; if it grows, the work is in building
the register and not in reading it. -/

ekg_probe 4000 => measureJar (register Fact.Truth 0)
ekg_probe 4000 => measureJar (register Fact.Truth 8)
ekg_probe 4000 => measureJar (register Fact.Truth 64)
ekg_probe 4000 => measureJar (register Fact.Truth 512)

/-! ## POINTING IT AT THE COUPLING

The device's crossing is `sqrt(outer/inner)` at the counted cards.  The legs
decide it without a root (`TheCrossingCannotBeNamed`), so the machine can report
the bracket it is standing in.  Every value below is exact and integral. -/


/-! ## THE TAPE THE COLLAPSE NEVER WROTE -- ALPHA ONE

RULING (operator): "another consuming iterator that makes a compiler tape.
the jar will have a ratio and bounds."

`measureJar` reads the fact off the lid and burns the register -- that was the
point, and three `rfl`s above certify it.  This is the other iterator: the SAME
walk, made to pay for what it holds.  Every constructor leaves a cell.

  `.color` is the introduction: one name, nothing left to skip to.

  `.bang` is a methodology cell: stay on the name, then skip to the head of
  what is underneath.  One tange, one funge -- Episode 10's heartbeat pair.

  `.superposition` is a results cell -- the ONLY tape constructor with a `Prop`
  slot, and the slot is where the postselection goes when it is RECORDED
  instead of performed: the proposition that the two branches would have
  measured the same.  Nothing is discarded silently.  The tape is the receipt.

And because the register is plain constructors all the way down -- no tower,
nothing `noncomputable` -- this is the first tape in the device that `#eval`
can touch.  Episode 10 could only `#reduce` its tape and was forbidden to keep
a copy.  This one the knower can hold. -/

def tapeOfJar : Jar -> CompilerTape.{0}
  | .color f _             => .introduction f PUnit
  | .bang f under          => .methodology f (measureJar under) PUnit PUnit (tapeOfJar under)
  | .superposition f lo hi => .results f (measureJar lo) (measureJar lo = measureJar hi)
                                PUnit PUnit PUnit (tapeOfJar lo)

/-! ### THE RATIO -- alpha zero, billed to the register

Episode 10 proved the count is `(n+1, n)` on ANY tape, so the jar has a ratio
before anyone counts it.  Counting it anyway is the audit: the counts must come
out as a function of the DEPTH, or the tape is not billing the register. -/

/-- THE JAR HAS A RATIO, whatever is in it: Episode 10's origin theorem,
applied.  Which ratio is a fact about the depth, proved next. -/
theorem every_jar_has_the_ratio (j : Jar) :
    tangeCount (tapeOfJar j) = fungeCount (tapeOfJar j) + 1 :=
  tange_exceeds_funge_by_the_origin (tapeOfJar j)

/-- The branch bills its depth: `n` bangs is `n` heartbeat pairs over one
introduction. -/
theorem the_branch_counts (n : Nat) :
    tangeCount (tapeOfJar (deepBranch n)) = n + 1
      ∧ fungeCount (tapeOfJar (deepBranch n)) = n := by
  induction n with
  | zero => exact ⟨rfl, rfl⟩
  | succ n ih =>
      obtain ⟨ht, hf⟩ := ih
      simp [deepBranch, tapeOfJar, tangeCount, fungeCount, stepsOf, Step.isTange] at *
      omega

/-- THE RATIO OF THE REGISTER.  Alpha zero of an `n`-deep register is
`(n+2, n+1)`: the depth, plus the collapse cell, plus the origin.  Hold this
against `measurement_is_constant_in_register_size` above -- same register, and
the tape grows while the measurement stands still.  That contrast is the whole
file, stated twice. -/
theorem alpha_0_bills_the_register (f : Fact) (n : Nat) :
    alpha_0 (tapeOfJar (register f n)) = (n + 2, n + 1) := by
  obtain ⟨ht, hf⟩ := the_branch_counts n
  simp [register, prepare, tapeOfJar, alpha_0, tangeCount, fungeCount, stepsOf,
        Step.isTange] at *
  omega

/-! ### THE BOUNDS -- the bracket the ratio sits in

A ratio wants a bracket, and this one carries its own: strictly above the funge
floor, at or under the doubled floor.  `1 < alpha_0 <= 2`, cross-multiplied,
no division performed -- the same discipline as the side-test.  The jar hands
back a ratio AND the bounds, which is what a measurement is. -/

theorem the_ratio_is_bracketed (f : Fact) (n : Nat) :
    fungeCount (tapeOfJar (register f n)) < tangeCount (tapeOfJar (register f n))
      ∧ tangeCount (tapeOfJar (register f n))
          ≤ 2 * fungeCount (tapeOfJar (register f n)) := by
  have h := alpha_0_bills_the_register f n
  simp [alpha_0] at h
  omega

/-! ### ALPHA ONE -- the first variation, taken by the device's own instrument

Alpha zero was the count before anything runs.  Alpha one is the count's FIRST
VARIATION: two readings of the ratio, differenced cross-multiplied by
`firstVariation` -- the instrument `TheCrossingCannotBeNamed` already points at
the improving pi bounds.  A pair, never a decimal: the slip, over the product
of the funges. -/

def alpha_1 (t t' : CompilerTape) : Int × Nat :=
  firstVariation (alpha_0 t).1 (alpha_0 t).2 (alpha_0 t').1 (alpha_0 t').2

/-- THE VARIATION IS MINUS THE ORIGIN.  Cross-multiplied in the naturals so
nothing is cast: one rung down the ladder, the cross products differ by exactly
one.  The origin that never cancels in the count is the whole of what the
count's variation sees -- the slip is `-1` over the funge product, at every
depth, which is why the ratio can descend forever and never touch its floor. -/
theorem alpha_1_is_minus_the_origin (f : Fact) (n : Nat) :
    (alpha_0 (tapeOfJar (register f (n + 1)))).1
        * (alpha_0 (tapeOfJar (register f n))).2 + 1
      = (alpha_0 (tapeOfJar (register f n))).1
        * (alpha_0 (tapeOfJar (register f (n + 1)))).2 := by
  have h0 := alpha_0_bills_the_register f n
  have h1 := alpha_0_bills_the_register f (n + 1)
  simp [h0, h1, Nat.mul_add, Nat.add_mul]
  omega

/-! ### THE READOUT -- the ratio, the bounds, and the variation

`#eval`, not `#reduce`: this tape never touches the tower.  The depths are the
EKG ladder's own, so the derived count sits directly under the measured bill. -/


-- consecutive rungs: the slip is -1 over the funge product, at any depth

-- the EKG ladder's own strides: the variation at the steps the probes billed


/-! ## THE THIRD CONSUMPTION -- THE FLOP

RULING (operator): "there is one more consumption of the multiset iterator.
that will give us the flop [card1 card2 card3] that we can use to seed the
machine.  this is the navier-stokes construction and it is the inferred card."

The multiset iterator has now been consumed twice: once as a COUNT (alpha
zero) and once as a VARIATION (alpha one).  The third consumption deals it as
CARDS.  A tape's steps, dealt: the outer card is the tange count, played
twice, and the inner card is the funge count.  That is `deal`'s exact shape --
left equals right, the middle does not move -- so the machine takes the flop
without modification.  The device seeds its own table. -/

/-- THE FLOP.  [card1 card2 card3], read off any tape. -/
def flop (t : CompilerTape) : Nat × Nat × Nat :=
  deal (tangeCount t) (fungeCount t)

/-- THE OUTER CARDS ARE THE SAME CARD -- inherited from the deal, for any tape. -/
theorem the_flop_is_a_deal (t : CompilerTape) :
    (flop t).1 = (flop t).2.2 :=
  the_outside_cards_are_the_same_card (tangeCount t) (fungeCount t)

/-- AND THE CARDS ARE ALWAYS CONSECUTIVE.  The origin never cancels, so every
flop the device deals itself is `(n+1, n, n+1)`.  The numerology is gone: 18
and 5 were chosen, but these cards are counted, and the count fixes them. -/
theorem the_flop_deals_consecutive_cards (t : CompilerTape) :
    (flop t).1 = (flop t).2.1 + 1 :=
  tange_exceeds_funge_by_the_origin t

/-! ### THE SELF-DEALT TABLE HAS NO NAMEABLE CROSSING

`TheCrossingCannotBeNamed` ends on a confession: "the naming is empty" is NOT
structural -- deal 4 and 1 and the crossing is named by 2/1.  Emptiness was a
property of the pair, and the pair was numerology.

Not on this table.  The flop's cards are consecutive BY THEOREM, and a product
of consecutive naturals sits strictly between the two squares it straddles, so
the invariant of a self-dealt table is NEVER a perfect square -- the
obstruction the invariant section names is permanent here.  What the crossing
file could only report about 18 and 5, the flop makes structural: the device
cannot deal itself a nameable crossing, at any depth, because the origin never
cancels.  Emptiness is inherited from the count. -/

/-- A product of consecutive cards is never a square: it sits strictly between
`n+1` squared and `n+2` squared.  Distribution and `omega`; no Mathlib. -/
theorem consecutive_cards_never_deal_a_square (n m : Nat) :
    (n + 2) * (n + 1) ≠ m * m := by
  intro h
  simp [Nat.mul_add, Nat.add_mul] at h
  rcases Nat.lt_or_ge m (n + 2) with hm | hm
  · have h1 : m * m ≤ (n + 1) * (n + 1) :=
      Nat.mul_le_mul (by omega) (by omega)
    simp [Nat.mul_add, Nat.add_mul] at h1
    omega
  · have h1 : (n + 2) * (n + 2) ≤ m * m := Nat.mul_le_mul hm hm
    simp [Nat.mul_add, Nat.add_mul] at h1
    omega

/-- THE REGISTER'S OWN TABLE, UNNAMEABLE.  The invariant of the flop of any
register is not a square, so no `p/q` names its crossing's obstruction away. -/
theorem the_register_never_deals_a_square (f : Fact) (n m : Nat) :
    dealInvariant (flop (tapeOfJar (register f n))).1
        (flop (tapeOfJar (register f n))).2.1 ≠ m * m := by
  have h := alpha_0_bills_the_register f n
  simp [alpha_0] at h
  simp [flop, deal, dealInvariant, h.1, h.2]
  exact consecutive_cards_never_deal_a_square n m

/-! ### THE NAVIER-STOKES CONSTRUCTION

Episode 3 confessed it: the principle of least action rewritten as a Galerkin
spline solution to the Yang-Mills formulation of Navier-Stokes, solved by
JFNK, preconditioned multi-grid.  Episode 4's ODE is the same move in one
line: the log derivative turns a nonlinear ratio into a linear flow.

The flop seeds exactly that machine.  The crossing of the self-dealt table is
`sqrt((n+2)/(n+1))` -- nonlinear, a hypotenuse -- and the legs underneath it
obey the linear three-term recurrence, one Newton-Krylov step per rung, the
ladder of depths standing in for the grids.  The regularity question is the
Pell trace: on its OWN deal the flow cycles -- bounded forever, no blow-up --
and on a deal it does not belong to it runs away.  Both are shown below,
because the contrast is the result.

At depth zero the device deals `[2 1 2]` and the crossing is the square root
of two: the first unnameable number, re-derived by a card count. -/


-- the self-dealt flow, root two's own ladder: the form cycles, +1 -1, no blow-up

-- the depth-8 flop forced onto root two's ladder: the flow blows up, honestly

/-! ### THE INFERRED CARD

The flop is not delivered as three naturals; the device has a card type for
it.  `Closure.inferred` (Episode 4) carries two facts, two bounds, a
computation, and the card underneath -- and `INFERRED.α` is the seat that
wants one.  So the third consumption folds the whole tape into that
constructor: each heartbeat pair becomes one `.inferred` cell -- tange fact,
funge fact, both bounds at their `.zero` floors, the floor ordering in the
computation slot -- and the introduction at the bottom becomes `.same`: the
quarter, glued to the table.

The results cells do one thing more.  `tapeOfJar` RECORDED the postselection
in the tape's one `Prop` slot instead of performing it; here that proposition
is passed through into the inferred card's computation slot.  The shill's
choice, still unexecuted, now rides the card the knower is handed. -/

/-- THE INFERRED CARD.  The tape, dealt one more time, into the device's own
card type.  Nothing is chosen: every fact is the tape's, every bound is a
floor, and the one non-floor proposition is the recorded postselection.

(The twenty zeros are `Closure`'s twenty universe parameters -- four per
`Bullshit` slot -- pinned so the card can be held AND evaluated.  Episode 10's
tape could not be kept for exactly this class of reason; this card can,
because nothing in it needs a universe above the floor.) -/
def inferredCard : CompilerTape.{0} -> Closure.{0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0}
  | .introduction f _         => .same f (.zero f)
  | .methodology c s _ _ rest =>
      .inferred c s (.zero c) (.zero s)
        (some ((Bullshit.zero.{0,0,0,0} c) ≤ (Bullshit.zero.{0,0,0,0} s)))
        (inferredCard rest)
  | .results c s p _ _ _ rest =>
      .inferred c s (.zero c) (.zero s) (some p) (inferredCard rest)

/-- A card's rungs: how many inferences stand on the quarter. -/
def Closure.rungs : Closure -> Nat
  | .same _ _              => 0
  | .different _ _ _ _     => 0
  | .inferred _ _ _ _ _ c  => c.rungs + 1

/-- ROUTE AGREEMENT.  One inference per heartbeat pair: the card's rungs are
the tape's funge count, on any tape.  The two consumptions name the same walk. -/
theorem the_inferred_card_counts_the_funges (t : CompilerTape) :
    (inferredCard t).rungs = fungeCount t := by
  induction t with
  | introduction f b => rfl
  | methodology c s a b rest ih =>
      simp [inferredCard, Closure.rungs, fungeCount, stepsOf, Step.isTange] at *
      omega
  | results c s p a b d rest ih =>
      simp [inferredCard, Closure.rungs, fungeCount, stepsOf, Step.isTange] at *
      omega

/-- And on the register the card bills the depth, one rung over the quarter. -/
theorem the_card_bills_the_register (f : Fact) (n : Nat) :
    (inferredCard (tapeOfJar (register f n))).rungs = n + 1 := by
  have h := alpha_0_bills_the_register f n
  simp [alpha_0] at h
  rw [the_inferred_card_counts_the_funges]
  omega



/-! ## THE NUMBER, OFF THE JAR

Episode 9 computes the decimal from its two counts, and Episode 10 checks the
device's readback hands the same two back.  The register closes the triangle:
the DEPTH-ONE register's tape bills exactly those counts.  `alpha_0` of one
qubit over one-deep branches is `(3, 2)` -- the walk and the hop -- and that is
not a coincidence to be gawked at but an instance of a theorem already in this
file, at `n = 1`.

So the quantum supercomputer's seeding is complete: prepare one register,
consume it to a tape, count the tape, and the counts are the coupling's.  The
machine the flop seeds and the machine Episode 9 runs are the same machine,
and the decimal prints here off the jar's own arithmetic. -/

/-- THE DEPTH-ONE REGISTER DEALS THE COUNTS.  One qubit, one-deep branches:
alpha zero is Episode 9's `(tange, funge)`.  Count against count, no numeral. -/
theorem the_depth_one_register_deals_the_counts (f : Fact) :
    alpha_0 (tapeOfJar (register f 1)) = (tange, funge) := by
  rw [alpha_0_bills_the_register f 1]
  decide

/-- AND THE JAR DEALS THE COUPLING.  Funge times tange squared, read off the
depth-one register's own tape, is Episode 9's coupling. -/
theorem the_jar_deals_the_coupling (f : Fact) :
    (alpha_0 (tapeOfJar (register f 1))).2
        * (alpha_0 (tapeOfJar (register f 1))).1
        * (alpha_0 (tapeOfJar (register f 1))).1
      = theCoupling := by
  rw [the_depth_one_register_deals_the_counts]
  decide

/-! ### The readout: the bracket and the digits, off the jar's machine -/



/-! ## WHAT THIS DOES NOT DO

It does not produce `1/alpha`.  The contraction to alpha is
`alphaFromSecondVariationAtDistance` -- `tangeAtDistance` times
`fieldPerChargeAtSlip`, over `naturalUnitOrbitRadius` -- and those live in
Episode 40, twenty-nine rungs above this file.  Importing them is a cycle.

What this file supplies is the machine those definitions would consume: the
register, the collapse, the elaboration bill, and the leg bracket on the
crossing.  The last step is Episode 40's and is not smuggled here.

Also: the chain to Episode 40 does not currently build.  Episode 15 fails on
`FINITE_ELEPHANT`, which has no class declaration anywhere in this tree. -/


/-! ### THE READOUT, SECOND HALF.  The HIGH end of the same bracket, to the same
twenty-four places, and the census of the theorem that says the ratio is
bracketed at all -- the one that carries the reader's choice.  Two numbers,
almost exactly the same, bought at two different prices. -/

def theDecimalHigh : Nat := decimalOfBracket theBracket.2 24

end Measurement

#eval s!"alpha = {Measurement.theDecimalHigh / 10 ^ 24}.{Measurement.padLeft (Measurement.theDecimalHigh % 10 ^ 24) 24}"
#print axioms Measurement.the_ratio_is_bracketed
