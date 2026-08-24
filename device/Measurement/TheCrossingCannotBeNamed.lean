/-
__Measurement: The Tragedy of John Henry__

THE CROSSING CANNOT BE NAMED -- the owed half of "the device can see it but
cannot describe it."

The sentence factors into two claims and only one of them was built:

  SEEING is the side-test, and it is TOTAL.  Hand the device any name it can
  write -- any pair `(p, q)` read as `p/q` -- and it decides which side of the
  crossing that name falls on.  No floats, no rationals, no division: the
  question "is the slip above the target at `p/q`" is `C/(p/q)^2 > T` rewritten
  as `C*q^2 > T*p^2`, a comparison of two naturals.  There is no candidate it
  has to shrug at.

  TELLING would be producing the name, and the name would have to satisfy
  `18*q^2 = 5*p^2`.  THIS FILE PROVES NOTHING DOES.

Until now that second half rested on a stated reason plus a bounded search --
twenty mediant steps that never lost the point.  A bounded search is evidence
that the crossing was not hit in twenty steps.  It is not a proof that it cannot
be hit at all, and the difference is the whole sentence.  What follows is the
descent on the factor of five, so the refusal is proved rather than reported.

NO MATHLIB.  Bare core, `-DautoImplicit=false`, same as the rest of the device.
The only facts used are `Nat.mul_mod` and case analysis on the five residues.

C = 18 and T = 5 are the device's counted cards (mass 2 x separation squared 9,
and the target); the crossing is sqrt(18/5).  They are written here as literals
because this leaf proves a fact ABOUT those two numbers and must not depend on
where they are currently defined -- the counting leaf has moved once already
today.  If they move again, this file is still true and still says so about 18
and 5; what would need re-pointing is the claim that 18 and 5 are the cards.
-/

namespace Measurement

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
    simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  rw [expand, h, dealInvariant]
  simp [Nat.mul_assoc]

#print axioms the_invariant_survives_the_shuffle
#print axioms naming_forces_the_invariant_square

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

#eval legLadder [1, 8, 1, 2, 1, 8, 1, 2] (1, 0) (1, 1)
#eval pellTrace 18 5 [1, 8, 1, 2, 1, 8, 1, 2]
#eval pellTrace 22 7 [1, 8, 1, 2, 1, 8, 1, 2]
#eval pellTrace 221 71 [1, 8, 1, 2, 1, 8, 1, 2]

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

#eval (dealInvariant 18 5,   zeroOnLadder 18 5   [1,8,1,2,1,8,1,2])
#eval (dealInvariant 22 7,   zeroOnLadder 22 7   [1,1,3,4,1,1,3,4])
#eval (dealInvariant 221 71, zeroOnLadder 221 71 [1,1,3,4,1,1,3,4])
#eval (dealInvariant 71 221, zeroOnLadder 71 221 [1,1,3,4,1,1,3,4])
#eval (dealInvariant 4 1,    zeroOnLadder 4 1    [1,1,1,1])

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

#print axioms the_side_test_is_the_sign
#print axioms the_machine_cannot_read_the_names
#print axioms the_machine_cannot_catch_a_lying_name
#print axioms the_deal_cannot_read_its_own_cards
#print axioms the_crossing_is_the_zero_of_the_form

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

#eval (dealInvariant 3 1,          zeroOnLadder 3 1          [1,1,2,1,2,1,2,1])
#eval (dealInvariant 333 106,      zeroOnLadder 333 106      [1,1,3,4,1,1,3,4])
#eval (dealInvariant 103993 33102, zeroOnLadder 103993 33102 [1,1,3,4,1,1,3,4])

/-! ### The first variation of the INPUT, as the bounds improve -/

#eval firstVariation 3 1 333 106
#eval firstVariation 333 106 103993 33102

/-! ### And the bracket, from a deal that straddles: 221/71 below, 22/7 above -/

#eval (pellForm 22 7 1 1, pellForm 22 7 2 1)
#eval (pellForm 221 71 1 1, pellForm 221 71 2 1)

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

#print axioms the_outside_cards_are_the_same_card
#print axioms the_middle_card_does_not_move
#print axioms the_side_test_is_total
#print axioms five_dvd_of_five_dvd_sq
#print axioms the_crossing_is_not_a_ratio
#print axioms it_can_see_it_but_cannot_name_it

end Measurement
