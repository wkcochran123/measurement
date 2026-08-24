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
import Measurement.TheCrossingCannotBeNamed
import Measurement.Calibration.EKGBounded
set_option maxHeartbeats 4000000

namespace Measurement

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

#eval (dealInvariant 18 5, zeroOnLadder 18 5 [1,8,1,2,1,8,1,2])
#eval legLadder [1,8,1,2,1,8,1,2] (1, 0) (1, 1)
#eval pellTrace 18 5 [1,8,1,2,1,8,1,2]

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

#eval alpha_0 (tapeOfJar (register Fact.Truth 0))
#eval alpha_0 (tapeOfJar (register Fact.Truth 8))
#eval alpha_0 (tapeOfJar (register Fact.Truth 64))
#eval alpha_0 (tapeOfJar (register Fact.Truth 512))

-- consecutive rungs: the slip is -1 over the funge product, at any depth
#eval alpha_1 (tapeOfJar (register Fact.Truth 0)) (tapeOfJar (register Fact.Truth 1))
#eval alpha_1 (tapeOfJar (register Fact.Truth 8)) (tapeOfJar (register Fact.Truth 9))
#eval alpha_1 (tapeOfJar (register Fact.Truth 64)) (tapeOfJar (register Fact.Truth 65))

-- the EKG ladder's own strides: the variation at the steps the probes billed
#eval alpha_1 (tapeOfJar (register Fact.Truth 0)) (tapeOfJar (register Fact.Truth 8))
#eval alpha_1 (tapeOfJar (register Fact.Truth 8)) (tapeOfJar (register Fact.Truth 64))
#eval alpha_1 (tapeOfJar (register Fact.Truth 64)) (tapeOfJar (register Fact.Truth 512))

#print axioms every_jar_has_the_ratio
#print axioms alpha_0_bills_the_register
#print axioms the_ratio_is_bracketed
#print axioms alpha_1_is_minus_the_origin

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

#eval flop (tapeOfJar (register Fact.Truth 0))
#eval flop (tapeOfJar (register Fact.Truth 8))
#eval flop (tapeOfJar (register Fact.Truth 64))
#eval flop (tapeOfJar (register Fact.Truth 512))

-- the self-dealt flow, root two's own ladder: the form cycles, +1 -1, no blow-up
#eval legLadder [2, 2, 2, 2, 2, 2, 2, 2] (1, 0) (1, 1)
#eval pellTrace 2 1 [2, 2, 2, 2, 2, 2, 2, 2]
#eval (dealInvariant 2 1, zeroOnLadder 2 1 [2, 2, 2, 2, 2, 2, 2, 2])

-- the depth-8 flop forced onto root two's ladder: the flow blows up, honestly
#eval pellTrace 10 9 [2, 2, 2, 2, 2, 2, 2, 2]

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

#eval (inferredCard (tapeOfJar (register Fact.Truth 0))).rungs
#eval (inferredCard (tapeOfJar (register Fact.Truth 8))).rungs
#eval (inferredCard (tapeOfJar (register Fact.Truth 64))).rungs
#eval (inferredCard (tapeOfJar (register Fact.Truth 512))).rungs

#print axioms the_flop_is_a_deal
#print axioms the_flop_deals_consecutive_cards
#print axioms consecutive_cards_never_deal_a_square
#print axioms the_register_never_deals_a_square
#print axioms the_inferred_card_counts_the_funges
#print axioms the_card_bills_the_register

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

#eval theBracket
#eval theDecimal

#print axioms the_depth_one_register_deals_the_counts
#print axioms the_jar_deals_the_coupling

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

#print axioms measurement_ignores_the_branches
#print axioms measurement_is_constant_in_register_size
#print axioms the_answer_is_the_one_you_prepared

end Measurement
