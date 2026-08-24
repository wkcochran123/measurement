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
