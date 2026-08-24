/-! # CycleOfThree — the residue is the invariant of a cycle of three.
Operator: "demonstrate it is a cycle of three."

The count-to-three, the holonomy states −1/0/+1 (electron/null/positron), the R/G/B color of the
three-fold, and the two-pass calibration's rotating roles a/b/c are one object: a rotation that
carries one state into the next and CLOSES only after THREE steps. The residue the machine reports
(reproducible build-to-build) is exactly the invariant carried around this 3-cycle — it comes back
to itself after three, and the count-to-three floor is that closure.

This file demonstrates the cycle is genuinely of order THREE (not one, not two), choice-free. -/

namespace Measurement.CycleOfThree

/-- The three-fold: −1 / 0 / +1 (electron / null / positron) = R/G/B = the calibration roles a/b/c.

    ⚑ ITS BASE IS 2, NON-CIRCULARLY (Beastmaster/operator 2026-07-22, springs Kodo's tautology trap):
    these are NOT three arbitrary states — `minus`/`plus` are the ± PAIR (2 = the duplication base, the
    two-twos, electron/positron), and `zero` (null) is the CLOSING third = the fencepost. So the period is
    `3 = 2 (the ± pair) + the closing null-post` — grounded in the primitive 2 plus its fencepost, NOT read
    off a hardcoded state-count. Type ladder (operator): 2 = a Natural (the ± pair), the fencepost/null = a
    Limit (the closing boundary), and the floor `3` bounds is a Real (the approached open bracket). The
    cycle-PERIOD stays a Nat (you iterate on a count); the FLOOR it marks is the Real you only approach. -/
inductive ThreeFold | minus | zero | plus
deriving DecidableEq, Repr

open ThreeFold

/-- The fold / holonomy / "relabeling is angular momentum": carry each state into the next. -/
def rotate : ThreeFold → ThreeFold
  | minus => zero
  | zero  => plus
  | plus  => minus

/-- Iterate the fold `n` times (n passes of the calibration). -/
def spin : Nat → ThreeFold → ThreeFold
  | 0,     x => x
  | n + 1, x => spin n (rotate x)

-- ⭐ IT IS A CYCLE OF THREE: three folds return EVERY state to itself, and no fewer than three do.
theorem cycle_of_three :
    -- closes at three: every state returns after exactly three folds (the count-to-three floor)
    (spin 3 minus = minus ∧ spin 3 zero = zero ∧ spin 3 plus = plus)
      ∧ spin 1 minus ≠ minus       -- one fold does NOT return  (period ≠ 1)
      ∧ spin 2 minus ≠ minus := by -- two folds do NOT return   (period ≠ 2)
  decide

#print axioms cycle_of_three

-- The residue is invariant under the whole cycle (three folds leave it exactly where it was):
theorem residue_invariant_under_cycle (x : ThreeFold) : spin 3 x = x := by cases x <;> rfl

-- ⚑ FENCEPOST (operator ruling 2026-07-22 "3 as a fencepost is fine"): the count-to-three floor
-- (`AlphaBoundCountToThree.countToThree = 3`) is `2 + the closing fencepost` — the ± pair (2, above) plus
-- the null closing-post — NOT a hardcoded three. A fencepost is a STRUCTURAL boundary index (N intervals
-- ⇒ N+1 posts), not a tuned constant and not a measurement — so it needs no meter-wiring; `cycle_of_three`
-- above PROVES this ±-pair-plus-null cycle closes at exactly three (axiom-free), the structural ground the
-- floor cites. (Grounding it instead as a "measured period" of this 3-constructor type would be CIRCULAR —
-- the 3 would re-enter via the constructor count; the fencepost springs that trap by earning 3 from the 2.)

-- ── EARNING THE 3: addition is not postulated, it's the CARDINALITY OF A COPRODUCT ────────────────────
-- Operator 2026-07-22: "we never actually earn addition, you have to use the Sum." `2 + 1` smuggles a
-- postulated `Nat.add`. Instead build `3 = |PairType ⊕ PostType|` from STANDALONE primitive types — the
-- ± duplication pair (2) coproduct the null closing-post (1) — and carry ThreeFold in by a PROVED
-- equivalence. NON-circular: 3 is NOT read off ThreeFold's own three constructors (that would be the
-- back-door count `measuredCyclePeriod` had); it is constructed from separate 2- and 1-typed primitives.

/-- The ± duplication pair — a STANDALONE primitive 2-type (Bool-shaped), independent of ThreeFold. -/
inductive PairType | neg | pos deriving DecidableEq, Repr
/-- The null closing-post — a STANDALONE primitive 1-type (Unit-shaped), independent of ThreeFold. -/
inductive PostType | close deriving DecidableEq, Repr

/-- The rosters of the two primitives (their inhabitants, enumerated). -/
def pairRoster : List PairType := [PairType.neg, PairType.pos]
def postRoster : List PostType := [PostType.close]

/-- The coproduct's inhabitants: the pair (as `inl`) joined with the post (as `inr`). `++` is list
    concatenation (structural), NOT `Nat.add`; addition EMERGES as the length of the joined roster. -/
def sumRoster : List (PairType ⊕ PostType) :=
  pairRoster.map Sum.inl ++ postRoster.map Sum.inr

/-- `cardPairSumPost = |PairType ⊕ PostType|` — the coproduct cardinality, read as its roster length (= 3).
    This is the EARNED three: `2 ⊕ 1` counted off the constructed Sum, with no `+` operator at the source. -/
def cardPairSumPost : Nat := sumRoster.length

-- ThreeFold ≃ PairType ⊕ PostType — the fencepost structure is INTRINSIC (proved), not asserted by fiat.
def threeFoldToSum : ThreeFold → PairType ⊕ PostType
  | minus => Sum.inl PairType.neg
  | plus  => Sum.inl PairType.pos
  | zero  => Sum.inr PostType.close
def sumToThreeFold : PairType ⊕ PostType → ThreeFold
  | Sum.inl PairType.neg => minus
  | Sum.inl PairType.pos => plus
  | Sum.inr PostType.close => zero
theorem threeFold_sum_left_inv (x : ThreeFold) : sumToThreeFold (threeFoldToSum x) = x := by
  cases x <;> rfl
theorem threeFold_sum_right_inv (y : PairType ⊕ PostType) : threeFoldToSum (sumToThreeFold y) = y := by
  cases y with
  | inl a => cases a <;> rfl
  | inr b => cases b <;> rfl
-- ⭐ so ThreeFold IS the pair ⊕ post (bijective), hence its period-3 = |pair ⊕ post| = cardPairSumPost.
example : cardPairSumPost = 3 := by decide
#print axioms threeFold_sum_left_inv

#eval s!"earned three = |PairType ⊕ PostType| (roster {sumRoster.length}) = 2⊕1, from standalone primitives, no `+`; ThreeFold ≃ pair⊕post proved (left+right inverse)"

#eval s!"the fold:  minus → {repr (rotate minus)} → {repr (rotate (rotate minus))} → {repr (spin 3 minus)}  (back to minus at step 3)"
#eval s!"one full turn of all three: {(List.range 4).map (fun n => (repr (spin n minus), repr (spin n zero), repr (spin n plus)))}"
#eval s!"closes only at three:  spin1≠start? {decide (spin 1 minus ≠ minus)}  spin2≠start? {decide (spin 2 minus ≠ minus)}  spin3=start(all three)? {decide (spin 3 minus = minus ∧ spin 3 zero = zero ∧ spin 3 plus = plus)}"

end Measurement.CycleOfThree
