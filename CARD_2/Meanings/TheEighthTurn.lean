/-
The eighth turn, by the series, and the error that will not close.

Cosine and sine are the series of the even and the odd powers, and on the circle cosine squared beside sine squared is
one.  Where the two are equal is the eighth turn, a quarter of the half turn.  No turn and no arctangent is used here:
only the two series at two rational angles, fifteen places apart, read at a finite stage.  Just below, cosine is past
sine; just above, sine is past cosine.  Between the two the series cross.  Machin's half turn, made from the arctangent
by another road, lies at every stage between four times the one and four times the other.

Each approximation misses.  At each of the two angles the difference of cosine and sine is a real, and it is past
nothing, shown at a finite stage: below by between 4.378 and 4.379 parts in ten to the sixteenth, above by between
9.763 and 9.764.  An equality would show at no finite stage, so no stage could show an approximation exact; that no
rational angle is the crossing is the irrationality of the half turn (Lambert, 1761), standard, and not proved here.
That the crossing of the two series is the eighth turn, and that it is the only one under one, is standard and not
proved here either.
The slip.  Below the crossing nothing can be read until the fourth stage, and from it the sign is read for good; above,
from the third, a stage sooner because the miss is larger.  Once parted, the difference one way leaves something and the
other way leaves nothing, and which way is which turns over across the crossing.  Neither error is computed exactly,
and the one is under the other at every pair of stages: out of reach, and comparable.  The Borwein threshold is the same
kind of statement: one third through one thirteenth is under one and through one fifteenth is past it; the integrals
that slip there are standard and not built.
Halving.  From nothing and one, look at the midpoint until the series part, and keep the half where they cross: a bit at
a time, the cut doubles or doubles and one more.  The looking ends only if the series part at every midpoint, that is,
only if no halving lands on the crossing; that is handed in, not proved.  Handed it, the eighth turn is a real with no
choice, and whatever was handed, the first twelve halvings give 3216 over 4096.  The cut after is read back to the cut
before by halving it, with nothing handed in; the cut before does not give the bit after, which only the comparison
returns.  Doubling, the other way, wraps round and forgets the top bit.
-/
import Meanings.Circle
import Meanings.Pi
import Meanings.Continuity
import Meanings.Baker

namespace Meanings
namespace EighthTurn

--| Fifteen places below the eighth turn, and fifteen places above.
def below : Nat := 785398163397448
def above : Nat := 785398163397449
def places : Nat := 1000000000000000

def cosineBelow : Bracketed := cosine below places (by decide) (by decide)
def sineBelow : Bracketed := sine below places (by decide) (by decide)
def cosineAbove : Bracketed := cosine above places (by decide) (by decide)
def sineAbove : Bracketed := sine above places (by decide) (by decide)

--| BELOW, COSINE IS PAST SINE.  At the fifth stage, sine's high wall is under cosine's low wall.
theorem below_the_crossing_cosine_is_past_sine : (sineBelow.high 5).lt (cosineBelow.low 5) := by decide +kernel

--| ABOVE, SINE IS PAST COSINE.
theorem above_the_crossing_sine_is_past_cosine : (cosineAbove.high 5).lt (sineAbove.low 5) := by decide +kernel

--| THE ERROR BELOW AND THE ERROR ABOVE, AS REALS.
def theErrorBelow : Bracketed := cosineBelow.difference sineBelow 5 (Fraction.le_of_lt below_the_crossing_cosine_is_past_sine)
def theErrorAbove : Bracketed := sineAbove.difference cosineAbove 5 (Fraction.le_of_lt above_the_crossing_sine_is_past_cosine)

def theErrorBelowsLowWall : Fraction := ⟨4378, 10 ^ 19, by decide⟩
def theErrorBelowsHighWall : Fraction := ⟨4379, 10 ^ 19, by decide⟩
def theErrorAbovesLowWall : Fraction := ⟨9763, 10 ^ 19, by decide⟩
def theErrorAbovesHighWall : Fraction := ⟨9764, 10 ^ 19, by decide⟩

theorem at_its_first_stage_the_error_below_is_between :
    theErrorBelowsLowWall.le (theErrorBelow.low 0) ∧ (theErrorBelow.high 0).le theErrorBelowsHighWall := by
  decide +kernel

theorem at_its_first_stage_the_error_above_is_between :
    theErrorAbovesLowWall.le (theErrorAbove.low 0) ∧ (theErrorAbove.high 0).le theErrorAbovesHighWall := by
  decide +kernel

--| AT EVERY STAGE THE ERROR BELOW LIES BETWEEN 4.378 AND 4.379 PARTS IN TEN TO THE SIXTEENTH.
theorem the_error_below_is_between (n : Nat) :
    theErrorBelowsLowWall.le (theErrorBelow.low n) ∧ (theErrorBelow.high n).le theErrorBelowsHighWall :=
  ⟨Fraction.le_trans at_its_first_stage_the_error_below_is_between.1 (theErrorBelow.low_le_of_le (Nat.zero_le n)),
   Fraction.le_trans (theErrorBelow.high_le_of_le (Nat.zero_le n)) at_its_first_stage_the_error_below_is_between.2⟩

--| AT EVERY STAGE THE ERROR ABOVE LIES BETWEEN 9.763 AND 9.764 PARTS IN TEN TO THE SIXTEENTH.
theorem the_error_above_is_between (n : Nat) :
    theErrorAbovesLowWall.le (theErrorAbove.low n) ∧ (theErrorAbove.high n).le theErrorAbovesHighWall :=
  ⟨Fraction.le_trans at_its_first_stage_the_error_above_is_between.1 (theErrorAbove.low_le_of_le (Nat.zero_le n)),
   Fraction.le_trans (theErrorAbove.high_le_of_le (Nat.zero_le n)) at_its_first_stage_the_error_above_is_between.2⟩

--| NEITHER ERROR IS NOTHING.  At every stage the low wall is past nothing.
theorem the_errors_are_past_nothing (n : Nat) : 0 < (theErrorBelow.low n).over ∧ 0 < (theErrorAbove.low n).over :=
  ⟨Fraction.past_nothing_of_le (the_error_below_is_between n).1 (by decide),
   Fraction.past_nothing_of_le (the_error_above_is_between n).1 (by decide)⟩

--| Four times below, and four times above.
def theWindowsLowWall : Fraction := ⟨4 * below, places, by decide⟩
def theWindowsHighWall : Fraction := ⟨4 * above, places, by decide⟩

theorem at_its_first_stage_machins_half_turn_is_in_the_window :
    theWindowsLowWall.le (theHalfTurn.low 0) ∧ (theHalfTurn.high 0).le theWindowsHighWall := by decide +kernel

--| MACHIN'S HALF TURN IS IN THE SERIES' WINDOW.  At every stage, between 3.141592653589792 and 3.141592653589796.
theorem machins_half_turn_is_in_the_window (n : Nat) :
    theWindowsLowWall.le (theHalfTurn.low n) ∧ (theHalfTurn.high n).le theWindowsHighWall :=
  ⟨Fraction.le_trans at_its_first_stage_machins_half_turn_is_in_the_window.1 (theHalfTurn.low_le_of_le (Nat.zero_le n)),
   Fraction.le_trans (theHalfTurn.high_le_of_le (Nat.zero_le n)) at_its_first_stage_machins_half_turn_is_in_the_window.2⟩

/-! The slip: nothing, and then the sign for good.  Out of reach, and comparable. -/

--| Below, at stage k, sine's high wall is under cosine's low wall.
def partedBelow (k : Nat) : Prop := (sineBelow.high k).lt (cosineBelow.low k)
--| Above, at stage k, cosine's high wall is under sine's low wall.
def partedAbove (k : Nat) : Prop := (cosineAbove.high k).lt (sineAbove.low k)

instance : DecidablePred partedBelow := fun k => inferInstanceAs (Decidable ((sineBelow.high k).lt (cosineBelow.low k)))
instance : DecidablePred partedAbove := fun k => inferInstanceAs (Decidable ((cosineAbove.high k).lt (sineAbove.low k)))

--| BELOW, NOTHING UNTIL THE FOURTH STAGE.  At stages nothing to three the walls overlap and no sign can be read; at the
--| fourth they have parted.
theorem below_nothing_until_the_fourth_stage : (∀ k, k < 4 → ¬ partedBelow k) ∧ partedBelow 4 := by decide +kernel

--| ABOVE, NOTHING UNTIL THE THIRD.  The larger miss shows a stage sooner.
theorem above_nothing_until_the_third_stage : (∀ k, k < 3 → ¬ partedAbove k) ∧ partedAbove 3 := by decide +kernel

--| FOUND BY LOOKING.  The least stage where each side parts, found with the click and no choice, is four and three.
theorem the_least_stage_found_by_looking :
    (findByLooking partedBelow ⟨4, below_nothing_until_the_fourth_stage.2⟩).1 = 4
      ∧ (findByLooking partedAbove ⟨3, above_nothing_until_the_third_stage.2⟩).1 = 3 := by
  constructor
  · have spec := (findByLooking partedBelow ⟨4, below_nothing_until_the_fourth_stage.2⟩).2
    generalize (findByLooking partedBelow ⟨4, below_nothing_until_the_fourth_stage.2⟩).1 = m at spec ⊢
    rcases Nat.lt_or_ge m 4 with h | h
    · exact absurd spec.1 (below_nothing_until_the_fourth_stage.1 m h)
    · rcases Nat.lt_or_ge 4 m with h' | h'
      · exact absurd below_nothing_until_the_fourth_stage.2 (spec.2 4 h')
      · omega
  · have spec := (findByLooking partedAbove ⟨3, above_nothing_until_the_third_stage.2⟩).2
    generalize (findByLooking partedAbove ⟨3, above_nothing_until_the_third_stage.2⟩).1 = m at spec ⊢
    rcases Nat.lt_or_ge m 3 with h | h
    · exact absurd spec.1 (above_nothing_until_the_third_stage.1 m h)
    · rcases Nat.lt_or_ge 3 m with h' | h'
      · exact absurd above_nothing_until_the_third_stage.2 (spec.2 3 h')
      · omega

--| ONCE PARTED, PARTED FOR GOOD.  Walls only move inward.
theorem parted_below_for_good {n : Nat} (h : 4 ≤ n) : partedBelow n :=
  Fraction.le_lt_trans (sineBelow.high_le_of_le h)
    (Fraction.lt_le_trans below_nothing_until_the_fourth_stage.2 (cosineBelow.low_le_of_le h))

theorem parted_above_for_good {n : Nat} (h : 3 ≤ n) : partedAbove n :=
  Fraction.le_lt_trans (cosineAbove.high_le_of_le h)
    (Fraction.lt_le_trans above_nothing_until_the_third_stage.2 (sineAbove.low_le_of_le h))

--| THE COIN FLIP, TURNED OVER ACROSS THE CROSSING.  Once parted, the difference one way leaves something and the other
--| way leaves nothing: below, cosine less sine is something and sine less cosine nothing; above, the other way about.
theorem below_one_way_something_and_the_other_nothing {n : Nat} (h : 4 ≤ n) :
    0 < ((cosineBelow.low n).sub (sineBelow.high n)).over ∧ ((sineBelow.high n).sub (cosineBelow.low n)).over = 0 :=
  ⟨Fraction.sub_pos (parted_below_for_good h), Nat.sub_eq_zero_of_le (Nat.le_of_lt (parted_below_for_good h))⟩

theorem above_one_way_something_and_the_other_nothing {n : Nat} (h : 3 ≤ n) :
    0 < ((sineAbove.low n).sub (cosineAbove.high n)).over ∧ ((cosineAbove.high n).sub (sineAbove.low n)).over = 0 :=
  ⟨Fraction.sub_pos (parted_above_for_good h), Nat.sub_eq_zero_of_le (Nat.le_of_lt (parted_above_for_good h))⟩

--| OUT OF REACH, AND COMPARABLE.  Neither error is computed exactly, and at every pair of stages the error below is
--| under the error above.
theorem the_error_below_is_under_the_error_above (n m : Nat) : (theErrorBelow.high n).lt (theErrorAbove.low m) :=
  Fraction.le_lt_trans (the_error_below_is_between n).2
    (Fraction.lt_le_trans (by decide : theErrorBelowsHighWall.lt theErrorAbovesLowWall) (the_error_above_is_between m).1)

/-! The Borwein threshold. -/

--| One third, one fifth, and so on: n of them.
def borweinSum : Nat → Fraction
  | 0 => ⟨0, 1, Nat.one_pos⟩
  | n + 1 => (borweinSum n).add ⟨1, 2 * n + 3, by omega⟩

def theOne : Fraction := ⟨1, 1, Nat.one_pos⟩

--| THE BORWEIN THRESHOLD.  One third through one thirteenth is under one; through one fifteenth it is past.  That the
--| Borwein integral is exactly a quarter turn while the sum is under one, and falls short of it past one, by about 2.3
--| parts in a hundred thousand million at one fifteenth (D. and J. Borwein, 2001), is standard and not proved here: the
--| integrals are out of reach, and the threshold they slip at is a comparison of fractions.
theorem the_borwein_threshold : (borweinSum 6).lt theOne ∧ theOne.lt (borweinSum 7) := by decide +kernel

/-! Halving: the eighth turn found a bit at a time, handed the gap. -/

def cosAt (c n : Nat) (h : c ≤ 2 ^ n) : Bracketed := cosine c (2 ^ n) (Nat.two_pow_pos n) h
def sinAt (c n : Nat) (h : c ≤ 2 ^ n) : Bracketed := sine c (2 ^ n) (Nat.two_pow_pos n) h

--| At the angle c over two to the n, at stage k: cosine ahead, or sine ahead.
def cosAhead (c n : Nat) (h : c ≤ 2 ^ n) (k : Nat) : Prop := ((sinAt c n h).high k).lt ((cosAt c n h).low k)
def sinAhead (c n : Nat) (h : c ≤ 2 ^ n) (k : Nat) : Prop := ((cosAt c n h).high k).lt ((sinAt c n h).low k)
def partedAt (c n : Nat) (h : c ≤ 2 ^ n) (k : Nat) : Prop := cosAhead c n h k ∨ sinAhead c n h k

instance (c n : Nat) (h : c ≤ 2 ^ n) (k : Nat) : Decidable (cosAhead c n h k) :=
  inferInstanceAs (Decidable (Fraction.lt _ _))
instance (c n : Nat) (h : c ≤ 2 ^ n) (k : Nat) : Decidable (sinAhead c n h k) :=
  inferInstanceAs (Decidable (Fraction.lt _ _))
instance (c n : Nat) (h : c ≤ 2 ^ n) : DecidablePred (partedAt c n h) := fun _ => inferInstanceAs (Decidable (_ ∨ _))

theorem Fraction.lt_irrefl' (p : Fraction) : ¬ p.lt p := Nat.lt_irrefl _

--| ONE SIDE ONLY.  Cosine ahead at one stage and sine ahead at another cannot both be.
theorem one_side_only {c n : Nat} {h : c ≤ 2 ^ n} {k j : Nat} (hc : cosAhead c n h k) (hs : sinAhead c n h j) : False :=
  Fraction.lt_irrefl' _ (Fraction.lt_le_trans
    (Fraction.le_lt_trans (Fraction.le_of_lt (Fraction.lt_le_trans hc ((cosAt c n h).low_under_high k j))) hs)
    ((sinAt c n h).low_under_high j k))

--| THE GAP, HANDED IN.  At every dyadic angle not past one, the two series part at some stage.  It is not proved here:
--| it says no halving lands on the crossing, the irrationality of the half turn read on the halvings (Lambert, 1761).
def TheGap : Prop := ∀ n c (h : c ≤ 2 ^ n), ∃ k, partedAt c n h k

theorem midpoint_bound {c n : Nat} (hc : c < 2 ^ n) : 2 * c + 1 ≤ 2 ^ (n + 1) := by rw [Nat.pow_succ]; omega
theorem up_bound {c n : Nat} (hc : c < 2 ^ n) : 2 * c + 1 < 2 ^ (n + 1) := by rw [Nat.pow_succ]; omega
theorem down_bound {c n : Nat} (hc : c < 2 ^ n) : 2 * c < 2 ^ (n + 1) := by rw [Nat.pow_succ]; omega

--| ONE HALVING.  Look at the midpoint until the series part; if cosine is ahead the crossing is above it, else below.
def halve (gap : TheGap) (n c : Nat) (hc : c < 2 ^ n) : { c' // c' < 2 ^ (n + 1) } :=
  if cosAhead (2 * c + 1) (n + 1) (midpoint_bound hc)
      (findByLooking (partedAt (2 * c + 1) (n + 1) (midpoint_bound hc)) (gap _ _ _)).1
  then ⟨2 * c + 1, up_bound hc⟩ else ⟨2 * c, down_bound hc⟩

--| THE CUT AFTER n HALVINGS.  The eighth turn lies between it and one more, over two to the n.
def cutOf (gap : TheGap) : (n : Nat) → { c // c < 2 ^ n }
  | 0 => ⟨0, by decide⟩
  | n + 1 => halve gap n (cutOf gap n).1 (cutOf gap n).2

theorem halve_up (gap : TheGap) (n c : Nat) (hc : c < 2 ^ n) (k : Nat)
    (h : cosAhead (2 * c + 1) (n + 1) (midpoint_bound hc) k) : (halve gap n c hc).1 = 2 * c + 1 := by
  unfold halve; split
  · rfl
  · rename_i no
    rcases (findByLooking (partedAt (2 * c + 1) (n + 1) (midpoint_bound hc)) (gap _ _ _)).2.1 with yes | s
    · exact absurd yes no
    · exact (one_side_only h s).elim

theorem halve_down (gap : TheGap) (n c : Nat) (hc : c < 2 ^ n) (k : Nat)
    (h : sinAhead (2 * c + 1) (n + 1) (midpoint_bound hc) k) : (halve gap n c hc).1 = 2 * c := by
  unfold halve; split
  · rename_i yes; exact (one_side_only yes h).elim
  · rfl

theorem next_up (gap : TheGap) (n c : Nat) (e : (cutOf gap n).1 = c) (hc : c < 2 ^ n) (k : Nat)
    (h : cosAhead (2 * c + 1) (n + 1) (midpoint_bound hc) k) : (cutOf gap (n + 1)).1 = 2 * c + 1 := by
  have key : ∀ x : { c // c < 2 ^ n }, x.1 = c → (halve gap n x.1 x.2).1 = 2 * c + 1 := by
    intro x ex; obtain ⟨x, hx⟩ := x; dsimp only at ex; subst ex; exact halve_up gap n x hx k h
  exact key (cutOf gap n) e

theorem next_down (gap : TheGap) (n c : Nat) (e : (cutOf gap n).1 = c) (hc : c < 2 ^ n) (k : Nat)
    (h : sinAhead (2 * c + 1) (n + 1) (midpoint_bound hc) k) : (cutOf gap (n + 1)).1 = 2 * c := by
  have key : ∀ x : { c // c < 2 ^ n }, x.1 = c → (halve gap n x.1 x.2).1 = 2 * c := by
    intro x ex; obtain ⟨x, hx⟩ := x; dsimp only at ex; subst ex; exact halve_down gap n x hx k h
  exact key (cutOf gap n) e

--| THE FIRST TWELVE HALVINGS.  Whatever gap is handed in, the cut after twelve is 3216: each midpoint is decided by the
--| kernel at its first or second stage, and the bits are 1, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0.
theorem the_first_twelve_halvings (gap : TheGap) : (cutOf gap 12).1 = 3216 := by
  have c1 := next_up gap 0 0 rfl (by decide) 0 (by decide +kernel)
  have c2 := next_up gap 1 1 c1 (by decide) 0 (by decide +kernel)
  have c3 := next_down gap 2 3 c2 (by decide) 0 (by decide +kernel)
  have c4 := next_down gap 3 6 c3 (by decide) 0 (by decide +kernel)
  have c5 := next_up gap 4 12 c4 (by decide) 1 (by decide +kernel)
  have c6 := next_down gap 5 25 c5 (by decide) 0 (by decide +kernel)
  have c7 := next_down gap 6 50 c6 (by decide) 0 (by decide +kernel)
  have c8 := next_up gap 7 100 c7 (by decide) 1 (by decide +kernel)
  have c9 := next_down gap 8 201 c8 (by decide) 1 (by decide +kernel)
  have c10 := next_down gap 9 402 c9 (by decide) 1 (by decide +kernel)
  have c11 := next_down gap 10 804 c10 (by decide) 1 (by decide +kernel)
  exact next_down gap 11 1608 c11 (by decide) 1 (by decide +kernel)

--| THE EIGHTH TURN BY HALVING: a real with no choice, handed the gap.
def theEighthTurnByHalving (gap : TheGap) : DyadicCut where
  cut n := (cutOf gap n).1
  doubles n := by
    show 2 * (cutOf gap n).1 ≤ (halve gap n (cutOf gap n).1 (cutOf gap n).2).1
      ∧ (halve gap n (cutOf gap n).1 (cutOf gap n).2).1 ≤ 2 * (cutOf gap n).1 + 1
    unfold halve; split <;> exact ⟨by dsimp only; omega, by dsimp only; omega⟩

/-! The record and its arrow. -/

--| THE PRESENT HALVED IS THE PAST.  The cut before is read off the cut after, with nothing handed in.
theorem the_present_halved_is_the_past (gap : TheGap) (n : Nat) : (cutOf gap (n + 1)).1 / 2 = (cutOf gap n).1 := by
  have := (theEighthTurnByHalving gap).doubles n
  show (theEighthTurnByHalving gap).cut (n + 1) / 2 = (theEighthTurnByHalving gap).cut n
  omega

--| THE RECORD NEVER FALLS.
theorem the_record_never_falls (gap : TheGap) (n : Nat) : (cutOf gap n).1 ≤ (cutOf gap (n + 1)).1 := by
  have := (theEighthTurnByHalving gap).doubles n
  show (theEighthTurnByHalving gap).cut n ≤ (theEighthTurnByHalving gap).cut (n + 1)
  omega

--| THE PAST DOES NOT GIVE THE NEXT BIT.  Both futures halve to the same past; the bit is what the comparison returned.
theorem both_futures_halve_to_one_past (c : Nat) : (2 * c) / 2 = c ∧ (2 * c + 1) / 2 = c := ⟨by omega, by omega⟩

--| DOUBLING FORGETS THE TOP BIT.  Read as an angle, doubling wraps round: c and c and a half turn's worth land alike.
theorem doubling_forgets_the_top_bit (c n : Nat) : (2 * (c + 2 ^ n)) % 2 ^ (n + 1) = (2 * c) % 2 ^ (n + 1) := by
  rw [Nat.mul_add, ← Nat.pow_succ', Nat.add_mod_right]

--| MACHIN'S HALF TURN IS WITHIN THE TWELFTH HALVING.  Four times 3216 and 3217 over 4096 hold it at every stage.
theorem machins_half_turn_is_within_the_twelfth_halving (n : Nat) :
    (⟨4 * 3216, 4096, by decide⟩ : Fraction).le (theHalfTurn.low n) ∧ (theHalfTurn.high n).le ⟨4 * 3217, 4096, by decide⟩ :=
  ⟨Fraction.le_trans (by decide : (⟨4 * 3216, 4096, by decide⟩ : Fraction).le theWindowsLowWall)
      (machins_half_turn_is_in_the_window n).1,
   Fraction.le_trans (machins_half_turn_is_in_the_window n).2 (by decide : theWindowsHighWall.le ⟨4 * 3217, 4096, by decide⟩)⟩

/-! The other one: doubling, and the baker who keeps what it forgets. -/

theorem the_first_halving (gap : TheGap) : (cutOf gap 1).1 = 1 := next_up gap 0 0 rfl (by decide) 0 (by decide +kernel)

--| The eighth turn's record, found by halving.
def theEighthTurnsRecord (gap : TheGap) : UnitCut :=
  ⟨(theEighthTurnByHalving gap).cut, (theEighthTurnByHalving gap).doubles, rfl⟩

--| BAKED ONCE.  The first record doubled: after eleven halvings it is 1168, the record of twice the eighth turn less one;
--| the bit it read is laid on the record of nothing, which becomes the record of one half.
theorem the_eighth_turn_baked_once (gap : TheGap) :
    (UnitCut.bake (theEighthTurnsRecord gap, UnitCut.nothing)).1.cut 11 = 1168
      ∧ ∀ n, (UnitCut.bake (theEighthTurnsRecord gap, UnitCut.nothing)).2.cut (n + 1) = 2 ^ n := by
  constructor
  · show (cutOf gap 12).1 - (cutOf gap 1).1 * 2 ^ 11 = 1168
    rw [the_first_twelve_halvings, the_first_halving]
  · intro n
    show (cutOf gap 1).1 * 2 ^ n + 0 = 2 ^ n
    rw [the_first_halving, Nat.one_mul, Nat.add_zero]

--| AND BACK.  Run backward, the baker returns the eighth turn's record and the record of nothing, exactly.
theorem the_eighth_turn_baked_and_back (gap : TheGap) :
    UnitCut.unbake (UnitCut.bake (theEighthTurnsRecord gap, UnitCut.nothing)) = (theEighthTurnsRecord gap, UnitCut.nothing) :=
  UnitCut.theBaker.there_then_back _

--| DOUBLING ALONE FORGETS.  The eighth turn, and the eighth turn less one half, double to one record, and are not one.
theorem the_eighth_turn_and_it_less_a_half_double_alike (gap : TheGap) :
    UnitCut.doubled (UnitCut.pushed 0 (by decide) (UnitCut.doubled (theEighthTurnsRecord gap)))
        = UnitCut.doubled (theEighthTurnsRecord gap)
      ∧ UnitCut.pushed 0 (by decide) (UnitCut.doubled (theEighthTurnsRecord gap)) ≠ theEighthTurnsRecord gap := by
  have top : (theEighthTurnsRecord gap).cut 1 = 1 := the_first_halving gap
  have back : UnitCut.pushed 1 (by decide) (UnitCut.doubled (theEighthTurnsRecord gap)) = theEighthTurnsRecord gap := by
    have : ∀ t (ht : t ≤ 1), t = (theEighthTurnsRecord gap).cut 1 →
        UnitCut.pushed t ht (UnitCut.doubled (theEighthTurnsRecord gap)) = theEighthTurnsRecord gap := by
      intro t ht et; subst et; exact UnitCut.pushed_doubled _
    exact this 1 _ top.symm
  obtain ⟨same, differ⟩ := UnitCut.doubling_forgets (UnitCut.doubled (theEighthTurnsRecord gap))
  rw [back] at same differ
  exact ⟨same, differ⟩

end EighthTurn
end Meanings
