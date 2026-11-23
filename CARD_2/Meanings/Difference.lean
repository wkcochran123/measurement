/-
The difference of two reals, and one over a signed real, with no choice.

Nothing is ever subtracted in a signed real: it is held and owed.  To take one real from another and get a real, the one
taken away must not be past the one it is taken from, and that shows at a stage: the high wall of the second not past the
low wall of the first.  From that stage on, the low wall of the difference is the first's low wall less the second's high,
and the high wall is the first's high less the second's low, and no subtraction runs past nothing.  The widths add, so the
walls are read as far on as the stage and twice the stage asked for and one.

The difference beside what was taken away is what it was taken from.  So a signed real whose held is past its owed at a
stage is one with the difference held and nothing owed; and one over it is one over that difference, held.  When the owed
is past the held, one over it is one over the other difference, owed.  Either way, a signed real by one over itself is one.
Which way it goes is handed in with the stage; a signed real does not say of itself which side of nothing it is on.

Not here: one over a complex number or a quaternion (one over the square of the norm, which wants the norm squared shown
past nothing at a stage), and an order on the signed reals.
-/
import Meanings.Reciprocal

namespace Meanings

--| Past, by crossing.
def Fraction.lt (p q : Fraction) : Prop := p.over * q.under < q.over * p.under

--| A factor on both sides of past can be taken away.  Written out: core Lean's own lemma for this bills choice.
theorem lt_of_mul_lt_mul_on_the_right {a b c : Nat} (h : a * c < b * c) : a < b :=
  Nat.lt_of_not_le fun hba => Nat.not_le_of_lt h (Nat.mul_le_mul_right c hba)

theorem Fraction.le_lt_trans {p q r : Fraction} (h1 : p.le q) (h2 : q.lt r) : p.lt r := by
  unfold Fraction.le Fraction.lt at *
  apply lt_of_mul_lt_mul_on_the_right (c := q.under)
  calc p.over * r.under * q.under = p.over * q.under * r.under := by ac_rfl
    _ ≤ q.over * p.under * r.under := Nat.mul_le_mul_right _ h1
    _ = q.over * r.under * p.under := by ac_rfl
    _ < r.over * q.under * p.under := Nat.mul_lt_mul_of_pos_right h2 p.under_pos
    _ = r.over * p.under * q.under := by ac_rfl

theorem Fraction.lt_le_trans {p q r : Fraction} (h1 : p.lt q) (h2 : q.le r) : p.lt r := by
  unfold Fraction.le Fraction.lt at *
  apply lt_of_mul_lt_mul_on_the_right (c := q.under)
  calc p.over * r.under * q.under = p.over * q.under * r.under := by ac_rfl
    _ < q.over * p.under * r.under := Nat.mul_lt_mul_of_pos_right h1 r.under_pos
    _ = q.over * r.under * p.under := by ac_rfl
    _ ≤ r.over * q.under * p.under := Nat.mul_le_mul_right _ h2
    _ = r.over * p.under * q.under := by ac_rfl

theorem Fraction.le_of_lt {p q : Fraction} (h : p.lt q) : p.le q := Nat.le_of_lt h

--| LESS, for fractions (`Fraction.sub`, written with the series): over by under less over by under, under by under.  It runs
--| past nothing only when asked to.

theorem Fraction.sub_pos {p q : Fraction} (h : q.lt p) : 0 < (p.sub q).over := Nat.sub_pos_of_lt h

--| Less keeps the order: more from which, less taken away.
theorem the_differences_keep_the_order (a b c d a' b' c' d' A B : Nat)
    (hA : A + c * b = a * d) (hB : B + c' * b' = a' * d')
    (hp : a * b' ≤ a' * b) (hq : c' * d ≤ c * d') :
    A * (b' * d') ≤ B * (b * d) := by
  have m1 := congrArg (· * (b' * d')) hA
  have m2 := congrArg (· * (b * d)) hB
  have m3 := Nat.mul_le_mul_right (d * d') hp
  have m4 := Nat.mul_le_mul_right (b * b') hq
  simp only [Nat.add_mul] at m1 m2 m3 m4 ⊢
  simp only [Nat.mul_comm, Nat.mul_left_comm] at m1 m2 m3 m4 ⊢
  omega

theorem Fraction.sub_le_sub {p p' q q' : Fraction} (hqp : q.le p) (hq'p' : q'.le p') (hp : p.le p') (hq : q'.le q) :
    (p.sub q).le (p'.sub q') := by
  unfold Fraction.le at *
  unfold Fraction.sub
  dsimp only
  exact the_differences_keep_the_order p.over p.under q.over q.under p'.over p'.under q'.over q'.under _ _
    (Nat.sub_add_cancel hqp) (Nat.sub_add_cancel hq'p') hp hq

--| The widths of a difference add: each width one part in twice as many, the difference's one part in as many.
theorem the_widths_subtract (a b a' b' c d c' d' H L N : Nat)
    (h1 : a' * b * (N + N) ≤ a * b' * (N + N) + b' * b)
    (h2 : c' * d * (N + N) ≤ c * d' * (N + N) + d' * d)
    (hH : H + c * b' = a' * d) (hL : L + c' * b = a * d') :
    H * (b * d') * N ≤ L * (b' * d) * N + (b' * d) * (b * d') := by
  have m1 := congrArg (· * (b * d' * N)) hH
  have m2 := congrArg (· * (b' * d * N)) hL
  have m3 := Nat.mul_le_mul_right (d * d') h1
  have m4 := Nat.mul_le_mul_right (b * b') h2
  simp only [Nat.add_mul, Nat.mul_add] at m1 m2 m3 m4 ⊢
  simp only [Nat.mul_comm, Nat.mul_left_comm] at m1 m2 m3 m4 ⊢
  omega

--| How far on the difference reads: the stage handed in, and twice the stage asked for and one.
def Bracketed.differenceStage (k n : Nat) : Nat := k + (2 * n + 1)

--| From the stage handed in, the second's high wall is not past the first's low wall, and the second's low not past the
--| first's high.
theorem Bracketed.apart_on {x y : Bracketed} {k : Nat} (apart : (y.high k).le (x.low k)) {s : Nat} (hs : k ≤ s) :
    (y.high s).le (x.low s) :=
  Fraction.le_trans (y.high_le_of_le hs) (Fraction.le_trans apart (x.low_le_of_le hs))

theorem Bracketed.apart_on_far {x y : Bracketed} {k : Nat} (apart : (y.high k).le (x.low k)) {s : Nat} (hs : k ≤ s) :
    (y.low s).le (x.high s) :=
  Fraction.le_trans (y.ordered s) (Fraction.le_trans (Bracketed.apart_on apart hs) (x.ordered s))

--| THE DIFFERENCE OF TWO REALS, from a stage where the second is not past the first.
def Bracketed.difference (x y : Bracketed) (k : Nat) (apart : (y.high k).le (x.low k)) : Bracketed where
  low n := (x.low (Bracketed.differenceStage k n)).sub (y.high (Bracketed.differenceStage k n))
  high n := (x.high (Bracketed.differenceStage k n)).sub (y.low (Bracketed.differenceStage k n))
  ordered _ := Fraction.sub_le_sub (Bracketed.apart_on apart (Nat.le_add_right _ _))
    (Bracketed.apart_on_far apart (Nat.le_add_right _ _)) (x.ordered _) (y.ordered _)
  low_rises n := Fraction.sub_le_sub (Bracketed.apart_on apart (Nat.le_add_right _ _))
    (Bracketed.apart_on apart (Nat.le_add_right _ _))
    (x.low_le_of_le (by unfold Bracketed.differenceStage; omega)) (y.high_le_of_le (by unfold Bracketed.differenceStage; omega))
  high_falls n := Fraction.sub_le_sub (Bracketed.apart_on_far apart (Nat.le_add_right _ _))
    (Bracketed.apart_on_far apart (Nat.le_add_right _ _))
    (x.high_le_of_le (by unfold Bracketed.differenceStage; omega)) (y.low_le_of_le (by unfold Bracketed.differenceStage; omega))
  narrows n := by
    have s1 := fewer_parts _ _ _ (n + 1 + (n + 1)) _ (x.narrows (Bracketed.differenceStage k n))
      (by unfold Bracketed.differenceStage; omega)
    have s2 := fewer_parts _ _ _ (n + 1 + (n + 1)) _ (y.narrows (Bracketed.differenceStage k n))
      (by unfold Bracketed.differenceStage; omega)
    exact the_widths_subtract _ _ _ _ _ _ _ _ _ _ (n + 1) s1 s2
      (Nat.sub_add_cancel (Bracketed.apart_on_far apart (Nat.le_add_right _ _)))
      (Nat.sub_add_cancel (Bracketed.apart_on apart (Nat.le_add_right _ _)))

--| A difference, and beside it what was taken away, against what it was taken from.
theorem the_difference_and_the_rest_is_not_past (po pu qo qu ro ru A : Nat)
    (hA : A + qo * pu = po * qu) (hr : ro * qu ≤ qo * ru) :
    (A * ru + ro * (pu * qu)) * pu ≤ po * (pu * qu * ru) := by
  have m1 := congrArg (· * (ru * pu)) hA
  have m2 := Nat.mul_le_mul_right (pu * pu) hr
  simp only [Nat.add_mul] at m1 m2 ⊢
  simp only [Nat.mul_comm, Nat.mul_left_comm] at m1 m2 ⊢
  omega

theorem the_difference_and_the_rest_is_not_under (po pu qo qu ro ru so su A : Nat)
    (hA : A + qo * pu = po * qu) (hs : so * pu ≤ po * su) (hr : qo * ru ≤ ro * qu) :
    so * (pu * qu * ru) ≤ (A * ru + ro * (pu * qu)) * su := by
  have m1 := congrArg (· * (ru * su)) hA
  have m2 := Nat.mul_le_mul_right (qu * ru) hs
  have m3 := Nat.mul_le_mul_right (pu * su) hr
  simp only [Nat.add_mul] at m1 m2 m3 ⊢
  simp only [Nat.mul_comm, Nat.mul_left_comm] at m1 m2 m3 ⊢
  omega

theorem Fraction.sub_add_le {p q r : Fraction} (hqp : q.le p) (hr : r.le q) : ((p.sub q).add r).le p := by
  unfold Fraction.le at *
  unfold Fraction.add Fraction.sub
  dsimp only
  exact the_difference_and_the_rest_is_not_past _ _ _ _ _ _ _ (Nat.sub_add_cancel hqp) hr

theorem Fraction.le_sub_add {p q r s : Fraction} (hqp : q.le p) (hs : s.le p) (hr : q.le r) : s.le ((p.sub q).add r) := by
  unfold Fraction.le at *
  unfold Fraction.add Fraction.sub
  dsimp only
  exact the_difference_and_the_rest_is_not_under _ _ _ _ _ _ _ _ _ (Nat.sub_add_cancel hqp) hs hr

--| THE DIFFERENCE BESIDE WHAT WAS TAKEN AWAY IS WHAT IT WAS TAKEN FROM.
theorem Bracketed.difference_add (x y : Bracketed) (k : Nat) (apart : (y.high k).le (x.low k)) :
    ((x.difference y k apart).add y).Same x := fun _ _ =>
  ⟨Fraction.le_trans
    (Fraction.sub_add_le (Bracketed.apart_on apart (Nat.le_add_right _ _)) (y.low_under_high _ _))
    (x.low_under_high _ _),
   Fraction.le_sub_add (Bracketed.apart_on_far apart (Nat.le_add_right _ _)) (x.low_under_high _ _) (y.low_under_high _ _)⟩

--| Strictly apart at a stage: the difference is past nothing at its first stage.
theorem Bracketed.difference_past_nothing (x y : Bracketed) (k : Nat) (strict : (y.high k).lt (x.low k)) :
    0 < ((x.difference y k (Fraction.le_of_lt strict)).low 0).over :=
  Fraction.sub_pos (Fraction.le_lt_trans (y.high_le_of_le (Nat.le_add_right _ _))
    (Fraction.lt_le_trans strict (x.low_le_of_le (Nat.le_add_right _ _))))

instance : @Trans Bracketed Bracketed Bracketed Bracketed.Same Bracketed.Same Bracketed.Same := ⟨Bracketed.same_trans⟩

--| Whole numbers, beside and each for each, as reals: every wall a whole number, the same at every stage.
theorem Bracketed.ofNat_add (a b : Nat) : ((Bracketed.ofNat a).add (Bracketed.ofNat b)).Same (Bracketed.ofNat (a + b)) :=
  fun _ _ => ⟨by show (a * 1 + b * 1) * 1 ≤ (a + b) * (1 * 1); simp, by show (a + b) * (1 * 1) ≤ (a * 1 + b * 1) * 1; simp⟩

theorem Bracketed.ofNat_mul (a b : Nat) : ((Bracketed.ofNat a).mul (Bracketed.ofNat b)).Same (Bracketed.ofNat (a * b)) :=
  fun _ _ => ⟨by show a * b * 1 ≤ a * b * (1 * 1); simp, by show a * b * (1 * 1) ≤ a * b * 1; simp⟩

theorem Bracketed.mul_zero (x : Bracketed) : (x.mul (Bracketed.ofNat 0)).Same (Bracketed.ofNat 0) :=
  Bracketed.same_trans (Bracketed.mul_comm _ _) (Bracketed.zero_mul x)

namespace SignedReal

theorem ofReal_same {a b : Bracketed} (h : a.Same b) : (ofReal a).Same (ofReal b) := of_parts h (Bracketed.same_refl _)

--| A real held by a real held is their product held.
theorem ofReal_mul (a b : Bracketed) : (ofReal a * ofReal b).Same (ofReal (a.mul b)) :=
  of_parts
    (Bracketed.same_trans (Bracketed.add_same (Bracketed.same_refl _) (Bracketed.zero_mul _)) (Bracketed.add_zero _))
    (Bracketed.same_trans (Bracketed.add_same (Bracketed.mul_zero _) (Bracketed.zero_mul _)) (Bracketed.zero_add _))

--| HELD PAST OWED: the signed real is the difference, held.
theorem is_its_difference_held (x : SignedReal) (k : Nat) (apart : (x.owed.high k).le (x.held.low k)) :
    x.Same (ofReal (x.held.difference x.owed k apart)) :=
  Bracketed.same_trans (Bracketed.add_zero _) (Bracketed.same_symm (Bracketed.difference_add x.held x.owed k apart))

--| OWED PAST HELD: the signed real is the other difference, owed.
theorem is_its_difference_owed (x : SignedReal) (k : Nat) (apart : (x.held.high k).le (x.owed.low k)) :
    x.Same (-ofReal (x.owed.difference x.held k apart)) :=
  Bracketed.same_trans (Bracketed.add_comm _ _)
    (Bracketed.same_trans (Bracketed.difference_add x.owed x.held k apart) (Bracketed.same_symm (Bracketed.zero_add _)))

--| ONE OVER A SIGNED REAL WHOSE HELD IS PAST ITS OWED AT A STAGE: one over the difference, held.
def reciprocalHeld (x : SignedReal) (k : Nat) (strict : (x.owed.high k).lt (x.held.low k)) : SignedReal :=
  ofReal ((x.held.difference x.owed k (Fraction.le_of_lt strict)).reciprocal 0
    (Bracketed.difference_past_nothing _ _ _ strict))

--| ONE OVER A SIGNED REAL WHOSE OWED IS PAST ITS HELD AT A STAGE: one over the other difference, owed.
def reciprocalOwed (x : SignedReal) (k : Nat) (strict : (x.held.high k).lt (x.owed.low k)) : SignedReal :=
  -ofReal ((x.owed.difference x.held k (Fraction.le_of_lt strict)).reciprocal 0
    (Bracketed.difference_past_nothing _ _ _ strict))

--| A SIGNED REAL BY ONE OVER ITSELF IS ONE, either way.
theorem mul_reciprocalHeld (x : SignedReal) (k : Nat) (strict : (x.owed.high k).lt (x.held.low k)) :
    (x * x.reciprocalHeld k strict).Same (ofNat 1) :=
  same_trans (mul_same_left (x.is_its_difference_held k (Fraction.le_of_lt strict)) _)
    (same_trans (ofReal_mul _ _) (ofReal_same (Bracketed.mul_reciprocal _ _ _)))

theorem mul_reciprocalOwed (x : SignedReal) (k : Nat) (strict : (x.held.high k).lt (x.owed.low k)) :
    (x * x.reciprocalOwed k strict).Same (ofNat 1) :=
  same_trans (mul_same_left (x.is_its_difference_owed k (Fraction.le_of_lt strict)) _)
    (same_trans (neg_mul_neg _ _) (same_trans (ofReal_mul _ _) (ofReal_same (Bracketed.mul_reciprocal _ _ _))))

end SignedReal

end Meanings
