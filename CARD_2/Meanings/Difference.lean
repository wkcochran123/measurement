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

And one over a complex number: its conjugate by one over its norm squared, the norm squared handed in held past owed at a
stage.  One over is one thing, for signed reals and complex numbers alike.

And one over a quaternion, the conjugate by one over its norm squared, on either side; one over is one thing there too.

Not here: an order on the signed reals.
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

instance (p q : Fraction) : Decidable (p.lt q) := inferInstanceAs (Decidable (_ < _))

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

namespace SignedReal

instance : @Trans SignedReal SignedReal SignedReal Same Same Same := ⟨same_trans⟩

theorem neg_neg (x : SignedReal) : -(-x) = x := rfl

theorem mul_one (x : SignedReal) : (x * ofNat 1).Same x := same_trans (mul_comm _ _) (one_mul x)

theorem mul_zero (x : SignedReal) : (x * ofNat 0).Same (ofNat 0) := same_trans (mul_comm _ _) (zero_mul x)

--| A real held beside a real held is their sum held.
theorem ofReal_add (a b : Bracketed) : (ofReal a + ofReal b).Same (ofReal (a.add b)) :=
  of_parts (Bracketed.same_refl _) (Bracketed.zero_add _)

--| ONE OVER IS ONE THING: two that each make one with the same signed real are one.
theorem reciprocal_unique {x u v : SignedReal} (hu : (x * u).Same (ofNat 1)) (hv : (x * v).Same (ofNat 1)) : u.Same v :=
  same_trans (same_symm (mul_one u))
    (same_trans (mul_same_right u (same_symm hv))
      (same_trans (same_symm (mul_assoc _ _ _))
        (same_trans (mul_same_left (mul_comm _ _) v)
          (same_trans (mul_same_left hu v) (one_mul v)))))

end SignedReal

/-
One over a complex number: the conjugate, by one over the norm squared.  The norm squared, along by along beside across by
across, is a signed real, and it is handed in held past owed at a stage, as for any signed real.  Then the complex number
by one over itself is one; and one over is one thing.
-/
namespace ComplexReal

def normSquared (z : ComplexReal) : SignedReal := z.along * z.along + z.across * z.across

--| ONE OVER A COMPLEX NUMBER, from a stage where its norm squared is held past owed.
def reciprocal (z : ComplexReal) (k : Nat) (strict : (z.normSquared.owed.high k).lt (z.normSquared.held.low k)) :
    ComplexReal :=
  ⟨z.along * z.normSquared.reciprocalHeld k strict, -(z.across * z.normSquared.reciprocalHeld k strict)⟩

theorem ofSigned_same {x y : SignedReal} (h : x.Same y) : (ofSigned x).Same (ofSigned y) := ⟨h, SignedReal.same_refl _⟩

--| A complex number by its conjugate is its norm squared, along.
theorem mul_conjugate (z : ComplexReal) : (z * z.conjugate).Same (ofSigned z.normSquared) := by
  constructor
  · show (z.along * z.along + -(z.across * -z.across)).Same (z.along * z.along + z.across * z.across)
    simp only [SignedReal.mul_neg, SignedReal.neg_neg]
    exact SignedReal.same_refl _
  · show (z.along * -z.across + z.across * z.along).Same (SignedReal.ofNat 0)
    simp only [SignedReal.mul_neg]
    exact SignedReal.same_trans (SignedReal.add_same (SignedReal.neg_same (SignedReal.mul_comm _ _)) (SignedReal.same_refl _))
      (SignedReal.same_trans (SignedReal.add_comm _ _) (SignedReal.add_neg _))

--| A COMPLEX NUMBER BY ONE OVER ITSELF IS ONE.
theorem mul_reciprocal (z : ComplexReal) (k : Nat) (strict : (z.normSquared.owed.high k).lt (z.normSquared.held.low k)) :
    (z * z.reciprocal k strict).Same (ofNat 1) := by
  have key := SignedReal.mul_reciprocalHeld z.normSquared k strict
  unfold ComplexReal.reciprocal
  generalize z.normSquared.reciprocalHeld k strict = r at key ⊢
  unfold ComplexReal.normSquared at key
  constructor
  · show (z.along * (z.along * r) + -(z.across * -(z.across * r))).Same (SignedReal.ofNat 1)
    simp only [SignedReal.mul_neg, SignedReal.neg_neg]
    exact SignedReal.same_trans
      (SignedReal.add_same (SignedReal.same_symm (SignedReal.mul_assoc _ _ _)) (SignedReal.same_symm (SignedReal.mul_assoc _ _ _)))
      (SignedReal.same_trans (SignedReal.same_symm (SignedReal.add_mul _ _ _)) key)
  · show (z.along * -(z.across * r) + z.across * (z.along * r)).Same (SignedReal.ofNat 0)
    simp only [SignedReal.mul_neg]
    have swap : (z.along * (z.across * r)).Same (z.across * (z.along * r)) :=
      SignedReal.same_trans (SignedReal.same_symm (SignedReal.mul_assoc _ _ _))
        (SignedReal.same_trans (SignedReal.mul_same_left (SignedReal.mul_comm _ _) r) (SignedReal.mul_assoc _ _ _))
    exact SignedReal.same_trans (SignedReal.add_same (SignedReal.neg_same swap) (SignedReal.same_refl _))
      (SignedReal.same_trans (SignedReal.add_comm _ _) (SignedReal.add_neg _))

--| ONE OVER IS ONE THING.
theorem reciprocal_unique {z u v : ComplexReal} (hu : (z * u).Same (ofNat 1)) (hv : (z * v).Same (ofNat 1)) : u.Same v :=
  same_trans (same_symm (mul_one u))
    (same_trans (mul_same (same_refl u) (same_symm hv))
      (same_trans (same_symm (mul_assoc _ _ _))
        (same_trans (mul_same (mul_comm _ _) (same_refl v))
          (same_trans (mul_same hu (same_refl v)) (one_mul v)))))

--| Signed reals along, each for each, are their product along.
theorem ofSigned_mul (x y : SignedReal) : (ofSigned x * ofSigned y).Same (ofSigned (x * y)) := by
  constructor
  · show (x * y + -(SignedReal.ofNat 0 * SignedReal.ofNat 0)).Same (x * y)
    exact SignedReal.same_trans (SignedReal.add_same (SignedReal.same_refl _) (SignedReal.neg_same (SignedReal.zero_mul _)))
      (SignedReal.add_zero _)
  · show (x * SignedReal.ofNat 0 + SignedReal.ofNat 0 * y).Same (SignedReal.ofNat 0)
    exact SignedReal.same_trans (SignedReal.add_same (SignedReal.mul_zero _) (SignedReal.zero_mul _)) (SignedReal.zero_add _)

end ComplexReal

/-
One over a quaternion: the conjugate, the first turned across the line and the second owed, by one over the norm squared,
the first's norm squared beside the second's.  The product does not commute, so one over is shown on both sides; and then
one over is one thing: whatever makes one when the quaternion is put before it is the quaternion's one over.
-/
namespace ComplexReal

theorem neg_neg (z : ComplexReal) : -(-z) = z := rfl

theorem ofSigned_add (x y : SignedReal) : (ofSigned x + ofSigned y).Same (ofSigned (x + y)) :=
  ⟨SignedReal.same_refl _, SignedReal.zero_add _⟩

theorem conjugate_ofSigned (x : SignedReal) : (ofSigned x).conjugate = ofSigned x := rfl

theorem neg_mul_neg (z w : ComplexReal) : ((-z) * (-w)).Same (z * w) := by
  have h := neg_mul z (-w)
  rw [mul_neg z w, neg_neg (z * w)] at h
  exact h

--| The conjugate by the number is the number's norm squared too.
theorem conjugate_mul_self (z : ComplexReal) : (z.conjugate * z).Same (ofSigned z.normSquared) :=
  same_trans (mul_comm _ _) (mul_conjugate z)

end ComplexReal

namespace QuaternionReal

def normSquared (p : QuaternionReal) : SignedReal := p.first.normSquared + p.second.normSquared

theorem neg_neg (p : QuaternionReal) : -(-p) = p := rfl

--| ONE OVER A QUATERNION, from a stage where its norm squared is held past owed.
def reciprocal (p : QuaternionReal) (k : Nat) (strict : (p.normSquared.owed.high k).lt (p.normSquared.held.low k)) :
    QuaternionReal :=
  ⟨p.first.conjugate * ComplexReal.ofSigned (p.normSquared.reciprocalHeld k strict),
   -(p.second * ComplexReal.ofSigned (p.normSquared.reciprocalHeld k strict))⟩

--| The two norms squared, along, by one over their sum, along, is one.
theorem the_norms_by_one_over (x y r : SignedReal) (key : ((x + y) * r).Same (SignedReal.ofNat 1)) :
    ((ComplexReal.ofSigned x + ComplexReal.ofSigned y) * ComplexReal.ofSigned r).Same (ComplexReal.ofNat 1) :=
  ComplexReal.same_trans (ComplexReal.mul_same (ComplexReal.ofSigned_add x y) (ComplexReal.same_refl _))
    (ComplexReal.same_trans (ComplexReal.ofSigned_mul _ _) (ComplexReal.ofSigned_same key))

--| A QUATERNION BY ONE OVER ITSELF IS ONE.
theorem mul_reciprocal (p : QuaternionReal) (k : Nat) (strict : (p.normSquared.owed.high k).lt (p.normSquared.held.low k)) :
    (p * p.reciprocal k strict).Same (ofNat 1) := by
  have key := SignedReal.mul_reciprocalHeld p.normSquared k strict
  unfold QuaternionReal.reciprocal
  generalize p.normSquared.reciprocalHeld k strict = r at key ⊢
  unfold QuaternionReal.normSquared at key
  obtain ⟨a, b⟩ := p
  constructor
  · show (a * (a.conjugate * ComplexReal.ofSigned r) + -((-(b * ComplexReal.ofSigned r)).conjugate * b)).Same
      (ComplexReal.ofNat 1)
    simp only [ComplexReal.conjugate_neg]
    refine ComplexReal.same_trans (ComplexReal.add_same (ComplexReal.same_refl _)
      (ComplexReal.neg_same (ComplexReal.neg_mul _ _))) ?_
    rw [ComplexReal.neg_neg]
    refine ComplexReal.same_trans (ComplexReal.add_same (ComplexReal.same_symm (ComplexReal.mul_assoc _ _ _))
      (ComplexReal.mul_same (ComplexReal.conjugate_mul b (ComplexReal.ofSigned r)) (ComplexReal.same_refl b))) ?_
    rw [ComplexReal.conjugate_ofSigned]
    refine ComplexReal.same_trans (ComplexReal.add_same (ComplexReal.same_refl _) (ComplexReal.swap_last _ _ _)) ?_
    refine ComplexReal.same_trans (ComplexReal.same_symm (ComplexReal.add_mul _ _ _)) ?_
    exact ComplexReal.same_trans
      (ComplexReal.mul_same (ComplexReal.add_same (ComplexReal.mul_conjugate a) (ComplexReal.conjugate_mul_self b))
        (ComplexReal.same_refl _))
      (the_norms_by_one_over _ _ _ key)
  · show ((-(b * ComplexReal.ofSigned r)) * a + b * (a.conjugate * ComplexReal.ofSigned r).conjugate).Same
      (ComplexReal.ofNat 0)
    have conj : (a.conjugate * ComplexReal.ofSigned r).conjugate.Same (a * ComplexReal.ofSigned r) :=
      ComplexReal.conjugate_conjugate_mul a (ComplexReal.ofSigned r)
    have swap : ((b * ComplexReal.ofSigned r) * a).Same (b * (a * ComplexReal.ofSigned r)) :=
      ComplexReal.same_trans (ComplexReal.mul_assoc _ _ _) (ComplexReal.mul_same (ComplexReal.same_refl b) (ComplexReal.mul_comm _ _))
    exact ComplexReal.same_trans
      (ComplexReal.add_same (ComplexReal.same_trans (ComplexReal.neg_mul _ _) (ComplexReal.neg_same swap))
        (ComplexReal.mul_same (ComplexReal.same_refl b) conj))
      (ComplexReal.same_trans (ComplexReal.add_comm _ _) (ComplexReal.add_neg _))

--| ONE OVER A QUATERNION BY THE QUATERNION IS ONE: one over works from the other side too.
theorem reciprocal_mul (p : QuaternionReal) (k : Nat) (strict : (p.normSquared.owed.high k).lt (p.normSquared.held.low k)) :
    (p.reciprocal k strict * p).Same (ofNat 1) := by
  have key := SignedReal.mul_reciprocalHeld p.normSquared k strict
  unfold QuaternionReal.reciprocal
  generalize p.normSquared.reciprocalHeld k strict = r at key ⊢
  unfold QuaternionReal.normSquared at key
  obtain ⟨a, b⟩ := p
  constructor
  · show (a.conjugate * ComplexReal.ofSigned r * a + -(b.conjugate * -(b * ComplexReal.ofSigned r))).Same
      (ComplexReal.ofNat 1)
    rw [ComplexReal.mul_neg, ComplexReal.neg_neg]
    refine ComplexReal.same_trans (ComplexReal.add_same (ComplexReal.swap_last _ _ _)
      (ComplexReal.same_symm (ComplexReal.mul_assoc _ _ _))) ?_
    refine ComplexReal.same_trans (ComplexReal.same_symm (ComplexReal.add_mul _ _ _)) ?_
    exact ComplexReal.same_trans
      (ComplexReal.mul_same (ComplexReal.add_same (ComplexReal.conjugate_mul_self a) (ComplexReal.conjugate_mul_self b))
        (ComplexReal.same_refl _))
      (the_norms_by_one_over _ _ _ key)
  · show (b * (a.conjugate * ComplexReal.ofSigned r) + (-(b * ComplexReal.ofSigned r)) * a.conjugate).Same
      (ComplexReal.ofNat 0)
    have swap : ((b * ComplexReal.ofSigned r) * a.conjugate).Same (b * (a.conjugate * ComplexReal.ofSigned r)) :=
      ComplexReal.same_trans (ComplexReal.mul_assoc _ _ _) (ComplexReal.mul_same (ComplexReal.same_refl b) (ComplexReal.mul_comm _ _))
    exact ComplexReal.same_trans
      (ComplexReal.add_same (ComplexReal.same_refl _) (ComplexReal.same_trans (ComplexReal.neg_mul _ _) (ComplexReal.neg_same swap)))
      (ComplexReal.add_neg _)

--| THE TURN OWED THROUGH A PRODUCT: a quaternion by one owed is the product owed.
theorem mul_neg (p q : QuaternionReal) : (p * -q).Same (-(p * q)) := by
  obtain ⟨a, b⟩ := p
  obtain ⟨c, d⟩ := q
  constructor
  · show (a * -c + -((-d).conjugate * b)).Same (-(a * c) + -(-(d.conjugate * b)))
    simp only [ComplexReal.mul_neg, ComplexReal.conjugate_neg]
    exact ComplexReal.add_same (ComplexReal.same_refl _) (ComplexReal.neg_same (ComplexReal.neg_mul _ _))
  · show ((-d) * a + b * (-c).conjugate).Same (-(d * a) + -(b * c.conjugate))
    simp only [ComplexReal.conjugate_neg, ComplexReal.mul_neg]
    exact ComplexReal.add_same (ComplexReal.neg_mul _ _) (ComplexReal.same_refl _)

--| THE CONJUGATE OF A QUATERNION: the first turned across the line, the second owed.
def conjugate (p : QuaternionReal) : QuaternionReal := ⟨p.first.conjugate, -p.second⟩

--| THE CONJUGATE OF A PRODUCT IS THE PRODUCT OF THE CONJUGATES, THE OTHER WAY ROUND.
theorem conjugate_mul (p q : QuaternionReal) : (p * q).conjugate.Same (q.conjugate * p.conjugate) := by
  obtain ⟨a, b⟩ := p
  obtain ⟨c, d⟩ := q
  constructor
  · show (a * c + -(d.conjugate * b)).conjugate.Same (c.conjugate * a.conjugate + -((-b).conjugate * (-d)))
    rw [ComplexReal.conjugate_add, ComplexReal.conjugate_neg, ComplexReal.conjugate_neg]
    exact ComplexReal.same_trans
      (ComplexReal.add_same (ComplexReal.conjugate_mul a c) (ComplexReal.neg_same (ComplexReal.conjugate_conjugate_mul d b)))
      (ComplexReal.same_trans
        (ComplexReal.add_same (ComplexReal.mul_comm _ _) (ComplexReal.neg_same (ComplexReal.mul_comm _ _)))
        (ComplexReal.add_same (ComplexReal.same_refl _)
          (ComplexReal.neg_same (ComplexReal.same_symm (ComplexReal.neg_mul_neg _ _)))))
  · show (-(d * a + b * c.conjugate)).Same ((-b) * c.conjugate + (-d) * a.conjugate.conjugate)
    rw [ComplexReal.neg_add, ComplexReal.conjugate_conjugate]
    exact ComplexReal.same_trans (ComplexReal.add_comm _ _)
      (ComplexReal.add_same (ComplexReal.same_symm (ComplexReal.neg_mul _ _)) (ComplexReal.same_symm (ComplexReal.neg_mul _ _)))

--| ONE OVER IS ONE THING: whatever the quaternion put before it makes one is its one over.
theorem reciprocal_unique (p : QuaternionReal) (k : Nat) (strict : (p.normSquared.owed.high k).lt (p.normSquared.held.low k))
    {v : QuaternionReal} (hv : (p * v).Same (ofNat 1)) : v.Same (p.reciprocal k strict) :=
  same_trans (same_symm (one_mul v))
    (same_trans (mul_same (same_symm (p.reciprocal_mul k strict)) (same_refl v))
      (same_trans (mul_assoc _ _ _)
        (same_trans (mul_same (same_refl _) hv) (mul_one _))))

end QuaternionReal

end Meanings
