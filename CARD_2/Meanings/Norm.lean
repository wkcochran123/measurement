/-
A bound on a weighed square.

A norm on two coins is a weighed square: so much of the first coin squared and so much of the second.  An operator on two
coins takes the pair to two sums.  Its norm, squared, is the least number that the weighed square of what comes out never
passes, against the weighed square of what went in.  Without the reals that least number is not written; it is walled.  An
upper wall is a number the square never passes, for every pair.  A lower wall is a pair that passes a number.

The upper wall is a statement about every pair, and it comes down to one form never being negative.  A form of two
unknowns is never negative when its first coefficient is more than nothing and the cross coefficient squared is not more
than the product of the other two.  That is the whole of it, in whole numbers.
-/

namespace Meanings

--| A square is never negative.
theorem a_square_is_never_negative (x : Int) : 0 ≤ x * x := by
  rcases Int.le_total 0 x with h | h
  · exact Int.mul_nonneg h h
  · have := Int.mul_nonneg (Int.neg_nonneg_of_nonpos h) (Int.neg_nonneg_of_nonpos h)
    rwa [Int.neg_mul_neg] at this

--| THE FORM.  First coefficient more than nothing, cross coefficient squared not more than the other two: never negative.
--| The first coefficient times the form is a square and a square by what is left over.
theorem the_form_is_never_negative (a b c x y : Int) (pos : 0 < a) (det : b * b ≤ a * c) :
    0 ≤ a * (x * x) + b * (x * y) + b * (x * y) + c * (y * y) := by
  have sq := a_square_is_never_negative (a * x + b * y)
  have rest : 0 ≤ (a * c - b * b) * (y * y) := Int.mul_nonneg (by omega) (a_square_is_never_negative y)
  have key : a * (a * (x * x) + b * (x * y) + b * (x * y) + c * (y * y))
      = (a * x + b * y) * (a * x + b * y) + (a * c - b * b) * (y * y) := by
    simp only [Int.mul_add, Int.add_mul, Int.sub_mul]; ac_nf; omega
  exact Int.nonneg_of_mul_nonneg_right (by rw [key]; omega) pos

--| The weighed square of what an operator gives, written out as a form in what went in.
theorem the_weighed_square_of_a_turn (w₁ w₂ p q r s x y : Int) :
    w₁ * ((p * x + q * y) * (p * x + q * y)) + w₂ * ((r * x + s * y) * (r * x + s * y))
      = (w₁ * (p * p) + w₂ * (r * r)) * (x * x) + (w₁ * (p * q) + w₂ * (r * s)) * (x * y)
          + (w₁ * (p * q) + w₂ * (r * s)) * (x * y) + (w₁ * (q * q) + w₂ * (s * s)) * (y * y) := by
  simp only [Int.mul_add, Int.add_mul]; ac_nf

--| THE UPPER WALL.  If the bound by the weights, less what comes out, is a form that is never negative, then for every pair
--| the weighed square of what comes out is never past the bound by the weighed square of what went in.
theorem a_bound_on_the_weighed_square (w₁ w₂ p q r s bound x y : Int)
    (pos : 0 < bound * w₁ - (w₁ * (p * p) + w₂ * (r * r)))
    (det : (w₁ * (p * q) + w₂ * (r * s)) * (w₁ * (p * q) + w₂ * (r * s))
        ≤ (bound * w₁ - (w₁ * (p * p) + w₂ * (r * r))) * (bound * w₂ - (w₁ * (q * q) + w₂ * (s * s)))) :
    w₁ * ((p * x + q * y) * (p * x + q * y)) + w₂ * ((r * x + s * y) * (r * x + s * y))
      ≤ bound * (w₁ * (x * x) + w₂ * (y * y)) := by
  have h := the_form_is_never_negative _ (-(w₁ * (p * q) + w₂ * (r * s))) _ x y pos
    (by rw [Int.neg_mul_neg]; exact det)
  rw [the_weighed_square_of_a_turn]
  have e : bound * (w₁ * (x * x) + w₂ * (y * y)) = (bound * w₁) * (x * x) + (bound * w₂) * (y * y) := by
    rw [Int.mul_add, Int.mul_assoc, Int.mul_assoc]
  rw [e]
  simp only [Int.sub_mul, Int.neg_mul] at h
  omega

end Meanings
