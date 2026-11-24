/-
The diagonal, with no choice.

Hand in any list of reals.  Start from nothing and one.  At the n-th step, cut the interval in thirds and read the n-th
real at a stage where its bracket is narrower than a third.  Its low wall is past the top of the first third, or it is
not; if it is, keep the first third, and the n-th real lies wholly above; if not, its high wall is under the bottom of the
last third, so keep the last third, and the n-th real lies wholly below.  Each step is a comparison of two fractions,
which clicks, and nothing is chosen.  The intervals nest and narrow, so they make a real, and at the n-th step it parts
from the n-th real.  So it is none of them.

Which way it parts is turned over from the listed real: above where the listed is below, below where it is above.  On
the two truths that is a crossing, never a level arm: the diagonal and each listed real compare as true on false or as
false on true, never as true on true.
-/
import Meanings.Gap
import Meanings.Difference

namespace Meanings
namespace Diagonal

theorem three_pow_pos (n : Nat) : 0 < 3 ^ n := Nat.pow_pos (by decide)

--| c over three to the n.
def third (c n : Nat) : Fraction := ⟨c, 3 ^ n, three_pow_pos n⟩

--| The cut after n steps: nothing at first, then the first third or the last.
def cutOf (f : Nat → Bracketed) : Nat → Nat
  | 0 => 0
  | n + 1 => if (third (3 * cutOf f n + 1) (n + 1)).lt ((f n).low (3 ^ (n + 1)))
      then 3 * cutOf f n else 3 * cutOf f n + 2

theorem cutOf_step (f : Nat → Bracketed) (n : Nat) :
    3 * cutOf f n ≤ cutOf f (n + 1) ∧ cutOf f (n + 1) ≤ 3 * cutOf f n + 2 := by
  by_cases h : (third (3 * cutOf f n + 1) (n + 1)).lt ((f n).low (3 ^ (n + 1)))
  · have e : cutOf f (n + 1) = 3 * cutOf f n := by show (if _ then _ else _) = _; rw [if_pos h]
    rw [e]; exact ⟨Nat.le_refl _, by omega⟩
  · have e : cutOf f (n + 1) = 3 * cutOf f n + 2 := by show (if _ then _ else _) = _; rw [if_neg h]
    rw [e]; exact ⟨by omega, Nat.le_refl _⟩

theorem succ_le_three_pow : ∀ n, n + 1 ≤ 3 ^ n
  | 0 => Nat.le_refl 1
  | n + 1 => by rw [Nat.pow_succ]; have := succ_le_three_pow n; omega

--| THE DIAGONAL.  A real, with no choice: between the cut and one more, over three to the n.
def theDiagonal (f : Nat → Bracketed) : Bracketed where
  low n := third (cutOf f n) n
  high n := third (cutOf f n + 1) n
  ordered n := Nat.mul_le_mul_right _ (Nat.le_succ _)
  low_rises n := by
    show cutOf f n * 3 ^ (n + 1) ≤ cutOf f (n + 1) * 3 ^ n
    rw [Nat.pow_succ, Nat.mul_comm (3 ^ n) 3, ← Nat.mul_assoc, Nat.mul_comm (cutOf f n) 3]
    exact Nat.mul_le_mul_right _ (cutOf_step f n).1
  high_falls n := by
    show (cutOf f (n + 1) + 1) * 3 ^ n ≤ (cutOf f n + 1) * 3 ^ (n + 1)
    rw [Nat.pow_succ, Nat.mul_comm (3 ^ n) 3, ← Nat.mul_assoc]
    exact Nat.mul_le_mul_right _ (by have := (cutOf_step f n).2; omega)
  narrows n := by
    show (cutOf f n + 1) * 3 ^ n * (n + 1) ≤ cutOf f n * 3 ^ n * (n + 1) + 3 ^ n * 3 ^ n
    rw [Nat.add_mul, Nat.add_mul, Nat.one_mul]
    exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (succ_le_three_pow n)) _

--| THE CROSSING.  At the n-th step the n-th real lies wholly above the diagonal or wholly below it.
theorem the_diagonal_crosses (f : Nat → Bracketed) (n : Nat) :
    ((theDiagonal f).high (n + 1)).lt ((f n).low (3 ^ (n + 1)))
      ∨ ((f n).high (3 ^ (n + 1))).lt ((theDiagonal f).low (n + 1)) := by
  by_cases above : (third (3 * cutOf f n + 1) (n + 1)).lt ((f n).low (3 ^ (n + 1)))
  · left
    have e : cutOf f (n + 1) = 3 * cutOf f n := by show (if _ then _ else _) = _; rw [if_pos above]
    show (third (cutOf f (n + 1) + 1) (n + 1)).lt _
    rw [e]; exact above
  · right
    have e : cutOf f (n + 1) = 3 * cutOf f n + 2 := by show (if _ then _ else _) = _; rw [if_neg above]
    show Fraction.lt _ (third (cutOf f (n + 1)) (n + 1))
    rw [e]
    have nar := (f n).narrows (3 ^ (n + 1))
    have notlt : ((f n).low (3 ^ (n + 1))).over * 3 ^ (n + 1) ≤ (3 * cutOf f n + 1) * ((f n).low (3 ^ (n + 1))).under :=
      Nat.le_of_not_lt above
    have hu := ((f n).high (3 ^ (n + 1))).under_pos
    have lu := ((f n).low (3 ^ (n + 1))).under_pos
    show ((f n).high (3 ^ (n + 1))).over * 3 ^ (n + 1) < (3 * cutOf f n + 2) * ((f n).high (3 ^ (n + 1))).under
    generalize ((f n).high (3 ^ (n + 1))).over = ho at *
    generalize ((f n).high (3 ^ (n + 1))).under = hu' at *
    generalize ((f n).low (3 ^ (n + 1))).over = lo at *
    generalize ((f n).low (3 ^ (n + 1))).under = lu' at *
    generalize 3 ^ (n + 1) = T at *
    generalize cutOf f n = c at *
    have step : T * (hu' * lu') < (T + 1) * (hu' * lu') := by
      rw [Nat.succ_mul]; have := Nat.mul_pos hu lu; omega
    apply lt_of_mul_lt_mul_on_the_right (c := lu' * (T + 1))
    calc ho * T * (lu' * (T + 1)) = T * (ho * lu' * (T + 1)) := by ac_rfl
      _ ≤ T * (lo * hu' * (T + 1) + hu' * lu') := Nat.mul_le_mul_left _ nar
      _ = (lo * T) * (hu' * (T + 1)) + T * (hu' * lu') := by rw [Nat.mul_add]; congr 1; ac_rfl
      _ ≤ ((3 * c + 1) * lu') * (hu' * (T + 1)) + T * (hu' * lu') :=
          Nat.add_le_add_right (Nat.mul_le_mul_right _ notlt) _
      _ < ((3 * c + 1) * lu') * (hu' * (T + 1)) + (T + 1) * (hu' * lu') := Nat.add_lt_add_left step _
      _ = (3 * c + 1) * (hu' * lu' * (T + 1)) + hu' * lu' * (T + 1) := by congr 1 <;> ac_rfl
      _ = (3 * c + 2) * hu' * (lu' * (T + 1)) := by
          rw [← Nat.succ_mul, show Nat.succ (3 * c + 1) = 3 * c + 2 from rfl]; ac_rfl

--| PARTED AT A STAGE.
theorem the_diagonal_parts_from (f : Nat → Bracketed) (n : Nat) :
    ∃ a b, (theDiagonal f).PartedAt (f n) a b := by
  rcases the_diagonal_crosses f n with above | below
  · exact ⟨3 ^ (n + 1), n + 1, Or.inr (Nat.not_le_of_lt above)⟩
  · exact ⟨n + 1, 3 ^ (n + 1), Or.inl (Nat.not_le_of_lt below)⟩

--| THE DIAGONAL IS NONE OF THEM.  Whatever list is handed in, the diagonal is not one with any real on it.
theorem the_diagonal_is_none_of_them (f : Nat → Bracketed) (n : Nat) : ¬ (theDiagonal f).Same (f n) :=
  Bracketed.parted_is_not_same (the_diagonal_parts_from f n)

end Diagonal
end Meanings
