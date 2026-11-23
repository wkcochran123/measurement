/-
The reals, with no choice.

A real is not a thing held.  It is a process of completion: a bracket of two fractions at every stage, the low wall never
falling, the high wall never rising, the low never past the high, and the width at the n-th stage not more than one part in
n and one.  That is all.  Nothing here asks for a click it was not handed, so nothing here bills choice.  The walls are
fractions of naturals, compared by crossing, and every comparison is a comparison of whole numbers.

Three are built.  The root of ninety, by halving: double the cut at each stage and keep the one more when its square is not
past ninety by the stage.  Eighteen and that root, the norm of the device's table.  And e, the base the derivative leaves
alone, from the factorial series: what the series has reached from below, and that and one part in m by m factorial above.

What is not here is the limit as a thing.  Mathlib's reals hold the limit, and bill choice to do it.  Here the real is the
bracket, at every stage, and the limit is only ever the process.
-/

namespace Meanings

--| A fraction of naturals, the under more than nothing.
structure Fraction where
  over : Nat
  under : Nat
  under_pos : 0 < under

--| Not past, by crossing.
def Fraction.le (p q : Fraction) : Prop := p.over * q.under ≤ q.over * p.under

--| THE REAL, AS A BRACKET AT EVERY STAGE.
structure Bracketed where
  low : Nat → Fraction
  high : Nat → Fraction
  ordered : ∀ n, (low n).le (high n)
  low_rises : ∀ n, (low n).le (low (n + 1))
  high_falls : ∀ n, (high (n + 1)).le (high n)
  narrows : ∀ n, (high n).over * (low n).under * (n + 1) ≤ (low n).over * (high n).under * (n + 1) + (high n).under * (low n).under

--| Two reals are one when no wall of the one is ever past a wall of the other.
def Bracketed.Same (x y : Bracketed) : Prop := ∀ n m, (x.low n).le (y.high m) ∧ (y.low n).le (x.high m)

--| A CUT AT EVERY HALVING.  The cut doubles, or doubles and one more, from one stage to the next.
structure DyadicCut where
  cut : Nat → Nat
  doubles : ∀ n, 2 * cut n ≤ cut (n + 1) ∧ cut (n + 1) ≤ 2 * cut n + 1

def DyadicCut.bracketed (d : DyadicCut) : Bracketed where
  low n := ⟨d.cut n, 2 ^ n, Nat.two_pow_pos n⟩
  high n := ⟨d.cut n + 1, 2 ^ n, Nat.two_pow_pos n⟩
  ordered n := Nat.mul_le_mul_right _ (Nat.le_succ _)
  low_rises n := by
    show d.cut n * 2 ^ (n + 1) ≤ d.cut (n + 1) * 2 ^ n
    rw [Nat.pow_succ, show d.cut n * (2 ^ n * 2) = (2 * d.cut n) * 2 ^ n by
      rw [Nat.mul_comm (2 ^ n) 2, ← Nat.mul_assoc, Nat.mul_comm (d.cut n) 2]]
    exact Nat.mul_le_mul_right _ (d.doubles n).1
  high_falls n := by
    show (d.cut (n + 1) + 1) * 2 ^ n ≤ (d.cut n + 1) * 2 ^ (n + 1)
    rw [Nat.pow_succ, show (d.cut n + 1) * (2 ^ n * 2) = (2 * d.cut n + 2) * 2 ^ n by
      rw [Nat.mul_comm (2 ^ n) 2, ← Nat.mul_assoc, Nat.mul_comm (d.cut n + 1) 2, Nat.mul_add]]
    exact Nat.mul_le_mul_right _ (by have := (d.doubles n).2; omega)
  narrows n := by
    show (d.cut n + 1) * 2 ^ n * (n + 1) ≤ d.cut n * 2 ^ n * (n + 1) + 2 ^ n * 2 ^ n
    rw [Nat.succ_mul, Nat.add_mul]
    exact Nat.add_le_add_left (Nat.mul_le_mul_left _ Nat.lt_two_pow_self) _

--| BY HALVING.  The root of N: double the cut, and keep the one more when its square is not past N by the stage.
def rootByHalving (N : Nat) (start : Nat) : Nat → Nat
  | 0 => start
  | n + 1 =>
    let cut := rootByHalving N start n
    if (2 * cut + 1) * (2 * cut + 1) ≤ N * 4 ^ (n + 1) then 2 * cut + 1 else 2 * cut

theorem rootByHalving_doubles (N start n : Nat) :
    2 * rootByHalving N start n ≤ rootByHalving N start (n + 1) ∧ rootByHalving N start (n + 1) ≤ 2 * rootByHalving N start n + 1 := by
  simp only [rootByHalving]
  split <;> exact ⟨by omega, by omega⟩

--| Every stage holds the root: the cut squared is not past N by the stage, and N by the stage is under the next square.
theorem rootByHalving_holds (N start : Nat) (s1 : start * start ≤ N) (s2 : N < (start + 1) * (start + 1)) (n : Nat) :
    rootByHalving N start n * rootByHalving N start n ≤ N * 4 ^ n
      ∧ N * 4 ^ n < (rootByHalving N start n + 1) * (rootByHalving N start n + 1) := by
  induction n with
  | zero => simpa [rootByHalving] using ⟨s1, s2⟩
  | succ n ih =>
    obtain ⟨i1, i2⟩ := ih
    have p : N * 4 ^ (n + 1) = 4 * (N * 4 ^ n) := by
      rw [Nat.pow_succ, Nat.mul_comm (4 ^ n) 4, ← Nat.mul_assoc, Nat.mul_comm N 4, Nat.mul_assoc]
    have sq : ∀ a : Nat, (2 * a) * (2 * a) = 4 * (a * a) := fun a => by rw [Nat.mul_mul_mul_comm]
    have sq1 : ∀ a : Nat, (2 * a + 2) * (2 * a + 2) = 4 * ((a + 1) * (a + 1)) := fun a => by
      rw [show 2 * a + 2 = 2 * (a + 1) by omega, Nat.mul_mul_mul_comm]
    simp only [rootByHalving]
    split
    · rename_i h
      refine ⟨h, ?_⟩
      rw [show 2 * rootByHalving N start n + 1 + 1 = 2 * rootByHalving N start n + 2 by omega, sq1, p]; omega
    · rename_i h
      refine ⟨?_, ?_⟩
      · rw [sq, p]; omega
      · exact Nat.lt_of_not_le h

--| THE ROOT OF NINETY.
def theRootOfNinety : DyadicCut where
  cut := rootByHalving 90 9
  doubles := rootByHalving_doubles 90 9

theorem theRootOfNinety_holds_the_root (n : Nat) :
    theRootOfNinety.cut n * theRootOfNinety.cut n ≤ 90 * 4 ^ n
      ∧ 90 * 4 ^ n < (theRootOfNinety.cut n + 1) * (theRootOfNinety.cut n + 1) :=
  rootByHalving_holds 90 9 (by decide) (by decide) n

--| EIGHTEEN AND THE ROOT OF NINETY.  The norm of the device's table, a real with no choice.
def theNorm : DyadicCut where
  cut n := 18 * 2 ^ n + theRootOfNinety.cut n
  doubles n := by
    obtain ⟨d1, d2⟩ := theRootOfNinety.doubles n
    show 2 * (18 * 2 ^ n + theRootOfNinety.cut n) ≤ 18 * 2 ^ (n + 1) + theRootOfNinety.cut (n + 1)
      ∧ 18 * 2 ^ (n + 1) + theRootOfNinety.cut (n + 1) ≤ 2 * (18 * 2 ^ n + theRootOfNinety.cut n) + 1
    rw [Nat.pow_succ]; exact ⟨by omega, by omega⟩

--| THE FACTORIAL SERIES.  m factorial, and what the series to m has reached, by m factorial.
def factorial : Nat → Nat
  | 0 => 1
  | m + 1 => (m + 1) * factorial m

def seriesByFactorial : Nat → Nat
  | 0 => 1
  | m + 1 => (m + 1) * seriesByFactorial m + 1

theorem factorial_pos : ∀ m, 0 < factorial m
  | 0 => by decide
  | m + 1 => Nat.mul_pos (Nat.succ_pos m) (factorial_pos m)

theorem the_low_wall_rises (m a f : Nat) : a * ((m + 1) * f) ≤ ((m + 1) * a + 1) * f := by
  simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul]; ac_nf; omega

theorem the_high_wall_falls (m a f : Nat) :
    ((m + 1) * ((m + 1) * a + 1) + 1) * (m * f) ≤ (m * a + 1) * ((m + 1) * ((m + 1) * f)) := by
  simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul]; ac_nf; omega

theorem the_walls_are_ordered (m a f : Nat) : a * (m * f) ≤ (m * a + 1) * f := by
  simp only [Nat.add_mul, Nat.one_mul]; ac_nf; omega

theorem the_walls_narrow (m a f : Nat) (pos : 0 < f) : (m * a + 1) * f * m ≤ a * (m * f) * m + (m * f) * f := by
  have h := Nat.le_mul_of_pos_right (m * f) pos
  simp only [Nat.add_mul, Nat.one_mul] at *; ac_nf at *; omega

--| e.  Below: the series to m, over m factorial.  Above: that and one part in m by m factorial.  At the n-th stage, m is n and one.
def theBaseTheDerivativeLeavesAlone : Bracketed where
  low n := ⟨seriesByFactorial (n + 1), factorial (n + 1), factorial_pos _⟩
  high n := ⟨(n + 1) * seriesByFactorial (n + 1) + 1, (n + 1) * factorial (n + 1), Nat.mul_pos (Nat.succ_pos n) (factorial_pos _)⟩
  ordered n := the_walls_are_ordered (n + 1) _ _
  low_rises n := the_low_wall_rises (n + 1) (seriesByFactorial (n + 1)) (factorial (n + 1))
  high_falls n := the_high_wall_falls (n + 1) (seriesByFactorial (n + 1)) (factorial (n + 1))
  narrows n := the_walls_narrow (n + 1) _ _ (factorial_pos _)

end Meanings
