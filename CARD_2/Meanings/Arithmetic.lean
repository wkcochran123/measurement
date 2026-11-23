/-
Arithmetic on the reals, with no choice.

A sum of two reals is a bracket of sums: the low walls added and the high walls added.  The widths add too, so the sum at a
stage is taken from each real twice as far on, where each is half as wide.  A product of two reals is a bracket of
products.  Its width is each width by the other's walls, so it is taken from each real as far on as the walls are high:
the first high wall of each bounds every wall after it, and no wall is ever looked for that was not dealt.
-/
import Meanings.Real

namespace Meanings

--| NOT PAST IS TRANSITIVE.  Cross twice and cancel the middle under.
theorem Fraction.le_trans {p q r : Fraction} (h1 : p.le q) (h2 : q.le r) : p.le r := by
  unfold Fraction.le at *
  have m1 := Nat.mul_le_mul_right r.under h1
  have m2 := Nat.mul_le_mul_right p.under h2
  apply Nat.le_of_mul_le_mul_right _ q.under_pos
  calc p.over * r.under * q.under = p.over * q.under * r.under := by ac_nf
    _ ≤ q.over * p.under * r.under := m1
    _ = q.over * r.under * p.under := by ac_nf
    _ ≤ r.over * q.under * p.under := m2
    _ = r.over * p.under * q.under := by ac_nf

theorem Fraction.le_refl (p : Fraction) : p.le p := Nat.le_refl _

--| The low wall never falls, however many stages on; the high never rises.
theorem Bracketed.low_rises_by (x : Bracketed) (n : Nat) : ∀ k, (x.low n).le (x.low (n + k))
  | 0 => Fraction.le_refl _
  | k + 1 => Fraction.le_trans (x.low_rises_by n k) (x.low_rises (n + k))

theorem Bracketed.high_falls_by (x : Bracketed) (n : Nat) : ∀ k, (x.high (n + k)).le (x.high n)
  | 0 => Fraction.le_refl _
  | k + 1 => Fraction.le_trans (x.high_falls (n + k)) (x.high_falls_by n k)

--| BESIDE.  Over by under and over by under, under by under.
def Fraction.add (p q : Fraction) : Fraction :=
  ⟨p.over * q.under + q.over * p.under, p.under * q.under, Nat.mul_pos p.under_pos q.under_pos⟩

theorem Fraction.add_le_add {p p' q q' : Fraction} (hp : p.le p') (hq : q.le q') : (p.add q).le (p'.add q') := by
  unfold Fraction.le Fraction.add at *
  have m1 := Nat.mul_le_mul_right (q.under * q'.under) hp
  have m2 := Nat.mul_le_mul_right (p.under * p'.under) hq
  simp only [Nat.add_mul] at *
  ac_nf at *
  omega

--| The widths of two brackets, each one part in twice as many, add to one part in as many.
theorem the_widths_add (a b a' b' c d c' d' N : Nat)
    (h1 : a' * b * (N + N) ≤ a * b' * (N + N) + b' * b)
    (h2 : c' * d * (N + N) ≤ c * d' * (N + N) + d' * d) :
    (a' * d' + c' * b') * (b * d) * N ≤ (a * d + c * b) * (b' * d') * N + (b' * d') * (b * d) := by
  have m1 := Nat.mul_le_mul_right (d * d') h1
  have m2 := Nat.mul_le_mul_right (b * b') h2
  simp only [Nat.add_mul, Nat.mul_add] at *
  ac_nf at *
  omega

--| THE SUM OF TWO REALS.  At the n-th stage, each real's stage two n and one.
def Bracketed.add (x y : Bracketed) : Bracketed where
  low n := (x.low (2 * n + 1)).add (y.low (2 * n + 1))
  high n := (x.high (2 * n + 1)).add (y.high (2 * n + 1))
  ordered n := Fraction.add_le_add (x.ordered _) (y.ordered _)
  low_rises n := by
    show ((x.low (2 * n + 1)).add (y.low (2 * n + 1))).le ((x.low (2 * (n + 1) + 1)).add (y.low (2 * (n + 1) + 1)))
    rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 2 by omega]
    exact Fraction.add_le_add (x.low_rises_by _ 2) (y.low_rises_by _ 2)
  high_falls n := by
    show ((x.high (2 * (n + 1) + 1)).add (y.high (2 * (n + 1) + 1))).le ((x.high (2 * n + 1)).add (y.high (2 * n + 1)))
    rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 2 by omega]
    exact Fraction.add_le_add (x.high_falls_by _ 2) (y.high_falls_by _ 2)
  narrows n := by
    have hx := x.narrows (2 * n + 1)
    have hy := y.narrows (2 * n + 1)
    rw [show 2 * n + 1 + 1 = (n + 1) + (n + 1) by omega] at hx hy
    exact the_widths_add _ _ _ _ _ _ _ _ (n + 1) hx hy

--| The widths of two brackets, each one part in as many as the walls are high, multiply to one part in as many.
theorem the_widths_multiply (a b a' b' c d c' d' B N K : Nat)
    (h1 : a' * b * K ≤ a * b' * K + b' * b)
    (h2 : c' * d * K ≤ c * d' * K + d' * d)
    (ba : a ≤ B * b) (bc : c ≤ B * d)
    (hK : K = (B + B + 1) * N) (hN : 0 < N) :
    a' * c' * (b * d) * N ≤ a * c * (b' * d') * N + (b' * d') * (b * d) := by
  have hKpos : 0 < K := by rw [hK]; exact Nat.mul_pos (by omega) hN
  have p := Nat.mul_le_mul h1 h2
  have s1 := Nat.mul_le_mul_right (b' * d' * d * K) ba
  have s2 := Nat.mul_le_mul_right (d' * b' * b * K) bc
  have q : a' * c' * (b * d) * (K * K) ≤ a * c * (b' * d') * (K * K) + (B + B) * K * (b' * d' * (b * d)) + b' * d' * (b * d) := by
    simp only [Nat.add_mul, Nat.mul_add] at p s1 s2 ⊢
    ac_nf at p s1 s2 ⊢
    have hQ : b' * d' * (b * d) = b * (b' * (d * d')) := by ac_nf
    omega
  have kk : K * K = (B + B + 1) * N * K := by rw [← hK]
  have nk := Nat.le_mul_of_pos_right N hKpos
  have t : (B + B) * K * N + N ≤ K * K := by
    rw [kk]; simp only [Nat.add_mul, Nat.one_mul] at nk ⊢; ac_nf at nk ⊢; omega
  have tq := Nat.mul_le_mul_right (b' * d' * (b * d)) t
  have qn := Nat.mul_le_mul_right N q
  apply Nat.le_of_mul_le_mul_right _ (Nat.mul_pos hKpos hKpos)
  simp only [Nat.add_mul] at tq qn ⊢
  ac_nf at tq qn ⊢
  omega

--| EACH FOR EACH.  Over by over, under by under.
def Fraction.mul (p q : Fraction) : Fraction :=
  ⟨p.over * q.over, p.under * q.under, Nat.mul_pos p.under_pos q.under_pos⟩

theorem Fraction.mul_le_mul {p p' q q' : Fraction} (hp : p.le p') (hq : q.le q') : (p.mul q).le (p'.mul q') := by
  unfold Fraction.le Fraction.mul at *
  have m := Nat.mul_le_mul hp hq
  calc p.over * q.over * (p'.under * q'.under) = p.over * p'.under * (q.over * q'.under) := by ac_nf
    _ ≤ p'.over * p.under * (q'.over * q.under) := m
    _ = p'.over * q'.over * (p.under * q.under) := by ac_nf

--| The first high wall bounds every low wall after it.
theorem Bracketed.low_is_under_the_first_high (x : Bracketed) (j : Nat) :
    (x.low j).over ≤ (x.high 0).over * (x.low j).under := by
  have h : (x.low j).le (x.high 0) :=
    Fraction.le_trans (x.ordered j) (by have := x.high_falls_by 0 j; rwa [Nat.zero_add] at this)
  have top : (x.high 0).le ⟨(x.high 0).over, 1, Nat.one_pos⟩ := by
    show (x.high 0).over * 1 ≤ (x.high 0).over * (x.high 0).under
    exact Nat.mul_le_mul_left _ (x.high 0).under_pos
  have := Fraction.le_trans h top
  unfold Fraction.le at this
  simpa using this

--| THE PRODUCT OF TWO REALS.  At the n-th stage, each real as far on as the walls are high.
def Bracketed.bound (x y : Bracketed) : Nat := (x.high 0).over + (y.high 0).over
def Bracketed.stageForProduct (x y : Bracketed) (n : Nat) : Nat :=
  (x.bound y + x.bound y + 1) * n + (x.bound y + x.bound y)

theorem Bracketed.stageForProduct_succ (x y : Bracketed) (n : Nat) :
    x.stageForProduct y (n + 1) = x.stageForProduct y n + (x.bound y + x.bound y + 1) := by
  unfold Bracketed.stageForProduct; rw [Nat.mul_succ]; omega

theorem Bracketed.stageForProduct_one_more (x y : Bracketed) (n : Nat) :
    x.stageForProduct y n + 1 = (x.bound y + x.bound y + 1) * (n + 1) := by
  unfold Bracketed.stageForProduct; rw [Nat.mul_succ]; omega

def Bracketed.mul (x y : Bracketed) : Bracketed where
  low n := (x.low (x.stageForProduct y n)).mul (y.low (x.stageForProduct y n))
  high n := (x.high (x.stageForProduct y n)).mul (y.high (x.stageForProduct y n))
  ordered n := Fraction.mul_le_mul (x.ordered _) (y.ordered _)
  low_rises n := by
    show ((x.low (x.stageForProduct y n)).mul (y.low (x.stageForProduct y n))).le
      ((x.low (x.stageForProduct y (n + 1))).mul (y.low (x.stageForProduct y (n + 1))))
    rw [Bracketed.stageForProduct_succ]
    exact Fraction.mul_le_mul (x.low_rises_by _ _) (y.low_rises_by _ _)
  high_falls n := by
    show ((x.high (x.stageForProduct y (n + 1))).mul (y.high (x.stageForProduct y (n + 1)))).le
      ((x.high (x.stageForProduct y n)).mul (y.high (x.stageForProduct y n)))
    rw [Bracketed.stageForProduct_succ]
    exact Fraction.mul_le_mul (x.high_falls_by _ _) (y.high_falls_by _ _)
  narrows n := by
    have hx := x.narrows (x.stageForProduct y n)
    have hy := y.narrows (x.stageForProduct y n)
    rw [Bracketed.stageForProduct_one_more] at hx hy
    have bx := x.low_is_under_the_first_high (x.stageForProduct y n)
    have by' := y.low_is_under_the_first_high (x.stageForProduct y n)
    exact the_widths_multiply _ _ _ _ _ _ _ _ (x.bound y) (n + 1) _ hx hy
      (Nat.le_trans bx (Nat.mul_le_mul_right _ (Nat.le_add_right _ _)))
      (Nat.le_trans by' (Nat.mul_le_mul_right _ (Nat.le_add_left _ _))) rfl (Nat.succ_pos n)

end Meanings
