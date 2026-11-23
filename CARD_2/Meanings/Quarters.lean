/-
The four quarters of the exponential, with no choice.

The powers of the quarter turn come round in four: one, the quarter turn, one owed, the quarter turn owed.  So the one
series of θ to the k over k factorial, taken with the quarter turn, falls into four series by k counted in fours: the
quarters S₀, S₁, S₂ and S₃.  Each has terms never under nothing, and each term is not past half the one four places
before it, so twice the next term bounds what is left, and each quarter is a real with no choice, for θ = p over q not
past one.

Cosine is the first quarter less the third, sine the second less the fourth; all four beside each other are the base the
derivative leaves alone, raised to θ; and at θ nothing they are one and three nothings.  What is checked here of those is
what the circle check checks: at the third stage, at θ one and θ a half, the brackets of the two sides hold each other.
That is a reading at a stage, decided by the kernel, not the sameness at every stage.
-/
import Meanings.Trigonometry

namespace Meanings

--| Twice a term four places on is not past the term: p to the fourth is not past q to the fourth, and the four places'
--| factors are at least twenty-four.
theorem twice_four_places_on (p q k : Nat) (hp : p ≤ q) :
    2 * (p ^ (k + 4) * (q ^ k * factorial k)) ≤ p ^ k * (q ^ (k + 4) * factorial (k + 4)) := by
  have f : factorial (k + 4) = (k + 4) * ((k + 3) * ((k + 2) * ((k + 1) * factorial k))) := rfl
  have e1 : p ^ (k + 4) = p ^ k * p ^ 4 := Nat.pow_add p k 4
  have e2 : q ^ (k + 4) = q ^ k * q ^ 4 := Nat.pow_add q k 4
  have h4 : p ^ 4 ≤ q ^ 4 := Nat.pow_le_pow_left hp 4
  have big : 2 ≤ (k + 4) * ((k + 3) * ((k + 2) * (k + 1))) :=
    Nat.le_trans (by decide : 2 ≤ 4 * (3 * (2 * 1)))
      (Nat.mul_le_mul (by omega) (Nat.mul_le_mul (by omega) (Nat.mul_le_mul (by omega) (by omega))))
  have key : 2 * p ^ 4 ≤ q ^ 4 * ((k + 4) * ((k + 3) * ((k + 2) * (k + 1)))) :=
    calc 2 * p ^ 4 ≤ 2 * q ^ 4 := Nat.mul_le_mul_left 2 h4
      _ = q ^ 4 * 2 := Nat.mul_comm _ _
      _ ≤ q ^ 4 * ((k + 4) * ((k + 3) * ((k + 2) * (k + 1)))) := Nat.mul_le_mul_left _ big
  rw [f, e1, e2]
  have m := Nat.mul_le_mul_left (p ^ k * q ^ k * factorial k) key
  calc 2 * (p ^ k * p ^ 4 * (q ^ k * factorial k)) = p ^ k * q ^ k * factorial k * (2 * p ^ 4) := by ac_rfl
    _ ≤ p ^ k * q ^ k * factorial k * (q ^ 4 * ((k + 4) * ((k + 3) * ((k + 2) * (k + 1))))) := m
    _ = p ^ k * (q ^ k * q ^ 4 * ((k + 4) * ((k + 3) * ((k + 2) * ((k + 1) * factorial k))))) := by ac_rfl

--| Twice a fraction.
def Fraction.twice (p : Fraction) : Fraction := ⟨2 * p.over, p.under, p.under_pos⟩

--| A term and twice the one four on are not past twice the term.
theorem the_term_and_twice_the_next (a b c d : Nat) (key : 2 * (c * b) ≤ a * d) :
    (a * d + 2 * c * b) * b ≤ 2 * a * (b * d) := by
  have m := Nat.mul_le_mul_right b key
  simp only [Nat.add_mul, Nat.mul_assoc] at m ⊢
  simp only [Nat.mul_comm, Nat.mul_left_comm] at m ⊢
  omega

--| THE j-TH QUARTER'S STEPS: θ to the four m and j over its factorial; the tail, twice the next.
def theQuarterSteps (p q : Nat) (hq : 0 < q) (hp : p ≤ q) (j : Nat) : StepsAndTail where
  step m := powerTerm p q hq (4 * m + j)
  tail m := (powerTerm p q hq (4 * (m + 1) + j)).twice
  tail_falls m := by
    show ((powerTerm p q hq (4 * (m + 1) + j)).add (powerTerm p q hq (4 * (m + 1 + 1) + j)).twice).le
      (powerTerm p q hq (4 * (m + 1) + j)).twice
    rw [show 4 * (m + 1 + 1) + j = (4 * (m + 1) + j) + 4 by omega]
    unfold Fraction.le Fraction.add Fraction.twice powerTerm
    dsimp only
    exact the_term_and_twice_the_next _ _ _ _ (twice_four_places_on p q _ hp)
  tail_narrows m := by
    show 2 * p ^ (4 * (m + 1) + j) * (m + 1) ≤ q ^ (4 * (m + 1) + j) * factorial (4 * (m + 1) + j)
    have h1 := Nat.pow_le_pow_left hp (4 * (m + 1) + j)
    have h2 : 2 * (m + 1) ≤ factorial (4 * (m + 1) + j) :=
      Nat.le_trans (by omega) (self_le_factorial _)
    calc 2 * p ^ (4 * (m + 1) + j) * (m + 1) = p ^ (4 * (m + 1) + j) * (2 * (m + 1)) := by ac_rfl
      _ ≤ q ^ (4 * (m + 1) + j) * factorial (4 * (m + 1) + j) := Nat.mul_le_mul h1 h2

--| THE QUARTERS OF THE EXPONENTIAL.
def quarter (p q : Nat) (hq : 0 < q) (hp : p ≤ q) (j : Nat) : Bracketed := (theQuarterSteps p q hq hp j).bracketed

--| At a stage, the brackets of two sides hold each other: neither low wall is past the other side's high wall.
def HoldEachOther (a b : Fraction × Fraction) : Prop := a.1.le b.2 ∧ b.1.le a.2
instance (a b : Fraction × Fraction) : Decidable (HoldEachOther a b) := inferInstanceAs (Decidable (_ ∧ _))

def walls (x : Bracketed) (n : Nat) : Fraction × Fraction := (x.low n, x.high n)
def wallsBeside (x y : Bracketed) (n : Nat) : Fraction × Fraction := ((x.low n).add (y.low n), (x.high n).add (y.high n))

--| COSINE IS THE FIRST QUARTER LESS THE THIRD, SINE THE SECOND LESS THE FOURTH: at the third stage, cosine beside the third
--| quarter holds the first, and sine beside the fourth holds the second; at θ one and at θ a half.
theorem cosine_beside_the_third_quarter_holds_the_first :
    HoldEachOther (wallsBeside (cosine 1 1 (by decide) (by decide)) (quarter 1 1 (by decide) (by decide) 2) 3)
        (walls (quarter 1 1 (by decide) (by decide) 0) 3)
      ∧ HoldEachOther (wallsBeside (cosine 1 2 (by decide) (by decide)) (quarter 1 2 (by decide) (by decide) 2) 3)
        (walls (quarter 1 2 (by decide) (by decide) 0) 3) := by
  decide +kernel

theorem sine_beside_the_fourth_quarter_holds_the_second :
    HoldEachOther (wallsBeside (sine 1 1 (by decide) (by decide)) (quarter 1 1 (by decide) (by decide) 3) 3)
        (walls (quarter 1 1 (by decide) (by decide) 1) 3)
      ∧ HoldEachOther (wallsBeside (sine 1 2 (by decide) (by decide)) (quarter 1 2 (by decide) (by decide) 3) 3)
        (walls (quarter 1 2 (by decide) (by decide) 1) 3) := by
  decide +kernel

--| ALL FOUR BESIDE EACH OTHER ARE THE BASE THE DERIVATIVE LEAVES ALONE: at θ one, at the third stage, the four quarters
--| beside each other hold e.
theorem the_four_quarters_beside_each_other_hold_e :
    HoldEachOther
      (((((quarter 1 1 (by decide) (by decide) 0).low 3).add ((quarter 1 1 (by decide) (by decide) 1).low 3)).add
          (((quarter 1 1 (by decide) (by decide) 2).low 3).add ((quarter 1 1 (by decide) (by decide) 3).low 3))),
       ((((quarter 1 1 (by decide) (by decide) 0).high 3).add ((quarter 1 1 (by decide) (by decide) 1).high 3)).add
          (((quarter 1 1 (by decide) (by decide) 2).high 3).add ((quarter 1 1 (by decide) (by decide) 3).high 3))))
      (walls theBaseTheDerivativeLeavesAlone 3) := by
  decide +kernel

--| AT θ NOTHING: the first quarter is one and the other three are nothing, wall for wall, at the third stage.
theorem at_nothing_the_quarters_are_one_and_three_nothings :
    (walls (quarter 0 1 (by decide) (by decide) 0) 3).1.over = (walls (quarter 0 1 (by decide) (by decide) 0) 3).1.under
      ∧ (walls (quarter 0 1 (by decide) (by decide) 0) 3).2.over = (walls (quarter 0 1 (by decide) (by decide) 0) 3).2.under
      ∧ (walls (quarter 0 1 (by decide) (by decide) 1) 3).1.over = 0
      ∧ (walls (quarter 0 1 (by decide) (by decide) 1) 3).2.over = 0
      ∧ (walls (quarter 0 1 (by decide) (by decide) 2) 3).2.over = 0
      ∧ (walls (quarter 0 1 (by decide) (by decide) 3) 3).2.over = 0 := by
  decide +kernel

end Meanings
