/-
The four quarters of the exponential, with no choice.

The powers of the quarter turn come round in four: one, the quarter turn, one owed, the quarter turn owed.  So the one
series of θ to the k over k factorial, taken with the quarter turn, falls into four series by k counted in fours: the
quarters S₀, S₁, S₂ and S₃.  Each has terms never under nothing, and each term is not past half the one four places
before it, so twice the next term bounds what is left, and each quarter is a real with no choice, for θ = p over q not
past one.

Cosine is the first quarter less the third, sine the second less the fourth; all four beside each other are the base the
derivative leaves alone, raised to θ; and at θ nothing they are one and three nothings.  What is checked here of those is
what the circle check checks: at the third stage, at θ one and θ a half, the brackets of the two sides hold each other,
decided by the kernel.  The first two are then proved one at every stage, for every θ = p over q not past one, from an
exact identity on the partial sums; and the four against e, at θ one, likewise at every stage.
-/
import Meanings.Difference

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

/-
THE IDENTITIES AT EVERY STAGE.  Two reals whose brackets hold each other at every single stage are one, because walls only
move inward: any two stages are compared at their sum.  An alternating series of falling terms, beside its odd terms
summed, is its even terms summed, exactly, at every length; so cosine beside the third quarter is the first, and sine
beside the fourth is the second, for every θ = p over q not past one.
-/

--| Holding each other at every stage is being one.
theorem Bracketed.same_of_each_stage {x y : Bracketed}
    (h : ∀ k, (x.low k).le (y.high k) ∧ (y.low k).le (x.high k)) : x.Same y := fun n m =>
  ⟨Fraction.le_trans (x.low_le_of_le (Nat.le_add_right n m))
    (Fraction.le_trans (h (n + m)).1 (y.high_le_of_le (Nat.le_add_left m n))),
   Fraction.le_trans (y.low_le_of_le (Nat.le_add_right n m))
    (Fraction.le_trans (h (n + m)).2 (x.high_le_of_le (Nat.le_add_left m n)))⟩

--| A term less the next, beside the next, is the term, both ways.
theorem Fraction.sub_add_self_le (a b : Fraction) (h : b.le a) : ((a.sub b).add b).le a :=
  Fraction.sub_then_add_is_not_past a b b (Fraction.le_refl b) h

theorem Fraction.le_sub_add_self (a b : Fraction) (h : b.le a) : a.le ((a.sub b).add b) :=
  Fraction.le_sub_add h (Fraction.le_refl a) (Fraction.le_refl b)

--| THE ALTERNATING SUM AND THE ODD SUM ARE THE EVEN SUM, at every length.
theorem the_alternating_and_the_odd_are_the_even (t : FallingTerms) (E O : StepsAndTail)
    (hE : ∀ j, E.step j = t.term (2 * j)) (hO : ∀ j, O.step j = t.term (2 * j + 1)) (M : Nat) :
    ((t.stepsAndTail.partial M).add (O.partial M)).le (E.partial M)
      ∧ (E.partial M).le ((t.stepsAndTail.partial M).add (O.partial M)) := by
  induction M with
  | zero =>
    show (((t.term (2 * 0)).sub (t.term (2 * 0 + 1))).add (O.step 0)).le (E.step 0)
      ∧ (E.step 0).le (((t.term (2 * 0)).sub (t.term (2 * 0 + 1))).add (O.step 0))
    rw [hE, hO]
    exact ⟨Fraction.sub_add_self_le _ _ (t.falls _), Fraction.le_sub_add_self _ _ (t.falls _)⟩
  | succ M ih =>
    show (((t.stepsAndTail.partial M).add ((t.term (2 * (M + 1))).sub (t.term (2 * (M + 1) + 1)))).add
          ((O.partial M).add (O.step (M + 1)))).le ((E.partial M).add (E.step (M + 1)))
      ∧ ((E.partial M).add (E.step (M + 1))).le
          (((t.stepsAndTail.partial M).add ((t.term (2 * (M + 1))).sub (t.term (2 * (M + 1) + 1)))).add
            ((O.partial M).add (O.step (M + 1))))
    rw [hE, hO]
    exact ⟨Fraction.le_trans (Fraction.swap_middle _ _ _ _)
        (Fraction.add_le_add ih.1 (Fraction.sub_add_self_le _ _ (t.falls _))),
      Fraction.le_trans (Fraction.add_le_add ih.2 (Fraction.le_sub_add_self _ _ (t.falls _)))
        (Fraction.swap_middle _ _ _ _)⟩

--| From the partial sums to the reals: the alternating real beside the odd real is the even real.
theorem the_alternating_beside_the_odd_is_the_even (t : FallingTerms) (E O : StepsAndTail)
    (hE : ∀ j, E.step j = t.term (2 * j)) (hO : ∀ j, O.step j = t.term (2 * j + 1)) :
    (t.bracketed.add O.bracketed).Same E.bracketed :=
  Bracketed.same_of_each_stage fun k =>
    ⟨Fraction.le_trans (the_alternating_and_the_odd_are_the_even t E O hE hO (2 * k + 1)).1
        (E.bracketed.low_under_high (2 * k + 1) k),
     Fraction.le_trans (E.bracketed.low_le_of_le (show k ≤ 2 * k + 1 by omega))
      (Fraction.le_trans (the_alternating_and_the_odd_are_the_even t E O hE hO (2 * k + 1)).2
        (Fraction.add_le_add (t.bracketed.ordered _) (O.bracketed.ordered _)))⟩

--| COSINE BESIDE THE THIRD QUARTER IS THE FIRST, at every stage.
theorem cosine_beside_the_third_quarter_is_the_first (p q : Nat) (hq : 0 < q) (hp : p ≤ q) :
    ((cosine p q hq hp).add (quarter p q hq hp 2)).Same (quarter p q hq hp 0) :=
  the_alternating_beside_the_odd_is_the_even (theTermsOfTheCosine p q hq hp) _ _
    (fun j => by show powerTerm p q hq (4 * j + 0) = powerTerm p q hq (2 * (2 * j)); congr 1; omega)
    (fun j => by show powerTerm p q hq (4 * j + 2) = powerTerm p q hq (2 * (2 * j + 1)); congr 1; omega)

--| SINE BESIDE THE FOURTH QUARTER IS THE SECOND, at every stage.
theorem sine_beside_the_fourth_quarter_is_the_second (p q : Nat) (hq : 0 < q) (hp : p ≤ q) :
    ((sine p q hq hp).add (quarter p q hq hp 3)).Same (quarter p q hq hp 1) :=
  the_alternating_beside_the_odd_is_the_even (theTermsOfTheSine p q hq hp) _ _
    (fun j => by show powerTerm p q hq (4 * j + 1) = powerTerm p q hq (2 * (2 * j) + 1); congr 1; omega)
    (fun j => by show powerTerm p q hq (4 * j + 3) = powerTerm p q hq (2 * (2 * j + 1) + 1); congr 1; omega)

/-
ALL FOUR BESIDE EACH OTHER ARE e, AT EVERY STAGE.  The four quarters' partial sums, regrouped, are the one series' partial
sum, exactly, at every length; and at θ one that series is e's own, the series by the factorial over the factorial.
-/

--| The one series, θ to the k over k factorial, summed to n.
def expPartial (p q : Nat) (hq : 0 < q) : Nat → Fraction
  | 0 => powerTerm p q hq 0
  | n + 1 => (expPartial p q hq n).add (powerTerm p q hq (n + 1))

theorem expPartial_rises (p q : Nat) (hq : 0 < q) (n : Nat) : ∀ d, (expPartial p q hq n).le (expPartial p q hq (n + d))
  | 0 => Fraction.le_refl _
  | d + 1 => Fraction.le_trans (expPartial_rises p q hq n d) (Fraction.le_add_right _ _)

theorem expPartial_mono (p q : Nat) (hq : 0 < q) {n N : Nat} (h : n ≤ N) : (expPartial p q hq n).le (expPartial p q hq N) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h; exact expPartial_rises p q hq n d

--| Beside, regrouped, four ways, both ways.
theorem four_on_one_le (E A B C D : Fraction) :
    ((((E.add A).add B).add C).add D).le (E.add (((A.add B).add C).add D)) :=
  Fraction.le_trans (Fraction.add_le_add (Fraction.add_le_add (Fraction.add_regroup E A B) (Fraction.le_refl C)) (Fraction.le_refl D))
    (Fraction.le_trans (Fraction.add_le_add (Fraction.add_regroup E (A.add B) C) (Fraction.le_refl D))
      (Fraction.add_regroup E ((A.add B).add C) D))

theorem four_on_one_ge (E A B C D : Fraction) :
    (E.add (((A.add B).add C).add D)).le ((((E.add A).add B).add C).add D) :=
  Fraction.le_trans (Fraction.add_regroup_back E ((A.add B).add C) D)
    (Fraction.le_trans (Fraction.add_le_add (Fraction.add_regroup_back E (A.add B) C) (Fraction.le_refl D))
      (Fraction.add_le_add (Fraction.add_le_add (Fraction.add_regroup_back E A B) (Fraction.le_refl C)) (Fraction.le_refl D)))

theorem two_pairs_le (a A b B c C d D : Fraction) :
    (((a.add A).add (b.add B)).add ((c.add C).add (d.add D))).le
      (((a.add b).add (c.add d)).add (((A.add B).add C).add D)) :=
  Fraction.le_trans (Fraction.add_le_add (Fraction.swap_middle a A b B) (Fraction.swap_middle c C d D))
    (Fraction.le_trans (Fraction.swap_middle _ _ _ _)
      (Fraction.add_le_add (Fraction.le_refl _) (Fraction.add_regroup_back (A.add B) C D)))

theorem two_pairs_ge (a A b B c C d D : Fraction) :
    (((a.add b).add (c.add d)).add (((A.add B).add C).add D)).le
      (((a.add A).add (b.add B)).add ((c.add C).add (d.add D))) :=
  Fraction.le_trans (Fraction.add_le_add (Fraction.le_refl _) (Fraction.add_regroup (A.add B) C D))
    (Fraction.le_trans (Fraction.swap_middle _ _ _ _)
      (Fraction.add_le_add (Fraction.swap_middle a b A B) (Fraction.swap_middle c d C D)))

def fourQuartersPartial (p q : Nat) (hq : 0 < q) (hp : p ≤ q) (M : Nat) : Fraction :=
  (((theQuarterSteps p q hq hp 0).partial M).add ((theQuarterSteps p q hq hp 1).partial M)).add
    (((theQuarterSteps p q hq hp 2).partial M).add ((theQuarterSteps p q hq hp 3).partial M))

theorem quarter_step (p q : Nat) (hq : 0 < q) (hp : p ≤ q) (j M : Nat) :
    (theQuarterSteps p q hq hp j).step (M + 1) = powerTerm p q hq (4 * M + 3 + (j + 1)) := by
  show powerTerm p q hq (4 * (M + 1) + j) = _; congr 1; omega

--| THE FOUR QUARTERS' PARTIAL SUMS ARE THE ONE SERIES' PARTIAL SUM, at every length.
theorem the_four_quarters_are_the_series (p q : Nat) (hq : 0 < q) (hp : p ≤ q) (M : Nat) :
    (fourQuartersPartial p q hq hp M).le (expPartial p q hq (4 * M + 3))
      ∧ (expPartial p q hq (4 * M + 3)).le (fourQuartersPartial p q hq hp M) := by
  induction M with
  | zero => exact ⟨Fraction.add_regroup_back _ _ _, Fraction.add_regroup _ _ _⟩
  | succ M ih =>
    have e : expPartial p q hq (4 * (M + 1) + 3)
        = (((((expPartial p q hq (4 * M + 3)).add (powerTerm p q hq (4 * M + 3 + 1))).add
            (powerTerm p q hq (4 * M + 3 + 2))).add (powerTerm p q hq (4 * M + 3 + 3))).add
            (powerTerm p q hq (4 * M + 3 + 4))) := by
      rw [show 4 * (M + 1) + 3 = 4 * M + 3 + 1 + 1 + 1 + 1 by omega]; rfl
    have g : fourQuartersPartial p q hq hp (M + 1)
        = ((((theQuarterSteps p q hq hp 0).partial M).add (powerTerm p q hq (4 * M + 3 + 1))).add
            (((theQuarterSteps p q hq hp 1).partial M).add (powerTerm p q hq (4 * M + 3 + 2)))).add
          ((((theQuarterSteps p q hq hp 2).partial M).add (powerTerm p q hq (4 * M + 3 + 3))).add
            (((theQuarterSteps p q hq hp 3).partial M).add (powerTerm p q hq (4 * M + 3 + 4)))) := by
      show (((((theQuarterSteps p q hq hp 0).partial M).add ((theQuarterSteps p q hq hp 0).step (M + 1))).add
            (((theQuarterSteps p q hq hp 1).partial M).add ((theQuarterSteps p q hq hp 1).step (M + 1)))).add
          ((((theQuarterSteps p q hq hp 2).partial M).add ((theQuarterSteps p q hq hp 2).step (M + 1))).add
            (((theQuarterSteps p q hq hp 3).partial M).add ((theQuarterSteps p q hq hp 3).step (M + 1))))) = _
      rw [quarter_step, quarter_step, quarter_step, quarter_step]
    rw [e, g]
    exact ⟨Fraction.le_trans (two_pairs_le _ _ _ _ _ _ _ _)
        (Fraction.le_trans (Fraction.add_le_add ih.1 (Fraction.le_refl _)) (four_on_one_ge _ _ _ _ _)),
      Fraction.le_trans (four_on_one_le _ _ _ _ _)
        (Fraction.le_trans (Fraction.add_le_add ih.2 (Fraction.le_refl _)) (two_pairs_ge _ _ _ _ _ _ _ _))⟩

--| AT θ ONE THE SERIES IS e's OWN: the series by the factorial, over the factorial.
theorem e_is_the_series_at_one (m : Nat) :
    (⟨seriesByFactorial m, factorial m, factorial_pos m⟩ : Fraction).le (expPartial 1 1 (by decide) m)
      ∧ (expPartial 1 1 (by decide) m).le ⟨seriesByFactorial m, factorial m, factorial_pos m⟩ := by
  induction m with
  | zero => exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  | succ m ih =>
    have v : (⟨seriesByFactorial (m + 1), factorial (m + 1), factorial_pos _⟩ : Fraction).le
          ((⟨seriesByFactorial m, factorial m, factorial_pos m⟩ : Fraction).add (powerTerm 1 1 (by decide) (m + 1)))
        ∧ ((⟨seriesByFactorial m, factorial m, factorial_pos m⟩ : Fraction).add (powerTerm 1 1 (by decide) (m + 1))).le
          ⟨seriesByFactorial (m + 1), factorial (m + 1), factorial_pos _⟩ := by
      unfold Fraction.le Fraction.add powerTerm
      simp only [seriesByFactorial, factorial, Nat.one_pow, Nat.one_mul]
      constructor <;> apply Nat.le_of_eq <;> simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul] <;> ac_rfl
    exact ⟨Fraction.le_trans v.1 (Fraction.add_le_add ih.1 (Fraction.le_refl _)),
      Fraction.le_trans (Fraction.add_le_add ih.2 (Fraction.le_refl _)) v.2⟩

--| ALL FOUR QUARTERS BESIDE EACH OTHER ARE e, AT EVERY STAGE.
def theFourQuartersAtOne : Bracketed :=
  ((quarter 1 1 (by decide) (by decide) 0).add (quarter 1 1 (by decide) (by decide) 1)).add
    ((quarter 1 1 (by decide) (by decide) 2).add (quarter 1 1 (by decide) (by decide) 3))

theorem theFourQuartersAtOne_low (k : Nat) :
    theFourQuartersAtOne.low k = fourQuartersPartial 1 1 (by decide) (by decide) (2 * (2 * k + 1) + 1) := rfl

theorem theBase_low (n : Nat) :
    theBaseTheDerivativeLeavesAlone.low n = ⟨seriesByFactorial (n + 1), factorial (n + 1), factorial_pos _⟩ := rfl

theorem the_four_quarters_beside_each_other_are_e : theFourQuartersAtOne.Same theBaseTheDerivativeLeavesAlone := by
  apply Bracketed.same_of_each_stage
  intro k
  have hq := the_four_quarters_are_the_series 1 1 (by decide) (by decide) (2 * (2 * k + 1) + 1)
  have he := e_is_the_series_at_one (4 * (2 * (2 * k + 1) + 1) + 2 + 1)
  have he' := e_is_the_series_at_one (k + 1)
  have mono := expPartial_mono 1 1 (by decide) (show k + 1 ≤ 4 * (2 * (2 * k + 1) + 1) + 3 by omega)
  have lh := theBaseTheDerivativeLeavesAlone.low_under_high (4 * (2 * (2 * k + 1) + 1) + 2) k
  have ord := theFourQuartersAtOne.ordered k
  rw [theBase_low] at lh
  rw [theFourQuartersAtOne_low] at ord ⊢
  rw [theBase_low]
  exact ⟨Fraction.le_trans hq.1 (Fraction.le_trans he.2 lh),
    Fraction.le_trans he'.1 (Fraction.le_trans mono (Fraction.le_trans hq.2 ord))⟩

end Meanings
