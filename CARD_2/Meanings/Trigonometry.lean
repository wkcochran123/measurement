/-
Cosine and sine, with no choice.

A series whose terms are never under nothing and each not past the one before, taken with alternating signs, is a real:
below, a term less the next added up so far; above, that and the next term.  The sum so far never falls, the sum and the
next term never rise, and the gap is the next term.  Cosine of p over q is such a series in the even powers, and sine in
the odd ones, for p not past q: each term falls to the one two places on because the angle squared is not past the
product of the two places.  At the third stage, at the angle one and at a half, cosine squared and sine squared beside each
other hold one.

Found on the way: the product of two reals reads them as far on as their first high wall's numerator, which for a fraction
of factorials is far too far; the circle is checked here on the walls at one stage instead.
-/
import Meanings.Signed
namespace Meanings

--| Adding something is never under what there was.
theorem Fraction.le_add_right (p t : Fraction) : p.le (p.add t) := by
  unfold Fraction.le Fraction.add
  have := Nat.mul_le_mul_right p.under (Nat.le_add_right (p.over * t.under) (t.over * p.under))
  calc p.over * (p.under * t.under) = p.over * t.under * p.under := by simp only [Nat.mul_comm, Nat.mul_left_comm]
    _ ≤ _ := this

--| Beside, regrouped.
theorem Fraction.add_regroup (a b c : Fraction) : ((a.add b).add c).le (a.add (b.add c)) := by
  unfold Fraction.le Fraction.add
  apply Nat.le_of_eq
  simp only [Nat.add_mul]
  simp only [Nat.mul_comm, Nat.mul_left_comm]
  omega

--| A SERIES OF STEPS NEVER UNDER NOTHING, AND A TAIL THAT BOUNDS WHAT IS LEFT.
structure StepsAndTail where
  step : Nat → Fraction
  tail : Nat → Fraction
  tail_falls : ∀ n, ((step (n + 1)).add (tail (n + 1))).le (tail n)
  tail_narrows : ∀ n, (tail n).over * (n + 1) ≤ (tail n).under

def StepsAndTail.partial (s : StepsAndTail) : Nat → Fraction
  | 0 => s.step 0
  | n + 1 => (s.partial n).add (s.step (n + 1))

--| The sum so far below, and it and the tail above.
def StepsAndTail.bracketed (s : StepsAndTail) : Bracketed where
  low n := s.partial n
  high n := (s.partial n).add (s.tail n)
  ordered n := Fraction.le_add_right _ _
  low_rises n := Fraction.le_add_right _ _
  high_falls n := Fraction.le_trans (Fraction.add_regroup _ _ _)
    (Fraction.add_le_add (Fraction.le_refl _) (s.tail_falls n))
  narrows n := by
    show ((s.partial n).add (s.tail n)).over * (s.partial n).under * (n + 1)
      ≤ (s.partial n).over * ((s.partial n).add (s.tail n)).under * (n + 1)
        + ((s.partial n).add (s.tail n)).under * (s.partial n).under
    unfold Fraction.add
    dsimp only
    have t := Nat.mul_le_mul_right ((s.partial n).under * (s.partial n).under) (s.tail_narrows n)
    generalize n + 1 = N at t ⊢
    generalize (s.partial n).over = a at t ⊢
    generalize (s.partial n).under = b at t ⊢
    generalize (s.tail n).over = c at t ⊢
    generalize (s.tail n).under = d at t ⊢
    simp only [Nat.add_mul] at t ⊢
    simp only [Nat.mul_comm, Nat.mul_left_comm] at t ⊢
    omega

--| LESS, where the one taken away is not past the other.
def Fraction.sub (a b : Fraction) : Fraction := ⟨a.over * b.under - b.over * a.under, a.under * b.under, Nat.mul_pos a.under_pos b.under_pos⟩

theorem Fraction.sub_then_add_is_not_past (a b c : Fraction) (cb : c.le b) (ba : b.le a) : ((a.sub b).add c).le a := by
  unfold Fraction.le Fraction.sub Fraction.add at *
  dsimp only
  obtain ⟨s, hs⟩ := Nat.exists_eq_add_of_le ba
  rw [hs, Nat.add_sub_cancel_left]
  have k := Nat.mul_le_mul_right (a.under * a.under) cb
  generalize a.over = ao at *; generalize a.under = au at *; generalize b.over = bo at *
  generalize b.under = bu at *; generalize c.over = co at *; generalize c.under = cu at *
  calc (s * cu + co * (au * bu)) * au = s * cu * au + co * bu * (au * au) := by rw [Nat.add_mul]; ac_rfl
    _ ≤ s * cu * au + bo * cu * (au * au) := Nat.add_le_add_left k _
    _ = (bo * au + s) * (au * cu) := by rw [Nat.add_mul]; ac_rfl
    _ = (ao * bu) * (au * cu) := by rw [hs]
    _ = ao * (au * bu * cu) := by ac_rfl

--| AN ALTERNATING SERIES.  Terms never under nothing, each not past the one before, and the even ones narrowing.
structure FallingTerms where
  term : Nat → Fraction
  falls : ∀ k, (term (k + 1)).le (term k)
  narrows : ∀ n, (term (2 * n + 2)).over * (n + 1) ≤ (term (2 * n + 2)).under

--| The steps are a term less the next, and the tail is the next even term.
def FallingTerms.stepsAndTail (t : FallingTerms) : StepsAndTail where
  step j := (t.term (2 * j)).sub (t.term (2 * j + 1))
  tail n := t.term (2 * n + 2)
  tail_falls n := by
    show (((t.term (2 * (n + 1))).sub (t.term (2 * (n + 1) + 1))).add (t.term (2 * (n + 1) + 2))).le (t.term (2 * n + 2))
    rw [show 2 * (n + 1) = 2 * n + 2 by omega]
    exact Fraction.sub_then_add_is_not_past _ _ _ (t.falls _) (t.falls _)
  tail_narrows n := t.narrows n

def FallingTerms.bracketed (t : FallingTerms) : Bracketed := t.stepsAndTail.bracketed

theorem self_le_factorial : ∀ m, m ≤ factorial m
  | 0 => Nat.zero_le _
  | m + 1 => by
    show m + 1 ≤ (m + 1) * factorial m
    exact Nat.le_mul_of_pos_right _ (factorial_pos m)

--| θ to the k over k factorial, for θ the fraction p over q.
def powerTerm (p q : Nat) (hq : 0 < q) (k : Nat) : Fraction :=
  ⟨p ^ k, q ^ k * factorial k, Nat.mul_pos (Nat.pow_pos hq) (factorial_pos k)⟩

theorem powerTerm_falls_by_two (p q : Nat) (hq : 0 < q) (hp : p ≤ q) (k : Nat) :
    (powerTerm p q hq (k + 2)).le (powerTerm p q hq k) := by
  show p ^ (k + 2) * (q ^ k * factorial k) ≤ p ^ k * (q ^ (k + 2) * factorial (k + 2))
  have pp : p * p ≤ q * q * ((k + 2) * (k + 1)) :=
    Nat.le_trans (Nat.mul_le_mul hp hp) (Nat.le_mul_of_pos_right _ (Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)))
  have big := Nat.mul_le_mul_left (p ^ k * q ^ k * factorial k) pp
  calc p ^ (k + 2) * (q ^ k * factorial k) = p ^ k * q ^ k * factorial k * (p * p) := by
        rw [Nat.pow_succ, Nat.pow_succ]; ac_rfl
    _ ≤ p ^ k * q ^ k * factorial k * (q * q * ((k + 2) * (k + 1))) := big
    _ = p ^ k * (q ^ (k + 2) * factorial (k + 2)) := by
        rw [Nat.pow_succ, Nat.pow_succ]; show _ = p ^ k * (q ^ k * q * q * ((k + 1 + 1) * ((k + 1) * factorial k))); ac_rfl

theorem powerTerm_narrows (p q : Nat) (hq : 0 < q) (hp : p ≤ q) (n K : Nat) (big : n + 1 ≤ K) :
    (powerTerm p q hq K).over * (n + 1) ≤ (powerTerm p q hq K).under :=
  Nat.mul_le_mul (Nat.pow_le_pow_left hp K) (Nat.le_trans big (self_le_factorial K))

--| COSINE AND SINE OF p OVER q, FOR p NOT PAST q.  The even terms and the odd terms.
def theTermsOfTheCosine (p q : Nat) (hq : 0 < q) (hp : p ≤ q) : FallingTerms where
  term j := powerTerm p q hq (2 * j)
  falls j := by rw [show 2 * (j + 1) = 2 * j + 2 by omega]; exact powerTerm_falls_by_two p q hq hp _
  narrows n := powerTerm_narrows p q hq hp n _ (by omega)

def theTermsOfTheSine (p q : Nat) (hq : 0 < q) (hp : p ≤ q) : FallingTerms where
  term j := powerTerm p q hq (2 * j + 1)
  falls j := by rw [show 2 * (j + 1) + 1 = 2 * j + 1 + 2 by omega]; exact powerTerm_falls_by_two p q hq hp _
  narrows n := powerTerm_narrows p q hq hp n _ (by omega)

def cosine (p q : Nat) (hq : 0 < q) (hp : p ≤ q) : Bracketed := (theTermsOfTheCosine p q hq hp).bracketed
def sine (p q : Nat) (hq : 0 < q) (hp : p ≤ q) : Bracketed := (theTermsOfTheSine p q hq hp).bracketed

--| THE CIRCLE, AT A STAGE.  Cosine and sine are never under nothing here, so cosine squared and sine squared beside each
--| other lie between the low walls squared and the high walls squared.  At the third stage, at θ one and θ a half, that
--| bracket holds one.
def theLowCircle (p q : Nat) (hq : 0 < q) (hp : p ≤ q) (n : Nat) : Fraction :=
  (((cosine p q hq hp).low n).mul ((cosine p q hq hp).low n)).add (((sine p q hq hp).low n).mul ((sine p q hq hp).low n))
def theHighCircle (p q : Nat) (hq : 0 < q) (hp : p ≤ q) (n : Nat) : Fraction :=
  (((cosine p q hq hp).high n).mul ((cosine p q hq hp).high n)).add (((sine p q hq hp).high n).mul ((sine p q hq hp).high n))

theorem the_circle_at_one_holds_one :
    (theLowCircle 1 1 (by decide) (by decide) 3).le ⟨1, 1, by decide⟩
      ∧ (⟨1, 1, by decide⟩ : Fraction).le (theHighCircle 1 1 (by decide) (by decide) 3) := by decide +kernel

theorem the_circle_at_a_half_holds_one :
    (theLowCircle 1 2 (by decide) (by decide) 3).le ⟨1, 1, by decide⟩
      ∧ (⟨1, 1, by decide⟩ : Fraction).le (theHighCircle 1 2 (by decide) (by decide) 3) := by decide +kernel

end Meanings
