/-
e to the θ by e to the θ owed is one, at every stage; and the tangent.

For θ = p over q not past one, e to the θ is the series of all the powers over their factorials: below, the sum so far;
above, that and twice the next term, which bounds what is left because each term is at most half the one before.  e to
the θ owed is the same terms with alternating signs.  Written as coefficients, as the circle was, the first variation of
the one cut-off is the one cut off a term sooner, and of the other it is the other cut off sooner, owed.  So their product
is one, and one term's worth more, which is held or owed as the cut-off is even or odd, every coefficient of one sign.
At the low walls the product is not past one; at the high walls it is not under one; so the two reals multiply to one.

The tangent is the sine over the cosine, the cosine handed in as past nothing at its first stage, where it is one less
half of θ squared, never under one half.
-/
import Meanings.Circle
import Meanings.Quarters
import Meanings.Reciprocal

namespace Meanings

/-! The tangent. -/

theorem the_cosine_is_past_nothing_at_its_first_stage (p q : Nat) (hq : 0 < q) (hp : p ≤ q) :
    0 < ((cosine p q hq hp).low 0).over := by
  show 0 < p ^ (2 * (2 * 0)) * (q ^ (2 * (2 * 0 + 1)) * factorial (2 * (2 * 0 + 1)))
    - p ^ (2 * (2 * 0 + 1)) * (q ^ (2 * (2 * 0)) * factorial (2 * (2 * 0)))
  have h : p ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left hp 2
  have hq2 : 0 < q ^ 2 := Nat.pow_pos hq
  show 0 < 1 * (q ^ 2 * 2) - p ^ 2 * (1 * 1)
  omega

--| THE TANGENT OF p OVER q, the sine over the cosine.
def tangent (p q : Nat) (hq : 0 < q) (hp : p ≤ q) : Bracketed :=
  (sine p q hq hp).div (cosine p q hq hp) 0 (the_cosine_is_past_nothing_at_its_first_stage p q hq hp)

--| THE TANGENT BY THE COSINE IS THE SINE.
theorem the_tangent_by_the_cosine_is_the_sine (p q : Nat) (hq : 0 < q) (hp : p ≤ q) :
    ((tangent p q hq hp).mul (cosine p q hq hp)).Same (sine p q hq hp) :=
  Bracketed.div_mul _ _ _ _

/-! e to the θ. -/

def Fraction.twice' (p : Fraction) : Fraction := ⟨2 * p.over, p.under, p.under_pos⟩

def theExponentialSteps (p q : Nat) (hq : 0 < q) (hp : p ≤ q) : StepsAndTail where
  step
    | 0 => (powerTerm p q hq 0).add (powerTerm p q hq 1)
    | j + 1 => powerTerm p q hq (j + 2)
  tail n := Fraction.twice' (powerTerm p q hq (n + 2))
  tail_falls n := by
    show (p ^ (n + 2) * (q ^ (n + 3) * factorial (n + 3)) + 2 * p ^ (n + 3) * (q ^ (n + 2) * factorial (n + 2)))
        * (q ^ (n + 2) * factorial (n + 2))
      ≤ 2 * p ^ (n + 2) * ((q ^ (n + 2) * factorial (n + 2)) * (q ^ (n + 3) * factorial (n + 3)))
    have key : 2 * p ^ (n + 3) * (q ^ (n + 2) * factorial (n + 2)) ≤ p ^ (n + 2) * (q ^ (n + 3) * factorial (n + 3)) := by
      have half : p * 2 ≤ q * (n + 3) := Nat.mul_le_mul hp (by omega)
      have f : factorial (n + 3) = (n + 3) * factorial (n + 2) := rfl
      rw [f, Nat.pow_succ p (n + 2), Nat.pow_succ q (n + 2)]
      calc 2 * (p ^ (n + 2) * p) * (q ^ (n + 2) * factorial (n + 2))
          = p ^ (n + 2) * q ^ (n + 2) * factorial (n + 2) * (p * 2) := by ac_rfl
        _ ≤ p ^ (n + 2) * q ^ (n + 2) * factorial (n + 2) * (q * (n + 3)) := Nat.mul_le_mul_left _ half
        _ = p ^ (n + 2) * (q ^ (n + 2) * q * ((n + 3) * factorial (n + 2))) := by ac_rfl
    calc (p ^ (n + 2) * (q ^ (n + 3) * factorial (n + 3)) + 2 * p ^ (n + 3) * (q ^ (n + 2) * factorial (n + 2)))
          * (q ^ (n + 2) * factorial (n + 2))
        ≤ (p ^ (n + 2) * (q ^ (n + 3) * factorial (n + 3)) + p ^ (n + 2) * (q ^ (n + 3) * factorial (n + 3)))
          * (q ^ (n + 2) * factorial (n + 2)) := Nat.mul_le_mul_right _ (Nat.add_le_add_left key _)
      _ = 2 * p ^ (n + 2) * ((q ^ (n + 2) * factorial (n + 2)) * (q ^ (n + 3) * factorial (n + 3))) := by
          rw [← Nat.two_mul]; ac_rfl
  tail_narrows n := by
    show 2 * p ^ (n + 2) * (n + 1) ≤ q ^ (n + 2) * factorial (n + 2)
    have h1 : p ^ (n + 2) ≤ q ^ (n + 2) := Nat.pow_le_pow_left hp _
    have h2 : 2 * (n + 1) ≤ factorial (n + 2) := by
      show 2 * (n + 1) ≤ (n + 2) * ((n + 1) * factorial n)
      have := factorial_pos n
      have : n + 1 ≤ (n + 1) * factorial n := Nat.le_mul_of_pos_right _ this
      calc 2 * (n + 1) ≤ (n + 2) * (n + 1) := Nat.mul_le_mul_right _ (by omega)
        _ ≤ (n + 2) * ((n + 1) * factorial n) := Nat.mul_le_mul_left _ this
    calc 2 * p ^ (n + 2) * (n + 1) = p ^ (n + 2) * (2 * (n + 1)) := by ac_rfl
      _ ≤ q ^ (n + 2) * factorial (n + 2) := Nat.mul_le_mul h1 h2

--| e TO THE θ, for θ = p over q not past one.
def eToThe (p q : Nat) (hq : 0 < q) (hp : p ≤ q) : Bracketed := (theExponentialSteps p q hq hp).bracketed

namespace Circle

/-! On the coefficients. -/

--| e to the θ cut off after the N-th power, and e to the θ owed.
def expHeld : Nat → Nat → Int
  | 0 => mono 0
  | N + 1 => plus (expHeld N) (mono (N + 1))

def expOwed : Nat → Nat → Int
  | 0 => mono 0
  | N + 1 => plus (expOwed N) (times (alt (N + 1)) (mono (N + 1)))

theorem alt_cases (k : Nat) : alt k = 1 ∨ alt k = -1 := by
  unfold alt; split
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem down_expHeld : ∀ N, down (expHeld (N + 1)) = expHeld N
  | 0 => by
    funext n
    show down (mono 0) n + down (mono (0 + 1)) n = mono 0 n
    rw [mono_down_zero, mono_down]; omega
  | N + 1 => by
    funext n
    show down (expHeld (N + 1)) n + down (mono (N + 1 + 1)) n = expHeld N n + mono (N + 1) n
    rw [down_expHeld N, mono_down]

theorem down_expOwed : ∀ N, down (expOwed (N + 1)) = owed (expOwed N)
  | 0 => by
    funext n
    show down (mono 0) n + alt (0 + 1) * down (mono (0 + 1)) n = - mono 0 n
    rw [mono_down_zero, mono_down, show alt (0 + 1) = -1 from rfl]; omega
  | N + 1 => by
    funext n
    show down (expOwed (N + 1)) n + alt (N + 1 + 1) * down (mono (N + 1 + 1)) n
      = - (expOwed N n + alt (N + 1) * mono (N + 1) n)
    rw [down_expOwed N, mono_down, alt_succ (N + 1), Int.neg_mul]
    show - expOwed N n + -(alt (N + 1) * mono (N + 1) n) = _
    omega

theorem expHeld_zero_place : ∀ N, expHeld N 0 = 1
  | 0 => rfl
  | N + 1 => by
    show expHeld N 0 + mono (N + 1) 0 = 1
    rw [expHeld_zero_place N, show mono (N + 1) 0 = 0 from if_neg (by omega)]; rfl

theorem expOwed_zero_place : ∀ N, expOwed N 0 = 1
  | 0 => rfl
  | N + 1 => by
    show expOwed N 0 + alt (N + 1) * mono (N + 1) 0 = 1
    rw [expOwed_zero_place N, show mono (N + 1) 0 = 0 from if_neg (by omega), Int.mul_zero]; rfl

theorem expHeld_past : ∀ N n, N < n → expHeld N n = 0
  | 0, n, h => if_neg (by omega)
  | N + 1, n, h => by
    show expHeld N n + mono (N + 1) n = 0
    rw [expHeld_past N n (by omega), show mono (N + 1) n = 0 from if_neg (by omega)]; rfl

theorem expOwed_past : ∀ N n, N < n → expOwed N n = 0
  | 0, n, h => if_neg (by omega)
  | N + 1, n, h => by
    show expOwed N n + alt (N + 1) * mono (N + 1) n = 0
    rw [expOwed_past N n (by omega), show mono (N + 1) n = 0 from if_neg (by omega), Int.mul_zero]; rfl

--| What the cut-off leaves: the held one against the term past it, signed by that term, less that term against the owed.
def expLeft (N : Nat) (h o : Nat → Int) (n : Nat) : Int :=
  alt (N + 1) * conv h (mono (N + 1)) n - conv (mono (N + 1)) o n

--| THE PRODUCT ON THE COEFFICIENTS.  One, and what the cut-off leaves, one place up.
theorem the_exponential_product_on_the_coefficients (N : Nat) :
    conv (expHeld (N + 1)) (expOwed (N + 1))
      = plus (mono 0) (up (expLeft N (expHeld N) (expOwed N))) := by
  funext n
  cases n with
  | zero =>
    show sumBelow _ 1 = mono 0 0 + 0
    rw [sumBelow_succ]
    show 0 + (choose 0 0 : Int) * expHeld (N + 1) 0 * expOwed (N + 1) (0 - 0) = 1 + 0
    rw [expHeld_zero_place, expOwed_zero_place]; rfl
  | succ n =>
    rw [conv_succ, down_expHeld, down_expOwed]
    show _ = mono 0 (n + 1) + expLeft N (expHeld N) (expOwed N) n
    unfold expLeft
    rw [show mono 0 (n + 1) = 0 from if_neg (by omega)]
    show conv (expHeld N) (plus (expOwed N) (times (alt (N + 1)) (mono (N + 1)))) n
        + conv (plus (expHeld N) (mono (N + 1))) (owed (expOwed N)) n = _
    rw [conv_plus_right, conv_times_right, conv_plus_left, conv_owed_right, conv_owed_right]
    omega

--| The left-over sums over the first M terms.
theorem expLeft_step (N M : Nat) :
    expLeft N (expHeld (M + 1)) (expOwed (M + 1))
      = plus (expLeft N (expHeld M) (expOwed M))
          (times ((alt (N + 1) - alt (M + 1)) * (choose (N + 1 + (M + 1)) (N + 1) : Int)) (mono (N + 1 + (M + 1)))) := by
  funext n
  unfold expLeft plus times
  show alt (N + 1) * conv (plus (expHeld M) (mono (M + 1))) (mono (N + 1)) n
      - conv (mono (N + 1)) (plus (expOwed M) (times (alt (M + 1)) (mono (M + 1)))) n = _
  rw [conv_plus_left, conv_plus_right, conv_times_right, conv_mono_mono, conv_mono_mono,
    choose_symm (M + 1) (N + 1), Nat.add_comm (M + 1) (N + 1)]
  show alt (N + 1) * (conv (expHeld M) (mono (N + 1)) n
        + (choose (N + 1 + (M + 1)) (N + 1) : Int) * mono (N + 1 + (M + 1)) n)
      - (conv (mono (N + 1)) (expOwed M) n
        + alt (M + 1) * ((choose (N + 1 + (M + 1)) (N + 1) : Int) * mono (N + 1 + (M + 1)) n))
    = (alt (N + 1) * conv (expHeld M) (mono (N + 1)) n - conv (mono (N + 1)) (expOwed M) n)
      + (alt (N + 1) - alt (M + 1)) * (choose (N + 1 + (M + 1)) (N + 1) : Int) * mono (N + 1 + (M + 1)) n
  generalize conv (expHeld M) (mono (N + 1)) n = a
  generalize conv (mono (N + 1)) (expOwed M) n = b
  generalize (choose (N + 1 + (M + 1)) (N + 1) : Int) = C
  generalize mono (N + 1 + (M + 1)) n = m
  generalize alt (N + 1) = x
  generalize alt (M + 1) = y
  have e : (x - y) * C * m = x * (C * m) - y * (C * m) := by
    rw [Int.sub_mul, Int.sub_mul, Int.mul_assoc, Int.mul_assoc]
  rw [e, Int.mul_add]
  omega

theorem expLeft_zero (N : Nat) :
    expLeft N (expHeld 0) (expOwed 0) = times (alt (N + 1) - 1) (mono (N + 1)) := by
  funext n
  unfold expLeft times
  show alt (N + 1) * conv (mono 0) (mono (N + 1)) n - conv (mono (N + 1)) (mono 0) n = _
  rw [conv_mono_mono, conv_mono_mono, Nat.zero_add, Nat.add_zero, choose_zero, choose_self, Int.sub_mul]
  show alt (N + 1) * ((1 : Int) * mono (N + 1) n) - (1 : Int) * mono (N + 1) n = _
  rw [Int.one_mul]

--| WHAT THE CUT-OFF LEAVES HAS ONE SIGN.  Held when the term past the cut-off is even, owed when it is odd.
theorem the_left_over_has_one_sign (p q K N : Nat) (hK : 2 * N + 2 ≤ 2 * K) : ∀ M, M ≤ N →
    0 ≤ alt (N + 1) * ev p q (2 * K) (up (expLeft N (expHeld M) (expOwed M)))
  | 0, _ => by
    rw [expLeft_zero, up_times, mono_up, ev_times, ev_mono _ _ _ _ (by omega)]
    rcases alt_cases (N + 1) with h | h <;> rw [h] <;> omega
  | M + 1, hM => by
    have ih := the_left_over_has_one_sign p q K N hK M (by omega)
    rw [expLeft_step, up_plus, ev_plus, up_times, mono_up, ev_times, ev_mono _ _ _ _ (by omega)]
    generalize ev p q (2 * K) (up (expLeft N (expHeld M) (expOwed M))) = V at *
    rw [Int.mul_assoc (alt (N + 1) - alt (M + 1))]
    have CT : (0 : Int) ≤ (choose (N + 1 + (M + 1)) (N + 1) : Int) * (term p q (2 * K) (N + 1 + (M + 1) + 1) : Int) :=
      Int.mul_nonneg (by omega) (by omega)
    generalize (choose (N + 1 + (M + 1)) (N + 1) : Int) * (term p q (2 * K) (N + 1 + (M + 1) + 1) : Int) = X at *
    rcases alt_cases (N + 1) with h | h <;> rcases alt_cases (M + 1) with h' | h' <;> rw [h] at ih <;> rw [h, h'] <;> omega

/-! The walls, valued, and the product. -/

theorem ev_expOwed_closed (p q K : Nat) : ∀ N, N ≤ K →
    ev p q K (expOwed N) = sumBelow (fun j => alt j * (term p q K j : Int)) (N + 1)
  | 0, _ => by
    rw [show expOwed 0 = mono 0 from rfl, ev_mono _ _ _ _ (Nat.zero_le _)]
    show (term p q K 0 : Int) = 0 + 1 * (term p q K 0 : Int)
    omega
  | N + 1, h => by
    rw [show expOwed (N + 1) = plus (expOwed N) (times (alt (N + 1)) (mono (N + 1))) from rfl, ev_plus, ev_times,
      ev_mono _ _ _ _ h, ev_expOwed_closed p q K N (by omega)]
    rfl

theorem val_exp_low (p q : Nat) (hq : 0 < q) (hp : p ≤ q) (K : Nat) : ∀ m, m + 1 ≤ K →
    Val ((eToThe p q hq hp).low m) (ev p q K (expHeld (m + 1))) (scale q K)
  | 0, h => val_congr (val_add (val_powerTerm p q hq K 0 (by omega)) (val_powerTerm p q hq K 1 h)) (by
      rw [show expHeld (0 + 1) = plus (mono 0) (mono (0 + 1)) from rfl, ev_plus, ev_mono _ _ _ _ (by omega),
        ev_mono _ _ _ _ h])
  | m + 1, h => val_congr (val_add (val_exp_low p q hq hp K m (by omega)) (val_powerTerm p q hq K (m + 2) h)) (by
      rw [show expHeld (m + 1 + 1) = plus (expHeld (m + 1)) (mono (m + 1 + 1)) from rfl, ev_plus, ev_mono _ _ _ _ h])

theorem val_exp_owed_low (p q : Nat) (hq : 0 < q) (hp : p ≤ q) (s : Nat) :
    Val ((eToTheOwed p q hq hp).low s) (ev p q (2 * s + 1) (expOwed (2 * s + 1))) (scale q (2 * s + 1)) := by
  refine val_congr (val_low (theTermsOfTheExponentialOwed p q hq hp) (fun j => (term p q (2 * s + 1) j : Int))
    (scale q (2 * s + 1)) (2 * s + 1) (fun j hj => val_powerTerm p q hq _ j hj) s (Nat.le_refl _)) ?_
  rw [lowValue_closed, ev_expOwed_closed p q _ (2 * s + 1) (Nat.le_refl _)]

theorem val_exp_owed_high (p q : Nat) (hq : 0 < q) (hp : p ≤ q) (s : Nat) :
    Val ((eToTheOwed p q hq hp).high s) (ev p q (2 * s + 2) (expOwed (2 * s + 2))) (scale q (2 * s + 2)) := by
  have a : alt (2 * s + 2) = 1 := by unfold alt; rw [if_pos (by omega)]
  refine val_congr (val_high (theTermsOfTheExponentialOwed p q hq hp) (fun j => (term p q (2 * s + 2) j : Int))
    (scale q (2 * s + 2)) (2 * s + 2) (fun j hj => val_powerTerm p q hq _ j hj) s (Nat.le_refl _)) ?_
  rw [lowValue_closed, ev_expOwed_closed p q _ (2 * s + 2) (Nat.le_refl _)]
  show sumBelow (fun j => alt j * (term p q (2 * s + 2) j : Int)) (2 * s + 2) + (term p q (2 * s + 2) (2 * s + 2) : Int)
    = sumBelow (fun j => alt j * (term p q (2 * s + 2) j : Int)) (2 * s + 2) + alt (2 * s + 2) * (term p q (2 * s + 2) (2 * s + 2) : Int)
  rw [a]; omega

--| THE PRODUCT, VALUED.
theorem the_exponential_product_valued (p q N K : Nat) (hK : N + 1 ≤ K) :
    ev p q K (expHeld (N + 1)) * ev p q K (expOwed (N + 1)) * (scale q (2 * K) : Int)
      = ((scale q (2 * K) : Int) + ev p q (2 * K) (up (expLeft N (expHeld N) (expOwed N))))
        * ((scale q K : Int) * scale q K) := by
  rw [ev_product p q K _ _ (fun n hn => expHeld_past _ n (by omega)) (fun n hn => expOwed_past _ n (by omega)),
    the_exponential_product_on_the_coefficients, ev_plus, ev_mono _ _ _ _ (Nat.zero_le _), term_at_nothing]

theorem the_low_exponential_product_is_not_past_one (p q : Nat) (hq : 0 < q) (hp : p ≤ q) (s : Nat) :
    (((eToThe p q hq hp).low s).mul ((eToTheOwed p q hq hp).low s)).le one := by
  apply Fraction.le_trans (Fraction.mul_le_mul ((eToThe p q hq hp).low_le_of_le (show s ≤ 2 * s by omega))
    (Fraction.le_refl _))
  apply le_one_of_val (val_mul (val_exp_low p q hq hp (2 * s + 1) (2 * s) (Nat.le_refl _)) (val_exp_owed_low p q hq hp s))
    (Nat.mul_pos (scale_pos q _ hq) (scale_pos q _ hq))
  have key := the_exponential_product_valued p q (2 * s) (2 * s + 1) (Nat.le_refl _)
  have sign := the_left_over_has_one_sign p q (2 * s + 1) (2 * s) (by omega) (2 * s) (Nat.le_refl _)
  have a : alt (2 * s + 1) = -1 := by unfold alt; rw [if_neg (by omega)]
  rw [a] at sign
  have S2 := scale_pos q (2 * (2 * s + 1)) hq
  have SS : (0 : Int) ≤ (scale q (2 * s + 1) : Int) * scale q (2 * s + 1) := Int.mul_nonneg (by omega) (by omega)
  apply Int.le_of_mul_le_mul_right _ (by omega : (0 : Int) < scale q (2 * (2 * s + 1)))
  rw [key, Int.natCast_mul]
  generalize ev p q (2 * (2 * s + 1)) (up (expLeft (2 * s) (expHeld (2 * s)) (expOwed (2 * s)))) = V at *
  generalize (scale q (2 * s + 1) : Int) * scale q (2 * s + 1) = T at *
  have VT : V * T ≤ 0 := by
    have := Int.mul_le_mul_of_nonneg_right (show V ≤ 0 by omega) SS
    rwa [Int.zero_mul] at this
  generalize (scale q (2 * (2 * s + 1)) : Int) = U at *
  rw [Int.add_mul, Int.mul_comm T U]
  omega

theorem the_high_exponential_product_is_not_under_one (p q : Nat) (hq : 0 < q) (hp : p ≤ q) (s : Nat) :
    one.le (((eToThe p q hq hp).high s).mul ((eToTheOwed p q hq hp).high s)) := by
  refine Fraction.le_trans ?_ (Fraction.mul_le_mul
    (Fraction.le_trans ((eToThe p q hq hp).ordered (2 * s + 1)) ((eToThe p q hq hp).high_le_of_le (show s ≤ 2 * s + 1 by omega)))
    (Fraction.le_refl _))
  apply one_le_of_val (val_mul (val_exp_low p q hq hp (2 * s + 2) (2 * s + 1) (Nat.le_refl _)) (val_exp_owed_high p q hq hp s))
    (Nat.mul_pos (scale_pos q _ hq) (scale_pos q _ hq))
  have key := the_exponential_product_valued p q (2 * s + 1) (2 * s + 2) (Nat.le_refl _)
  have sign := the_left_over_has_one_sign p q (2 * s + 2) (2 * s + 1) (by omega) (2 * s + 1) (Nat.le_refl _)
  have a : alt (2 * s + 1 + 1) = 1 := by unfold alt; rw [if_pos (by omega)]
  rw [a, Int.one_mul] at sign
  have SS : (0 : Int) ≤ (scale q (2 * s + 2) : Int) * scale q (2 * s + 2) := Int.mul_nonneg (by omega) (by omega)
  have S2 := scale_pos q (2 * (2 * s + 2)) hq
  apply Int.le_of_mul_le_mul_right _ (by omega : (0 : Int) < scale q (2 * (2 * s + 2)))
  rw [key, Int.natCast_mul]
  generalize ev p q (2 * (2 * s + 2)) (up (expLeft (2 * s + 1) (expHeld (2 * s + 1)) (expOwed (2 * s + 1)))) = V at *
  generalize (scale q (2 * s + 2) : Int) * scale q (2 * s + 2) = T at *
  have VT : 0 ≤ V * T := Int.mul_nonneg sign SS
  generalize (scale q (2 * (2 * s + 2)) : Int) = U at *
  rw [Int.add_mul, Int.mul_comm T U]
  omega

end Circle

--| e TO THE θ BY e TO THE θ OWED IS ONE, at every pair of stages, for θ = p over q not past one.
theorem e_to_the_theta_by_e_to_the_theta_owed_is_one (p q : Nat) (hq : 0 < q) (hp : p ≤ q) :
    ((eToThe p q hq hp).mul (eToTheOwed p q hq hp)).Same (Bracketed.ofNat 1) := fun _ _ =>
  ⟨Circle.the_low_exponential_product_is_not_past_one p q hq hp _,
   Circle.the_high_exponential_product_is_not_under_one p q hq hp _⟩

end Meanings
