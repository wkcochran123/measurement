/-
The circle, at every stage.

Cosine and sine are written as their coefficients: what stands beside θ to the n over n factorial.  Read that way, the
first variation is a shift, one place down, and a product is a sum weighed by the ways of choosing (Leibniz's rule is
Pascal's).  Cut off after the N-th term, the cosine's first variation is the sine owed and one coefficient left over, at
2N + 1; the sine's is the cosine.  So the first variation of cosine squared beside sine squared is what that one
coefficient leaves, and nothing else; at nothing it is one.  Cosine squared and sine squared beside each other are one,
and the leftover term's half-way sum, owed or held as N is odd or even.

That sum is an alternating series of falling terms, so it is never under nothing.  At the low walls N is odd and the
circle is under one; at the high walls N is even and it is past one.  So at every stage the low walls squared are not
past one and the high walls squared are not under it, and the reals are one.  Nothing is taken from outside: the
evaluation is whole numbers over q to the K and K factorial, and the identity is exact.
-/
import Meanings.Trigonometry
import Meanings.Laws

namespace Meanings
namespace Circle

/-! Sums, written out. -/

def sumBelow (f : Nat → Int) : Nat → Int
  | 0 => 0
  | n + 1 => sumBelow f n + f n

theorem sumBelow_succ (f : Nat → Int) (n : Nat) : sumBelow f (n + 1) = sumBelow f n + f n := rfl

theorem sumBelow_congr {f g : Nat → Int} : ∀ {n : Nat}, (∀ i, i < n → f i = g i) → sumBelow f n = sumBelow g n
  | 0, _ => rfl
  | n + 1, h => by
    rw [sumBelow_succ, sumBelow_succ, sumBelow_congr (fun i hi => h i (Nat.lt_succ_of_lt hi)), h n (Nat.lt_succ_self n)]

theorem sumBelow_add (f g : Nat → Int) : ∀ n, sumBelow (fun i => f i + g i) n = sumBelow f n + sumBelow g n
  | 0 => rfl
  | n + 1 => by
    rw [sumBelow_succ, sumBelow_succ, sumBelow_succ, sumBelow_add f g n]
    omega

theorem sumBelow_mul (c : Int) (f : Nat → Int) : ∀ n, sumBelow (fun i => c * f i) n = c * sumBelow f n
  | 0 => (Int.mul_zero c).symm
  | n + 1 => by rw [sumBelow_succ, sumBelow_succ, sumBelow_mul c f n, Int.mul_add]

theorem sumBelow_mul_right (c : Int) (f : Nat → Int) (n : Nat) : sumBelow (fun i => f i * c) n = sumBelow f n * c := by
  rw [Int.mul_comm, ← sumBelow_mul]
  exact sumBelow_congr fun i _ => Int.mul_comm _ _

theorem sumBelow_neg (f : Nat → Int) : ∀ n, sumBelow (fun i => - f i) n = - sumBelow f n
  | 0 => rfl
  | n + 1 => by
    rw [sumBelow_succ, sumBelow_succ, sumBelow_neg f n]
    omega

theorem sumBelow_zero {f : Nat → Int} : ∀ {n : Nat}, (∀ i, i < n → f i = 0) → sumBelow f n = 0
  | 0, _ => rfl
  | n + 1, h => by
    rw [sumBelow_succ, sumBelow_zero (fun i hi => h i (Nat.lt_succ_of_lt hi)), h n (Nat.lt_succ_self n)]
    rfl

--| The first term, and the rest moved down a place.
theorem sumBelow_first (f : Nat → Int) : ∀ n, sumBelow f (n + 1) = f 0 + sumBelow (fun i => f (i + 1)) n
  | 0 => by rw [sumBelow_succ]; show 0 + f 0 = f 0 + 0; omega
  | n + 1 => by
    rw [sumBelow_succ, sumBelow_first f n, sumBelow_succ]
    omega

--| One term that is not nothing.
theorem sumBelow_single {f : Nat → Int} {a : Nat} : ∀ {n : Nat}, a < n → (∀ i, i < n → i ≠ a → f i = 0) →
    sumBelow f n = f a
  | 0, ha, _ => absurd ha (Nat.not_lt_zero _)
  | n + 1, ha, h => by
    rw [sumBelow_succ]
    rcases Nat.lt_or_ge a n with lt | ge
    · rw [sumBelow_single lt (fun i hi ne => h i (Nat.lt_succ_of_lt hi) ne), h n (Nat.lt_succ_self n) (by omega)]
      omega
    · have e : a = n := by omega
      subst e
      rw [sumBelow_zero (fun i hi => h i (Nat.lt_succ_of_lt hi) (by omega))]
      omega

--| More terms, all nothing.
theorem sumBelow_extend {f : Nat → Int} {n : Nat} : ∀ (k : Nat), (∀ i, n ≤ i → i < n + k → f i = 0) →
    sumBelow f (n + k) = sumBelow f n
  | 0, _ => rfl
  | k + 1, h => by
    rw [← Nat.add_assoc, sumBelow_succ, sumBelow_extend k (fun i h1 h2 => h i h1 (by omega)), h (n + k) (by omega) (by omega)]
    omega

theorem sumBelow_extend' {f : Nat → Int} {n m : Nat} (nm : n ≤ m) (h : ∀ i, n ≤ i → i < m → f i = 0) :
    sumBelow f m = sumBelow f n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le nm
  exact sumBelow_extend k h

theorem sumBelow_mul_sumBelow (f g : Nat → Int) (m : Nat) : ∀ n,
    sumBelow f n * sumBelow g m = sumBelow (fun i => sumBelow (fun j => f i * g j) m) n
  | 0 => Int.zero_mul _
  | n + 1 => by
    rw [sumBelow_succ, sumBelow_succ, Int.add_mul, sumBelow_mul_sumBelow f g m n, sumBelow_mul]

--| THE TRIANGLE.  Summed by the total, or by the first and then the second.
theorem the_triangle (g : Nat → Nat → Int) : ∀ M,
    sumBelow (fun n => sumBelow (fun j => g j (n - j)) (n + 1)) M
      = sumBelow (fun j => sumBelow (fun l => g j l) (M - j)) M
  | 0 => rfl
  | M + 1 => by
    rw [sumBelow_succ, the_triangle g M]
    have inner : sumBelow (fun j => sumBelow (fun l => g j l) (M + 1 - j)) (M + 1)
        = sumBelow (fun j => sumBelow (fun l => g j l) (M - j) + g j (M - j)) (M + 1) :=
      sumBelow_congr fun j hj => by
        rw [show M + 1 - j = (M - j) + 1 by omega, sumBelow_succ]
    rw [inner, sumBelow_add, sumBelow_succ (fun j => sumBelow (fun l => g j l) (M - j)), Nat.sub_self]
    show _ = _ + 0 + _
    omega

--| THE SQUARE.  The triangle, where nothing past R is anything.
theorem the_square (g : Nat → Nat → Int) (R M : Nat) (hM : R + R ≤ M + 1) (hR : R ≤ M)
    (h : ∀ j l, R ≤ j ∨ R ≤ l → g j l = 0) :
    sumBelow (fun j => sumBelow (fun l => g j l) (M - j)) M = sumBelow (fun j => sumBelow (fun l => g j l) R) R := by
  rw [sumBelow_extend' hR (fun j hj _ => sumBelow_zero fun l _ => h j l (Or.inl hj))]
  exact sumBelow_congr fun j hj =>
    sumBelow_extend' (by omega) (fun l hl _ => h j l (Or.inr hl))

/-! Choosing. -/

def choose : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => choose n k + choose n (k + 1)

theorem choose_succ_succ (n k : Nat) : choose (n + 1) (k + 1) = choose n k + choose n (k + 1) := rfl

theorem choose_zero (n : Nat) : choose n 0 = 1 := by cases n <;> rfl

theorem choose_past : ∀ n k, n < k → choose n k = 0
  | 0, _ + 1, _ => rfl
  | _, 0, h => absurd h (Nat.not_lt_zero _)
  | n + 1, k + 1, h => by
    rw [choose_succ_succ, choose_past n k (by omega), choose_past n (k + 1) (by omega)]

theorem choose_self : ∀ n, choose n n = 1
  | 0 => rfl
  | n + 1 => by rw [choose_succ_succ, choose_self n, choose_past n (n + 1) (Nat.lt_succ_self n)]

theorem factorial_succ (n : Nat) : factorial (n + 1) = (n + 1) * factorial n := rfl

--| THE WAYS OF CHOOSING, BY THE FACTORIALS.
theorem choose_by_factorials : ∀ a b, choose (a + b) a * factorial a * factorial b = factorial (a + b)
  | 0, b => by rw [choose_zero, Nat.zero_add, Nat.one_mul]; exact Nat.one_mul _
  | a + 1, 0 => by rw [Nat.add_zero, choose_self, Nat.one_mul]; exact Nat.mul_one _
  | a + 1, b + 1 => by
    have h1 := choose_by_factorials a (b + 1)
    have h2 := choose_by_factorials (a + 1) b
    rw [show a + 1 + (b + 1) = (a + 1 + b) + 1 by omega, choose_succ_succ, factorial_succ (a + 1 + b)]
    rw [show a + (b + 1) = a + 1 + b by omega] at h1
    rw [factorial_succ a, factorial_succ b] at *
    generalize choose (a + 1 + b) a = X at *
    generalize choose (a + 1 + b) (a + 1) = Y at *
    generalize factorial a = fa at *
    generalize factorial b = fb at *
    generalize factorial (a + 1 + b) = F at *
    calc (X + Y) * ((a + 1) * fa) * ((b + 1) * fb)
        = (a + 1) * (X * fa * ((b + 1) * fb)) + (b + 1) * (Y * ((a + 1) * fa) * fb) := by
          rw [Nat.add_mul, Nat.add_mul]; congr 1 <;> ac_rfl
      _ = (a + 1 + b + 1) * F := by rw [h1, h2, ← Nat.add_mul, show a + 1 + (b + 1) = a + 1 + b + 1 by omega]

theorem factorial_pos' (n : Nat) : 0 < factorial n := factorial_pos n

--| Choosing a of a and b is choosing b.
theorem choose_symm (a b : Nat) : choose (a + b) a = choose (a + b) b := by
  have h1 := choose_by_factorials a b
  have h2 := choose_by_factorials b a
  rw [Nat.add_comm b a] at h2
  have : choose (a + b) a * (factorial a * factorial b) = choose (a + b) b * (factorial a * factorial b) := by
    rw [← Nat.mul_assoc, h1, ← h2, Nat.mul_assoc, Nat.mul_comm (factorial a)]
  exact Nat.eq_of_mul_eq_mul_right (Nat.mul_pos (factorial_pos a) (factorial_pos b)) this

--| Two more of the second, and two more of the whole.
theorem choose_two_on (a b : Nat) :
    choose (a + b + 2) a * ((b + 1) * (b + 2)) = choose (a + b) a * ((a + b + 1) * (a + b + 2)) := by
  have h1 := choose_by_factorials a (b + 2)
  have h2 := choose_by_factorials a b
  rw [show a + (b + 2) = a + b + 2 by omega] at h1
  rw [show factorial (a + b + 2) = (a + b + 2) * ((a + b + 1) * factorial (a + b)) from rfl,
    show factorial (b + 2) = (b + 2) * ((b + 1) * factorial b) from rfl, ← h2] at h1
  generalize choose (a + b + 2) a = A at *
  generalize choose (a + b) a = B at *
  have : A * ((b + 1) * (b + 2)) * (factorial a * factorial b)
      = B * ((a + b + 1) * (a + b + 2)) * (factorial a * factorial b) := by
    calc A * ((b + 1) * (b + 2)) * (factorial a * factorial b)
        = A * factorial a * ((b + 2) * ((b + 1) * factorial b)) := by ac_rfl
      _ = (a + b + 2) * ((a + b + 1) * (B * factorial a * factorial b)) := h1
      _ = _ := by ac_rfl
  exact Nat.eq_of_mul_eq_mul_right (Nat.mul_pos (factorial_pos a) (factorial_pos b)) this

/-! Coefficients. -/

--| A coefficient at k alone.
def mono (k : Nat) (n : Nat) : Int := if n = k then 1 else 0
def plus (f g : Nat → Int) (n : Nat) : Int := f n + g n
def times (a : Int) (f : Nat → Int) (n : Nat) : Int := a * f n
def owed (f : Nat → Int) (n : Nat) : Int := - f n
--| The first variation: one place down.
def down (f : Nat → Int) (n : Nat) : Int := f (n + 1)
--| One place up, nothing at the bottom.
def up (f : Nat → Int) : Nat → Int
  | 0 => 0
  | n + 1 => f n

--| Held on the even, owed on the odd.
def alt (k : Nat) : Int := if k % 2 = 0 then 1 else -1

theorem alt_zero : alt 0 = 1 := rfl
theorem alt_succ (k : Nat) : alt (k + 1) = - alt k := by
  unfold alt; split <;> split <;> omega

theorem mono_down (k : Nat) : down (mono (k + 1)) = mono k := by
  funext n; unfold down mono; split <;> split <;> omega

theorem mono_down_zero (n : Nat) : down (mono 0) n = 0 := by
  unfold down mono; split <;> omega

theorem mono_up (k : Nat) : up (mono k) = mono (k + 1) := by
  funext n; cases n with
  | zero => rfl
  | succ n => show mono k n = mono (k + 1) (n + 1); unfold mono; split <;> split <;> omega

theorem up_times (a : Int) (f : Nat → Int) : up (times a f) = times a (up f) := by
  funext n; cases n with
  | zero => exact (Int.mul_zero a).symm
  | succ n => rfl

theorem up_plus (f g : Nat → Int) : up (plus f g) = plus (up f) (up g) := by
  funext n; cases n with
  | zero => rfl
  | succ n => rfl

--| COSINE AND SINE, CUT OFF.  The cosine to the 2N-th power, the sine to the 2N + 1-th.
def cosCoef : Nat → Nat → Int
  | 0 => mono 0
  | N + 1 => plus (cosCoef N) (times (alt (N + 1)) (mono (2 * N + 2)))

def sinCoef : Nat → Nat → Int
  | 0 => mono 1
  | N + 1 => plus (sinCoef N) (times (alt (N + 1)) (mono (2 * N + 3)))

theorem cosCoef_succ (N : Nat) : cosCoef (N + 1) = plus (cosCoef N) (times (alt (N + 1)) (mono (2 * N + 2))) := rfl
theorem sinCoef_succ (N : Nat) : sinCoef (N + 1) = plus (sinCoef N) (times (alt (N + 1)) (mono (2 * N + 3))) := rfl

--| THE SINE'S FIRST VARIATION IS THE COSINE.
theorem down_sin : ∀ N, down (sinCoef N) = cosCoef N
  | 0 => mono_down 0
  | N + 1 => by
    funext n
    show down (sinCoef N) n + alt (N + 1) * down (mono (2 * N + 2 + 1)) n = cosCoef N n + alt (N + 1) * mono (2 * N + 2) n
    rw [down_sin N, mono_down]

--| THE COSINE'S FIRST VARIATION IS THE SINE OWED, AND ONE COEFFICIENT LEFT OVER.
theorem down_cos : ∀ N, down (cosCoef N) = plus (owed (sinCoef N)) (times (alt N) (mono (2 * N + 1)))
  | 0 => by
    funext n
    show down (mono 0) n = - mono 1 n + 1 * mono 1 n
    rw [mono_down_zero, Int.one_mul]; omega
  | N + 1 => by
    funext n
    show down (cosCoef N) n + alt (N + 1) * down (mono (2 * N + 1 + 1)) n
      = - (sinCoef N n + alt (N + 1) * mono (2 * N + 3) n) + alt (N + 1) * mono (2 * (N + 1) + 1) n
    rw [down_cos N, mono_down, show 2 * (N + 1) + 1 = 2 * N + 3 by omega, alt_succ]
    show - sinCoef N n + alt N * mono (2 * N + 1) n + -alt N * mono (2 * N + 1) n = _
    rw [Int.neg_mul]
    omega

theorem cosCoef_zero_place : ∀ N, cosCoef N 0 = 1
  | 0 => rfl
  | N + 1 => by
    show cosCoef N 0 + alt (N + 1) * mono (2 * N + 2) 0 = 1
    rw [cosCoef_zero_place N, show mono (2 * N + 2) 0 = 0 from if_neg (by omega), Int.mul_zero]; rfl

theorem sinCoef_zero_place : ∀ N, sinCoef N 0 = 0
  | 0 => rfl
  | N + 1 => by
    show sinCoef N 0 + alt (N + 1) * mono (2 * N + 3) 0 = 0
    rw [sinCoef_zero_place N, show mono (2 * N + 3) 0 = 0 from if_neg (by omega), Int.mul_zero]; rfl

theorem cosCoef_past : ∀ N n, 2 * N < n → cosCoef N n = 0
  | 0, n, h => if_neg (by omega)
  | N + 1, n, h => by
    show cosCoef N n + alt (N + 1) * mono (2 * N + 2) n = 0
    rw [cosCoef_past N n (by omega), show mono (2 * N + 2) n = 0 from if_neg (by omega), Int.mul_zero]; rfl

theorem sinCoef_past : ∀ N n, 2 * N + 1 < n → sinCoef N n = 0
  | 0, n, h => if_neg (by omega)
  | N + 1, n, h => by
    show sinCoef N n + alt (N + 1) * mono (2 * N + 3) n = 0
    rw [sinCoef_past N n (by omega), show mono (2 * N + 3) n = 0 from if_neg (by omega), Int.mul_zero]; rfl

/-! The product, weighed by the ways of choosing. -/

def conv (f g : Nat → Int) (n : Nat) : Int := sumBelow (fun j => (choose n j : Int) * f j * g (n - j)) (n + 1)

theorem conv_plus_left (f g h : Nat → Int) (n : Nat) : conv (plus f g) h n = conv f h n + conv g h n := by
  unfold conv; rw [← sumBelow_add]
  exact sumBelow_congr fun j _ => by unfold plus; rw [Int.mul_add, Int.add_mul]

theorem conv_plus_right (f g h : Nat → Int) (n : Nat) : conv h (plus f g) n = conv h f n + conv h g n := by
  unfold conv; rw [← sumBelow_add]
  exact sumBelow_congr fun j _ => by unfold plus; rw [Int.mul_add]

theorem conv_times_left (a : Int) (f h : Nat → Int) (n : Nat) : conv (times a f) h n = a * conv f h n := by
  unfold conv; rw [← sumBelow_mul]
  exact sumBelow_congr fun j _ => by unfold times; ac_rfl

theorem conv_times_right (a : Int) (f h : Nat → Int) (n : Nat) : conv h (times a f) n = a * conv h f n := by
  unfold conv; rw [← sumBelow_mul]
  exact sumBelow_congr fun j _ => by unfold times; ac_rfl

theorem conv_owed_left (f h : Nat → Int) (n : Nat) : conv (owed f) h n = - conv f h n := by
  unfold conv; rw [← sumBelow_neg]
  exact sumBelow_congr fun j _ => by unfold owed; rw [Int.mul_neg, Int.neg_mul]

theorem conv_owed_right (f h : Nat → Int) (n : Nat) : conv h (owed f) n = - conv h f n := by
  unfold conv; rw [← sumBelow_neg]
  exact sumBelow_congr fun j _ => by unfold owed; rw [Int.mul_neg]

--| LEIBNIZ, FROM PASCAL.  The first variation of a product is each first variation against the other.
theorem conv_succ (f g : Nat → Int) (n : Nat) : conv f g (n + 1) = conv (down f) g n + conv f (down g) n := by
  unfold conv down
  rw [sumBelow_first, choose_zero, Nat.sub_zero]
  have split : sumBelow (fun i => (choose (n + 1) (i + 1) : Int) * f (i + 1) * g (n + 1 - (i + 1))) (n + 1)
      = sumBelow (fun i => (choose n i : Int) * f (i + 1) * g (n - i)) (n + 1)
        + sumBelow (fun i => (choose n (i + 1) : Int) * f (i + 1) * g (n - i)) (n + 1) := by
    rw [← sumBelow_add]
    exact sumBelow_congr fun i _ => by
      rw [choose_succ_succ, Nat.add_sub_add_right]; push_cast; rw [Int.add_mul, Int.add_mul]
  rw [split, sumBelow_first (fun j => (choose n j : Int) * f j * g (n - j + 1)) n, choose_zero, Nat.sub_zero,
    sumBelow_succ (fun i => (choose n (i + 1) : Int) * f (i + 1) * g (n - i)) n, choose_past n (n + 1) (by omega)]
  have last : sumBelow (fun i => (choose n (i + 1) : Int) * f (i + 1) * g (n - i)) n
      = sumBelow (fun i => (choose n (i + 1) : Int) * f (i + 1) * g (n - (i + 1) + 1)) n :=
    sumBelow_congr fun i hi => by rw [show n - (i + 1) + 1 = n - i by omega]
  rw [last]
  show _ = _ + ((1 : Nat) * f 0 * g (n + 1) + _)
  push_cast
  omega

--| A coefficient alone, against a coefficient alone.
theorem conv_mono_mono (a b n : Nat) : conv (mono a) (mono b) n = (choose (a + b) a : Int) * mono (a + b) n := by
  unfold conv
  rcases Nat.lt_or_ge n a with lt | ge
  · rw [sumBelow_zero fun j hj => by unfold mono; rw [if_neg (by omega)]; rw [Int.mul_zero, Int.zero_mul]]
    unfold mono; rw [if_neg (by omega), Int.mul_zero]
  · rw [sumBelow_single (a := a) (by omega) fun j _ ne => by unfold mono; rw [if_neg ne, Int.mul_zero, Int.zero_mul]]
    unfold mono
    rw [if_pos rfl, Int.mul_one]
    by_cases e : n = a + b
    · subst e; rw [if_pos (by omega), if_pos rfl]
    · rw [if_neg (by omega), if_neg e, Int.mul_zero, Int.mul_zero]

/-! The circle on the coefficients. -/

def circle (N : Nat) (n : Nat) : Int := conv (cosCoef N) (cosCoef N) n + conv (sinCoef N) (sinCoef N) n

--| What the left-over coefficient leaves.
def leftOver (N : Nat) (f : Nat → Int) (n : Nat) : Int := conv (mono (2 * N + 1)) f n + conv f (mono (2 * N + 1)) n

theorem circle_at_nothing (N : Nat) : circle N 0 = 1 := by
  unfold circle conv
  rw [sumBelow_succ, sumBelow_succ]
  show 0 + (1 : Nat) * cosCoef N 0 * cosCoef N 0 + (0 + (1 : Nat) * sinCoef N 0 * sinCoef N 0) = 1
  rw [cosCoef_zero_place, sinCoef_zero_place]
  decide

theorem circle_moves_by_the_left_over (N n : Nat) : circle N (n + 1) = alt N * leftOver N (cosCoef N) n := by
  unfold circle leftOver
  rw [conv_succ, conv_succ, down_cos, down_sin, conv_plus_left, conv_plus_right, conv_owed_left, conv_owed_right,
    conv_times_left, conv_times_right, Int.mul_add]
  generalize conv (sinCoef N) (cosCoef N) n = a
  generalize conv (cosCoef N) (sinCoef N) n = b
  generalize alt N * conv (mono (2 * N + 1)) (cosCoef N) n = c
  generalize alt N * conv (cosCoef N) (mono (2 * N + 1)) n = d
  omega

--| THE CIRCLE, ON THE COEFFICIENTS.  One, and the left-over term's sum one place up, by the sign of N.
theorem the_circle_on_the_coefficients (N : Nat) :
    circle N = plus (mono 0) (times (alt N) (up (leftOver N (cosCoef N)))) := by
  funext n
  cases n with
  | zero => rw [circle_at_nothing]; show (1 : Int) = 1 + alt N * 0; rw [Int.mul_zero]; rfl
  | succ n =>
    rw [circle_moves_by_the_left_over]
    show _ = mono 0 (n + 1) + alt N * leftOver N (cosCoef N) n
    unfold mono; rw [if_neg (by omega)]; omega


/-! Evaluation: whole numbers over q to the K and K factorial. -/

--| n + 1, n + 2, up to n + d.
def rise : Nat → Nat → Nat
  | _, 0 => 1
  | n, d + 1 => (n + 1) * rise (n + 1) d

theorem factorial_rise : ∀ n d, factorial n * rise n d = factorial (n + d)
  | _, 0 => Nat.mul_one _
  | n, d + 1 => by
    show factorial n * ((n + 1) * rise (n + 1) d) = _
    rw [← Nat.mul_assoc, Nat.mul_comm (factorial n), ← factorial_succ, factorial_rise (n + 1) d,
      show n + 1 + d = n + (d + 1) by omega]

--| θ to the n over n factorial, for θ = p over q, as a whole number over q to the K and K factorial.
def term (p q K n : Nat) : Nat := p ^ n * q ^ (K - n) * rise n (K - n)
def scale (q K : Nat) : Nat := q ^ K * factorial K

theorem scale_pos (q K : Nat) (hq : 0 < q) : 0 < scale q K := Nat.mul_pos (Nat.pow_pos hq) (factorial_pos K)

theorem term_by_factorial (p q K n : Nat) (h : n ≤ K) : term p q K n * factorial n = p ^ n * q ^ (K - n) * factorial K := by
  unfold term
  rw [Nat.mul_assoc, Nat.mul_comm (rise n (K - n)), factorial_rise, Nat.add_sub_of_le h]

theorem term_at_nothing (p q K : Nat) : term p q K 0 = scale q K := by
  have := factorial_rise 0 K
  unfold term scale
  rw [Nat.pow_zero, Nat.one_mul, Nat.sub_zero, Nat.zero_add] at *
  rw [← this]; exact congrArg _ (Nat.one_mul _).symm

--| Two places on: θ squared over the two places.
theorem term_two_on (p q M n : Nat) (h : n + 2 ≤ M) :
    term p q M (n + 2) * ((n + 1) * (n + 2)) * (q * q) = term p q M n * (p * p) := by
  unfold term
  obtain ⟨d, hd⟩ : ∃ d, M - n = d + 2 := ⟨M - n - 2, by omega⟩
  rw [show M - (n + 2) = d by omega, hd]
  show p ^ (n + 2) * q ^ d * rise (n + 2) d * ((n + 1) * (n + 2)) * (q * q)
    = p ^ n * q ^ (d + 2) * ((n + 1) * ((n + 2) * rise (n + 2) d)) * (p * p)
  rw [Nat.pow_succ, Nat.pow_succ, Nat.pow_succ q, Nat.pow_succ q]
  ac_rfl

--| THE PRODUCT OF TWO TERMS.  The ways of choosing, at twice the scale.
theorem term_product (p q K i j : Nat) (hi : i ≤ K) (hj : j ≤ K) :
    term p q K i * term p q K j * scale q (2 * K) = choose (i + j) i * term p q (2 * K) (i + j) * (scale q K * scale q K) := by
  have e1 : q ^ (K - i) * q ^ (K - j) * q ^ (2 * K) = q ^ (2 * K - (i + j)) * q ^ K * q ^ K := by
    rw [← Nat.pow_add, ← Nat.pow_add, ← Nat.pow_add, ← Nat.pow_add]; congr 1; omega
  apply Nat.eq_of_mul_eq_mul_right (Nat.mul_pos (factorial_pos i) (factorial_pos j))
  calc term p q K i * term p q K j * scale q (2 * K) * (factorial i * factorial j)
      = (term p q K i * factorial i) * (term p q K j * factorial j) * (q ^ (2 * K) * factorial (2 * K)) := by
        unfold scale; ac_rfl
    _ = (p ^ i * q ^ (K - i) * factorial K) * (p ^ j * q ^ (K - j) * factorial K) * (q ^ (2 * K) * factorial (2 * K)) := by
        rw [term_by_factorial _ _ _ _ hi, term_by_factorial _ _ _ _ hj]
    _ = (p ^ i * p ^ j) * (q ^ (K - i) * q ^ (K - j) * q ^ (2 * K)) * (factorial K * factorial K * factorial (2 * K)) := by
        ac_rfl
    _ = p ^ (i + j) * (q ^ (2 * K - (i + j)) * q ^ K * q ^ K) * (factorial K * factorial K * factorial (2 * K)) := by
        rw [← Nat.pow_add, e1]
    _ = (p ^ (i + j) * q ^ (2 * K - (i + j)) * factorial (2 * K)) * (q ^ K * factorial K * (q ^ K * factorial K)) := by
        ac_rfl
    _ = (term p q (2 * K) (i + j) * factorial (i + j)) * (scale q K * scale q K) := by
        rw [term_by_factorial _ _ _ _ (by omega)]; rfl
    _ = choose (i + j) i * term p q (2 * K) (i + j) * (scale q K * scale q K) * (factorial i * factorial j) := by
        rw [← choose_by_factorials i j]; ac_rfl

--| The value of the coefficients, over q to the K and K factorial.
def ev (p q K : Nat) (f : Nat → Int) : Int := sumBelow (fun n => f n * (term p q K n : Int)) (K + 1)

theorem ev_plus (p q K : Nat) (f g : Nat → Int) : ev p q K (plus f g) = ev p q K f + ev p q K g := by
  unfold ev; rw [← sumBelow_add]
  exact sumBelow_congr fun n _ => Int.add_mul _ _ _

theorem ev_times (p q K : Nat) (a : Int) (f : Nat → Int) : ev p q K (times a f) = a * ev p q K f := by
  unfold ev; rw [← sumBelow_mul]
  exact sumBelow_congr fun n _ => Int.mul_assoc _ _ _

theorem ev_mono (p q K k : Nat) (h : k ≤ K) : ev p q K (mono k) = term p q K k := by
  unfold ev
  rw [sumBelow_single (a := k) (by omega) fun i _ ne => by unfold mono; rw [if_neg ne, Int.zero_mul]]
  unfold mono; rw [if_pos rfl, Int.one_mul]

--| THE PRODUCT OF TWO VALUES IS THE VALUE OF THE PRODUCT, at twice the scale.
theorem ev_product (p q K : Nat) (f g : Nat → Int) (hf : ∀ n, K < n → f n = 0) (hg : ∀ n, K < n → g n = 0) :
    ev p q K f * ev p q K g * (scale q (2 * K) : Int)
      = ev p q (2 * K) (conv f g) * ((scale q K : Int) * scale q K) := by
  let h : Nat → Nat → Int := fun j l =>
    (choose (j + l) j : Int) * f j * g l * (term p q (2 * K) (j + l) : Int) * ((scale q K : Int) * scale q K)
  have right : ev p q (2 * K) (conv f g) * ((scale q K : Int) * scale q K)
      = sumBelow (fun n => sumBelow (fun j => h j (n - j)) (n + 1)) (2 * K + 1) := by
    unfold ev; rw [← sumBelow_mul_right]
    exact sumBelow_congr fun n _ => by
      unfold conv; rw [← sumBelow_mul_right, ← sumBelow_mul_right]
      exact sumBelow_congr fun j hj => by
        show _ = (choose (j + (n - j)) j : Int) * f j * g (n - j) * (term p q (2 * K) (j + (n - j)) : Int) * _
        rw [Nat.add_sub_of_le (by omega)]
  rw [right, the_triangle, the_square h (K + 1) (2 * K + 1) (by omega) (by omega) (fun j l hjl => by
    rcases hjl with hj | hl
    · show (choose (j + l) j : Int) * f j * _ * _ * _ = 0; rw [hf j (by omega)]; simp only [Int.mul_zero, Int.zero_mul]
    · show _ * g l * _ * _ = 0; rw [hg l (by omega)]; simp only [Int.mul_zero, Int.zero_mul])]
  unfold ev
  rw [sumBelow_mul_sumBelow, ← sumBelow_mul_right]
  exact sumBelow_congr fun i hi => by
    rw [← sumBelow_mul_right]
    exact sumBelow_congr fun j hj => by
      have e := congrArg (fun x : Nat => (x : Int)) (term_product p q K i j (by omega) (by omega))
      simp only [Int.natCast_mul] at e
      show f i * (term p q K i : Int) * (g j * (term p q K j : Int)) * (scale q (2 * K) : Int)
        = (choose (i + j) i : Int) * f i * g j * (term p q (2 * K) (i + j) : Int) * ((scale q K : Int) * scale q K)
      calc f i * (term p q K i : Int) * (g j * (term p q K j : Int)) * (scale q (2 * K) : Int)
          = f i * g j * ((term p q K i : Int) * (term p q K j : Int) * (scale q (2 * K) : Int)) := by ac_rfl
        _ = f i * g j * ((choose (i + j) i : Int) * (term p q (2 * K) (i + j) : Int) * ((scale q K : Int) * scale q K)) := by
          rw [e]
        _ = _ := by ac_rfl

/-! The left-over term, summed. -/

theorem leftOver_plus (N : Nat) (f g : Nat → Int) : leftOver N (plus f g) = plus (leftOver N f) (leftOver N g) := by
  funext n; unfold leftOver; rw [conv_plus_right, conv_plus_left]; unfold plus; dsimp only; omega

theorem leftOver_times (N : Nat) (a : Int) (f : Nat → Int) : leftOver N (times a f) = times a (leftOver N f) := by
  funext n; unfold leftOver; rw [conv_times_right, conv_times_left]; unfold times; rw [Int.mul_add]

theorem leftOver_mono (N i : Nat) :
    leftOver N (mono i) = times (2 * (choose (2 * N + 1 + i) (2 * N + 1) : Int)) (mono (2 * N + 1 + i)) := by
  funext n; unfold leftOver times
  rw [conv_mono_mono, conv_mono_mono, choose_symm i (2 * N + 1), Nat.add_comm i (2 * N + 1), Int.mul_assoc]
  generalize (choose (2 * N + 1 + i) (2 * N + 1) : Int) * mono (2 * N + 1 + i) n = x
  omega

--| The left-over term's k-th part: twice the ways, at the place 2N + 2 + 2k.
def tailPart (p q K N k : Nat) : Int := 2 * ((choose (2 * N + 1 + 2 * k) (2 * N + 1) * term p q (2 * K) (2 * N + 2 + 2 * k) : Nat) : Int)

def leftOverValue (p q K N : Nat) (f : Nat → Int) : Int := ev p q (2 * K) (up (leftOver N f))

theorem tailPart_eq (p q K N k : Nat) :
    tailPart p q K N k = 2 * (choose (2 * N + 1 + 2 * k) (2 * N + 1) : Int) * (term p q (2 * K) (2 * N + 2 + 2 * k) : Int) := by
  unfold tailPart; rw [Int.natCast_mul, Int.mul_assoc]

theorem leftOverValue_of_cos (p q K N : Nat) : ∀ M, 2 * N + 2 + 2 * M ≤ 2 * K →
    leftOverValue p q K N (cosCoef M) = sumBelow (fun k => alt k * tailPart p q K N k) (M + 1)
  | 0, h => by
    unfold leftOverValue
    show ev p q (2 * K) (up (leftOver N (mono 0))) = 0 + 1 * tailPart p q K N 0
    rw [leftOver_mono, up_times, mono_up, ev_times, ev_mono _ _ _ _ (by omega), tailPart_eq,
      show 2 * N + 1 + 0 = 2 * N + 1 + 2 * 0 by omega, show 2 * N + 1 + 2 * 0 + 1 = 2 * N + 2 + 2 * 0 by omega]
    omega
  | M + 1, h => by
    unfold leftOverValue
    rw [cosCoef_succ, leftOver_plus, up_plus, ev_plus, leftOver_times, up_times, ev_times]
    have ih := leftOverValue_of_cos p q K N M (by omega)
    unfold leftOverValue at ih
    rw [ih, sumBelow_succ _ (M + 1), tailPart_eq, leftOver_mono, up_times, mono_up, ev_times, ev_mono _ _ _ _ (by omega),
      show 2 * N + 1 + (2 * M + 2) = 2 * N + 1 + 2 * (M + 1) by omega,
      show 2 * N + 1 + 2 * (M + 1) + 1 = 2 * N + 2 + 2 * (M + 1) by omega]

--| AN ALTERNATING SERIES OF FALLING TERMS IS NEVER UNDER NOTHING, AND NEVER PAST ITS FIRST TERM.
theorem alternating_falls : ∀ (N : Nat) (a : Nat → Int), (∀ k, k ≤ N → 0 ≤ a k) → (∀ k, k < N → a (k + 1) ≤ a k) →
    0 ≤ sumBelow (fun k => alt k * a k) (N + 1) ∧ sumBelow (fun k => alt k * a k) (N + 1) ≤ a 0
  | 0, a, pos, _ => by
    show 0 ≤ 0 + 1 * a 0 ∧ 0 + 1 * a 0 ≤ a 0
    have := pos 0 (Nat.le_refl 0)
    rw [Int.one_mul]; exact ⟨by omega, by omega⟩
  | N + 1, a, pos, falls => by
    have ih := alternating_falls N (fun k => a (k + 1)) (fun k hk => pos (k + 1) (by omega))
      (fun k hk => falls (k + 1) (by omega))
    dsimp only at ih
    have rest : sumBelow (fun k => alt (k + 1) * a (k + 1)) (N + 1) = - sumBelow (fun k => alt k * a (k + 1)) (N + 1) := by
      rw [← sumBelow_neg]; exact sumBelow_congr fun k _ => by rw [alt_succ, Int.neg_mul]
    rw [sumBelow_first, rest, alt_zero, Int.one_mul]
    have f0 := falls 0 (by omega)
    obtain ⟨i1, i2⟩ := ih
    exact ⟨by omega, by omega⟩

theorem tailPart_nonneg (p q K N k : Nat) : 0 ≤ tailPart p q K N k := by unfold tailPart; omega

theorem tailPart_falls (p q K N k : Nat) (hq : 0 < q) (hp : p ≤ q) (h : 2 * N + 2 + 2 * k + 2 ≤ 2 * K) :
    tailPart p q K N (k + 1) ≤ tailPart p q K N k := by
  unfold tailPart
  have r1 := choose_two_on (2 * N + 1) (2 * k)
  have r2 := term_two_on p q (2 * K) (2 * N + 2 + 2 * k) h
  rw [show 2 * N + 1 + 2 * (k + 1) = 2 * N + 1 + 2 * k + 2 by omega,
    show 2 * N + 2 + 2 * (k + 1) = 2 * N + 2 + 2 * k + 2 by omega]
  generalize choose (2 * N + 1 + 2 * k + 2) (2 * N + 1) = A at *
  generalize choose (2 * N + 1 + 2 * k) (2 * N + 1) = B at *
  generalize term p q (2 * K) (2 * N + 2 + 2 * k + 2) = T2 at *
  generalize term p q (2 * K) (2 * N + 2 + 2 * k) = T at *
  have bound : (2 * N + 1 + 2 * k + 1) * (2 * N + 1 + 2 * k + 2) * (p * p)
      ≤ ((2 * k + 1) * (2 * k + 2)) * ((2 * N + 2 + 2 * k + 1) * (2 * N + 2 + 2 * k + 2) * (q * q)) :=
    Nat.le_trans (Nat.mul_le_mul (Nat.mul_le_mul (by omega) (by omega)) (Nat.mul_le_mul hp hp))
      (Nat.le_mul_of_pos_left _ (Nat.mul_pos (by omega) (by omega)))
  have key : A * T2 * (((2 * k + 1) * (2 * k + 2)) * ((2 * N + 2 + 2 * k + 1) * (2 * N + 2 + 2 * k + 2) * (q * q)))
      = B * T * ((2 * N + 1 + 2 * k + 1) * (2 * N + 1 + 2 * k + 2) * (p * p)) := by
    calc A * T2 * (((2 * k + 1) * (2 * k + 2)) * ((2 * N + 2 + 2 * k + 1) * (2 * N + 2 + 2 * k + 2) * (q * q)))
        = (A * ((2 * k + 1) * (2 * k + 2))) * (T2 * ((2 * N + 2 + 2 * k + 1) * (2 * N + 2 + 2 * k + 2)) * (q * q)) := by
          ac_rfl
      _ = _ := by rw [r1, r2]; ac_rfl
  have le : A * T2 ≤ B * T :=
    Nat.le_of_mul_le_mul_right (Nat.le_trans (Nat.le_of_eq key) (Nat.mul_le_mul_left _ bound))
      (Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (Nat.mul_pos hq hq)))
  omega

--| THE LEFT-OVER TERM'S VALUE IS NEVER UNDER NOTHING.
theorem leftOver_is_never_under_nothing (p q K N : Nat) (hq : 0 < q) (hp : p ≤ q) (h : 4 * N + 2 ≤ 2 * K) :
    0 ≤ leftOverValue p q K N (cosCoef N) := by
  rw [leftOverValue_of_cos p q K N N (by omega)]
  exact (alternating_falls N _ (fun k _ => tailPart_nonneg p q K N k)
    (fun k hk => tailPart_falls p q K N k hq hp (by omega))).1

/-! The walls, valued. -/

--| A fraction whose value is X over D.
def Val (F : Fraction) (X : Int) (D : Nat) : Prop := (F.over : Int) * (D : Int) = X * (F.under : Int)

theorem val_congr {F : Fraction} {X Y : Int} {D : Nat} (h : Val F X D) (e : X = Y) : Val F Y D := e ▸ h

theorem val_powerTerm (p q : Nat) (hq : 0 < q) (K k : Nat) (h : k ≤ K) :
    Val (powerTerm p q hq k) (term p q K k) (scale q K) := by
  have e : p ^ k * scale q K = term p q K k * (q ^ k * factorial k) := by
    calc p ^ k * scale q K = p ^ k * (q ^ (K - k) * q ^ k) * factorial K := by
          unfold scale; rw [← Nat.pow_add, Nat.sub_add_cancel h, Nat.mul_assoc]
      _ = (p ^ k * q ^ (K - k) * factorial K) * q ^ k := by ac_rfl
      _ = term p q K k * factorial k * q ^ k := by rw [term_by_factorial _ _ _ _ h]
      _ = _ := by ac_rfl
  unfold Val
  show ((p ^ k : Nat) : Int) * (scale q K : Int) = (term p q K k : Int) * ((q ^ k * factorial k : Nat) : Int)
  rw [← Int.natCast_mul, ← Int.natCast_mul, e]

theorem val_add {a b : Fraction} {X Y : Int} {D : Nat} (ha : Val a X D) (hb : Val b Y D) : Val (a.add b) (X + Y) D := by
  unfold Val at *
  show ((a.over * b.under + b.over * a.under : Nat) : Int) * (D : Int) = (X + Y) * ((a.under * b.under : Nat) : Int)
  rw [Int.natCast_add, Int.natCast_mul, Int.natCast_mul, Int.natCast_mul]
  calc ((a.over : Int) * b.under + (b.over : Int) * a.under) * (D : Int)
      = ((a.over : Int) * D) * b.under + ((b.over : Int) * D) * a.under := by rw [Int.add_mul]; congr 1 <;> ac_rfl
    _ = X * a.under * b.under + Y * b.under * a.under := by rw [ha, hb]
    _ = _ := by rw [Int.add_mul]; congr 1 <;> ac_rfl

theorem val_sub {a b : Fraction} {X Y : Int} {D : Nat} (ba : b.le a) (ha : Val a X D) (hb : Val b Y D) :
    Val (a.sub b) (X - Y) D := by
  unfold Val at *
  show ((a.over * b.under - b.over * a.under : Nat) : Int) * (D : Int) = (X - Y) * ((a.under * b.under : Nat) : Int)
  rw [Int.ofNat_sub ba, Int.natCast_mul, Int.natCast_mul, Int.natCast_mul]
  calc ((a.over : Int) * b.under - (b.over : Int) * a.under) * (D : Int)
      = ((a.over : Int) * D) * b.under - ((b.over : Int) * D) * a.under := by rw [Int.sub_mul]; congr 1 <;> ac_rfl
    _ = X * a.under * b.under - Y * b.under * a.under := by rw [ha, hb]
    _ = _ := by rw [Int.sub_mul]; congr 1 <;> ac_rfl

theorem val_mul {a b : Fraction} {X Y : Int} {D E : Nat} (ha : Val a X D) (hb : Val b Y E) :
    Val (a.mul b) (X * Y) (D * E) := by
  unfold Val at *
  show ((a.over * b.over : Nat) : Int) * ((D * E : Nat) : Int) = X * Y * ((a.under * b.under : Nat) : Int)
  rw [Int.natCast_mul, Int.natCast_mul, Int.natCast_mul]
  calc (a.over : Int) * b.over * ((D : Int) * E) = ((a.over : Int) * D) * ((b.over : Int) * E) := by ac_rfl
    _ = X * a.under * (Y * b.under) := by rw [ha, hb]
    _ = _ := by ac_rfl

def one : Fraction := ⟨1, 1, Nat.one_pos⟩

theorem le_one_of_val {F : Fraction} {X : Int} {D : Nat} (h : Val F X D) (hD : 0 < D) (hX : X ≤ (D : Int)) :
    F.le one := by
  unfold Val at h
  show F.over * 1 ≤ 1 * F.under
  have u : (0 : Int) ≤ F.under := by omega
  have : (F.over : Int) * D ≤ (F.under : Int) * D := by
    rw [h, Int.mul_comm (F.under : Int)]; exact Int.mul_le_mul_of_nonneg_right hX u
  have := Int.le_of_mul_le_mul_right this (by omega)
  omega

theorem one_le_of_val {F : Fraction} {X : Int} {D : Nat} (h : Val F X D) (hD : 0 < D) (hX : (D : Int) ≤ X) :
    one.le F := by
  unfold Val at h
  show 1 * F.under ≤ F.over * 1
  have u : (0 : Int) ≤ F.under := by omega
  have : (F.under : Int) * D ≤ (F.over : Int) * D := by
    rw [h, Int.mul_comm (F.under : Int)]; exact Int.mul_le_mul_of_nonneg_right hX u
  have := Int.le_of_mul_le_mul_right this (by omega)
  omega

--| The low wall's value: a term less the next, summed.
def lowValue (v : Nat → Int) : Nat → Int
  | 0 => v 0 - v 1
  | m + 1 => lowValue v m + (v (2 * (m + 1)) - v (2 * (m + 1) + 1))

theorem lowValue_closed (v : Nat → Int) : ∀ m, lowValue v m = sumBelow (fun j => alt j * v j) (2 * m + 2)
  | 0 => by
    show v 0 - v 1 = 0 + alt 0 * v 0 + alt 1 * v 1
    rw [alt_zero, show alt 1 = -1 from rfl]; omega
  | m + 1 => by
    have ih := lowValue_closed v m
    have a1 : alt (2 * (m + 1)) = 1 := by unfold alt; rw [if_pos (by omega)]
    have a2 : alt (2 * (m + 1) + 1) = -1 := by unfold alt; rw [if_neg (by omega)]
    show lowValue v m + (v (2 * (m + 1)) - v (2 * (m + 1) + 1))
      = sumBelow (fun j => alt j * v j) (2 * m + 2) + alt (2 * (m + 1)) * v (2 * (m + 1))
        + alt (2 * (m + 1) + 1) * v (2 * (m + 1) + 1)
    rw [ih, a1, a2]; omega

theorem val_low (t : FallingTerms) (v : Nat → Int) (D B : Nat) (hv : ∀ j, j ≤ B → Val (t.term j) (v j) D) :
    ∀ m, 2 * m + 1 ≤ B → Val (t.bracketed.low m) (lowValue v m) D
  | 0, h => val_sub (t.falls 0) (hv 0 (by omega)) (hv 1 h)
  | m + 1, h => val_add (val_low t v D B hv m (by omega))
      (val_sub (t.falls (2 * (m + 1))) (hv _ (by omega)) (hv _ (by omega)))

theorem val_high (t : FallingTerms) (v : Nat → Int) (D B : Nat) (hv : ∀ j, j ≤ B → Val (t.term j) (v j) D)
    (m : Nat) (h : 2 * m + 2 ≤ B) : Val (t.bracketed.high m) (lowValue v m + v (2 * m + 2)) D :=
  val_add (val_low t v D B hv m (by omega)) (hv (2 * m + 2) h)

theorem ev_cos_closed (p q K : Nat) : ∀ N, 2 * N ≤ K →
    ev p q K (cosCoef N) = sumBelow (fun j => alt j * (term p q K (2 * j) : Int)) (N + 1)
  | 0, _ => by
    rw [show cosCoef 0 = mono 0 from rfl, ev_mono _ _ _ _ (Nat.zero_le _)]
    show (term p q K 0 : Int) = 0 + 1 * (term p q K 0 : Int)
    omega
  | N + 1, h => by
    rw [cosCoef_succ, ev_plus, ev_times, ev_mono _ _ _ _ (by omega), ev_cos_closed p q K N (by omega),
      show 2 * N + 2 = 2 * (N + 1) by omega]
    rfl

theorem ev_sin_closed (p q K : Nat) : ∀ N, 2 * N + 1 ≤ K →
    ev p q K (sinCoef N) = sumBelow (fun j => alt j * (term p q K (2 * j + 1) : Int)) (N + 1)
  | 0, h => by
    rw [show sinCoef 0 = mono 1 from rfl, ev_mono _ _ _ _ h]
    show (term p q K 1 : Int) = 0 + 1 * (term p q K 1 : Int)
    omega
  | N + 1, h => by
    rw [sinCoef_succ, ev_plus, ev_times, ev_mono _ _ _ _ (by omega), ev_sin_closed p q K N (by omega),
      show 2 * N + 3 = 2 * (N + 1) + 1 by omega]
    rfl

/-! The circle, at every stage. -/

theorem circle_value (p q K N : Nat) :
    ev p q (2 * K) (conv (cosCoef N) (cosCoef N)) + ev p q (2 * K) (conv (sinCoef N) (sinCoef N))
      = (scale q (2 * K) : Int) + alt N * leftOverValue p q K N (cosCoef N) := by
  rw [← ev_plus]
  show ev p q (2 * K) (circle N) = _
  rw [the_circle_on_the_coefficients, ev_plus, ev_times, ev_mono _ _ _ _ (Nat.zero_le _), term_at_nothing]
  rfl

--| THE LOW WALLS SQUARED ARE NOT PAST ONE, AT EVERY STAGE.
theorem the_low_circle_is_not_past_one (p q : Nat) (hq : 0 < q) (hp : p ≤ q) (m : Nat) :
    (theLowCircle p q hq hp m).le one := by
  have vc : Val ((cosine p q hq hp).low m) (ev p q (4 * m + 5) (cosCoef (2 * m + 1))) (scale q (4 * m + 5)) := by
    refine val_congr (val_low (theTermsOfTheCosine p q hq hp) (fun j => (term p q (4 * m + 5) (2 * j) : Int))
      (scale q (4 * m + 5)) (2 * m + 2) (fun j hj => val_powerTerm p q hq _ (2 * j) (by omega)) m (by omega)) ?_
    rw [lowValue_closed, ev_cos_closed p q _ (2 * m + 1) (by omega)]
  have vs : Val ((sine p q hq hp).low m) (ev p q (4 * m + 5) (sinCoef (2 * m + 1))) (scale q (4 * m + 5)) := by
    refine val_congr (val_low (theTermsOfTheSine p q hq hp) (fun j => (term p q (4 * m + 5) (2 * j + 1) : Int))
      (scale q (4 * m + 5)) (2 * m + 2) (fun j hj => val_powerTerm p q hq _ (2 * j + 1) (by omega)) m (by omega)) ?_
    rw [lowValue_closed, ev_sin_closed p q _ (2 * m + 1) (by omega)]
  apply le_one_of_val (val_add (val_mul vc vc) (val_mul vs vs))
    (Nat.mul_pos (scale_pos q _ hq) (scale_pos q _ hq))
  have hc := ev_product p q (4 * m + 5) (cosCoef (2 * m + 1)) (cosCoef (2 * m + 1))
    (fun n hn => cosCoef_past _ n (by omega)) (fun n hn => cosCoef_past _ n (by omega))
  have hs := ev_product p q (4 * m + 5) (sinCoef (2 * m + 1)) (sinCoef (2 * m + 1))
    (fun n hn => sinCoef_past _ n (by omega)) (fun n hn => sinCoef_past _ n (by omega))
  have sum := circle_value p q (4 * m + 5) (2 * m + 1)
  have pos := leftOver_is_never_under_nothing p q (4 * m + 5) (2 * m + 1) hq hp (by omega)
  have a : alt (2 * m + 1) = -1 := by unfold alt; rw [if_neg (by omega)]
  have S2 := scale_pos q (2 * (4 * m + 5)) hq
  have S1 := scale_pos q (4 * m + 5) hq
  apply Int.le_of_mul_le_mul_right _ (by omega : (0 : Int) < scale q (2 * (4 * m + 5)))
  rw [Int.add_mul, hc, hs, ← Int.add_mul, sum, a, Int.natCast_mul]
  have SSpos : 0 ≤ (scale q (4 * m + 5) : Int) * scale q (4 * m + 5) := Int.mul_nonneg (by omega) (by omega)
  generalize leftOverValue p q (4 * m + 5) (2 * m + 1) (cosCoef (2 * m + 1)) = L at *
  generalize (scale q (4 * m + 5) : Int) * scale q (4 * m + 5) = SS at *
  have LSS := Int.mul_nonneg pos SSpos
  generalize (scale q (2 * (4 * m + 5)) : Int) = T at *
  rw [Int.add_mul, Int.mul_assoc, Int.neg_one_mul, Int.mul_comm SS T]
  omega

--| THE HIGH WALLS SQUARED ARE NOT UNDER ONE, AT EVERY STAGE.
theorem the_high_circle_is_not_under_one (p q : Nat) (hq : 0 < q) (hp : p ≤ q) (m : Nat) :
    one.le (theHighCircle p q hq hp m) := by
  have a1 : alt (2 * m + 2) = 1 := by unfold alt; rw [if_pos (by omega)]
  have vc : Val ((cosine p q hq hp).high m) (ev p q (4 * m + 5) (cosCoef (2 * m + 2))) (scale q (4 * m + 5)) := by
    refine val_congr (val_high (theTermsOfTheCosine p q hq hp) (fun j => (term p q (4 * m + 5) (2 * j) : Int))
      (scale q (4 * m + 5)) (2 * m + 2) (fun j hj => val_powerTerm p q hq _ (2 * j) (by omega)) m (by omega)) ?_
    rw [lowValue_closed, ev_cos_closed p q _ (2 * m + 2) (by omega)]
    show sumBelow (fun j => alt j * (term p q (4 * m + 5) (2 * j) : Int)) (2 * m + 2) + (term p q (4 * m + 5) (2 * (2 * m + 2)) : Int)
      = sumBelow (fun j => alt j * (term p q (4 * m + 5) (2 * j) : Int)) (2 * m + 2)
        + alt (2 * m + 2) * (term p q (4 * m + 5) (2 * (2 * m + 2)) : Int)
    rw [a1]; omega
  have vs : Val ((sine p q hq hp).high m) (ev p q (4 * m + 5) (sinCoef (2 * m + 2))) (scale q (4 * m + 5)) := by
    refine val_congr (val_high (theTermsOfTheSine p q hq hp) (fun j => (term p q (4 * m + 5) (2 * j + 1) : Int))
      (scale q (4 * m + 5)) (2 * m + 2) (fun j hj => val_powerTerm p q hq _ (2 * j + 1) (by omega)) m (by omega)) ?_
    rw [lowValue_closed, ev_sin_closed p q _ (2 * m + 2) (by omega)]
    show sumBelow (fun j => alt j * (term p q (4 * m + 5) (2 * j + 1) : Int)) (2 * m + 2) + (term p q (4 * m + 5) (2 * (2 * m + 2) + 1) : Int)
      = sumBelow (fun j => alt j * (term p q (4 * m + 5) (2 * j + 1) : Int)) (2 * m + 2)
        + alt (2 * m + 2) * (term p q (4 * m + 5) (2 * (2 * m + 2) + 1) : Int)
    rw [a1]; omega
  apply one_le_of_val (val_add (val_mul vc vc) (val_mul vs vs))
    (Nat.mul_pos (scale_pos q _ hq) (scale_pos q _ hq))
  have hc := ev_product p q (4 * m + 5) (cosCoef (2 * m + 2)) (cosCoef (2 * m + 2))
    (fun n hn => cosCoef_past _ n (by omega)) (fun n hn => cosCoef_past _ n (by omega))
  have hs := ev_product p q (4 * m + 5) (sinCoef (2 * m + 2)) (sinCoef (2 * m + 2))
    (fun n hn => sinCoef_past _ n (by omega)) (fun n hn => sinCoef_past _ n (by omega))
  have sum := circle_value p q (4 * m + 5) (2 * m + 2)
  have pos := leftOver_is_never_under_nothing p q (4 * m + 5) (2 * m + 2) hq hp (by omega)
  have S2 := scale_pos q (2 * (4 * m + 5)) hq
  have S1 := scale_pos q (4 * m + 5) hq
  apply Int.le_of_mul_le_mul_right _ (by omega : (0 : Int) < scale q (2 * (4 * m + 5)))
  rw [Int.add_mul, hc, hs, ← Int.add_mul, sum, a1, Int.natCast_mul]
  have SSpos : 0 ≤ (scale q (4 * m + 5) : Int) * scale q (4 * m + 5) := Int.mul_nonneg (by omega) (by omega)
  generalize leftOverValue p q (4 * m + 5) (2 * m + 2) (cosCoef (2 * m + 2)) = L at *
  generalize (scale q (4 * m + 5) : Int) * scale q (4 * m + 5) = SS at *
  have LSS := Int.mul_nonneg pos SSpos
  generalize (scale q (2 * (4 * m + 5)) : Int) = T at *
  rw [Int.add_mul, Int.one_mul, Int.mul_comm SS T]
  omega

end Circle

--| THE CIRCLE.  Cosine squared beside sine squared is one, at every pair of stages, for every θ = p/q not past one.
theorem the_circle_holds_at_every_stage (p q : Nat) (hq : 0 < q) (hp : p ≤ q) :
    (((cosine p q hq hp).mul (cosine p q hq hp)).add ((sine p q hq hp).mul (sine p q hq hp))).Same (Bracketed.ofNat 1) := by
  intro n m
  constructor
  · have hc := (cosine p q hq hp).low_rises_by ((cosine p q hq hp).stageForProduct (cosine p q hq hp) (2 * n + 1))
      ((sine p q hq hp).stageForProduct (sine p q hq hp) (2 * n + 1))
    have hs := (sine p q hq hp).low_rises_by ((sine p q hq hp).stageForProduct (sine p q hq hp) (2 * n + 1))
      ((cosine p q hq hp).stageForProduct (cosine p q hq hp) (2 * n + 1))
    rw [Nat.add_comm ((sine p q hq hp).stageForProduct (sine p q hq hp) (2 * n + 1))] at hs
    exact Fraction.le_trans (Fraction.add_le_add (Fraction.mul_le_mul hc hc) (Fraction.mul_le_mul hs hs))
      (Circle.the_low_circle_is_not_past_one p q hq hp _)
  · have hc := (cosine p q hq hp).high_falls_by ((cosine p q hq hp).stageForProduct (cosine p q hq hp) (2 * m + 1))
      ((sine p q hq hp).stageForProduct (sine p q hq hp) (2 * m + 1))
    have hs := (sine p q hq hp).high_falls_by ((sine p q hq hp).stageForProduct (sine p q hq hp) (2 * m + 1))
      ((cosine p q hq hp).stageForProduct (cosine p q hq hp) (2 * m + 1))
    rw [Nat.add_comm ((sine p q hq hp).stageForProduct (sine p q hq hp) (2 * m + 1))] at hs
    exact Fraction.le_trans (Circle.the_high_circle_is_not_under_one p q hq hp _)
      (Fraction.add_le_add (Fraction.mul_le_mul hc hc) (Fraction.mul_le_mul hs hs))

end Meanings
