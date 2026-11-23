/-
The laws, with no choice.

Two reals are one when no wall of either is past a wall of the other.  That is an equivalence: every real is one with
itself, because every low wall is under every high wall; one with another both ways; and through a third, because the
third narrows: what the first is past the last by is never more than one part in any number, and Archimedes says that
is nothing.  Then the sum commutes and associates, and the product commutes, each up to being one.

And the sum and the product keep being one: put a real one with another in place of it, beside or each for each, and
what comes out is one with what came out before.  The product associates, and it spreads over the sum.  Each is a law of
the walls of fractions of naturals, carried to every pair of stages because every low wall is under every high wall.
Nothing beside a real is the real, one for each of it is the real, and nothing for each of it is nothing.  So the reals
here, up to being one, are a commutative semiring, with no choice.  And a real beside both sides can be taken away: the
real beside narrows, so what is left is past by no part at all.

Then the signed reals, held and owed, at the end of this file: being one is an equivalence (through a third by taking the
third away), and beside and each for each have the laws of a commutative ring, every signed real beside itself turned over
being nothing.

Then the complex numbers, along and across: the laws of a commutative ring, up to being one.  And the quaternions, a first
and a second: the laws of a ring that is not commutative.

Not here: a reciprocal, and so division.
-/
import Meanings.Trigonometry
import Meanings.Quaternion
namespace Meanings

--| Every low wall is under every high wall.
theorem Bracketed.low_under_high (x : Bracketed) (n m : Nat) : (x.low n).le (x.high m) :=
  Fraction.le_trans (x.low_rises_by n m)
    (Fraction.le_trans (x.ordered (n + m)) (by have := x.high_falls_by m n; rwa [Nat.add_comm m n] at this))

theorem Bracketed.same_refl (x : Bracketed) : x.Same x := fun n m => ⟨x.low_under_high n m, x.low_under_high n m⟩

theorem Bracketed.same_symm {x y : Bracketed} (h : x.Same y) : y.Same x := fun n m => ⟨(h n m).2, (h n m).1⟩

--| Through a narrowing middle: if a is under the middle's high walls and the middle's low walls are under b, then a is
--| past b by no more than one part in k and one, at every k.
theorem through_the_middle (A H L B : Fraction) (K : Nat) (ah : A.le H) (lb : L.le B)
    (narrow : H.over * L.under * K ≤ L.over * H.under * K + H.under * L.under) :
    A.over * B.under * K ≤ B.over * A.under * K + A.under * B.under := by
  unfold Fraction.le at ah lb
  have hpos : 0 < H.under * L.under := Nat.mul_pos H.under_pos L.under_pos
  apply Nat.le_of_mul_le_mul_right _ hpos
  have s1 := Nat.mul_le_mul_right (B.under * L.under * K) ah
  have s2 := Nat.mul_le_mul_left (A.under * B.under) narrow
  have s3 := Nat.mul_le_mul_right (A.under * H.under * K) lb
  calc A.over * B.under * K * (H.under * L.under) = A.over * H.under * (B.under * L.under * K) := by ac_rfl
    _ ≤ H.over * A.under * (B.under * L.under * K) := s1
    _ = A.under * B.under * (H.over * L.under * K) := by ac_rfl
    _ ≤ A.under * B.under * (L.over * H.under * K + H.under * L.under) := s2
    _ = L.over * B.under * (A.under * H.under * K) + A.under * B.under * (H.under * L.under) := by
        rw [Nat.mul_add]; ac_rfl
    _ ≤ B.over * L.under * (A.under * H.under * K) + A.under * B.under * (H.under * L.under) := Nat.add_le_add_right s3 _
    _ = (B.over * A.under * K + A.under * B.under) * (H.under * L.under) := by rw [Nat.add_mul]; ac_rfl

--| ARCHIMEDES.  Past by no more than one part in every k and one is not past.
theorem not_past_by_any_part (A B : Fraction) (all : ∀ K, 0 < K → A.over * B.under * K ≤ B.over * A.under * K + A.under * B.under) :
    A.le B := by
  unfold Fraction.le
  have h := all (A.under * B.under + 1) (Nat.succ_pos _)
  apply Nat.le_of_not_lt
  intro lt
  have := Nat.mul_le_mul_right (A.under * B.under + 1) lt
  rw [Nat.succ_mul] at this
  omega

theorem Bracketed.same_trans {x y z : Bracketed} (h1 : x.Same y) (h2 : y.Same z) : x.Same z := by
  intro n m
  constructor
  · exact not_past_by_any_part _ _ fun K hK => by
      obtain ⟨k, rfl⟩ : ∃ k, K = k + 1 := ⟨K - 1, by omega⟩
      exact through_the_middle _ (y.high k) (y.low k) _ _ (h1 n k).1 (h2 k m).1 (y.narrows k)
  · exact not_past_by_any_part _ _ fun K hK => by
      obtain ⟨k, rfl⟩ : ∃ k, K = k + 1 := ⟨K - 1, by omega⟩
      exact through_the_middle _ (y.high k) (y.low k) _ _ (h2 n k).2 (h1 k m).2 (y.narrows k)

theorem Fraction.add_comm_le (a b : Fraction) : (a.add b).le (b.add a) := by
  unfold Fraction.le Fraction.add; apply Nat.le_of_eq; dsimp only; rw [Nat.add_comm (a.over * b.under)]; ac_rfl

theorem Fraction.add_regroup_back (a b c : Fraction) : (a.add (b.add c)).le ((a.add b).add c) := by
  unfold Fraction.le Fraction.add; apply Nat.le_of_eq
  simp only [Nat.add_mul]
  simp only [Nat.mul_comm, Nat.mul_left_comm]
  omega

theorem Fraction.mul_comm_le (a b : Fraction) : (a.mul b).le (b.mul a) := by
  unfold Fraction.le Fraction.mul; apply Nat.le_of_eq; dsimp only; ac_rfl

--| THE SUM COMMUTES.
theorem Bracketed.add_comm (x y : Bracketed) : (x.add y).Same (y.add x) := fun _ _ =>
  ⟨Fraction.le_trans (Fraction.add_le_add (x.low_under_high _ _) (y.low_under_high _ _)) (Fraction.add_comm_le _ _),
   Fraction.le_trans (Fraction.add_le_add (y.low_under_high _ _) (x.low_under_high _ _)) (Fraction.add_comm_le _ _)⟩

--| THE SUM ASSOCIATES.
theorem Bracketed.add_assoc (x y z : Bracketed) : ((x.add y).add z).Same (x.add (y.add z)) := fun _ _ =>
  ⟨Fraction.le_trans
    (Fraction.add_le_add (Fraction.add_le_add (x.low_under_high _ _) (y.low_under_high _ _)) (z.low_under_high _ _))
    (Fraction.add_regroup _ _ _),
   Fraction.le_trans
    (Fraction.add_le_add (x.low_under_high _ _) (Fraction.add_le_add (y.low_under_high _ _) (z.low_under_high _ _)))
    (Fraction.add_regroup_back _ _ _)⟩

--| THE PRODUCT COMMUTES.
theorem Bracketed.mul_comm (x y : Bracketed) : (x.mul y).Same (y.mul x) := fun _ _ =>
  ⟨Fraction.le_trans (Fraction.mul_le_mul (x.low_under_high _ _) (y.low_under_high _ _)) (Fraction.mul_comm_le _ _),
   Fraction.le_trans (Fraction.mul_le_mul (y.low_under_high _ _) (x.low_under_high _ _)) (Fraction.mul_comm_le _ _)⟩

--| THE SUM KEEPS BEING ONE.  Each in place of one it is one with, beside.
theorem Bracketed.add_same {x x' y y' : Bracketed} (hx : x.Same x') (hy : y.Same y') : (x.add y).Same (x'.add y') :=
  fun _ _ => ⟨Fraction.add_le_add (hx _ _).1 (hy _ _).1, Fraction.add_le_add (hx _ _).2 (hy _ _).2⟩

--| THE PRODUCT KEEPS BEING ONE.  Each in place of one it is one with, each for each.
theorem Bracketed.mul_same {x x' y y' : Bracketed} (hx : x.Same x') (hy : y.Same y') : (x.mul y).Same (x'.mul y') :=
  fun _ _ => ⟨Fraction.mul_le_mul (hx _ _).1 (hy _ _).1, Fraction.mul_le_mul (hx _ _).2 (hy _ _).2⟩

theorem Fraction.mul_regroup (a b c : Fraction) : ((a.mul b).mul c).le (a.mul (b.mul c)) := by
  unfold Fraction.le Fraction.mul; apply Nat.le_of_eq; dsimp only; ac_rfl

theorem Fraction.mul_regroup_back (a b c : Fraction) : (a.mul (b.mul c)).le ((a.mul b).mul c) := by
  unfold Fraction.le Fraction.mul; apply Nat.le_of_eq; dsimp only; ac_rfl

--| Each for a sum is the sum of each for each, and back.
theorem Fraction.spread (a b c : Fraction) : (a.mul (b.add c)).le ((a.mul b).add (a.mul c)) := by
  unfold Fraction.le Fraction.mul Fraction.add; apply Nat.le_of_eq; dsimp only
  simp only [Nat.add_mul, Nat.mul_add]
  simp only [Nat.mul_comm, Nat.mul_left_comm]

theorem Fraction.gather (a b c : Fraction) : ((a.mul b).add (a.mul c)).le (a.mul (b.add c)) := by
  unfold Fraction.le Fraction.mul Fraction.add; apply Nat.le_of_eq; dsimp only
  simp only [Nat.add_mul, Nat.mul_add]
  simp only [Nat.mul_comm, Nat.mul_left_comm]

--| THE PRODUCT ASSOCIATES.
theorem Bracketed.mul_assoc (x y z : Bracketed) : ((x.mul y).mul z).Same (x.mul (y.mul z)) := fun _ _ =>
  ⟨Fraction.le_trans
    (Fraction.mul_le_mul (Fraction.mul_le_mul (x.low_under_high _ _) (y.low_under_high _ _)) (z.low_under_high _ _))
    (Fraction.mul_regroup _ _ _),
   Fraction.le_trans
    (Fraction.mul_le_mul (x.low_under_high _ _) (Fraction.mul_le_mul (y.low_under_high _ _) (z.low_under_high _ _)))
    (Fraction.mul_regroup_back _ _ _)⟩

--| THE PRODUCT SPREADS OVER THE SUM.
theorem Bracketed.mul_add (x y z : Bracketed) : (x.mul (y.add z)).Same ((x.mul y).add (x.mul z)) := fun _ _ =>
  ⟨Fraction.le_trans (Fraction.spread _ _ _)
    (Fraction.add_le_add (Fraction.mul_le_mul (x.low_under_high _ _) (y.low_under_high _ _))
      (Fraction.mul_le_mul (x.low_under_high _ _) (z.low_under_high _ _))),
   Fraction.le_trans
    (Fraction.add_le_add (Fraction.mul_le_mul (x.low_under_high _ _) (y.low_under_high _ _))
      (Fraction.mul_le_mul (x.low_under_high _ _) (z.low_under_high _ _)))
    (Fraction.gather _ _ _)⟩

--| NOTHING AND ONE, as fractions.
theorem Fraction.zero_add_le (p : Fraction) : ((⟨0, 1, Nat.one_pos⟩ : Fraction).add p).le p := by
  unfold Fraction.le Fraction.add; apply Nat.le_of_eq; dsimp only; simp only [Nat.zero_mul, Nat.zero_add, Nat.mul_one, Nat.one_mul]

theorem Fraction.le_zero_add (p : Fraction) : p.le ((⟨0, 1, Nat.one_pos⟩ : Fraction).add p) := by
  unfold Fraction.le Fraction.add; apply Nat.le_of_eq; dsimp only; simp only [Nat.zero_mul, Nat.zero_add, Nat.mul_one, Nat.one_mul]

theorem Fraction.one_mul_le (p : Fraction) : ((⟨1, 1, Nat.one_pos⟩ : Fraction).mul p).le p := by
  unfold Fraction.le Fraction.mul; apply Nat.le_of_eq; dsimp only; simp only [Nat.one_mul]

theorem Fraction.le_one_mul (p : Fraction) : p.le ((⟨1, 1, Nat.one_pos⟩ : Fraction).mul p) := by
  unfold Fraction.le Fraction.mul; apply Nat.le_of_eq; dsimp only; simp only [Nat.one_mul]

theorem Fraction.zero_mul_le (p : Fraction) : ((⟨0, 1, Nat.one_pos⟩ : Fraction).mul p).le ⟨0, 1, Nat.one_pos⟩ := by
  unfold Fraction.le Fraction.mul; dsimp only; simp only [Nat.zero_mul, Nat.le_refl]

theorem Fraction.le_zero_mul (p : Fraction) : (⟨0, 1, Nat.one_pos⟩ : Fraction).le ((⟨0, 1, Nat.one_pos⟩ : Fraction).mul p) := by
  unfold Fraction.le Fraction.mul; dsimp only; simp only [Nat.zero_mul, Nat.le_refl]

--| NOTHING BESIDE A REAL IS THE REAL.
theorem Bracketed.zero_add (x : Bracketed) : ((Bracketed.ofNat 0).add x).Same x := fun _ _ =>
  ⟨Fraction.le_trans (Fraction.zero_add_le _) (x.low_under_high _ _),
   Fraction.le_trans (x.low_under_high _ _) (Fraction.le_zero_add _)⟩

theorem Bracketed.add_zero (x : Bracketed) : (x.add (Bracketed.ofNat 0)).Same x :=
  Bracketed.same_trans (Bracketed.add_comm _ _) (Bracketed.zero_add x)

--| ONE FOR EACH OF A REAL IS THE REAL.
theorem Bracketed.one_mul (x : Bracketed) : ((Bracketed.ofNat 1).mul x).Same x := fun _ _ =>
  ⟨Fraction.le_trans (Fraction.one_mul_le _) (x.low_under_high _ _),
   Fraction.le_trans (x.low_under_high _ _) (Fraction.le_one_mul _)⟩

--| NOTHING FOR EACH OF A REAL IS NOTHING.
theorem Bracketed.zero_mul (x : Bracketed) : ((Bracketed.ofNat 0).mul x).Same (Bracketed.ofNat 0) := fun _ _ =>
  ⟨Fraction.zero_mul_le _, Fraction.le_zero_mul _⟩

--| The product spreads over the sum from the other side.
theorem Bracketed.add_mul (x y z : Bracketed) : ((x.add y).mul z).Same ((x.mul z).add (y.mul z)) :=
  Bracketed.same_trans (Bracketed.mul_comm _ _)
    (Bracketed.same_trans (Bracketed.mul_add z x y) (Bracketed.add_same (Bracketed.mul_comm _ _) (Bracketed.mul_comm _ _)))

--| FOUR BESIDE EACH OTHER, THE MIDDLE TWO EXCHANGED.
theorem Fraction.swap_middle (a b c d : Fraction) : ((a.add b).add (c.add d)).le ((a.add c).add (b.add d)) := by
  unfold Fraction.le Fraction.add; apply Nat.le_of_eq; dsimp only
  simp only [Nat.add_mul]
  simp only [Nat.mul_comm, Nat.mul_left_comm]
  omega

theorem Bracketed.swap_middle (a b c d : Bracketed) : ((a.add b).add (c.add d)).Same ((a.add c).add (b.add d)) := fun _ _ =>
  ⟨Fraction.le_trans
    (Fraction.add_le_add (Fraction.add_le_add (a.low_under_high _ _) (b.low_under_high _ _))
      (Fraction.add_le_add (c.low_under_high _ _) (d.low_under_high _ _)))
    (Fraction.swap_middle _ _ _ _),
   Fraction.le_trans
    (Fraction.add_le_add (Fraction.add_le_add (a.low_under_high _ _) (c.low_under_high _ _))
      (Fraction.add_le_add (b.low_under_high _ _) (d.low_under_high _ _)))
    (Fraction.swap_middle _ _ _ _)⟩

--| The second and the fourth exchanged; and the first pair and the second, with the second and fourth exchanged.
theorem Bracketed.swap_second_and_fourth (a b c d : Bracketed) : ((a.add b).add (c.add d)).Same ((a.add d).add (c.add b)) :=
  Bracketed.same_trans (Bracketed.add_same (Bracketed.same_refl _) (Bracketed.add_comm c d))
    (Bracketed.same_trans (Bracketed.swap_middle a b d c) (Bracketed.add_same (Bracketed.same_refl _) (Bracketed.add_comm b c)))

theorem Bracketed.swap_first_and_third (a b c d : Bracketed) : ((a.add b).add (c.add d)).Same ((c.add b).add (a.add d)) :=
  Bracketed.same_trans (Bracketed.add_comm _ _) (Bracketed.swap_second_and_fourth c d a b)

--| A wall a stage on is never outward of the wall before it.
theorem Bracketed.low_le_of_le (x : Bracketed) {n k : Nat} (h : n ≤ k) : (x.low n).le (x.low k) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h; exact x.low_rises_by n d

theorem Bracketed.high_le_of_le (x : Bracketed) {n k : Nat} (h : n ≤ k) : (x.high k).le (x.high n) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h; exact x.high_falls_by n d

--| Past by no more than one part in more parts is past by no more than one part in fewer.
theorem fewer_parts (X Y Z K K' : Nat) (h : X * K' ≤ Y * K' + Z) (le : K ≤ K') : X * K ≤ Y * K + Z := by
  rcases Nat.le_total X Y with xy | yx
  · have := Nat.mul_le_mul_right K xy; omega
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le yx
    rw [Nat.add_mul] at h ⊢
    have := Nat.mul_le_mul_left d le
    omega

--| A beside the low wall of a narrowing real is not past B beside its high wall: so A is past B by no more than the width.
theorem cancel_by_the_width (A B L H : Fraction) (K : Nat) (h : (A.add L).le (B.add H))
    (narrow : H.over * L.under * K ≤ L.over * H.under * K + H.under * L.under) :
    A.over * B.under * K ≤ B.over * A.under * K + A.under * B.under := by
  unfold Fraction.le Fraction.add at h
  dsimp only at h
  have pos : 0 < H.under * L.under := Nat.mul_pos H.under_pos L.under_pos
  apply Nat.le_of_mul_le_mul_right _ pos
  have hK := Nat.mul_le_mul_right K h
  have nq := Nat.mul_le_mul_left (A.under * B.under) narrow
  generalize A.over = p at *
  generalize A.under = q at *
  generalize B.over = r at *
  generalize B.under = s at *
  generalize L.over = u at *
  generalize L.under = v at *
  generalize H.over = w at *
  generalize H.under = x at *
  simp only [Nat.add_mul, Nat.mul_add] at hK nq ⊢
  simp only [Nat.mul_comm, Nat.mul_left_comm] at hK nq ⊢
  omega

--| A REAL BESIDE BOTH SIDES CAN BE TAKEN AWAY.  The real beside narrows, so what is left is past by no part at all.
theorem Bracketed.add_cancel_le {a b c : Bracketed} (h : (a.add c).Same (b.add c)) (n m : Nat) : (a.low n).le (b.high m) := by
  apply not_past_by_any_part
  intro K _
  have h1 : ((a.low (2 * (n + m + K) + 1)).add (c.low (2 * (n + m + K) + 1))).le
      ((b.high (2 * (n + m + K) + 1)).add (c.high (2 * (n + m + K) + 1))) := (h (n + m + K) (n + m + K)).1
  have h2 : ((a.low n).add (c.low (2 * (n + m + K) + 1))).le ((b.high m).add (c.high (2 * (n + m + K) + 1))) :=
    Fraction.le_trans (Fraction.add_le_add (a.low_le_of_le (by omega)) (Fraction.le_refl _))
      (Fraction.le_trans h1 (Fraction.add_le_add (b.high_le_of_le (by omega)) (Fraction.le_refl _)))
  exact fewer_parts _ _ _ _ _ (cancel_by_the_width _ _ _ _ _ h2 (c.narrows _)) (by omega)

theorem Bracketed.add_cancel {a b c : Bracketed} (h : (a.add c).Same (b.add c)) : a.Same b :=
  fun n m => ⟨Bracketed.add_cancel_le h n m, Bracketed.add_cancel_le (Bracketed.same_symm h) n m⟩

/-
The signed reals: held and owed.  Two are one when the held of each beside the owed of the other are one.  That is an
equivalence, through a third because what the third holds and owes can be taken away from both sides.  Beside commutes,
associates, keeps nothing, and every signed real beside itself turned over is nothing.  Each for each commutes,
associates, keeps one, and spreads over beside; and both keep being one.  So the signed reals here, up to being one, have
the laws of a commutative ring, with no choice.
-/
namespace SignedReal

theorem same_refl (x : SignedReal) : x.Same x := Bracketed.same_refl _

theorem same_symm {x y : SignedReal} (h : x.Same y) : y.Same x := Bracketed.same_symm h

theorem same_trans {x y z : SignedReal} (h1 : x.Same y) (h2 : y.Same z) : x.Same z :=
  Bracketed.add_cancel (c := y.held.add y.owed)
    (Bracketed.same_trans (Bracketed.swap_second_and_fourth x.held z.owed y.held y.owed)
      (Bracketed.same_trans (Bracketed.add_same h1 h2) (Bracketed.swap_first_and_third y.held x.owed z.held y.owed)))

--| One part by one part: what is held is one with what is held, and what is owed with what is owed.
theorem of_parts {x y : SignedReal} (hh : x.held.Same y.held) (ho : x.owed.Same y.owed) : x.Same y :=
  Bracketed.add_same hh (Bracketed.same_symm ho)

--| BESIDE KEEPS BEING ONE.
theorem add_same {x x' y y' : SignedReal} (hx : x.Same x') (hy : y.Same y') : (x + y).Same (x' + y') :=
  Bracketed.same_trans (Bracketed.swap_middle x.held y.held x'.owed y'.owed)
    (Bracketed.same_trans (Bracketed.add_same hx hy) (Bracketed.swap_middle x'.held x.owed y'.held y.owed))

--| TURNED OVER KEEPS BEING ONE.
theorem neg_same {x y : SignedReal} (h : x.Same y) : (-x).Same (-y) :=
  Bracketed.same_trans (Bracketed.add_comm _ _) (Bracketed.same_trans (Bracketed.same_symm h) (Bracketed.add_comm _ _))

--| LESS IS BESIDE THE OTHER TURNED OVER.
theorem sub_is_add_neg (x y : SignedReal) : x - y = x + -y := rfl

--| BESIDE COMMUTES, ASSOCIATES, AND KEEPS NOTHING.
theorem add_comm (x y : SignedReal) : (x + y).Same (y + x) :=
  of_parts (Bracketed.add_comm _ _) (Bracketed.add_comm _ _)

theorem add_assoc (x y z : SignedReal) : ((x + y) + z).Same (x + (y + z)) :=
  of_parts (Bracketed.add_assoc _ _ _) (Bracketed.add_assoc _ _ _)

theorem zero_add (x : SignedReal) : (ofNat 0 + x).Same x :=
  of_parts (Bracketed.zero_add _) (Bracketed.zero_add _)

--| A SIGNED REAL BESIDE ITSELF TURNED OVER IS NOTHING.
theorem add_neg (x : SignedReal) : (x + -x).Same (ofNat 0) :=
  Bracketed.same_trans (Bracketed.add_comm _ _) (Bracketed.add_same (Bracketed.same_refl _) (Bracketed.add_comm _ _))

--| EACH FOR EACH COMMUTES.
theorem mul_comm (x y : SignedReal) : (x * y).Same (y * x) :=
  of_parts (Bracketed.add_same (Bracketed.mul_comm _ _) (Bracketed.mul_comm _ _))
    (Bracketed.same_trans (Bracketed.add_same (Bracketed.mul_comm _ _) (Bracketed.mul_comm _ _)) (Bracketed.add_comm _ _))

--| ONE FOR EACH OF A SIGNED REAL IS IT.
theorem one_and_nothing (a b : Bracketed) : (((Bracketed.ofNat 1).mul a).add ((Bracketed.ofNat 0).mul b)).Same a :=
  Bracketed.same_trans (Bracketed.add_same (Bracketed.one_mul a) (Bracketed.zero_mul b)) (Bracketed.add_zero a)

theorem one_mul (x : SignedReal) : (ofNat 1 * x).Same x :=
  of_parts (one_and_nothing _ _) (one_and_nothing _ _)

--| EACH FOR EACH SPREADS OVER BESIDE.
theorem mul_add (x y z : SignedReal) : (x * (y + z)).Same (x * y + x * z) :=
  of_parts
    (Bracketed.same_trans (Bracketed.add_same (Bracketed.mul_add _ _ _) (Bracketed.mul_add _ _ _)) (Bracketed.swap_middle _ _ _ _))
    (Bracketed.same_trans (Bracketed.add_same (Bracketed.mul_add _ _ _) (Bracketed.mul_add _ _ _)) (Bracketed.swap_middle _ _ _ _))

--| Two pairs each spread by a third, regrouped; and each for each, three deep, regrouped.
theorem spread_and_regroup (a b c d e f : Bracketed) :
    (((a.mul b).add (c.mul d)).mul e).add (((a.mul d).add (c.mul b)).mul f)
      |>.Same (((a.mul (b.mul e)).add (a.mul (d.mul f))).add ((c.mul (b.mul f)).add (c.mul (d.mul e)))) :=
  Bracketed.same_trans (Bracketed.add_same (Bracketed.add_mul _ _ _) (Bracketed.add_mul _ _ _))
    (Bracketed.same_trans
      (Bracketed.add_same (Bracketed.add_same (Bracketed.mul_assoc _ _ _) (Bracketed.mul_assoc _ _ _))
        (Bracketed.add_same (Bracketed.mul_assoc _ _ _) (Bracketed.mul_assoc _ _ _)))
      (Bracketed.same_trans (Bracketed.swap_middle _ _ _ _)
        (Bracketed.add_same (Bracketed.same_refl _) (Bracketed.add_comm _ _))))

--| EACH FOR EACH ASSOCIATES.
theorem mul_assoc (x y z : SignedReal) : ((x * y) * z).Same (x * (y * z)) :=
  of_parts
    (Bracketed.same_trans (spread_and_regroup x.held y.held x.owed y.owed z.held z.owed)
      (Bracketed.same_symm (Bracketed.add_same (Bracketed.mul_add _ _ _) (Bracketed.mul_add _ _ _))))
    (Bracketed.same_trans (spread_and_regroup x.held y.held x.owed y.owed z.owed z.held)
      (Bracketed.same_symm (Bracketed.add_same (Bracketed.mul_add _ _ _) (Bracketed.mul_add _ _ _))))

--| EACH FOR EACH KEEPS BEING ONE, on the left; then on the right, by commuting; then on both.
theorem mul_same_left {x x' : SignedReal} (hx : x.Same x') (y : SignedReal) : (x * y).Same (x' * y) :=
  Bracketed.same_trans
    (Bracketed.same_symm (Bracketed.same_trans (Bracketed.add_same (Bracketed.add_mul _ _ _) (Bracketed.add_mul _ _ _))
      (Bracketed.swap_second_and_fourth _ _ _ _)))
    (Bracketed.same_trans
      (Bracketed.add_same (Bracketed.mul_same hx (Bracketed.same_refl y.held))
        (Bracketed.mul_same (Bracketed.same_symm hx) (Bracketed.same_refl y.owed)))
      (Bracketed.same_trans (Bracketed.add_same (Bracketed.add_mul _ _ _) (Bracketed.add_mul _ _ _))
        (Bracketed.swap_second_and_fourth _ _ _ _)))

theorem mul_same_right (x : SignedReal) {y y' : SignedReal} (hy : y.Same y') : (x * y).Same (x * y') :=
  same_trans (mul_comm _ _) (same_trans (mul_same_left hy x) (mul_comm _ _))

theorem mul_same {x x' y y' : SignedReal} (hx : x.Same x') (hy : y.Same y') : (x * y).Same (x' * y') :=
  same_trans (mul_same_left hx y) (mul_same_right x' hy)

--| What the complex numbers lean on.  Nothing on the right; four beside each other regrouped; nothing for each is nothing;
--| spreading from the right; and the owed carried through each for each.
theorem add_zero (x : SignedReal) : (x + ofNat 0).Same x := same_trans (add_comm _ _) (zero_add x)

theorem swap_middle (a b c d : SignedReal) : ((a + b) + (c + d)).Same ((a + c) + (b + d)) :=
  of_parts (Bracketed.swap_middle _ _ _ _) (Bracketed.swap_middle _ _ _ _)

theorem regroup (a b c d : SignedReal) : ((a + b) + (c + d)).Same ((a + c) + (d + b)) :=
  same_trans (swap_middle a b c d) (add_same (same_refl _) (add_comm _ _))

theorem zero_mul (x : SignedReal) : (ofNat 0 * x).Same (ofNat 0) :=
  of_parts (Bracketed.same_trans (Bracketed.add_same (Bracketed.zero_mul _) (Bracketed.zero_mul _)) (Bracketed.zero_add _))
    (Bracketed.same_trans (Bracketed.add_same (Bracketed.zero_mul _) (Bracketed.zero_mul _)) (Bracketed.zero_add _))

theorem add_mul (x y z : SignedReal) : ((x + y) * z).Same (x * z + y * z) :=
  same_trans (mul_comm _ _) (same_trans (mul_add z x y) (add_same (mul_comm _ _) (mul_comm _ _)))

theorem neg_add (x y : SignedReal) : -(x + y) = -x + -y := rfl

theorem mul_neg (x y : SignedReal) : x * -y = -(x * y) := rfl

theorem neg_add_same (x y : SignedReal) : (-(x + y)).Same (-x + -y) := by rw [neg_add]; exact same_refl _

theorem neg_mul_neg (x y : SignedReal) : ((-x) * (-y)).Same (x * y) :=
  of_parts (Bracketed.add_comm _ _) (Bracketed.add_comm _ _)

theorem neg_mul (x y : SignedReal) : ((-x) * y).Same (-(x * y)) :=
  of_parts (Bracketed.add_comm _ _) (Bracketed.add_comm _ _)

theorem neg_zero : -(ofNat 0) = ofNat 0 := rfl

--| Less, written as beside the other turned over, through each for each.
theorem sub_mul (x y z : SignedReal) : ((x + -y) * z).Same (x * z + -(y * z)) :=
  same_trans (add_mul x (-y) z) (add_same (same_refl _) (neg_mul y z))

theorem mul_sub (x y z : SignedReal) : (x * (y + -z)).Same (x * y + -(x * z)) := by
  have h := mul_add x y (-z)
  rw [mul_neg] at h
  exact h

end SignedReal

/-
The complex numbers: along and across, two signed reals.  Two are one when along is one with along and across with
across.  Beside commutes, associates, keeps nothing, and a complex number beside itself turned over is nothing.  Each for
each commutes, associates, keeps one and spreads over beside; and both keep being one.  So the complex numbers here, up
to being one, have the laws of a commutative ring, with no choice.  Each for each associating is the one long step: each
side spreads into four products of three, with their signs, and the same four come out in another order.
-/
namespace ComplexReal

--| The parts of beside, turned over and each for each, read off; less written as beside the other turned over.
theorem add_along (z w : ComplexReal) : (z + w).along = z.along + w.along := rfl
theorem add_across (z w : ComplexReal) : (z + w).across = z.across + w.across := rfl
theorem neg_along (z : ComplexReal) : (-z).along = -z.along := rfl
theorem neg_across (z : ComplexReal) : (-z).across = -z.across := rfl
theorem mul_along (z w : ComplexReal) : (z * w).along = z.along * w.along + -(z.across * w.across) := rfl
theorem mul_across (z w : ComplexReal) : (z * w).across = z.along * w.across + z.across * w.along := rfl
theorem ofNat_along (k : Nat) : (ofNat k).along = SignedReal.ofNat k := rfl
theorem ofNat_across (k : Nat) : (ofNat k).across = SignedReal.ofNat 0 := rfl
theorem sub_is_add_neg (z w : ComplexReal) : z - w = z + -w := rfl

theorem same_refl (z : ComplexReal) : z.Same z := ⟨SignedReal.same_refl _, SignedReal.same_refl _⟩

theorem same_symm {z w : ComplexReal} (h : z.Same w) : w.Same z := ⟨SignedReal.same_symm h.1, SignedReal.same_symm h.2⟩

theorem same_trans {z w v : ComplexReal} (h1 : z.Same w) (h2 : w.Same v) : z.Same v :=
  ⟨SignedReal.same_trans h1.1 h2.1, SignedReal.same_trans h1.2 h2.2⟩

--| BESIDE AND TURNED OVER KEEP BEING ONE.
theorem add_same {z z' w w' : ComplexReal} (hz : z.Same z') (hw : w.Same w') : (z + w).Same (z' + w') := by
  constructor <;> simp only [add_along, add_across]
  · exact SignedReal.add_same hz.1 hw.1
  · exact SignedReal.add_same hz.2 hw.2

theorem neg_same {z w : ComplexReal} (h : z.Same w) : (-z).Same (-w) := by
  constructor <;> simp only [neg_along, neg_across]
  · exact SignedReal.neg_same h.1
  · exact SignedReal.neg_same h.2

--| EACH FOR EACH KEEPS BEING ONE.
theorem mul_same {z z' w w' : ComplexReal} (hz : z.Same z') (hw : w.Same w') : (z * w).Same (z' * w') := by
  constructor <;> simp only [mul_along, mul_across]
  · exact SignedReal.add_same (SignedReal.mul_same hz.1 hw.1) (SignedReal.neg_same (SignedReal.mul_same hz.2 hw.2))
  · exact SignedReal.add_same (SignedReal.mul_same hz.1 hw.2) (SignedReal.mul_same hz.2 hw.1)

--| BESIDE COMMUTES, ASSOCIATES, KEEPS NOTHING, AND A NUMBER BESIDE ITSELF TURNED OVER IS NOTHING.
theorem add_comm (z w : ComplexReal) : (z + w).Same (w + z) := by
  constructor <;> simp only [add_along, add_across]
  · exact SignedReal.add_comm _ _
  · exact SignedReal.add_comm _ _

theorem add_assoc (z w v : ComplexReal) : ((z + w) + v).Same (z + (w + v)) := by
  constructor <;> simp only [add_along, add_across]
  · exact SignedReal.add_assoc _ _ _
  · exact SignedReal.add_assoc _ _ _

theorem zero_add (z : ComplexReal) : (ofNat 0 + z).Same z := by
  constructor <;> simp only [add_along, add_across, ofNat_along, ofNat_across]
  · exact SignedReal.zero_add _
  · exact SignedReal.zero_add _

theorem add_neg (z : ComplexReal) : (z + -z).Same (ofNat 0) := by
  constructor <;> simp only [add_along, add_across, neg_along, neg_across, ofNat_along, ofNat_across]
  · exact SignedReal.add_neg _
  · exact SignedReal.add_neg _

--| EACH FOR EACH COMMUTES.
theorem mul_comm (z w : ComplexReal) : (z * w).Same (w * z) := by
  constructor <;> simp only [mul_along, mul_across]
  · exact SignedReal.add_same (SignedReal.mul_comm _ _) (SignedReal.neg_same (SignedReal.mul_comm _ _))
  · exact SignedReal.same_trans (SignedReal.add_same (SignedReal.mul_comm _ _) (SignedReal.mul_comm _ _)) (SignedReal.add_comm _ _)

--| ONE FOR EACH OF A COMPLEX NUMBER IS IT.
theorem one_mul (z : ComplexReal) : (ofNat 1 * z).Same z := by
  constructor <;> simp only [mul_along, mul_across, ofNat_along, ofNat_across]
  · exact SignedReal.same_trans (SignedReal.add_same (SignedReal.one_mul _) (SignedReal.neg_same (SignedReal.zero_mul _)))
      (SignedReal.add_zero _)
  · exact SignedReal.same_trans (SignedReal.add_same (SignedReal.one_mul _) (SignedReal.zero_mul _)) (SignedReal.add_zero _)

--| EACH FOR EACH SPREADS OVER BESIDE.
theorem mul_add (z w v : ComplexReal) : (z * (w + v)).Same (z * w + z * v) := by
  constructor <;> simp only [mul_along, mul_across, add_along, add_across]
  · exact SignedReal.same_trans
      (SignedReal.add_same (SignedReal.mul_add _ _ _)
        (SignedReal.same_trans (SignedReal.neg_same (SignedReal.mul_add _ _ _)) (SignedReal.neg_add_same _ _)))
      (SignedReal.swap_middle _ _ _ _)
  · exact SignedReal.same_trans (SignedReal.add_same (SignedReal.mul_add _ _ _) (SignedReal.mul_add _ _ _))
      (SignedReal.swap_middle _ _ _ _)

--| EACH FOR EACH ASSOCIATES.  Along: (ac − bd)e − (ad + bc)f and a(ce − df) − b(cf + de), four products of three each.
--| Across: (ac − bd)f + (ad + bc)e and a(cf + de) + b(ce − df).
theorem mul_assoc (z w v : ComplexReal) : ((z * w) * v).Same (z * (w * v)) := by
  obtain ⟨a, b⟩ := z
  obtain ⟨c, d⟩ := w
  obtain ⟨e, f⟩ := v
  constructor <;> simp only [mul_along, mul_across]
  · refine SignedReal.same_trans (SignedReal.add_same (SignedReal.sub_mul _ _ _)
      (SignedReal.same_trans (SignedReal.neg_same (SignedReal.add_mul _ _ _)) (SignedReal.neg_add_same _ _))) ?_
    refine SignedReal.same_trans (SignedReal.add_same
      (SignedReal.add_same (SignedReal.mul_assoc a c e) (SignedReal.neg_same (SignedReal.mul_assoc b d e)))
      (SignedReal.add_same (SignedReal.neg_same (SignedReal.mul_assoc a d f)) (SignedReal.neg_same (SignedReal.mul_assoc b c f)))) ?_
    refine SignedReal.same_trans (SignedReal.regroup _ _ _ _) ?_
    exact SignedReal.same_symm (SignedReal.add_same (SignedReal.mul_sub _ _ _)
      (SignedReal.same_trans (SignedReal.neg_same (SignedReal.mul_add _ _ _)) (SignedReal.neg_add_same _ _)))
  · refine SignedReal.same_trans (SignedReal.add_same (SignedReal.sub_mul _ _ _) (SignedReal.add_mul _ _ _)) ?_
    refine SignedReal.same_trans (SignedReal.add_same
      (SignedReal.add_same (SignedReal.mul_assoc a c f) (SignedReal.neg_same (SignedReal.mul_assoc b d f)))
      (SignedReal.add_same (SignedReal.mul_assoc a d e) (SignedReal.mul_assoc b c e))) ?_
    refine SignedReal.same_trans (SignedReal.regroup _ _ _ _) ?_
    exact SignedReal.same_symm (SignedReal.add_same (SignedReal.mul_add _ _ _) (SignedReal.mul_sub _ _ _))


--| What the quaternions lean on.  Nothing and one on the other side; spreading from the right; the owed through each for
--| each; and the conjugate, turned across the line, through beside and each for each.
instance : @Trans ComplexReal ComplexReal ComplexReal Same Same Same := ⟨same_trans⟩

theorem add_zero (z : ComplexReal) : (z + ofNat 0).Same z := same_trans (add_comm _ _) (zero_add z)

theorem mul_one (z : ComplexReal) : (z * ofNat 1).Same z := same_trans (mul_comm _ _) (one_mul z)

theorem zero_mul (z : ComplexReal) : (ofNat 0 * z).Same (ofNat 0) := by
  constructor <;> simp only [mul_along, mul_across, ofNat_along, ofNat_across]
  · exact SignedReal.same_trans (SignedReal.add_same (SignedReal.zero_mul _) (SignedReal.neg_same (SignedReal.zero_mul _)))
      (SignedReal.add_neg _)
  · exact SignedReal.same_trans (SignedReal.add_same (SignedReal.zero_mul _) (SignedReal.zero_mul _)) (SignedReal.zero_add _)

theorem mul_zero (z : ComplexReal) : (z * ofNat 0).Same (ofNat 0) := same_trans (mul_comm _ _) (zero_mul z)

theorem add_mul (z w v : ComplexReal) : ((z + w) * v).Same (z * v + w * v) :=
  same_trans (mul_comm _ _) (same_trans (mul_add v z w) (add_same (mul_comm _ _) (mul_comm _ _)))

theorem neg_add (z w : ComplexReal) : -(z + w) = -z + -w := rfl

theorem neg_add_same (z w : ComplexReal) : (-(z + w)).Same (-z + -w) := by rw [neg_add]; exact same_refl _

theorem mul_neg (z w : ComplexReal) : z * -w = -(z * w) := rfl

theorem neg_mul (z w : ComplexReal) : ((-z) * w).Same (-(z * w)) :=
  same_trans (mul_comm _ _) (by rw [mul_neg]; exact neg_same (mul_comm w z))

theorem sub_mul (z w v : ComplexReal) : ((z + -w) * v).Same (z * v + -(w * v)) :=
  same_trans (add_mul z (-w) v) (add_same (same_refl _) (neg_mul w v))

theorem mul_sub (z w v : ComplexReal) : (z * (w + -v)).Same (z * w + -(z * v)) := by
  have h := mul_add z w (-v)
  rw [mul_neg] at h
  exact h

theorem swap_middle (a b c d : ComplexReal) : ((a + b) + (c + d)).Same ((a + c) + (b + d)) :=
  ⟨SignedReal.swap_middle _ _ _ _, SignedReal.swap_middle _ _ _ _⟩

theorem regroup (a b c d : ComplexReal) : ((a + b) + (c + d)).Same ((a + c) + (d + b)) :=
  same_trans (swap_middle a b c d) (add_same (same_refl _) (add_comm _ _))

--| Three each for each, the last two exchanged.
theorem swap_last (x y z : ComplexReal) : (x * y * z).Same (x * z * y) :=
  same_trans (mul_assoc _ _ _) (same_trans (mul_same (same_refl _) (mul_comm _ _)) (same_symm (mul_assoc _ _ _)))

theorem conjugate_along (z : ComplexReal) : z.conjugate.along = z.along := rfl
theorem conjugate_across (z : ComplexReal) : z.conjugate.across = -z.across := rfl
theorem conjugate_add (z w : ComplexReal) : (z + w).conjugate = z.conjugate + w.conjugate := rfl
theorem conjugate_neg (z : ComplexReal) : (-z).conjugate = -z.conjugate := rfl
theorem conjugate_conjugate (z : ComplexReal) : z.conjugate.conjugate = z := rfl
theorem conjugate_zero : (ofNat 0).conjugate = ofNat 0 := rfl
theorem conjugate_one : (ofNat 1).conjugate = ofNat 1 := rfl

--| THE CONJUGATE KEEPS BEING ONE, AND GOES THROUGH EACH FOR EACH.
theorem conjugate_same {z w : ComplexReal} (h : z.Same w) : z.conjugate.Same w.conjugate := ⟨h.1, SignedReal.neg_same h.2⟩

theorem conjugate_mul (z w : ComplexReal) : (z * w).conjugate.Same (z.conjugate * w.conjugate) := by
  constructor <;> simp only [conjugate_along, conjugate_across, mul_along, mul_across, SignedReal.mul_neg]
  · exact SignedReal.add_same (SignedReal.same_refl _) (SignedReal.neg_same (SignedReal.same_symm (SignedReal.neg_mul_neg _ _)))
  · exact SignedReal.same_trans (SignedReal.neg_add_same _ _)
      (SignedReal.add_same (SignedReal.same_refl _) (SignedReal.same_symm (SignedReal.neg_mul _ _)))

theorem conjugate_mul_conjugate (z w : ComplexReal) : (z * w.conjugate).conjugate.Same (z.conjugate * w) := by
  have h := conjugate_mul z w.conjugate
  rw [conjugate_conjugate] at h
  exact h

theorem conjugate_conjugate_mul (z w : ComplexReal) : (z.conjugate * w).conjugate.Same (z * w.conjugate) := by
  have h := conjugate_mul z.conjugate w
  rw [conjugate_conjugate] at h
  exact h

end ComplexReal


local infix:50 " ≋ " => ComplexReal.Same

/-
The quaternions: a first and a second complex number, doubled the way the complex numbers doubled the signed reals.  Two
are one when first is one with first and second with second.  Beside commutes, associates, keeps nothing, and a
quaternion beside itself turned over is nothing.  Each for each keeps one on either side, spreads over beside on either
side, and associates; and both keep being one.  It does not commute (`i_by_j_is_not_j_by_i`).  So the quaternions here,
up to being one, have the laws of a ring that is not commutative, with no choice.  Associating is the long step again:
each side's first and second spread into four products of three complex numbers, some turned across the line, and since
the complex numbers commute the same four come out in another order.
-/
namespace QuaternionReal

theorem first_add (p q : QuaternionReal) : (p + q).first = p.first + q.first := rfl
theorem second_add (p q : QuaternionReal) : (p + q).second = p.second + q.second := rfl
theorem first_neg (p : QuaternionReal) : (-p).first = -p.first := rfl
theorem second_neg (p : QuaternionReal) : (-p).second = -p.second := rfl
theorem first_mul (p q : QuaternionReal) : (p * q).first = p.first * q.first + -(q.second.conjugate * p.second) := rfl
theorem second_mul (p q : QuaternionReal) : (p * q).second = q.second * p.first + p.second * q.first.conjugate := rfl
theorem first_ofNat (k : Nat) : (ofNat k).first = ComplexReal.ofNat k := rfl
theorem second_ofNat (k : Nat) : (ofNat k).second = ComplexReal.ofNat 0 := rfl
theorem sub_is_add_neg (p q : QuaternionReal) : p - q = p + -q := rfl

theorem same_refl (p : QuaternionReal) : p.Same p := ⟨ComplexReal.same_refl _, ComplexReal.same_refl _⟩

theorem same_symm {p q : QuaternionReal} (h : p.Same q) : q.Same p := ⟨ComplexReal.same_symm h.1, ComplexReal.same_symm h.2⟩

theorem same_trans {p q r : QuaternionReal} (h1 : p.Same q) (h2 : q.Same r) : p.Same r :=
  ⟨ComplexReal.same_trans h1.1 h2.1, ComplexReal.same_trans h1.2 h2.2⟩

--| BESIDE AND TURNED OVER KEEP BEING ONE.
theorem add_same {p p' q q' : QuaternionReal} (hp : p.Same p') (hq : q.Same q') : (p + q).Same (p' + q') := by
  constructor <;> simp only [first_add, second_add]
  · exact ComplexReal.add_same hp.1 hq.1
  · exact ComplexReal.add_same hp.2 hq.2

theorem neg_same {p q : QuaternionReal} (h : p.Same q) : (-p).Same (-q) := by
  constructor <;> simp only [first_neg, second_neg]
  · exact ComplexReal.neg_same h.1
  · exact ComplexReal.neg_same h.2

--| EACH FOR EACH KEEPS BEING ONE.
theorem mul_same {p p' q q' : QuaternionReal} (hp : p.Same p') (hq : q.Same q') : (p * q).Same (p' * q') := by
  constructor <;> simp only [first_mul, second_mul]
  · exact ComplexReal.add_same (ComplexReal.mul_same hp.1 hq.1)
      (ComplexReal.neg_same (ComplexReal.mul_same (ComplexReal.conjugate_same hq.2) hp.2))
  · exact ComplexReal.add_same (ComplexReal.mul_same hq.2 hp.1) (ComplexReal.mul_same hp.2 (ComplexReal.conjugate_same hq.1))

--| BESIDE COMMUTES, ASSOCIATES, KEEPS NOTHING, AND A QUATERNION BESIDE ITSELF TURNED OVER IS NOTHING.
theorem add_comm (p q : QuaternionReal) : (p + q).Same (q + p) := by
  constructor <;> simp only [first_add, second_add]
  · exact ComplexReal.add_comm _ _
  · exact ComplexReal.add_comm _ _

theorem add_assoc (p q r : QuaternionReal) : ((p + q) + r).Same (p + (q + r)) := by
  constructor <;> simp only [first_add, second_add]
  · exact ComplexReal.add_assoc _ _ _
  · exact ComplexReal.add_assoc _ _ _

theorem zero_add (p : QuaternionReal) : (ofNat 0 + p).Same p := by
  constructor <;> simp only [first_add, second_add, first_ofNat, second_ofNat]
  · exact ComplexReal.zero_add _
  · exact ComplexReal.zero_add _

theorem add_neg (p : QuaternionReal) : (p + -p).Same (ofNat 0) := by
  constructor <;> simp only [first_add, second_add, first_neg, second_neg, first_ofNat, second_ofNat]
  · exact ComplexReal.add_neg _
  · exact ComplexReal.add_neg _

--| ONE FOR EACH, ON EITHER SIDE, IS THE QUATERNION.
theorem one_mul (q : QuaternionReal) : (ofNat 1 * q).Same q := by
  constructor <;> simp only [first_mul, second_mul, first_ofNat, second_ofNat]
  · exact ComplexReal.same_trans
      (ComplexReal.add_same (ComplexReal.one_mul q.first) (ComplexReal.neg_same (ComplexReal.mul_zero q.second.conjugate)))
      (ComplexReal.add_zero q.first)
  · exact ComplexReal.same_trans
      (ComplexReal.add_same (ComplexReal.mul_one q.second) (ComplexReal.zero_mul q.first.conjugate))
      (ComplexReal.add_zero q.second)

theorem mul_one (p : QuaternionReal) : (p * ofNat 1).Same p := by
  constructor <;> simp only [first_mul, second_mul, first_ofNat, second_ofNat, ComplexReal.conjugate_zero,
    ComplexReal.conjugate_one]
  · exact ComplexReal.same_trans
      (ComplexReal.add_same (ComplexReal.mul_one p.first) (ComplexReal.neg_same (ComplexReal.zero_mul p.second)))
      (ComplexReal.add_zero p.first)
  · exact ComplexReal.same_trans
      (ComplexReal.add_same (ComplexReal.zero_mul p.first) (ComplexReal.mul_one p.second))
      (ComplexReal.zero_add p.second)

--| EACH FOR EACH SPREADS OVER BESIDE, ON EITHER SIDE.
theorem mul_add (p q r : QuaternionReal) : (p * (q + r)).Same (p * q + p * r) := by
  constructor <;> simp only [first_mul, second_mul, first_add, second_add, ComplexReal.conjugate_add]
  · exact ComplexReal.same_trans
      (ComplexReal.add_same (ComplexReal.mul_add _ _ _)
        (ComplexReal.same_trans (ComplexReal.neg_same (ComplexReal.add_mul _ _ _)) (ComplexReal.neg_add_same _ _)))
      (ComplexReal.swap_middle _ _ _ _)
  · exact ComplexReal.same_trans (ComplexReal.add_same (ComplexReal.add_mul _ _ _) (ComplexReal.mul_add _ _ _))
      (ComplexReal.swap_middle _ _ _ _)

theorem add_mul (p q r : QuaternionReal) : ((p + q) * r).Same (p * r + q * r) := by
  constructor <;> simp only [first_mul, second_mul, first_add, second_add]
  · exact ComplexReal.same_trans
      (ComplexReal.add_same (ComplexReal.add_mul _ _ _)
        (ComplexReal.same_trans (ComplexReal.neg_same (ComplexReal.mul_add _ _ _)) (ComplexReal.neg_add_same _ _)))
      (ComplexReal.swap_middle _ _ _ _)
  · exact ComplexReal.same_trans (ComplexReal.add_same (ComplexReal.mul_add _ _ _) (ComplexReal.add_mul _ _ _))
      (ComplexReal.swap_middle _ _ _ _)

--| EACH FOR EACH ASSOCIATES.  With p = (a, b), q = (c, d), r = (e, f) and a bar for the conjugate:
--| first: (ac − d̄b)e − f̄(da + bc̄) and a(ce − f̄d) − (fc + dē)‾b;
--| second: f(ac − d̄b) + (da + bc̄)ē and (fc + dē)a + b(ce − f̄d)‾.
theorem mul_assoc (p q r : QuaternionReal) : ((p * q) * r).Same (p * (q * r)) := by
  obtain ⟨a, b⟩ := p
  obtain ⟨c, d⟩ := q
  obtain ⟨e, f⟩ := r
  constructor
  · show (a * c + -(d.conjugate * b)) * e + -(f.conjugate * (d * a + b * c.conjugate))
        ≋ a * (c * e + -(f.conjugate * d)) + -(((f * c).conjugate + (d * e.conjugate).conjugate) * b)
    calc (a * c + -(d.conjugate * b)) * e + -(f.conjugate * (d * a + b * c.conjugate))
        ≋ (a * c * e + -(d.conjugate * b * e)) + (-(f.conjugate * (d * a)) + -(f.conjugate * (b * c.conjugate))) :=
          ComplexReal.add_same (ComplexReal.sub_mul _ _ _) (ComplexReal.same_trans (ComplexReal.neg_same (ComplexReal.mul_add _ _ _)) (ComplexReal.neg_add_same _ _))
      _ ≋ (a * (c * e) + -(d.conjugate * e * b)) + (-(a * (f.conjugate * d)) + -(f.conjugate * c.conjugate * b)) :=
          ComplexReal.add_same (ComplexReal.add_same (ComplexReal.mul_assoc _ _ _) (ComplexReal.neg_same (ComplexReal.swap_last _ _ _)))
            (ComplexReal.add_same (ComplexReal.neg_same (ComplexReal.same_trans (ComplexReal.same_symm (ComplexReal.mul_assoc _ _ _)) (ComplexReal.mul_comm _ _)))
              (ComplexReal.neg_same (ComplexReal.same_trans (ComplexReal.mul_same (ComplexReal.same_refl _) (ComplexReal.mul_comm _ _)) (ComplexReal.same_symm (ComplexReal.mul_assoc _ _ _)))))
      _ ≋ (a * (c * e) + -(a * (f.conjugate * d))) + (-(f.conjugate * c.conjugate * b) + -(d.conjugate * e * b)) :=
          ComplexReal.regroup _ _ _ _
      _ ≋ a * (c * e + -(f.conjugate * d)) + -(((f * c).conjugate + (d * e.conjugate).conjugate) * b) :=
          ComplexReal.same_symm (ComplexReal.add_same (ComplexReal.mul_sub _ _ _)
            (ComplexReal.same_trans (ComplexReal.neg_same (ComplexReal.add_mul _ _ _)) (ComplexReal.same_trans (ComplexReal.neg_add_same _ _)
              (ComplexReal.add_same (ComplexReal.neg_same (ComplexReal.mul_same (ComplexReal.conjugate_mul f c) (ComplexReal.same_refl b)))
                (ComplexReal.neg_same (ComplexReal.mul_same (ComplexReal.conjugate_mul_conjugate d e) (ComplexReal.same_refl b)))))))
  · show f * (a * c + -(d.conjugate * b)) + (d * a + b * c.conjugate) * e.conjugate
        ≋ (f * c + d * e.conjugate) * a + b * ((c * e).conjugate + -((f.conjugate * d).conjugate))
    calc f * (a * c + -(d.conjugate * b)) + (d * a + b * c.conjugate) * e.conjugate
        ≋ (f * (a * c) + -(f * (d.conjugate * b))) + (d * a * e.conjugate + b * c.conjugate * e.conjugate) :=
          ComplexReal.add_same (ComplexReal.mul_sub _ _ _) (ComplexReal.add_mul _ _ _)
      _ ≋ (f * c * a + -(b * (f * d.conjugate))) + (d * e.conjugate * a + b * (c.conjugate * e.conjugate)) :=
          ComplexReal.add_same
            (ComplexReal.add_same (ComplexReal.same_trans (ComplexReal.mul_same (ComplexReal.same_refl _) (ComplexReal.mul_comm _ _)) (ComplexReal.same_symm (ComplexReal.mul_assoc _ _ _)))
              (ComplexReal.neg_same (ComplexReal.same_trans (ComplexReal.same_symm (ComplexReal.mul_assoc _ _ _)) (ComplexReal.mul_comm _ _))))
            (ComplexReal.add_same (ComplexReal.swap_last _ _ _) (ComplexReal.mul_assoc _ _ _))
      _ ≋ (f * c * a + d * e.conjugate * a) + (b * (c.conjugate * e.conjugate) + -(b * (f * d.conjugate))) :=
          ComplexReal.regroup _ _ _ _
      _ ≋ (f * c + d * e.conjugate) * a + b * ((c * e).conjugate + -((f.conjugate * d).conjugate)) :=
          ComplexReal.same_symm (ComplexReal.add_same (ComplexReal.add_mul _ _ _)
            (ComplexReal.same_trans (ComplexReal.mul_sub _ _ _)
              (ComplexReal.add_same (ComplexReal.mul_same (ComplexReal.same_refl b) (ComplexReal.conjugate_mul c e))
                (ComplexReal.neg_same (ComplexReal.mul_same (ComplexReal.same_refl b) (ComplexReal.conjugate_conjugate_mul f d))))))

end QuaternionReal


end Meanings
