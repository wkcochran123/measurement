/-
The laws, with no choice.

Two reals are one when no wall of either is past a wall of the other.  That is an equivalence: every real is one with
itself, because every low wall is under every high wall; one with another both ways; and through a third, because the
third narrows: what the first is past the last by is never more than one part in any number, and Archimedes says that
is nothing.  Then the sum commutes and associates, and the product commutes, each up to being one.

Not here: the product associating, and the product spreading over the sum.
-/
import Meanings.Trigonometry
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

end Meanings
