/-
The reciprocal, with no choice.

One over a real is one over its walls, the low wall over the high and the high over the low.  That needs a wall that is
past nothing, and a real does not say of itself that it is apart from nothing: being past nothing shows at a finite stage,
and no finite stage shows that a real is nothing.  So the reciprocal is handed the stage where the low wall is past
nothing.  From there every wall is past nothing, and one over them is a real: the walls are read as far on as the stage
and the square of the low wall's under, n and one times over, so that the width, which one over divides by the walls
twice, is still no more than one part in n and one.

A real by one over itself is one; one over keeps being one, whichever stage was handed in; and a real over another is the
first by one over the second.  Given only that some stage shows the low wall past nothing, the least such stage is found
by looking, with the click, and nothing bills choice.

Not here: one over a signed, complex or quaternion number.  Those want the difference of two reals as a real, held past
owed at a stage, and that is not yet written.
-/
import Meanings.Laws
import Meanings.Continuity

namespace Meanings

--| A wall not under one that is past nothing is past nothing.
theorem Fraction.past_nothing_of_le {p q : Fraction} (h : p.le q) (hp : 0 < p.over) : 0 < q.over := by
  unfold Fraction.le at h
  rcases Nat.eq_zero_or_pos q.over with hq | hq
  · rw [hq, Nat.zero_mul] at h
    have := Nat.mul_pos hp q.under_pos
    omega
  · exact hq

--| ONE OVER A FRACTION PAST NOTHING: the under over the over.
def Fraction.recip (p : Fraction) (hp : 0 < p.over) : Fraction := ⟨p.under, p.over, hp⟩

--| One over turns the order over.
theorem Fraction.recip_le_recip {p q : Fraction} (hp : 0 < p.over) (hq : 0 < q.over) (h : p.le q) :
    (q.recip hq).le (p.recip hp) := by
  unfold Fraction.le Fraction.recip at *
  dsimp only
  rw [Nat.mul_comm q.under, Nat.mul_comm p.under]
  exact h

--| From the stage handed in, every wall is past nothing.
theorem Bracketed.low_pos (x : Bracketed) (k : Nat) (pos : 0 < (x.low k).over) {s : Nat} (hs : k ≤ s) :
    0 < (x.low s).over :=
  Fraction.past_nothing_of_le (x.low_le_of_le hs) pos

theorem Bracketed.high_pos (x : Bracketed) (k : Nat) (pos : 0 < (x.low k).over) {s : Nat} (hs : k ≤ s) :
    0 < (x.high s).over :=
  Fraction.past_nothing_of_le (x.ordered s) (x.low_pos k pos hs)

--| How far on one over reads: the stage handed in, and n and one times the low wall's under squared.
def Bracketed.reciprocalStage (x : Bracketed) (k n : Nat) : Nat := k + (n + 1) * ((x.low k).under * (x.low k).under)

theorem Bracketed.reciprocalStage_past (x : Bracketed) (k n : Nat) : k ≤ x.reciprocalStage k n := Nat.le_add_right _ _

theorem Bracketed.reciprocalStage_rises (x : Bracketed) (k n : Nat) : x.reciprocalStage k n ≤ x.reciprocalStage k (n + 1) := by
  unfold Bracketed.reciprocalStage
  rw [Nat.succ_mul (n + 1)]
  omega

theorem Bracketed.reciprocalStage_big (x : Bracketed) (k n : Nat) :
    (n + 1) * ((x.low k).under * (x.low k).under) ≤ x.reciprocalStage k n + 1 := by
  unfold Bracketed.reciprocalStage
  omega

--| THE WIDTH OF ONE OVER.  With the walls a over b and c over d, both not under p over q: what one over divides the width
--| by is the walls' product, never under p squared over q squared, so reading q squared times as far on pays for it.
theorem the_reciprocal_narrows (a b c d p q s N : Nat)
    (narrow : c * b * (s + 1) ≤ a * d * (s + 1) + d * b)
    (pl : p * b ≤ a * q) (ph : p * d ≤ c * q) (pp : 0 < p) (qpos : 0 < q)
    (big : N * (q * q) ≤ s + 1) :
    b * c * N ≤ d * a * N + a * c := by
  rcases Nat.le_total (c * b) (a * d) with h | h
  · have m := Nat.mul_le_mul_right N h
    calc b * c * N = c * b * N := by rw [Nat.mul_comm b c]
      _ ≤ a * d * N := m
      _ = d * a * N := by rw [Nat.mul_comm a d]
      _ ≤ d * a * N + a * c := Nat.le_add_right _ _
  · obtain ⟨w, hw⟩ := Nat.exists_eq_add_of_le h
    have w1 : w * (s + 1) ≤ d * b := by
      rw [hw, Nat.add_mul] at narrow
      omega
    have w2 : w * N * (q * q) ≤ a * c * (q * q) :=
      calc w * N * (q * q) = w * (N * (q * q)) := Nat.mul_assoc _ _ _
        _ ≤ w * (s + 1) := Nat.mul_le_mul_left _ big
        _ ≤ d * b := w1
        _ ≤ (p * p) * (d * b) := Nat.le_mul_of_pos_left _ (Nat.mul_pos pp pp)
        _ = (p * b) * (p * d) := by ac_rfl
        _ ≤ (a * q) * (c * q) := Nat.mul_le_mul pl ph
        _ = a * c * (q * q) := by ac_rfl
    have w3 : w * N ≤ a * c := Nat.le_of_mul_le_mul_right w2 (Nat.mul_pos qpos qpos)
    have bc : b * c = a * d + w := by rw [Nat.mul_comm b c]; exact hw
    rw [bc, Nat.add_mul, Nat.mul_comm d a]
    omega

--| ONE OVER A REAL, from a stage where its low wall is past nothing.
def Bracketed.reciprocal (x : Bracketed) (k : Nat) (pos : 0 < (x.low k).over) : Bracketed where
  low n := (x.high (x.reciprocalStage k n)).recip (x.high_pos k pos (x.reciprocalStage_past k n))
  high n := (x.low (x.reciprocalStage k n)).recip (x.low_pos k pos (x.reciprocalStage_past k n))
  ordered _ := Fraction.recip_le_recip _ _ (x.ordered _)
  low_rises n := Fraction.recip_le_recip _ _ (x.high_le_of_le (x.reciprocalStage_rises k n))
  high_falls n := Fraction.recip_le_recip _ _ (x.low_le_of_le (x.reciprocalStage_rises k n))
  narrows n :=
    the_reciprocal_narrows _ _ _ _ _ _ _ (n + 1) (x.narrows _)
      (x.low_le_of_le (x.reciprocalStage_past k n))
      (Fraction.le_trans (x.low_le_of_le (x.reciprocalStage_past k n)) (x.ordered _))
      pos (x.low k).under_pos (x.reciprocalStage_big k n)

--| Every wall of one over is inside one over the walls at the stage handed in.
theorem Bracketed.reciprocal_low_is_past (x : Bracketed) (k : Nat) (pos : 0 < (x.low k).over) (n : Nat) :
    ((x.high k).recip (x.high_pos k pos (Nat.le_refl k))).le ((x.reciprocal k pos).low n) :=
  Fraction.recip_le_recip _ _ (x.high_le_of_le (x.reciprocalStage_past k n))

theorem Bracketed.reciprocal_high_is_under (x : Bracketed) (k : Nat) (pos : 0 < (x.low k).over) (n : Nat) :
    ((x.reciprocal k pos).high n).le ((x.low k).recip pos) :=
  Fraction.recip_le_recip _ _ (x.low_le_of_le (x.reciprocalStage_past k n))

--| A fraction by one over a fraction not under it is not past one; by one over a fraction not past it, not under one.
theorem Fraction.mul_recip_le_one {p q : Fraction} (hq : 0 < q.over) (h : p.le q) :
    (p.mul (q.recip hq)).le ⟨1, 1, Nat.one_pos⟩ := by
  unfold Fraction.le Fraction.mul Fraction.recip at *
  dsimp only
  rw [Nat.mul_one, Nat.one_mul, Nat.mul_comm p.under]
  exact h

theorem Fraction.one_le_mul_recip {p q : Fraction} (hq : 0 < q.over) (h : q.le p) :
    (⟨1, 1, Nat.one_pos⟩ : Fraction).le (p.mul (q.recip hq)) := by
  unfold Fraction.le Fraction.mul Fraction.recip at *
  dsimp only
  rw [Nat.mul_one, Nat.one_mul, Nat.mul_comm p.under]
  exact h

--| A REAL BY ONE OVER ITSELF IS ONE.
theorem Bracketed.mul_reciprocal (x : Bracketed) (k : Nat) (pos : 0 < (x.low k).over) :
    (x.mul (x.reciprocal k pos)).Same (Bracketed.ofNat 1) := fun _ _ =>
  ⟨Fraction.mul_recip_le_one _ (x.low_under_high _ _), Fraction.one_le_mul_recip _ (x.low_under_high _ _)⟩

theorem Bracketed.reciprocal_mul (x : Bracketed) (k : Nat) (pos : 0 < (x.low k).over) :
    ((x.reciprocal k pos).mul x).Same (Bracketed.ofNat 1) :=
  Bracketed.same_trans (Bracketed.mul_comm _ _) (x.mul_reciprocal k pos)

--| ONE OVER KEEPS BEING ONE, whichever stages were handed in.
theorem Bracketed.reciprocal_same {x y : Bracketed} {k k' : Nat} {pos : 0 < (x.low k).over} {pos' : 0 < (y.low k').over}
    (h : x.Same y) : (x.reciprocal k pos).Same (y.reciprocal k' pos') := fun _ _ =>
  ⟨Fraction.recip_le_recip _ _ (h _ _).2, Fraction.recip_le_recip _ _ (h _ _).1⟩

theorem Bracketed.mul_one (x : Bracketed) : (x.mul (Bracketed.ofNat 1)).Same x :=
  Bracketed.same_trans (Bracketed.mul_comm _ _) (Bracketed.one_mul x)

--| OVER.  A real over another is the first by one over the second; and by the second again it is the first.
def Bracketed.div (x y : Bracketed) (k : Nat) (pos : 0 < (y.low k).over) : Bracketed := x.mul (y.reciprocal k pos)

theorem Bracketed.div_mul (x y : Bracketed) (k : Nat) (pos : 0 < (y.low k).over) : ((x.div y k pos).mul y).Same x :=
  Bracketed.same_trans (Bracketed.mul_assoc _ _ _)
    (Bracketed.same_trans (Bracketed.mul_same (Bracketed.same_refl x) (y.reciprocal_mul k pos)) (Bracketed.mul_one x))

--| FOUND BY LOOKING.  Handed only that some stage shows the low wall past nothing, the least such stage, with the click.
def Bracketed.reciprocalFound (x : Bracketed) (apart : ∃ k, 0 < (x.low k).over) : Bracketed :=
  x.reciprocal (findByLooking (fun k => 0 < (x.low k).over) apart).1 (findByLooking (fun k => 0 < (x.low k).over) apart).2.1

theorem Bracketed.mul_reciprocalFound (x : Bracketed) (apart : ∃ k, 0 < (x.low k).over) :
    (x.mul (x.reciprocalFound apart)).Same (Bracketed.ofNat 1) :=
  x.mul_reciprocal _ _

end Meanings
