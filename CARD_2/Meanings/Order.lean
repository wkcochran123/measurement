/-
The order, with no choice.

One real is not past another when no low wall of the one is past a high wall of the other.  That is half of being one:
two reals are one exactly when each is not past the other.  It is reflexive, and transitive through the middle real's
narrowing, by Archimedes, as being one is.  Beside keeps it, and each for each keeps it, every real here being never under
nothing; and a real beside both sides can be taken away from it.

A signed real is not past another when what the first holds beside what the second owes is not past what the second holds
beside what the first owes.  It is reflexive and transitive, the middle taken away from both sides; two signed reals each
not past the other are one; being one keeps it; and beside keeps it.

A product of two signed reals not under nothing is not under nothing: crossing never gains.

What is not here, and cannot be without a click: that of two reals one is not past the other.  Whether a real is past
another shows at a finite stage; that it is not past shows at no finite stage.  So the order is not total here, and the
reader who wants it total is handed the comparison, or chooses.
-/
import Meanings.Difference

namespace Meanings

--| NOT PAST.
def Bracketed.NotPast (a b : Bracketed) : Prop := ∀ n m, (a.low n).le (b.high m)

theorem Bracketed.notPast_refl (a : Bracketed) : a.NotPast a := a.low_under_high

theorem Bracketed.notPast_trans {a b c : Bracketed} (h1 : a.NotPast b) (h2 : b.NotPast c) : a.NotPast c := fun n m =>
  not_past_by_any_part _ _ fun K hK => by
    obtain ⟨k, rfl⟩ : ∃ k, K = k + 1 := ⟨K - 1, by omega⟩
    exact through_the_middle _ (b.high k) (b.low k) _ _ (h1 n k) (h2 k m) (b.narrows k)

--| Being one is being not past both ways.
theorem Bracketed.notPast_of_same {a b : Bracketed} (h : a.Same b) : a.NotPast b := fun n m => (h n m).1

theorem Bracketed.same_of_notPast {a b : Bracketed} (h1 : a.NotPast b) (h2 : b.NotPast a) : a.Same b :=
  fun n m => ⟨h1 n m, h2 n m⟩

--| Every real is not under nothing.
theorem Bracketed.zero_notPast (a : Bracketed) : (Bracketed.ofNat 0).NotPast a := fun _ _ => by
  show 0 * (a.high _).under ≤ (a.high _).over * 1
  rw [Nat.zero_mul]; exact Nat.zero_le _

--| BESIDE AND EACH FOR EACH KEEP IT.
theorem Bracketed.add_notPast {a a' b b' : Bracketed} (ha : a.NotPast a') (hb : b.NotPast b') :
    (a.add b).NotPast (a'.add b') := fun _ _ => Fraction.add_le_add (ha _ _) (hb _ _)

theorem Bracketed.mul_notPast {a a' b b' : Bracketed} (ha : a.NotPast a') (hb : b.NotPast b') :
    (a.mul b).NotPast (a'.mul b') := fun _ _ => Fraction.mul_le_mul (ha _ _) (hb _ _)

--| A REAL BESIDE BOTH SIDES CAN BE TAKEN AWAY.
theorem Bracketed.add_cancel_notPast {a b c : Bracketed} (h : (a.add c).NotPast (b.add c)) : a.NotPast b := by
  intro n m
  apply not_past_by_any_part
  intro K _
  have h1 : ((a.low (2 * (n + m + K) + 1)).add (c.low (2 * (n + m + K) + 1))).le
      ((b.high (2 * (n + m + K) + 1)).add (c.high (2 * (n + m + K) + 1))) := h (n + m + K) (n + m + K)
  have h2 : ((a.low n).add (c.low (2 * (n + m + K) + 1))).le ((b.high m).add (c.high (2 * (n + m + K) + 1))) :=
    Fraction.le_trans (Fraction.add_le_add (a.low_le_of_le (by omega)) (Fraction.le_refl _))
      (Fraction.le_trans h1 (Fraction.add_le_add (b.high_le_of_le (by omega)) (Fraction.le_refl _)))
  exact fewer_parts _ _ _ _ _ (cancel_by_the_width _ _ _ _ _ h2 (c.narrows _)) (by omega)

namespace SignedReal

--| NOT PAST, FOR SIGNED REALS.
def NotPast (x y : SignedReal) : Prop := (x.held.add y.owed).NotPast (y.held.add x.owed)

theorem notPast_refl (x : SignedReal) : x.NotPast x := Bracketed.notPast_refl _

theorem notPast_trans {x y z : SignedReal} (h1 : x.NotPast y) (h2 : y.NotPast z) : x.NotPast z :=
  Bracketed.add_cancel_notPast (c := y.held.add y.owed)
    (Bracketed.notPast_trans (Bracketed.notPast_of_same (Bracketed.swap_second_and_fourth x.held z.owed y.held y.owed))
      (Bracketed.notPast_trans (Bracketed.add_notPast h1 h2)
        (Bracketed.notPast_of_same (Bracketed.swap_first_and_third y.held x.owed z.held y.owed))))

--| Each not past the other is one; and one is not past both ways.
theorem same_of_notPast {x y : SignedReal} (h1 : x.NotPast y) (h2 : y.NotPast x) : x.Same y :=
  Bracketed.same_of_notPast h1 h2

theorem notPast_of_same {x y : SignedReal} (h : x.Same y) : x.NotPast y := Bracketed.notPast_of_same h

--| BEING ONE KEEPS IT.
theorem notPast_of_same_notPast {x x' y y' : SignedReal} (hx : x.Same x') (hy : y.Same y') (h : x.NotPast y) :
    x'.NotPast y' :=
  notPast_trans (notPast_of_same (same_symm hx)) (notPast_trans h (notPast_of_same hy))

--| BESIDE KEEPS IT.
theorem add_notPast {x x' y y' : SignedReal} (hx : x.NotPast x') (hy : y.NotPast y') : (x + y).NotPast (x' + y') :=
  Bracketed.notPast_trans (Bracketed.notPast_of_same (Bracketed.swap_middle x.held y.held x'.owed y'.owed))
    (Bracketed.notPast_trans (Bracketed.add_notPast hx hy)
      (Bracketed.notPast_of_same (Bracketed.swap_middle x'.held x.owed y'.held y.owed)))

--| A real held is not under nothing; a real owed is not past nothing.
theorem zero_notPast_ofReal (a : Bracketed) : (ofNat 0).NotPast (ofReal a) :=
  Bracketed.add_notPast (Bracketed.zero_notPast a) (Bracketed.notPast_refl _)

theorem neg_ofReal_notPast_zero (a : Bracketed) : (-ofReal a).NotPast (ofNat 0) :=
  Bracketed.add_notPast (Bracketed.notPast_refl _) (Bracketed.zero_notPast a)

end SignedReal

/-
A PRODUCT OF TWO NOT UNDER NOTHING IS NOT UNDER NOTHING.  What a signed real holds is not under what it owes; then the
product holds, like by like, not under what it owes, unlike by unlike.  At the walls this is a rearrangement: with the one
not past the other, crossing the pairs never gains.  It needs no stage handed in.
-/

--| Crossing never gains: u by t and v by s are not past u by s and v by t, when v is not past u and t not past s.
theorem crossing_never_gains (u v s t : Nat) (hvu : v ≤ u) (hts : t ≤ s) : u * t + v * s ≤ u * s + v * t := by
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hvu
  obtain ⟨f, rfl⟩ := Nat.exists_eq_add_of_le hts
  simp only [Nat.add_mul, Nat.mul_add]
  simp only [Nat.mul_comm]
  omega

theorem Fraction.rearrange {A B C D : Fraction} (hBA : B.le A) (hDC : D.le C) :
    ((A.mul D).add (B.mul C)).le ((A.mul C).add (B.mul D)) := by
  unfold Fraction.le Fraction.add Fraction.mul at *
  dsimp only
  have core := crossing_never_gains (A.over * B.under) (B.over * A.under) (C.over * D.under) (D.over * C.under) hBA hDC
  have m := Nat.mul_le_mul_right (A.under * B.under * C.under * D.under) core
  generalize A.over = a at *; generalize A.under = a' at *; generalize B.over = b at *; generalize B.under = b' at *
  generalize C.over = c at *; generalize C.under = c' at *; generalize D.over = d at *; generalize D.under = d' at *
  simp only [Nat.add_mul] at m ⊢
  simp only [Nat.mul_comm, Nat.mul_left_comm] at m ⊢
  omega

theorem Bracketed.rearrange {a b c d : Bracketed} (hba : b.NotPast a) (hdc : d.NotPast c) :
    ((a.mul d).add (b.mul c)).NotPast ((a.mul c).add (b.mul d)) := fun _ m =>
  Fraction.le_trans
    (Fraction.add_le_add (Fraction.mul_le_mul (a.low_under_high _ (a.stageForProduct c (2 * m + 1))) (Fraction.le_refl _))
      (Fraction.mul_le_mul (Fraction.le_refl _) (c.low_under_high _ (a.stageForProduct c (2 * m + 1)))))
    (Fraction.le_trans (Fraction.rearrange (hba _ _) (hdc _ _))
      (Fraction.add_le_add (Fraction.le_refl _)
        (Fraction.mul_le_mul (b.low_under_high _ _) (d.low_under_high _ _))))

namespace SignedReal

theorem held_not_under_owed {x : SignedReal} (hx : (ofNat 0).NotPast x) : x.owed.NotPast x.held :=
  Bracketed.notPast_trans (Bracketed.notPast_of_same (Bracketed.same_symm (Bracketed.zero_add _)))
    (Bracketed.notPast_trans hx (Bracketed.notPast_of_same (Bracketed.add_zero _)))

--| A PRODUCT OF TWO SIGNED REALS NOT UNDER NOTHING IS NOT UNDER NOTHING.
theorem mul_not_under_nothing {x y : SignedReal} (hx : (ofNat 0).NotPast x) (hy : (ofNat 0).NotPast y) :
    (ofNat 0).NotPast (x * y) :=
  Bracketed.notPast_trans (Bracketed.notPast_of_same (Bracketed.zero_add _))
    (Bracketed.notPast_trans (Bracketed.rearrange (held_not_under_owed hx) (held_not_under_owed hy))
      (Bracketed.notPast_of_same (Bracketed.same_symm (Bracketed.add_zero _))))

end SignedReal

end Meanings
