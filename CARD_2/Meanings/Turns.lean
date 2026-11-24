/-
A turn read through its norm, with no choice.

A turn with whole-number parts, a along and b across, has a whole-number norm squared, a by a beside b by b.  Its radius is
the root of that whole number, which halving computes.  So its cosine and sine are reals: a, and b, each by one over the
radius.  And for every such turn cosine squared beside sine squared is one, exactly, at every stage: the parts squared
beside each other are the norm squared, and the root by itself is the norm squared too.  That is Pythagoras for the turn's
own triangle; it passes through no series, so it needs no addition law.

What the norm does not give is the angle as a number: it gives the angle's cosine and sine, not the angle.
-/
import Meanings.Pi

namespace Meanings

--| THE ROOT OF A WHOLE NUMBER, BY HALVING, from a start whose square is not past it and whose next square is.
def theRootOf (N s : Nat) (_h1 : s * s ≤ N) (_h2 : N < (s + 1) * (s + 1)) : Bracketed :=
  (⟨rootByHalving N s, rootByHalving_doubles N s⟩ : DyadicCut).bracketed

theorem theRootOf_holds (N s : Nat) (h1 : s * s ≤ N) (h2 : N < (s + 1) * (s + 1)) (j : Nat) :
    rootByHalving N s j * rootByHalving N s j * 1 ≤ N * (2 ^ j * 2 ^ j)
      ∧ N * (2 ^ j * 2 ^ j) ≤ (rootByHalving N s j + 1) * (rootByHalving N s j + 1) * 1 := by
  rw [Nat.mul_one, Nat.mul_one, ← Nat.mul_pow]
  exact ⟨(rootByHalving_holds N s h1 h2 j).1, Nat.le_of_lt (rootByHalving_holds N s h1 h2 j).2⟩

--| THE ROOT BY ITSELF IS THE WHOLE NUMBER.
theorem theRootOf_by_itself (N s : Nat) (h1 : s * s ≤ N) (h2 : N < (s + 1) * (s + 1)) :
    ((theRootOf N s h1 h2).mul (theRootOf N s h1 h2)).Same (Bracketed.ofNat N) := fun _ _ =>
  ⟨(theRootOf_holds N s h1 h2 _).1, (theRootOf_holds N s h1 h2 _).2⟩

theorem theRootOf_past_nothing (N s : Nat) (h1 : s * s ≤ N) (h2 : N < (s + 1) * (s + 1)) (hs : 0 < s) :
    0 < ((theRootOf N s h1 h2).low 0).over := hs

--| Four each for each, the middle two exchanged.
theorem Bracketed.mul_swap_middle (a b c d : Bracketed) : ((a.mul b).mul (c.mul d)).Same ((a.mul c).mul (b.mul d)) :=
  Bracketed.same_trans (Bracketed.mul_assoc _ _ _)
    (Bracketed.same_trans (Bracketed.mul_same (Bracketed.same_refl a) (Bracketed.same_symm (Bracketed.mul_assoc _ _ _)))
      (Bracketed.same_trans
        (Bracketed.mul_same (Bracketed.same_refl a) (Bracketed.mul_same (Bracketed.mul_comm b c) (Bracketed.same_refl d)))
        (Bracketed.same_trans (Bracketed.mul_same (Bracketed.same_refl a) (Bracketed.mul_assoc _ _ _))
          (Bracketed.same_symm (Bracketed.mul_assoc _ _ _)))))

--| The norm squared by one over the radius squared is one.
theorem the_norm_by_one_over_the_radius_squared {r : Bracketed} {N k : Nat} {pos : 0 < (r.low k).over}
    (hr : (r.mul r).Same (Bracketed.ofNat N)) :
    ((Bracketed.ofNat N).mul ((r.reciprocal k pos).mul (r.reciprocal k pos))).Same (Bracketed.ofNat 1) :=
  Bracketed.same_trans (Bracketed.mul_same (Bracketed.same_symm hr) (Bracketed.same_refl _))
    (Bracketed.same_trans (Bracketed.mul_swap_middle _ _ _ _)
      (Bracketed.same_trans (Bracketed.mul_same (r.mul_reciprocal k pos) (r.mul_reciprocal k pos)) (Bracketed.one_mul _)))

--| A TURN READ THROUGH ITS NORM IS ON THE CIRCLE.  With a along and b across, the parts squared beside each other the norm
--| squared, and the radius by itself the norm squared: a over the radius squared, beside b over the radius squared, is one.
theorem the_turn_through_its_norm_is_on_the_circle (a b r : Bracketed) (N k : Nat) (pos : 0 < (r.low k).over)
    (hab : ((a.mul a).add (b.mul b)).Same (Bracketed.ofNat N)) (hr : (r.mul r).Same (Bracketed.ofNat N)) :
    (((a.mul (r.reciprocal k pos)).mul (a.mul (r.reciprocal k pos))).add
      ((b.mul (r.reciprocal k pos)).mul (b.mul (r.reciprocal k pos)))).Same (Bracketed.ofNat 1) :=
  Bracketed.same_trans (Bracketed.add_same (Bracketed.mul_swap_middle _ _ _ _) (Bracketed.mul_swap_middle _ _ _ _))
    (Bracketed.same_trans (Bracketed.same_symm (Bracketed.add_mul _ _ _))
      (Bracketed.same_trans (Bracketed.mul_same hab (Bracketed.same_refl _)) (the_norm_by_one_over_the_radius_squared hr)))

--| THE STEP (n, 1): its radius, the root of n by n and one; its cosine, n over the radius; its sine, one over the radius.
theorem the_step_starts_under (n : Nat) (hn : 0 < n) : n * n + 1 < (n + 1) * (n + 1) := by
  have : 1 ≤ n := hn
  simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
  omega

def theStepRadius (n : Nat) (hn : 0 < n) : Bracketed := theRootOf (n * n + 1) n (Nat.le_succ _) (the_step_starts_under n hn)

def theStepCosine (n : Nat) (hn : 0 < n) : Bracketed :=
  (Bracketed.ofNat n).mul ((theStepRadius n hn).reciprocal 0 hn)

def theStepSine (n : Nat) (hn : 0 < n) : Bracketed :=
  (Bracketed.ofNat 1).mul ((theStepRadius n hn).reciprocal 0 hn)

--| EVERY STEP IS ON THE CIRCLE: its cosine squared beside its sine squared is one, at every stage.
theorem every_step_is_on_the_circle (n : Nat) (hn : 0 < n) :
    (((theStepCosine n hn).mul (theStepCosine n hn)).add ((theStepSine n hn).mul (theStepSine n hn))).Same
      (Bracketed.ofNat 1) :=
  the_turn_through_its_norm_is_on_the_circle _ _ _ (n * n + 1) 0 hn
    (Bracketed.same_trans (Bracketed.add_same (Bracketed.ofNat_mul n n) (Bracketed.ofNat_mul 1 1)) (Bracketed.ofNat_add _ _))
    (theRootOf_by_itself _ _ _ _)

--| THE RADIUS BY THE COSINE IS THE ALONG, AND BY THE SINE THE ACROSS: the step is its radius by its turn.
theorem the_radius_by_a_part_over_it (a r : Bracketed) (k : Nat) (pos : 0 < (r.low k).over) :
    (r.mul (a.mul (r.reciprocal k pos))).Same a :=
  Bracketed.same_trans (Bracketed.mul_same (Bracketed.same_refl r) (Bracketed.mul_comm _ _))
    (Bracketed.same_trans (Bracketed.same_symm (Bracketed.mul_assoc _ _ _))
      (Bracketed.same_trans (Bracketed.mul_same (r.mul_reciprocal k pos) (Bracketed.same_refl a)) (Bracketed.one_mul a)))

theorem the_step_is_its_radius_by_its_turn (n : Nat) (hn : 0 < n) :
    ((theStepRadius n hn).mul (theStepCosine n hn)).Same (Bracketed.ofNat n)
      ∧ ((theStepRadius n hn).mul (theStepSine n hn)).Same (Bracketed.ofNat 1) :=
  ⟨the_radius_by_a_part_over_it _ _ _ _, the_radius_by_a_part_over_it _ _ _ _⟩

--| A whole number by one over it is one; one over the radius squared is one over the norm squared.
theorem Bracketed.ofNat_by_one_over (N : Nat) (hN : 0 < N) :
    ((Bracketed.ofNat N).mul (Bracketed.ofFraction ⟨1, N, hN⟩)).Same (Bracketed.ofNat 1) := fun _ _ =>
  ⟨by show N * 1 * 1 ≤ 1 * (1 * N); simp, by show 1 * (1 * N) ≤ N * 1 * 1; simp⟩

theorem one_over_the_radius_squared {r : Bracketed} {N k : Nat} {pos : 0 < (r.low k).over}
    (hr : (r.mul r).Same (Bracketed.ofNat N)) (hN : 0 < N) :
    ((r.reciprocal k pos).mul (r.reciprocal k pos)).Same (Bracketed.ofFraction ⟨1, N, hN⟩) :=
  Bracketed.same_trans (Bracketed.same_symm (Bracketed.mul_one _))
    (Bracketed.same_trans (Bracketed.mul_same (Bracketed.same_refl _) (Bracketed.same_symm (Bracketed.ofNat_by_one_over N hN)))
      (Bracketed.same_trans (Bracketed.same_symm (Bracketed.mul_assoc _ _ _))
        (Bracketed.same_trans (Bracketed.mul_same (Bracketed.mul_comm _ _) (Bracketed.same_refl _))
          (Bracketed.same_trans (Bracketed.mul_same (the_norm_by_one_over_the_radius_squared hr) (Bracketed.same_refl _))
            (Bracketed.one_mul _)))))

--| A WHOLE PART OVER THE RADIUS, SQUARED, IS THE PART SQUARED OVER THE NORM SQUARED.
theorem a_whole_part_over_the_radius_squared (a : Nat) {r : Bracketed} {N k : Nat} {pos : 0 < (r.low k).over}
    (hr : (r.mul r).Same (Bracketed.ofNat N)) (hN : 0 < N) :
    (((Bracketed.ofNat a).mul (r.reciprocal k pos)).mul ((Bracketed.ofNat a).mul (r.reciprocal k pos))).Same
      (Bracketed.ofFraction ⟨a * a, N, hN⟩) :=
  Bracketed.same_trans (Bracketed.mul_swap_middle _ _ _ _)
    (Bracketed.same_trans (Bracketed.mul_same (Bracketed.ofNat_mul a a) (one_over_the_radius_squared hr hN))
      (fun _ _ => ⟨by show a * a * 1 * N ≤ a * a * (1 * N); simp, by show a * a * (1 * N) ≤ a * a * 1 * N; simp⟩))

--| AND A ROOT PART OVER THE RADIUS, SQUARED, IS ITS WHOLE NUMBER OVER THE NORM SQUARED.
theorem a_root_part_over_the_radius_squared {b r : Bracketed} {M N k : Nat} {pos : 0 < (r.low k).over}
    (hb : (b.mul b).Same (Bracketed.ofNat M)) (hr : (r.mul r).Same (Bracketed.ofNat N)) (hN : 0 < N) :
    ((b.mul (r.reciprocal k pos)).mul (b.mul (r.reciprocal k pos))).Same (Bracketed.ofFraction ⟨M, N, hN⟩) :=
  Bracketed.same_trans (Bracketed.mul_swap_middle _ _ _ _)
    (Bracketed.same_trans (Bracketed.mul_same hb (one_over_the_radius_squared hr hN))
      (fun _ _ => ⟨by show M * 1 * N ≤ M * (1 * N); simp, by show M * (1 * N) ≤ M * 1 * N; simp⟩))

/-
THE ADDITION LAW FOR TURNS, THROUGH THEIR NORMS.  Two reals whose squares are one are one: squares of walls never under
nothing keep the order, and walls only move inward.  So the radius of a product of turns is the product of the radii, and
one over it is the product of the one-overs.  Then, for turns with whole parts and the along of the product not under
nothing, the cosine of the product beside the sines' product is the cosines' product, and the sine of the product is the
crossed products beside each other.  This is the addition law for turns read through their norms: it rests on
Brahmagupta's identity in whole numbers, and passes through no series.
-/

theorem Fraction.le_of_squares_le {p q : Fraction} (h : (p.mul p).le (q.mul q)) : p.le q := by
  unfold Fraction.le Fraction.mul at *
  dsimp only at h
  apply Nat.mul_self_le_mul_self_iff.1
  calc p.over * q.under * (p.over * q.under) = p.over * p.over * (q.under * q.under) := by ac_rfl
    _ ≤ q.over * q.over * (p.under * p.under) := h
    _ = q.over * p.under * (q.over * p.under) := by ac_rfl

theorem Bracketed.le_stageForProduct (x y : Bracketed) (n : Nat) : n ≤ x.stageForProduct y n := by
  unfold Bracketed.stageForProduct
  exact Nat.le_trans (Nat.le_mul_of_pos_left n (Nat.succ_pos _)) (Nat.le_add_right _ _)

--| TWO REALS WHOSE SQUARES ARE ONE ARE ONE.
theorem Bracketed.same_of_squares_same {x y : Bracketed} (h : (x.mul x).Same (y.mul y)) : x.Same y := fun n m =>
  ⟨Fraction.le_of_squares_le (Fraction.le_trans
      (Fraction.mul_le_mul (x.low_le_of_le (Bracketed.le_stageForProduct x x n))
        (x.low_le_of_le (Bracketed.le_stageForProduct x x n)))
      (Fraction.le_trans (h n m).1
        (Fraction.mul_le_mul (y.high_le_of_le (Bracketed.le_stageForProduct y y m))
          (y.high_le_of_le (Bracketed.le_stageForProduct y y m))))),
   Fraction.le_of_squares_le (Fraction.le_trans
      (Fraction.mul_le_mul (y.low_le_of_le (Bracketed.le_stageForProduct y y n))
        (y.low_le_of_le (Bracketed.le_stageForProduct y y n)))
      (Fraction.le_trans (h n m).2
        (Fraction.mul_le_mul (x.high_le_of_le (Bracketed.le_stageForProduct x x m))
          (x.high_le_of_le (Bracketed.le_stageForProduct x x m)))))⟩

--| ONE OVER IS ONE THING, for reals.
theorem Bracketed.reciprocal_unique {x u v : Bracketed} (hu : (x.mul u).Same (Bracketed.ofNat 1))
    (hv : (x.mul v).Same (Bracketed.ofNat 1)) : u.Same v :=
  Bracketed.same_trans (Bracketed.same_symm (Bracketed.mul_one u))
    (Bracketed.same_trans (Bracketed.mul_same (Bracketed.same_refl u) (Bracketed.same_symm hv))
      (Bracketed.same_trans (Bracketed.same_symm (Bracketed.mul_assoc _ _ _))
        (Bracketed.same_trans (Bracketed.mul_same (Bracketed.mul_comm u x) (Bracketed.same_refl v))
          (Bracketed.same_trans (Bracketed.mul_same hu (Bracketed.same_refl v)) (Bracketed.one_mul v)))))

--| BRAHMAGUPTA, IN WHOLE NUMBERS: the parts of a product of turns, squared and beside each other, are the norms' product.
theorem brahmagupta (a b c d e : Nat) (hac : a * c = b * d + e) :
    e * e + (a * d + b * c) * (a * d + b * c) = (a * a + b * b) * (c * c + d * d) := by
  have m1 := congrArg (fun z => z * z) hac
  have m2 := congrArg (fun z => z * (b * d)) hac
  simp only [Nat.add_mul, Nat.mul_add] at m1 m2 ⊢
  simp only [Nat.mul_comm, Nat.mul_left_comm] at m1 m2 ⊢
  omega

--| THE ADDITION LAW FOR TURNS.
theorem the_turns_add (a b c d : Nat) (hbd : b * d ≤ a * c) (rz rw rzw : Bracketed) (kz kw kzw : Nat)
    (pz : 0 < (rz.low kz).over) (pw : 0 < (rw.low kw).over) (pzw : 0 < (rzw.low kzw).over)
    (hz : (rz.mul rz).Same (Bracketed.ofNat (a * a + b * b))) (hw : (rw.mul rw).Same (Bracketed.ofNat (c * c + d * d)))
    (hzw : (rzw.mul rzw).Same (Bracketed.ofNat ((a * c - b * d) * (a * c - b * d) + (a * d + b * c) * (a * d + b * c)))) :
    rzw.Same (rz.mul rw)
      ∧ (((Bracketed.ofNat (a * c - b * d)).mul (rzw.reciprocal kzw pzw)).add
          (((Bracketed.ofNat b).mul (rz.reciprocal kz pz)).mul ((Bracketed.ofNat d).mul (rw.reciprocal kw pw)))).Same
          (((Bracketed.ofNat a).mul (rz.reciprocal kz pz)).mul ((Bracketed.ofNat c).mul (rw.reciprocal kw pw)))
      ∧ ((Bracketed.ofNat (a * d + b * c)).mul (rzw.reciprocal kzw pzw)).Same
          ((((Bracketed.ofNat a).mul (rz.reciprocal kz pz)).mul ((Bracketed.ofNat d).mul (rw.reciprocal kw pw))).add
            (((Bracketed.ofNat b).mul (rz.reciprocal kz pz)).mul ((Bracketed.ofNat c).mul (rw.reciprocal kw pw)))) := by
  have norm : (a * c - b * d) * (a * c - b * d) + (a * d + b * c) * (a * d + b * c) = (a * a + b * b) * (c * c + d * d) :=
    brahmagupta a b c d _ (Nat.add_sub_of_le hbd).symm
  have radius : rzw.Same (rz.mul rw) := by
    apply Bracketed.same_of_squares_same
    rw [norm] at hzw
    exact Bracketed.same_trans hzw
      (Bracketed.same_trans (Bracketed.same_symm (Bracketed.ofNat_mul _ _))
        (Bracketed.same_trans (Bracketed.mul_same (Bracketed.same_symm hz) (Bracketed.same_symm hw))
          (Bracketed.mul_swap_middle _ _ _ _)))
  have over : (rzw.reciprocal kzw pzw).Same ((rz.reciprocal kz pz).mul (rw.reciprocal kw pw)) :=
    Bracketed.reciprocal_unique (rzw.mul_reciprocal kzw pzw)
      (Bracketed.same_trans (Bracketed.mul_same radius (Bracketed.same_refl _))
        (Bracketed.same_trans (Bracketed.mul_swap_middle _ _ _ _)
          (Bracketed.same_trans (Bracketed.mul_same (rz.mul_reciprocal kz pz) (rw.mul_reciprocal kw pw))
            (Bracketed.one_mul _))))
  have part : ∀ x y : Nat, (((Bracketed.ofNat x).mul (rz.reciprocal kz pz)).mul ((Bracketed.ofNat y).mul (rw.reciprocal kw pw))).Same
      ((Bracketed.ofNat (x * y)).mul (rzw.reciprocal kzw pzw)) := fun x y =>
    Bracketed.same_trans (Bracketed.mul_swap_middle _ _ _ _)
      (Bracketed.mul_same (Bracketed.ofNat_mul x y) (Bracketed.same_symm over))
  refine ⟨radius, ?_, ?_⟩
  · have sum : ((Bracketed.ofNat (a * c - b * d)).add (Bracketed.ofNat (b * d))).Same (Bracketed.ofNat (a * c)) := by
      have h := Bracketed.ofNat_add (a * c - b * d) (b * d)
      rw [Nat.sub_add_cancel hbd] at h
      exact h
    exact Bracketed.same_trans (Bracketed.add_same (Bracketed.same_refl _) (part b d))
      (Bracketed.same_trans (Bracketed.same_symm (Bracketed.add_mul _ _ _))
        (Bracketed.same_trans (Bracketed.mul_same sum (Bracketed.same_refl _)) (Bracketed.same_symm (part a c))))
  · exact Bracketed.same_trans (Bracketed.mul_same (Bracketed.same_symm (Bracketed.ofNat_add _ _)) (Bracketed.same_refl _))
      (Bracketed.same_trans (Bracketed.add_mul _ _ _)
        (Bracketed.add_same (Bracketed.same_symm (part a d)) (Bracketed.same_symm (part b c))))

end Meanings
