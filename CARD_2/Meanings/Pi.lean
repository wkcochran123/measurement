/-
The half turn, with no choice.

The arctangent of p over q, not past one, is an alternating series of falling terms: the odd powers over their places.
So it is a real, as cosine and sine are.  A real by a whole number is read as far on as the number times the stage, so
the width still narrows; it is one with the general product, which would read the series millions of terms on.  The half
turn is sixteen arctangents of a fifth less four arctangents of one in two hundred and thirty-nine, Machin's formula: that
this is the half turn is standard (Machin, 1706) and is not proved here, where there is no cosine past one.

Checked: at every stage the half turn lies between 3.14159265358 and 3.14159265359.  And the cut-off cosine, one less θ
squared over two and θ to the fourth over twenty-four, has its first root at the root of six less twice the root of three;
the quarter turn squared is under that, decided at the first stages: the cut-off cosine has not yet reached nothing at the
quarter turn.  A root past another shows at a finite stage, and here it shows.
-/
import Meanings.Quarters

namespace Meanings

--| θ to the 2k and one over 2k and one, for θ = p over q.
def arctanTerm (p q : Nat) (hq : 0 < q) (k : Nat) : Fraction :=
  ⟨p ^ (2 * k + 1), q ^ (2 * k + 1) * (2 * k + 1), Nat.mul_pos (Nat.pow_pos hq) (Nat.succ_pos _)⟩

theorem arctanTerm_falls (p q : Nat) (hq : 0 < q) (hp : p ≤ q) (k : Nat) :
    (arctanTerm p q hq (k + 1)).le (arctanTerm p q hq k) := by
  show p ^ (2 * (k + 1) + 1) * (q ^ (2 * k + 1) * (2 * k + 1)) ≤ p ^ (2 * k + 1) * (q ^ (2 * (k + 1) + 1) * (2 * (k + 1) + 1))
  rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 by omega, Nat.pow_add p (2 * k + 1) 2, Nat.pow_add q (2 * k + 1) 2]
  have h2 : p ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left hp 2
  have m := Nat.mul_le_mul h2 (show 2 * k + 1 ≤ 2 * k + 1 + 2 by omega)
  have m2 := Nat.mul_le_mul_left (p ^ (2 * k + 1) * q ^ (2 * k + 1)) m
  calc p ^ (2 * k + 1) * p ^ 2 * (q ^ (2 * k + 1) * (2 * k + 1))
        = p ^ (2 * k + 1) * q ^ (2 * k + 1) * (p ^ 2 * (2 * k + 1)) := by ac_rfl
    _ ≤ p ^ (2 * k + 1) * q ^ (2 * k + 1) * (q ^ 2 * (2 * k + 1 + 2)) := m2
    _ = p ^ (2 * k + 1) * (q ^ (2 * k + 1) * q ^ 2 * (2 * k + 1 + 2)) := by ac_rfl

def theTermsOfTheArctangent (p q : Nat) (hq : 0 < q) (hp : p ≤ q) : FallingTerms where
  term := arctanTerm p q hq
  falls := arctanTerm_falls p q hq hp
  narrows n := by
    show p ^ (2 * (2 * n + 2) + 1) * (n + 1) ≤ q ^ (2 * (2 * n + 2) + 1) * (2 * (2 * n + 2) + 1)
    exact Nat.mul_le_mul (Nat.pow_le_pow_left hp _) (by omega)

--| THE ARCTANGENT OF p OVER q, FOR p NOT PAST q.
def arctan (p q : Nat) (hq : 0 < q) (hp : p ≤ q) : Bracketed := (theTermsOfTheArctangent p q hq hp).bracketed

--| A REAL BY A WHOLE NUMBER, read c times as far on.
def Bracketed.scale (c : Nat) (x : Bracketed) : Bracketed where
  low n := ⟨c * (x.low (c * n + c)).over, (x.low (c * n + c)).under, (x.low _).under_pos⟩
  high n := ⟨c * (x.high (c * n + c)).over, (x.high (c * n + c)).under, (x.high _).under_pos⟩
  ordered n := by
    show c * (x.low _).over * (x.high _).under ≤ c * (x.high _).over * (x.low _).under
    rw [Nat.mul_assoc, Nat.mul_assoc]; exact Nat.mul_le_mul_left c (x.ordered _)
  low_rises n := by
    show c * (x.low _).over * (x.low _).under ≤ c * (x.low _).over * (x.low _).under
    rw [Nat.mul_assoc, Nat.mul_assoc]
    exact Nat.mul_le_mul_left c (x.low_le_of_le (show c * n + c ≤ c * (n + 1) + c by rw [Nat.mul_succ]; omega))
  high_falls n := by
    show c * (x.high _).over * (x.high _).under ≤ c * (x.high _).over * (x.high _).under
    rw [Nat.mul_assoc, Nat.mul_assoc]
    exact Nat.mul_le_mul_left c (x.high_le_of_le (show c * n + c ≤ c * (n + 1) + c by rw [Nat.mul_succ]; omega))
  narrows n := by
    show c * (x.high (c * n + c)).over * (x.low (c * n + c)).under * (n + 1)
      ≤ c * (x.low (c * n + c)).over * (x.high (c * n + c)).under * (n + 1)
        + (x.high (c * n + c)).under * (x.low (c * n + c)).under
    have h := fewer_parts _ _ _ (c * (n + 1)) _ (x.narrows (c * n + c)) (by rw [Nat.mul_succ]; omega)
    calc c * (x.high (c * n + c)).over * (x.low (c * n + c)).under * (n + 1)
          = (x.high (c * n + c)).over * (x.low (c * n + c)).under * (c * (n + 1)) := by ac_rfl
      _ ≤ (x.low (c * n + c)).over * (x.high (c * n + c)).under * (c * (n + 1))
            + (x.high (c * n + c)).under * (x.low (c * n + c)).under := h
      _ = c * (x.low (c * n + c)).over * (x.high (c * n + c)).under * (n + 1)
            + (x.high (c * n + c)).under * (x.low (c * n + c)).under := by ac_rfl

--| The scaled real is the whole number by the real.
theorem Bracketed.scale_same_mul (c : Nat) (x : Bracketed) : (x.scale c).Same ((Bracketed.ofNat c).mul x) := fun n m =>
  ⟨by
    show c * (x.low _).over * (1 * (x.high _).under) ≤ c * (x.high _).over * (x.low _).under
    rw [Nat.one_mul, Nat.mul_assoc, Nat.mul_assoc]; exact Nat.mul_le_mul_left c (x.low_under_high _ _),
   by
    show c * (x.low _).over * (x.high _).under ≤ c * (x.high _).over * (1 * (x.low _).under)
    rw [Nat.one_mul, Nat.mul_assoc, Nat.mul_assoc]; exact Nat.mul_le_mul_left c (x.low_under_high _ _)⟩

def sixteenArctanFifth : Bracketed := (arctan 1 5 (by decide) (by decide)).scale 16
def fourArctan239th : Bracketed := (arctan 1 239 (by decide) (by decide)).scale 4

theorem machins_two_parts_are_apart : (fourArctan239th.high 0).le (sixteenArctanFifth.low 0) := by decide +kernel

--| THE HALF TURN, BY MACHIN'S FORMULA.
def theHalfTurn : Bracketed := sixteenArctanFifth.difference fourArctan239th 0 machins_two_parts_are_apart

def theHalfTurnsLowWall : Fraction := ⟨314159265358, 100000000000, by decide⟩
def theHalfTurnsHighWall : Fraction := ⟨314159265359, 100000000000, by decide⟩

theorem at_its_first_stage_the_half_turn_is_between :
    theHalfTurnsLowWall.le (theHalfTurn.low 0) ∧ (theHalfTurn.high 0).le theHalfTurnsHighWall := by decide +kernel

--| AT EVERY STAGE THE HALF TURN LIES BETWEEN 3.14159265358 AND 3.14159265359.
theorem the_half_turn_is_between (n : Nat) :
    theHalfTurnsLowWall.le (theHalfTurn.low n) ∧ (theHalfTurn.high n).le theHalfTurnsHighWall :=
  ⟨Fraction.le_trans at_its_first_stage_the_half_turn_is_between.1 (theHalfTurn.low_le_of_le (Nat.zero_le n)),
   Fraction.le_trans (theHalfTurn.high_le_of_le (Nat.zero_le n)) at_its_first_stage_the_half_turn_is_between.2⟩

--| ARCHIMEDES' WALLS.  The polygons of ninety-six sides drawn inside and outside the circle bracket the half turn between
--| three and ten seventy-firsts and three and a seventh: 223/71 and 22/7.  At every stage the half turn here lies between
--| them; and so between 221/71 and 22/7, as the author wrote it.  The walls are Archimedes' (standard); that the half turn
--| is between them is decided from the first stage and carried to every stage by the walls only moving inward.
def archimedesLowWall : Fraction := ⟨223, 71, by decide⟩
def archimedesHighWall : Fraction := ⟨22, 7, by decide⟩
def theAuthorsLowWall : Fraction := ⟨221, 71, by decide⟩

theorem the_half_turn_is_between_archimedes_walls (n : Nat) :
    archimedesLowWall.le (theHalfTurn.low n) ∧ (theHalfTurn.high n).le archimedesHighWall :=
  ⟨Fraction.le_trans (by decide : archimedesLowWall.le theHalfTurnsLowWall) (the_half_turn_is_between n).1,
   Fraction.le_trans (the_half_turn_is_between n).2 (by decide : theHalfTurnsHighWall.le archimedesHighWall)⟩

theorem the_half_turn_is_between_221_over_71_and_22_over_7 (n : Nat) :
    theAuthorsLowWall.le (theHalfTurn.low n) ∧ (theHalfTurn.high n).le archimedesHighWall :=
  ⟨Fraction.le_trans (by decide : theAuthorsLowWall.le archimedesLowWall) (the_half_turn_is_between_archimedes_walls n).1,
   (the_half_turn_is_between_archimedes_walls n).2⟩

--| A real by a whole number keeps being one, and spreads over beside; a fraction, as a real, by a whole number is the
--| fraction so many times; and fractions as reals add as fractions.
theorem Bracketed.scale_same {x y : Bracketed} (c : Nat) (h : x.Same y) : (x.scale c).Same (y.scale c) :=
  Bracketed.same_trans (Bracketed.scale_same_mul c x)
    (Bracketed.same_trans (Bracketed.mul_same (Bracketed.same_refl _) h) (Bracketed.same_symm (Bracketed.scale_same_mul c y)))

theorem Bracketed.scale_add (c : Nat) (x y : Bracketed) : ((x.add y).scale c).Same ((x.scale c).add (y.scale c)) :=
  Bracketed.same_trans (Bracketed.scale_same_mul c _)
    (Bracketed.same_trans (Bracketed.mul_add _ _ _)
      (Bracketed.add_same (Bracketed.same_symm (Bracketed.scale_same_mul c x)) (Bracketed.same_symm (Bracketed.scale_same_mul c y))))

theorem Bracketed.scale_ofFraction (c : Nat) (a : Fraction) :
    ((Bracketed.ofFraction a).scale c).Same (Bracketed.ofFraction ⟨c * a.over, a.under, a.under_pos⟩) :=
  fun _ _ => ⟨Fraction.le_refl _, Fraction.le_refl _⟩

theorem Bracketed.ofFraction_add (a b : Fraction) :
    ((Bracketed.ofFraction a).add (Bracketed.ofFraction b)).Same (Bracketed.ofFraction (a.add b)) :=
  fun _ _ => ⟨Fraction.le_refl _, Fraction.le_refl _⟩

theorem Bracketed.ofFraction_same {a b : Fraction} (h1 : a.le b) (h2 : b.le a) :
    (Bracketed.ofFraction a).Same (Bracketed.ofFraction b) := fun _ _ => ⟨h1, h2⟩

--| THE ROOT OF THREE, BY HALVING.
def theRootOfThree : DyadicCut where
  cut := rootByHalving 3 1
  doubles := rootByHalving_doubles 3 1

--| THE CUT-OFF COSINE HAS NOT REACHED NOTHING AT THE QUARTER TURN.  Its first root squared is six less twice the root of
--| three; the quarter turn squared, a quarter of the half turn's high wall squared, beside twice the root of three's high
--| wall, is under six: so the quarter turn is under the cut-off cosine's first root.  Decided at the half turn's first
--| stage and the root of three's twentieth; every later stage only brings the high walls down.
theorem the_quarter_turn_is_under_the_cut_off_cosines_first_root :
    ((((theHalfTurn.high 0).mul (theHalfTurn.high 0)).mul ⟨1, 4, by decide⟩).add
        ((⟨2, 1, by decide⟩ : Fraction).mul (theRootOfThree.bracketed.high 20))).lt ⟨6, 1, by decide⟩ := by
  decide +kernel

/-
THE BRANCH NEVER TAKEN.  Read linearly, a step's angle is its first term, θ itself.  What that reading drops is the rest of
the arctangent, θ cubed over three less θ to the fifth over five and on: an alternating series of falling terms, a real.
The angle beside the branch never taken is the step, exactly, at every stage: the two series telescope.
-/

theorem arctanTerm_le_first (p q : Nat) (hq : 0 < q) (hp : p ≤ q) : ∀ k, (arctanTerm p q hq k).le (arctanTerm p q hq 0)
  | 0 => Fraction.le_refl _
  | k + 1 => Fraction.le_trans (arctanTerm_falls p q hq hp k) (arctanTerm_le_first p q hq hp k)

def theTermsNeverTaken (p q : Nat) (hq : 0 < q) (hp : p ≤ q) : FallingTerms where
  term k := arctanTerm p q hq (k + 1)
  falls k := arctanTerm_falls p q hq hp (k + 1)
  narrows n := by
    show p ^ (2 * (2 * n + 2 + 1) + 1) * (n + 1) ≤ q ^ (2 * (2 * n + 2 + 1) + 1) * (2 * (2 * n + 2 + 1) + 1)
    exact Nat.mul_le_mul (Nat.pow_le_pow_left hp _) (by omega)

--| THE BRANCH NEVER TAKEN: θ cubed over three, less θ to the fifth over five, and on.
def theBranchNeverTaken (p q : Nat) (hq : 0 < q) (hp : p ≤ q) : Bracketed := (theTermsNeverTaken p q hq hp).bracketed

--| A difference beside the next difference is the whole difference, both ways.
theorem the_differences_telescope (ao au bo bu co cu X Y Z : Nat)
    (hX : bo * au + X = ao * bu) (hY : co * bu + Y = bo * cu) (hZ : co * au + Z = ao * cu) :
    (X * (bu * cu) + Y * (au * bu)) * (au * cu) = Z * ((au * bu) * (bu * cu)) := by
  have z : Z * bu = X * cu + Y * au := by
    have m1 := congrArg (· * cu) hX
    have m2 := congrArg (· * au) hY
    have m3 := congrArg (· * bu) hZ
    simp only [Nat.add_mul] at m1 m2 m3
    simp only [Nat.mul_comm, Nat.mul_left_comm] at m1 m2 m3 ⊢
    omega
  have m := congrArg (· * (bu * (au * cu))) z
  simp only [Nat.add_mul] at m ⊢
  simp only [Nat.mul_comm, Nat.mul_left_comm] at m ⊢
  omega

theorem Fraction.sub_add_sub (a b c : Fraction) (hcb : c.le b) (hba : b.le a) :
    ((a.sub b).add (b.sub c)).le (a.sub c) ∧ (a.sub c).le ((a.sub b).add (b.sub c)) := by
  have hca : c.le a := Fraction.le_trans hcb hba
  unfold Fraction.le at hcb hba hca
  have e := the_differences_telescope a.over a.under b.over b.under c.over c.under _ _ _
    (Nat.add_sub_of_le hba) (Nat.add_sub_of_le hcb) (Nat.add_sub_of_le hca)
  unfold Fraction.le Fraction.add Fraction.sub
  dsimp only
  exact ⟨Nat.le_of_eq e, Nat.le_of_eq e.symm⟩

theorem arctan_partial (p q : Nat) (hq : 0 < q) (hp : p ≤ q) (M : Nat) :
    (theTermsOfTheArctangent p q hq hp).stepsAndTail.partial (M + 1)
      = ((theTermsOfTheArctangent p q hq hp).stepsAndTail.partial M).add
          ((arctanTerm p q hq (2 * M + 2)).sub (arctanTerm p q hq (2 * M + 3))) := by
  show _ = _
  show ((theTermsOfTheArctangent p q hq hp).stepsAndTail.partial M).add
      ((arctanTerm p q hq (2 * (M + 1))).sub (arctanTerm p q hq (2 * (M + 1) + 1))) = _
  rw [show 2 * (M + 1) = 2 * M + 2 by omega, show 2 * M + 2 + 1 = 2 * M + 3 by omega]

theorem never_taken_partial (p q : Nat) (hq : 0 < q) (hp : p ≤ q) (M : Nat) :
    (theTermsNeverTaken p q hq hp).stepsAndTail.partial (M + 1)
      = ((theTermsNeverTaken p q hq hp).stepsAndTail.partial M).add
          ((arctanTerm p q hq (2 * M + 3)).sub (arctanTerm p q hq (2 * M + 4))) := by
  show ((theTermsNeverTaken p q hq hp).stepsAndTail.partial M).add
      ((arctanTerm p q hq (2 * (M + 1) + 1)).sub (arctanTerm p q hq (2 * (M + 1) + 1 + 1))) = _
  rw [show 2 * (M + 1) + 1 = 2 * M + 3 by omega, show 2 * M + 3 + 1 = 2 * M + 4 by omega]

--| THE ANGLE AND THE BRANCH NEVER TAKEN, SUMMED TO M, ARE THE STEP LESS THE TERM 2M AND TWO ON, both ways.
theorem the_angle_and_the_branch_telescope (p q : Nat) (hq : 0 < q) (hp : p ≤ q) (M : Nat) :
    (((theTermsOfTheArctangent p q hq hp).stepsAndTail.partial M).add
        ((theTermsNeverTaken p q hq hp).stepsAndTail.partial M)).le
      ((arctanTerm p q hq 0).sub (arctanTerm p q hq (2 * M + 2)))
    ∧ ((arctanTerm p q hq 0).sub (arctanTerm p q hq (2 * M + 2))).le
      (((theTermsOfTheArctangent p q hq hp).stepsAndTail.partial M).add
        ((theTermsNeverTaken p q hq hp).stepsAndTail.partial M)) := by
  have f := arctanTerm_falls p q hq hp
  have first := arctanTerm_le_first p q hq hp
  induction M with
  | zero =>
    show (((arctanTerm p q hq 0).sub (arctanTerm p q hq 1)).add ((arctanTerm p q hq 1).sub (arctanTerm p q hq 2))).le
        ((arctanTerm p q hq 0).sub (arctanTerm p q hq 2))
      ∧ ((arctanTerm p q hq 0).sub (arctanTerm p q hq 2)).le
        (((arctanTerm p q hq 0).sub (arctanTerm p q hq 1)).add ((arctanTerm p q hq 1).sub (arctanTerm p q hq 2)))
    exact Fraction.sub_add_sub _ _ _ (f 1) (f 0)
  | succ M ih =>
    rw [arctan_partial, never_taken_partial, show 2 * (M + 1) + 2 = 2 * M + 4 by omega]
    have t1 := Fraction.sub_add_sub _ _ _ (f (2 * M + 3)) (f (2 * M + 2))
    have t2 := Fraction.sub_add_sub (arctanTerm p q hq 0) (arctanTerm p q hq (2 * M + 2)) (arctanTerm p q hq (2 * M + 4))
      (Fraction.le_trans (f (2 * M + 3)) (f (2 * M + 2))) (first _)
    exact ⟨Fraction.le_trans (Fraction.swap_middle _ _ _ _)
        (Fraction.le_trans (Fraction.add_le_add ih.1 t1.1) t2.1),
      Fraction.le_trans t2.2
        (Fraction.le_trans (Fraction.add_le_add ih.2 t1.2) (Fraction.swap_middle _ _ _ _))⟩

theorem arctan_low (p q : Nat) (hq : 0 < q) (hp : p ≤ q) (n : Nat) :
    (arctan p q hq hp).low n = (theTermsOfTheArctangent p q hq hp).stepsAndTail.partial n := rfl
theorem arctan_high (p q : Nat) (hq : 0 < q) (hp : p ≤ q) (n : Nat) :
    (arctan p q hq hp).high n
      = ((theTermsOfTheArctangent p q hq hp).stepsAndTail.partial n).add (arctanTerm p q hq (2 * n + 2)) := rfl
theorem branch_low (p q : Nat) (hq : 0 < q) (hp : p ≤ q) (n : Nat) :
    (theBranchNeverTaken p q hq hp).low n = (theTermsNeverTaken p q hq hp).stepsAndTail.partial n := rfl
theorem branch_high (p q : Nat) (hq : 0 < q) (hp : p ≤ q) (n : Nat) :
    (theBranchNeverTaken p q hq hp).high n
      = ((theTermsNeverTaken p q hq hp).stepsAndTail.partial n).add (arctanTerm p q hq (2 * n + 2 + 1)) := rfl

--| THE ANGLE BESIDE THE BRANCH NEVER TAKEN IS THE STEP, at every stage.
theorem the_angle_beside_the_branch_never_taken_is_the_step (p q : Nat) (hq : 0 < q) (hp : p ≤ q) :
    ((arctan p q hq hp).add (theBranchNeverTaken p q hq hp)).Same (Bracketed.ofFraction (arctanTerm p q hq 0)) := by
  apply Bracketed.same_of_each_stage
  intro k
  have t := the_angle_and_the_branch_telescope p q hq hp (2 * k + 1)
  have last := arctanTerm_le_first p q hq hp (2 * (2 * k + 1) + 2)
  show (((arctan p q hq hp).low (2 * k + 1)).add ((theBranchNeverTaken p q hq hp).low (2 * k + 1))).le (arctanTerm p q hq 0)
    ∧ (arctanTerm p q hq 0).le (((arctan p q hq hp).high (2 * k + 1)).add ((theBranchNeverTaken p q hq hp).high (2 * k + 1)))
  rw [arctan_low, branch_low, arctan_high, branch_high]
  exact ⟨Fraction.le_trans t.1 (Fraction.le_trans (Fraction.le_add_right _ _) (Fraction.sub_add_self_le _ _ last)),
    Fraction.le_trans (Fraction.le_sub_add_self _ _ last)
      (Fraction.le_trans (Fraction.add_le_add t.2 (Fraction.le_refl _))
        (Fraction.le_trans (Fraction.le_add_right _ _)
          (Fraction.le_trans (Fraction.add_regroup _ _ _) (Fraction.swap_middle _ _ _ _))))⟩

end Meanings
