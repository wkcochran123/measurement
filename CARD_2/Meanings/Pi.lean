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
import Meanings.Order

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

end Meanings
