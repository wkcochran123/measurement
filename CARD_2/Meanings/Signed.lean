/-
Negatives: what is held and what is owed.

Episode 13 makes the integers from Areas without taking anything away: an Account is two Areas kept side by side, what is
held and what is owed.  The reals take their negatives the same way.  A signed real is two reals, held and owed; it is
their difference, and nothing is ever subtracted.  Two signed reals are one when the held of each and the owed of the
other are one.  Turned over, what was held is owed.  Each for each: like with like is held, unlike is owed.
-/
import Meanings.Arithmetic

namespace Meanings

--| A whole number, as a real: the same fraction for a wall on both sides, at every stage.
def Bracketed.ofNat (k : Nat) : Bracketed where
  low _ := ⟨k, 1, Nat.one_pos⟩
  high _ := ⟨k, 1, Nat.one_pos⟩
  ordered _ := Nat.le_refl _
  low_rises _ := Nat.le_refl _
  high_falls _ := Nat.le_refl _
  narrows _ := Nat.le_add_right _ _

instance (p q : Fraction) : Decidable (p.le q) := inferInstanceAs (Decidable (_ ≤ _))

--| HELD AND OWED.
structure SignedReal where
  held : Bracketed
  owed : Bracketed

namespace SignedReal

def ofReal (x : Bracketed) : SignedReal := ⟨x, Bracketed.ofNat 0⟩
def ofNat (k : Nat) : SignedReal := ofReal (Bracketed.ofNat k)

--| Beside: held with held, owed with owed.
instance : Add SignedReal := ⟨fun x y => ⟨x.held.add y.held, x.owed.add y.owed⟩⟩
--| Turned over: what was held is owed.
instance : Neg SignedReal := ⟨fun x => ⟨x.owed, x.held⟩⟩
--| Less: beside the other turned over.
instance : Sub SignedReal := ⟨fun x y => ⟨x.held.add y.owed, x.owed.add y.held⟩⟩
--| Each for each: like with like is held, unlike is owed.
instance : Mul SignedReal :=
  ⟨fun x y => ⟨(x.held.mul y.held).add (x.owed.mul y.owed), (x.held.mul y.owed).add (x.owed.mul y.held)⟩⟩

--| Two signed reals are one when the held of each beside the owed of the other are one.
def Same (x y : SignedReal) : Prop := (x.held.add y.owed).Same (y.held.add x.owed)

--| At a stage, a signed real's bracket holds nothing: no wall of what is held is past the far wall of what is owed.
def HoldsNothingAt (x : SignedReal) (n : Nat) : Prop := (x.held.low n).le (x.owed.high n) ∧ (x.owed.low n).le (x.held.high n)

instance (x : SignedReal) (n : Nat) : Decidable (x.HoldsNothingAt n) := inferInstanceAs (Decidable (_ ∧ _))

end SignedReal

--| THE ROOT OF NINETY, BY ITSELF, IS NINETY.  At every stage of the product, the low wall is not past ninety and ninety is
--| not past the high wall; so it is ninety, whichever stages are set side by side.
theorem the_root_holds_ninety_at_every_stage (j : Nat) :
    theRootOfNinety.cut j * theRootOfNinety.cut j * 1 ≤ 90 * (2 ^ j * 2 ^ j)
      ∧ 90 * (2 ^ j * 2 ^ j) ≤ (theRootOfNinety.cut j + 1) * (theRootOfNinety.cut j + 1) * 1 := by
  rw [Nat.mul_one, Nat.mul_one, ← Nat.mul_pow]
  exact ⟨(theRootOfNinety_holds_the_root j).1, Nat.le_of_lt (theRootOfNinety_holds_the_root j).2⟩

theorem the_low_square_is_not_past_ninety (j m : Nat) :
    ((theRootOfNinety.bracketed.low j).mul (theRootOfNinety.bracketed.low j)).le ((Bracketed.ofNat 90).high m) :=
  (the_root_holds_ninety_at_every_stage j).1

theorem ninety_is_not_past_the_high_square (j m : Nat) :
    ((Bracketed.ofNat 90).low m).le ((theRootOfNinety.bracketed.high j).mul (theRootOfNinety.bracketed.high j)) :=
  (the_root_holds_ninety_at_every_stage j).2

theorem the_root_by_itself_is_ninety :
    (theRootOfNinety.bracketed.mul theRootOfNinety.bracketed).Same (Bracketed.ofNat 90) :=
  fun n m =>
    ⟨the_low_square_is_not_past_ninety (theRootOfNinety.bracketed.stageForProduct theRootOfNinety.bracketed n) m,
     ninety_is_not_past_the_high_square (theRootOfNinety.bracketed.stageForProduct theRootOfNinety.bracketed m) n⟩

--| THE TABLE'S TWO ROOTS, AS SIGNED REALS.  Eighteen and the root held; and eighteen held with the root owed.
def theUpperRoot : SignedReal := SignedReal.ofReal theNorm.bracketed
def theLowerRoot : SignedReal := ⟨Bracketed.ofNat 18, theRootOfNinety.bracketed⟩

--| The table's own polynomial, λ by λ less thirty-six λ and two hundred and thirty-four, at a signed real.
def theTablesPolynomialAt (r : SignedReal) : SignedReal := r * r - SignedReal.ofNat 36 * r + SignedReal.ofNat 234

end Meanings
