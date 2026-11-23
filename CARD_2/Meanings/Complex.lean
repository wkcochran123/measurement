/-
The complex numbers, with no choice: a pair of signed reals.

A complex number is two signed reals, one along and one across.  Beside is beside, part by part.  Each for each: along
by along, less across by across, is along; along by across and across by along is across.  The quarter turn is nothing
along and one across, and by itself it is one owed.  So the turn that two of make a whole turn owed is written, and the
polynomial of the table turned over, whose gap squared is under nothing, has its two roots here: eighteen along and the
root of ninety across, held or owed.
-/
import Meanings.Signed

namespace Meanings

--| ALONG AND ACROSS.
structure ComplexReal where
  along : SignedReal
  across : SignedReal

namespace ComplexReal

def ofSigned (x : SignedReal) : ComplexReal := ⟨x, SignedReal.ofNat 0⟩
def ofNat (k : Nat) : ComplexReal := ofSigned (SignedReal.ofNat k)

instance : Add ComplexReal := ⟨fun z w => ⟨z.along + w.along, z.across + w.across⟩⟩
instance : Neg ComplexReal := ⟨fun z => ⟨-z.along, -z.across⟩⟩
instance : Sub ComplexReal := ⟨fun z w => ⟨z.along - w.along, z.across - w.across⟩⟩
instance : Mul ComplexReal :=
  ⟨fun z w => ⟨z.along * w.along - z.across * w.across, z.along * w.across + z.across * w.along⟩⟩

--| Turned across the line: the across owed.
def conjugate (z : ComplexReal) : ComplexReal := ⟨z.along, -z.across⟩

def Same (z w : ComplexReal) : Prop := z.along.Same w.along ∧ z.across.Same w.across

def HoldsNothingAt (z : ComplexReal) (n : Nat) : Prop := z.along.HoldsNothingAt n ∧ z.across.HoldsNothingAt n
instance (z : ComplexReal) (n : Nat) : Decidable (z.HoldsNothingAt n) := inferInstanceAs (Decidable (_ ∧ _))

--| THE QUARTER TURN: nothing along, one across.
def quarterTurn : ComplexReal := ⟨SignedReal.ofNat 0, SignedReal.ofNat 1⟩

end ComplexReal

--| THE QUARTER TURN, TWICE, IS ONE OWED.  Every wall here is a whole number, the same at every stage, so the walls are read
--| off at any two stages alike.
theorem the_quarter_turn_twice_is_one_owed :
    (ComplexReal.quarterTurn * ComplexReal.quarterTurn).Same (-ComplexReal.ofNat 1) :=
  ⟨fun _ _ => ⟨Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl⟩,
   fun _ _ => ⟨Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl⟩⟩

--| THE TABLE TURNED OVER, AND ITS ROOTS.  Its polynomial is λ by λ less thirty-six λ and four hundred and fourteen.
def theTurnedPolynomialAt (z : ComplexReal) : ComplexReal :=
  z * z - ComplexReal.ofNat 36 * z + ComplexReal.ofNat 414

--| Eighteen along and the root of ninety across, held; and the same with the across owed.
def theTurnedRoot : ComplexReal := ⟨SignedReal.ofNat 18, SignedReal.ofReal theRootOfNinety.bracketed⟩
def theOtherTurnedRoot : ComplexReal := theTurnedRoot.conjugate

end Meanings
