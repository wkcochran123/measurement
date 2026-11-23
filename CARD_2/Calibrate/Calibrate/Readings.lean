/-
The readings, as Mathlib reads them.

Meanings says a kind, up to its reader, corresponds to the naturals, the integers or the ratios: a way there and a way back,
and the operations carried across.  Mathlib has a name for exactly that, `≃+*`: an equivalence that carries sums and
products.  Here each correspondence is handed to Mathlib under that name.  Nothing is proved about the device here that
Episode 13 had not already proved; Mathlib only checks the name fits.
-/
import Mathlib.Algebra.Ring.Equiv
import Meanings

namespace Calibrate
open Meanings

universe u

section counted
variable {α : Type u} [Add α] [Mul α] [Sub α] [LT α] [CountedAsNat α]

--| Counted as the naturals, read as Mathlib's: the reading up to the count is the naturals, as a ring.
def countedRingEquiv : CountedAsNat.ReadAsNat α ≃+* ℕ where
  toFun     := CountedAsNat.correspondence.there
  invFun    := CountedAsNat.correspondence.back
  left_inv  := CountedAsNat.correspondence.there_then_back
  right_inv := CountedAsNat.correspondence.back_then_there
  map_mul'  := CountedAsNat.there_multiplies
  map_add'  := CountedAsNat.there_adds

--| And the order goes across: less is less.
theorem counted_less (x y : CountedAsNat.ReadAsNat α) : x < y ↔ countedRingEquiv x < countedRingEquiv y :=
  CountedAsNat.there_less x y
end counted

section balanced
variable {α : Type u} [Add α] [Neg α] [Sub α] [Mul α] [BalancedAsInt α]

--| Balanced as the integers, read as Mathlib's.
def balancedRingEquiv : BalancedAsInt.ReadAsInt α ≃+* ℤ where
  toFun     := BalancedAsInt.correspondence.there
  invFun    := BalancedAsInt.correspondence.back
  left_inv  := BalancedAsInt.correspondence.there_then_back
  right_inv := BalancedAsInt.correspondence.back_then_there
  map_mul'  := BalancedAsInt.there_multiplies
  map_add'  := BalancedAsInt.there_adds

--| Ratioed as the rationals, read as Mathlib's.  This one bills choice: Lean's rationals bring it.
def ratioedRingEquiv : BalancedAsInt.ReadAsRat α ≃+* Rat where
  toFun     := BalancedAsInt.ratioCorrespondence.there
  invFun    := BalancedAsInt.ratioCorrespondence.back
  left_inv  := BalancedAsInt.ratioCorrespondence.there_then_back
  right_inv := BalancedAsInt.ratioCorrespondence.back_then_there
  map_mul'  := BalancedAsInt.there_multiplies_ratios
  map_add'  := BalancedAsInt.there_adds_ratios
end balanced

end Calibrate
