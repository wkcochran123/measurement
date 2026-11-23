/-
Balanced as the integers.

A kind is balanced as the integers when a reader takes each thing to an integer, set beside is added, turned over is
negated, less is less, each for each is multiplied, and every integer can be dealt.  Then the kind, taken up to its
balance, corresponds to the integers, and the operations go across.
-/
import Meanings.Correspondence

namespace Meanings
universe u

--| THE INTERFACE.  A balance, a deal that the balance undoes, and the operations read as the integers' own.
class BalancedAsInt (α : Type u) [Add α] [Neg α] [Sub α] [Mul α] where
  balance : α → Int
  deal : Int → α
  balance_deal : ∀ z, balance (deal z) = z
  adds : ∀ a b, balance (a + b) = balance a + balance b
  negates : ∀ a, balance (-a) = - balance a
  subtracts : ∀ a b, balance (a - b) = balance a - balance b
  multiplies : ∀ a b, balance (a * b) = balance a * balance b

namespace BalancedAsInt
variable (α : Type u) [Add α] [Neg α] [Sub α] [Mul α] [BalancedAsInt α]

--| Two things are read alike when they have one balance.
def byBalance : Setoid α := ⟨fun a b => balance a = balance b, ⟨fun _ => rfl, fun h => h.symm, fun h k => h.trans k⟩⟩

--| The kind as the reader keeps it.
def ReadAsInt : Type u := Quotient (byBalance α)

variable {α}

def keep (a : α) : ReadAsInt α := Quotient.mk (byBalance α) a

instance : Add (ReadAsInt α) :=
  ⟨Quotient.lift₂ (s₁ := byBalance α) (s₂ := byBalance α) (fun a b => keep (a + b))
    (fun a b a' b' (ha : balance a = balance a') (hb : balance b = balance b') =>
      Quotient.sound (s := byBalance α) (show balance (a + b) = balance (a' + b') by rw [adds, adds, ha, hb]))⟩
instance : Neg (ReadAsInt α) :=
  ⟨Quotient.lift (s := byBalance α) (fun a => keep (-a))
    (fun a a' (ha : balance a = balance a') =>
      Quotient.sound (s := byBalance α) (show balance (-a) = balance (-a') by rw [negates, negates, ha]))⟩
instance : Sub (ReadAsInt α) :=
  ⟨Quotient.lift₂ (s₁ := byBalance α) (s₂ := byBalance α) (fun a b => keep (a - b))
    (fun a b a' b' (ha : balance a = balance a') (hb : balance b = balance b') =>
      Quotient.sound (s := byBalance α) (show balance (a - b) = balance (a' - b') by rw [subtracts, subtracts, ha, hb]))⟩
instance : Mul (ReadAsInt α) :=
  ⟨Quotient.lift₂ (s₁ := byBalance α) (s₂ := byBalance α) (fun a b => keep (a * b))
    (fun a b a' b' (ha : balance a = balance a') (hb : balance b = balance b') =>
      Quotient.sound (s := byBalance α) (show balance (a * b) = balance (a' * b') by rw [multiplies, multiplies, ha, hb]))⟩

--| THE CORRESPONDENCE.  There is the balance; back is the deal.
def toInt : ReadAsInt α → Int := Quotient.lift (s := byBalance α) balance (fun _ _ h => h)

def correspondence : Correspondence (ReadAsInt α) Int where
  there := toInt
  back z := keep (deal z)
  there_then_back := fun x => Quotient.inductionOn x (fun a => Quotient.sound (s := byBalance α) (balance_deal (balance a)))
  back_then_there := balance_deal

theorem there_adds (x y : ReadAsInt α) : toInt (x + y) = toInt x + toInt y :=
  Quotient.inductionOn₂ x y (fun a b => adds a b)
theorem there_negates (x : ReadAsInt α) : toInt (-x) = - toInt x :=
  Quotient.inductionOn x (fun a => negates a)
theorem there_subtracts (x y : ReadAsInt α) : toInt (x - y) = toInt x - toInt y :=
  Quotient.inductionOn₂ x y (fun a b => subtracts a b)
theorem there_multiplies (x y : ReadAsInt α) : toInt (x * y) = toInt x * toInt y :=
  Quotient.inductionOn₂ x y (fun a b => multiplies a b)

end BalancedAsInt
end Meanings
