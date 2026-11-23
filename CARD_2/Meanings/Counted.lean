/-
Counted as the naturals.

A kind is counted as the naturals when a reader takes each thing to a natural, set beside is added, each for each is
multiplied, taken away is taken away and stops at nothing, less is less, and every natural can be dealt.  Then the kind,
taken up to its count, corresponds to the naturals, and the four operations go across.

Nothing here says the things are numbers.  Two things with one count are different things.  Only what the reader keeps is
the naturals.
-/
import Meanings.Correspondence

namespace Meanings
universe u

--| THE INTERFACE.  A count, a deal that the count undoes, and the four operations read as the naturals' own.
class CountedAsNat (α : Type u) [Add α] [Mul α] [Sub α] [LT α] where
  count : α → Nat
  deal : Nat → α
  count_deal : ∀ n, count (deal n) = n
  adds : ∀ a b, count (a + b) = count a + count b
  multiplies : ∀ a b, count (a * b) = count a * count b
  subtracts : ∀ a b, count (a - b) = count a - count b
  less : ∀ a b, a < b ↔ count a < count b

namespace CountedAsNat
variable (α : Type u) [Add α] [Mul α] [Sub α] [LT α] [CountedAsNat α]

--| Two things are read alike when they have one count.
def byCount : Setoid α := ⟨fun a b => count a = count b, ⟨fun _ => rfl, fun h => h.symm, fun h k => h.trans k⟩⟩

--| The kind as the reader keeps it.
def ReadAsNat : Type u := Quotient (byCount α)

variable {α}

--| The reading of a thing kept.
def keep (a : α) : ReadAsNat α := Quotient.mk (byCount α) a

instance : Add (ReadAsNat α) :=
  ⟨Quotient.lift₂ (s₁ := byCount α) (s₂ := byCount α) (fun a b => keep (a + b))
    (fun a b a' b' (ha : count a = count a') (hb : count b = count b') =>
      Quotient.sound (s := byCount α) (show count (a + b) = count (a' + b') by rw [adds, adds, ha, hb]))⟩
instance : Mul (ReadAsNat α) :=
  ⟨Quotient.lift₂ (s₁ := byCount α) (s₂ := byCount α) (fun a b => keep (a * b))
    (fun a b a' b' (ha : count a = count a') (hb : count b = count b') =>
      Quotient.sound (s := byCount α) (show count (a * b) = count (a' * b') by rw [multiplies, multiplies, ha, hb]))⟩
instance : Sub (ReadAsNat α) :=
  ⟨Quotient.lift₂ (s₁ := byCount α) (s₂ := byCount α) (fun a b => keep (a - b))
    (fun a b a' b' (ha : count a = count a') (hb : count b = count b') =>
      Quotient.sound (s := byCount α) (show count (a - b) = count (a' - b') by rw [subtracts, subtracts, ha, hb]))⟩
instance : LT (ReadAsNat α) :=
  ⟨fun x y => Quotient.lift₂ (s₁ := byCount α) (s₂ := byCount α) (fun a b => a < b)
    (fun a b a' b' (ha : count a = count a') (hb : count b = count b') =>
      propext ((less a b).trans (by rw [ha, hb]; exact (less a' b').symm))) x y⟩

--| THE CORRESPONDENCE.  There is the count; back is the deal.
def toNat : ReadAsNat α → Nat := Quotient.lift (s := byCount α) count (fun _ _ h => h)

def correspondence : Correspondence (ReadAsNat α) Nat where
  there := toNat
  back n := keep (deal n)
  there_then_back := fun x => Quotient.inductionOn x (fun a => Quotient.sound (s := byCount α) (count_deal (count a)))
  back_then_there := count_deal

--| And the four operations go across.
theorem there_adds (x y : ReadAsNat α) : toNat (x + y) = toNat x + toNat y :=
  Quotient.inductionOn₂ x y (fun a b => adds a b)
theorem there_multiplies (x y : ReadAsNat α) : toNat (x * y) = toNat x * toNat y :=
  Quotient.inductionOn₂ x y (fun a b => multiplies a b)
theorem there_subtracts (x y : ReadAsNat α) : toNat (x - y) = toNat x - toNat y :=
  Quotient.inductionOn₂ x y (fun a b => subtracts a b)
theorem there_less (x y : ReadAsNat α) : x < y ↔ toNat x < toNat y :=
  Quotient.inductionOn₂ x y (fun a b => less a b)

end CountedAsNat
end Meanings
