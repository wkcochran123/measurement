/-
Ratioed as the rationals.

Nothing more is asked.  Whatever is balanced as the integers gives ratios for free: a pair of things, the second with a
balance that is not nothing, and two pairs read alike when their balances cross-multiply to one integer.  Taken up to
that, the pairs correspond to the rationals, and beside and each for each go across.

The crossing is an equality.  Read with less-or-equal instead, every pair is alike every other, because one of the two
ways round always holds, and the reading has one point.
-/
import Meanings.Balanced

namespace Meanings
namespace BalancedAsInt
universe u
variable {α : Type u} [Add α] [Neg α] [Sub α] [Mul α] [BalancedAsInt α]

--| A ratio: a thing over a thing whose balance is not nothing.
structure Ratio (α : Type u) [Add α] [Neg α] [Sub α] [Mul α] [BalancedAsInt α] where
  over  : α
  under : α
  under_is_something : balance under ≠ 0

--| What the reader makes of a ratio.
def Ratio.read (r : Ratio α) : Rat := Rat.divInt (balance r.over) (balance r.under)

--| Two ratios are alike when they cross-multiply to one integer.  That is the same as being read as one rational.
def Ratio.crossed (r s : Ratio α) : Prop := balance r.over * balance s.under = balance s.over * balance r.under

theorem Ratio.crossed_is_read_alike (r s : Ratio α) : r.crossed s ↔ r.read = s.read :=
  (Rat.divInt_eq_divInt_iff r.under_is_something s.under_is_something).symm

variable (α) in
def byCrossing : Setoid (Ratio α) :=
  ⟨Ratio.crossed, ⟨fun r => (Ratio.crossed_is_read_alike r r).2 rfl,
    fun h => (Ratio.crossed_is_read_alike _ _).2 ((Ratio.crossed_is_read_alike _ _).1 h).symm,
    fun h k => (Ratio.crossed_is_read_alike _ _).2 (((Ratio.crossed_is_read_alike _ _).1 h).trans
      ((Ratio.crossed_is_read_alike _ _).1 k))⟩⟩

variable (α) in
--| The ratios as the reader keeps them.
def ReadAsRat : Type u := Quotient (byCrossing α)

def Ratio.keep (r : Ratio α) : ReadAsRat α := Quotient.mk (byCrossing α) r

--| Beside: over by under and over by under, under by under.  Each for each: over by over, under by under.
def Ratio.add (r s : Ratio α) : Ratio α :=
  ⟨r.over * s.under + s.over * r.under, r.under * s.under,
    by rw [multiplies]; exact Int.mul_ne_zero r.under_is_something s.under_is_something⟩
def Ratio.mul (r s : Ratio α) : Ratio α :=
  ⟨r.over * s.over, r.under * s.under,
    by rw [multiplies]; exact Int.mul_ne_zero r.under_is_something s.under_is_something⟩

theorem Ratio.read_add (r s : Ratio α) : (r.add s).read = r.read + s.read := by
  simp only [Ratio.read, Ratio.add, adds, multiplies]
  rw [Rat.divInt_add_divInt _ _ r.under_is_something s.under_is_something]
theorem Ratio.read_mul (r s : Ratio α) : (r.mul s).read = r.read * s.read := by
  simp only [Ratio.read, Ratio.mul, multiplies]
  rw [Rat.divInt_mul_divInt]

instance : Add (ReadAsRat α) :=
  ⟨Quotient.lift₂ (s₁ := byCrossing α) (s₂ := byCrossing α) (fun r s => Ratio.keep (r.add s))
    (fun r s r' s' hr hs => Quotient.sound (s := byCrossing α) ((Ratio.crossed_is_read_alike _ _).2 (by
      rw [Ratio.read_add, Ratio.read_add, (Ratio.crossed_is_read_alike r r').1 hr,
        (Ratio.crossed_is_read_alike s s').1 hs])))⟩
instance : Mul (ReadAsRat α) :=
  ⟨Quotient.lift₂ (s₁ := byCrossing α) (s₂ := byCrossing α) (fun r s => Ratio.keep (r.mul s))
    (fun r s r' s' hr hs => Quotient.sound (s := byCrossing α) ((Ratio.crossed_is_read_alike _ _).2 (by
      rw [Ratio.read_mul, Ratio.read_mul, (Ratio.crossed_is_read_alike r r').1 hr,
        (Ratio.crossed_is_read_alike s s').1 hs])))⟩

--| THE CORRESPONDENCE.  There is the reading; back deals the numerator over the denominator.
def toRat : ReadAsRat α → Rat :=
  Quotient.lift (s := byCrossing α) Ratio.read (fun _ _ h => (Ratio.crossed_is_read_alike _ _).1 h)

def dealRatio (q : Rat) : Ratio α :=
  ⟨deal q.num, deal (q.den : Int), by rw [balance_deal]; exact Int.natCast_ne_zero.mpr q.den_nz⟩

theorem dealRatio_read (q : Rat) : (dealRatio (α := α) q).read = q := by
  simp only [Ratio.read, dealRatio, balance_deal]
  exact Rat.num_divInt_den q

def ratioCorrespondence : Correspondence (ReadAsRat α) Rat where
  there := toRat
  back q := Ratio.keep (dealRatio q)
  there_then_back := fun x => Quotient.inductionOn x (fun r =>
    Quotient.sound (s := byCrossing α) ((Ratio.crossed_is_read_alike _ _).2 (dealRatio_read r.read)))
  back_then_there := dealRatio_read

theorem there_adds_ratios (x y : ReadAsRat α) : toRat (x + y) = toRat x + toRat y :=
  Quotient.inductionOn₂ x y (fun r s => Ratio.read_add r s)
theorem there_multiplies_ratios (x y : ReadAsRat α) : toRat (x * y) = toRat x * toRat y :=
  Quotient.inductionOn₂ x y (fun r s => Ratio.read_mul r s)

end BalancedAsInt
end Meanings
