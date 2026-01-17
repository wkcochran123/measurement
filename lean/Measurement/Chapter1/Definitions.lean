import Std

namespace Measurement

universe u v w

/-- Definition 1: Ledger
-/
class Ledger (L : Type u) (R : Type v) where
  entries : L -> Array R


/-- Definition 2: Partially Ordered Set -/
class Poset (L : Type u) (R : Type v) [Ledger L R] where
  prec : L -> R -> R -> Prop

notation:50 a " ≺ " b => Poset a b

/-- Definition 3: Time Series -/
class TimeSeries (S : Type u) (T : Type v) (α : Type w) where
  get? : S -> Nat -> Option α

end Measurement
