import Std

namespace Entropy

universe u v w

/-- Poset-like: a type equipped with a precedence relation. -/
class PosetLike (α : Type u) where
  prec : α -> α -> Prop

notation:50 a " ≺ " b => PosetLike.prec a b

/-- Ledger-like: a finite ordered record of readings. -/
class LedgerLike (L : Type u) (R : Type v) where
  entries : L -> Array R

/-- Time-series-like: values indexed by a time or index type. -/
class TimeSeriesLike (S : Type u) (T : Type v) (α : Type w) where
  get : S -> T -> α

end Entropy
