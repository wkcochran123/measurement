import Std
import Entropy.Chapter1.Interfaces

namespace Entropy

universe u v

/-- A hash/encoding of values into Nat. No laws yet. -/
class HashCount (α : Type u) where
  hash : α -> Nat

/-- Records are instrument-symbol pairs (counting comes later). -/
class RecordLike (R : Type u) (I : Type v) (sigma : Type w) where
  instrument : R -> I
  symbol     : R -> sigma

class RecordOrder (R : Type u) where
  prec : R -> R -> Prop

/-- Events are finite bundles of records. -/
class EventLike (E : Type u) (R : outParam (Type v)) where
  records : E -> Array R

/-- A causal precedence relation on events. -/
class EventOrder (E : Type u) where
  prec : E -> E -> Prop

structure RefinementOperator (E : Type u) where
  refine : E → E

notation "R̂" => RefinementOperator.refine

end Entropy
