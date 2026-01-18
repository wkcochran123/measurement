import Std

namespace Measurement

universe u v w

/-- Things in real life take up space, unlike abstract entities in a set. -/
class Size (R : Type v) where
  size : R -> Nat

/-- A recursive ledger: either empty, or it has a last entry and a previous
ledger. All accessors can be defined by recursion on `prev`. -/
class Ledger (L : Type u) (R : Type v) where
  /-- Base case witness. -/
  empty : L

  /-- Decide emptiness. -/
  isEmpty : L -> Bool

  /-- The last entry, if any (the "back"). -/
  entry : L -> Option R

  /-- The previous ledger state (the "pop"). -/
  prev : L -> Option L

  /-- Coherence laws for the recursion. -/
  empty_isEmpty : isEmpty empty = true
  empty_entry   : entry empty = none
  empty_prev    : prev empty = none

  /-- If not empty, we can step back. -/
  prev_of_nonempty :
    forall Lt : L, isEmpty Lt = false -> exists Lp : L, prev Lt = some Lp

  /-- Default recursive size: number of steps to empty. -/
  size : L -> Nat :=
    fun Lt =>
      let rec go (k : Nat) (cur : L) : Nat :=
        if isEmpty cur = true then
          k
        else
          match prev cur with
          | some p => go (k + 1) p
          | none   => k  -- should not happen if prev_of_nonempty holds
      go 0 Lt

  /-- Default recursive get: 0 means last entry, then walk prev. -/
  get : L -> Nat -> Option R :=
    fun Lt n =>
      let rec go_get (cur : L) (m : Nat) : Option R :=
        match m with
        | 0 =>
            entry cur
        | m + 1 =>
            match prev cur with
            | some p => go_get p m
            | none   => none
      go_get Lt n

  push : L -> R -> L





/-- Definition 2: Partially Ordered Set -/
class Poset (L : Type u) (R : Type v) [Ledger L R] where
  prec : L -> R -> R -> Prop

notation:50 a " ≺ " b => Poset a b

/-- Definition 3: Time Series -/
class TimeSeries (S : Type u) (T : Type v) (α : Type w) where
  get? : S -> Nat -> Option α

end Measurement
