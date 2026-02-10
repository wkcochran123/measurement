import Measurement.Chapter2.Propositions

namespace Measurement

structure Inversion (σ : Type u) (τ : Type v) where
  inv : Decomposition τ σ

namespace Inversion

def eta {σ : Type u} {τ : Type v} (I : Inversion σ τ) : Nat → Option (τ × σ) :=
  fun n => Enumeration.nth I.inv.pairs n   -- adjust field name

end Inversion

namespace Enumeration

/-- Map a function over an enumeration. -/
def map {A : Type u} {B : Type v} (f : A → B) : Enumeration A → Enumeration B
  | .nil        => .nil
  | .cons a as  => .cons (f a) (map f as)

def findMap? {A : Type u} {B : Type v} (f : A → Option B) : Enumeration A → Option B
  | .nil        => none
  | .cons a as  =>
      match f a with
      | some b => some b
      | none   => findMap? f as

/-- `indexOf`, but using a user-supplied equality test instead of `DecidableEq`. -/
def indexOfBy {A : Type u} (eqb : A → A → Bool) : Enumeration A → A → Option Nat
  | .nil,        _ => none
  | .cons a as,  x =>
      if eqb a x then
        some 0
      else
        Option.map Nat.succ (indexOfBy eqb as x)


end Enumeration

namespace Decomposition

/-- Swap the components of each pair in a decomposition. -/
def inverse {σ : Type u} {τ : Type v} (D : Decomposition σ τ) : Decomposition τ σ :=
{ pairs :=
    D.pairs.map (fun p : (σ × τ) => (p.2, p.1)) }

def read? {σ : Type u} {τ : Type v} [DecidableEq σ]
    (D : Decomposition σ τ) (s : σ) : Option τ :=
  none

/-- Decode along a decomposition by searching the enumerated pairs. -/
def decode? {τ : Type u} {σ : Type v} [DecidableEq τ]
    (D : Decomposition τ σ) (t : τ) : Option σ :=
  Enumeration.findMap?
    (fun p : (τ × σ) =>
      if h : p.1 = t then
        some p.2
      else
        none)
    D.pairs

end Decomposition

end Measurement
