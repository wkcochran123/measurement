import Measurement.Chapter3

namespace Measurement

universe u v w

/--
Definition : Parial Order

A partial order is a relation on a set that provides some indication of
"less than or equal to" between elements, but does not necessarily compare
every pair of elements.
-/

structure PartialOrder (σ : Type u) where
  poset : Enumeration (Inversion σ σ)

namespace Enumeration

/-- Walk until false; if no false encountered, return true. -/
def all {A : Type u} (p : A → Bool) : Enumeration A → Bool
  | .nil        => true
  | .cons a as  => if p a then all p as else false

/-- "Exists" helper (often useful alongside `all`). -/
def any {A : Type u} (p : A → Bool) : Enumeration A → Bool
  | .nil        => false
  | .cons a as  => if p a then true else any p as

end Enumeration

namespace Decomposition

/-- Boolean membership test for a specific pair in a decomposition. -/
def contains {σ : Type u} {τ : Type v} [DecidableEq σ] [DecidableEq τ]
    (D : Decomposition σ τ) (p : σ × τ) : Bool :=
  match Enumeration.indexOfBy (fun a b => decide (a = b)) D.pairs p with
  | some _ => true
  | none   => false

end Decomposition

namespace Inversion

/-- The inversion "admits" the ordered pair (a,b) iff it occurs in the enumerated pairs. -/
def admits {σ : Type u} [DecidableEq σ] (I : Inversion σ σ) (a b : σ) : Bool :=
  I.inv.contains (a, b)

end Inversion

namespace PartialOrder

/-- `a ≤ b` iff every inversion in the poset admits (a,b). -/
def le {σ : Type u} [DecidableEq σ] (P : PartialOrder σ) (a b : σ) : Bool :=
  Enumeration.all (fun I => Inversion.admits I a b) P.poset


/-- `y` is a bottom element among the candidates `>= x` iff:
    (1) x ≤ y, and
    (2) for every z with x ≤ z, we have y ≤ z. -/
def isCeil {σ : Type u} [DecidableEq σ]
    (P : PartialOrder σ) (xs : Enumeration σ) (x y : σ) : Bool :=
  P.le x y ∧
  Enumeration.all (fun z => if P.le x z then P.le y z else true) xs

/-- `ceil(x)`: walk the enumeration, skipping candidates with `¬(x ≤ y)`,
    return the first `y` that is bottom among all `>= x`. -/
def ceil? {σ : Type u} [DecidableEq σ]
    (P : PartialOrder σ) (xs : Enumeration σ) (x : σ) : Option σ :=
  Enumeration.findMap?
    (fun y => if P.isCeil xs x y then some y else none)
    xs

/-- `x` is bottom (least) among the enumerated candidates iff `x ≤ y` for all `y` in `xs`. -/
def isBottom {σ : Type u} [DecidableEq σ]
    (P : PartialOrder σ) (xs : Enumeration σ) (x : σ) : Bool :=
  Enumeration.all (fun y => P.le x y) xs

/-- Find the least element by walking the enumeration: first `x` with no counterexample. -/
def bottom? {σ : Type u} [DecidableEq σ]
    (P : PartialOrder σ) (xs : Enumeration σ) : Option σ :=
  Enumeration.findMap?
    (fun x => if P.isBottom xs x then some x else none)
    xs

end PartialOrder


structure Walking (σ : Type u) where
  poset : PartialOrder σ
  candidates : Enumeration σ

namespace Walking

def iterate (W : Walking σ) :
    Nat → Option (ULift σ) :=
  fun t =>
    let u' := t.succ
    match Enumeration.nth W.candidates u' with
    | none   => none
    | some s => some ⟨s⟩

end Walking


structure Calibration (σ : Type u) (τ : Type v) where
  measurment: Decomposition σ τ
  reference: Decomposition τ σ
  read : σ → Option τ

namespace Calibration

def judgeEq {σ : Type u} {τ : Type v} [DecidableEq τ]
    (C : Calibration σ τ) (a b : σ) : Bool :=
  match C.read a, C.read b with
  | some x, some y => decide (x = y)
  | _, _           => false

end Calibration


/-- Introducing Geometry!-/
structure Manifold (σ : Type u) (τ : Type v) where
  domain: PartialOrder σ
  range: Invariant σ τ
  map: σ → Option σ

namespace Manifold

noncomputable def ψ {σ : Type u} {τ : Type v} [DecidableEq σ]
    (M : Manifold σ τ) (xs : Enumeration σ) (x : σ) : Option (σ × τ) :=
  match PartialOrder.ceil? M.domain xs x with
  | none    => none
  | some x' =>
      match M.range.admissible x' with
      | none   => none
      | some y => some (x', y)

end Manifold


end Measurement
