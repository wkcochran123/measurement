import Std

import Measurement.Chapter3.Constructions

namespace Measurement

universe u v

namespace Ledger

variable {X : Type u}

/--
Find the first index of `x` in the ledger.
Indexing: 0=head, 1.. in tail.
-/
def find [DecidableEq X] (L : Ledger X) (x : X) : Option Nat :=
  if L.head = x then
    some 0
  else
    let rec go : Enumeration X -> Nat -> Option Nat
      | .nil,        _ => none
      | .cons y ys,  i =>
          if y = x then some i else go ys (i + 1)
    go L.tail 1

/--
Find the first index whose projected symbol equals `sym`.
Indexing: 0=head, 1.. in tail.
-/
def find_symbol {σ : Type v} [DecidableEq σ]
    (L : Ledger X) (proj : X -> σ) (sym : σ) : Option Nat :=
  if proj L.head = sym then
    some 0
  else
    let rec go : Enumeration X -> Nat -> Option Nat
      | .nil,        _ => none
      | .cons y ys,  i =>
          if proj y = sym then some i else go ys (i + 1)
    go L.tail 1

end Ledger

structure CoarseningMap (σ : Type u) where
  coarsen : σ -> Option σ

/-- Definition 13: Grid map. -/
structure GridMap where
  grid : Nat -> Option Nat

/-- Definition 14: A record coarsening map. -/
def RecordCoarseningMap (R : Type u) :=
  R -> Option R

/-- Definition 15: Dense response. -/
def DenseResponse : Type :=
  ZFC.Qpos -> Rat

/-- Definition 16: Domain response. -/
def DomainResponse : Type :=
  ZFC.Rpos -> Real


/-- Unary refinement acting on ledgers. -/
structure LedgerRefinement (R : Type u) where
  refine : Ledger R -> Ledger R

namespace LedgerRefinement

/-- Canonical cons refinement: new head, old ledger becomes the tail. -/
def consRefine {R : Type u} (new : Ledger R -> R) : LedgerRefinement R :=
  { refine := fun Lt => { head := new Lt, tail := Lt.toEnum } }

end LedgerRefinement


/-- Definition 18: Refinement Operator (unary Ledger style). -/
structure RefinementOperator (R : Type v) (X : Type w) (σ : Type u) [DecidableEq σ] where
  Rhat : LedgerRefinement R
  f : X -> R
  rhoTilde : R -> X
  proj : R -> σ

  /-- Growth: refinement adds exactly one new ledger entry. -/
  ledger_growth :
    forall Lt : Ledger R,
      Ledger.size (Rhat.refine Lt) =
        Ledger.size Lt + 1

  /-- Coherence: the refined ledger has at least one symbol (find_symbol succeeds). -/
  ledger_coherence :
    forall Lt : Ledger R,
      exists s : σ, exists n : Nat,
        Ledger.find_symbol (Rhat.refine Lt) proj s = some n

end Measurement
