import Std

import Measurement.Chapter1.Definitions
import Measurement.Chapter2.Constructions

namespace Measurement

universe u v

/-- Definition 4: Alphabet -/
class Alphabet (S : Type u) (σ : Type v) where
  get : S -> Nat -> σ
  index : S -> σ -> Nat


/-- Definition 5: Refinement -/
structure Refinement (S: Type u) where
  refine: S -> S


/-- Definition 6: Structure -/
structure Record where
  a : Nat
  b : Nat
  c : Nat



/-- Definition 7: Moment -/
abbrev Moment (t : Real) : Type :=
  { u : Real // u ∈ ZFC.unitIocAt t } -> Real


/-- Definition 8: Representational Map -/
class Representation (σ : Type u) (X : Type v) where
  encode : X -> σ
  decode : σ -> X


/-- Definition 9: Predition Map -/
class Prediction (X : Type u) (Y : Type v) where
  predict : X -> Y


/-- Definition 10: Event -/
structure Event where
  records : ZFC.FiniteSet Record

/-- Definition 11: Phenomenon -/
structure Phenomenon where
  events : ZFC.FiniteSet Event

/-- Definition 12: Coarsening map-/
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

/-- Definition 17: History -/
structure History where
  events : Array Event


/-- Definition 18: Refinement Operator -/


structure RefinementOperator
    (L : Type u) (R : Type v) (X : Type w) [Ledger L R] where
  /-- The underlying refinement (Definition 5). -/
  Rhat : Refinement L

  /-- Prediction map f. -/
  f : X -> R

  /-- Representation map rhoTilde. -/
  rhoTilde : R -> X

  /-- Growth: refinement adds exactly one new ledger entry. -/
  ledger_growth :
    forall Lt : L,
      Ledger.size (L := L) (R := R) (Rhat.refine Lt) =
        Ledger.size (L := L) (R := R) Lt + 1

  ledger_coherence :
    forall Lt : L,
      exists e : R,
        Ledger.entry (L := L) (R := R) (Rhat.refine Lt) = some e



end Measurement
