import Measurement.Chapter9

namespace Measurement

structure Flattening (σ : Type u) (τ : Type (u+1)) where
  options: Enumeration (Walking σ τ)
  selector: PartialOrder σ τ

structure Poset (σ : Type u) (τ : Type (u+1)) where
  ordering: Flattening σ τ
  elements: Enumeration σ

structure Hierarchy (σ : Type u) (τ : Type (u+1)) where
  time: CauchySequence σ τ
  distance: CantorDecomposition σ τ

structure Regime (σ : Type u) (τ : Type (u+1)) where
  poset: Poset σ τ
  hierarchy: Hierarchy σ τ


namespace Walking

-- "Computational equality": ignore poset, compare only enumerated events.
def equiv [DecidableEq (Event σ τ)] (W1 W2 : Walking σ τ) : Prop :=
  W1.candidates = W2.candidates

end Walking

end Measurement
