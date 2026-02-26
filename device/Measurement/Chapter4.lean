import Measurement.Chapter3

namespace Measurement


structure Indirection (σ : Type u) where
  arrow: ArrowOfTime σ

structure Event (σ : Type u) where
  description: Friction Indirection σ

structure Commutator (σ : Type u) (τ : Type (v+1)) where
  left: Distinguishable (Event σ)
  right: Friction Distinguishable (Event τ)

structure TotalVariation (σ : Type u) (τ : Type (u+1))(υ : Type (v+1)) where
  first: Indirection σ τ
  second: Commutator σ τ

abbrev Refinement (σ : Type u)(τ : Type (u+1)) := TotalVariation σ τ τ

structure CausalUniverseTensor (σ : Type u) (τ : Type (u+1)) where
  events: Ledger (Event σ)
  partitions: Numbering (Commutator σ τ)
  variations: Numbering (Refinement σ τ)




end Measurement
