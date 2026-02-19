import Measurement.Chapter8

namespace Measurement

structure Limit (σ : Type u) (τ : Type (u+1)) where
  sequence: Enumeration (Invariant σ τ)
  limit: Invariant σ τ

structure CantorDecomposition (σ : Type u) (τ : Type (u+1)) where
  left: Enumeration (Invariant σ τ)
  right: Enumeration (Invariant σ τ)

structure CauchySequence (σ : Type u) (τ : Type (u+1)) where
  terms: Limit σ τ
  limit: CantorDecomposition σ τ

structure RealNumber (σ : Type u) (τ : Type (u+1)) where
  value: Hypothesis σ τ
  representation: CauchySequence σ τ


end Measurement
