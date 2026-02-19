import Measurement.Chapter6


namespace Measurement

structure Indirection (σ : Type u) (τ : Type (u+1)) where
  model : Inversion σ τ
  step  : Indirection σ τ

structure RationalNumber (σ : Type u) (τ : Type (u+1)) where
  numerator: NaturalNumbers
  denominator: NaturalNumbers

structure Representation (A : Type u) where
  physical : Decomposition A A
  metaphysical : Enumeration A

structure Number (σ : Type u) (τ : Type (u+1)) where
  symbol: Representation (RationalNumber σ τ)
  value: RationalNumber σ τ

structure Ring (σ : Type u) (τ : Type (u+1)) where
  left: Number σ τ
  right: Number σ τ



end Measurement
