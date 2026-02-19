import Measurement.Chapter7

namespace Measurement

structure Trial (σ : Type u) (τ : Type (u+1)) where
  reading: Enumeration (Number σ τ)
  average: Enumeration (Invariant σ τ)
  dispersion: Enumeration (Invariant σ τ)

structure Study (σ : Type u) (τ : Type (u+1)) where
  evidence: Enumeration (Trial σ τ)
  distribution: Representation (Invariant σ τ)

structure BayesPredictor (σ : Type u) (τ : Type (u+1)) where
  prior: Study σ τ
  likelihood: Representation (Invariant σ τ)
  posterior: Representation (Invariant σ τ)

structure Hypothesis (σ : Type u) (τ : Type (u+1)) where
  predictor: BayesPredictor σ τ
  confidence: Number σ τ

end Measurement
