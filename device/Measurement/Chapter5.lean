import Measurement.Chapter4

namespace Measurement

universe u v w


structure Map (σ : Type u)
    (O : Type u → Type u → Type (u+1)) where
  domain : σ
  range : O σ σ


structure Model (σ : Type u) (τ : Type (u+1)) : Type (max u v +2) where
  next_step: Indirection (σ × τ)
  representation : Invariant (σ × τ) (next_step.after)




end Measurement
