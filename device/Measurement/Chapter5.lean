import Measurement.Chapter4

namespace Measurement

structure Partition (σ : Type u) (τ : Type v) where
  key : σ
  fiber : (σ × τ) → Alphabet σ


structure Kernel (σ : Type u) (τ : Type v) where
  space: Partition σ τ
  injection: Inversion σ τ

namespace Kernel

  noncomputable def phi {σ : Type u} {τ : Type v}
    [DecidableEq σ]
    (K : Kernel σ τ) (x : σ) : Option (Alphabet σ × τ) :=
  match K.injection.inv.inverse.decode? x with
  | none      => none
  | some y    =>
      let lbl : σ × τ := (x, y)
      some (K.space.fiber lbl, y)

end Kernel

structure DotProduct (σ : Type u) (τ : Type v) where
  kernel : Kernel σ τ
  vector : Manifold σ τ

end Measurement
