import Measurement.Chapter4

namespace Measurement

universe u v w

structure Partition (σ : Type u) (τ : Type v) where
  key : σ
  fiber : (σ × τ) → Alphabet σ

structure Kernel (σ : Type u) (τ : Type v) where
  space: Partition σ τ
  injection: Inversion σ τ

structure DotProduct (σ : Type u) (τ : Type v) where
  kernel : Kernel σ τ
  vector : Manifold σ τ

structure Variation (σ : Type u) (τ : Type (u+1)) where
  step: ArrowOfTime σ τ
  norm: DotProduct σ τ


namespace Partition
  def representative {σ : Type u} {τ : Type v} (P : Partition σ τ) : σ :=
  P.key
end Partition

namespace Kernel

  noncomputable def φ {σ : Type u} {τ : Type v}
    [DecidableEq σ]
    (K : Kernel σ τ) (x : σ) : Option (Alphabet σ × τ) :=
  match K.injection.inv.inverse.decode? x with
  | none      => none
  | some y    =>
      let lbl : σ × τ := (x, y)
      some (K.space.fiber lbl, y)

end Kernel

namespace DotProduct

noncomputable def correlance {σ : Type u} {τ : Type v}
    [DecidableEq σ] [DecidableEq τ]
    (DP : DotProduct σ τ) (x : σ) : Option Bool :=
  match (Kernel.φ DP.kernel x, DP.vector.range.admissible x) with
  | (some (_, y₁), some y₂) => some (decide (y₁ = y₂))
  | _                       => none

noncomputable def project {σ : Type u} {τ : Type v} [DecidableEq σ] [DecidableEq τ]
  (DP : DotProduct σ τ) (x : σ) : Option Bool := DotProduct.correlance DP x
end DotProduct



noncomputable def Variation.succ {σ : Type u} {τ : Type (u+1)}
    [DecidableEq σ] [DecidableEq τ]
    (V : Variation σ τ) (x : σ) : Option τ :=
  let rep := V.norm.kernel.space.representative

  match DotProduct.project V.norm rep with
  | some true =>
      V.step.elapse
  | _ =>
      none


/-- Law of Bit Sufficiency?-/
abbrev Prediction := Variation Nat (ULift Nat)

end Measurement
