import Measurement.Chapter4

namespace Measurement

universe u v w

structure TemporalVariation
  (A : Type u → Type v → Type w)
  (B : Type (u+1) → Type (v+1) → Type w')
  (σ  : Type u) (τ  : Type v)
  (σ' : Type (u+1)) (τ' : Type (v+1)) where
  left  : A σ τ
  right : B σ' τ'

structure PhenomenalVariation
  (A : Type u → Type v → Type w)
  (σ : Type u) (τ : Type v) where
  left  : A σ τ
  right : A σ τ

structure MixedVariation (A : Type u → Type v → Type w)
  (A : Type u → Type v → Type w)
  (B : Type (u+1) → Type (v+1) → Type w')
  (σ  : Type u) (τ  : Type v)
  (σ' : Type (u+1)) (τ' : Type (v+1)) where

  timelike: TemporalVariation A B σ τ σ' τ'
  spacelike: PhenomenalVariation A σ τ




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

namespace DotProduct

noncomputable def correlance {σ : Type u} {τ : Type v}
    [DecidableEq σ] [DecidableEq τ]
    (DP : DotProduct σ τ) (x : σ) : Option Bool :=
  match (Kernel.phi DP.kernel x, DP.vector.range.admissible x) with
  | (some (_, y₁), some y₂) => some (decide (y₁ = y₂))
  | _                       => none

end DotProduct

structure Projection (σ : Type u) (τ : Type v) where
  dot: DotProduct σ τ
  manifold: Manifold τ τ

namespace Projection
  noncomputable def project {σ : Type u} {τ : Type v} [DecidableEq σ] [DecidableEq τ]
    (P : Projection σ τ) (x : σ) : Option Bool := P.dot.correlance x

end Projection

abbrev LorentzProjection (σ : Type u) := Projection σ σ

abbrev CantorProjection := Projection Nat ℚ
abbrev CauchyProjection := Projection ℚ ℝ

/-- If the required ingredients exist, then the projections exist. -/
theorem cantor_exists
  (dot : DotProduct Nat ℚ) (man : Manifold ℚ ℚ) :
  ∃ P : CantorProjection, True :=
by
  refine ⟨{ dot := dot, manifold := man }, trivial⟩

theorem cauchy_exists
  (dot : DotProduct ℚ ℝ) (man : Manifold ℝ ℝ) :
  ∃ P : CauchyProjection, True :=
by
  refine ⟨{ dot := dot, manifold := man }, trivial⟩


end Measurement
