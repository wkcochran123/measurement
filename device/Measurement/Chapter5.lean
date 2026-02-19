import Measurement.Chapter4

namespace Measurement

universe u v w

structure Partition (σ : Type u) (τ : Type (u+1)) where
  key : σ
  fiber : (σ × τ) → Alphabet σ

structure Kernel (σ : Type u) (τ : Type (u+1)) where
  space:     Partition σ τ
  injection: Decomposition σ τ

structure Manifold (σ : Type u) (τ : Type (u+1)) where
  domain: PartialOrder σ τ
  range: Invariant σ τ
  map: σ → Option σ

structure InnerProduct (σ : Type u) (τ : Type (u+1)) where
  kernel : Kernel σ τ
  vector : Manifold σ τ





namespace Partition

  def representative {σ : Type u} {τ : Type (u+1)} (P : Partition σ τ) : σ :=
  P.key

end Partition


namespace Kernel

  noncomputable def φ {σ : Type u} {τ : Type (u+1)}
    [DecidableEq σ]
    [DecidableEq τ]
    (K : Kernel σ τ) (x : σ) : Option (Alphabet σ × τ) :=
  match K.injection.decode? x with
  | none      => none
  | some y    =>
      let lbl : σ × τ := (x, y)
      some (K.space.fiber lbl, y)

end Kernel

namespace DotProduct

noncomputable def correlance {σ : Type u} {τ : Type (u+1)}
    [DecidableEq σ] [DecidableEq τ]
    (DP : InnerProduct σ τ) (x : τ) : Option Bool :=
  match DP.vector.range.model.inv.decode? x with
  | none => none                     -- no preimage exists → not correlant
  | some preimage =>                 -- preimage : σ
      match (Kernel.φ DP.kernel preimage, DP.vector.range.admissible x) with
      | (some (_, y₁), some y₂) => some (decide (y₁ = y₂))
      | _                       => none

end DotProduct





namespace Event

noncomputable def value (e : Event σ τ) (x : ℝ) : Option σ :=
  if _h : (0 < x ∧ x ≤ 1) then
    some e.state
  else
    none

end Event



end Measurement
