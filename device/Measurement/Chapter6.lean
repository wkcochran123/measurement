import Measurement.Chapter5

namespace Measurement

structure Accumulation (σ : Type u) (τ : Type (u+1)) where
  numbers: Counting σ τ
  values: Enumeration (Invariant σ τ)

structure Function (σ : Type u) (τ : Type (u+1)) where
  domain: Manifold σ τ
  codomain: Accumulation σ τ

structure Integration (σ : Type u) (τ : Type (u+1)) where
  f: Function σ τ
  integral: Accumulation σ τ

structure WeakForm (σ : Type u) (τ : Type (u+1)) where
  domain: Manifold σ τ
  range:  Integration σ τ



namespace Counting
  def accumulate (C : Counting σ τ) {F: Function σ τ}: Accumulation σ τ :=
    { numbers := C
      values := F.codomain.values }
end Counting


namespace Function
  def f {σ : Type u} {τ : Type (u+1)} [DecidableEq σ] [DecidableEq τ]
    (F : Function σ τ) (_x : σ) : Counting σ τ := F.codomain.numbers

  def integrate {σ : Type u} {τ : Type (u+1)} [DecidableEq σ] [DecidableEq τ]
    (F : Function σ τ) (_x : σ) : Integration σ τ :=
    { f := F
      integral := F.codomain }
end Function

namespace Integration

  def weakForm {σ : Type u} {τ : Type (u+1)} [DecidableEq σ] [DecidableEq τ]
    (I : Integration σ τ) : WeakForm σ τ :=
    { domain := I.f.domain
      range := I }

end Integration

namespace WeakForm

  /-
  You get a list of invariants (whatever they may be) and their associated numbers.
  This describes how to make a list of Type u+1 from Type u.
  -/
  def measure {σ : Type u} {τ : Type (u+1)} [DecidableEq σ] [DecidableEq τ]
    (WF : WeakForm σ τ) (_x : σ) : Accumulation σ τ :=
    WF.range.integral

end WeakForm


end Measurement
