import Measurement.Chapter9

namespace Measurement


universe u v

structure Gauge (σ : Type u) (τ : Type (u+1)) where
  state : Surface σ τ
  sequence : Commutator σ τ

structure Frame (σ : Type u) (τ : Type (u+1)) where
  measurement: Observer σ τ
  units: Surface σ τ


-- Strictly positive reals
abbrev Rpos : Type := { r : Real // 0 < r }

structure PhysicalLaw (σ : Type u) (τ : Type (u+1)) where
  finiteGauge: Ledger (Gauge σ τ)
  observer: Frame σ τ

namespace PhysicalLaw

def f (PL : PhysicalLaw σ τ) : ℝ := 0.0 --- not for long!

end PhysicalLaw

/--
f(t) = t (!)
f:Rpos -> R
-/
abbrev TrivialPhysicalLaw := PhysicalLaw ℚ (ULift ℚ)

end Measurement
