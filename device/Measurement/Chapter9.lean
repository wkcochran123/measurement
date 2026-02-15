import Measurement.Chapter8

namespace Measurement

structure Commutator (σ : Type u) (τ : Type (u+1)) where
  left: Surface σ τ
  right: Surface σ τ
  dispersion: Statistic σ τ

structure Gauge (σ : Type u) (τ : Type (u+1)) where
  state : Surface σ τ
  sequence : Commutator σ τ

structure Observer (σ : Type u) (τ : Type (u+1)) where
  gauge: Gauge σ τ
  measurement: Residue σ τ

structure Frame (σ : Type u) (τ : Type (u+1)) where
  origin: Calibration σ τ
  units: Surface σ τ

end Measurement
