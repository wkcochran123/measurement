import Measurement.Chapter9

namespace Measurement


structure PhysicalLaw (σ : Type u) (τ : Type (u+1)) where
  evidence: Ledger (Observer σ τ)
  rule: Gauge σ τ
  prediction: Sensor σ τ

noncomputable def PhysicalLaw.f (PL : PhysicalLaw σ τ)  {t : ℝ } : (ℝ×ℝ) :=
  -- get a DopplerCarrer for the real from the gauge
  -- hand it to the sensor to get the invariant
  -- get the average and dispersion for the invariant from the evidence
  -- use these to make a variation (σ τ σ' τ')
  -- step the variation forward and, given σ τ σ', compute τ'
  -- give τ' back to the DopplerCarrier for the return value.

end Measurement
