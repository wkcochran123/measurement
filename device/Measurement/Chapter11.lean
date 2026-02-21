import Measurement.Chapter10

namespace Measurement
structure Apparatus (σ : Type u) (τ : Type (u+1)) where
  physical_process: DopplerCarrier
  readout: Number σ τ
  ordering: ArrowOfTime σ τ

structure Stimulus (σ : Type u) (τ : Type (u+1)) where
  state: Event σ τ
  measurement: Invariant σ τ

structure Observer (σ : Type u) (τ : Type (u+1)) where
  apparatus: Apparatus σ τ
  calibration: Regime σ τ

structure PhysicalLaw (σ : Type u) (τ : Type (u+1)) where
  observer: Observer σ τ
  hypothesis: Hypothesis σ τ
  stimulus: Stimulus σ τ



namespace PhysicalLaw

def predict {σ : Type u} {τ : Type (u+1)} (PL : PhysicalLaw σ τ) (s : Stimulus σ τ)
  [DecidableEq σ] [DecidableEq τ] : Numbers σ τ :=

  -- Step 1: Get the Bayes predictor for the law:
  let predictor := PL.hypothesis.predictor

  -- Step 2: Get the latest reading for the observer:
  let last_reading := PL.observer.apparatus.readout

end PhysicalLaw

end Measurement
