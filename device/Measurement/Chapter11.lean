import Measurement.Chapter10

namespace Measurement
structure Apparatus (σ : Type u) (τ : Type (u+1)) where
  physical_process: DopplerCarrier
  readout: RealNumber σ τ
  ordering: ArrowOfTime σ τ

structure Stimulus (σ : Type u) (τ : Type (u+1)) where
  state: Event σ τ
  threshold: Invariant σ τ

structure Observer (σ : Type u) (τ : Type (u+1)) where
  apparatus: Apparatus σ τ
  calibration: Regime σ τ

structure PhysicalLaw (σ : Type u) (τ : Type (u+1)) where
  observer: Observer σ τ
  hypothesis: Hypothesis σ τ
  stimulus: Stimulus σ τ



namespace PhysicalLaw

def predict {σ : Type u} {τ : Type (u+1)} (PL : PhysicalLaw σ τ) (s : Stimulus σ τ) : RealNumber σ τ :=
  -- Step 1: We agree on a set of symbols to represent the hypothesis.
  let symbol := PL.hypothesis.predictor.posterior.physical.pairs

  -- Step 2: We make a ledger for those symbols to be written on.
  let ledger := Ledger.mk symbol

  -- Step 2: We design the instrument to measure the stimulus
  let instrument := PL.stimulus.state.instrument

  -- Step 3: We build the device to measure the stimulus
  let device := PL.stimulus.state.device

  -- Step 4: We turn on the device and wait for a reading
  let reading := device.silence.after

  -- Step 5: Now that we have a reading, we write it in the ledger and
  -- make sure it cannot be rewritten.
  let ledger := Ledger.linked_list.append reading

  -- Step 6: Now that we have a ledger, we can build a model of the stimulus!
  -- First, we build a Real model of the carrier
  let carrier := DopplerCarrier.mk instrument model map ordering

  -- Step 7: We then set the state of the carrier model by modeling the stimulus
  let carrier := carrier.recv? PL.stimulus.state


end PhysicalLaw

end Measurement
