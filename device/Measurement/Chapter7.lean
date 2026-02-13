import Measurement.Chapter6

namespace Measurement

structure Counting (σ : Type u) (τ : Type (u+1)) where
  list: Enumeration (Sensor σ τ Nat)

structure Norm (σ : Type u) (τ : Type (u+1)) where
  distance: (σ × τ) → Nat

structure Accumulator (σ : Type u) (τ : Type (u+1)) where
  dx: Counting σ τ
  x: Norm σ τ

structure Space (σ : Type u) (τ : Type (u+1)) where
  histories: Enumeration (Accumulator σ τ)

structure Fact (σ : Type u) (τ : Type (u+1)) where
  sensor : Sensor σ τ RealCarrier
  record : Ledger (Event τ)

namespace Fact

/-- Project an observation into the observer's record: accept it iff the sensor accepts it,
    then append the resulting event to the ledger. -/
noncomputable def project
  {σ : Type u} {τ : Type (u+1)}
  [DecidableEq σ] [DecidableEq τ]
  (F : Fact σ τ) (s : σ) (t : τ) : Fact σ τ :=
  match Sensor.reading? F.sensor s t with
  | none   => F
  | some y =>
      { F with record := F.record.snoc { symbol := y } }

end Fact

abbrev TimeSeries (σ : Type u) (τ : Type (u+1)) := Ledger (Fact σ τ)

end Measurement
