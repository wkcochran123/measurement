import Measurement.Chapter2

namespace Measurement

/--
Invariant:     The ability to compute an inversion by listing values out
Instrument:    A metaphysical construction that explains the transmission
               and arrival of a stimulus
Device:        The list of possible carrier/sensor interactions
Closure:       The invariant of measurement
-/

structure Inversion (σ : Type u) (τ : Type (u+1)) where
  inv : Decomposition τ σ

structure Carrier (σ : Type u) (τ : Type (u+1)) where
  instrument: Instrument σ τ
  model: TuringDevice σ τ
  map: Inversion σ τ
  ordering: ArrowOfTime σ τ

structure Phenomenon (σ : Type u) (τ : Type (u+1)) where
  sensor : Device σ τ
  carrier : Carrier σ τ

structure Invariant (σ : Type u) (τ : Type (u+1)) where
  description : Device σ τ
  model       : Inversion σ τ


abbrev DopplerCarrier := Carrier Nat (ULift Nat)
abbrev Digitizer (σ : Type u):= Computer σ (ULift Nat)






end Measurement
