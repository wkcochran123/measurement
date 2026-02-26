import Measurement.Chapter2

namespace Measurement

/--
Invariant:     The ability to compute an inversion by listing values out
Instrument:    A metaphysical construction that explains the transmission
               and arrival of a stimulus
Device:        The list of possible carrier/sensor interactions
Closure:       The invariant of measurement
-/

structure Inversion
    (σ : Type u) [Distinguishable σ]
    (τ : Type v) [Distinguishable τ] where
  inv : Decomposition τ σ

structure Carrier
    (σ : Type u) [Distinguishable σ]
    (τ : Type v) [Distinguishable τ] where
  instrument: Instrument σ τ
  model: Friction (Device σ) (ULift τ)
  map: Inversion σ τ
  arrow: ArrowOfTime τ

structure Phenomenon (σ : Type u) (τ : Type v) where
  sensor : Device σ τ
  carrier : Carrier σ τ

structure Invariant (σ : Type u) (τ : Type v) where
  description : Device σ τ
  model       : Inversion σ τ


abbrev DopplerCarrier (σ : Type u) := Carrier σ (ULift Nat)

structure Digitizer (σ : Type u) where
  carrier: Friction DopplerCarrier σ
  cpu: Friction (Computer Nat) (ULift Rat) -- Computer that associates a symbol index with a rational number
  calibration: Numbering Rat



end Measurement
