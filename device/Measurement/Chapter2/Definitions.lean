import Std


import Measurement.Chapter2.Constructions

namespace Measurement
open Classical


structure Alphabet (σ : Type v) where
  symbols : Enumeration σ


structure Instrument (S : Type u) (σ : Type v) where
  -- The State
  alphabet : Alphabet σ
  ledger   : Ledger S

  domainLogic     : DecodingMap S
  instrumentLogic : DecodingMap σ

structure Device (σ : Type S) (τ:Type T) where
  instrument : Instrument σ τ
  decomposition : Decomposition τ σ

abbrev EinsteinDevice := Device Nat Nat

abbrev TuringDevice (S : Type u) (σ : Type v) : Type (max u v) :=
  Device S σ


end Measurement
