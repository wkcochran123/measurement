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



abbrev Clock := Instrument Nat Nat
abbrev Ruler := Instrument ZFC.QPos ZFC.QPos


structure TuringDevice (S : Type u) (σ : Type v) where
  instrument     : Instrument S σ
  decomposition  : DecomposingMap S σ

end Measurement
