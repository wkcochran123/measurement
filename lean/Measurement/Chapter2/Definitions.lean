import Std


import Measurement.Chapter2.Constructions

namespace Measurement
open Classical





structure Instrument (S : Type u) (σ : Type v) where
  -- The State
  alphabet : Alphabet σ
  ledger   : Ledger S

  domainLogic     : DecodingMap S
  instrumentLogic : DecodingMap σ

namespace Instrument

  def domainRefinement {S σ} (I : Instrument S σ) : Refinement S :=
    { enumeration := I.ledger.toEnum -- (Assuming Ledger wraps Enumeration)
    , predictor   := I.domainLogic
    }

  def instrumentRefinement {S σ} (I : Instrument S σ) : Refinement σ :=
    { enumeration := I.alphabet.symbols
    , predictor   := I.instrumentLogic
    }

  def search {Record σ} (I : Instrument Record σ) (k : Nat) : Option Record :=
    I.ledger.index k
end Instrument

structure CoarseningMap (σ : Type u) where
  coarsen : σ -> Option σ

structure GridMap where
  grid : Nat -> Option Nat

abbrev RationalInstrument := Instrument ZFC.QPos ZFC.QPos


structure RationalMap where
  map : ZFC.QPos -> ZFC.Q

structure DenseResponse where
  rationals: Enumeration ZFC.QPos
  instrument: RationalInstrument

namespace DenseResponse
  noncomputable def map (D : DenseResponse) (t : ZFC.QPos) : Option ZFC.QPos :=
    match D.rationals.indexOf t with
    | none   => none
    | some i => (D.instrument).search i

end DenseResponse


structure DomainResponse where
  ψ         : Real → Real
  certifies : DenseResponse

  -- membership predicate (your "q ∈ QPos")
  QPosSet   : Set Real

  -- turn membership evidence into an actual QPos value
  toQPos    : ∀ {q : Real}, q ∈ QPosSet → ZFC.QPos

  -- interpret a QPos back in the continuum
  embedQPos : ZFC.QPos → Real

namespace DomainResponse

/--
If `q ∈ QPosSet`, try the certified dense response; otherwise fall back to `ψ`.
If the certified lookup fails (`none`), also fall back to `ψ`.
-/
noncomputable def psi (D : DomainResponse) (q : Real) : Real := by
  classical
  by_cases h : q ∈ D.QPosSet
  ·
    let t : ZFC.QPos := D.toQPos h
    match DenseResponse.map D.certifies t with
    | some t' => exact D.embedQPos t'
    | none    => exact D.ψ q
  ·
    exact D.ψ q

end DomainResponse

end Measurement
