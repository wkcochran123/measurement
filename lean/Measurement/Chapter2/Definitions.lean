import Std


import Measurement.Chapter2.Constructions

namespace Measurement
open Classical

structure Refinement (X : Type u) where
  enumeration : Enumeration X
  predictor : DecodingMap X

namespace Refinement
  def step {X : Type u} (R : Refinement X) : Enumeration X :=
    let n := Enumeration.len R.enumeration
      match R.predictor.ζ n with
      | none   => R.enumeration
      | some x => Enumeration.snoc R.enumeration x

end Refinement
structure Alphabet (σ : Type v) where
  symbols : Enumeration σ


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

abbrev Moment : Type :=
  Σ t : Real, ({ u : Real // u ∈ ZFC.unitIocAt t } → Real)

abbrev Phenomenon := Enumeration Moment

abbrev QPos := { q : Rat // 0 < q }

abbrev RationalInstrument := Instrument QPos QPos

structure RationalMap where
  map : QPos -> Q

structure DenseResponse where
  rationals: Enumeration QPos
  instrument: RationalInstrument

namespace DenseResponse
  noncomputable def map (D : DenseResponse) (t : QPos) : Option QPos :=
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
  toQPos    : ∀ {q : Real}, q ∈ QPosSet → QPos

  -- interpret a QPos back in the continuum
  embedQPos : QPos → Real

namespace DomainResponse

/--
If `q ∈ QPosSet`, try the certified dense response; otherwise fall back to `ψ`.
If the certified lookup fails (`none`), also fall back to `ψ`.
-/
noncomputable def psi (D : DomainResponse) (q : Real) : Real := by
  classical
  by_cases h : q ∈ D.QPosSet
  ·
    let t : QPos := D.toQPos h
    match DenseResponse.map D.certifies t with
    | some t' => exact D.embedQPos t'
    | none    => exact D.ψ q
  ·
    exact D.ψ q

end DomainResponse

end Measurement
