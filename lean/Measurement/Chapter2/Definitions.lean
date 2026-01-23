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

structure Instrument (S: Type u)(σ :Type v) where
  alphabet : Alphabet σ
  ledger : Ledger S

abbrev Moment : Type :=
  Σ t : Real, ({ u : Real // u ∈ ZFC.unitIocAt t } → Real)

abbrev Phenomenon := Enumeration Moment

structure DenseResponse (X: Type u) where
  refinement: Refinement X
  map : QPos -> Q

structure DomainResponse (X: Type u) where
  -- Who needs a continuum hypothesis when I have this continuous function right here?
  ψ : Real -> Real
  certifies : DenseResponse X

abbrev QPos := { q : Rat // q > 0 }

namespace DomainResponse
  noncomputable def psi {X : Type u}
    (D : DomainResponse X) (t : Real) : Real :=

    -- Check if t is a Rational Positive number
    if h : ∃ (q : QPos), ((q : Rat) : Real) = t then
      -- CASE 1: Rational. Use the Ledger (Evidence).
      -- 'h.choose' extracts the rational q from the existence proof.
      (D.certifies.map h.choose : Real)
    else
      -- CASE 2: Irrational. Use the Ghost Function (ZFC).
      D.ψ t

end DomainResponse


structure TimeSeries (E : Type u)(X : Type v) where
  data : E → X
  order : PartialOrder E
  /-- The sequence of records (partial to allow finite series). -/
  seq : Nat → Option E
  /-- No two distinct records share the same position. -/
  seq_injective :
    ∀ {n m r},
      seq n = some r →
      seq m = some r →
      n = m
  /-- Successive records respect the order. -/
  seq_ordered :
    ∀ {n r s},
      seq n = some r →
      seq (n+1) = some s →
      order.le r s

end Measurement
