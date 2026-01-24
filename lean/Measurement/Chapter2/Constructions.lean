import Measurement.Chapter2.ZFC


namespace Measurement

universe u v w

abbrev Moment : Type :=
  Σ t : Real, ({ u : Real // u ∈ ZFC.unitIocAt t } → Real)

abbrev Phenomenon := Enumeration Moment



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






end Measurement
