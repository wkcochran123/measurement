import Measurement.Chapter7

namespace Measurement

structure Reading (σ : Type u) (τ : Type (u+1)) where
  value: Number σ τ
  event: Event σ τ

structure Statistic (σ : Type u) (τ : Type (u+1)) where
  evidence: Enumeration (Reading σ τ)
  distribution: Enumeration (Representation (Invariant σ τ))
  dispersion: Enumeration (Invariant σ τ)

structure BayesPredictor (σ : Type u) (τ : Type (u+1)) where
  prior: Statistic σ τ
  likelihood: Representation (Invariant σ τ)
  posterior: Representation (Invariant σ τ)

structure Hypothesis (σ : Type u) (τ : Type (u+1)) where
  predictor: BayesPredictor σ τ
  confidence: Number σ τ


namespace Reading
  def event? {σ : Type u} {τ : Type (u+1)} (r : Reading σ τ) : Option (Event σ τ) :=
    some r.event
end Reading

namespace Statistic
  def counting {σ : Type u} {τ : Type (u+1)} [DecidableEq σ] [DecidableEq τ] (S : Statistic σ τ) (_x : σ) : Counting σ τ :=
    let readings := S.evidence
    let enumeration := readings.map (fun r => r.event)
    Counting.mk enumeration

end Statistic


namespace BayesPredictor

  def predict {σ : Type u}{τ : Type (u+1)}
      (B: BayesPredictor σ τ) (N: Number σ τ) (E: Event σ τ)
      [DecidableEq σ] [DecidableEq τs] : Number σ τ :=

      let invariant := N.value


end BayesPredictor

end Measurement
