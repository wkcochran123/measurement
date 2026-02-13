import Measurement.Chapter7

namespace Measurement

structure RationalMap (σ : Type u) (τ : Type (u+1)) where
  domain: Decomposition σ τ
  range: Decomposition σ τ

structure Integration (σ : Type u) (τ : Type (u+1)) where
  volume: Enumeration (RationalMap σ τ)

structure Prediction (σ : Type u) (τ : Type (u+1)) where
  model: RationalMap σ τ
  representation: Inversion σ τ

structure Residue (σ : Type u) (τ : Type (u+1)) where
  bayes: Prediction σ τ
  model: Prediction σ τ
  norm: Norm σ τ

namespace Residue
universe u

variable {σ : Type u} {τ : Type (u+1)}
variable [DecidableEq σ] [DecidableEq τ]

def fromModels
    (bayesModel : Prediction σ τ)
    (phenomenalModel : Prediction σ τ)
    (n : Norm σ τ) : Residue σ τ :=
  { bayes := bayesModel
    model := phenomenalModel
    norm  := n }


/-- Sum of `Norm.distance` over an enumeration of pairs. -/
def enumSum (n : Norm σ τ) : Enumeration (σ × τ) → Nat
  | .nil => 0
  | .cons p ps => n.distance p + enumSum n ps

/-- Cost of disagreeing pairs at a single step (symmetric in the two predictors). -/
def stepCost (n : Norm σ τ) (p q : σ × τ) : Nat :=
  if h : p = q then
    0
  else
    n.distance p + n.distance q

/--
Compare two enumerated decompositions pairwise.
If one list ends first, the remaining tail also contributes cost via `enumSum`.
-/
def enumCost (n : Norm σ τ) : Enumeration (σ × τ) → Enumeration (σ × τ) → Nat
  | .nil, ys => enumSum n ys
  | xs, .nil => enumSum n xs
  | .cons p ps, .cons q qs =>
      stepCost n p q + enumCost n ps qs

/-- Cost between two `RationalMap`s: compare both `domain` and `range`. -/
def mapCost (n : Norm σ τ) (f g : RationalMap σ τ) : Nat :=
  enumCost n f.domain.pairs g.domain.pairs
  + enumCost n f.range.pairs g.range.pairs

/--
The Residue as a scalar action: distance between Bayes and Model predictions,
measured by the provided `Norm`.
-/
def length (r : Residue σ τ) : Nat :=
  mapCost r.norm r.bayes.model r.model.model

end Residue

structure CommonExperience (σ : Type u) (τ : Type (u+1)) where
  projection: Projection σ τ
  experiences: Enumeration (TimeSeries σ τ)

namespace CommonExperience

/-- Map an `Enumeration`. -/
def map {A : Type u} {B : Type v} (f : A → B) : Enumeration A → Enumeration B
  | .nil        => .nil
  | .cons a as  => .cons (f a) (map f as)

/-- Flatten an `Enumeration` of `Enumeration`s. -/
def flatten {A : Type u} : Enumeration (Enumeration A) → Enumeration A
  | .nil        => .nil
  | .cons xs xss => Enumeration.append xs (flatten xss)

/-- The event-ledger associated to a single `TimeSeries`: take the last `Fact`'s record. -/
def timeSeriesEvents {σ : Type u} {τ : Type (u+1)} (T : TimeSeries σ τ) : Ledger (Event τ) :=
  (Ledger.last T).record

/-- All events contributed by all common experiences, concatenated in enumeration order. -/
def allEvents {σ : Type u} {τ : Type (u+1)} (C : CommonExperience σ τ) : Enumeration (Event τ) :=
  flatten (map (fun T => (timeSeriesEvents T).toEnum) C.experiences)

/-- The `n`th event in the common experience stream (if it exists). -/
def next_event? {σ : Type u} {τ : Type (u+1)}
  (C : CommonExperience σ τ) (n : Nat) : Option (Event τ) :=
  Enumeration.nth (allEvents C) n

end CommonExperience

end Measurement
