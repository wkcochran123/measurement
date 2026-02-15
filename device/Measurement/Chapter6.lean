import Measurement.Chapter5

namespace Measurement


structure Flattening (σ : Type u) (τ : Type (u+1)) where
  ordering : Enumeration (Walking σ)
  shape : Enumeration (Enumeration (σ × τ))

structure Refinement(σ : Type u) (τ : Type (u+1)) where
  step: ArrowOfTime σ τ
  value: Flattening σ τ

structure GateauxVariation (σ : Type u) (τ : Type (u+1)) where
  variation: Variation σ τ
  Refinement: Refinement σ τ

structure Sensor (σ : Type u) (τ : Type (u+1))  where
  projection: GateauxVariation σ τ
  reading: Inversion σ τ





namespace Flattening

  noncomputable def ceil? {σ : Type u} {τ : Type (u+1)}
  [DecidableEq σ]
  (F : Flattening σ τ) (x : σ) : Option σ :=
  Enumeration.findMap?
    (fun W => PartialOrder.ceil? W.poset W.candidates x)
    F.ordering

end Flattening

namespace Refinement

def step? {σ : Type u} {τ : Type (u+1)}
  (R : Refinement σ τ) : Option τ :=
  ArrowOfTime.elapse R.step

noncomputable def next? {σ : Type u} {τ : Type (u+1)}
  [DecidableEq σ]
  (R : Refinement σ τ) (x : σ) : Option (σ × τ) :=
  match R.value.ceil? x, R.step? with
  | some x', some y => some (x', y)
  | _, _            => none

end Refinement

namespace GateauxVariation

noncomputable def predict? {σ : Type u} {τ : Type (u+1)}
  [DecidableEq σ] [DecidableEq τ]
  (G : GateauxVariation σ τ) (x : σ) : Option τ :=
  match G.Refinement.value.ceil? x with
  | none    => none
  | some x' => Variation.succ G.variation x'

end GateauxVariation


namespace Sensor

noncomputable def read? {σ : Type u} {τ : Type (u+1)}
  [DecidableEq σ] [DecidableEq τ]
  (S : Sensor σ τ) (x : σ) : Option τ :=
  match S.projection.predict? x with
  | none   => none
  | some y =>
      match S.reading.inv.decode? y with
      | none   => none
      | some _ => some y

end Sensor
