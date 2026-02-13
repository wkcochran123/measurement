import Measurement.Chapter5

namespace Measurement

/--
Miss me with that Godel-incompleteness stuff.  Don't you know it's whack
to reference yourself?
-/
structure Indirection (σ : Type u) (τ : Type (u+1)) where
  model: Inversion σ τ
  step: Ledger (Event σ) → Ledger (Event τ)

structure Refinement(σ : Type u) (τ : Type (u+1)) where
  step: Indirection σ τ

structure Predictor (σ : Type u) (τ : Type (u+1)) where
  state: Ledger (Event σ)
  refinement: Refinement σ τ

namespace Ledger

/-- Append one entry to the end of a ledger. -/
def snoc {X : Type u} (L : Ledger X) (x : X) : Ledger X :=
  match Enumeration.snoc (Ledger.toEnum L) x with
  | .nil       => { head := x, tail := .nil }   -- unreachable in practice
  | .cons h t  => { head := h, tail := t }

end Ledger


namespace Indirection

/-- One lawful refinement step: use the ledger size as the address,
    query the model for the next admissible symbol, and append it. -/
noncomputable def refine {σ : Type u} {τ : Type (u+1)}
    (I : Indirection σ τ) (L : Ledger (Event σ)) : Ledger (Event σ) :=
  let n := Ledger.size L
  match Inversion.eta I.model n with
  | none        => L
  | some (t, s) => Ledger.snoc L { symbol := s }

end Indirection


namespace Refinement

/-- Refinement is just indirection applied to the current ledger. -/
noncomputable def refine {σ : Type u} {τ : Type (u+1)}
    (R : Refinement σ τ) (L : Ledger (Event σ)) : Ledger (Event σ) :=
  Indirection.refine R.step L

end Refinement


namespace Predictor

/-- Advance the sensor by one refinement step. -/
noncomputable def refine {σ : Type u} {τ : Type (u+1)}
    (S : Predictor σ τ) : Predictor σ τ :=
  { state      := Refinement.refine S.refinement S.state
    refinement := S.refinement }

end Predictor

/--
A Restriction is the "coarsening interface":
it pairs a Projection (what counts as comparable / correlant)
with an Inversion (how to recover a candidate value).
-/
structure Restriction (σ : Type u) (τ : Type v) where
  projection : Projection σ τ
  inversion  : Inversion σ τ

abbrev CauchyRestriction := Restriction RealCarrier ℚ
abbrev CantorRestriction := Restriction RealCarrier Nat

namespace Restriction

/--
Coarsen a `σ` into a `τ` only when the projection agrees.

This is the literal "coarsen without contradiction" move:
- the `Projection` certifies compatibility (some true),
- the `Inversion` supplies the candidate value (decode?).
-/
noncomputable def coarsen?
  {σ : Type u} {τ : Type v}
  [DecidableEq σ] [DecidableEq τ]
  (R : Restriction σ τ) (x : σ) : Option τ :=
  match R.projection.project x with
  | some true  => R.inversion.inv.inverse.decode? x
  | _          => none

/-- Coarsen an `Event σ` to an `Event τ` when lawful. -/
noncomputable def coarsenEvent?
  {σ : Type u} {τ : Type v}
  [DecidableEq σ] [DecidableEq τ]
  (R : Restriction σ τ) (e : Event σ) : Option (Event τ) :=
  Option.map (fun t => { symbol := t }) (coarsen? R e.symbol)

end Restriction

abbrev PhenomenalModel := Restriction ℝ RealCarrier

namespace PhenomenalModel

/-- Evaluate the phenomenal model (coarsen ambient real into internal carrier). -/
noncomputable def eval?
  [DecidableEq ℝ] [DecidableEq RealCarrier]
  (M : PhenomenalModel) (x : ℝ) : Option RealCarrier :=
  Restriction.coarsen? M x

end PhenomenalModel

abbrev BayesModel := Restriction RealCarrier RealCarrier

namespace BayesModel
noncomputable def eval?
  [DecidableEq RealCarrier]
  (B : BayesModel) (x : RealCarrier) : Option RealCarrier :=
  Restriction.coarsen? B x
end BayesModel


structure Sensor (σ : Type u) (τ : Type (u+1)) (υ : Type v) where
  hardware: Device σ τ
  tare: Calibration τ τ
  noise_floor: Restriction υ σ
  resolution: Projection τ υ

namespace Device

/-- Raw device reading: pass `σ` through the instrument's ledger to obtain its
    record index, then read the corresponding `τ` from the device decomposition. -/
noncomputable def reading? {σ : Type u} {τ : Type v}
  [DecidableEq σ] [DecidableEq τ]
  (D : Device σ τ) (s : σ) : Option τ :=
  match Enumeration.indexOfBy (fun a b => decide (a = b)) D.instrument.ledger.toEnum s with
  | none => none
  | some n =>
      match Enumeration.nth D.decomposition.pairs n with
      | none        => none
      | some (t, _) => some t


end Device

namespace Sensor

/-- Calibrated sensor reading: accept an observed `t : τ` as a reading for `s : σ`
    iff the calibration judges it equal to the device's predicted reading. -/
noncomputable def reading? {σ : Type u} {τ : Type (u+1)} {υ: Type v}
  [DecidableEq σ] [DecidableEq τ]
  (S : Sensor σ τ υ) (s : σ) (t : τ) : Option τ :=
  match Device.reading? S.hardware s with
  | none     => none
  | some t'  =>
      if S.tare.judgeEq t t' then
        some t
      else
        none

end Sensor

abbrev RealSensor (σ : Type u) (τ : Type (u+1)):= Sensor σ τ ℝ

end Measurement
