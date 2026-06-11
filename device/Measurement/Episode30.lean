import Measurement.Episode29

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000
set_option allowUnsafeReducibility true

namespace Measurement

/-
__EPISODE 30__: _The Boundary Actually Evaluates_

Episode29 produced `NullspaceKilled` for first-derivative energy, but the
anchor-kills-constant step was still a single strong certificate:

  constant mode + load anchor = zero activity.

This episode opens that certificate.  The loaded boundary now depends on the
activity `x`:

  x constant
  -> x = valueAtLoad x
  -> valueAtLoad x = anchor.trace .load
  -> anchor.trace .load = zero
  -> x = zero.

The compiler version makes the `.load` step explicit: a compiler-native loaded
anchor realizes the per-activity value at the analytic load boundary.

Stated formally:
* `LoadedBoundaryEvaluation` is the analytic boundary evaluation layer.
* `BoundaryEvaluatedFirstDerivativeNullspaceModel` derives Episode29's
  `FirstDerivativeNullspaceModel`.
* `CompilerLoadedBoundaryEvaluation` says compiler `.load` realizes the
  per-activity loaded value.
* `CompilerBoundaryEvaluatedFirstDerivativeGalerkinActivity` packages the full
  compiler-boundary-to-SPD path.

Residue left:
The actual function evaluator is still abstract.  The next layer may instantiate
`valueAtLoad` with a real finite-element/partition evaluation operator.
-/

structure LoadedBoundaryEvaluation
    (form : GalerkinBilinearForm)
    (anchor : WhiteHoleLoadAnchor form)
    (ConstantMode : form.V -> Prop) where
  valueAtLoad : form.V -> form.V
  anchoredAtLoad : form.V -> Prop
  constant_eq_loaded_value :
    forall x,
      ConstantMode x -> x = valueAtLoad x
  loaded_value_eq_anchor_trace :
    forall x,
      anchoredAtLoad x -> valueAtLoad x = anchor.trace .load

namespace LoadedBoundaryEvaluation

theorem loaded_value_zero
    {form : GalerkinBilinearForm}
    {anchor : WhiteHoleLoadAnchor form}
    {ConstantMode : form.V -> Prop}
    (evaluation :
      LoadedBoundaryEvaluation form anchor ConstantMode)
    (x : form.V)
    (hAnchored : evaluation.anchoredAtLoad x) :
    evaluation.valueAtLoad x = form.zero := by
  rw [evaluation.loaded_value_eq_anchor_trace x hAnchored]
  exact anchor.load_is_anchor

theorem constant_mode_eq_zero
    {form : GalerkinBilinearForm}
    {anchor : WhiteHoleLoadAnchor form}
    {ConstantMode : form.V -> Prop}
    (evaluation :
      LoadedBoundaryEvaluation form anchor ConstantMode)
    (x : form.V)
    (hConstant : ConstantMode x)
    (hAnchored : evaluation.anchoredAtLoad x) :
    x = form.zero := by
  calc
    x = evaluation.valueAtLoad x :=
      evaluation.constant_eq_loaded_value x hConstant
    _ = form.zero :=
      LoadedBoundaryEvaluation.loaded_value_zero
        evaluation
        x
        hAnchored

end LoadedBoundaryEvaluation

structure BoundaryEvaluatedFirstDerivativeNullspaceModel
    (form : GalerkinBilinearForm)
    (anchor : WhiteHoleLoadAnchor form) where
  ConstantMode : form.V -> Prop
  boundary :
    LoadedBoundaryEvaluation form anchor ConstantMode
  diagonal_zero_implies_constant :
    forall x,
      form.a x x = 0 -> ConstantMode x
  constant_mode_anchoredAtLoad :
    forall x,
      ConstantMode x -> boundary.anchoredAtLoad x

namespace BoundaryEvaluatedFirstDerivativeNullspaceModel

def toFirstDerivativeNullspaceModel
    {form : GalerkinBilinearForm}
    {anchor : WhiteHoleLoadAnchor form}
    (model :
      BoundaryEvaluatedFirstDerivativeNullspaceModel form anchor) :
    FirstDerivativeNullspaceModel form anchor where
  ConstantMode := model.ConstantMode
  diagonal_zero_implies_constant :=
    model.diagonal_zero_implies_constant
  whiteHoleLoadAnchor_kills_constant := by
    intro x hConstant _hAnchor
    exact
      LoadedBoundaryEvaluation.constant_mode_eq_zero
        model.boundary
        x
        hConstant
        (model.constant_mode_anchoredAtLoad x hConstant)

def toNullspaceKilled
    {form : GalerkinBilinearForm}
    {anchor : WhiteHoleLoadAnchor form}
    (model :
      BoundaryEvaluatedFirstDerivativeNullspaceModel form anchor)
    (natural : NaturalBoundary form) :
    NullspaceKilled form natural anchor :=
  FirstDerivativeNullspaceModel.toNullspaceKilled
    (BoundaryEvaluatedFirstDerivativeNullspaceModel.toFirstDerivativeNullspaceModel
      model)
    natural

end BoundaryEvaluatedFirstDerivativeNullspaceModel

structure BoundaryEvaluatedFirstDerivativeGalerkinActivity where
  form :
    GalerkinBilinearForm
  natural :
    NaturalBoundary form
  anchor :
    WhiteHoleLoadAnchor form
  boundaryModel :
    BoundaryEvaluatedFirstDerivativeNullspaceModel form anchor

namespace BoundaryEvaluatedFirstDerivativeGalerkinActivity

def toFirstDerivativeAnchoredGalerkinActivity
    (activity : BoundaryEvaluatedFirstDerivativeGalerkinActivity) :
    FirstDerivativeAnchoredGalerkinActivity where
  form := activity.form
  natural := activity.natural
  anchor := activity.anchor
  nullspaceModel :=
    BoundaryEvaluatedFirstDerivativeNullspaceModel.toFirstDerivativeNullspaceModel
      activity.boundaryModel

def toSPDGalerkinActivity
    (activity : BoundaryEvaluatedFirstDerivativeGalerkinActivity) :
    SPDGalerkinActivity :=
  FirstDerivativeAnchoredGalerkinActivity.toSPDGalerkinActivity
    (BoundaryEvaluatedFirstDerivativeGalerkinActivity.toFirstDerivativeAnchoredGalerkinActivity
      activity)

def boundaryEvaluation_firstDerivative_implies_spd
    (activity : BoundaryEvaluatedFirstDerivativeGalerkinActivity) :
    SPDGalerkinActivity :=
  BoundaryEvaluatedFirstDerivativeGalerkinActivity.toSPDGalerkinActivity
    activity

end BoundaryEvaluatedFirstDerivativeGalerkinActivity

structure CompilerLoadedBoundaryEvaluation
    (form : GalerkinBilinearForm)
    (anchor : WhiteHoleLoadAnchor form)
    (compilerAnchor : CompilerWhiteHoleLoadAnchor form)
    (ConstantMode : form.V -> Prop) where
  valueAtLoad : form.V -> form.V
  anchoredAtLoad : form.V -> Prop
  constant_eq_loaded_value :
    forall x,
      ConstantMode x -> x = valueAtLoad x
  compiler_load_realizes_loaded_value :
    compilerAnchor.anchor_loaded ->
      forall x,
        anchoredAtLoad x -> valueAtLoad x = anchor.trace .load

namespace CompilerLoadedBoundaryEvaluation

def toLoadedBoundaryEvaluation
    {form : GalerkinBilinearForm}
    {anchor : WhiteHoleLoadAnchor form}
    {compilerAnchor : CompilerWhiteHoleLoadAnchor form}
    {ConstantMode : form.V -> Prop}
    (evaluation :
      CompilerLoadedBoundaryEvaluation
        form
        anchor
        compilerAnchor
        ConstantMode) :
    LoadedBoundaryEvaluation form anchor ConstantMode where
  valueAtLoad := evaluation.valueAtLoad
  anchoredAtLoad := evaluation.anchoredAtLoad
  constant_eq_loaded_value :=
    evaluation.constant_eq_loaded_value
  loaded_value_eq_anchor_trace := by
    intro x hAnchored
    exact
      evaluation.compiler_load_realizes_loaded_value
        compilerAnchor.anchor_loaded_proof
        x
        hAnchored

theorem compiler_load_realizes_zero_anchor
    {form : GalerkinBilinearForm}
    {anchor : WhiteHoleLoadAnchor form}
    {compilerAnchor : CompilerWhiteHoleLoadAnchor form}
    {ConstantMode : form.V -> Prop}
    (evaluation :
      CompilerLoadedBoundaryEvaluation
        form
        anchor
        compilerAnchor
        ConstantMode)
    (x : form.V)
    (hAnchored : evaluation.anchoredAtLoad x) :
    evaluation.valueAtLoad x = form.zero := by
  have hLoaded :
      evaluation.valueAtLoad x = anchor.trace .load :=
    evaluation.compiler_load_realizes_loaded_value
      compilerAnchor.anchor_loaded_proof
      x
      hAnchored
  rw [hLoaded]
  exact anchor.load_is_anchor

end CompilerLoadedBoundaryEvaluation

structure CompilerBoundaryEvaluatedFirstDerivativeNullspaceModel
    (form : GalerkinBilinearForm)
    (anchor : WhiteHoleLoadAnchor form)
    (compilerAnchor : CompilerWhiteHoleLoadAnchor form) where
  ConstantMode : form.V -> Prop
  boundary :
    CompilerLoadedBoundaryEvaluation
      form
      anchor
      compilerAnchor
      ConstantMode
  diagonal_zero_implies_constant :
    forall x,
      form.a x x = 0 -> ConstantMode x
  constant_mode_anchoredAtLoad :
    forall x,
      ConstantMode x -> boundary.anchoredAtLoad x

namespace CompilerBoundaryEvaluatedFirstDerivativeNullspaceModel

def toBoundaryEvaluatedModel
    {form : GalerkinBilinearForm}
    {anchor : WhiteHoleLoadAnchor form}
    {compilerAnchor : CompilerWhiteHoleLoadAnchor form}
    (model :
      CompilerBoundaryEvaluatedFirstDerivativeNullspaceModel
        form
        anchor
        compilerAnchor) :
    BoundaryEvaluatedFirstDerivativeNullspaceModel form anchor where
  ConstantMode := model.ConstantMode
  boundary :=
    CompilerLoadedBoundaryEvaluation.toLoadedBoundaryEvaluation
      model.boundary
  diagonal_zero_implies_constant :=
    model.diagonal_zero_implies_constant
  constant_mode_anchoredAtLoad :=
    model.constant_mode_anchoredAtLoad

def toFirstDerivativeNullspaceModel
    {form : GalerkinBilinearForm}
    {anchor : WhiteHoleLoadAnchor form}
    {compilerAnchor : CompilerWhiteHoleLoadAnchor form}
    (model :
      CompilerBoundaryEvaluatedFirstDerivativeNullspaceModel
        form
        anchor
        compilerAnchor) :
    FirstDerivativeNullspaceModel form anchor :=
  BoundaryEvaluatedFirstDerivativeNullspaceModel.toFirstDerivativeNullspaceModel
    (CompilerBoundaryEvaluatedFirstDerivativeNullspaceModel.toBoundaryEvaluatedModel
      model)

end CompilerBoundaryEvaluatedFirstDerivativeNullspaceModel

structure CompilerBoundaryEvaluatedFirstDerivativeGalerkinActivity where
  form :
    GalerkinBilinearForm
  natural :
    NaturalBoundary form
  anchor :
    WhiteHoleLoadAnchor form
  compilerAnchor :
    CompilerWhiteHoleLoadAnchor form
  boundaryModel :
    CompilerBoundaryEvaluatedFirstDerivativeNullspaceModel
      form
      anchor
      compilerAnchor
  compilerAnchor_realizes_whiteHoleLoad :
    compilerAnchor.anchor_loaded ->
      anchor.source_to_load

namespace CompilerBoundaryEvaluatedFirstDerivativeGalerkinActivity

def toBoundaryEvaluatedFirstDerivativeGalerkinActivity
    (activity :
      CompilerBoundaryEvaluatedFirstDerivativeGalerkinActivity) :
    BoundaryEvaluatedFirstDerivativeGalerkinActivity where
  form := activity.form
  natural := activity.natural
  anchor := activity.anchor
  boundaryModel :=
    CompilerBoundaryEvaluatedFirstDerivativeNullspaceModel.toBoundaryEvaluatedModel
      activity.boundaryModel

def toCompilerAnchoredFirstDerivativeGalerkinActivity
    (activity :
      CompilerBoundaryEvaluatedFirstDerivativeGalerkinActivity) :
    CompilerAnchoredFirstDerivativeGalerkinActivity where
  activity :=
    { form := activity.form
      natural := activity.natural
      anchor := activity.anchor
      nullspaceModel :=
        CompilerBoundaryEvaluatedFirstDerivativeNullspaceModel.toFirstDerivativeNullspaceModel
          activity.boundaryModel }
  compilerAnchor := activity.compilerAnchor
  compilerAnchor_realizes_whiteHoleLoad :=
    activity.compilerAnchor_realizes_whiteHoleLoad

def toSPDGalerkinActivity
    (activity :
      CompilerBoundaryEvaluatedFirstDerivativeGalerkinActivity) :
    SPDGalerkinActivity :=
  BoundaryEvaluatedFirstDerivativeGalerkinActivity.toSPDGalerkinActivity
    (CompilerBoundaryEvaluatedFirstDerivativeGalerkinActivity.toBoundaryEvaluatedFirstDerivativeGalerkinActivity
      activity)

def compilerBoundaryEvaluation_firstDerivative_implies_spd
    (activity :
      CompilerBoundaryEvaluatedFirstDerivativeGalerkinActivity) :
    SPDGalerkinActivity :=
  CompilerBoundaryEvaluatedFirstDerivativeGalerkinActivity.toSPDGalerkinActivity
    activity

theorem compiler_load_realizes_zero_anchor
    (activity :
      CompilerBoundaryEvaluatedFirstDerivativeGalerkinActivity)
    (x : activity.form.V)
    (hAnchored :
      activity.boundaryModel.boundary.anchoredAtLoad x) :
    activity.boundaryModel.boundary.valueAtLoad x =
      activity.form.zero :=
  CompilerLoadedBoundaryEvaluation.compiler_load_realizes_zero_anchor
    activity.boundaryModel.boundary
    x
    hAnchored

theorem source_to_load
    (activity :
      CompilerBoundaryEvaluatedFirstDerivativeGalerkinActivity) :
    activity.anchor.source_to_load :=
  CompilerAnchoredFirstDerivativeGalerkinActivity.source_to_load
    (CompilerBoundaryEvaluatedFirstDerivativeGalerkinActivity.toCompilerAnchoredFirstDerivativeGalerkinActivity
      activity)

end CompilerBoundaryEvaluatedFirstDerivativeGalerkinActivity

def truthLoadedBoundaryEvaluation :
    LoadedBoundaryEvaluation
      truthGalerkinBilinearForm
      truthWhiteHoleLoadAnchor
      (fun _ => True) where
  valueAtLoad := fun _ => ()
  anchoredAtLoad := fun _ => True
  constant_eq_loaded_value := by
    intro x h
    cases x
    rfl
  loaded_value_eq_anchor_trace := by
    intro x h
    cases x
    rfl

def truthBoundaryEvaluatedFirstDerivativeNullspaceModel :
    BoundaryEvaluatedFirstDerivativeNullspaceModel
      truthGalerkinBilinearForm
      truthWhiteHoleLoadAnchor where
  ConstantMode := fun _ => True
  boundary := truthLoadedBoundaryEvaluation
  diagonal_zero_implies_constant := by
    intro x h
    trivial
  constant_mode_anchoredAtLoad := by
    intro x h
    trivial

def truthBoundaryEvaluatedFirstDerivativeGalerkinActivity :
    BoundaryEvaluatedFirstDerivativeGalerkinActivity where
  form := truthGalerkinBilinearForm
  natural := truthNaturalBoundary
  anchor := truthWhiteHoleLoadAnchor
  boundaryModel := truthBoundaryEvaluatedFirstDerivativeNullspaceModel

def truthBoundaryEvaluatedSPDGalerkinActivity :
    SPDGalerkinActivity :=
  BoundaryEvaluatedFirstDerivativeGalerkinActivity.toSPDGalerkinActivity
    truthBoundaryEvaluatedFirstDerivativeGalerkinActivity

theorem truthBoundaryEvaluated_energySq_zero_detector
    (x : truthBoundaryEvaluatedSPDGalerkinActivity.form.V) :
    (SPDGalerkinActivity.toEnergySqCertificate
        truthBoundaryEvaluatedSPDGalerkinActivity).energySq x = 0 <->
      x =
        (SPDGalerkinActivity.toEnergySqCertificate
          truthBoundaryEvaluatedSPDGalerkinActivity).zero :=
  EnergySqCertificate.energySq_eq_zero_iff_eq_zero
    (SPDGalerkinActivity.toEnergySqCertificate
      truthBoundaryEvaluatedSPDGalerkinActivity)
    x

end Measurement
