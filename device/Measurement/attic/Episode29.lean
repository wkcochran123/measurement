import Measurement.Episode28

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000
set_option allowUnsafeReducibility true

namespace Measurement

/-
__EPISODE 29__: _The Loaded Anchor Kills the Nullspace_

Episode28 moved the residue to the correct certificate:

  `NullspaceKilled`

For first-derivative Galerkin energy, the analytic story is small:

  energy zero
  -> derivative zero
  -> constant mode
  -> loaded anchor f(0) = 0 kills constants
  -> zero activity.

For cubic/bending energy, the nullspace is larger: affine modes survive.  This
episode therefore gives the first-derivative certificate as the main theorem
and also names the bending/affine certificate shape that a later cubic episode
must fill.

Stated formally:
* `FirstDerivativeNullspaceModel.toNullspaceKilled` builds the Episode28
  nullspace certificate.
* `FirstDerivativeAnchoredGalerkinActivity.toSPDGalerkinActivity` then uses
  Episode28 to build the SPD Galerkin package.
* `CompilerAnchoredFirstDerivativeGalerkinActivity` wires that first-derivative
  activity to the compiler-native `.white_hole -> .load` anchor bridge.

Residue left:
The model still abstracts over the actual function space and derivative
operator.  It states the certificate that the constructive first-derivative
Sobolev layer must provide.
-/

structure FirstDerivativeNullspaceModel
    (form : GalerkinBilinearForm)
    (anchor : WhiteHoleLoadAnchor form) where
  ConstantMode : form.V -> Prop
  diagonal_zero_implies_constant :
    forall x,
      form.a x x = 0 -> ConstantMode x
  whiteHoleLoadAnchor_kills_constant :
    forall x,
      ConstantMode x ->
        anchor.trace .load = form.zero ->
          x = form.zero

namespace FirstDerivativeNullspaceModel

def toNullspaceKilled
    {form : GalerkinBilinearForm}
    {anchor : WhiteHoleLoadAnchor form}
    (model : FirstDerivativeNullspaceModel form anchor)
    (natural : NaturalBoundary form) :
    NullspaceKilled form natural anchor where
  uses_natural_boundary := natural.boundary_terms_vanish_proof
  uses_white_hole_load := anchor.source_to_load_proof
  diagonal_zero_detects := by
    intro x hDiagonal
    exact
      model.whiteHoleLoadAnchor_kills_constant
        x
        (model.diagonal_zero_implies_constant x hDiagonal)
        anchor.load_is_anchor

end FirstDerivativeNullspaceModel

structure FirstDerivativeAnchoredGalerkinActivity where
  form :
    GalerkinBilinearForm
  natural :
    NaturalBoundary form
  anchor :
    WhiteHoleLoadAnchor form
  nullspaceModel :
    FirstDerivativeNullspaceModel form anchor

namespace FirstDerivativeAnchoredGalerkinActivity

def nullspaceKilled
    (activity : FirstDerivativeAnchoredGalerkinActivity) :
    NullspaceKilled activity.form activity.natural activity.anchor :=
  FirstDerivativeNullspaceModel.toNullspaceKilled
    activity.nullspaceModel
    activity.natural

def toSPDGalerkinActivity
    (activity : FirstDerivativeAnchoredGalerkinActivity) :
    SPDGalerkinActivity :=
  SPDGalerkinActivity.naturalBoundary_whiteHoleLoadAnchor_implies_spd
    activity.form
    activity.natural
    activity.anchor
    (FirstDerivativeAnchoredGalerkinActivity.nullspaceKilled activity)

def firstDerivative_naturalBoundary_whiteHoleLoadAnchor_implies_spd
    (activity : FirstDerivativeAnchoredGalerkinActivity) :
    SPDGalerkinActivity :=
  FirstDerivativeAnchoredGalerkinActivity.toSPDGalerkinActivity activity

end FirstDerivativeAnchoredGalerkinActivity

structure CompilerAnchoredFirstDerivativeGalerkinActivity where
  activity :
    FirstDerivativeAnchoredGalerkinActivity
  compilerAnchor :
    CompilerWhiteHoleLoadAnchor activity.form
  compilerAnchor_realizes_whiteHoleLoad :
    compilerAnchor.anchor_loaded ->
      activity.anchor.source_to_load

namespace CompilerAnchoredFirstDerivativeGalerkinActivity

def toCompilerAnchoredGalerkinActivity
    (activity : CompilerAnchoredFirstDerivativeGalerkinActivity) :
    CompilerAnchoredGalerkinActivity where
  spd :=
    FirstDerivativeAnchoredGalerkinActivity.toSPDGalerkinActivity
      activity.activity
  compilerAnchor := activity.compilerAnchor
  compilerAnchor_realizes_whiteHoleLoad :=
    activity.compilerAnchor_realizes_whiteHoleLoad

theorem source_to_load
    (activity : CompilerAnchoredFirstDerivativeGalerkinActivity) :
    activity.activity.anchor.source_to_load :=
  CompilerAnchoredGalerkinActivity.source_to_load
    (CompilerAnchoredFirstDerivativeGalerkinActivity.toCompilerAnchoredGalerkinActivity
      activity)

end CompilerAnchoredFirstDerivativeGalerkinActivity

structure BendingAffineNullspaceModel
    (form : GalerkinBilinearForm)
    (anchor : WhiteHoleLoadAnchor form) where
  AffineMode : form.V -> Prop
  SlopeModeKilled : form.V -> Prop
  diagonal_zero_implies_affine :
    forall x,
      form.a x x = 0 -> AffineMode x
  whiteHoleLoadAnchor_and_slope_kill_affine :
    forall x,
      AffineMode x ->
        SlopeModeKilled x ->
          anchor.trace .load = form.zero ->
            x = form.zero

namespace BendingAffineNullspaceModel

def toNullspaceKilled
    {form : GalerkinBilinearForm}
    {anchor : WhiteHoleLoadAnchor form}
    (model : BendingAffineNullspaceModel form anchor)
    (natural : NaturalBoundary form)
    (slopeKilled :
      forall x,
        model.SlopeModeKilled x) :
    NullspaceKilled form natural anchor where
  uses_natural_boundary := natural.boundary_terms_vanish_proof
  uses_white_hole_load := anchor.source_to_load_proof
  diagonal_zero_detects := by
    intro x hDiagonal
    exact
      model.whiteHoleLoadAnchor_and_slope_kill_affine
        x
        (model.diagonal_zero_implies_affine x hDiagonal)
        (slopeKilled x)
        anchor.load_is_anchor

end BendingAffineNullspaceModel

def truthFirstDerivativeNullspaceModel :
    FirstDerivativeNullspaceModel
      truthGalerkinBilinearForm
      truthWhiteHoleLoadAnchor where
  ConstantMode := fun _ => True
  diagonal_zero_implies_constant := by
    intro x h
    trivial
  whiteHoleLoadAnchor_kills_constant := by
    intro x hConstant hAnchor
    cases x
    rfl

def truthFirstDerivativeAnchoredGalerkinActivity :
    FirstDerivativeAnchoredGalerkinActivity where
  form := truthGalerkinBilinearForm
  natural := truthNaturalBoundary
  anchor := truthWhiteHoleLoadAnchor
  nullspaceModel := truthFirstDerivativeNullspaceModel

def truthFirstDerivativeSPDGalerkinActivity :
    SPDGalerkinActivity :=
  FirstDerivativeAnchoredGalerkinActivity.toSPDGalerkinActivity
    truthFirstDerivativeAnchoredGalerkinActivity

theorem truthFirstDerivative_energySq_zero_detector
    (x : truthFirstDerivativeSPDGalerkinActivity.form.V) :
    (SPDGalerkinActivity.toEnergySqCertificate
        truthFirstDerivativeSPDGalerkinActivity).energySq x = 0 <->
      x =
        (SPDGalerkinActivity.toEnergySqCertificate
          truthFirstDerivativeSPDGalerkinActivity).zero :=
  EnergySqCertificate.energySq_eq_zero_iff_eq_zero
    (SPDGalerkinActivity.toEnergySqCertificate
      truthFirstDerivativeSPDGalerkinActivity)
    x

end Measurement
