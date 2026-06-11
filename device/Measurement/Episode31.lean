import Measurement.Episode30

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000
set_option allowUnsafeReducibility true

namespace Measurement

/-
__EPISODE 31__: _The Second Variation Is the Single Invariant_

Episode18 recovered the finite first Frechet term.
Episode24 split the coupled cubic variation into left first variation,
right first variation, and mixed coupling.

Here we name the mixed coupling as the finite second variation and prove:

1. The coupled difference decomposes as first-left + first-right + second.
2. Once the middle-node Euler-Lagrange equations vanish, the coupled
   difference is exactly the second variation.
3. The second-variation remainder is unique for this decomposition.
4. In the Galerkin realization, the second variation is the bilinear/Hessian
   invariant whose diagonal is energy-squared.

Residue left:
The full Hilbert norm still comes later.  This episode identifies the
invariant that the Hilbert geometry will measure.
-/

namespace CubicGaugeVariation

def secondVariation
    (action : FiniteGaugeAction) (path : CubicGaugePath)
    (variation : CubicGaugeVariation) : Int :=
  mixedCubicCoupling action path variation

theorem secondVariation_eq_mixedCubicCoupling
    (action : FiniteGaugeAction) (path : CubicGaugePath)
    (variation : CubicGaugeVariation) :
    secondVariation action path variation =
      mixedCubicCoupling action path variation := by
  rfl

theorem coupledCubicDifference_eq_left_right_plus_secondVariation
    (action : FiniteGaugeAction) (path : CubicGaugePath)
    (variation : CubicGaugeVariation) :
    coupledCubicDifference action path variation =
      CubicGaugePath.leftMiddleResidual
          action path (leftVariation variation) +
        CubicGaugePath.rightMiddleResidual
          action path (rightVariation variation) +
          secondVariation action path variation := by
  rw [coupledCubicDifference_eq_left_right_plus_mixed]
  rfl

theorem coupledCubicDifference_eq_secondVariation_of_middleResiduals_zero
    (action : FiniteGaugeAction) (path : CubicGaugePath)
    (variation : CubicGaugeVariation)
    (hLeft :
      CubicGaugePath.leftMiddleResidual
        action path (leftVariation variation) = 0)
    (hRight :
      CubicGaugePath.rightMiddleResidual
        action path (rightVariation variation) = 0) :
    coupledCubicDifference action path variation =
      secondVariation action path variation := by
  rw [coupledCubicDifference_eq_left_right_plus_secondVariation,
    hLeft, hRight]
  simp

def secondVariationVanished
    (action : FiniteGaugeAction) (path : CubicGaugePath)
    (variation : CubicGaugeVariation) : Prop :=
  secondVariation action path variation = 0

theorem secondVariationVanished_iff_mixedCouplingSolved
    (action : FiniteGaugeAction) (path : CubicGaugePath)
    (variation : CubicGaugeVariation) :
    secondVariationVanished action path variation <->
      mixedCouplingSolved action path variation := by
  rfl

theorem coupledCubicDifference_eq_zero_of_middleResiduals_and_secondVariation
    (action : FiniteGaugeAction) (path : CubicGaugePath)
    (variation : CubicGaugeVariation)
    (hLeft :
      CubicGaugePath.leftMiddleResidual
        action path (leftVariation variation) = 0)
    (hRight :
      CubicGaugePath.rightMiddleResidual
        action path (rightVariation variation) = 0)
    (hSecond : secondVariationVanished action path variation) :
    coupledCubicDifference action path variation = 0 :=
  coupledCubicDifference_eq_zero_of_middleResiduals_and_mixed
    action
    path
    variation
    hLeft
    hRight
    ((secondVariationVanished_iff_mixedCouplingSolved
      action
      path
      variation).1 hSecond)

def IsSecondVariationRemainder
    (action : FiniteGaugeAction) (path : CubicGaugePath)
    (R : CubicGaugeVariation -> Int) : Prop :=
  forall variation,
    coupledCubicDifference action path variation =
      CubicGaugePath.leftMiddleResidual
          action path (leftVariation variation) +
        CubicGaugePath.rightMiddleResidual
          action path (rightVariation variation) +
          R variation

theorem secondVariation_remainder_unique
    (action : FiniteGaugeAction) (path : CubicGaugePath)
    (R : CubicGaugeVariation -> Int)
    (hR : IsSecondVariationRemainder action path R) :
    forall variation,
      R variation =
        secondVariation action path variation := by
  intro variation
  have hCanonical :
      coupledCubicDifference action path variation =
        CubicGaugePath.leftMiddleResidual
            action path (leftVariation variation) +
          CubicGaugePath.rightMiddleResidual
            action path (rightVariation variation) +
            secondVariation action path variation :=
    coupledCubicDifference_eq_left_right_plus_secondVariation
      action
      path
      variation
  have hOther := hR variation
  omega

end CubicGaugeVariation

namespace CubicPartitionedLanczosApproximation

theorem supported_data_coupledCubicDifference_eq_secondVariation
    {action : FiniteGaugeAction} {path : CubicGaugePath}
    {range : AdmissibleRange}
    (approximation :
      CubicPartitionedLanczosApproximation action path range)
    (variation : CubicGaugeVariation)
    (hLeft :
      approximation.support.leftSupportedVariation
        (CubicGaugeVariation.leftVariation variation))
    (hRight :
      approximation.support.rightSupportedVariation
        (CubicGaugeVariation.rightVariation variation)) :
    CubicGaugeVariation.coupledCubicDifference action path variation =
      CubicGaugeVariation.secondVariation action path variation :=
  CubicGaugeVariation.coupledCubicDifference_eq_secondVariation_of_middleResiduals_zero
    action
    path
    variation
    (approximation.leftEulerLagrange
      (CubicGaugeVariation.leftVariation variation)
      hLeft)
    (approximation.rightEulerLagrange
      (CubicGaugeVariation.rightVariation variation)
      hRight)

theorem supported_data_and_secondVariation_solve_coupledCubicVariation
    {action : FiniteGaugeAction} {path : CubicGaugePath}
    {range : AdmissibleRange}
    (approximation :
      CubicPartitionedLanczosApproximation action path range)
    (variation : CubicGaugeVariation)
    (hLeft :
      approximation.support.leftSupportedVariation
        (CubicGaugeVariation.leftVariation variation))
    (hRight :
      approximation.support.rightSupportedVariation
        (CubicGaugeVariation.rightVariation variation))
    (hSecond :
      CubicGaugeVariation.secondVariationVanished
        action path variation) :
    CubicGaugeVariation.coupledCubicDifference action path variation = 0 :=
  CubicGaugeVariation.coupledCubicDifference_eq_zero_of_middleResiduals_and_secondVariation
    action
    path
    variation
    (approximation.leftEulerLagrange
      (CubicGaugeVariation.leftVariation variation)
      hLeft)
    (approximation.rightEulerLagrange
      (CubicGaugeVariation.rightVariation variation)
      hRight)
    hSecond

end CubicPartitionedLanczosApproximation

structure SecondVariationGalerkinRealization
    (action : FiniteGaugeAction) (path : CubicGaugePath)
    (spd : SPDGalerkinActivity) where
  leftActivity :
    CubicGaugeVariation -> spd.form.V
  rightActivity :
    CubicGaugeVariation -> spd.form.V
  secondVariation_matches_bilinear :
    forall variation,
      CubicGaugeVariation.secondVariation action path variation =
        spd.form.a (leftActivity variation) (rightActivity variation)

structure DiagonalSecondVariationGalerkinRealization
    (action : FiniteGaugeAction) (path : CubicGaugePath)
    (spd : SPDGalerkinActivity) where
  activity :
    CubicGaugeVariation -> spd.form.V
  secondVariation_matches_diagonal :
    forall variation,
      CubicGaugeVariation.secondVariation action path variation =
        spd.form.a (activity variation) (activity variation)

namespace DiagonalSecondVariationGalerkinRealization

theorem diagonal_secondVariation_positive_of_nonzero_activity
    {action : FiniteGaugeAction} {path : CubicGaugePath}
    {spd : SPDGalerkinActivity}
    (realization :
      DiagonalSecondVariationGalerkinRealization action path spd)
    (variation : CubicGaugeVariation)
    (hNonzero :
      realization.activity variation ≠ spd.form.zero) :
    0 < CubicGaugeVariation.secondVariation action path variation := by
  rw [realization.secondVariation_matches_diagonal]
  exact spd.positive_definite
    (realization.activity variation)
    hNonzero

theorem diagonal_secondVariation_magnitude_eq_energySq
    {action : FiniteGaugeAction} {path : CubicGaugePath}
    {spd : SPDGalerkinActivity}
    (realization :
      DiagonalSecondVariationGalerkinRealization action path spd)
    (variation : CubicGaugeVariation) :
    intActivityMagnitude
        (CubicGaugeVariation.secondVariation action path variation) =
      GalerkinBilinearForm.energySq
        spd.form
        (realization.activity variation) := by
  unfold GalerkinBilinearForm.energySq
  rw [realization.secondVariation_matches_diagonal]

end DiagonalSecondVariationGalerkinRealization

end Measurement
