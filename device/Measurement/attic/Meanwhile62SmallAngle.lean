import Measurement.Meanwhile62Semiconductor

/- MEANWHILE 62.5 -- SMALL-ANGLE APPROXIMATION. The photoelectric boundary
leaves a natural angle in the apparatus:

  theta = workFunction / photonEnergy.

That is the part of the photon used to make the electron distinguishable. The
small-angle question is whether the first nonlinear sine term, `theta^3 / 6`,
is resolvable by the device. The term is signed: on the positive side the sine
curve sits below the line, while on the negative side it sits above the line.
If that signed correction is below the one-unit de Broglie wave residual, then
the finite read cannot distinguish `sin(theta)` from `theta` at the active
scale, even though the next scale still sees the asymmetry.

This is the pendulum miracle in device language: in the small-angle regime the
curved restoring law collapses to the linear one, so the period read is
amplitude-independent at the active scale.
-/

namespace Measurement

def ApparatusRatio.cube (q : ApparatusRatio) : ApparatusRatio :=
  q.sq.mul q

def smallAngleTheta : ApparatusRatio :=
  { numerator := photoelectricWorkFunctionScaledAt18
    denominator := Nat.max 1 photoelectricPhotonEnergyScaledAt18 }

def smallAngleThetaScaledAt18 : Nat :=
  smallAngleTheta.scaledFloor (pow10 18)

def smallAngleThetaScaledAt36 : Nat :=
  smallAngleTheta.scaledFloor (pow10 36)

def smallAngleCubicCorrection : ApparatusRatio :=
  smallAngleTheta.cube.divNat 6

def smallAngleCubicCorrectionScaledAt18 : Nat :=
  smallAngleCubicCorrection.scaledFloor (pow10 18)

def smallAngleCubicCorrectionScaledAt36 : Nat :=
  smallAngleCubicCorrection.scaledFloor (pow10 36)

def smallAngleSineApproxScaledAt18 : Nat :=
  smallAngleThetaScaledAt18 - smallAngleCubicCorrectionScaledAt18

def smallAngleSineApproxScaledAt36 : Nat :=
  smallAngleThetaScaledAt36 - smallAngleCubicCorrectionScaledAt36

def smallAnglePositiveLinearSignedScaledAt36 : Int :=
  Int.ofNat smallAngleThetaScaledAt36

def smallAnglePositiveSineSignedScaledAt36 : Int :=
  Int.ofNat smallAngleSineApproxScaledAt36

def smallAngleNegativeLinearSignedScaledAt36 : Int :=
  -Int.ofNat smallAngleThetaScaledAt36

def smallAngleNegativeSineSignedScaledAt36 : Int :=
  -Int.ofNat smallAngleSineApproxScaledAt36

def smallAnglePositiveSineMinusLineScaledAt36 : Int :=
  smallAnglePositiveSineSignedScaledAt36 -
    smallAnglePositiveLinearSignedScaledAt36

def smallAngleNegativeSineMinusLineScaledAt36 : Int :=
  smallAngleNegativeSineSignedScaledAt36 -
    smallAngleNegativeLinearSignedScaledAt36

def smallAnglePositiveBendsBelowLinear : Bool :=
  decide
    (smallAnglePositiveSineSignedScaledAt36 <
      smallAnglePositiveLinearSignedScaledAt36)

def smallAngleNegativeBendsAboveLinear : Bool :=
  decide
    (smallAngleNegativeLinearSignedScaledAt36 <
      smallAngleNegativeSineSignedScaledAt36)

def smallAngleSignedErrorsOppose : Bool :=
  decide
    (smallAnglePositiveSineMinusLineScaledAt36 +
      smallAngleNegativeSineMinusLineScaledAt36 = 0)

def smallAngleSineOverThetaScaledAt18? : Option Nat :=
  if smallAngleThetaScaledAt18 = 0 then
    none
  else
    some
      (smallAngleSineApproxScaledAt18 * pow10 18 /
        smallAngleThetaScaledAt18)

def smallAngleCubicBelowWaveResidual : Bool :=
  decide
    (smallAngleCubicCorrectionScaledAt18 <=
      photoelectricWaveResidualScaledAt18)

def smallAngleLinearCollapseAtScale18 : Bool :=
  decide (smallAngleSineApproxScaledAt18 = smallAngleThetaScaledAt18)

def smallAnglePendulumLinearRegime : Bool :=
  photoelectricElectronEmitted &&
    smallAngleCubicBelowWaveResidual &&
    smallAngleLinearCollapseAtScale18

def smallAngleAsymmetricOneSidedRead : Bool :=
  smallAnglePositiveBendsBelowLinear &&
    smallAngleNegativeBendsAboveLinear &&
    smallAngleSignedErrorsOppose

structure SmallAngleApproximationReport where
  name : String
  interpretation : String
  angleSource : String
  photonEnergyScaledAt18 : Nat
  workFunctionScaledAt18 : Nat
  thetaScaledAt18 : Nat
  thetaScaledAt36 : Nat
  sineLinearReadScaledAt18 : Nat
  sineApproxScaledAt36 : Nat
  cubicCorrectionScaledAt18 : Nat
  cubicCorrectionScaledAt36 : Nat
  positiveLinearSignedScaledAt36 : Int
  positiveSineSignedScaledAt36 : Int
  positiveSineMinusLineScaledAt36 : Int
  negativeLinearSignedScaledAt36 : Int
  negativeSineSignedScaledAt36 : Int
  negativeSineMinusLineScaledAt36 : Int
  positiveBendsBelowLinear : Bool
  negativeBendsAboveLinear : Bool
  signedErrorsOppose : Bool
  asymmetricOneSidedRead : Bool
  waveResidualScaledAt18 : Nat
  cubicBelowWaveResidual : Bool
  sineEqualsThetaAtScale18 : Bool
  sineOverThetaScaledAt18? : Option Nat
  pendulumLinearRegime : Bool
  periodIndependentOfAmplitude : Bool
  photoelectronEmitted : Bool
deriving Repr

def smallAngleApproximationReport : SmallAngleApproximationReport :=
  { name := "small-angle-approximation"
    interpretation :=
      "the finite instrument cannot resolve the signed theta^3 / 6 sine correction at scale 18; at scale 36 the positive side bends below the line and the negative side bends above it"
    angleSource :=
      "photoelectric work function divided by de Broglie photon energy"
    photonEnergyScaledAt18 := photoelectricPhotonEnergyScaledAt18
    workFunctionScaledAt18 := photoelectricWorkFunctionScaledAt18
    thetaScaledAt18 := smallAngleThetaScaledAt18
    thetaScaledAt36 := smallAngleThetaScaledAt36
    sineLinearReadScaledAt18 := smallAngleSineApproxScaledAt18
    sineApproxScaledAt36 := smallAngleSineApproxScaledAt36
    cubicCorrectionScaledAt18 := smallAngleCubicCorrectionScaledAt18
    cubicCorrectionScaledAt36 := smallAngleCubicCorrectionScaledAt36
    positiveLinearSignedScaledAt36 :=
      smallAnglePositiveLinearSignedScaledAt36
    positiveSineSignedScaledAt36 :=
      smallAnglePositiveSineSignedScaledAt36
    positiveSineMinusLineScaledAt36 :=
      smallAnglePositiveSineMinusLineScaledAt36
    negativeLinearSignedScaledAt36 :=
      smallAngleNegativeLinearSignedScaledAt36
    negativeSineSignedScaledAt36 :=
      smallAngleNegativeSineSignedScaledAt36
    negativeSineMinusLineScaledAt36 :=
      smallAngleNegativeSineMinusLineScaledAt36
    positiveBendsBelowLinear := smallAnglePositiveBendsBelowLinear
    negativeBendsAboveLinear := smallAngleNegativeBendsAboveLinear
    signedErrorsOppose := smallAngleSignedErrorsOppose
    asymmetricOneSidedRead := smallAngleAsymmetricOneSidedRead
    waveResidualScaledAt18 := photoelectricWaveResidualScaledAt18
    cubicBelowWaveResidual := smallAngleCubicBelowWaveResidual
    sineEqualsThetaAtScale18 := smallAngleLinearCollapseAtScale18
    sineOverThetaScaledAt18? := smallAngleSineOverThetaScaledAt18?
    pendulumLinearRegime := smallAnglePendulumLinearRegime
    periodIndependentOfAmplitude := smallAnglePendulumLinearRegime
    photoelectronEmitted := photoelectricElectronEmitted }

#eval smallAngleApproximationReport

end Measurement
