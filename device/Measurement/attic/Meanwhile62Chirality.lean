import Measurement.Meanwhile62SmallAngle

/- MEANWHILE 62.6 -- CHIRALITY / RIGHT-HAND RULE. The small-angle read is
one-sided, so the next approximation needs an orientation convention. The
right-hand rule is that convention: electric/current direction crossed with the
magnetic direction names the positive propagation direction.

The electron does not change the convention. Its negative charge flips the
observed response relative to the conventional positive-current hand. Thus the
apparatus carries two facts:

* the field basis is right-handed;
* the electron response is the mirrored, left-handed read of that basis.

This module does not add a new coefficient. It only records the sign convention
that lets the asymmetric small-angle correction line up with the magnetic photon
response.
-/

namespace Measurement

inductive Chirality where
  | rightHanded
  | leftHanded
  | achiral
deriving Repr, DecidableEq

inductive RightHandAxis where
  | electricCurrent
  | magneticField
  | propagation
deriving Repr, DecidableEq

structure RightHandBasisRead where
  first : RightHandAxis
  second : RightHandAxis
  crossProduct : RightHandAxis
  convention : Chirality
  signConvention : Int
deriving Repr

def rightHandBasisRead : RightHandBasisRead :=
  { first := .electricCurrent
    second := .magneticField
    crossProduct := .propagation
    convention := .rightHanded
    signConvention := 1 }

def chiralityOfChargeUnit (chargeUnit : Int) : Chirality :=
  if chargeUnit = 0 then
    .achiral
  else if chargeUnit < 0 then
    .leftHanded
  else
    .rightHanded

def electronRightHandRuleChargeUnit : Int :=
  electronElaborationChargeReport.chargeUnit

def positronRightHandRuleChargeUnit : Int :=
  1

def electronResponseChirality : Chirality :=
  chiralityOfChargeUnit electronRightHandRuleChargeUnit

def positronResponseChirality : Chirality :=
  chiralityOfChargeUnit positronRightHandRuleChargeUnit

def rightHandRuleConventionPresent : Bool :=
  decide (rightHandBasisRead.convention = Chirality.rightHanded) &&
    decide (rightHandBasisRead.signConvention = 1)

def electronFlipsRightHandRule : Bool :=
  decide (electronRightHandRuleChargeUnit < 0) &&
    decide (electronResponseChirality = Chirality.leftHanded)

def positronKeepsRightHandRule : Bool :=
  decide (0 < positronRightHandRuleChargeUnit) &&
    decide (positronResponseChirality = Chirality.rightHanded)

def chiralMirrorPairDistinguished : Bool :=
  decide (electronResponseChirality ≠ positronResponseChirality)

def rightHandPhotonResponseAvailable : Bool :=
  magneticPhotonExchangeReport.photonMediatorPresent &&
    magneticPhotonExchangeReport.responseOnLightCone &&
    magneticPhotonExchangeReport.recoilCarriedByCooperPair

def smallAnglePositiveSideBendsWithRightHandRule : Bool :=
  decide (smallAnglePositiveSineMinusLineScaledAt36 < 0)

def smallAngleNegativeSideMirrorsRightHandRule : Bool :=
  decide (0 < smallAngleNegativeSineMinusLineScaledAt36)

def smallAngleChiralAsymmetryAvailable : Bool :=
  smallAngleApproximationReport.asymmetricOneSidedRead &&
    smallAnglePositiveSideBendsWithRightHandRule &&
    smallAngleNegativeSideMirrorsRightHandRule

def chiralitySignConventionCloses : Bool :=
  rightHandRuleConventionPresent &&
    rightHandPhotonResponseAvailable &&
    smallAngleChiralAsymmetryAvailable &&
    electronFlipsRightHandRule &&
    positronKeepsRightHandRule &&
    chiralMirrorPairDistinguished

structure ChiralityRightHandRuleReport where
  name : String
  interpretation : String
  basis : RightHandBasisRead
  photonResponseAvailable : Bool
  electronChargeUnit : Int
  positronChargeUnit : Int
  electronResponseChirality : Chirality
  positronResponseChirality : Chirality
  electronFlipsRightHandRule : Bool
  positronKeepsRightHandRule : Bool
  mirrorPairDistinguished : Bool
  positiveSmallAngleCorrectionScaledAt36 : Int
  negativeSmallAngleCorrectionScaledAt36 : Int
  positiveSideBendsWithRightHandRule : Bool
  negativeSideMirrorsRightHandRule : Bool
  smallAngleAsymmetryAvailable : Bool
  rightHandRuleIsSignConvention : Bool
  chiralityCertificate : Bool
deriving Repr

def chiralityRightHandRuleReport : ChiralityRightHandRuleReport :=
  { name := "chirality-right-hand-rule"
    interpretation :=
      "the right-hand rule fixes the positive field convention; the electron's negative charge mirrors the response, and the small-angle asymmetry supplies the signed witness"
    basis := rightHandBasisRead
    photonResponseAvailable := rightHandPhotonResponseAvailable
    electronChargeUnit := electronRightHandRuleChargeUnit
    positronChargeUnit := positronRightHandRuleChargeUnit
    electronResponseChirality := electronResponseChirality
    positronResponseChirality := positronResponseChirality
    electronFlipsRightHandRule := electronFlipsRightHandRule
    positronKeepsRightHandRule := positronKeepsRightHandRule
    mirrorPairDistinguished := chiralMirrorPairDistinguished
    positiveSmallAngleCorrectionScaledAt36 :=
      smallAnglePositiveSineMinusLineScaledAt36
    negativeSmallAngleCorrectionScaledAt36 :=
      smallAngleNegativeSineMinusLineScaledAt36
    positiveSideBendsWithRightHandRule :=
      smallAnglePositiveSideBendsWithRightHandRule
    negativeSideMirrorsRightHandRule :=
      smallAngleNegativeSideMirrorsRightHandRule
    smallAngleAsymmetryAvailable := smallAngleChiralAsymmetryAvailable
    rightHandRuleIsSignConvention := rightHandRuleConventionPresent
    chiralityCertificate := chiralitySignConventionCloses }

#eval chiralityRightHandRuleReport

end Measurement
