import Measurement.Meanwhile77

/- MEANWHILE 78 -- SPINOR END INTO THE ANTIMATTER KNOB. The previous layer
proved that the finite Yang-Mills/Dirac antimatter model closes. This layer
names the actual plug:

  spinor plus --one vector turn--> spinor minus --charge conjugate--> antimatter

The spinor connection supplies the sign-changing end. The antimatter knob is
the carried anti-Cooper-pair variance channel. Plugging them together does not
move the alpha center; it selects the positive antimatter side of the symmetric
variance envelope.
-/

namespace Measurement

def finiteMatterOrientationOfSpinorSheet :
    FiniteSpinorSheet -> FiniteMatterOrientation
  | .plus => .matter
  | .minus => .antimatter

structure FiniteSpinorEndRead where
  name : String
  initialSheet : FiniteSpinorSheet
  afterOneVectorTurn : FiniteSpinorSheet
  afterTwoVectorTurns : FiniteSpinorSheet
  orientationAfterOneVectorTurn : FiniteMatterOrientation
  changesSignAfterOneVectorTurn : Bool
  returnsAfterTwoVectorTurns : Bool
  connectionMagnitudeScaledAt18 : Nat
  connectionSignedScaledAt18 : Int
  spinorEndAvailable : Bool
deriving Repr

def finiteSpinorEndRead : FiniteSpinorEndRead :=
  { name := "finite-spinor-end"
    initialSheet := finiteSpinorInitialState.sheet
    afterOneVectorTurn := finiteSpinorAfterOneVectorTurn
    afterTwoVectorTurns := finiteSpinorAfterTwoVectorTurns
    orientationAfterOneVectorTurn :=
      finiteMatterOrientationOfSpinorSheet finiteSpinorAfterOneVectorTurn
    changesSignAfterOneVectorTurn :=
      finiteSpinorConnectionReport.changesSignAfterOneVectorTurn
    returnsAfterTwoVectorTurns :=
      finiteSpinorConnectionReport.returnsAfterTwoVectorTurns
    connectionMagnitudeScaledAt18 :=
      finiteSpinorConnectionReport.spinorConnectionTaxScaledAt18
    connectionSignedScaledAt18 :=
      finiteSpinorConnectionReport.spinorConnectionSignedScaledAt18
    spinorEndAvailable :=
      finiteSpinorConnectionReport.spinorConnectionApplies &&
        finiteSpinorConnectionReport.changesSignAfterOneVectorTurn &&
        decide
          (finiteMatterOrientationOfSpinorSheet finiteSpinorAfterOneVectorTurn =
            FiniteMatterOrientation.antimatter) }

def finiteSpinorPlugsAntimatterKnob : Bool :=
  finiteSpinorEndRead.spinorEndAvailable &&
    finiteAntimatterYangMillsDiracReport.modelCloses &&
    finiteAntimatterYangMillsDiracReport.yangMillsRead.yangMillsCloses &&
    finiteAntimatterYangMillsDiracReport.diracRead.diracChannelCloses

def finiteSpinorAntimatterKnobMagnitudeScaledAt18 : Nat :=
  if finiteSpinorPlugsAntimatterKnob then
    finiteAntimatterYangMillsDiracReport.antimatterAmplitudeScaledAt18
  else
    0

def finiteSpinorAntimatterKnobOutputSignedScaledAt18 : Int :=
  if finiteSpinorPlugsAntimatterKnob then
    Int.ofNat finiteSpinorAntimatterKnobMagnitudeScaledAt18
  else
    0

def finiteSpinorAntimatterKnobGainScaledAt18? : Option Nat :=
  ratioScaledAt18? finiteSpinorAntimatterKnobMagnitudeScaledAt18
    finiteSpinorEndRead.connectionMagnitudeScaledAt18

def finiteSpinorAntimatterSelectedAlphaScaledAt18 : Nat :=
  if finiteSpinorEndRead.orientationAfterOneVectorTurn =
      FiniteMatterOrientation.antimatter then
    finiteAntimatterYangMillsDiracReport.upperAlphaWithAntimatterScaledAt18
  else
    finiteAntimatterYangMillsDiracReport.centerAlphaScaledAt18

def finiteSpinorAntimatterSelectedInverseAlphaScaledAt18? : Option Nat :=
  alphaInverseReadScaledAt18? finiteSpinorAntimatterSelectedAlphaScaledAt18

structure FiniteSpinorAntimatterKnobReport where
  name : String
  interpretation : String
  spinorEnd : FiniteSpinorEndRead
  diracChannelCloses : Bool
  yangMillsCloses : Bool
  antimatterModelCloses : Bool
  knobPlugCloses : Bool
  knobInputSignedScaledAt18 : Int
  knobOutputSignedScaledAt18 : Int
  knobMagnitudeScaledAt18 : Nat
  knobGainScaledAt18? : Option Nat
  centerAlphaScaledAt18 : Nat
  centerInverseAlphaScaledAt18? : Option Nat
  lowerAlphaWithAntimatterScaledAt18 : Nat
  upperAlphaWithAntimatterScaledAt18 : Nat
  selectedAntimatterAlphaScaledAt18 : Nat
  selectedAntimatterInverseAlphaScaledAt18? : Option Nat
  centerUnchangedByKnob : Bool
deriving Repr

def finiteSpinorAntimatterKnobReport :
    FiniteSpinorAntimatterKnobReport :=
  { name := "finite-spinor-antimatter-knob"
    interpretation :=
      "plug the sign-changing spinor end into the antimatter variance knob; the minus sheet selects the positive charge-conjugate side"
    spinorEnd := finiteSpinorEndRead
    diracChannelCloses :=
      finiteAntimatterYangMillsDiracReport.diracRead.diracChannelCloses
    yangMillsCloses :=
      finiteAntimatterYangMillsDiracReport.yangMillsRead.yangMillsCloses
    antimatterModelCloses :=
      finiteAntimatterYangMillsDiracReport.modelCloses
    knobPlugCloses := finiteSpinorPlugsAntimatterKnob
    knobInputSignedScaledAt18 :=
      finiteSpinorEndRead.connectionSignedScaledAt18
    knobOutputSignedScaledAt18 :=
      finiteSpinorAntimatterKnobOutputSignedScaledAt18
    knobMagnitudeScaledAt18 :=
      finiteSpinorAntimatterKnobMagnitudeScaledAt18
    knobGainScaledAt18? :=
      finiteSpinorAntimatterKnobGainScaledAt18?
    centerAlphaScaledAt18 :=
      finiteAntimatterYangMillsDiracReport.centerAlphaScaledAt18
    centerInverseAlphaScaledAt18? :=
      finiteAntimatterYangMillsDiracReport.centerInverseAlphaScaledAt18?
    lowerAlphaWithAntimatterScaledAt18 :=
      finiteAntimatterYangMillsDiracReport.lowerAlphaWithAntimatterScaledAt18
    upperAlphaWithAntimatterScaledAt18 :=
      finiteAntimatterYangMillsDiracReport.upperAlphaWithAntimatterScaledAt18
    selectedAntimatterAlphaScaledAt18 :=
      finiteSpinorAntimatterSelectedAlphaScaledAt18
    selectedAntimatterInverseAlphaScaledAt18? :=
      finiteSpinorAntimatterSelectedInverseAlphaScaledAt18?
    centerUnchangedByKnob :=
      decide
        (finiteAntimatterYangMillsDiracReport.centerAlphaScaledAt18 =
          finiteMechanicsAlphaEstimateScaledAt18) }

#eval finiteSpinorAntimatterKnobReport

end Measurement
