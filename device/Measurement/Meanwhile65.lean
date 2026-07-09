import Measurement.Meanwhile64

/- MEANWHILE 65 -- NEUTRINO GRAVITY DELIVERY. The visible static from
Meanwhile64 is the transaction tax. In the apparatus, that tax is not a new
charge term: it is one mass-noise quantum on each side of the QFT alpha read.

The delivery channel is the neutrino/Cooper-pair same-read: the neutrino is the
exclusion carrier that can deliver the external gravity tug without opening the
charge horizon.
-/

namespace Measurement

def basisPointScale : Nat :=
  pow10 4

def scaledFractionToBasisPointsScaledAt18 (fractionScaledAt18 : Nat) : Nat :=
  fractionScaledAt18 * basisPointScale

def qftGravityQuantumScaledAt18 : Nat :=
  qftMassNoiseScaledAt18

def qftTransactionTaxScaledAt18 : Nat :=
  qftAlphaNoiseUpperScaledAt18 - qftAlphaNoiseLowerScaledAt18

def qftTransactionTaxIsTwoGravityQuanta : Bool :=
  decide (qftTransactionTaxScaledAt18 =
    qftGravityQuantumScaledAt18 + qftGravityQuantumScaledAt18)

def qftLowerTaxIsOneGravityQuantum : Bool :=
  decide (qftAlphaScaledAt18 - qftAlphaNoiseLowerScaledAt18 =
    qftGravityQuantumScaledAt18)

def qftUpperTaxIsOneGravityQuantum : Bool :=
  decide (qftAlphaNoiseUpperScaledAt18 - qftAlphaScaledAt18 =
    qftGravityQuantumScaledAt18)

def neutrinoGravityDeliveryBool : Bool :=
  factDecision Fact.NEUTRINO &&
    cooperPairHorizonReport.lastNeutrinoSameFact &&
    qftNoiseReport.noiseInterpretedAsMass &&
    !cooperPairHorizonReport.horizonContainsGravity &&
    !cooperPairHorizonReport.electronTugRead.affectsChargeHorizon

def qftGravityQuantumOfFlavorResidueBpsScaledAt18? : Option Nat :=
  qftNoiseReport.tugNoiseFractionOfFlavorResidueScaledAt18?.map
    scaledFractionToBasisPointsScaledAt18

def qftGravityQuantumOfSectorResidueBpsScaledAt18? : Option Nat :=
  qftNoiseReport.tugNoiseFractionOfQFTSectorResidueScaledAt18?.map
    scaledFractionToBasisPointsScaledAt18

structure NeutrinoGravityDeliveryReport where
  name : String
  interpretation : String
  neutrinoFact : Bool
  cooperPairFact : Bool
  neutrinoAndCooperPairSameRead : Bool
  chargeHorizonClosedToGravity : Bool
  tugAffectsChargeHorizon : Bool
  deliveredByNeutrino : Bool
  qftAlphaScaledAt18 : Nat
  gravityQuantumScaledAt18 : Nat
  transactionTaxScaledAt18 : Nat
  lowerTaxIsOneGravityQuantum : Bool
  upperTaxIsOneGravityQuantum : Bool
  transactionTaxIsTwoGravityQuanta : Bool
  gravityQuantumOfFlavorResidueBpsScaledAt18? : Option Nat
  gravityQuantumOfSectorResidueBpsScaledAt18? : Option Nat
  staticMassGlyphCounts : List Nat
deriving Repr

def neutrinoGravityDeliveryReport : NeutrinoGravityDeliveryReport :=
  { name := "neutrino-gravity-delivery"
    interpretation :=
      "the neutrino same-read delivers one mass-noise gravity quantum on each side of the QFT alpha transaction"
    neutrinoFact := factDecision Fact.NEUTRINO
    cooperPairFact := factDecision Fact.COOPER_PAIR
    neutrinoAndCooperPairSameRead :=
      cooperPairHorizonReport.lastNeutrinoSameFact
    chargeHorizonClosedToGravity :=
      !cooperPairHorizonReport.horizonContainsGravity
    tugAffectsChargeHorizon :=
      cooperPairHorizonReport.electronTugRead.affectsChargeHorizon
    deliveredByNeutrino := neutrinoGravityDeliveryBool
    qftAlphaScaledAt18 := qftAlphaScaledAt18
    gravityQuantumScaledAt18 := qftGravityQuantumScaledAt18
    transactionTaxScaledAt18 := qftTransactionTaxScaledAt18
    lowerTaxIsOneGravityQuantum := qftLowerTaxIsOneGravityQuantum
    upperTaxIsOneGravityQuantum := qftUpperTaxIsOneGravityQuantum
    transactionTaxIsTwoGravityQuanta :=
      qftTransactionTaxIsTwoGravityQuanta
    gravityQuantumOfFlavorResidueBpsScaledAt18? :=
      qftGravityQuantumOfFlavorResidueBpsScaledAt18?
    gravityQuantumOfSectorResidueBpsScaledAt18? :=
      qftGravityQuantumOfSectorResidueBpsScaledAt18?
    staticMassGlyphCounts := qftStaticMassCounts }

#eval neutrinoGravityDeliveryReport

end Measurement
