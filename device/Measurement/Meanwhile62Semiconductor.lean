import Measurement.Meanwhile62Photoelectric

/- MEANWHILE 62.4 -- SEMICONDUCTOR PLUS FLOW. The photoelectric read ejects an
electron into a free channel. In a semiconductor lattice, the same threshold
event is read as a band transition: a valence electron is promoted to the
conduction band and leaves a hole behind.

The hole is not an extra electron. It is the missing valence electron carried as
a positive mobile label. Microscopic electron hops and hole motion run in
opposite directions, but the conventional current read is positive in both
descriptions:

  electron: charge -1, microscopic hop -1, current +
  hole:     charge +1, microscopic flow +1, current +

That is the `+ flow`: a positive carrier read produced by moving a negative
electron through a finite lattice.
-/

namespace Measurement

inductive SemiconductorBand where
  | valence
  | conduction
deriving Repr, DecidableEq

inductive SemiconductorCarrier where
  | electron
  | hole
deriving Repr, DecidableEq

inductive SemiconductorFlowDirection where
  | minus
  | plus
  | neutral
deriving Repr, DecidableEq

def semiconductorDirectionOfSigned (value : Int) :
    SemiconductorFlowDirection :=
  if value = 0 then
    .neutral
  else if value < 0 then
    .minus
  else
    .plus

def semiconductorBandGapScaledAt18 : Nat :=
  photoelectricWorkFunctionScaledAt18

def semiconductorPhotonEnergyScaledAt18 : Nat :=
  photoelectricPhotonEnergyScaledAt18

def semiconductorPhotonAboveBandGap : Bool :=
  decide (semiconductorBandGapScaledAt18 <=
    semiconductorPhotonEnergyScaledAt18)

def semiconductorElectronPromoted : Bool :=
  photoelectricElectronEmitted && semiconductorPhotonAboveBandGap

def semiconductorHoleCreated : Bool :=
  semiconductorElectronPromoted

def semiconductorElectronChargeUnit : Int :=
  -1

def semiconductorHoleChargeUnit : Int :=
  1

def semiconductorElectronMicroscopicMotion : Int :=
  -1

def semiconductorHoleMicroscopicMotion : Int :=
  1

def semiconductorCarrierMagnitudeScaledAt18 : Nat :=
  photoelectricEmittedElectronChargeScaledAt18

def semiconductorCarrierKineticEnergyScaledAt18 : Nat :=
  photoelectricKineticEnergyScaledAt18

def semiconductorSignedConventionalFlowScaledAt18
    (chargeUnit motion : Int) (magnitude : Nat) : Int :=
  chargeUnit * motion * Int.ofNat magnitude

def semiconductorElectronConventionalFlowScaledAt18 : Int :=
  semiconductorSignedConventionalFlowScaledAt18
    semiconductorElectronChargeUnit semiconductorElectronMicroscopicMotion
    semiconductorCarrierMagnitudeScaledAt18

def semiconductorHoleConventionalFlowScaledAt18 : Int :=
  semiconductorSignedConventionalFlowScaledAt18
    semiconductorHoleChargeUnit semiconductorHoleMicroscopicMotion
    semiconductorCarrierMagnitudeScaledAt18

def semiconductorTotalPositiveFlowScaledAt18 : Int :=
  semiconductorElectronConventionalFlowScaledAt18 +
    semiconductorHoleConventionalFlowScaledAt18

def semiconductorPairNetChargeUnit : Int :=
  semiconductorElectronChargeUnit + semiconductorHoleChargeUnit

def semiconductorElectronHolePairNeutral : Bool :=
  decide (semiconductorPairNetChargeUnit = 0)

def semiconductorElectronFlowIsPositive : Bool :=
  decide (0 < semiconductorElectronConventionalFlowScaledAt18)

def semiconductorHoleFlowIsPositive : Bool :=
  decide (0 < semiconductorHoleConventionalFlowScaledAt18)

def semiconductorPlusFlowExists : Bool :=
  semiconductorElectronPromoted &&
    semiconductorHoleCreated &&
    semiconductorElectronFlowIsPositive &&
    semiconductorHoleFlowIsPositive &&
    decide (0 < semiconductorTotalPositiveFlowScaledAt18)

structure SemiconductorCarrierRead where
  carrier : SemiconductorCarrier
  band : SemiconductorBand
  chargeUnit : Int
  microscopicMotion : Int
  conventionalFlowScaledAt18 : Int
  conventionalDirection : SemiconductorFlowDirection
  carrierMagnitudeScaledAt18 : Nat
  kineticEnergyScaledAt18 : Nat
deriving Repr

def semiconductorElectronRead : SemiconductorCarrierRead :=
  { carrier := .electron
    band := .conduction
    chargeUnit := semiconductorElectronChargeUnit
    microscopicMotion := semiconductorElectronMicroscopicMotion
    conventionalFlowScaledAt18 :=
      semiconductorElectronConventionalFlowScaledAt18
    conventionalDirection :=
      semiconductorDirectionOfSigned
        semiconductorElectronConventionalFlowScaledAt18
    carrierMagnitudeScaledAt18 := semiconductorCarrierMagnitudeScaledAt18
    kineticEnergyScaledAt18 := semiconductorCarrierKineticEnergyScaledAt18 }

def semiconductorHoleRead : SemiconductorCarrierRead :=
  { carrier := .hole
    band := .valence
    chargeUnit := semiconductorHoleChargeUnit
    microscopicMotion := semiconductorHoleMicroscopicMotion
    conventionalFlowScaledAt18 :=
      semiconductorHoleConventionalFlowScaledAt18
    conventionalDirection :=
      semiconductorDirectionOfSigned
        semiconductorHoleConventionalFlowScaledAt18
    carrierMagnitudeScaledAt18 := semiconductorCarrierMagnitudeScaledAt18
    kineticEnergyScaledAt18 := semiconductorCarrierKineticEnergyScaledAt18 }

def semiconductorCarrierReads : List SemiconductorCarrierRead :=
  [semiconductorElectronRead, semiconductorHoleRead]

structure SemiconductorPlusFlowReport where
  name : String
  interpretation : String
  afterPhotoelectric : Bool
  bandGapScaledAt18 : Nat
  photonEnergyScaledAt18 : Nat
  photonAboveBandGap : Bool
  electronPromotedToConductionBand : Bool
  valenceHoleCreated : Bool
  carrierReads : List SemiconductorCarrierRead
  electronHolePairNetChargeUnit : Int
  electronHolePairNeutral : Bool
  electronConventionalFlowPositive : Bool
  holeConventionalFlowPositive : Bool
  totalPositiveFlowScaledAt18 : Int
  plusFlowExists : Bool
deriving Repr

def semiconductorPlusFlowReport : SemiconductorPlusFlowReport :=
  { name := "semiconductor-plus-flow"
    interpretation :=
      "a photon above the band gap promotes a valence electron, leaving a positive hole; the electron-hole pair is neutral, but the current read is positive flow"
    afterPhotoelectric := photoelectricElectronEmitted
    bandGapScaledAt18 := semiconductorBandGapScaledAt18
    photonEnergyScaledAt18 := semiconductorPhotonEnergyScaledAt18
    photonAboveBandGap := semiconductorPhotonAboveBandGap
    electronPromotedToConductionBand := semiconductorElectronPromoted
    valenceHoleCreated := semiconductorHoleCreated
    carrierReads := semiconductorCarrierReads
    electronHolePairNetChargeUnit := semiconductorPairNetChargeUnit
    electronHolePairNeutral := semiconductorElectronHolePairNeutral
    electronConventionalFlowPositive := semiconductorElectronFlowIsPositive
    holeConventionalFlowPositive := semiconductorHoleFlowIsPositive
    totalPositiveFlowScaledAt18 := semiconductorTotalPositiveFlowScaledAt18
    plusFlowExists := semiconductorPlusFlowExists }

#eval semiconductorPlusFlowReport

end Measurement
