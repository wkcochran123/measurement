import Measurement.Meanwhile69

/- MEANWHILE 70 -- MAXIMUM SIMULTANEOUS ANTIMATTER. The previous tax dial is
not a measurement: if an amplification can be chosen by hand, it can fit any
target. The apparatus now carries the open anti-Cooper-pair residue as variance.

This file asks for the largest amount of antimatter the current universe-state
can carry at one time. In this device that is the full spin-up/spin-down
anti-Cooper-pair variance capacity. The alpha center is unchanged; the anti-pair
only supplies the maximum simultaneous variance envelope.
-/

namespace Measurement

structure AntimatterCapacityRead where
  channel : String
  memberCount : Nat
  amplitudeScaledAt18 : Nat
  varianceScaledAt36 : Nat
  amplitudeQuanta : Nat
  amplitudeRemainderScaledAt18 : Nat
  lowerAlphaScaledAt18 : Nat
  upperAlphaScaledAt18 : Nat
  lowerInverseAlphaScaledAt18? : Option Nat
  upperInverseAlphaScaledAt18? : Option Nat
deriving Repr

def singleAntimatterCapacityRead : AntimatterCapacityRead :=
  { channel := "single-open-antimatter-channel"
    memberCount := 1
    amplitudeScaledAt18 := antimatterResidueAmplitudeScaledAt18
    varianceScaledAt36 := antimatterResidueVarianceScaledAt36
    amplitudeQuanta := antimatterResidueAmplitudeQuanta
    amplitudeRemainderScaledAt18 :=
      antimatterResidueAmplitudeRemainderScaledAt18
    lowerAlphaScaledAt18 := antimatterVarianceLowerAlphaScaledAt18
    upperAlphaScaledAt18 := antimatterVarianceUpperAlphaScaledAt18
    lowerInverseAlphaScaledAt18? :=
      alphaInverseReadScaledAt18? antimatterVarianceLowerAlphaScaledAt18
    upperInverseAlphaScaledAt18? :=
      alphaInverseReadScaledAt18? antimatterVarianceUpperAlphaScaledAt18 }

def pairAntimatterCapacityRead : AntimatterCapacityRead :=
  { channel := "spin-up-spin-down-anti-pair"
    memberCount := antimatterVarianceMemberCount
    amplitudeScaledAt18 := antimatterPairResidueAmplitudeScaledAt18
    varianceScaledAt36 := antimatterPairResidueVarianceScaledAt36
    amplitudeQuanta := antimatterPairResidueAmplitudeQuanta
    amplitudeRemainderScaledAt18 :=
      antimatterPairResidueAmplitudeRemainderScaledAt18
    lowerAlphaScaledAt18 := antimatterPairVarianceLowerAlphaScaledAt18
    upperAlphaScaledAt18 := antimatterPairVarianceUpperAlphaScaledAt18
    lowerInverseAlphaScaledAt18? :=
      alphaInverseReadScaledAt18? antimatterPairVarianceLowerAlphaScaledAt18
    upperInverseAlphaScaledAt18? :=
      alphaInverseReadScaledAt18? antimatterPairVarianceUpperAlphaScaledAt18 }

structure MaxSimultaneousAntimatterReport where
  name : String
  interpretation : String
  antiCooperPairChannelOpen : Bool
  antiCooperPairOccupied : Bool
  antiCooperPairResidueCarried : Bool
  noFreeAmplificationDial : Bool
  qftAlphaScaledAt18 : Nat
  qftInverseAlphaScaledAt18? : Option Nat
  reads : List AntimatterCapacityRead
  maximumChannel : String
  maximumAmplitudeScaledAt18 : Nat
  maximumVarianceScaledAt36 : Nat
  maximumQuanta : Nat
  maximumRemainderScaledAt18 : Nat
  maximumComesFromFullAntiPair : Bool
  centerUnchanged : Bool
deriving Repr

def maxSimultaneousAntimatterReport :
    MaxSimultaneousAntimatterReport :=
  { name := "maximum-simultaneous-antimatter"
    interpretation :=
      "predict the maximum simultaneous antimatter capacity by carrying the open anti-Cooper-pair residue as variance"
    antiCooperPairChannelOpen := antiCooperPairChannelOpenBool
    antiCooperPairOccupied := antiCooperPairOccupiedBool
    antiCooperPairResidueCarried := antiCooperPairResidueCarried
    noFreeAmplificationDial := true
    qftAlphaScaledAt18 := qftAlphaScaledAt18
    qftInverseAlphaScaledAt18? := qftAlphaReport.qftInverseAlphaScaledAt18?
    reads := [singleAntimatterCapacityRead, pairAntimatterCapacityRead]
    maximumChannel := "spin-up-spin-down-anti-pair"
    maximumAmplitudeScaledAt18 :=
      maxSimultaneousAntimatterAmplitudeScaledAt18
    maximumVarianceScaledAt36 :=
      maxSimultaneousAntimatterVarianceScaledAt36
    maximumQuanta := maxSimultaneousAntimatterQuanta
    maximumRemainderScaledAt18 :=
      maxSimultaneousAntimatterRemainderScaledAt18
    maximumComesFromFullAntiPair :=
      decide
        (maxSimultaneousAntimatterAmplitudeScaledAt18 =
          pairAntimatterCapacityRead.amplitudeScaledAt18)
    centerUnchanged :=
      decide (qftAlphaScaledAt18 = qftAlphaReport.qftAlphaScaledAt18) }

#eval maxSimultaneousAntimatterReport

end Measurement
