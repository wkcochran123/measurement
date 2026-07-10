import Measurement.Meanwhile68

/- MEANWHILE 69 -- CARRIED ANTIMATTER VARIANCE. The one-quantum gravity tax was
too small because it was only the local delivery quantum. The missing term is
the anti-Cooper-pair channel that the neutrino construction leaves unoccupied.

The anti-pair is open, spin balanced, and charge-orientation balanced. That does
not mean the apparatus may throw the residue away. The unoccupied anti-pair is
the exclusion channel, so its residue is carried as variance around the QFT alpha
center. The maximum simultaneous antimatter read is the full spin-up/spin-down
anti-pair variance capacity; it widens the read and leaves the center unchanged.
-/

namespace Measurement

def antiCooperPairMembers : List PairMember :=
  [antiCooperPairChannel.left, antiCooperPairChannel.right]

def isAntimatterMember (member : PairMember) : Bool :=
  decide (member.orientation = .antimatter)

def antimatterVarianceMemberCount : Nat :=
  antiCooperPairMembers.foldl
    (fun count member => if isAntimatterMember member then count.succ else count)
    0

def antiCooperPairResidueCarried : Bool :=
  antiCooperPairChannelOpenBool && !antiCooperPairOccupiedBool

def antimatterResidueAmplitudeScaledAt18 : Nat :=
  horizonFlavorColorAlphaReport.flavorRead.residueScaledAt18

def antimatterPairResidueAmplitudeScaledAt18 : Nat :=
  antimatterResidueAmplitudeScaledAt18 * antimatterVarianceMemberCount

def antimatterResidueVarianceScaledAt36 : Nat :=
  square antimatterResidueAmplitudeScaledAt18

def antimatterPairResidueVarianceScaledAt36 : Nat :=
  square antimatterPairResidueAmplitudeScaledAt18

def antimatterResidueAmplitudeQuanta : Nat :=
  taxQuotient antimatterResidueAmplitudeScaledAt18 qftGravityQuantumScaledAt18

def antimatterResidueAmplitudeRemainderScaledAt18 : Nat :=
  taxRemainder antimatterResidueAmplitudeScaledAt18 qftGravityQuantumScaledAt18

def antimatterPairResidueAmplitudeQuanta : Nat :=
  taxQuotient antimatterPairResidueAmplitudeScaledAt18
    qftGravityQuantumScaledAt18

def antimatterPairResidueAmplitudeRemainderScaledAt18 : Nat :=
  taxRemainder antimatterPairResidueAmplitudeScaledAt18
    qftGravityQuantumScaledAt18

def antimatterVarianceLowerAlphaScaledAt18 : Nat :=
  qftAlphaScaledAt18 - antimatterResidueAmplitudeScaledAt18

def antimatterVarianceUpperAlphaScaledAt18 : Nat :=
  qftAlphaScaledAt18 + antimatterResidueAmplitudeScaledAt18

def antimatterPairVarianceLowerAlphaScaledAt18 : Nat :=
  qftAlphaScaledAt18 - antimatterPairResidueAmplitudeScaledAt18

def antimatterPairVarianceUpperAlphaScaledAt18 : Nat :=
  qftAlphaScaledAt18 + antimatterPairResidueAmplitudeScaledAt18

def antimatterVarianceOfAlphaBpsScaledAt18? : Option Nat :=
  (ratioScaledAt18? antimatterResidueAmplitudeScaledAt18
    qftAlphaScaledAt18).map scaledFractionToBasisPointsScaledAt18

def antimatterPairVarianceOfAlphaBpsScaledAt18? : Option Nat :=
  (ratioScaledAt18? antimatterPairResidueAmplitudeScaledAt18
    qftAlphaScaledAt18).map scaledFractionToBasisPointsScaledAt18

def maxSimultaneousAntimatterAmplitudeScaledAt18 : Nat :=
  antimatterPairResidueAmplitudeScaledAt18

def maxSimultaneousAntimatterVarianceScaledAt36 : Nat :=
  antimatterPairResidueVarianceScaledAt36

def maxSimultaneousAntimatterQuanta : Nat :=
  antimatterPairResidueAmplitudeQuanta

def maxSimultaneousAntimatterRemainderScaledAt18 : Nat :=
  antimatterPairResidueAmplitudeRemainderScaledAt18

structure AntimatterVarianceReport where
  name : String
  interpretation : String
  antiCooperPairChannelOpen : Bool
  antiCooperPairOccupied : Bool
  antiCooperPairResidueCarried : Bool
  antiCooperPairFact : Bool
  neutrinoFact : Bool
  antimatterVarianceMemberCount : Nat
  qftAlphaScaledAt18 : Nat
  gravityQuantumScaledAt18 : Nat
  localGravityTaxScaledAt18 : Nat
  antimatterResidueAmplitudeScaledAt18 : Nat
  antimatterResidueVarianceScaledAt36 : Nat
  antimatterResidueAmplitudeQuanta : Nat
  antimatterResidueAmplitudeRemainderScaledAt18 : Nat
  antimatterVarianceLowerAlphaScaledAt18 : Nat
  antimatterVarianceUpperAlphaScaledAt18 : Nat
  antimatterVarianceLowerInverseScaledAt18? : Option Nat
  antimatterVarianceUpperInverseScaledAt18? : Option Nat
  antimatterVarianceOfAlphaBpsScaledAt18? : Option Nat
  antimatterPairResidueAmplitudeScaledAt18 : Nat
  antimatterPairResidueVarianceScaledAt36 : Nat
  antimatterPairResidueAmplitudeQuanta : Nat
  antimatterPairResidueAmplitudeRemainderScaledAt18 : Nat
  antimatterPairVarianceLowerAlphaScaledAt18 : Nat
  antimatterPairVarianceUpperAlphaScaledAt18 : Nat
  antimatterPairVarianceLowerInverseScaledAt18? : Option Nat
  antimatterPairVarianceUpperInverseScaledAt18? : Option Nat
  antimatterPairVarianceOfAlphaBpsScaledAt18? : Option Nat
  maxSimultaneousAntimatterAmplitudeScaledAt18 : Nat
  maxSimultaneousAntimatterVarianceScaledAt36 : Nat
  maxSimultaneousAntimatterQuanta : Nat
  maxSimultaneousAntimatterRemainderScaledAt18 : Nat
  centerUnchanged : Bool
deriving Repr

def antimatterVarianceReport : AntimatterVarianceReport :=
  { name := "carried-antimatter-variance"
    interpretation :=
      "carry the open but unoccupied anti-Cooper-pair residue as variance instead of throwing it away"
    antiCooperPairChannelOpen := antiCooperPairChannelOpenBool
    antiCooperPairOccupied := antiCooperPairOccupiedBool
    antiCooperPairResidueCarried := antiCooperPairResidueCarried
    antiCooperPairFact := factDecision Fact.ANTI_COOPER_PAIR
    neutrinoFact := factDecision Fact.NEUTRINO
    antimatterVarianceMemberCount := antimatterVarianceMemberCount
    qftAlphaScaledAt18 := qftAlphaScaledAt18
    gravityQuantumScaledAt18 := qftGravityQuantumScaledAt18
    localGravityTaxScaledAt18 := oneSidedTransactionTaxScaledAt18
    antimatterResidueAmplitudeScaledAt18 :=
      antimatterResidueAmplitudeScaledAt18
    antimatterResidueVarianceScaledAt36 :=
      antimatterResidueVarianceScaledAt36
    antimatterResidueAmplitudeQuanta := antimatterResidueAmplitudeQuanta
    antimatterResidueAmplitudeRemainderScaledAt18 :=
      antimatterResidueAmplitudeRemainderScaledAt18
    antimatterVarianceLowerAlphaScaledAt18 :=
      antimatterVarianceLowerAlphaScaledAt18
    antimatterVarianceUpperAlphaScaledAt18 :=
      antimatterVarianceUpperAlphaScaledAt18
    antimatterVarianceLowerInverseScaledAt18? :=
      alphaInverseReadScaledAt18? antimatterVarianceLowerAlphaScaledAt18
    antimatterVarianceUpperInverseScaledAt18? :=
      alphaInverseReadScaledAt18? antimatterVarianceUpperAlphaScaledAt18
    antimatterVarianceOfAlphaBpsScaledAt18? :=
      antimatterVarianceOfAlphaBpsScaledAt18?
    antimatterPairResidueAmplitudeScaledAt18 :=
      antimatterPairResidueAmplitudeScaledAt18
    antimatterPairResidueVarianceScaledAt36 :=
      antimatterPairResidueVarianceScaledAt36
    antimatterPairResidueAmplitudeQuanta :=
      antimatterPairResidueAmplitudeQuanta
    antimatterPairResidueAmplitudeRemainderScaledAt18 :=
      antimatterPairResidueAmplitudeRemainderScaledAt18
    antimatterPairVarianceLowerAlphaScaledAt18 :=
      antimatterPairVarianceLowerAlphaScaledAt18
    antimatterPairVarianceUpperAlphaScaledAt18 :=
      antimatterPairVarianceUpperAlphaScaledAt18
    antimatterPairVarianceLowerInverseScaledAt18? :=
      alphaInverseReadScaledAt18?
        antimatterPairVarianceLowerAlphaScaledAt18
    antimatterPairVarianceUpperInverseScaledAt18? :=
      alphaInverseReadScaledAt18?
        antimatterPairVarianceUpperAlphaScaledAt18
    antimatterPairVarianceOfAlphaBpsScaledAt18? :=
      antimatterPairVarianceOfAlphaBpsScaledAt18?
    maxSimultaneousAntimatterAmplitudeScaledAt18 :=
      maxSimultaneousAntimatterAmplitudeScaledAt18
    maxSimultaneousAntimatterVarianceScaledAt36 :=
      maxSimultaneousAntimatterVarianceScaledAt36
    maxSimultaneousAntimatterQuanta := maxSimultaneousAntimatterQuanta
    maxSimultaneousAntimatterRemainderScaledAt18 :=
      maxSimultaneousAntimatterRemainderScaledAt18
    centerUnchanged :=
      decide (qftAlphaScaledAt18 = qftAlphaReport.qftAlphaScaledAt18) }

#eval antimatterVarianceReport

end Measurement
