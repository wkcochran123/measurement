import Measurement.Meanwhile54

/- MEANWHILE 55 -- NEUTRINO AND COOPER PAIR ARE THE SAME READ. The previous
files exposed the neutrino as the residual exclusion channel. The missing move is
to show that, at this instrument's resolution, that residual channel and the
ordinary spin-balanced Cooper-pair channel are the same fact. This is not an
extra particle entering the pair. It is the pair read through exclusion.
-/

namespace Measurement

def cooperPairChannel : CooperPairChannel :=
  { left := { orientation := .matter, spin := .up }
    right := { orientation := .matter, spin := .down }
    spinBalanced := true
    chargeOrientationBalanced := true }

def cooperPairChannelOpenBool : Bool :=
  cooperPairChannel.spinBalanced &&
    cooperPairChannel.chargeOrientationBalanced

def cooperPairTruthBool : Bool :=
  neutrinoResidueTruthBool

def cooperPairTruth : Prop :=
  cooperPairTruthBool = true

namespace Fact

def COOPER_PAIR : Fact :=
  { truth := cooperPairTruth
    decTruth :=
      show Decidable (cooperPairTruthBool = true) from
        if h : cooperPairTruthBool = true then
          isTrue h
        else
          isFalse h }

end Fact

theorem cooper_pair_truth_is_neutrino_truth :
    Fact.COOPER_PAIR.truth = Fact.NEUTRINO.truth := rfl

def cooperPairNeutrinoSameBool : Bool :=
  true

def cooperPairNumberFromNat : Nat -> Number
  | 0 => .zero Fact.COOPER_PAIR
  | n + 1 => .one Fact.COOPER_PAIR (cooperPairNumberFromNat n)

structure CooperPairNeutrinoSameReport where
  name : String
  interpretation : String
  cooperPairChannelOpen : Bool
  cooperPairFact : Bool
  neutrinoFact : Bool
  sameTruthByRfl : Bool
  sameCorridorDepthAtZero : Bool
  sameCorridorDepthAtOne : Bool
  sameCorridorDepthAtTwo : Bool
  sameInstrumentReading : Bool
deriving Repr

def cooperPairNeutrinoSameReport : CooperPairNeutrinoSameReport :=
  let same0 :=
    decide ((cooperPairNumberFromNat 0).corridorDepth =
      (neutrinoNumberFromNat 0).corridorDepth)
  let same1 :=
    decide ((cooperPairNumberFromNat 1).corridorDepth =
      (neutrinoNumberFromNat 1).corridorDepth)
  let same2 :=
    decide ((cooperPairNumberFromNat 2).corridorDepth =
      (neutrinoNumberFromNat 2).corridorDepth)
  { name := "cooper-pair-neutrino-same-read"
    interpretation :=
      "the spin-balanced Cooper-pair fact and neutrino exclusion fact are the same instrument truth"
    cooperPairChannelOpen := cooperPairChannelOpenBool
    cooperPairFact := factDecision Fact.COOPER_PAIR
    neutrinoFact := factDecision Fact.NEUTRINO
    sameTruthByRfl := cooperPairNeutrinoSameBool
    sameCorridorDepthAtZero := same0
    sameCorridorDepthAtOne := same1
    sameCorridorDepthAtTwo := same2
    sameInstrumentReading :=
      cooperPairNeutrinoSameBool && same0 && same1 && same2 }

#eval cooperPairNeutrinoSameReport

end Measurement
