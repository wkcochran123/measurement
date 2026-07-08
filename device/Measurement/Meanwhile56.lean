import Measurement.Meanwhile55

/- MEANWHILE 56 -- CRANK THE SAME READ THREE TIMES. The Cooper-pair fact and
the neutrino fact are the same instrument truth. Now crank that same read three
times and report whether the equality survives as both number depth and carried
orbit state.
-/

namespace Measurement

def cooperPairNeutrinoSameCrankCount : Nat :=
  3

def cooperPairNeutrinoSameCrankState? : Option OrbitCarryState :=
  defaultAdjacentWobbleReport?.map fun aperture =>
    neutrinoCrankStateAfterThree aperture cavendishChargeMassNormalization

structure CooperPairNeutrinoThreeCrankReport where
  name : String
  interpretation : String
  crankCount : Nat
  sameInstrumentReadingBeforeCrank : Bool
  cooperPairFact : Bool
  neutrinoFact : Bool
  cooperPairNumberDepthAfterCrank : Nat
  neutrinoNumberDepthAfterCrank : Nat
  depthsMatchAfterCrank : Bool
  crankedState : Option OrbitCarryState
  selectedFaceAfterCrank : Option CorridorFace
  carriedResidueNumeratorAfterCrank : Option Nat
  carriedResidueTurnScaledAt18AfterCrank : Option Nat
  carriedResidueRadiansScaledAt18AfterCrank : Option Nat
  sameInstrumentReadingAfterCrank : Bool
deriving Repr

def cooperPairNeutrinoThreeCrankReport :
    CooperPairNeutrinoThreeCrankReport :=
  let cooperDepth :=
    (cooperPairNumberFromNat cooperPairNeutrinoSameCrankCount).corridorDepth
  let neutrinoDepth :=
    (neutrinoNumberFromNat cooperPairNeutrinoSameCrankCount).corridorDepth
  let depthsMatch := decide (cooperDepth = neutrinoDepth)
  let state? := cooperPairNeutrinoSameCrankState?
  { name := "cooper-pair-neutrino-three-crank"
    interpretation :=
      "crank the Cooper-pair/neutrino same-read three times and keep the equality as an instrument invariant"
    crankCount := cooperPairNeutrinoSameCrankCount
    sameInstrumentReadingBeforeCrank :=
      cooperPairNeutrinoSameReport.sameInstrumentReading
    cooperPairFact := factDecision Fact.COOPER_PAIR
    neutrinoFact := factDecision Fact.NEUTRINO
    cooperPairNumberDepthAfterCrank := cooperDepth
    neutrinoNumberDepthAfterCrank := neutrinoDepth
    depthsMatchAfterCrank := depthsMatch
    crankedState := state?
    selectedFaceAfterCrank := state?.map fun state => state.selectedFace
    carriedResidueNumeratorAfterCrank :=
      state?.map fun state => state.carriedResidueNumerator
    carriedResidueTurnScaledAt18AfterCrank :=
      state?.map fun state => state.carriedResidueTurnScaledAt18
    carriedResidueRadiansScaledAt18AfterCrank :=
      state?.map fun state => state.carriedResidueRadiansScaledAt18
    sameInstrumentReadingAfterCrank :=
      cooperPairNeutrinoSameReport.sameInstrumentReading &&
        depthsMatch && state?.isSome }

#eval cooperPairNeutrinoThreeCrankReport

end Measurement
