import Measurement.Meanwhile59

/- MEANWHILE 60 -- PUT A CHARGE HORIZON ON THE COOPER PAIR. The Cooper pair is
now read only through its charge surface. Its interior pairing channel is
deliberately hidden: ordinary Cooper-pair interior and neutrino/exclusion
interior collapse when they cast the same charge read.

Gravity is not part of the horizon. The electron tugs on the "doesn't matter"
Cooper pair outside the quotient, and that tug is recorded as a separate device
read. The horizon can hide charge; the tug can still be measured.
-/

namespace Measurement

inductive CooperPairInteriorKind where
  | spinBalancedPair
  | neutrinoExclusionPair
deriving Repr, DecidableEq

structure CooperPairSurfaceRead where
  chargeSurfaceRead : Nat
  alphaScaledAt18 : Nat
  inverseAlphaScaledAt18? : Option Nat
deriving Repr, DecidableEq

structure ElectronCooperPairTugRead where
  electronChargeRead : Nat
  cooperPairMatterRead : Nat
  gravityTugResidueScaledAt18 : Nat
  proximityBreaks : Bool
  approachHeartbeat : Nat
  timelikeCertificate : Bool
  affectsChargeHorizon : Bool
deriving Repr, DecidableEq

structure CooperPairInterior where
  kind : CooperPairInteriorKind
  pairingWitness : Nat
  spinWitness : Nat
  exclusionWitness : Nat
  surface : CooperPairSurfaceRead
deriving Repr

def currentChargeOnlyAlphaScaledAt18 : Nat :=
  match defaultAlphaMeasurementReport? with
  | some report => report.measuredAlphaScaledAt18
  | none => 0

def currentReaderSeededAlphaScaledAt18 : Nat :=
  match defaultSeededElectronAlphaMeasurementReport? with
  | some report => report.seededAlphaScaledAt18
  | none => currentChargeOnlyAlphaScaledAt18

def currentReaderSeededInverseAlphaScaledAt18? : Option Nat :=
  match defaultSeededElectronAlphaMeasurementReport? with
  | some report => report.seededInverseAlphaScaledAt18?
  | none => alphaInverseReadScaledAt18? currentChargeOnlyAlphaScaledAt18

def cooperPairDoesNotMatterRead : Nat :=
  0

def electronCooperPairTugRead : ElectronCooperPairTugRead :=
  { electronChargeRead := currentReaderSeededAlphaScaledAt18
    cooperPairMatterRead := cooperPairDoesNotMatterRead
    gravityTugResidueScaledAt18 :=
      eventHorizonStudyExecutionReport.finalHeartbeat
    proximityBreaks := (proximityRead eventHorizonRadius).pairBreaks
    approachHeartbeat :=
      eventHorizonStudyExecutionReport.finalHeartbeat
    timelikeCertificate :=
      eventHorizonStudyExecutionReport.certifiedTimelike
    affectsChargeHorizon := false }

def cooperPairHorizonSurfaceRead : CooperPairSurfaceRead :=
  { chargeSurfaceRead := currentReaderSeededAlphaScaledAt18
    alphaScaledAt18 := currentReaderSeededAlphaScaledAt18
    inverseAlphaScaledAt18? := currentReaderSeededInverseAlphaScaledAt18? }

def cooperPairHorizonInterior : CooperPairInterior :=
  { kind := .spinBalancedPair
    pairingWitness := cooperPairNeutrinoSameCrankCount
    spinWitness := cooperPairNeutrinoThreeCrankReport.carriedResidueNumeratorAfterCrank.getD 0
    exclusionWitness := 0
    surface := cooperPairHorizonSurfaceRead }

def neutrinoHorizonInterior : CooperPairInterior :=
  { kind := .neutrinoExclusionPair
    pairingWitness := 0
    spinWitness := 0
    exclusionWitness := cooperPairNeutrinoThreeCrankReport.carriedResidueNumeratorAfterCrank.getD 0
    surface := cooperPairHorizonSurfaceRead }

def CooperPairInteriorSameSurface
    (left right : CooperPairInterior) : Prop :=
  left.surface = right.surface

def CooperPairHorizon : Type :=
  Quot CooperPairInteriorSameSurface

def cooperPairHorizonMk (interior : CooperPairInterior) :
    CooperPairHorizon :=
  Quot.mk CooperPairInteriorSameSurface interior

def cooperPairHorizonSurface : CooperPairHorizon -> CooperPairSurfaceRead :=
  Quot.lift (fun interior : CooperPairInterior => interior.surface)
    (fun _ _ sameSurface => sameSurface)

theorem cooperPair_neutrino_horizon_same :
    cooperPairHorizonMk cooperPairHorizonInterior =
      cooperPairHorizonMk neutrinoHorizonInterior :=
  selection_sound (r := CooperPairInteriorSameSurface) rfl

namespace Fact

def NEUTRINO_HORIZON_SAME : Fact :=
  { truth :=
      cooperPairHorizonMk cooperPairHorizonInterior =
        cooperPairHorizonMk neutrinoHorizonInterior
    decTruth := isTrue cooperPair_neutrino_horizon_same }

end Fact

def cooperPairHorizonSurfaceFromPair : CooperPairSurfaceRead :=
  cooperPairHorizonSurface (cooperPairHorizonMk cooperPairHorizonInterior)

def cooperPairHorizonSurfaceFromNeutrino : CooperPairSurfaceRead :=
  cooperPairHorizonSurface (cooperPairHorizonMk neutrinoHorizonInterior)

structure CooperPairHorizonReport where
  name : String
  interpretation : String
  canInspectInterior : Bool
  horizonContainsChargeOnly : Bool
  horizonContainsGravity : Bool
  interiorKindsDiffer : Bool
  exteriorSurfacesSame : Bool
  lastNeutrinoSameFact : Bool
  cooperPairFact : Bool
  neutrinoFact : Bool
  horizonSurface : CooperPairSurfaceRead
  electronTugRead : ElectronCooperPairTugRead
  readerSeed : Nat
  chargeOnlyAlphaScaledAt18 : Nat
  horizonAlphaScaledAt18 : Nat
  horizonInverseAlphaScaledAt18? : Option Nat
  horizonAlphaDiffersFromChargeOnly : Bool
  electronTugHeartbeat : Nat
  electronTugTimelikeCertificate : Bool
deriving Repr

def cooperPairHorizonReport : CooperPairHorizonReport :=
  let surface := cooperPairHorizonSurfaceFromNeutrino
  let tugRead := electronCooperPairTugRead
  { name := "cooper-pair-horizon"
    interpretation :=
      "ordinary Cooper-pair interior and neutrino exclusion interior collapse to the same opaque charge surface while gravity remains an external tug"
    canInspectInterior := false
    horizonContainsChargeOnly := true
    horizonContainsGravity := false
    interiorKindsDiffer :=
      decide (cooperPairHorizonInterior.kind ≠ neutrinoHorizonInterior.kind)
    exteriorSurfacesSame :=
      decide (cooperPairHorizonSurfaceFromPair =
        cooperPairHorizonSurfaceFromNeutrino)
    lastNeutrinoSameFact := factDecision Fact.NEUTRINO_HORIZON_SAME
    cooperPairFact := factDecision Fact.COOPER_PAIR
    neutrinoFact := factDecision Fact.NEUTRINO
    horizonSurface := surface
    electronTugRead := tugRead
    readerSeed := readerProvidedSeed
    chargeOnlyAlphaScaledAt18 := currentChargeOnlyAlphaScaledAt18
    horizonAlphaScaledAt18 := surface.alphaScaledAt18
    horizonInverseAlphaScaledAt18? := surface.inverseAlphaScaledAt18?
    horizonAlphaDiffersFromChargeOnly :=
      decide (surface.alphaScaledAt18 ≠ currentChargeOnlyAlphaScaledAt18)
    electronTugHeartbeat := tugRead.approachHeartbeat
    electronTugTimelikeCertificate := tugRead.timelikeCertificate }

#eval cooperPairHorizonReport

end Measurement
