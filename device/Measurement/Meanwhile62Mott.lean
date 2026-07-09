import Measurement.Meanwhile62SternGerlach

/- MEANWHILE 62.2 -- MOTT CLOUD-CHAMBER TRACK. Mott's paradox is the cloud
chamber version of the same approximation story: an alpha particle leaves the
source as a spherical de Broglie wave, but the gas cloud records a straight
track.

The apparatus resolves this by carrying the first ionization as the selected
ray. After that first hit, later ionizations are admitted only when they are
correlated with the same ray and farther from the source. The spherical wave is
not erased; it is the pre-interaction candidate set. The observed straight line
is the correlated post-interaction record.
-/

namespace Measurement

inductive MottGasRay where
  | east
  | north
  | diagonal
deriving Repr, DecidableEq

structure MottGasAtom where
  ray : MottGasRay
  shell : Nat
  densityScaledAt18 : Nat
deriving Repr, DecidableEq

def mottGasCloudDensityScaledAt18 : Nat :=
  sternGerlachMagneticGradientScaledAt18

def mottGasCloud : List MottGasAtom :=
  [ { ray := .east, shell := 1,
      densityScaledAt18 := mottGasCloudDensityScaledAt18 },
    { ray := .north, shell := 1,
      densityScaledAt18 := mottGasCloudDensityScaledAt18 },
    { ray := .diagonal, shell := 1,
      densityScaledAt18 := mottGasCloudDensityScaledAt18 },
    { ray := .east, shell := 2,
      densityScaledAt18 := mottGasCloudDensityScaledAt18 },
    { ray := .north, shell := 2,
      densityScaledAt18 := mottGasCloudDensityScaledAt18 },
    { ray := .diagonal, shell := 2,
      densityScaledAt18 := mottGasCloudDensityScaledAt18 },
    { ray := .east, shell := 3,
      densityScaledAt18 := mottGasCloudDensityScaledAt18 },
    { ray := .north, shell := 3,
      densityScaledAt18 := mottGasCloudDensityScaledAt18 },
    { ray := .diagonal, shell := 3,
      densityScaledAt18 := mottGasCloudDensityScaledAt18 } ]

def mottAlphaParticleMomentumScaledAt18 : Nat :=
  qftPhotonDeBroglieMomentumScaledAt18

def mottAlphaParticleWavelengthScaledAt18 : Nat :=
  qftPhotonDeBroglieWavelengthScaledAt18

def mottAlphaParticleWaveProductScaledAt18 : Nat :=
  qftPhotonDeBroglieProductScaledAt18

def mottAlphaParticleWaveResidualScaledAt18 : Nat :=
  qftPhotonDeBroglieResidualScaledAt18

def mottAlphaParticleSphericalWaveAvailable : Bool :=
  qftPhotonDeBroglieReport.productClosesOneQuantum &&
    qftPhotonDeBroglieReport.phaseKickAvailable

def mottFirstIonization : MottGasAtom :=
  { ray := .east, shell := 1,
    densityScaledAt18 := mottGasCloudDensityScaledAt18 }

def mottSecondIonization : MottGasAtom :=
  { ray := .east, shell := 2,
    densityScaledAt18 := mottGasCloudDensityScaledAt18 }

def mottThirdIonization : MottGasAtom :=
  { ray := .east, shell := 3,
    densityScaledAt18 := mottGasCloudDensityScaledAt18 }

def mottTrackAtoms : List MottGasAtom :=
  [mottFirstIonization, mottSecondIonization, mottThirdIonization]

def mottSameRay (first later : MottGasAtom) : Bool :=
  decide (first.ray = later.ray)

def mottFartherFromSource (first later : MottGasAtom) : Bool :=
  decide (first.shell < later.shell)

def mottAdmitsLaterIonization
    (first later : MottGasAtom) : Bool :=
  mottSameRay first later && mottFartherFromSource first later

def mottAtomOnTrack (atom : MottGasAtom) : Bool :=
  decide (atom.ray = mottFirstIonization.ray)

def mottTrackIonizationStrengthScaledAt18 (atom : MottGasAtom) : Nat :=
  mottAlphaParticleMomentumScaledAt18 / atom.shell.succ

def mottCloudCandidateCount : Nat :=
  mottGasCloud.length

def mottTrackIonizationCount : Nat :=
  mottTrackAtoms.length

def mottOffTrackSuppressedCount : Nat :=
  mottCloudCandidateCount - mottTrackIonizationCount

def mottTrackAtomsOnSelectedRay : Bool :=
  mottTrackAtoms.all mottAtomOnTrack

def mottTrackShellsIncrease : Bool :=
  mottAdmitsLaterIonization mottFirstIonization mottSecondIonization &&
    mottAdmitsLaterIonization mottSecondIonization mottThirdIonization

def mottOffRayExampleSuppressed : Bool :=
  !mottAdmitsLaterIonization mottFirstIonization
    { ray := .north, shell := 2,
      densityScaledAt18 := mottGasCloudDensityScaledAt18 }

structure MottIonizationRead where
  atom : MottGasAtom
  selectedTrackAtom : Bool
  ionizationStrengthScaledAt18 : Nat
  admittedAfterFirstHit : Bool
deriving Repr

def mottIonizationRead (atom : MottGasAtom) : MottIonizationRead :=
  { atom := atom
    selectedTrackAtom := mottAtomOnTrack atom
    ionizationStrengthScaledAt18 :=
      mottTrackIonizationStrengthScaledAt18 atom
    admittedAfterFirstHit :=
      if atom = mottFirstIonization then
        true
      else
        mottAdmitsLaterIonization mottFirstIonization atom }

def mottTrackReads : List MottIonizationRead :=
  mottTrackAtoms.map mottIonizationRead

def mottStraightTrackSelected : Bool :=
  mottAlphaParticleSphericalWaveAvailable &&
    mottTrackAtomsOnSelectedRay &&
    mottTrackShellsIncrease &&
    mottOffRayExampleSuppressed

def mottParadoxResolvedByCorrelations : Bool :=
  mottAlphaParticleSphericalWaveAvailable &&
    mottStraightTrackSelected &&
    decide (0 < mottOffTrackSuppressedCount)

structure MottCloudChamberReport where
  name : String
  interpretation : String
  afterDeBroglie : Bool
  alphaParticleMomentumScaledAt18 : Nat
  alphaParticleWavelengthScaledAt18 : Nat
  alphaParticleWaveProductScaledAt18 : Nat
  alphaParticleWaveResidualScaledAt18 : Nat
  sphericalWaveBeforeIonization : Bool
  gasCloudCandidateCount : Nat
  selectedRay : MottGasRay
  firstIonization : MottGasAtom
  trackReads : List MottIonizationRead
  trackIonizationCount : Nat
  offTrackSuppressedCount : Nat
  trackAtomsOnSelectedRay : Bool
  trackShellsIncrease : Bool
  offRayExampleSuppressed : Bool
  straightTrackSelected : Bool
  paradoxResolvedByCorrelations : Bool
deriving Repr

def mottCloudChamberReport : MottCloudChamberReport :=
  { name := "mott-cloud-chamber-alpha-track"
    interpretation :=
      "a spherical de Broglie alpha wave supplies the gas-cloud candidates, but the first ionization selects one ray and later correlations form a straight track"
    afterDeBroglie := qftPhotonDeBroglieReport.phaseKickAvailable
    alphaParticleMomentumScaledAt18 :=
      mottAlphaParticleMomentumScaledAt18
    alphaParticleWavelengthScaledAt18 :=
      mottAlphaParticleWavelengthScaledAt18
    alphaParticleWaveProductScaledAt18 :=
      mottAlphaParticleWaveProductScaledAt18
    alphaParticleWaveResidualScaledAt18 :=
      mottAlphaParticleWaveResidualScaledAt18
    sphericalWaveBeforeIonization :=
      mottAlphaParticleSphericalWaveAvailable
    gasCloudCandidateCount := mottCloudCandidateCount
    selectedRay := mottFirstIonization.ray
    firstIonization := mottFirstIonization
    trackReads := mottTrackReads
    trackIonizationCount := mottTrackIonizationCount
    offTrackSuppressedCount := mottOffTrackSuppressedCount
    trackAtomsOnSelectedRay := mottTrackAtomsOnSelectedRay
    trackShellsIncrease := mottTrackShellsIncrease
    offRayExampleSuppressed := mottOffRayExampleSuppressed
    straightTrackSelected := mottStraightTrackSelected
    paradoxResolvedByCorrelations :=
      mottParadoxResolvedByCorrelations }

#eval mottCloudChamberReport

end Measurement
