import Measurement.Meanwhile78

/- MEANWHILE 79 -- FILL THE SKETCHBOOK INTO THE APPARATUS. The experiments
were earlier attempts to understand this step. Here we pull the useful probes
back into the `Measurement` chain:

  * the coarsest stress/strain mesh has exactly three readings;
  * the positron-admitting tilt is bracketed by the two straddling knots;
  * the symmetric receiver can miss an antisymmetric residue.

The experiments remain audits. The meanwhile carries the result forward as a
single finite report that the next apparatus layer can consume.
-/

namespace Measurement

inductive FiniteSketchTag where
  | origin
  | firstTilt
  | secondTilt
deriving DecidableEq, Repr

def FiniteSketchTag.stress : FiniteSketchTag -> Int
  | .origin => -1
  | .firstTilt => 1
  | .secondTilt => 0

structure FiniteSketchPath where
  strain : FiniteSketchTag
deriving DecidableEq, Repr

def finiteSketchCoarsePath : Nat -> FiniteSketchPath
  | 0 => { strain := .origin }
  | 1 => { strain := .firstTilt }
  | _ => { strain := .secondTilt }

def finiteSketchStress (s : Nat) : Int :=
  (finiteSketchCoarsePath s).strain.stress

theorem finiteSketchStress_origin : finiteSketchStress 0 = -1 := by decide
theorem finiteSketchStress_one : finiteSketchStress 1 = 1 := by decide
theorem finiteSketchStress_two : finiteSketchStress 2 = 0 := by decide

def finiteSketchBeforeStress : Int :=
  finiteSketchStress 0

def finiteSketchAfterStress : Int :=
  finiteSketchStress 1

theorem finiteSketchBeforeStress_is_electron :
    finiteSketchBeforeStress = -1 := by decide

theorem finiteSketchAfterStress_is_positron :
    finiteSketchAfterStress = 1 := by decide

def finiteSketchKnotCrossing (s0 d0 s1 d1 : Int) : Int × Int :=
  (s0 * (d1 - d0) + (-d0) * (s1 - s0), d1 - d0)

def finiteSketchKnotThreshold : Int × Int :=
  finiteSketchKnotCrossing 0 finiteSketchBeforeStress 1 finiteSketchAfterStress

theorem finiteSketchKnotThreshold_is_half :
    finiteSketchKnotThreshold = (1, 2) := by decide

def finiteSketchAntimatterCount (stressReadings : List Int) : Nat :=
  (stressReadings.filter (fun stress => decide (0 < stress))).length

def finiteSketchFlatStressReadings : List Int :=
  [finiteSketchBeforeStress]

def finiteSketchTiltedStressReadings : List Int :=
  [finiteSketchAfterStress]

structure FiniteSketchMeshReport where
  name : String
  interpretation : String
  stressAtOrigin : Int
  stressAtOne : Int
  stressAtTwo : Int
  beforeStress : Int
  afterStress : Int
  flatAntimatterCount : Nat
  tiltedAntimatterCount : Nat
  thresholdBracketLower : Int
  thresholdBracketUpper : Int
  knotThreshold : Int × Int
  knotThresholdIsHalf : Bool
  devicePinnedAtCoarsestMesh : Bool
  ownsContinuumLimit : Bool
deriving Repr

def finiteSketchMeshReport : FiniteSketchMeshReport :=
  { name := "finite-sketch-mesh"
    interpretation :=
      "the experiment sketchbook supplies the three coarse stress readings and the straddling-knot positron threshold"
    stressAtOrigin := finiteSketchStress 0
    stressAtOne := finiteSketchStress 1
    stressAtTwo := finiteSketchStress 2
    beforeStress := finiteSketchBeforeStress
    afterStress := finiteSketchAfterStress
    flatAntimatterCount :=
      finiteSketchAntimatterCount finiteSketchFlatStressReadings
    tiltedAntimatterCount :=
      finiteSketchAntimatterCount finiteSketchTiltedStressReadings
    thresholdBracketLower := 0
    thresholdBracketUpper := 1
    knotThreshold := finiteSketchKnotThreshold
    knotThresholdIsHalf := decide (finiteSketchKnotThreshold = (1, 2))
    devicePinnedAtCoarsestMesh :=
      decide
        (finiteSketchStress 0 = -1 ∧
          finiteSketchStress 1 = 1 ∧
          finiteSketchStress 2 = 0)
    ownsContinuumLimit := false }

structure FiniteProjectionUpdate where
  slot0 : Int
  slot1 : Int
deriving DecidableEq, Repr

def FiniteProjectionUpdate.twist (u : FiniteProjectionUpdate) : Int :=
  u.slot0 - u.slot1

def FiniteProjectionUpdate.symContent (u : FiniteProjectionUpdate) : Int :=
  u.slot0 + u.slot1

def FiniteProjectionUpdate.flip (u : FiniteProjectionUpdate) :
    FiniteProjectionUpdate :=
  { slot0 := u.slot1, slot1 := u.slot0 }

def finiteProjectionSameMessage
    (u v : FiniteProjectionUpdate) : Bool :=
  decide (u.symContent = v.symContent)

def finiteProjectionPureSymmetric : FiniteProjectionUpdate :=
  { slot0 := 3, slot1 := 3 }

def finiteProjectionPureTwist : FiniteProjectionUpdate :=
  { slot0 := 5, slot1 := -5 }

def finiteProjectionSilent : FiniteProjectionUpdate :=
  { slot0 := 0, slot1 := 0 }

def finiteProjectionTwistIsUnrecordable : Bool :=
  finiteProjectionSameMessage finiteProjectionPureTwist finiteProjectionSilent

def finiteProjectionTwistResidue : Int :=
  finiteProjectionPureTwist.twist

def finiteProjectionTwistResidueNonzero : Bool :=
  decide (finiteProjectionTwistResidue ≠ 0)

def finiteProjectionSymmetricDifferentFromSilent : Bool :=
  decide
    (finiteProjectionPureSymmetric.symContent ≠
      finiteProjectionSilent.symContent)

def finiteProjectionFlipKeepsProjection : Bool :=
  finiteProjectionSameMessage
    finiteProjectionPureTwist finiteProjectionPureTwist.flip

def finiteProjectionFlipNegatesTwistOnPureTwist : Bool :=
  decide
    (finiteProjectionPureTwist.flip.twist =
      -finiteProjectionPureTwist.twist)

structure FiniteProjectionResidueReport where
  name : String
  interpretation : String
  pureTwist : FiniteProjectionUpdate
  silent : FiniteProjectionUpdate
  pureSymmetric : FiniteProjectionUpdate
  twistSameAsSilent : Bool
  twistResidue : Int
  twistResidueNonzero : Bool
  symmetricDifferentFromSilent : Bool
  flipKeepsProjection : Bool
  flipNegatesTwist : Bool
deriving Repr

def finiteProjectionResidueReport : FiniteProjectionResidueReport :=
  { name := "finite-projection-residue"
    interpretation :=
      "a symmetric readout carries the sum and leaves the antisymmetric twist as hidden residue"
    pureTwist := finiteProjectionPureTwist
    silent := finiteProjectionSilent
    pureSymmetric := finiteProjectionPureSymmetric
    twistSameAsSilent := finiteProjectionTwistIsUnrecordable
    twistResidue := finiteProjectionTwistResidue
    twistResidueNonzero := finiteProjectionTwistResidueNonzero
    symmetricDifferentFromSilent :=
      finiteProjectionSymmetricDifferentFromSilent
    flipKeepsProjection := finiteProjectionFlipKeepsProjection
    flipNegatesTwist := finiteProjectionFlipNegatesTwistOnPureTwist }

structure FiniteExperimentSketchbookMeanwhileReport where
  name : String
  interpretation : String
  mesh : FiniteSketchMeshReport
  projection : FiniteProjectionResidueReport
  spinorAntimatterKnob : FiniteSpinorAntimatterKnobReport
  bracketSelectsAntimatterSide : Bool
  hiddenResidueCanDriveKnob : Bool
  continuumRemainsExternal : Bool
  filledMeanwhileCloses : Bool
deriving Repr

def finiteExperimentSketchbookMeanwhileReport :
    FiniteExperimentSketchbookMeanwhileReport :=
  { name := "finite-experiment-sketchbook-meanwhile"
    interpretation :=
      "the older experiment probes are now readings in the apparatus: coarse mesh, threshold bracket, projection residue, and the spinor antimatter knob"
    mesh := finiteSketchMeshReport
    projection := finiteProjectionResidueReport
    spinorAntimatterKnob := finiteSpinorAntimatterKnobReport
    bracketSelectsAntimatterSide :=
      decide (finiteSketchAfterStress = 1) &&
        finiteSpinorAntimatterKnobReport.knobPlugCloses
    hiddenResidueCanDriveKnob :=
      finiteProjectionTwistIsUnrecordable &&
        finiteProjectionTwistResidueNonzero
    continuumRemainsExternal :=
      decide (finiteSketchMeshReport.ownsContinuumLimit = false)
    filledMeanwhileCloses :=
      finiteSketchMeshReport.knotThresholdIsHalf &&
        finiteProjectionResidueReport.twistSameAsSilent &&
        finiteProjectionResidueReport.twistResidueNonzero &&
        finiteProjectionResidueReport.symmetricDifferentFromSilent &&
        finiteSpinorAntimatterKnobReport.knobPlugCloses &&
        decide (finiteSketchMeshReport.ownsContinuumLimit = false) }

#eval finiteExperimentSketchbookMeanwhileReport

end Measurement
