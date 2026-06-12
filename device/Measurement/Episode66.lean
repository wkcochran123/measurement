import Measurement.Episode65

namespace Measurement

/-!
Episode 66 turns Episode65's finite skeleton into the named pre-Hilbert
completion skeleton.

This is still an interface layer.  "Dense" and "completion" are tokens carried
by the door, while the countability content is concrete: every finite spline
condition has a natural code from Episode63.
-/

structure SeparablePreHilbertSkeleton
    (epsilon : Nat) (D : SobolevHilbertDoor) where
  finite : FiniteCohenPreHilbertSkeleton epsilon D
  conditionCode : SplineCondition epsilon -> Nat
  conditionCode_matches :
    forall condition,
      conditionCode condition = finite.enumeration.code condition
  every_condition_coded :
    forall condition,
      exists code : Nat, conditionCode condition = code
  dense : Prop
  dense_proof : dense

def separablePreHilbertSkeletonOfFinite
    {epsilon : Nat} {D : SobolevHilbertDoor}
    (finite : FiniteCohenPreHilbertSkeleton epsilon D) :
    SeparablePreHilbertSkeleton epsilon D where
  finite := finite
  conditionCode := finite.enumeration.code
  conditionCode_matches := by
    intro _condition
    rfl
  every_condition_coded := by
    intro condition
    exact finite.every_condition_coded condition
  dense := True
  dense_proof := trivial

theorem separableSkeleton_condition_coded
    {epsilon : Nat} {D : SobolevHilbertDoor}
    (skeleton : SeparablePreHilbertSkeleton epsilon D)
    (condition : SplineCondition epsilon) :
    exists code : Nat, skeleton.conditionCode condition = code :=
  skeleton.every_condition_coded condition

structure CompletionMappedResidual (arc : HilbertCompletionArc) where
  separableSkeleton :
    SeparablePreHilbertSkeleton arc.epsilon arc.door
  completionToken : arc.door.complete
  finiteResidue :
    GaugeFrechetLinearTermCloses generatedThreeRungQEDProgram /\
      QEDResidueIsMixedPairTerm generatedThreeRungQEDProgram

def hilbertCompletionArc_separableSkeleton
    (arc : HilbertCompletionArc) :
    SeparablePreHilbertSkeleton arc.epsilon arc.door :=
  separablePreHilbertSkeletonOfFinite arc.skeleton

def finiteResidualMapsIntoCompletion
    (arc : HilbertCompletionArc) :
    CompletionMappedResidual arc where
  separableSkeleton := hilbertCompletionArc_separableSkeleton arc
  completionToken := arc.door.complete_proof
  finiteResidue := arc.finiteResidue

theorem finiteResidualMapsIntoCompletion_retains_residue
    (arc : HilbertCompletionArc) :
    (finiteResidualMapsIntoCompletion arc).finiteResidue =
      arc.finiteResidue := by
  rfl

theorem threeRung_completion_maps_finite_residue
    (epsilon : Nat) :
    GaugeFrechetLinearTermCloses generatedThreeRungQEDProgram /\
      QEDResidueIsMixedPairTerm generatedThreeRungQEDProgram := by
  exact
    (finiteResidualMapsIntoCompletion
      (threeRungHilbertCompletionArc epsilon)).finiteResidue

#print axioms separablePreHilbertSkeletonOfFinite
#print axioms separableSkeleton_condition_coded
#print axioms finiteResidualMapsIntoCompletion
#print axioms finiteResidualMapsIntoCompletion_retains_residue
#print axioms threeRung_completion_maps_finite_residue

end Measurement
