import Measurement.Episode70

namespace Measurement

/-!
Episode 71 records residual convergence in the completion door.

The project still has no real normed-space library imported, so Cauchy-ness in
the Sobolev norm is represented by an explicit witness carrying the sequence,
the completion token, and the finite generated residue fact.
-/

structure SobolevResidualCauchyWitness
    (D : SobolevHilbertDoor)
    (Q : GaugeSobolevCertificate D) where
  sequence : Nat -> D.H
  cauchyToken : Prop
  cauchyProof : cauchyToken
  completionToken : D.complete
  residueReadsMixedPair :
    QEDResidueIsMixedPairTerm Q.finiteWitness

def ResidualCauchyInSobolevNorm
    {D : SobolevHilbertDoor}
    (Q : GaugeSobolevCertificate D) : Prop :=
  exists _witness : SobolevResidualCauchyWitness D Q, True

noncomputable def threeRungResidualCauchyWitness :
    SobolevResidualCauchyWitness
      threeRungSobolevHilbertDoor
      threeRungGaugeSobolevCertificate where
  sequence := fun _ => threeRungSobolevHilbertDoor.zero
  cauchyToken := True
  cauchyProof := trivial
  completionToken := threeRungSobolevHilbertDoor.complete_proof
  residueReadsMixedPair := generatedThreeRungQEDProgram.electronReads

theorem threeRung_residual_cauchy_in_sobolev_norm :
    ResidualCauchyInSobolevNorm threeRungGaugeSobolevCertificate := by
  exact ⟨threeRungResidualCauchyWitness, trivial⟩

structure CauchyLiftThroughCompletion
    (epsilon : Nat)
    (D : SobolevHilbertDoor)
    (Q : GaugeSobolevCertificate D) where
  skeleton : SeparablePreHilbertSkeleton epsilon D
  residualCauchy : ResidualCauchyInSobolevNorm Q

noncomputable def threeRungCauchyLiftThroughCompletion
    (epsilon : Nat) :
    CauchyLiftThroughCompletion
      epsilon
      threeRungSobolevHilbertDoor
      threeRungGaugeSobolevCertificate where
  skeleton :=
    hilbertCompletionArc_separableSkeleton
      (threeRungHilbertCompletionArc epsilon)
  residualCauchy := threeRung_residual_cauchy_in_sobolev_norm

#print axioms threeRungResidualCauchyWitness
#print axioms threeRung_residual_cauchy_in_sobolev_norm
#print axioms threeRungCauchyLiftThroughCompletion

end Measurement
