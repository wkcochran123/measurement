import Measurement.Episode66

namespace Measurement

/-!
Episode 67 names the continuum certificate families that will live inside a
`SobolevHilbertDoor`.

The concrete three-rung certificates use the door zero as their vector.  This
keeps the first interface conservative: the finite witnesses carry the actual
generation content, while later episodes can replace the zero vector with a
nontrivial dense embedding.
-/

structure GeometricSobolevCertificate (D : SobolevHilbertDoor) where
  vector : D.H
  finiteWitness : GeometricProgram

structure GaugeSobolevCertificate (D : SobolevHilbertDoor) where
  vector : D.H
  finiteWitness : GeneratedQEDProgram threeRungGeometricProgram

def BoundaryGenerated
    {D : SobolevHilbertDoor}
    (G : GeometricSobolevCertificate D)
    (Q : GaugeSobolevCertificate D) : Prop :=
  G.finiteWitness = threeRungGeometricProgram ∧
    Q.finiteWitness.generated_by = threeRungBoundaryCompiler

noncomputable def threeRungGeometricSobolevCertificate :
    GeometricSobolevCertificate threeRungSobolevHilbertDoor where
  vector := threeRungSobolevHilbertDoor.zero
  finiteWitness := threeRungGeometricProgram

noncomputable def threeRungGaugeSobolevCertificate :
    GaugeSobolevCertificate threeRungSobolevHilbertDoor where
  vector := threeRungSobolevHilbertDoor.zero
  finiteWitness := generatedThreeRungQEDProgram

theorem threeRung_boundaryGenerated :
    BoundaryGenerated
      threeRungGeometricSobolevCertificate
      threeRungGaugeSobolevCertificate := by
  exact ⟨rfl, rfl⟩

structure ContinuumCertificatePair (D : SobolevHilbertDoor) where
  geometric : GeometricSobolevCertificate D
  gauge : GaugeSobolevCertificate D
  generated : BoundaryGenerated geometric gauge

noncomputable def threeRungContinuumCertificatePair :
    ContinuumCertificatePair threeRungSobolevHilbertDoor where
  geometric := threeRungGeometricSobolevCertificate
  gauge := threeRungGaugeSobolevCertificate
  generated := threeRung_boundaryGenerated

#print axioms threeRungGeometricSobolevCertificate
#print axioms threeRungGaugeSobolevCertificate
#print axioms threeRung_boundaryGenerated
#print axioms threeRungContinuumCertificatePair

end Measurement
