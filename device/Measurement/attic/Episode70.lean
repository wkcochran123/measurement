import Measurement.Episode69

namespace Measurement

/-!
Episode 70 installs the continuum-facing boundary trace interface.

The concrete trace still reads the finite generated boundary residue from
Episode57.  The point is to name the continuum functional shape now:
boundary flux equals terminal residual on the generated dense representative.
-/

structure BoundaryTraceFunctional (D : SobolevHilbertDoor) where
  boundaryFlux : GaugeSobolevCertificate D -> Int
  terminalResidual : GaugeSobolevCertificate D -> Int
  agreesOnGenerated :
    forall Q : GaugeSobolevCertificate D,
      Q.finiteWitness = generatedThreeRungQEDProgram ->
        boundaryFlux Q = terminalResidual Q

def BoundaryTraceCompatible
    {D : SobolevHilbertDoor}
    (trace : BoundaryTraceFunctional D)
    (Q : GaugeSobolevCertificate D) : Prop :=
  trace.boundaryFlux Q = trace.terminalResidual Q

noncomputable def generatedBoundaryTraceFunctional :
    BoundaryTraceFunctional threeRungSobolevHilbertDoor where
  boundaryFlux := fun _ =>
    (generatedBoundaryResidue generatedThreeRungQEDProgram).boundaryFlux
  terminalResidual := fun _ =>
    (generatedBoundaryResidue generatedThreeRungQEDProgram).terminalResidual
  agreesOnGenerated := by
    intro _Q _hGenerated
    exact generated_boundary_flux_eq_terminal_residual

theorem generatedBoundaryTrace_compatible :
    BoundaryTraceCompatible
      generatedBoundaryTraceFunctional
      threeRungGaugeSobolevCertificate := by
  unfold BoundaryTraceCompatible
  exact
    generatedBoundaryTraceFunctional.agreesOnGenerated
      threeRungGaugeSobolevCertificate
      rfl

theorem boundaryTrace_agrees_with_terminal_residual
    {D : SobolevHilbertDoor}
    (trace : BoundaryTraceFunctional D)
    (Q : GaugeSobolevCertificate D)
    (hGenerated : Q.finiteWitness = generatedThreeRungQEDProgram) :
    BoundaryTraceCompatible trace Q := by
  exact trace.agreesOnGenerated Q hGenerated

#print axioms generatedBoundaryTraceFunctional
#print axioms generatedBoundaryTrace_compatible
#print axioms boundaryTrace_agrees_with_terminal_residual

end Measurement
