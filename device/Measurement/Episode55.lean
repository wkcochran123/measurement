import Measurement.Episode54

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000
set_option allowUnsafeReducibility true

namespace Measurement

/-
__EPISODE 55__: _The Generated Gauge Program_

Episode53 made the geometric side a program.  Episode54 built the compiler.
This episode names what comes out the other end: a generated QED-shaped
gauge program, with TWO channels that are never collapsed into one action --
the review that audited Episode52 was explicit about this, and the paper
lane filed it as a design rule.  The vacuum channel carries the C-squared
certificate; the excitation channel carries the residue.  One action cannot
do both jobs (where the residue is nonzero the certificates are refused,
Episode48), so the program carries both actions, each one a named compiler
output with its generation link recorded as a field.

The instance is the point.  Every field of
`generatedThreeRungQEDProgram` is either a compiler output or a theorem
already filed: the excitation action is
`threeRungBoundaryCompiler.compileAction threeRungGeometricProgram` (the
boundary read, which IS `discriminatingAction` by Episode54's `rfl`); the
vacuum action is the interior read (which IS the zero action by funext);
the certificate is Episode52's `hilberts_sixth_on_the_vacuum` transported
through the vacuum generation; the electron and positron readings are
Episode52's charges, verbatim, because the generation is definitional.

And then the sentence the paper has been building toward, as one theorem:

  `geometric_program_generates_qed_program` --

there exists a generated QED program over the three-rung geometric program
whose vacuum channel is C-squared-certified and whose excitation channel
produces the signed unit pair residue.  Write the geometric program, run
the compiler, and the gauge program -- certificates, electron, positron --
comes out.  GR-shaped data in, QED-shaped residue out, every arrow checked.

Stated formally:
* `GeneratedQEDProgram` -- two channels, generation links, certificate and
  residue obligations.
* `generatedThreeRungQEDProgram` -- the concrete instance; generation links
  by `rfl`.
* `geometric_program_generates_qed_program` -- the main near-term theorem
  of the paper lane.

Residue left (honest scope):
"QED-shaped" means exactly: a certified vacuum channel and a signed unit
pair residue on the excitation channel.  No photon, no coupling constant,
no renormalization, no Standard Model -- the claim gates hold the line at
the generated program.  The path and pair are still the compiler's fixed
choices; freeing them is mechanical.  The device-image reading of the two
charges needs the repaired Formalization stack (separate experiments per
orientation) and is the next file.
-/

/-- A generated QED-shaped gauge program over a geometric program `P`: two
channels (vacuum certificate, excitation residue), each action a recorded
compiler output, with the certificate and the two charge readings as
obligations. -/
structure GeneratedQEDProgram (P : GeometricProgram) where
  vacuumAction : FiniteGaugeAction0
  excitationAction : FiniteGaugeAction0
  path : CubicGaugePath0
  electronPair : CubicGaugeVariation0
  generated_by : BoundaryGaugeCompiler
  excitation_generated :
    excitationAction = generated_by.compileAction P
  vacuum_generated :
    vacuumAction = generated_by.compileVacuumAction P
  path_generated :
    path = generated_by.compilePath P
  pair_generated :
    electronPair = generated_by.compilePair P
  vacuumCertified : IsC2Certified vacuumAction path
  electronReads :
    CubicGaugeVariation.mixedCubicCoupling
      excitationAction path electronPair = -1
  positronReads :
    (CubicGaugePath.leftMiddleResidual excitationAction path
        (CubicGaugeVariation.leftVariation electronPair) +
      CubicGaugePath.rightMiddleResidual excitationAction path
        (CubicGaugeVariation.rightVariation electronPair)) -
      CubicGaugeVariation.coupledCubicDifference
        excitationAction path electronPair = 1

/-- The generated program over the three-rung geometric program.  Every
generation link is `rfl`; the certificate is Episode52's, transported
through the vacuum generation; the charges are Episode52's, verbatim,
because the excitation generation is definitional. -/
noncomputable def generatedThreeRungQEDProgram :
    GeneratedQEDProgram threeRungGeometricProgram where
  vacuumAction :=
    threeRungBoundaryCompiler.compileVacuumAction threeRungGeometricProgram
  excitationAction :=
    threeRungBoundaryCompiler.compileAction threeRungGeometricProgram
  path := flatPath
  electronPair := pairKick
  generated_by := threeRungBoundaryCompiler
  excitation_generated := rfl
  vacuum_generated := rfl
  path_generated := rfl
  pair_generated := rfl
  vacuumCertified := by
    show
      IsC2Certified
        (boundaryReadVacuumAction threeRungGeometricProgram) flatPath
    rw [threeRung_vacuum_compiles_to_zero_action]
    exact hilberts_sixth_on_the_vacuum
  electronReads := electron_charge
  positronReads := positron_charge

/-- THE MAIN NEAR-TERM THEOREM of the paper lane: the geometric program
generates a QED-shaped gauge program -- certified vacuum channel, signed
unit pair residue on the excitation channel -- and the generation is
PINNED: the program's compiler is the boundary-read compiler, and the
excitation action is the boundary read of the geometric program (both by
`rfl` at the witness).  Without those two conjuncts the existential would
be inhabitable by a constant compiler and carry no generation content;
with them, the theorem is sensitive to the geometric data.  GR-shaped data
in, QED-shaped residue out, every arrow checked. -/
theorem geometric_program_generates_qed_program :
    exists Q : GeneratedQEDProgram threeRungGeometricProgram,
      Q.generated_by = threeRungBoundaryCompiler /\
      Q.excitationAction = boundaryReadAction threeRungGeometricProgram /\
      IsC2Certified Q.vacuumAction Q.path /\
      CubicGaugeVariation.mixedCubicCoupling
        Q.excitationAction Q.path Q.electronPair = -1 :=
  ⟨generatedThreeRungQEDProgram,
    rfl,
    rfl,
    generatedThreeRungQEDProgram.vacuumCertified,
    generatedThreeRungQEDProgram.electronReads⟩

/-
The standing record.
-/

-- Expect `[propext, Classical.choice, Quot.sound]`: the generated program
-- references the geometric chair.  The charges themselves stayed axiom-free
-- back in Episode52; the chair is the price of the generation story.
#print axioms generatedThreeRungQEDProgram
#print axioms geometric_program_generates_qed_program

end Measurement
