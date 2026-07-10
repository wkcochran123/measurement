import Measurement.Episode63

namespace Measurement

/-!
Episode 64 closes the finite arc.

The spline side is now packaged as finite Cohen compliance up to epsilon:
the finite ledger, the extensional condition order, and the natural coding
surface all sit in one certificate.  The gauge side records the generated
QED residue as the mixed pair term left after the Frechet-linear/vacuum
certificate has closed.
-/

structure FiniteCohenCompliantEpsilon (epsilon : Nat) where
  finiteLedger : FiniteCohenUpToEpsilon epsilon
  extensionalOrder : ExtensionalConditionOrder epsilon
  countableLedger : NatEnumerable (SplineCondition epsilon)

def splineCondition_finiteCohenCompliant (epsilon : Nat) :
    FiniteCohenCompliantEpsilon epsilon where
  finiteLedger := splineCondition_cohen_up_to_epsilon epsilon
  extensionalOrder := splineCondition_extensional_order epsilon
  countableLedger := splineCondition_conditions_countable epsilon

theorem lanczosSpline_cohen_compliant
    (epsilon : Nat) {action : FiniteGaugeAction} {path : FiniteGaugePath}
    (certificate : LanczosCubicSpline action path) :
    (exists _ledger : FiniteCohenCompliantEpsilon epsilon, True) /\
      splineSufficient action path := by
  exact ⟨⟨splineCondition_finiteCohenCompliant epsilon, trivial⟩,
    law_of_spline_sufficiency certificate⟩

theorem finiteCohen_boundary_radiation_closeout (epsilon : Nat) :
    (exists _ledger : FiniteCohenCompliantEpsilon epsilon, True) /\
      (threeRungCertificateSplit.dotH
          threeRungCertificateSplit.geometric
          threeRungCertificateSplit.gauge = 0 ∧
        ¬ HasInteriorScalarMixedCertificate
            (cliffordOfSplit threeRungCertificateSplit)
            threeRungCertificateSplit.geometric
            threeRungCertificateSplit.gauge ∧
          (generatedBoundaryResidue generatedThreeRungQEDProgram).boundaryFlux =
            (generatedBoundaryResidue generatedThreeRungQEDProgram).terminalResidual) := by
  exact ⟨⟨splineCondition_finiteCohenCompliant epsilon, trivial⟩,
    boundary_radiation_finite⟩

def GaugeFrechetLinearTermCloses {P : GeometricProgram}
    (program : GeneratedQEDProgram P) : Prop :=
  IsC2Certified program.vacuumAction program.path

def QEDResidueIsMixedPairTerm {P : GeometricProgram}
    (program : GeneratedQEDProgram P) : Prop :=
  CubicGaugeVariation.mixedCubicCoupling
    program.excitationAction program.path program.electronPair = -1

structure GaugeCommutatorResidueCertificate where
  counting :
    Natural.succ (Natural.succ (1 : Natural)) =
      Natural.succ (2 : Natural)
  linearTermCloses :
    GaugeFrechetLinearTermCloses generatedThreeRungQEDProgram
  residueIsMixedPair :
    QEDResidueIsMixedPairTerm generatedThreeRungQEDProgram

def finiteGauge_successor_commutator_residue :
    GaugeCommutatorResidueCertificate where
  counting := Natural.succ_certificate_lift
  linearTermCloses := generatedThreeRungQEDProgram.vacuumCertified
  residueIsMixedPair := generatedThreeRungQEDProgram.electronReads

theorem finiteGauge_successor_commutator_residue_theorem :
    GaugeFrechetLinearTermCloses generatedThreeRungQEDProgram /\
      QEDResidueIsMixedPairTerm generatedThreeRungQEDProgram := by
  exact ⟨finiteGauge_successor_commutator_residue.linearTermCloses,
    finiteGauge_successor_commutator_residue.residueIsMixedPair⟩

theorem finiteGauge_successor_commutator_residue_from_count
    (_hcount :
      Natural.succ (Natural.succ (1 : Natural)) =
        Natural.succ (2 : Natural)) :
    GaugeFrechetLinearTermCloses generatedThreeRungQEDProgram /\
      QEDResidueIsMixedPairTerm generatedThreeRungQEDProgram := by
  exact finiteGauge_successor_commutator_residue_theorem

theorem finiteCohen_gauge_residue_closeout (epsilon : Nat) :
    (exists _ledger : FiniteCohenCompliantEpsilon epsilon, True) /\
      GaugeFrechetLinearTermCloses generatedThreeRungQEDProgram /\
        QEDResidueIsMixedPairTerm generatedThreeRungQEDProgram := by
  exact ⟨⟨splineCondition_finiteCohenCompliant epsilon, trivial⟩,
    finiteGauge_successor_commutator_residue_theorem⟩

#print axioms splineCondition_finiteCohenCompliant
#print axioms lanczosSpline_cohen_compliant
#print axioms finiteCohen_boundary_radiation_closeout
#print axioms finiteGauge_successor_commutator_residue
#print axioms finiteGauge_successor_commutator_residue_theorem
#print axioms finiteGauge_successor_commutator_residue_from_count
#print axioms finiteCohen_gauge_residue_closeout

end Measurement
