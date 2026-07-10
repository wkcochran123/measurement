import Measurement.Episode73
import Measurement.Formalization.ReciprocalAccounting

namespace Measurement

/-!
Episode 74 lifts the checked reciprocal-accounting artifact into the episode
spine.  The episode does not reprove the Nat numerator ledger; it packages the
three-rung instance and points back to the accepted finite accounting surface.
-/

def threeRungReciprocalIndex : ReciprocalFiniteIndex where
  count := 3
  positive := by decide

theorem threeRung_resolved_add_unresolved_eq_whole :
    (resolvedComplement threeRungReciprocalIndex).numerator +
        (unresolvedPartScale threeRungReciprocalIndex).numerator =
      (wholeCountUnit threeRungReciprocalIndex).numerator :=
  resolved_add_unresolved_eq_whole threeRungReciprocalIndex

theorem reciprocalAccounting_truth_parity_surface :
    orientationOfParity .same = .covariantWhole /\
      orientationOfParity .different = .contravariantPart := by
  exact
    ⟨same_truth_parity_selects_whole,
      different_truth_parity_selects_reciprocal⟩

theorem threeRung_reciprocal_residue_certificate
    (epsilon : Nat) :
    exists _cert :
      ReciprocalResidueCertificate epsilon threeRungReciprocalIndex,
      True :=
  reciprocal_residue_certificate epsilon threeRungReciprocalIndex

theorem threeRung_preHilbert_reciprocal_energy
    {epsilon : Nat} {D : SobolevHilbertDoor}
    (skeleton : FiniteCohenPreHilbertSkeleton epsilon D) :
    exists _energy :
      PreHilbertReciprocalEnergyLedger skeleton threeRungReciprocalIndex,
      True :=
  finiteCohen_preHilbert_reciprocal_energy skeleton threeRungReciprocalIndex

theorem episode74_reciprocal_accounting_package
    {epsilon : Nat} {D : SobolevHilbertDoor}
    (skeleton : FiniteCohenPreHilbertSkeleton epsilon D) :
    (resolvedComplement threeRungReciprocalIndex).numerator +
        (unresolvedPartScale threeRungReciprocalIndex).numerator =
      (wholeCountUnit threeRungReciprocalIndex).numerator /\
    (orientationOfParity .same = .covariantWhole /\
      orientationOfParity .different = .contravariantPart) /\
    (exists _cert :
      ReciprocalResidueCertificate epsilon threeRungReciprocalIndex,
      True) /\
    (exists _energy :
      PreHilbertReciprocalEnergyLedger skeleton threeRungReciprocalIndex,
      True) := by
  exact
    ⟨threeRung_resolved_add_unresolved_eq_whole,
      reciprocalAccounting_truth_parity_surface,
      threeRung_reciprocal_residue_certificate epsilon,
      threeRung_preHilbert_reciprocal_energy skeleton⟩

#print axioms threeRung_resolved_add_unresolved_eq_whole
#print axioms reciprocalAccounting_truth_parity_surface
#print axioms threeRung_reciprocal_residue_certificate
#print axioms threeRung_preHilbert_reciprocal_energy
#print axioms episode74_reciprocal_accounting_package

end Measurement
