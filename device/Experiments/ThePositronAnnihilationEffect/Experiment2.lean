import Experiments.ThePositronAnnihilationEffect.Experiment1

namespace Experiments.ThePositronAnnihilationEffect

/-
Experiment2: audit layer for the canonical annihilation test.

Unlike the generated CountSetup files, this experiment is not a frozen claim
behind the common interface.  Its exported claim is the setup-local coincidence
predicate itself, while the top-level `claim_holds` receipt couples the
canonical coincidence to the real Measurement device theorems.
-/

def defaultOutput : Bool :=
  run canonicalSetup

theorem defaultOutput_eq_run :
    defaultOutput = run canonicalSetup := by
  rfl

theorem exported_tag_matches_claim :
    experiment.tag = claim.tag := by
  rfl

theorem tag_allows_finite_ledger_model :
    Experiments.Common.ClaimTag.allowsModelKind
      claim.tag Experiments.Common.ModelKind.preserves = true := by
  decide

theorem exported_claim_is_setup_local (setup : Setup) :
    experiment.claim setup = setup.detector.registers setup.left setup.right := by
  rfl

theorem exported_claim_holds_at_canonical :
    experiment.claim canonicalSetup := by
  exact registers_canonical

theorem canonical_run_is_true :
    run canonicalSetup = true := by
  decide

theorem same_direction_run_is_false :
    run { canonicalSetup with right := gammaA } = false := by
  decide

theorem audited_claim_holds :
    claim.statement := by
  exact claim_holds

theorem device_coupling_holds :
    Measurement.electronMeasurement.relVel + Measurement.positronReading.relVel = 0 ∧
      Measurement.HasPositronEvent Measurement.tiltedEvents := by
  exact ⟨Measurement.split_cancels, Measurement.positron_over_tiltedPath⟩

theorem claim_contains_device_split :
    claim.statement ->
      Measurement.electronMeasurement.relVel + Measurement.positronReading.relVel = 0 :=
  fun h => h.2.1

theorem claim_contains_tilted_positron :
    claim.statement -> Measurement.HasPositronEvent Measurement.tiltedEvents :=
  fun h => h.2.2.1

def auditedExperiment : Experiments.Common.Experiment Setup Bool :=
  experiment

end Experiments.ThePositronAnnihilationEffect
