import Experiments.ThePositronAnnihilationEffect.Experiment2

namespace Experiments.ThePositronAnnihilationEffect

/-
Experiment3: short path versus long path.

The short path is the direct annihilation apparatus from Experiment1.  The long
path is the audited common-interface route from Experiment2.  They must agree
on the canonical coincidence, preserve the same non-vacuous local claim, and
still expose the real Measurement device receipt.
-/

/-- The short path is the direct Experiment1 reading. -/
def shortPath : Bool :=
  run canonicalSetup

/-- The long path is the audited Experiment2 run on the same setup. -/
def longPath : Bool :=
  auditedExperiment.run canonicalSetup

/-- Both paths register the same canonical annihilation event. -/
theorem short_long_outputs_agree :
    shortPath = longPath := by
  rfl

/-- The direct claim and the audited exported claim are the same setup-local proposition. -/
theorem short_long_claims_agree :
    experiment.claim canonicalSetup = auditedExperiment.claim canonicalSetup := by
  rfl

/-- The short path sees the canonical coincidence. -/
theorem short_path_detects_canonical :
    shortPath = true := by
  decide

/-- The long path sees the same canonical coincidence. -/
theorem long_path_detects_canonical :
    longPath = true := by
  decide

/-- The control path rejects a same-direction pair, so the test is not vacuous. -/
theorem control_path_rejected :
    run { canonicalSetup with right := gammaA } = false := by
  exact same_direction_run_is_false

/--
The receipt comparison closes: both the short direct claim and the audited
exported claim hold at the canonical setup.
-/
theorem short_long_receipt_closes :
    experiment.claim canonicalSetup ∧ auditedExperiment.claim canonicalSetup := by
  constructor
  · exact exported_claim_holds_at_canonical
  · exact exported_claim_holds_at_canonical

/-- The audited route keeps the same claim ceiling. -/
theorem short_long_tags_agree :
    auditedExperiment.tag = claim.tag := by
  rfl

/-- The comparison still carries the real device coupling, not only the finite detector check. -/
theorem short_long_device_receipt_closes :
    Measurement.electronMeasurement.relVel + Measurement.positronReading.relVel = 0 ∧
      Measurement.HasPositronEvent Measurement.tiltedEvents := by
  exact device_coupling_holds

end Experiments.ThePositronAnnihilationEffect
