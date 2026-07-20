import Experiments.TheProverVerifierEffect.Experiment2

namespace Experiments.TheProverVerifierEffect

/-
Experiment3: short path versus long path (updated for the device-coupled Experiment1).

The direct Experiment1 reading and the Experiment2 audited route must funge back to the same
receipt: the same run output, the same exported claim, and the same proved default receipt.
-/

/-- The short path is the direct Experiment1 reading. -/
def shortPath : Bool :=
  run defaultSetup

/-- The long path is the Experiment2 audited experiment run on the same setup. -/
def longPath : Bool :=
  auditedExperiment.run defaultSetup

/-- Both paths read the same output. -/
theorem short_long_outputs_agree :
    shortPath = longPath := rfl

/-- The direct exported claim and the audited exported claim are the same proposition. -/
theorem short_long_claims_agree :
    experiment.claim defaultSetup = auditedExperiment.claim defaultSetup := rfl

/-- The receipt comparison closes: the exported claim holds at the default setup on both routes. -/
theorem short_long_receipt_closes :
    experiment.claim defaultSetup ∧ auditedExperiment.claim defaultSetup :=
  ⟨exported_claim_holds_at_default, exported_claim_holds_at_default⟩

/-- The audit path adds bookkeeping, not a new claim ceiling. -/
theorem short_long_tags_agree :
    auditedExperiment.tag = claim.tag := rfl

end Experiments.TheProverVerifierEffect
