import Experiments.TheOlbersEffect.Experiment2

namespace Experiments.TheOlbersEffect

/-
Experiment3: short path versus long path (updated for the device-coupled Experiment1).
The direct reading and the audited route funge back to the same receipt.
-/

def shortPath : Bool :=
  run defaultSetup

def longPath : Bool :=
  auditedExperiment.run defaultSetup

theorem short_long_outputs_agree :
    shortPath = longPath := rfl

theorem short_long_claims_agree :
    experiment.claim defaultSetup = auditedExperiment.claim defaultSetup := rfl

theorem short_long_receipt_closes :
    experiment.claim defaultSetup ∧ auditedExperiment.claim defaultSetup :=
  ⟨exported_claim_holds_at_default, exported_claim_holds_at_default⟩

theorem short_long_tags_agree :
    auditedExperiment.tag = claim.tag := rfl

end Experiments.TheOlbersEffect
