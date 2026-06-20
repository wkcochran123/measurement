import Experiments.TheMaxwellEffect.Experiment2

namespace Experiments.TheMaxwellEffect

/-
Experiment3: short path versus long path.

Experiment1 gives the direct finite ledger reading: run the default setup and
state the local claim on that output.

Experiment2 gives the audited route: expose the exported experiment, its tag,
and the fact that the exported claim is the setup-local statement evaluated at `defaultSetup`.

This layer compares those two routes.  The extra audit bookkeeping is allowed
to travel, but it must funge back to the same receipt: the same run output, the
same claim proposition, and the same proved default receipt.
-/

/-- The short path is the direct Experiment1 reading. -/
def shortPath : RunOutput :=
  run defaultSetup

/-- The long path is the Experiment2 audited experiment run on the same setup. -/
def longPath : RunOutput :=
  auditedExperiment.run defaultSetup

/-- Both paths read the same finite ledger output. -/
theorem short_long_outputs_agree :
    shortPath = longPath := by
  rfl

/-- The direct claim and the exported audited claim are the same proposition. -/
theorem short_long_claims_agree :
    claimStatement shortPath = auditedExperiment.claim defaultSetup := by
  rfl

/--
The receipt comparison closes: both the short direct claim and the audited
exported claim hold at the default setup.
-/
theorem short_long_receipt_closes :
    claimStatement shortPath ∧ auditedExperiment.claim defaultSetup := by
  constructor
  · exact claim_holds
  · exact exported_claim_holds_at_default

/-- The audit path adds bookkeeping, not a new claim ceiling. -/
theorem short_long_tags_agree :
    auditedExperiment.tag = claim.tag := by
  rfl

end Experiments.TheMaxwellEffect
