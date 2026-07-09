import Experiments.TheMessageEffect.Experiment2

namespace Experiments.TheMessageEffect

/-
Experiment3: short path versus long path.

Experiment1 gives the direct finite ledger reading: run the default setup and
state the local claim on that output.

Experiment2 gives the audited route: expose the exported experiment, its tag,
and the fact that the exported claim is the setup-local message predicate at
`canonicalSetup`.

This layer compares those two routes.  The extra audit bookkeeping is allowed
to travel, but it must funge back to the same receipt: the same run output, the
same claim proposition, and the same proved default receipt.
-/

/-- The short path is the direct Experiment1 reading. -/
def shortPath : Bool :=
  run canonicalSetup

/-- The long path is the Experiment2 audited experiment run on the same setup. -/
def longPath : Bool :=
  auditedExperiment.run canonicalSetup

/-- Both paths read the same finite ledger output. -/
theorem short_long_outputs_agree :
    shortPath = longPath := by
  rfl

/-- The direct claim and the exported audited claim are the same proposition. -/
theorem short_long_claims_agree :
    experiment.claim canonicalSetup = auditedExperiment.claim canonicalSetup := by
  rfl

/--
The receipt comparison closes: both the short direct claim and the audited
exported claim hold at the default setup.
-/
theorem short_long_receipt_closes :
    experiment.claim canonicalSetup ∧ auditedExperiment.claim canonicalSetup := by
  exact ⟨exported_claim_holds_at_canonical, exported_claim_holds_at_canonical⟩

/-- The audit path adds bookkeeping, not a new claim ceiling. -/
theorem short_long_tags_agree :
    auditedExperiment.tag = claim.tag := by
  rfl

end Experiments.TheMessageEffect
