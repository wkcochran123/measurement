import Experiments.TheMessageEffect.Experiment1

namespace Experiments.TheMessageEffect

/-
Experiment2: feedback audit layer.

The adversarial review noted that `Experiment1.experiment.claim` must not be
read as a theorem about arbitrary setups.  This layer makes the intended shape
explicit: the exported claim is the setup-local proposition computed from
`run setup`.  The default receipt is still only a proof for `defaultSetup`;
other setups must supply their own preconditions.
-/

def defaultOutput : Bool :=
  run canonicalSetup

theorem defaultOutput_eq_run :
    defaultOutput = run canonicalSetup := by
  rfl

theorem exported_tag_matches_claim :
    experiment.tag = claim.tag := by
  rfl

theorem tag_allows_modelKind :
    Experiments.Common.ClaimTag.allowsModelKind
      claim.tag Experiments.Common.ModelKind.projects = true := by
  decide

theorem exported_claim_is_setup_local (setup : Setup) :
    experiment.claim setup = sameMessage setup.sent setup.reference := by
  rfl

theorem audited_claim_holds :
    claim.statement := by
  exact claim_holds

theorem exported_claim_holds_at_canonical :
    experiment.claim canonicalSetup := by
  exact curl_is_unrecordable

theorem exported_claim_tracks_run (setup : Setup) :
    run setup = true ↔ experiment.claim setup :=
  run_iff_claim setup

def auditedExperiment : Experiments.Common.Experiment Setup Bool :=
  experiment

end Experiments.TheMessageEffect
