import Experiments.TheQuicksandEffect.Experiment1

namespace Experiments.TheQuicksandEffect

/-
Experiment2: feedback audit layer.

The adversarial review noted that `Experiment1.experiment.claim` must not be
read as a theorem about arbitrary setups.  This layer makes the intended shape
explicit: the exported claim is the setup-local proposition computed from
`run setup`.  The default receipt is still only a proof for `defaultSetup`;
other setups must supply their own preconditions.
-/

def defaultOutput : RunOutput :=
  run defaultSetup

theorem defaultOutput_eq_run :
    defaultOutput = run defaultSetup := by
  rfl

theorem exported_tag_matches_claim :
    experiment.tag = claim.tag := by
  rfl

theorem tag_allows_modelKind :
    Experiments.Common.ClaimTag.allowsModelKind claim.tag modelKind = true := by
  decide

theorem claimStatement_holds_when_transport_budget_suffices (setup : Setup)
    (h : (run setup).required <= (run setup).recorded + (run setup).accessible) :
    claimStatement (run setup) := by
  exact h

theorem exported_claim_is_setup_local (setup : Setup) :
    experiment.claim setup = claimStatement (run setup) := by
  rfl

theorem audited_claim_holds :
    claim.statement := by
  exact claim_holds

theorem exported_claim_holds_at_default :
    experiment.claim defaultSetup := by
  exact claim_holds

theorem exported_claim_tracks_run (setup : Setup) :
    experiment.claim setup = claimStatement (run setup) := by
  rfl

def auditedExperiment : Experiments.Common.Experiment Setup RunOutput :=
  experiment

end Experiments.TheQuicksandEffect
