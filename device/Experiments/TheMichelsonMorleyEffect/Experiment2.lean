import Experiments.TheMichelsonMorleyEffect.Experiment1

namespace Experiments.TheMichelsonMorleyEffect

/-
Experiment2: feedback audit layer (updated for the device-coupled Experiment1).
The exported per-setup claim is the run firing, the default receipt holds, and the tag is unchanged.
-/

def defaultOutput : Bool :=
  run defaultSetup

theorem defaultOutput_eq_run :
    defaultOutput = run defaultSetup := rfl

theorem exported_tag_matches_claim :
    experiment.tag = claim.tag := rfl

theorem audited_claim_holds :
    claim.statement := claim_holds

/-- The exported per-setup claim fires exactly when the run reports `true` (setup-local, decidable). -/
theorem exported_claim_iff_run (setup : Setup) :
    experiment.claim setup ↔ run setup = true := by
  show framesRelative setup ↔ decide (framesRelative setup) = true
  exact (decide_eq_true_iff).symm

/-- The exported claim holds at the default setup (the two frames read opposite signs). -/
theorem exported_claim_holds_at_default :
    experiment.claim defaultSetup := by
  show framesRelative defaultSetup
  decide

def auditedExperiment : Experiments.Common.Experiment Setup Bool :=
  experiment

end Experiments.TheMichelsonMorleyEffect
