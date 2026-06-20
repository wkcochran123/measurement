import Experiments.Common

namespace Experiments.TheVonNeumannEffect

/-
Source description: The von Neumann Effect
Claim ceiling: inadmissibilityNoGo.
The model records a finite obstruction: the requested refinement exceeds the accessible ledger.
-/

abbrev Setup := Experiments.Common.CountSetup

abbrev RunOutput := Experiments.Common.CountOutput

def modelKind : Experiments.Common.ModelKind :=
  Experiments.Common.ModelKind.blocks

def defaultSetup : Setup :=
  { recorded := 1, accessible := 1, required := 2 }

def run (setup : Setup) : RunOutput :=
  Experiments.Common.runCount setup

def claimStatement (output : RunOutput) : Prop :=
  Experiments.Common.ModelKind.holds modelKind output

def claim : Experiments.Common.Claim :=
  { tag := Experiments.Common.ClaimTag.inadmissibilityNoGo
    statement := claimStatement (run defaultSetup) }

theorem claim_holds : claim.statement := by
  unfold claim claimStatement modelKind Experiments.Common.ModelKind.holds
  decide

theorem ceiling :
    claim.tag = Experiments.Common.ClaimTag.inadmissibilityNoGo := by
  rfl

def experiment : Experiments.Common.Experiment Setup RunOutput :=
  { tag := claim.tag
    run := fun setup => run setup
    claim := fun setup => claimStatement (run setup) }


/-- Bring a minimal device next to this experiment: it records whether the exported claim fires. -/
def deviceNear (setup : Setup) : Bool :=
  decide (experiment.claim setup)

theorem deviceNear_detects_claim (setup : Setup) :
    deviceNear setup = true ↔ experiment.claim setup := by
  simp [deviceNear]

def triangulation : Experiments.Common.Triangulation Setup RunOutput :=
  { experiment := experiment
    device := deviceNear
    detects := deviceNear_detects_claim }

end Experiments.TheVonNeumannEffect
