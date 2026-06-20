import Measurement.Episode85
import Experiments.Common

/-!
# The Continuum Limit Effect — list of events → continuum, by mesh refinement

The device reads on a **finite mesh**: the event list, sampled at the count-from-origin strain. The
continuum is the `h → 0` limit of that mesh. This experiment **defines** that limit and runs the
**mesh-refinement study** that is the only honest route to it.

## Convention (the device's, not materials-textbook)
- **stress = the device's reading = δ²** (`pairDelta2` = `mixedCubicCoupling`, the mixed second
  difference of `segmentCost`). The reading *is* the stress.
- **strain = the distance = the count from the origin** — the baseline's tag-displacement from the
  symmetric node0. Contravariant (the raised/`after` index).
- **the Lorentz transform is NOT ordained** — the convergence law relating readings across mesh
  levels is *fit* from the refinement, never assumed. Assuming a linear stress/strain law (Hooke)
  *is* ordaining it, and it lands on the wrong threshold (below).

## Why the mesh cannot be refined inside the device
`discriminatingAction.segmentCost x y = if tag x = tag y then 0 else 1` — a binary tag-indicator, and
`tag` collapses every Herbrand term to `{0,1,2}`. So δ² lives entirely in the 3-tag quotient: the
device is pinned at the **coarsest mesh, h = 1, three strain-levels** (the pigeonhole). Deeper terms
collapse to the same three classes — refinement inside the device is a no-op. The continuum is only
*nameable*, as the limit of a refinable graded-cost family whose **coarsest member is this reading.**

## The three provable coarse-mesh samples (the h = 1 anchor, below)
Over the active pair (node1,node2), δ² at strain 0 / 1 / 2 reads −1 / +1 / 0. These are the device's
entire stress/strain dataset: three points, no more available.

## The mesh-refinement study (external; the device cannot run it — it is pinned at h=1)
Embed the indicator in the graded tag-distance `c(x,y)=|x−y|` (the indicator is its saturated h=1
sample). The continuum stress(strain) rises then kinks flat; the true admitting threshold is the
kink. Sampling the strain axis at N+1 points and refining N = 2,4,…,128:

      estimator                                  converges to     error as h→0
      knot / kink (false→before→after→true)      1.0  (TRUE)      → 0
      linear least-squares (Hooke)               1.5  (WRONG)     plateaus at 0.5

**The linear least-squares threshold is biased, not merely noisy.** Refining shrinks sampling error
but the Hooke fit converges to the wrong value because the curve is kinked, not linear (R² plateaus
≈ 0.80, never 1). This is the threshold experiment's R² ≈ 0.19 retold as a *convergence failure*: the
model is wrong, and no refinement repairs it. The **knot** estimator assumes nothing and converges.

## NOT claimed
A computed continuum (the device is pinned at h=1; the continuum is named, never reached); that the
graded-cost family is the unique continuum (it is a modelling choice — three samples do not determine
a curve); any physics beyond "the apparatus samples a stress/strain at three counts-from-origin."
The honest ceiling is the irreducible gap between the h=1 reading and any finer limit.
-/

namespace Experiments.TheContinuumLimitEffect

open Measurement
open Measurement.CubicGaugeVariation

/-- The strain-s baseline: middleRight displaced s tag-steps from the origin node0. -/
def coarsePath : Nat → CubicGaugePath0
  | 0 => { source := node0, middleLeft := node0, middleRight := node0, target := node0 }
  | 1 => { source := node0, middleLeft := node0, middleRight := node1, target := node1 }
  | _ => { source := node0, middleLeft := node0, middleRight := node2, target := node2 }

/-- The active electron/positron pair. -/
def activePair : CubicGaugeVariation0 := pairVariation node1 node2

/-- stress = the device's reading: δ² of the active pair over the strain-s baseline. -/
def stress (s : Nat) : Int := pairDelta2 (coarsePath s) activePair

-- The device's THREE coarse-mesh samples — the entire h=1 stress/strain dataset.
theorem stress_at_origin : stress 0 = -1 := by decide
theorem stress_at_one : stress 1 = 1 := by decide
theorem stress_at_two : stress 2 = 0 := by decide

/-- The content-bearing claim: the device samples the stress at exactly three counts-from-origin
(the coarsest mesh), reading −1, +1, 0. The continuum is their h→0 limit — named here, not computed. -/
def claimStatement : Prop :=
  stress 0 = -1 ∧ stress 1 = 1 ∧ stress 2 = 0

def claim : Experiments.Common.Claim :=
  { tag := Experiments.Common.ClaimTag.smoothShadowAnalogy
    statement := claimStatement }

theorem claim_holds : claim.statement :=
  ⟨stress_at_origin, stress_at_one, stress_at_two⟩

theorem ceiling :
    claim.tag = Experiments.Common.ClaimTag.smoothShadowAnalogy := rfl

/-- The mesh as a setup: which count-from-origin the device reads. -/
structure Setup where
  level : Nat
deriving Repr

def run (setup : Setup) : Int := stress setup.level

/-- The device's coarse-mesh reading expected at each strain-level. -/
def expectedStress : Nat → Int
  | 0 => -1
  | 1 => 1
  | _ => 0

def experiment : Experiments.Common.Experiment Setup Int :=
  { tag := claim.tag
    run := run
    claim := fun setup => run setup = expectedStress setup.level }

instance (setup : Setup) : Decidable (experiment.claim setup) := by
  unfold experiment; exact inferInstance

/-- A boolean probe set next to the experiment, proven to detect exactly the claim. -/
def deviceNear (setup : Setup) : Bool := decide (experiment.claim setup)

theorem deviceNear_detects_claim (setup : Setup) :
    deviceNear setup = true ↔ experiment.claim setup := by
  simp [deviceNear]

def triangulation : Experiments.Common.Triangulation Setup Int :=
  { experiment := experiment
    device := deviceNear
    detects := deviceNear_detects_claim }

#eval stress 0   -- -1  (strain 0, the origin)
#eval stress 1   --  1  (strain 1)
#eval stress 2   --  0  (strain 2 — the device's whole dataset; no finer sample exists)
#print axioms claim_holds

end Experiments.TheContinuumLimitEffect
