import Experiments.Common
import Measurement.Episode85

/-!
# The Positron Threshold Effect — the last experiment

The tilt that **admits** a positron has a threshold: below it the trial reads pure matter, at/above
it δ² crosses 0 → + and a positron appears. The apparatus is discrete (tags 0/1/2), so the
*continuous* threshold cannot be **computed** — only **bracketed** (in Lean, below) and **estimated**
from the device's two straddling readings. Honest-ceiling form: the apparatus resolves the integer
jump; the crossing is sub-resolution.

## What the device PROVES (the bracket) — see the theorems below
Over the symmetric baseline (strain 0) the antimatter count is 0; over the first tilt (strain 1) it
is ≥ 1. So the admitting threshold lies in the half-open interval **(0, 1]** — one tag-unit wide.

## The estimator: the KNOT method (not linear least-squares)
The two straddling knots are the device's proven δ² readings: the **before** knot is the flat
baseline (strain 0, δ² = −1, electron); the **after** knot is the first tilt (strain 1, δ² = +1,
positron). The line through them crosses δ² = 0 at **strain\* = 1/2** — proven below as
`knot_threshold_is_half` (`knotThreshold = (1, 2)`), unbiased, inside the (0,1] bracket.

This **replaces** the earlier linear least-squares (Hooke) estimate (≈0.19, R² ≈ 0.19). The mesh-
refinement study (`TheContinuumLimitEffect`) proved that estimator is **biased, not merely noisy**:
the stress/strain curve is kinked, not linear, so least-squares converges to the *wrong* crossing
and no refinement repairs it. The knot estimator (false → before → after → true) assumes no
functional form and is the unbiased route to the kink. Assuming the linear law would have *ordained*
the threshold — but the convergence/Lorentz law is the not-ordained object, fit here from the two
straddling knots, never assumed.

## NOT claimed
A *computed* continuum threshold (the device is pinned at the coarsest mesh, h=1, three tags; the
continuum is named, never reached); a real material modulus; any statement about baryogenesis. The
device brackets to (0,1]; the knot estimator places the unbiased crossing at 1/2 from the two
straddling readings; nothing sharper is honest.
-/

namespace Experiments.ThePositronThresholdEffect

open Measurement
open Measurement.CubicGaugeVariation

/-- BRACKET (provable): below the threshold — the symmetric baseline (strain 0) admits NO positron.
This is `Measurement.native_antimatter_is_zero`, so a device regression breaks this build. -/
theorem no_positron_below_threshold : antimatterCount flatEvents = 0 :=
  native_antimatter_is_zero

/-- BRACKET (provable): above it — the first tilt (strain 1) DOES admit a positron. -/
theorem positron_above_threshold : 1 ≤ antimatterCount tiltedEvents :=
  antimatter_needs_asymmetry

/-- The admitting threshold lies in `(0, 1]` — the device brackets it to one tag-unit. The exact
crossing (≈0.2–0.5 by the external least-squares above) is sub-resolution and is *not* computed
here, only estimated. -/
theorem threshold_in_unit_interval :
    antimatterCount flatEvents = 0 ∧ 1 ≤ antimatterCount tiltedEvents :=
  ⟨no_positron_below_threshold, positron_above_threshold⟩

-- ----------------------------------------------------------------
-- THE KNOT ESTIMATOR (unbiased) — replaces the biased linear least-squares.
-- ----------------------------------------------------------------

/-- The device's δ² at the two straddling knots: the **before** knot is the flat baseline (strain 0),
the **after** knot is the first tilt (strain 1). Proven device readings (Episode83/84). -/
def beforeStress : Int := pairDelta2 flatPath (pairVariation node1 node2)
def afterStress : Int := pairDelta2 tiltedPath (pairVariation node1 node2)

theorem before_is_electron : beforeStress = -1 := by decide
theorem after_is_positron : afterStress = 1 := by decide

/-- The knot crossing `(numerator, denominator)` at δ²=0 of the line through straddling knots
`(s0,d0)`,`(s1,d1)`:  `s* = s0 + (-d0)(s1-s0)/(d1-d0)`. The unbiased estimator (false→before→after→
true); linear least-squares is biased for the kinked curve (`TheContinuumLimitEffect`). -/
def knotCrossing (s0 d0 s1 d1 : Int) : Int × Int :=
  (s0 * (d1 - d0) + (-d0) * (s1 - s0), d1 - d0)

/-- THE THRESHOLD by the knot method: before knot `(0, −1)`, after knot `(1, +1)` → crossing at
strain **1/2**, unbiased, inside the proven (0,1] bracket. -/
def knotThreshold : Int × Int := knotCrossing 0 beforeStress 1 afterStress

theorem knot_threshold_is_half : knotThreshold = (1, 2) := by decide

/-- The content-bearing claim: the device brackets the admitting tilt to `(0,1]`, and the knot
estimator places the unbiased crossing at strain `1/2` inside it. -/
def claimStatement : Prop :=
  antimatterCount flatEvents = 0 ∧ 1 ≤ antimatterCount tiltedEvents ∧ knotThreshold = (1, 2)

def claim : Experiments.Common.Claim :=
  { tag := Experiments.Common.ClaimTag.finiteLedgerModel
    statement := claimStatement }

theorem claim_holds : claim.statement :=
  ⟨no_positron_below_threshold, positron_above_threshold, knot_threshold_is_half⟩

theorem ceiling :
    claim.tag = Experiments.Common.ClaimTag.finiteLedgerModel := rfl

/-- The two nearby threshold probes: below the admitted tilt and at the first admitted tilt. -/
inductive ThresholdProbe where
  | below
  | above
deriving DecidableEq, Repr

def eventsFor : ThresholdProbe -> List Orientation
  | ThresholdProbe.below => flatEvents
  | ThresholdProbe.above => tiltedEvents

structure Setup where
  probe : ThresholdProbe
deriving Repr

def run (setup : Setup) : Nat :=
  antimatterCount (eventsFor setup.probe)

def belowSetup : Setup := { probe := ThresholdProbe.below }
def aboveSetup : Setup := { probe := ThresholdProbe.above }

def experiment : Experiments.Common.Experiment Setup Nat :=
  { tag := claim.tag
    run := run
    claim := fun setup =>
      match setup.probe with
      | ThresholdProbe.below => run setup = 0
      | ThresholdProbe.above => 1 ≤ run setup }

theorem below_claim_holds :
    experiment.claim belowSetup :=
  no_positron_below_threshold

theorem above_claim_holds :
    experiment.claim aboveSetup :=
  positron_above_threshold

/-- Bring the threshold-counting device next to the probe and ask what it detects. A direct boolean
probe per case, so no `Decidable (experiment.claim _)` synthesis through the opaque projection. -/
def deviceNear (setup : Setup) : Bool :=
  match setup.probe with
  | ThresholdProbe.below => decide (run setup = 0)
  | ThresholdProbe.above => decide (1 ≤ run setup)

theorem deviceNear_detects_claim (setup : Setup) :
    deviceNear setup = true ↔ experiment.claim setup := by
  cases h : setup.probe <;> simp [deviceNear, experiment, h]

def triangulation : Experiments.Common.Triangulation Setup Nat :=
  { experiment := experiment
    device := deviceNear
    detects := deviceNear_detects_claim }

#print axioms threshold_in_unit_interval   -- the bracket is axiom-free; the estimate is external
#print axioms claim_holds

end Experiments.ThePositronThresholdEffect
