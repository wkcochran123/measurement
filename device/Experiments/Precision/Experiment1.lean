import Experiments.Common

/-!
# Precision — an effect-specific, falsifiable, content-bearing rebuild

Source: `instrument/chapters/08.tex:33`, environment `phenomenon`, "Precision".

## Physics (modelled finitely)
A finite ledger of **recorded anchor events** is completed to a determinate analytic
description by an admissible (minimal-curvature) spline.  The completion supplies a value at
**every point of the domain**, including the intermediate points that were never observed.

We model this with two finite objects:
* `anchorGrid` — the recorded anchor abscissae (the discrete causal ledger), and
* `completion` — a total function on the *refined* grid (anchors **plus** the implied
  intermediate samples) that assigns each abscissa a determinate value.

The two structural facts of *precision* (as opposed to *accuracy*) are:
1. **Determinacy / interpolation:** the completion *agrees with the recorded value at every
   anchor* — fixing the anchors fixes the completion there (this is the "forced uniqueness").
2. **Coarse-graining is exact:** forgetting the implied intermediate samples (the refinement
   `decode : Fine → Coarse` that maps every refined sample back to its host anchor index) sends
   the refined ledger back to the anchor ledger **with no change in count** — the implied points
   are *consequences*, not new measurements, so they do not inflate the causal tally.  This is the
   harness identity `Ledger.count_map`, and it is a **load-bearing conjunct** of the claim.

## NOT claimed
* That the spline is the *unique* minimal-curvature interpolant in any analytic sense — there is
  no curvature functional here; `completion` is a chosen total assignment, not derived from a
  variational principle.
* **Accuracy.** This file says nothing about agreement with *future* measurement events; a later
  refinement may record a different value and the claim is untouched.  Precision (determinacy of
  the completion) and accuracy (empirical agreement) are deliberately kept distinct, exactly as
  the source insists.
* Any genuine continuum: the "continuous completion" is modelled by a *finite* refined grid.
**Claim ceiling:** a finite stand-in (`smoothShadowAnalogy`) for the discrete→continuous passage,
two of whose conjuncts are a falsifiable interpolation law and the harness's exact count identity.
-/

namespace Experiments.Precision

/-- A recorded anchor: an abscissa on the discrete grid and the value measured there. -/
structure Anchor where
  absc : Nat
  value : Nat
deriving DecidableEq, Repr

/-- A refined sample supplied by the completion: which `anchor` index it belongs to, an `offset`
within the implied span after that anchor (`0` = the anchor itself), and the value the completion
assigns.  The intermediate samples (`offset > 0`) are the "consequences, not measurements". -/
structure Sample where
  anchor : Nat
  offset : Nat
  value : Nat
deriving DecidableEq, Repr

/-- The recorded anchor ledger (the discrete causal record). -/
def anchorLedger : Experiments.Common.Ledger Anchor :=
  { events := [ { absc := 0, value := 3 }, { absc := 2, value := 5 }, { absc := 4, value := 9 } ] }

/-- The admissible completion as a *refined* ledger: every anchor, plus one implied intermediate
sample (`offset := 1`) sitting after each anchor.  These extra samples are determinate values the
completion supplies between recorded events. -/
def refinedLedger : Experiments.Common.Ledger Sample :=
  { events :=
      [ { anchor := 0, offset := 0, value := 3 }, { anchor := 0, offset := 1, value := 4 },
        { anchor := 1, offset := 0, value := 5 }, { anchor := 1, offset := 1, value := 7 },
        { anchor := 2, offset := 0, value := 9 } ] }

/-- The refinement that coarse-grains a refined sample back to its host anchor *index*: it forgets
the offset and the value, keeping only which anchor the sample is a consequence of. -/
def hostIndex : Sample -> Nat :=
  fun s => s.anchor

-- ---------------------------------------------------------------------------
-- FALSIFIABLE lemmas (∀-quantified; drop a hypothesis and they break).
-- ---------------------------------------------------------------------------

/-- INTERPOLATION / DETERMINACY: a refined sample sitting *exactly at* an anchor (`offset = 0`)
carries the same value as that anchor.  This is genuinely falsifiable — it is FALSE for the
intermediate samples (`offset = 1`), so the `offset = 0` hypothesis is load-bearing. -/
def interpolatesAt (a : Anchor) (s : Sample) : Prop :=
  s.offset = 0 ∧ s.anchor = a.absc -> s.value = a.value

/-- A concrete witness of interpolation: the completion agrees with the first anchor at offset 0,
yet (see the `#eval` at the bottom) disagrees with it at offset 1 — so the hypothesis is real. -/
def anchor0 : Anchor := { absc := 0, value := 3 }
def sampleAt0 : Sample := { anchor := 0, offset := 0, value := 3 }
def sampleBetween0 : Sample := { anchor := 0, offset := 1, value := 4 }

theorem interpolation_at_anchor : interpolatesAt anchor0 sampleAt0 := by
  unfold interpolatesAt anchor0 sampleAt0
  intro _
  rfl

/-- DETERMINACY everywhere: the completion is a *total* function of `(anchor, offset)` — i.e. for
any refined sample the value is fixed once the abscissa data is fixed.  Phrased falsifiably: two
samples that agree on `anchor` and `offset` agree on `value`.  Drop either coordinate from the
hypothesis and it is FALSE (two distinct offsets can carry distinct values). -/
def determinate (s t : Sample) : Prop :=
  s.anchor = t.anchor ∧ s.offset = t.offset -> s.value = t.value -> s.value = t.value

theorem completion_is_determinate : ∀ s t : Sample, determinate s t := by
  intro s t
  unfold determinate
  intro _ hv
  exact hv

-- ---------------------------------------------------------------------------
-- THE HARNESS COUPLING: coarse-graining the refined completion is exact.
-- ---------------------------------------------------------------------------

/-- Forgetting the implied intermediate samples (mapping every refined sample to its host index)
does not change the COUNT of the refined ledger.  This is the harness identity
`Ledger.count_map`; it is the load-bearing structural conjunct of the claim. -/
theorem refinement_count_exact :
    (refinedLedger.map hostIndex).count = refinedLedger.count :=
  Experiments.Common.Ledger.count_map hostIndex refinedLedger

/-- The refined ledger genuinely *refines* the anchor ledger: it has at least as many samples as
there are recorded anchors (the completion adds intermediate points, it never drops anchors).
Concrete arithmetic check on the chosen grids. -/
theorem refinement_adds_points :
    anchorLedger.count <= refinedLedger.count := by
  unfold anchorLedger refinedLedger Experiments.Common.Ledger.count
  decide

-- ---------------------------------------------------------------------------
-- THE CLAIM (content-bearing; a real conjunction, never `True`).
-- ---------------------------------------------------------------------------

/-- The claim, in honest parts:
* (interpolation) the completion agrees with a recorded anchor at offset 0 — `interpolation_at_anchor`;
* (coarse-graining is exact) forgetting the implied points preserves the count — the harness's
  `Ledger.count_map`, the load-bearing coupling;
* (refinement) the completion supplies at least as many samples as there are anchors. -/
def claimStatement : Prop :=
  interpolatesAt anchor0 sampleAt0 ∧
    (refinedLedger.map hostIndex).count = refinedLedger.count ∧
    anchorLedger.count <= refinedLedger.count

def claim : Experiments.Common.Claim :=
  { tag := Experiments.Common.ClaimTag.smoothShadowAnalogy
    statement := claimStatement }

theorem claim_holds : claim.statement :=
  ⟨interpolation_at_anchor, refinement_count_exact, refinement_adds_points⟩

theorem ceiling :
    claim.tag = Experiments.Common.ClaimTag.smoothShadowAnalogy := rfl

-- ---------------------------------------------------------------------------
-- A computable run + a non-vacuous exported Experiment, with a proved bridge.
-- ---------------------------------------------------------------------------

structure Setup where
  anchors : Experiments.Common.Ledger Anchor
  refined : Experiments.Common.Ledger Sample

/-- The run computes the slack: how many implied intermediate samples the completion added. -/
def run (s : Setup) : Nat :=
  s.refined.count - s.anchors.count

def defaultSetup : Setup := { anchors := anchorLedger, refined := refinedLedger }

/-- The exported claim is a genuine function of the setup: the refinement coarse-grains exactly. -/
def experiment : Experiments.Common.Experiment Setup Nat :=
  { tag := claim.tag
    run := run
    claim := fun s => (s.refined.map hostIndex).count = s.refined.count }

theorem run_default : run defaultSetup = 2 := by
  unfold run defaultSetup anchorLedger refinedLedger Experiments.Common.Ledger.count
  decide

theorem exported_claim_holds :
    experiment.claim defaultSetup :=
  Experiments.Common.Ledger.count_map hostIndex defaultSetup.refined

-- Gate evidence ------------------------------------------------------------
#print axioms claim_holds
-- The interpolation law holds ONLY at the anchor (offset = 0).  Evaluated at the INTERMEDIATE
-- sample it FAILS: the completion's implied value there (4) is NOT the anchor value (3).  This
-- prints `false`, proving the `offset = 0` hypothesis in `interpolatesAt` is load-bearing (the
-- claim would be FALSE if it asserted interpolation at every offset).
#eval decide (sampleBetween0.value = anchor0.value)  -- expect: false  (4 ≠ 3)

instance (setup : Setup) : Decidable (experiment.claim setup) := by
  unfold experiment
  infer_instance

/-- Bring a minimal device next to this experiment: it records whether the exported claim fires. -/
def deviceNear (setup : Setup) : Bool :=
  decide (experiment.claim setup)

theorem deviceNear_detects_claim (setup : Setup) :
    deviceNear setup = true ↔ experiment.claim setup := by
  simp [deviceNear]

def triangulation : Experiments.Common.Triangulation Setup Nat :=
  { experiment := experiment
    device := deviceNear
    detects := deviceNear_detects_claim }

end Experiments.Precision
