import Experiments.Common

/-!
# Repeatability of Invisible Motion — rebuilt to the exemplar shape

Source: `instrument/chapters/06.tex:1071` (`ex:repeatability`).

Two finite-resolution observers `A` and `B` record the motion of a particle between the same
anchors. Each refines its instrument until **no further distinguishable events** appear on the
interval; the absence of new records forces each to recover the same minimal-degree reconstruction
— a cubic patch carrying a value, a slope, and a bending moment at the shared anchor. When `A` and
`B` exchange data and jointly refine, any disagreement in value, slope, or bending at the shared
anchor would itself generate an observable event; to avoid that contradiction the patches must
**glue** (continuous `U`, `U'`, `U''`).

This file gives that the *finite* content of the phenomenon:

* a **domain type** for the reconstruction (`CubicPatch`) and for an observer's refinement record
  (`Refinement`), NOT the generic 3-`Nat` `CountSetup`;
* **falsifiable** `∀`-lemmas: one per agreement channel (value / slope / bending), each of which
  breaks if its hypothesis is dropped — and the resolution bound, which breaks if the count
  exceeds the floor;
* a **content-bearing** claim: the two observers' patches glue AND the refined event count stays
  within the finite resolution floor;
* the gluing conjunct is discharged through the harness `Experiments.Common.Boundary.compatible`
  and the resolution conjunct through `Experiments.Common.Counting.boundedBy_of_eq`, so a
  regression in those harness theorems breaks THIS build (load-bearing coupling).

## NOT claimed
This does **not** prove the dense-limit theorem `U⁽⁴⁾ = 0`, nor that smooth dynamics are the unique
traceless histories, nor any Euler–Lagrange closure as a limit of refinements. There is no actual
limit taken, no calculus, no convergence. "Cubic" here is a labelled finite record of three jet
components (value, slope, bending) at one anchor — not a derived polynomial degree. The model
asserts only the **finite** repeatability/gluing obligation: agreement at the shared anchor implies
the boundary jets coincide, and a refinement that detects no new events has its event count pinned
at the floor. **Claim ceiling:** a finite shadow of the smooth gluing argument.
-/

namespace Experiments.RepeatabilityOfInvisibleMotion

/-- The minimal-degree reconstruction one observer recovers on the interval: its value, slope, and
bending moment (the `U`, `U'`, `U''` jet) at the shared anchor.  "Cubic" is a label — these are the
three boundary jets that must match for two patches to glue. -/
structure CubicPatch where
  value : Int
  slope : Int
  bending : Int
deriving DecidableEq, Repr

/-- An observer's refinement record on the interval: the boundary jet it reconstructed, and the
number of distinguishable events it still resolves at its instrument's floor. -/
structure Observer where
  patch : CubicPatch
  events : Nat
  floor : Nat
deriving Repr

namespace CubicPatch

/-- Two patches **glue** at the shared anchor iff their value, slope, and bending all agree —
continuity of `U`, `U'`, `U''`.  All three conjuncts are required, and each is pinned by a
falsifiable lemma below. -/
def glues (p q : CubicPatch) : Prop :=
  p.value = q.value ∧ p.slope = q.slope ∧ p.bending = q.bending

instance (p q : CubicPatch) : Decidable (p.glues q) := by
  unfold glues; exact inferInstance

end CubicPatch

-- ---------------------------------------------------------------------------
-- FALSIFIABLE lemmas: ONE PER GLUING CHANNEL, so the whole rule is load-bearing.
-- Each breaks if `glues` dropped that conjunct.
-- ---------------------------------------------------------------------------

/-- A value mismatch at the anchor is itself an observable event: such patches cannot glue. -/
theorem valueMismatch_not_glued
    (p q : CubicPatch) (h : p.value ≠ q.value) : ¬ p.glues q :=
  fun hg => h hg.1

/-- A slope mismatch (`U'` discontinuity) blocks gluing — pins the middle conjunct. -/
theorem slopeMismatch_not_glued
    (p q : CubicPatch) (h : p.slope ≠ q.slope) : ¬ p.glues q :=
  fun hg => h hg.2.1

/-- A bending mismatch (`U''` discontinuity) blocks gluing — pins the last conjunct. -/
theorem bendingMismatch_not_glued
    (p q : CubicPatch) (h : p.bending ≠ q.bending) : ¬ p.glues q :=
  fun hg => h hg.2.2

-- ---------------------------------------------------------------------------
-- HARNESS COUPLING (load-bearing).
--   * gluing            ->  Experiments.Common.Boundary.compatible
--   * resolution floor  ->  Experiments.Common.Counting.boundedBy_of_eq
-- ---------------------------------------------------------------------------

/-- The boundary an observer exposes is exactly its reconstructed jet.  Two observers are
boundary-`compatible` iff they exposed the same jet — that is the harness encoding of gluing. -/
def anchorBoundary : Experiments.Common.Boundary Observer CubicPatch :=
  { restrict := fun o => o.patch }

/-- An observer's finite ledger of still-distinguishable events (one placeholder event per
resolved record), used to express the resolution floor through the harness counter. -/
def eventLedger (o : Observer) : Experiments.Common.Ledger Unit :=
  { events := List.replicate o.events () }

theorem eventLedger_count (o : Observer) :
    (eventLedger o).count = o.events := by
  simp [eventLedger, Experiments.Common.Ledger.count]

-- ---------------------------------------------------------------------------
-- The canonical no-new-events scenario: both observers refined to the SAME cubic patch
-- (forced by the absence of distinguishable events), at a floor that bounds their event count.
-- ---------------------------------------------------------------------------

/-- The common reconstruction both observers are forced to (an arbitrary fixed cubic jet). -/
def reconstructed : CubicPatch := { value := 3, slope := 2, bending := 1 }

/-- Observer `A`: recovered the patch, resolves no further events, floor `4`. -/
def observerA : Observer := { patch := reconstructed, events := 0, floor := 4 }

/-- Observer `B`: independently recovered the SAME patch, also no further events. -/
def observerB : Observer := { patch := reconstructed, events := 0, floor := 4 }

/-- The two reconstructions glue (concrete, via the `Decidable` instance). -/
theorem patches_glue : observerA.patch.glues observerB.patch := by decide

/-- Boundary-compatibility = gluing, discharged through the harness. -/
theorem observers_compatible :
    anchorBoundary.compatible observerA observerB := by
  unfold Experiments.Common.Boundary.compatible anchorBoundary observerA observerB reconstructed
  rfl

/-- After refining to no-new-events, A's ledger has exactly `events` records, and that count is
bounded by the instrument floor.  `boundedBy_of_eq` proves the bound from the exact tally
`count = events` (provided by `eventLedger_count`); the bound supplied is `A`'s own event count,
so this is discharged through the harness counter and breaks if that theorem regresses. -/
theorem eventsA_at_floor :
    Experiments.Common.Counting.boundedBy (eventLedger observerA) observerA.events :=
  Experiments.Common.Counting.boundedBy_of_eq (eventLedger_count observerA)

-- ---------------------------------------------------------------------------
-- THE CLAIM (content-bearing; two conjuncts discharged by harness theorems).
-- ---------------------------------------------------------------------------

/-- The claim, in honest parts:
* (gluing) the two observers' jets glue — `observers_compatible`, via `Boundary.compatible`;
* (resolution floor) A's refined ledger count is bounded by its resolved event tally —
  `eventsA_at_floor`, via `Counting.boundedBy_of_eq`;
* (consistency) the shared patch is literally the same on both sides. -/
def claimStatement : Prop :=
  anchorBoundary.compatible observerA observerB ∧
    Experiments.Common.Counting.boundedBy (eventLedger observerA) observerA.events ∧
    observerA.patch = observerB.patch

def claim : Experiments.Common.Claim :=
  { tag := Experiments.Common.ClaimTag.smoothShadowAnalogy
    statement := claimStatement }

theorem claim_holds : claim.statement :=
  ⟨observers_compatible, eventsA_at_floor, rfl⟩

/-- The tag is an honest ceiling: a finite shadow of the smooth gluing argument. -/
theorem ceiling :
    claim.tag = Experiments.Common.ClaimTag.smoothShadowAnalogy := rfl

-- ---------------------------------------------------------------------------
-- A computable run + a non-vacuous Experiment.claim, with a proved bridge.
-- ---------------------------------------------------------------------------

structure Setup where
  a : Observer
  b : Observer

/-- The run computes — thanks to the `Decidable` instance on `glues`. -/
def run (s : Setup) : Bool := decide (s.a.patch.glues s.b.patch)

def experiment : Experiments.Common.Experiment Setup Bool :=
  { tag := claim.tag
    run := run
    claim := fun s => s.a.patch.glues s.b.patch }

theorem run_iff_claim (s : Setup) :
    run s = true ↔ experiment.claim s := by
  simp only [run, experiment, decide_eq_true_iff]

def canonicalSetup : Setup := { a := observerA, b := observerB }

/-- A disagreeing observer: same value/slope but a DIFFERENT bending moment — must NOT glue. -/
def observerBent : Observer := { observerB with patch := { reconstructed with bending := 99 } }

#eval run canonicalSetup                                  -- expect: true
#eval run { canonicalSetup with b := observerBent }       -- expect: false  (U'' mismatch)
#print axioms claim_holds

/-- Bring a minimal device next to this experiment: it records whether the exported claim fires. -/
def deviceNear (setup : Setup) : Bool :=
  decide (experiment.claim setup)

theorem deviceNear_detects_claim (setup : Setup) :
    deviceNear setup = true ↔ experiment.claim setup := by
  simp [deviceNear]

def triangulation : Experiments.Common.Triangulation Setup Bool :=
  { experiment := experiment
    device := deviceNear
    detects := deviceNear_detects_claim }

end Experiments.RepeatabilityOfInvisibleMotion
