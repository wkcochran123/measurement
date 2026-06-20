import Experiments.Common
import Measurement.Episode84

/-!
# The Foucault Effect — holonomy of an inconsistent connection

Source: `instrument/chapters/08.tex:1252`, environment `phenomenon`.

> A refinement direction transported around a closed causal loop does not generally return to its
> initial orientation. The failure of closure is not a mechanical torque, but the accumulated
> informational strain required to preserve admissibility under transport. The observed precession
> is the holonomy of an inconsistent connection: a closed path in events produces an open path in
> orientation.

## The model (finite, decidable)
An **orientation** lives on a finite ring of `slots` direction-bins. A **transport schedule** is the
list of signed bin-kicks applied as the refinement direction is carried around a path. We model:

* `transport` — fold the kicks onto a starting orientation (mod `slots`);
* `closes` — the carried orientation returns to where it started (a *closed* path in orientation);
* `precession` — the net residual bin-shift, the **holonomy** of the schedule.

The Foucault statement is then literal: a path whose kicks sum to a nonzero residue does **not**
close — `closes` is false exactly when `precession ≠ 0`. That residue is the holonomy. The model's
falsifiable lemmas pin precisely this (drop the no-residue hypothesis and closure breaks).

## DEVICE COUPLING (load-bearing)
This effect is genuinely holonomy-shaped, so `claim_holds` is discharged in part by the device's own
holonomy theorems (`Measurement`, Episode 84), not just the finite ring:

* the **closed causal loop carries a charged holonomy** — `Measurement.holonomy_loop_is_charged`
  (the both-legs commutator residue reads `±1`: a nonzero precession, the "failure of closure");
* the **open path carries no holonomy** — `Measurement.holonomy_open_is_trivial`
  (a single-leg/open path returns trivially, residue `0`).

A sign/rename/`sorry` regression in those device theorems breaks *this* build. That is the coupling:
the device symbols sit inside `claim_holds`.

## NOT claimed
That this reproduces the physical Foucault pendulum, real general-relativistic parallel transport,
a real Berry phase, or the *magnitude* of any precession angle. `slots = 360` is a labelled ring
size, not a derived `2π sin(latitude)` rate. The connection's inconsistency (why the loop fails to
close at all) is *imported* from the device's commutator residue, not derived here. **Claim ceiling:**
a finite shadow of holonomy-on-a-loop, two of whose conjuncts are the device's own holonomy theorems.
-/

namespace Experiments.TheFoucaultEffect

/-- An orientation: a coarse direction slot on a finite ring of size `slots`. -/
structure Orientation where
  slot : Nat
deriving DecidableEq, Repr

/-- A transport schedule around a path: the ring size and the signed bin-kicks applied in order as
the refinement direction is carried around. -/
structure Schedule where
  slots : Nat
  kicks : List Int
deriving Repr

namespace Schedule

/-- The net holonomy residue of the schedule: the sum of the signed kicks reduced mod `slots`,
taken in `0..slots-1`. This is the **precession** — the bin-shift accumulated around the path. -/
def precession (s : Schedule) : Nat :=
  ((s.kicks.foldl (fun acc k => acc + k) 0) % (s.slots : Int)).toNat

/-- Carry an orientation around the schedule: apply the net residue to the starting slot (mod
`slots`). -/
def transport (s : Schedule) (start : Orientation) : Orientation :=
  { slot := (start.slot + s.precession) % s.slots }

/-- A path **closes** (in orientation) iff transport returns every starting slot to itself, i.e.
the holonomy residue vanishes. The Foucault statement: a closed causal *loop* need not close in
*orientation*. -/
def closes (s : Schedule) : Prop :=
  s.precession = 0

instance (s : Schedule) : Decidable s.closes := by
  unfold closes; exact inferInstance

end Schedule

-- ---------------------------------------------------------------------------
-- FALSIFIABLE lemmas. Each is ∀-quantified; drop the stated hypothesis and it breaks.
-- ---------------------------------------------------------------------------

/-- **The Foucault failure-of-closure, finitely.** A schedule with a NONZERO holonomy residue does
NOT close: some orientation fails to return to itself. Quantified over ALL schedules and starting
orientations. Drop `h : s.precession ≠ 0` and the conclusion is false (the zero-residue schedule
closes), so the hypothesis is load-bearing. -/
theorem nonzero_holonomy_fails_to_close
    (s : Schedule) (h : s.precession ≠ 0) : ¬ s.closes :=
  fun hc => h hc

/-- A path with vanishing holonomy residue DOES close: every starting orientation returns to itself.
Quantified over all schedules. (The converse face: closure is *exactly* a trivial holonomy.) -/
theorem zero_holonomy_closes
    (s : Schedule) (h : s.precession = 0) (start : Orientation) :
    (s.transport start).slot % s.slots = start.slot % s.slots := by
  unfold Schedule.transport
  simp only [h, Nat.add_zero, Nat.mod_mod]

-- ---------------------------------------------------------------------------
-- The canonical loop vs. open path on the standard 360-slot ring.
-- ---------------------------------------------------------------------------

/-- The standard ring size (a labelled constant — NOT a derived `2π sin φ` rate). -/
def standardSlots : Nat := 360

/-- A canonical CLOSED CAUSAL LOOP whose orientation transport leaves a nonzero residue: the
both-legs commutator does not cancel, so the carried direction precesses by one slot. -/
def canonicalLoop : Schedule := { slots := standardSlots, kicks := [1, 1, -1] }

/-- A canonical OPEN PATH whose kicks cancel: it carries no residue and closes trivially. -/
def openPath : Schedule := { slots := standardSlots, kicks := [1, -1] }

/-- The loop precesses (does not close): its holonomy residue is `1`. -/
theorem loop_precesses : canonicalLoop.precession = 1 := by decide

/-- The open path closes: its holonomy residue is `0`. -/
theorem open_closes : openPath.closes := by decide

theorem loop_does_not_close : ¬ canonicalLoop.closes :=
  nonzero_holonomy_fails_to_close canonicalLoop (by decide)

-- ---------------------------------------------------------------------------
-- THE CLAIM (content-bearing; two of four conjuncts are the device's holonomy theorems).
-- ---------------------------------------------------------------------------

/-- The claim, in honest halves:
* (finite shadow) the canonical loop precesses (`precession = 1` ⇒ does NOT close) while the
  open path closes (`precession = 0`) — proved here on the ring;
* (DEVICE: the loop is charged) the both-legs commutator residue around the gauge loop is
  nonzero — `Measurement.holonomy_loop_is_charged`;
* (DEVICE: the open path is trivial) a single-leg/open path carries zero holonomy —
  `Measurement.holonomy_open_is_trivial`.
The last two read the device's actual commutator-residue computation: a sign or rename regression
in `Measurement` fails this build. -/
def claimStatement : Prop :=
  canonicalLoop.precession = 1
    ∧ openPath.closes
    ∧ (Measurement.holonomy Measurement.tiltedPath
          (Measurement.CubicGaugeVariation.pairVariation Measurement.node1 Measurement.node2) = 1
        ∧ Measurement.holonomy Measurement.flatPath
            (Measurement.CubicGaugeVariation.pairVariation Measurement.node1 Measurement.node2) = -1)
    ∧ Measurement.holonomy Measurement.tiltedPath
        (Measurement.CubicGaugeVariation.pairVariation Measurement.node2 Measurement.node1) = 0

def claim : Experiments.Common.Claim :=
  { tag := Experiments.Common.ClaimTag.smoothShadowAnalogy
    statement := claimStatement }

theorem claim_holds : claim.statement :=
  ⟨loop_precesses, open_closes,
    Measurement.holonomy_loop_is_charged, Measurement.holonomy_open_is_trivial⟩

/-- The tag is an honest ceiling: a finite SHADOW of a continuous holonomy phenomenon
(parallel transport / precession), not the smooth theorem itself. -/
theorem ceiling :
    claim.tag = Experiments.Common.ClaimTag.smoothShadowAnalogy := rfl

-- ---------------------------------------------------------------------------
-- A computable run + a non-vacuous Experiment.claim, with a proved bridge.
-- ---------------------------------------------------------------------------

/-- The exported claim FIRES exactly when the path fails to close (a precession). Decidable, so it
computes. -/
def fails (s : Schedule) : Prop := ¬ s.closes

instance (s : Schedule) : Decidable (fails s) := by
  unfold fails; exact inferInstance

/-- The run actually computes — thanks to the `Decidable` instances above. -/
def run (s : Schedule) : Bool := decide (fails s)

def experiment : Experiments.Common.Experiment Schedule Bool :=
  { tag := claim.tag
    run := run
    claim := fun s => fails s }

theorem run_iff_claim (s : Schedule) :
    run s = true ↔ experiment.claim s := by
  show decide (fails s) = true ↔ fails s
  exact decide_eq_true_iff

-- ---------------------------------------------------------------------------
-- The standing record (gate evidence).
-- ---------------------------------------------------------------------------

/-- Bring a minimal device next to this experiment: it records whether the exported claim fires. -/
def deviceNear (setup : Schedule) : Bool :=
  decide (fails setup)

theorem deviceNear_detects_claim (setup : Schedule) :
    deviceNear setup = true ↔ experiment.claim setup := by
  show decide (fails setup) = true ↔ fails setup
  exact decide_eq_true_iff

def triangulation : Experiments.Common.Triangulation Schedule Bool :=
  { experiment := experiment
    device := deviceNear
    detects := deviceNear_detects_claim }

#eval run canonicalLoop                 -- expect: true   (loop precesses — does NOT close)
#eval run openPath                      -- expect: false  (open path closes — no holonomy)
#print axioms claim_holds
#eval decide (¬ openPath.closes)        -- expect: FALSE  (load-bearing: the lemma is non-vacuous)

end Experiments.TheFoucaultEffect
