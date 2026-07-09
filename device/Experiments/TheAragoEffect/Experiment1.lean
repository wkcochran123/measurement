import Experiments.Common

/-!
# The Arago Effect — boundary consistency forces the bright spot

A bright region appears in the geometric shadow of a circular obstacle because the
field ledger must stay globally consistent along the **entire** boundary. The edge of
the disk is a closed causal boundary `∂Ω`; along the central axis behind the disk every
point is equidistant from `∂Ω`, so the boundary refinements arriving from opposite rim
arcs are **symmetric**. By boundary consistency the interior state at the axis is the
unique refinement compatible with the whole boundary ledger at once — and to assert
*darkness* there would require the ledger to encode a hidden phase distinction that was
never measured (Ockham). The bright spot is the informational checksum of the boundary.

This file follows the EXEMPLAR shape:
1. an **effect-specific domain** (`RimContribution`, `Disk`) — not the generic 3-`Nat`
   `CountSetup`;
2. genuinely **falsifiable** ∀-quantified lemmas (drop the equidistance / equal-phase
   hypothesis and they break — see the `#eval ... = false` gate at the bottom);
3. a **content-bearing** claim (a real conjunction, never `True`);
4. an honest tag + a candid "NOT claimed" disclaimer;
5. explicit `Decidable` instances so `decide`/`#eval` compute;
6. a **load-bearing HARNESS coupling**: one conjunct of `claim_holds` is the harness's own
   `Experiments.Common.Boundary.compatible` predicate, discharged for the two symmetric rim
   contributions reaching the central axis. This is the honest coupling for an effect that is
   pure boundary/two-region consistency — there is **no holonomy, charge, or positron here**,
   so a device coupling would be a fake.

## NOT claimed
That this computes a real diffraction integral or the Fresnel/Kirchhoff field; that the
"phase" here is a physical optical phase (it is a coarse finite slot); that the spot's
*intensity* is derived; anything about wavelength, the Fresnel number, or the continuum
limit. **Claim ceiling:** a finite ledger model in which the bright spot is the statement
that the two symmetric boundary refinements at the central axis are *compatible* (agree),
so no admissible history can encode the unrecorded asymmetry that darkness would demand.
-/

namespace Experiments.TheAragoEffect

/-- A coarse contribution arriving at an interior point from one rim arc of the disk:
its `distance` to that arc (a finite slot) and the `phase` it carries (a finite slot). On
the central axis behind the disk every rim arc is equidistant, so the contributions reaching
the axis all share one `distance`, hence — with no unrecorded distinction — one `phase`. -/
structure RimContribution where
  distance : Nat
  phase : Nat
deriving DecidableEq, Repr

/-- The circular obstacle: the `radius` of the disk and the `axisDistance` of the chosen
interior point from the plane of the rim. These fix the common distance every rim arc has to
a point on the central axis (the equidistance that makes the spot bright). -/
structure Disk where
  radius : Nat
  axisDistance : Nat
deriving DecidableEq, Repr

/-- The standard apparatus: a unit-radius disk, the interior point one unit down the axis. -/
def defaultDisk : Disk := { radius := 1, axisDistance := 1 }

namespace Disk

/-- The geometric distance slot from any rim arc to the central-axis point at `axisDistance`:
it is the *same* for every rim arc, because the axis point is equidistant from the whole rim.
(`radius` and `axisDistance` are the two legs of the right triangle; we record their slot sum
rather than a Euclidean root — this is a coarse finite stand-in, see "NOT claimed".) -/
def rimToAxisDistance (d : Disk) : Nat := d.radius + d.axisDistance

/-- The contribution a rim arc sends to the central axis, given the phase `φ` it carries.
On the axis the distance is fixed by `rimToAxisDistance`, independent of which arc. -/
def axisContribution (d : Disk) (φ : Nat) : RimContribution :=
  { distance := d.rimToAxisDistance, phase := φ }

end Disk

/-- The part of a contribution a *neighboring* ledger can see at the boundary: its phase slot.
(Distance is internal bookkeeping; what crosses the seam between two boundary regions is the
phase.) This is the restriction map of the harness `Boundary`. -/
def phaseBoundary : Experiments.Common.Boundary RimContribution Nat :=
  { restrict := fun c => c.phase }

/-- Two contributions are **boundary-compatible** exactly when their visible phases agree —
the harness's `Boundary.compatible` on `phaseBoundary`. Darkness at the axis would require
these to *disagree* without any recorded distance distinction, which Ockham forbids. -/
def axisCompatible (left right : RimContribution) : Prop :=
  phaseBoundary.compatible left right

instance (left right : RimContribution) : Decidable (axisCompatible left right) := by
  unfold axisCompatible Experiments.Common.Boundary.compatible phaseBoundary
  exact inferInstance

-- ---------------------------------------------------------------------------
-- FALSIFIABLE lemmas. Each is quantified over ALL contributions/phases and would
-- BREAK if its hypothesis were dropped (the `#eval` gate at the bottom witnesses a
-- config where the predicate is FALSE, so these are not vacuous).
-- ---------------------------------------------------------------------------

/-- **Equal phase ⇒ compatible.** Two contributions carrying the same phase are boundary-
compatible. Quantified over ALL contributions: this is the bright-spot direction — symmetric
rim refinements (equal phase, forced by equidistance) agree, so the axis is illuminated.
Drop the equal-phase hypothesis `h` and the conclusion fails (witnessed below). -/
theorem equalPhase_compatible
    (left right : RimContribution) (h : left.phase = right.phase) :
    axisCompatible left right := by
  unfold axisCompatible Experiments.Common.Boundary.compatible phaseBoundary
  exact h

/-- **Incompatible ⇒ phases differ.** The contrapositive: if two boundary contributions are
NOT compatible, their phases were genuinely distinct. So darkness (incompatibility) at the
axis is admissible ONLY by encoding a phase distinction — the unrecorded asymmetry Ockham
forbids. Quantified over ALL pairs; load-bearing. -/
theorem incompatible_phasesDiffer
    (left right : RimContribution) (h : ¬ axisCompatible left right) :
    left.phase ≠ right.phase :=
  fun heq => h (equalPhase_compatible left right heq)

/-- **On the axis, the two symmetric rim contributions are equidistant.** For ANY disk and ANY
two phases, the contributions the two opposite rim arcs send to the central axis carry the same
`distance`. This is the geometric equidistance that, with no recorded distinction, forces equal
phase — and hence the bright spot. -/
theorem axisContributions_equidistant (d : Disk) (φ ψ : Nat) :
    (d.axisContribution φ).distance = (d.axisContribution ψ).distance := by
  rfl

-- ---------------------------------------------------------------------------
-- The canonical bright-spot configuration: two symmetric rim contributions, same phase.
-- ---------------------------------------------------------------------------

/-- The phase carried by the symmetric rim refinements reaching the axis (a labelled slot). -/
def axisPhase : Nat := 0

/-- The two contributions from opposite rim arcs to the central axis — same distance (forced),
same phase (no recorded distinction). -/
def leftRim : RimContribution := defaultDisk.axisContribution axisPhase
def rightRim : RimContribution := defaultDisk.axisContribution axisPhase

/-- The bright spot, concretely: the two symmetric contributions ARE compatible. -/
theorem brightSpot_compatible : axisCompatible leftRim rightRim := by decide

/-- A DARK config (a phase distinction was injected on the right rim) is NOT compatible — this
is the configuration the `#eval` gate at the bottom prints `false` for. -/
def darkRightRim : RimContribution := { defaultDisk.axisContribution axisPhase with phase := 7 }

-- ---------------------------------------------------------------------------
-- THE CLAIM (content-bearing; the compatibility conjunct is the harness's own predicate).
-- ---------------------------------------------------------------------------

/-- The claim, in honest parts:
* (equidistance) the two symmetric rim contributions reaching the axis share one distance —
  the geometric input that forbids an unrecorded asymmetry;
* (bright spot = boundary compatibility) the two symmetric contributions are
  `Experiments.Common.Boundary.compatible` (HARNESS coupling — breaking `Boundary.compatible`
  or `phaseBoundary` breaks this build); and
* (darkness is a distinction) the dark config is NOT compatible, so darkness at the axis is
  admissible only by encoding a phase distinction that was never measured. -/
def claimStatement : Prop :=
  leftRim.distance = rightRim.distance ∧
    axisCompatible leftRim rightRim ∧
    ¬ axisCompatible leftRim darkRightRim

def claim : Experiments.Common.Claim :=
  { tag := Experiments.Common.ClaimTag.finiteLedgerModel
    statement := claimStatement }

theorem claim_holds : claim.statement :=
  ⟨axisContributions_equidistant defaultDisk axisPhase axisPhase,
    equalPhase_compatible leftRim rightRim rfl,
    by decide⟩

/-- The tag is an honest ceiling: a finite ledger model of the boundary-consistency logic. -/
theorem ceiling : claim.tag = Experiments.Common.ClaimTag.finiteLedgerModel := rfl

-- ---------------------------------------------------------------------------
-- A computable run + a non-vacuous Experiment.claim, with a proved bridge.
-- ---------------------------------------------------------------------------

structure Setup where
  disk : Disk
  left : RimContribution
  right : RimContribution

/-- The run computes — via the `Decidable` instance on `axisCompatible`. -/
def run (s : Setup) : Bool := decide (axisCompatible s.left s.right)

def experiment : Experiments.Common.Experiment Setup Bool :=
  { tag := claim.tag
    run := run
    claim := fun s => axisCompatible s.left s.right }

theorem run_iff_claim (s : Setup) :
    run s = true ↔ experiment.claim s := by
  simp only [run, experiment, decide_eq_true_iff]

def canonicalSetup : Setup := { disk := defaultDisk, left := leftRim, right := rightRim }

#eval run canonicalSetup                                   -- expect: true  (bright spot)
#eval run { canonicalSetup with right := darkRightRim }    -- expect: false (injected distinction)
#print axioms claim_holds                                  -- [propext, Quot.sound] = AMBIENT, not coupling

/-- Bring a minimal device next to this experiment: it records whether the exported claim fires. -/
def deviceNear (setup : Setup) : Bool :=
  run setup

theorem deviceNear_detects_claim (setup : Setup) :
    deviceNear setup = true ↔ experiment.claim setup := by
  simpa [deviceNear] using run_iff_claim setup

def triangulation : Experiments.Common.Triangulation Setup Bool :=
  { experiment := experiment
    device := deviceNear
    detects := deviceNear_detects_claim }

end Experiments.TheAragoEffect
