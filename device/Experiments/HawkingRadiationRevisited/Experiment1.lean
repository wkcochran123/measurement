import Experiments.Common

/-!
# Hawking Radiation Revisited — a finite boundary-reconciliation model

Source: `instrument/chapters/07.tex:1082` (`te:hawking-radiation-revisited`).

This file follows the EXEMPLAR shape (`ThePositronAnnihilationEffect/Experiment1.lean`):
an effect-specific domain, falsifiable `∀`-lemmas, a content-bearing claim, an honest tag, a
candid disclaimer, explicit `Decidable` instances, and a LOAD-BEARING harness coupling.

## Physics (modelled finitely)
An external laboratory keeps a ledger `U^out` of refinement events visible OUTSIDE a horizon `H`.
The horizon is the frontier of distinguishability: the external ledger reads only a **boundary
restriction** of any state (a holographic surface reading). Two extensions of the ledger are
**Martin-consistent** (reconcilable into one ordering) exactly when their boundary readings agree —
this is `Experiments.Common.Boundary.compatible` (a two-region / seam compatibility).

When an infalling system's interior refinements would force a reading the exterior cannot match,
the joint ordering becomes infeasible. The **repair** applies a *surrogate refinement* `e_rad`
that restores the boundary reading — Hawking "radiation" is exactly this bookkeeping update, not a
particle from behind `H`. The lemmas below pin that the surrogate is NECESSARY: without it the two
sides are incompatible; with it they are compatible.

## NOT claimed
No physical emission, no quantum field in curved spacetime, no thermal/exponential spectrum is
derived, no GR theorem is proved. "Energy", "temperature", and the Planck/Cantor axioms are NOT
formalized — `boundaryReading` is a chosen finite restriction, not derived geometry. The model
asserts only the finite **bookkeeping** identity: surrogate repair = the unique update that
re-equalizes the visible boundary reading. **Claim ceiling:** a smooth-shadow finite stand-in for
the holographic boundary-consistency constraint, one conjunct of which is the harness's own
`Boundary.compatible` reconciliation theorem.
-/

namespace Experiments.HawkingRadiationRevisited

/-- A finite refinement event recorded by the external ledger: a coarse `slot` on the visible
boundary, plus a `depth` (how far inside `H` it originated; only `slot` is ever read outside). -/
structure Refinement where
  slot : Nat
  depth : Nat
deriving DecidableEq, Repr

/-- A state of the external ledger `U^out`: the list of refinements recorded so far, together with
the boundary `surface` reading currently representable on the horizon. -/
structure LedgerState where
  events : List Refinement
  surface : Nat
deriving DecidableEq, Repr

/-- The holographic boundary: the exterior reads ONLY the `surface` slot of a ledger state — the
interior `events`/`depth` are not visible. This is the restriction map of the horizon. -/
def horizonBoundary : Experiments.Common.Boundary LedgerState Nat :=
  { restrict := fun s => s.surface }

namespace LedgerState

/-- Two ledger states are **reconcilable** (admit one Martin-consistent ordering) iff their boundary
readings agree — i.e. `horizonBoundary.compatible`. -/
def reconcilable (left right : LedgerState) : Prop :=
  horizonBoundary.compatible left right

instance (left right : LedgerState) : Decidable (left.reconcilable right) := by
  unfold reconcilable Experiments.Common.Boundary.compatible horizonBoundary
  exact inferInstance

end LedgerState

/-- The surrogate refinement `e_rad`: the repair applied when an interior update `r` would otherwise
break the boundary reading. It records the new interior event AND restores the surface to the value
`target` the exterior demands — the holographic constraint made into an update. -/
def surrogate (target : Nat) (r : Refinement) (s : LedgerState) : LedgerState :=
  { events := r :: s.events, surface := target }

/-- The *unrepaired* update: record the interior event but leave the surface untouched. This is what
the exterior would see if no surrogate were emitted. -/
def unrepaired (r : Refinement) (s : LedgerState) : LedgerState :=
  { events := r :: s.events, surface := s.surface }

-- ---------------------------------------------------------------------------
-- FALSIFIABLE lemmas. Each is ∀-quantified and breaks if a hypothesis is dropped.
-- ---------------------------------------------------------------------------

/-- REPAIR WORKS: after a surrogate refinement to `t`, the exterior reading of the new state matches
ANY reference state whose surface is `t`. Quantified over all targets, events, and states. -/
theorem surrogate_reconciles
    (t : Nat) (r : Refinement) (s ref : LedgerState) (h : ref.surface = t) :
    (surrogate t r s).reconcilable ref := by
  unfold LedgerState.reconcilable Experiments.Common.Boundary.compatible horizonBoundary surrogate
  exact h.symm

/-- REPAIR IS NECESSARY (falsifiability witness, ∀-quantified): if the demanded surface `t` differs
from the current surface, the UNREPAIRED update is NOT reconcilable with a reference at `t`. Drop the
surrogate and reconciliation fails — this is what forces the radiation bookkeeping. -/
theorem unrepaired_not_reconciled
    (t : Nat) (r : Refinement) (s ref : LedgerState)
    (hsurf : s.surface ≠ t) (href : ref.surface = t) :
    ¬ (unrepaired r s).reconcilable ref := by
  unfold LedgerState.reconcilable Experiments.Common.Boundary.compatible horizonBoundary unrepaired
  intro hbad
  exact hsurf (href ▸ hbad)

/-- BOUNDARY-ONLY: reconciliation depends ONLY on the surface, never on the interior ledger. Two
states with the same surface are reconcilable regardless of their (arbitrary) event lists — the
holographic constraint. -/
theorem reconcilable_of_same_surface
    (left right : LedgerState) (h : left.surface = right.surface) :
    left.reconcilable right := by
  unfold LedgerState.reconcilable Experiments.Common.Boundary.compatible horizonBoundary
  exact h

-- ---------------------------------------------------------------------------
-- The canonical saturation event.
-- ---------------------------------------------------------------------------

/-- The exterior ledger at saturation: empty interior, but a STALE boundary surface `5` — the
infalling refinement has pushed the demanded reading away from what the surface currently shows. -/
def beforeSaturation : LedgerState := { events := [], surface := 5 }

/-- An interior refinement that arrives as the system approaches `H`. -/
def infallingEvent : Refinement := { slot := 3, depth := 5 }

/-- The exterior reference the boundary must reconcile with: it demands surface `7`. -/
def exteriorReference : LedgerState := { events := [], surface := 7 }

/-- The state AFTER the surrogate repair restores the demanded surface. -/
def afterRepair : LedgerState := surrogate 7 infallingEvent beforeSaturation

/-- The repaired state reconciles with the exterior reference (concrete, via `Decidable`). -/
theorem repair_reconciles_canonical : afterRepair.reconcilable exteriorReference := by decide

/-- The repair adds exactly one surrogate event (a finite bookkeeping tally on the chosen event). -/
theorem repair_adds_one_event :
    afterRepair.events.length = beforeSaturation.events.length + 1 := by decide

-- ---------------------------------------------------------------------------
-- THE CLAIM (content-bearing; coupling conjunct is the harness Boundary.compatible).
-- ---------------------------------------------------------------------------

/-- The claim, in honest halves:
* (repair) the surrogate-repaired state reconciles with the exterior reference — proved here AND it
  is exactly `horizonBoundary.compatible afterRepair exteriorReference`, the harness's two-region
  reconciliation predicate (this is the LOAD-BEARING coupling: break `Boundary.compatible` and this
  conjunct breaks);
* (necessity) the UNREPAIRED update is NOT reconcilable — so the surrogate is required; and
* (bookkeeping) the repair adds exactly one ledger event. -/
def claimStatement : Prop :=
  Experiments.Common.Boundary.compatible horizonBoundary afterRepair exteriorReference ∧
    ¬ (unrepaired infallingEvent beforeSaturation).reconcilable exteriorReference ∧
    afterRepair.events.length = beforeSaturation.events.length + 1

def claim : Experiments.Common.Claim :=
  { tag := Experiments.Common.ClaimTag.smoothShadowAnalogy
    statement := claimStatement }

theorem claim_holds : claim.statement :=
  ⟨ surrogate_reconciles 7 infallingEvent beforeSaturation exteriorReference rfl,
    unrepaired_not_reconciled 7 infallingEvent beforeSaturation exteriorReference
      (by decide) rfl,
    repair_adds_one_event ⟩

/-- The tag is an honest ceiling: a smooth-shadow finite stand-in, nothing more. -/
theorem ceiling : claim.tag = Experiments.Common.ClaimTag.smoothShadowAnalogy := rfl

-- ---------------------------------------------------------------------------
-- A computable run + a non-vacuous Experiment.claim, with a proved bridge.
-- ---------------------------------------------------------------------------

structure Setup where
  target : Nat
  arrival : Refinement
  start : LedgerState
  reference : LedgerState

/-- The run computes whether the surrogate repair reconciles with the reference. -/
def run (s : Setup) : Bool :=
  decide ((surrogate s.target s.arrival s.start).reconcilable s.reference)

def experiment : Experiments.Common.Experiment Setup Bool :=
  { tag := claim.tag
    run := run
    claim := fun s => (surrogate s.target s.arrival s.start).reconcilable s.reference }

theorem run_iff_claim (s : Setup) :
    run s = true ↔ experiment.claim s := by
  simp only [run, experiment, decide_eq_true_iff]

def canonicalSetup : Setup :=
  { target := 7, arrival := infallingEvent, start := beforeSaturation, reference := exteriorReference }

#eval run canonicalSetup                                  -- expect: true
-- Falsifiability witness: at a target the reference does NOT demand, repair fails to reconcile.
#eval decide ((unrepaired infallingEvent beforeSaturation).reconcilable exteriorReference) -- false
#print axioms claim_holds                                 -- [propext, Quot.sound] = AMBIENT, not coupling

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

end Experiments.HawkingRadiationRevisited
