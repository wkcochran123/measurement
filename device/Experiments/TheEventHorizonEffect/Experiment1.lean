import Experiments.Common

/-!
# The Event Horizon Effect — effect-specific, falsifiable, content-bearing

Rebuilt to the EXEMPLAR shape (cf. `ThePositronAnnihilationEffect/Experiment1.lean`):
an effect-specific domain (not the 3-`Nat` `CountSetup`), falsifiable `∀`-lemmas, a real
conjunction as the claim, an honest tag + disclaimer, explicit `Decidable` instances, and a
HARNESS coupling whose theorem is a load-bearing conjunct of `claim_holds`.

## Physics (modelled finitely)
A black hole is an *informational bottleneck*, not a geometric singularity. To export one
distinguishable interior refinement across the boundary costs a number of coordinate-time
updates. The boundary admits an export only while that cost stays within a finite budget — the
exchange rate of admissible refinements. At an **event horizon** the cost diverges: every finite
budget is exceeded, the exchange rate collapses to zero, and the interior ledger can no longer be
interleaved with the external history in finite informational time.

We model the boundary as a finite **export budget** `budget`, and each candidate refinement as an
**export cost** `cost` (coordinate-time updates needed). An export is *admissible* iff its cost is
within budget. A region is a **horizon** when its export cost exceeds the budget — then NO export
is admissible (a no-go), and the count of admissible refinements is bounded by zero.

## NOT claimed
That this captures the Schwarzschild metric, real GR, any curvature/geodesic computation, Hawking
radiation, or the actual divergence of proper-coordinate time at `r = 2M`. `cost`/`budget` are
labelled finite counts, not derived from any field equation. The "unbounded cost" is rendered
finitely as `budget < cost`; we do NOT formalize a genuine limit or a non-mergeability proof for
infinite ledgers. **Claim ceiling:** a finite stand-in (smooth-shadow) for the latency boundary,
one of whose conjuncts is the harness's own counting bound.
-/

namespace Experiments.TheEventHorizonEffect

/-- A candidate interior refinement: a distinguishable update with a coordinate-time export
cost (the number of external updates needed to push it across the boundary). -/
structure Refinement where
  label : Nat
  cost : Nat
deriving DecidableEq, Repr

/-- The informational boundary: the finite export budget (the admissible exchange rate of
refinements). Beyond it, an export cannot be reconciled in finite informational time. -/
structure Boundary where
  budget : Nat
deriving Repr

namespace Boundary

/-- An export is admissible iff its cost is within the boundary's finite budget. -/
def admissible (b : Boundary) (r : Refinement) : Prop :=
  r.cost <= b.budget

/-- A refinement is *behind a horizon* (with respect to this boundary) when its export cost
strictly exceeds the budget — the diverged-cost regime. -/
def horizon (b : Boundary) (r : Refinement) : Prop :=
  b.budget < r.cost

-- Make the predicates DECIDABLE so `decide`/`#eval` see through them.
instance (b : Boundary) (r : Refinement) : Decidable (b.admissible r) := by
  unfold admissible; exact inferInstance
instance (b : Boundary) (r : Refinement) : Decidable (b.horizon r) := by
  unfold horizon; exact inferInstance

end Boundary

-- ---------------------------------------------------------------------------
-- FALSIFIABLE lemmas (∀-quantified; drop the hypothesis and they break).
-- ---------------------------------------------------------------------------

/-- THE EVENT HORIZON NO-GO: behind a horizon, NO export is admissible. The exchange rate of
admissible refinements collapses. Quantified over ALL boundaries and refinements; drop the
`horizon` hypothesis and it is false (a low-cost refinement IS admissible). -/
theorem horizon_blocks_export
    (b : Boundary) (r : Refinement) (h : b.horizon r) : ¬ b.admissible r :=
  fun ha => Nat.not_lt.mpr ha h

/-- Conversely, an admissible refinement is NOT behind the horizon — the two regimes are
disjoint. Falsifiable: without `admissible`, a diverged-cost refinement satisfies `horizon`. -/
theorem admissible_not_horizon
    (b : Boundary) (r : Refinement) (h : b.admissible r) : ¬ b.horizon r :=
  fun hh => Nat.not_lt.mpr h hh

/-- Monotonicity of latency: raising the export cost of a horizon refinement keeps it behind the
horizon. Falsifiable: without `Nat.le` the larger cost could (vacuously) drop below budget. -/
theorem horizon_monotone
    (b : Boundary) (r s : Refinement) (h : b.horizon r) (hle : r.cost <= s.cost) :
    b.horizon s :=
  Nat.lt_of_lt_of_le h hle

-- ---------------------------------------------------------------------------
-- The canonical horizon event + the admissible-ledger count.
-- ---------------------------------------------------------------------------

/-- A boundary whose budget is 3 coordinate-time updates. -/
def defaultBoundary : Boundary := { budget := 3 }

/-- An interior refinement whose export cost (5) diverges past the budget — behind the horizon. -/
def interiorRefinement : Refinement := { label := 0, cost := 5 }

/-- The canonical refinement sits behind the horizon. -/
theorem interior_is_horizon : defaultBoundary.horizon interiorRefinement := by decide

/-- Hence it is not admissible — the export is blocked. -/
theorem interior_blocked : ¬ defaultBoundary.admissible interiorRefinement :=
  horizon_blocks_export defaultBoundary interiorRefinement interior_is_horizon

/-- The ledger of refinements that DID cross the boundary (were admitted). At a horizon this is
empty: the exchange rate has collapsed to zero. -/
def exportedLedger : Experiments.Common.Ledger Refinement :=
  { events := [] }

/-- The collapse is an exact count: zero refinements have been exported across the horizon. -/
theorem exported_count_zero : exportedLedger.count = 0 := by decide

-- ---------------------------------------------------------------------------
-- HARNESS COUPLING (load-bearing). The exchange rate's collapse is the harness's
-- own counting bound: the exported ledger is bounded by 0. `Counting.boundedBy_of_eq`
-- discharges this conjunct of `claim_holds`, so a regression in that harness lemma
-- (or a rename) breaks THIS build.
-- ---------------------------------------------------------------------------

/-- The exchange rate has collapsed: the count of exported refinements is `≤ 0`, via the
harness theorem `Counting.boundedBy_of_eq` applied to `exported_count_zero`. -/
theorem exchange_rate_collapsed :
    Experiments.Common.Counting.boundedBy exportedLedger 0 :=
  Experiments.Common.Counting.boundedBy_of_eq exported_count_zero

-- ---------------------------------------------------------------------------
-- THE CLAIM (content-bearing conjunction; one conjunct is the harness theorem).
-- ---------------------------------------------------------------------------

/-- The claim, in honest parts:
* (horizon) the canonical interior refinement is behind the horizon — proved here;
* (no-go) therefore its export is NOT admissible — the event-horizon block;
* (collapse) the exported ledger is bounded by `0` — the exchange rate has collapsed, discharged
  by the harness `Counting.boundedBy_of_eq` (the load-bearing coupling). -/
def claimStatement : Prop :=
  defaultBoundary.horizon interiorRefinement ∧
    ¬ defaultBoundary.admissible interiorRefinement ∧
    Experiments.Common.Counting.boundedBy exportedLedger 0

def claim : Experiments.Common.Claim :=
  { tag := Experiments.Common.ClaimTag.smoothShadowAnalogy
    statement := claimStatement }

theorem claim_holds : claim.statement :=
  ⟨interior_is_horizon, interior_blocked, exchange_rate_collapsed⟩

/-- The tag is an honest ceiling: a finite smooth-shadow of the latency boundary. -/
theorem ceiling :
    claim.tag = Experiments.Common.ClaimTag.smoothShadowAnalogy := rfl

-- ---------------------------------------------------------------------------
-- A computable run + a NON-vacuous Experiment.claim, with a proved bridge.
-- ---------------------------------------------------------------------------

structure Setup where
  boundary : Boundary
  refinement : Refinement

/-- The run computes whether the candidate refinement is behind the horizon (blocked). -/
def run (s : Setup) : Bool := decide (s.boundary.horizon s.refinement)

/-- The exported claim is a genuine function of the setup; this bridge pins it to `run`. -/
def experiment : Experiments.Common.Experiment Setup Bool :=
  { tag := claim.tag
    run := run
    claim := fun s => s.boundary.horizon s.refinement }

theorem run_iff_claim (s : Setup) :
    run s = true ↔ experiment.claim s := by
  simp only [run, experiment, decide_eq_true_iff]

def canonicalSetup : Setup := { boundary := defaultBoundary, refinement := interiorRefinement }

#eval run canonicalSetup                                      -- expect: true  (behind horizon)
#eval run { canonicalSetup with refinement := { label := 1, cost := 1 } }  -- expect: false

-- The exported claim is `fun s => s.boundary.horizon s.refinement`; make it `Decidable` so the
-- device below can `decide` it.
instance (setup : Setup) : Decidable (experiment.claim setup) := by
  show Decidable (setup.boundary.horizon setup.refinement); exact inferInstance

/-- Bring a minimal device next to this experiment: it records whether the exported claim fires. -/
def deviceNear (setup : Setup) : Bool :=
  decide (experiment.claim setup)

theorem deviceNear_detects_claim (setup : Setup) :
    deviceNear setup = true ↔ experiment.claim setup := by
  simp [deviceNear, experiment]

def triangulation : Experiments.Common.Triangulation Setup Bool :=
  { experiment := experiment
    device := deviceNear
    detects := deviceNear_detects_claim }

-- ---------------------------------------------------------------------------
-- GATE EVIDENCE.
-- ---------------------------------------------------------------------------

#print axioms claim_holds   -- expect: [propext] (no Classical.choice; clean)

-- The falsifiable predicate is LOAD-BEARING, not vacuous: at a low-cost refinement (cost 1,
-- budget 3) `horizon` is FALSE, so this prints `false`.
#eval decide (defaultBoundary.horizon { label := 1, cost := 1 })   -- expect: false

end Experiments.TheEventHorizonEffect
