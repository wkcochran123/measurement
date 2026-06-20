import Experiments.Common

/-!
# The Ising Effect — a finite ledger model of binary domain alignment

Source: `instrument/chapters/10.tex:1226` (`ph:ising-effect`).

## Physics (modelled finitely)
Each admissible refinement carries a **two-valued label** (`Spin.up`/`Spin.down`).  In isolation
the labels fluctuate freely.  Once refinements are **dense** (here: adjacent), the Master
Constraint forbids an **unobserved discontinuity** across the seam between two regions: adjacent
refinements must reconcile their binary states.  We model a region as a finite lattice of labelled
cells; its **seam** is the label on its shared edge.  Two adjacent regions are **admissible**
(reconcilable, no discontinuity) exactly when their seam labels agree — this is the harness's
`Boundary.compatible`.  An aligned (single-domain) region is the canonical reconciled witness; a
region that flips its label at the interior is the canonical domain *wall*, where admissibility
cost accumulates.

## NOT claimed
No spin physics: `Spin` is the minimal nontrivial label, not a magnetic moment.  No critical
temperature, no partition function, no probability measure, no thermodynamic limit, and no actual
energy — "admissibility cost" here is the boolean fact of a wall, not a Hamiltonian.  The threshold
is rendered only as the qualitative jump "free in isolation / forced when adjacent"; its
combinatorial *value* is not derived.  **Claim ceiling:** an `inadmissibilityNoGo` — a mismatched
seam is a blocked (inadmissible) two-region configuration — whose compatibility conjunct is the
harness's own `Boundary.compatible`.
-/

namespace Experiments.TheIsingEffect

/-- The minimal nontrivial label a causal ledger may assign to a refinement. -/
inductive Spin where
  | up
  | down
deriving DecidableEq, Repr

/-- A finite region of refinement cells, each carrying a binary label. -/
structure Region where
  cells : List Spin
deriving DecidableEq, Repr

namespace Region

/-- The seam a region presents to a neighbor: the label on its (last) shared edge. -/
def seam (r : Region) : Spin :=
  match r.cells.getLast? with
  | some s => s
  | none => Spin.up

/-- A region is a single coherent **domain** (aligned) when every cell carries the SAME label as
the seam — no interior wall.  Quantified over all cells, so adding a single flipped cell breaks it. -/
def aligned (r : Region) : Prop :=
  ∀ s, s ∈ r.cells → s = r.seam

instance (r : Region) : Decidable (r.aligned) := by
  unfold aligned; exact inferInstance

end Region

/-- The seam viewed as the boundary the harness restricts to. -/
def isingBoundary : Experiments.Common.Boundary Region Spin :=
  { restrict := Region.seam }

/-- THE RECONCILIATION RULE (harness `Boundary.compatible`): two adjacent regions are admissible —
no unobserved discontinuity — exactly when their seam labels agree.  This is the Master Constraint
at the interface. -/
def reconciles (left right : Region) : Prop :=
  isingBoundary.compatible left right

instance (left right : Region) : Decidable (reconciles left right) := by
  unfold reconciles Experiments.Common.Boundary.compatible; exact inferInstance

-- ---------------------------------------------------------------------------
-- FALSIFIABLE lemmas.  Each would break if its hypothesis were dropped.
-- ---------------------------------------------------------------------------

/-- NO-GO: regions presenting OPPOSITE seam labels can never reconcile.  This is the
inadmissibility core — a discontinuity at the interface is forbidden.  Drop the seam-disagreement
hypothesis and the conclusion is false (the next `#eval` exhibits a reconciling pair). -/
theorem mismatched_seam_not_reconciled
    (left right : Region) (h : left.seam ≠ right.seam) : ¬ reconciles left right :=
  fun hr => h hr

/-- An aligned region presents exactly its common label at the seam: alignment determines the
boundary every member cell shows.  Quantified over ALL cells; a single misaligned cell falsifies
the hypothesis. -/
theorem aligned_cells_match_seam
    (r : Region) (s : Spin) (hmem : s ∈ r.cells) (hal : r.aligned) : s = r.seam :=
  hal s hmem

/-- Two aligned regions that share the SAME common label reconcile: dense alignment propagates
across the seam into a single coherent domain.  Drop the seam-agreement hypothesis and it breaks. -/
theorem aligned_same_label_reconciles
    (left right : Region) (h : left.seam = right.seam) : reconciles left right :=
  h

-- ---------------------------------------------------------------------------
-- Canonical configurations: one coherent domain, one domain wall.
-- ---------------------------------------------------------------------------

/-- A coherent up-domain: three aligned `up` cells. -/
def upDomain : Region := { cells := [Spin.up, Spin.up, Spin.up] }

/-- A coherent down-domain (same `up`-seam neighbor is incompatible with it). -/
def downDomain : Region := { cells := [Spin.down, Spin.down, Spin.down] }

/-- A domain WALL: the label flips at the interior, so the region is NOT aligned. -/
def wall : Region := { cells := [Spin.up, Spin.up, Spin.down] }

/-- The up-domain is genuinely aligned (a coherent single domain). -/
theorem upDomain_aligned : upDomain.aligned := by decide

/-- The wall is genuinely NOT aligned — admissibility cost accumulates at the interior flip. -/
theorem wall_not_aligned : ¬ wall.aligned := by decide

/-- Two up-domains reconcile across their seam (one extended coherent domain). -/
theorem upDomain_self_reconciles : reconciles upDomain upDomain := by decide

/-- An up-domain and a down-domain do NOT reconcile — the seam carries a forbidden discontinuity. -/
theorem up_down_not_reconciled : ¬ reconciles upDomain downDomain := by decide

-- ---------------------------------------------------------------------------
-- THE CLAIM (content-bearing; the compatibility conjunct IS the harness theorem).
-- ---------------------------------------------------------------------------

/-- The claim, in honest parts:
* (domain) `upDomain` is a single coherent aligned domain;
* (wall) `wall` is genuinely not aligned — a domain wall exists;
* (reconciliation) two aligned up-domains reconcile across the seam
  (the harness's `Boundary.compatible` — the LOAD-BEARING coupling); and
* (no-go) an up-domain and a down-domain do NOT reconcile — a mismatched seam is inadmissible.
Breaking `isingBoundary.compatible` (rename `restrict`/`compatible`, or regress `Region.seam`)
breaks the third conjunct and so this build. -/
def claimStatement : Prop :=
  upDomain.aligned ∧
    ¬ wall.aligned ∧
    isingBoundary.compatible upDomain upDomain ∧
    ¬ isingBoundary.compatible upDomain downDomain

def claim : Experiments.Common.Claim :=
  { tag := Experiments.Common.ClaimTag.inadmissibilityNoGo
    statement := claimStatement }

theorem claim_holds : claim.statement :=
  ⟨upDomain_aligned, wall_not_aligned, upDomain_self_reconciles, up_down_not_reconciled⟩

/-- The tag is an honest ceiling: a no-go on inadmissible (mismatched-seam) configurations. -/
theorem ceiling : claim.tag = Experiments.Common.ClaimTag.inadmissibilityNoGo := rfl

-- ---------------------------------------------------------------------------
-- A computable run + a NON-vacuous Experiment.claim, with a proved bridge.
-- ---------------------------------------------------------------------------

structure Setup where
  left : Region
  right : Region
deriving Repr

/-- The run actually computes — thanks to the `Decidable` instances above. -/
def run (s : Setup) : Bool := decide (reconciles s.left s.right)

/-- The exported claim is a genuine function of the setup; this bridge pins it to `run`, so the
claim body cannot be silently swapped for `fun _ => True`. -/
def experiment : Experiments.Common.Experiment Setup Bool :=
  { tag := claim.tag
    run := run
    claim := fun s => reconciles s.left s.right }

theorem run_iff_claim (s : Setup) :
    run s = true ↔ experiment.claim s := by
  simp only [run, experiment, decide_eq_true_iff]

def canonicalSetup : Setup := { left := upDomain, right := upDomain }

#eval run canonicalSetup                                  -- expect: true  (one coherent domain)
#eval run { canonicalSetup with right := downDomain }     -- expect: false (forbidden discontinuity)

/-- Bring a minimal device next to this experiment: it records whether the exported claim fires. -/
def deviceNear (setup : Setup) : Bool :=
  run setup

theorem deviceNear_detects_claim (setup : Setup) :
    deviceNear setup = true ↔ experiment.claim setup := by
  simp only [deviceNear, run, experiment, decide_eq_true_iff]

def triangulation : Experiments.Common.Triangulation Setup Bool :=
  { experiment := experiment
    device := deviceNear
    detects := deviceNear_detects_claim }

-- GATE EVIDENCE -------------------------------------------------------------
#print axioms claim_holds
-- Load-bearing check: evaluate the falsifiable predicate at a config where it is FALSE.
-- `reconciles upDomain downDomain` is FALSE (opposite seams) -> prints `false`.
#eval decide (reconciles upDomain downDomain)             -- expect: false

end Experiments.TheIsingEffect
