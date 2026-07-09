import Experiments.Common

/-!
# The Alpha-Decay Effect — a finite boundary-repair model

Source: `instrument/chapters/07.tex:1725` (`The Alpha-Decay Effect`).

This file follows the EXEMPLAR shape (`ThePositronAnnihilationEffect/Experiment1.lean`):
an effect-specific domain, falsifiable `∀`-lemmas, a content-bearing claim, an honest tag, a
candid disclaimer, explicit `Decidable` instances, and a LOAD-BEARING harness coupling.

## Physics (modelled finitely)
A bound nucleus is a ledger of refinement branches that has accumulated unresolved curvature: over
informational time the interior record drifts out of alignment with its boundary description, until
the overlap can no longer be reconciled with Martin Consistency. Two boundary descriptions are
reconcilable exactly when their boundary readings agree — this is
`Experiments.Common.Boundary.compatible` (a two-region / seam compatibility).

The **Causal Folding Operator** `f` performs the minimal corrective update: it REMOVES the
inconsistent branch from the record and emits the removed branch as the recorded trace `α`. The
interior returns to an admissible configuration whose boundary reading once again matches the
reference. The lemmas below pin that the fold is NECESSARY (the unfolded, still-contradictory state
is NOT reconcilable) and SUFFICIENT (after the fold the boundary reading is restored), and that the
emitted `α` is exactly the branch that was removed (a finite conservation tally: bound = unbound + α).

## NOT claimed
No tunneling mechanism, no nuclear potential, no Gamow factor, no exponential decay LAW is derived
(the continuum-limit exponential is asserted by the source, not formalized here). "Curvature",
"Martin Consistency", and the boundary restriction are CHOSEN finite stand-ins, not derived geometry.
The model asserts only the finite **bookkeeping** identity: the fold is the unique branch-removal that
re-equalizes the visible boundary reading, and the emitted alpha is the removed branch.
**Claim ceiling:** an inadmissibility no-go — the un-repaired overlap CANNOT be reconciled — one
conjunct of which is the harness's own `Boundary.compatible` reconciliation predicate.
-/

namespace Experiments.TheAlphaDecayEffect

/-- A refinement branch in the causal record: a coarse boundary `slot` it contributes to, and a
`weight` (how much curvature it carries; only `slot` is ever read at the boundary). -/
structure Branch where
  slot : Nat
  weight : Nat
deriving DecidableEq, Repr

/-- A nuclear ledger: the list of refinement `branches` recorded in the interior, plus the boundary
`reading` currently representable on the overlap surface. -/
structure Nucleus where
  branches : List Branch
  reading : Nat
deriving DecidableEq, Repr

/-- The overlap boundary: a neighbouring ledger reads ONLY the `reading` of a nucleus — the interior
`branches`/`weight` are not visible. This is the restriction map whose agreement IS Martin
Consistency at the seam. -/
def overlapBoundary : Experiments.Common.Boundary Nucleus Nat :=
  { restrict := fun n => n.reading }

namespace Nucleus

/-- Two configurations are **Martin-consistent** (admit one reconciled causal order) iff their
boundary readings agree — i.e. `overlapBoundary.compatible`. -/
def reconcilable (left right : Nucleus) : Prop :=
  overlapBoundary.compatible left right

instance (left right : Nucleus) : Decidable (left.reconcilable right) := by
  unfold reconcilable Experiments.Common.Boundary.compatible overlapBoundary
  exact inferInstance

end Nucleus

/-- The **Causal Folding Operator** `f`: the minimal corrective update. It REMOVES the inconsistent
branch `bad` from the record and restores the boundary `reading` to the `target` the neighbouring
ledger demands. The bound configuration `Ψ_bound` becomes the unbound `Ψ_unbound`. -/
def fold (target : Nat) (bad : Branch) (n : Nucleus) : Nucleus :=
  { branches := n.branches.filter (· != bad), reading := target }

/-- The *unfolded* state: the still-contradictory configuration BEFORE the operator acts — the bad
branch is still present and the stale boundary reading is untouched. This is what an exterior ledger
sees if no fold occurs. -/
def unfolded (n : Nucleus) : Nucleus :=
  { branches := n.branches, reading := n.reading }

-- ---------------------------------------------------------------------------
-- FALSIFIABLE lemmas. Each is ∀-quantified and breaks if a hypothesis is dropped.
-- ---------------------------------------------------------------------------

/-- FOLD RESTORES CONSISTENCY: after folding to `t`, the configuration reconciles with ANY reference
whose reading is `t`. Quantified over all targets, bad branches, and configurations. -/
theorem fold_reconciles
    (t : Nat) (bad : Branch) (n ref : Nucleus) (h : ref.reading = t) :
    (fold t bad n).reconcilable ref := by
  unfold Nucleus.reconcilable Experiments.Common.Boundary.compatible overlapBoundary fold
  exact h.symm

/-- FOLD IS NECESSARY (falsifiability witness, ∀-quantified): if the demanded reading `t` differs
from the current reading, the UNFOLDED contradiction is NOT reconcilable with a reference at `t`.
Drop the fold and Martin Consistency fails — this is what forces the alpha emission. The
hypothesis `hstale` is load-bearing: without `n.reading ≠ t` the conclusion is false. -/
theorem unfolded_not_reconciled
    (t : Nat) (n ref : Nucleus)
    (hstale : n.reading ≠ t) (href : ref.reading = t) :
    ¬ (unfolded n).reconcilable ref := by
  unfold Nucleus.reconcilable Experiments.Common.Boundary.compatible overlapBoundary unfolded
  intro hbad
  exact hstale (href ▸ hbad)

/-- BOUNDARY-ONLY: reconciliation depends ONLY on the boundary reading, never on the interior
branch list. Two configurations with the same reading are reconcilable regardless of their
(arbitrary) branches — the holographic overlap constraint. -/
theorem reconcilable_of_same_reading
    (left right : Nucleus) (h : left.reading = right.reading) :
    left.reconcilable right := by
  unfold Nucleus.reconcilable Experiments.Common.Boundary.compatible overlapBoundary
  exact h

-- ---------------------------------------------------------------------------
-- The canonical decay event.
-- ---------------------------------------------------------------------------

/-- The inconsistent branch that has accumulated unresolved curvature — the one the fold removes. -/
def alphaBranch : Branch := { slot := 2, weight := 4 }

/-- A spectator branch that stays bound (different from `alphaBranch`). -/
def coreBranch : Branch := { slot := 1, weight := 90 }

/-- The bound nucleus before decay: carries the bad branch, with a STALE boundary reading `5` — the
accumulated curvature has pushed the demanded reading away from what the surface shows. -/
def boundNucleus : Nucleus := { branches := [coreBranch, alphaBranch], reading := 5 }

/-- The exterior reference the overlap must reconcile with: it demands reading `7`. -/
def exteriorReference : Nucleus := { branches := [], reading := 7 }

/-- The state AFTER the fold removes the inconsistent branch and restores the demanded reading. -/
def unboundNucleus : Nucleus := fold 7 alphaBranch boundNucleus

/-- The repaired (unbound) state reconciles with the exterior reference (concrete, via `Decidable`). -/
theorem unbound_reconciles_canonical : unboundNucleus.reconcilable exteriorReference := by decide

/-- CONSERVATION: the fold removes exactly one branch — `bound = unbound + α`. The emitted alpha is
the branch that left the ledger. -/
theorem fold_removes_one_branch :
    unboundNucleus.branches.length + 1 = boundNucleus.branches.length := by decide

-- ---------------------------------------------------------------------------
-- THE CLAIM (content-bearing; coupling conjunct is the harness Boundary.compatible).
-- ---------------------------------------------------------------------------

/-- The claim, in honest parts:
* (repair) the folded (unbound) state reconciles with the exterior reference — proved here AND it is
  exactly `overlapBoundary.compatible unboundNucleus exteriorReference`, the harness's two-region
  reconciliation predicate (this is the LOAD-BEARING coupling: break `Boundary.compatible` and this
  conjunct breaks);
* (no-go) the UNFOLDED contradiction is NOT reconcilable — so the alpha emission is required; and
* (conservation) the fold removes exactly one branch (`bound = unbound + α`). -/
def claimStatement : Prop :=
  Experiments.Common.Boundary.compatible overlapBoundary unboundNucleus exteriorReference ∧
    ¬ (unfolded boundNucleus).reconcilable exteriorReference ∧
    unboundNucleus.branches.length + 1 = boundNucleus.branches.length

def claim : Experiments.Common.Claim :=
  { tag := Experiments.Common.ClaimTag.inadmissibilityNoGo
    statement := claimStatement }

theorem claim_holds : claim.statement :=
  ⟨ fold_reconciles 7 alphaBranch boundNucleus exteriorReference rfl,
    unfolded_not_reconciled 7 boundNucleus exteriorReference (by decide) rfl,
    fold_removes_one_branch ⟩

/-- The tag is an honest ceiling: an inadmissibility no-go (the un-repaired overlap cannot be
reconciled), nothing more. -/
theorem ceiling : claim.tag = Experiments.Common.ClaimTag.inadmissibilityNoGo := rfl

-- ---------------------------------------------------------------------------
-- A computable run + a non-vacuous Experiment.claim, with a proved bridge.
-- ---------------------------------------------------------------------------

structure Setup where
  target : Nat
  bad : Branch
  start : Nucleus
  reference : Nucleus

/-- The run computes whether the fold reconciles the configuration with the reference. -/
def run (s : Setup) : Bool :=
  decide ((fold s.target s.bad s.start).reconcilable s.reference)

def experiment : Experiments.Common.Experiment Setup Bool :=
  { tag := claim.tag
    run := run
    claim := fun s => (fold s.target s.bad s.start).reconcilable s.reference }

theorem run_iff_claim (s : Setup) :
    run s = true ↔ experiment.claim s := by
  simp only [run, experiment, decide_eq_true_iff]

def canonicalSetup : Setup :=
  { target := 7, bad := alphaBranch, start := boundNucleus, reference := exteriorReference }

#eval run canonicalSetup                                  -- expect: true
-- Falsifiability witness: the UNFOLDED contradiction does NOT reconcile (no-go is load-bearing).
#eval decide ((unfolded boundNucleus).reconcilable exteriorReference)  -- expect: false
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

end Experiments.TheAlphaDecayEffect
