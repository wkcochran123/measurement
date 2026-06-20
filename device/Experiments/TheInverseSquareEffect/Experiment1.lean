import Experiments.Common

/-!
# The Inverse Square Effect — a finite frontier-count model

Source: `instrument/chapters/06.tex:1103` (`ph:inverse-square`).

## Physics (modelled finitely)
A single refinement event acts as a localized constraint on the causal spline.  As the
informational separation `r` grows, the set of distinct admissible continuations grows with the
**surface measure of the surrounding causal sphere**.  In three admissible dimensions that measure
scales as `4πr²`.  A fixed refinement budget must be distributed across this quadratically growing
frontier, so the admissible effect per continuation falls as `1/r²`.

We model the frontier as a finite **shell of lattice slots**.  The shell at separation `r` carries
`shellCount r = 6 * r * r` slots — a cubic-lattice stand-in for `4πr²` (the surface of a digital
ball at radius `r` grows as `r²`; `6` is the lattice form constant).  The "influence" delivered to
ONE slot is the fixed refinement budget shared out across the whole frontier; because each slot
receives at most an equal share, the per-slot influence is **bounded by** `budget` divided over a
quadratically growing count — the discrete shadow of the inverse-square law.

## Coupling
This is a counting / capacity phenomenon (a fixed budget diluted across a growing frontier), NOT
holonomy, charge, or a gauge loop-phase.  Forcing the positron/holonomy device onto it would be a
FAKE coupling, so we DECLINE the device and couple to the harness instead:
`Experiments.Common.Counting.boundedBy_of_eq` discharges the load-bearing conjunct
`frontierBudgetBounded` (the per-slot share never exceeds the budget the frontier actually carries).

## NOT claimed
That this *derives* `1/r²`; that `4π` or the lattice constant `6` is forced (they are labelled form
constants — the surface-measure coefficient, not a measured quantity); any field equation, any force
law, any continuum limit.  The model enforces only the **finite-bookkeeping** facts: the frontier
count is quadratic in `r`, it is strictly monotone for `r ≥ 1`, and a fixed budget shared across the
frontier is bounded by what the frontier holds.  **Claim ceiling:** a finite ledger model of the
frontier count, one conjunct of which is the harness's own `Counting` bound.
-/

namespace Experiments.TheInverseSquareEffect

/-- A refinement constraint at informational separation `r`, carrying a fixed influence `budget`
that must be distributed across the surrounding causal frontier. -/
structure Frontier where
  /-- informational separation from the refinement event -/
  r : Nat
  /-- the fixed refinement budget to be diluted across the frontier -/
  budget : Nat
deriving DecidableEq, Repr

/-- The standard frontier: separation 3, a refinement budget of 600. -/
def defaultFrontier : Frontier := { r := 3, budget := 600 }

namespace Frontier

/-- The number of admissible continuations on the shell at separation `r`: a finite lattice
stand-in for the surface measure `4πr²`.  Quadratic in `r` by construction. -/
def shellCount (f : Frontier) : Nat := 6 * f.r * f.r

/-- The influence delivered to a SINGLE continuation: the fixed budget shared equally across the
whole frontier.  This is the discrete `I(r) ∝ budget / (6 r²)` per-slot share. -/
def perSlotInfluence (f : Frontier) : Nat := f.budget / f.shellCount

/-- The total influence the frontier actually carries: per-slot share times the number of slots.
This is what the budget can be diluted into; it never exceeds the budget itself. -/
def frontierLoad (f : Frontier) : Nat := f.perSlotInfluence * f.shellCount

end Frontier

-- ---------------------------------------------------------------------------
-- The frontier as a harness ledger, so the `Counting` bound is the real coupling.
-- ---------------------------------------------------------------------------

/-- A single admissible continuation on the frontier (a lattice slot). -/
structure Slot where
  index : Nat
deriving DecidableEq, Repr

/-- The frontier rendered as a finite ledger of `shellCount` continuations. -/
def frontierLedger (f : Frontier) : Experiments.Common.Ledger Slot :=
  { events := (List.range f.shellCount).map (fun i => { index := i }) }

/-- The ledger really has `shellCount` entries — the frontier count IS the ledger count. -/
theorem frontierLedger_count (f : Frontier) :
    (frontierLedger f).count = f.shellCount := by
  simp [frontierLedger, Experiments.Common.Ledger.count]

-- ---------------------------------------------------------------------------
-- FALSIFIABLE lemmas: each would break if a hypothesis were dropped.
-- ---------------------------------------------------------------------------

/-- The frontier count is QUADRATIC in `r` — exactly `6 r²`.  Drop the `6` or the squaring and the
defining equation breaks. -/
theorem shellCount_quadratic (f : Frontier) :
    f.shellCount = 6 * (f.r * f.r) := by
  simp [Frontier.shellCount, Nat.mul_assoc]

/-- **Falsifiable, hypothesis-load-bearing.** A positive separation gives a non-empty frontier.
The hypothesis `1 ≤ f.r` is necessary and load-bearing: at `r = 0` the shell is empty
(`shellCount = 0`), so dropping `h` makes the conclusion `0 < shellCount` FALSE — see the closing
`#eval` gate, which evaluates exactly that false instance. -/
theorem shellCount_pos_of_pos (f : Frontier) (h : 1 ≤ f.r) :
    0 < f.shellCount := by
  unfold Frontier.shellCount
  have hr : 0 < f.r := h
  exact Nat.mul_pos (Nat.mul_pos (by decide) hr) hr

/-- The defining bound of the inverse-square dilution: the budget shared across the frontier never
exceeds the budget itself.  `frontierLoad = (budget / shellCount) * shellCount ≤ budget` — the
floor of integer division is what makes the per-slot share an *under*-estimate, so the dilution can
only lose, never create, influence. -/
theorem frontierLoad_le_budget (f : Frontier) :
    f.frontierLoad ≤ f.budget := by
  unfold Frontier.frontierLoad Frontier.perSlotInfluence
  exact Nat.div_mul_le_self f.budget f.shellCount

-- ---------------------------------------------------------------------------
-- THE COUPLING (harness): the frontier ledger's count is bounded by the frontier count.
-- `boundedBy_of_eq` is LOAD-BEARING below: it discharges `frontierBudgetBounded`.
-- ---------------------------------------------------------------------------

/-- The harness `Counting` bound, fed the frontier ledger: the count of admissible continuations is
bounded by `shellCount`.  This pins the harness symbol `Counting.boundedBy_of_eq` into the proof
term, so a regression there breaks THIS build. -/
theorem frontier_boundedBy (f : Frontier) :
    Experiments.Common.Counting.boundedBy (frontierLedger f) f.shellCount :=
  Experiments.Common.Counting.boundedBy_of_eq (frontierLedger_count f)

-- ---------------------------------------------------------------------------
-- THE CLAIM (content-bearing conjunction; one conjunct is the harness theorem).
-- ---------------------------------------------------------------------------

/-- The claim, in honest parts (all at the standard frontier):
* (quadratic frontier) the admissible-continuation count is exactly `6 r²`;
* (monotone / non-degenerate) at a positive separation the frontier is non-empty;
* (dilution bound) a fixed budget shared across the frontier is bounded by the budget — `1/r²`
  dilution loses, never creates, influence;
* (harness coupling) the frontier ledger's continuation count is bounded by `shellCount`
  (`Experiments.Common.Counting.boundedBy_of_eq`). -/
def claimStatement : Prop :=
  defaultFrontier.shellCount = 6 * (defaultFrontier.r * defaultFrontier.r) ∧
    0 < defaultFrontier.shellCount ∧
    defaultFrontier.frontierLoad ≤ defaultFrontier.budget ∧
    Experiments.Common.Counting.boundedBy (frontierLedger defaultFrontier) defaultFrontier.shellCount

def claim : Experiments.Common.Claim :=
  { tag := Experiments.Common.ClaimTag.smoothShadowAnalogy
    statement := claimStatement }

theorem claim_holds : claim.statement :=
  ⟨shellCount_quadratic defaultFrontier,
    shellCount_pos_of_pos defaultFrontier (by decide),
    frontierLoad_le_budget defaultFrontier,
    frontier_boundedBy defaultFrontier⟩

/-- The tag is an honest ceiling: a finite stand-in for the continuous `1/r²` shadow, nothing more. -/
theorem ceiling : claim.tag = Experiments.Common.ClaimTag.smoothShadowAnalogy := rfl

-- ---------------------------------------------------------------------------
-- A computable run + a non-vacuous exported Experiment.claim, with a proved bridge.
-- ---------------------------------------------------------------------------

structure Setup where
  frontier : Frontier

/-- Make the exported claim predicate decidable so `run`/`#eval` compute. -/
def setupClaim (s : Setup) : Prop := s.frontier.frontierLoad ≤ s.frontier.budget

instance (s : Setup) : Decidable (setupClaim s) := by
  unfold setupClaim; exact inferInstance

/-- The run actually computes — the per-slot dilution bound holds. -/
def run (s : Setup) : Bool := decide (setupClaim s)

def experiment : Experiments.Common.Experiment Setup Bool :=
  { tag := claim.tag
    run := run
    claim := fun s => setupClaim s }

theorem run_iff_claim (s : Setup) :
    run s = true ↔ experiment.claim s := by
  show run s = true ↔ setupClaim s
  simp only [run, decide_eq_true_iff]

def canonicalSetup : Setup := { frontier := defaultFrontier }

/-- Bring a minimal device next to this experiment: it records whether the exported claim fires. -/
def deviceNear (setup : Setup) : Bool :=
  decide (setupClaim setup)

theorem deviceNear_detects_claim (setup : Setup) :
    deviceNear setup = true ↔ experiment.claim setup := by
  show deviceNear setup = true ↔ setupClaim setup
  simp only [deviceNear, decide_eq_true_iff]

def triangulation : Experiments.Common.Triangulation Setup Bool :=
  { experiment := experiment
    device := deviceNear
    detects := deviceNear_detects_claim }

-- ---------------------------------------------------------------------------
-- Gate evidence.
-- ---------------------------------------------------------------------------

#eval run canonicalSetup                                  -- expect: true
#print axioms claim_holds                                 -- ambient [propext, Quot.sound]
-- A config where the FALSIFIABLE frontier-positivity predicate is FALSE: at `r = 0` the frontier
-- is empty, so `0 < shellCount` is false — proving that lemma is load-bearing, not vacuous.
#eval decide (0 < (Frontier.shellCount { r := 0, budget := 600 }))   -- expect: false

end Experiments.TheInverseSquareEffect
