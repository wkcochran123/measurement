import Experiments.Common

/-!
# The Jupyter Effect — Sequential Necessity of the causal ledger

Source: `instrument/chapters/11.tex:351` (`phenomenon`).

A computational notebook has no cell value until its predecessors execute: the
causal ledger is **order-dependent**. If two admissible updates try to modify the
same dependency with **no defined order between them**, the ledger does not branch,
average, or superpose — the history is **rejected** (the kernel halts). Observable
physics is exactly the surviving execution trace that did not fault.

We model this finitely:

* a `Dependency` is a named slot with a value (`Update` writes a value to a slot);
* a `History` is a list of updates plus the order each update sits at;
* **Sequential Necessity** = every update carries a defined order index, and no two
  updates to the *same* slot share an order index. When that holds, the final state
  is well defined; when two writes to one slot collide at the same order, the history
  is **inadmissible** — there is no merged boundary state the two candidate timelines
  can agree on (the no-go).

## Coupling (HARNESS, load-bearing)
The collision is discharged by `Experiments.Common.Boundary.compatible`: two candidate
post-update boundary states are admissible to merge **iff** they restrict to the same
shared-slot value. Conflicting unordered writes restrict to *different* values, so they
are NOT `compatible` — and `claim_holds` carries a conjunct
`¬ depBoundary.compatible …` discharged by `conflict_incompatible`. Break that boundary
identity and this file fails to build.

## NOT claimed
That this is a real notebook kernel, a real scheduler, or any continuum dynamics;
that "time" is *derived* (the order index is a labelled `Nat`, not a clock); any claim
about concurrency theory (linearizability, CRDTs, vector clocks). The model forbids
exactly one thing — two unordered writes to one slot — and asserts exactly that the
ordered case has a defined final state. **Claim ceiling:** a finite inadmissibility
no-go on the causal ledger, one conjunct of which is the harness boundary theorem.
-/

namespace Experiments.TheJupyterEffect

/-- A named dependency slot carrying a `Nat` value. `slot` identifies *which* cell. -/
structure Update where
  slot : Nat
  value : Nat
  order : Nat
deriving DecidableEq, Repr

/-- The shared boundary a neighbouring ledger can see of a write: the slot it touched
and the value it left there. (The `order` is internal bookkeeping, not observable across
the seam — only the slot/value pair must reconcile.) -/
structure SlotState where
  slot : Nat
  value : Nat
deriving DecidableEq, Repr

/-- Project an update onto the boundary state it exposes. -/
def expose (u : Update) : SlotState := { slot := u.slot, value := u.value }

/-- The harness boundary for updates: what is visible across the seam is the
slot/value pair `expose` records. -/
def depBoundary : Experiments.Common.Boundary Update SlotState :=
  { restrict := expose }

-- ---------------------------------------------------------------------------
-- SEQUENTIAL NECESSITY: the admissibility predicate on a pair of updates.
-- ---------------------------------------------------------------------------

/-- Two updates **collide** when they write the *same* slot at the *same* order with
*different* values: an asynchronous conflict with no defined resolution. -/
def collides (u v : Update) : Prop :=
  u.slot = v.slot ∧ u.order = v.order ∧ u.value ≠ v.value

/-- Sequential Necessity for a pair: either they touch different slots, or they sit at
distinct order indices. (The negation of `collides`'s first two conjuncts — admissibility
is exactly "ordered or independent".) -/
def sequentiallyOrdered (u v : Update) : Prop :=
  u.slot ≠ v.slot ∨ u.order ≠ v.order

instance (u v : Update) : Decidable (collides u v) := by
  unfold collides; exact inferInstance
instance (u v : Update) : Decidable (sequentiallyOrdered u v) := by
  unfold sequentiallyOrdered; exact inferInstance

-- ---------------------------------------------------------------------------
-- FALSIFIABLE lemmas (∀-quantified; drop a hypothesis and each one breaks).
-- ---------------------------------------------------------------------------

/-- A collision is genuinely a value disagreement at the seam: colliding updates expose
DIFFERENT boundary states, hence are NOT `compatible`. This is the no-go, quantified over
ALL update pairs. (Drop the `u.value ≠ v.value` hypothesis hidden in `collides` and the two
boundary states could coincide — so it is load-bearing.) -/
theorem conflict_incompatible (u v : Update) (h : collides u v) :
    ¬ depBoundary.compatible u v := by
  intro hc
  -- hc : depBoundary.restrict u = depBoundary.restrict v, i.e. expose u = expose v
  have hval : u.value = v.value := by
    have : (expose u).value = (expose v).value := by
      simp only [Experiments.Common.Boundary.compatible, depBoundary] at hc
      rw [hc]
    simpa [expose] using this
  exact h.2.2 hval

/-- Sequential Necessity *prevents* a collision: if two updates are sequentially ordered
(different slot OR different order index), they cannot collide. Quantified over all pairs;
drop either disjunct and a same-slot/same-order conflict slips through. -/
theorem ordered_not_collides (u v : Update) (h : sequentiallyOrdered u v) :
    ¬ collides u v := by
  intro hcol
  match h with
  | Or.inl hslot => exact hslot hcol.1
  | Or.inr horder => exact horder hcol.2.1

/-- Independent writes (different slots) RECONCILE structurally: two updates to different
slots that were forced to share a value still expose distinct boundaries — but if they
share slot AND value they are compatible regardless of order. This pins the *positive*
half: agreeing writes are admissible. -/
theorem agreeing_compatible (u v : Update)
    (hslot : u.slot = v.slot) (hval : u.value = v.value) :
    depBoundary.compatible u v := by
  simp only [Experiments.Common.Boundary.compatible, depBoundary, expose, hslot, hval]

-- ---------------------------------------------------------------------------
-- The canonical conflict event: two unordered writes to slot 0.
-- ---------------------------------------------------------------------------

/-- Update A: writes value 1 to slot 0 at order 5. -/
def writeA : Update := { slot := 0, value := 1, order := 5 }
/-- Update B: writes value 2 to the SAME slot 0 at the SAME order 5 — the conflict. -/
def writeB : Update := { slot := 0, value := 2, order := 5 }
/-- A sequentially ordered counterpart: same slot/value disagreement, but order 6. -/
def writeBLater : Update := { slot := 0, value := 2, order := 6 }

theorem canonical_collides : collides writeA writeB := by decide
theorem canonical_ordered : sequentiallyOrdered writeA writeBLater := by decide

-- ---------------------------------------------------------------------------
-- THE CLAIM (content-bearing conjunction; the boundary conjunct is harness-coupled).
-- ---------------------------------------------------------------------------

/-- The claim, in honest parts:
* (the conflict) `writeA`/`writeB` collide — two unordered writes to one slot;
* (the NO-GO, harness-coupled) those two candidate histories are **inadmissible**:
  `¬ depBoundary.compatible writeA writeB` — discharged by `conflict_incompatible`,
  which reads the harness `Boundary.compatible`;
* (Sequential Necessity restores admissibility) moving the second write to a distinct
  order index removes the collision: `¬ collides writeA writeBLater`. -/
def claimStatement : Prop :=
  collides writeA writeB ∧
    ¬ depBoundary.compatible writeA writeB ∧
    ¬ collides writeA writeBLater

def claim : Experiments.Common.Claim :=
  { tag := Experiments.Common.ClaimTag.inadmissibilityNoGo
    statement := claimStatement }

theorem claim_holds : claim.statement :=
  ⟨canonical_collides,
   conflict_incompatible writeA writeB canonical_collides,
   ordered_not_collides writeA writeBLater canonical_ordered⟩

/-- The tag is an honest ceiling: an inadmissibility no-go, nothing more. -/
theorem ceiling :
    claim.tag = Experiments.Common.ClaimTag.inadmissibilityNoGo := rfl

-- ---------------------------------------------------------------------------
-- A computable run + a NON-vacuous Experiment.claim, with a proved bridge.
-- ---------------------------------------------------------------------------

structure Setup where
  first : Update
  second : Update

/-- The run computes whether the pair is admissible (sequentially ordered) — via the
`Decidable` instance. `true` = admissible timeline; `false` = the kernel halts. -/
def run (s : Setup) : Bool := decide (sequentiallyOrdered s.first s.second)

def experiment : Experiments.Common.Experiment Setup Bool :=
  { tag := claim.tag
    run := run
    claim := fun s => sequentiallyOrdered s.first s.second }

theorem run_iff_claim (s : Setup) :
    run s = true ↔ experiment.claim s := by
  simp only [run, experiment, decide_eq_true_iff]

def conflictSetup : Setup := { first := writeA, second := writeB }
def orderedSetup : Setup := { first := writeA, second := writeBLater }

/-- Make the exported claim decidable so the device can `decide` it. -/
instance (setup : Setup) : Decidable (experiment.claim setup) := by
  unfold experiment Experiments.Common.Experiment.claim; exact inferInstance

/-- Bring a minimal device next to this experiment: it records whether the exported claim fires. -/
def deviceNear (setup : Setup) : Bool :=
  decide (experiment.claim setup)

theorem deviceNear_detects_claim (setup : Setup) :
    deviceNear setup = true ↔ experiment.claim setup := by
  simp only [deviceNear, decide_eq_true_iff]

def triangulation : Experiments.Common.Triangulation Setup Bool :=
  { experiment := experiment
    device := deviceNear
    detects := deviceNear_detects_claim }

#eval run orderedSetup    -- expect: true  (distinct order indices → admissible)
#eval run conflictSetup   -- expect: FALSE (same slot, same order → kernel halts) — load-bearing
#print axioms claim_holds

end Experiments.TheJupyterEffect
