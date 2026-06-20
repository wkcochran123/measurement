import Experiments.Common

/-!
# The Ideal Ledger Effect — finite bookkeeping model of `P V ∝ n T`

Source: `instrument/chapters/07.tex:685` (`ph:ideal-ledger`).

## Physics (modelled finitely)
A region `Ω` holds `n` mutually **uncorrelant** causal threads. Each thread emits
refinement events into the bulk; because the threads do not refine one another, their
only point of interaction is the **boundary**. The boundary must reconcile every
incoming event against the addressable refinement slots `V` of the partition, and the
informational **pressure** is the flux density of reconciliation:
`P ∝ n T / V`, i.e. the bookkeeping identity `P V ∝ n T`.

This file models that finitely as a **ledger of reconciliation events**: the boundary
work of `n` independent threads is the *append* of the per-thread ledgers, so the total
count is exactly the sum of the parts (the `n T` side). The **hard failure** is a finite
bandwidth bound: when the demanded reconciliation count exceeds the boundary's admissible
bandwidth, the partition ruptures.

## NOT claimed
That this *derives* the ideal gas law from kinetic theory; that `P`, `V`, `n`, `T` are
the physical pressure/volume/mole/temperature (they are finite event counts and slot
counts — a labelled stand-in); any continuum thermodynamics, any equation-of-state limit,
any statement about elastic collisions or a real explosion. **Claim ceiling:** a finite
ledger model whose `n T` side is the device-free harness identity
`Experiments.Common.Ledger.count_append` (additivity of independent ledgers), plus a
finite bandwidth no-go. No holonomy / charge / positron content — coupling is HARNESS.
-/

namespace Experiments.TheIdealLedgerEffect

open Experiments.Common

/-- A single reconciliation event raised by some thread, tagged by which thread raised it
and which addressable slot it targets on the boundary. -/
structure Reconcile where
  thread : Nat
  slot : Nat
deriving DecidableEq, Repr

/-- The boundary apparatus: `slots` addressable refinement slots (the `V`), and an
admissible reconciliation `bandwidth` per partition (the rupture floor). -/
structure Boundary where
  slots : Nat
  bandwidth : Nat
deriving Repr

/-- The standard partition: 4 addressable slots, bandwidth 8 reconciliations. -/
def defaultBoundary : Boundary := { slots := 4, bandwidth := 8 }

/-- The reconciliation ledger raised by one uncorrelant thread: `rate` events, all tagged
with this `thread`, spread `% slots` across the boundary addresses. -/
def threadLedger (b : Boundary) (thread rate : Nat) : Ledger Reconcile :=
  { events := (List.range rate).map (fun k => { thread := thread, slot := k % b.slots }) }

/-- One thread of `rate` events contributes exactly `rate` reconciliations. -/
theorem threadLedger_count (b : Boundary) (thread rate : Nat) :
    (threadLedger b thread rate).count = rate := by
  simp [threadLedger, Ledger.count]

namespace Boundary

/-- THE PRESSURE PREDICATE (the `P V ∝ n T` side, as a finite identity): the total
reconciliation work demanded equals the per-thread sum. Stated for a TWO-thread region so
the additivity is exactly the harness `count_append`. -/
def balances (b : Boundary) (left right : Ledger Reconcile) : Prop :=
  (Ledger.append left right).count = left.count + right.count

/-- THE RUPTURE PREDICATE (the hard failure): the demanded reconciliation count exceeds the
boundary's admissible bandwidth. -/
def ruptures (b : Boundary) (demand : Nat) : Prop :=
  b.bandwidth < demand

/-- THE STABILITY PREDICATE: the demand is within bandwidth. -/
def stable (b : Boundary) (demand : Nat) : Prop :=
  demand <= b.bandwidth

instance (b : Boundary) (l r : Ledger Reconcile) : Decidable (b.balances l r) := by
  unfold balances; exact inferInstance
instance (b : Boundary) (demand : Nat) : Decidable (b.ruptures demand) := by
  unfold ruptures; exact inferInstance
instance (b : Boundary) (demand : Nat) : Decidable (b.stable demand) := by
  unfold stable; exact inferInstance

end Boundary

-- ---------------------------------------------------------------------------
-- FALSIFIABLE lemmas (each ∀; drop a hypothesis and it breaks).
-- ---------------------------------------------------------------------------

/-- A demand strictly above bandwidth is NOT stable. Quantified over all boundaries and
demands; drop `h` and it is false (a demand can sit at-or-below bandwidth). -/
theorem ruptured_not_stable (b : Boundary) (demand : Nat)
    (h : b.ruptures demand) : ¬ b.stable demand :=
  fun hs => Nat.not_lt.mpr hs h

/-- A stable demand does NOT rupture. The dual; pins `stable` and `ruptures` as exclusive. -/
theorem stable_not_ruptured (b : Boundary) (demand : Nat)
    (h : b.stable demand) : ¬ b.ruptures demand :=
  fun hr => Nat.not_lt.mpr h hr

/-- THE BOOKKEEPING IDENTITY, falsifiable form: the two-thread demand is the sum of the
threads. This is `P V ∝ n T` read off the ledger — and it is the harness theorem
`Ledger.count_append`, so it is device-free but load-bearing. -/
theorem twoThread_demand_is_sum (b : Boundary) (left right : Ledger Reconcile) :
    b.balances left right :=
  Ledger.count_append left right

-- ---------------------------------------------------------------------------
-- The canonical two-thread region.
-- ---------------------------------------------------------------------------

/-- Two uncorrelant threads: thread 0 fires 3 events, thread 1 fires 3 events. -/
def threadA : Ledger Reconcile := threadLedger defaultBoundary 0 3
def threadB : Ledger Reconcile := threadLedger defaultBoundary 1 3

/-- The total demand of the canonical region: `n T = 3 + 3 = 6` reconciliations. -/
def canonicalDemand : Nat := (Ledger.append threadA threadB).count

theorem canonicalDemand_value : canonicalDemand = 6 := by
  unfold canonicalDemand threadA threadB
  simp [threadLedger, Ledger.append, Ledger.count]

/-- The canonical region balances (the `P V ∝ n T` identity holds here). -/
theorem balances_canonical : defaultBoundary.balances threadA threadB :=
  twoThread_demand_is_sum defaultBoundary threadA threadB

/-- The canonical region is STABLE: `6 ≤ 8` bandwidth, so the partition does not rupture. -/
theorem canonical_stable : defaultBoundary.stable canonicalDemand := by
  unfold canonicalDemand threadA threadB defaultBoundary Boundary.stable
  simp [threadLedger, Ledger.append, Ledger.count]

-- ---------------------------------------------------------------------------
-- THE CLAIM (content-bearing; the `n T` conjunct is the harness theorem).
-- ---------------------------------------------------------------------------

/-- The claim, in honest parts:
* (bookkeeping identity) the canonical two-thread demand equals the per-thread sum
  — `Ledger.count_append`, the HARNESS coupling, load-bearing here;
* (within bandwidth) the canonical demand is stable, the partition does not rupture; and
* (the hard failure is real) a demand above bandwidth genuinely ruptures. -/
def claimStatement : Prop :=
  defaultBoundary.balances threadA threadB ∧
    defaultBoundary.stable canonicalDemand ∧
    defaultBoundary.ruptures (defaultBoundary.bandwidth + 1)

def claim : Experiments.Common.Claim :=
  { tag := Experiments.Common.ClaimTag.finiteLedgerModel
    statement := claimStatement }

theorem claim_holds : claim.statement :=
  ⟨balances_canonical, canonical_stable, Nat.lt_succ_self defaultBoundary.bandwidth⟩

/-- The tag is an honest ceiling: a finite ledger model, nothing more. -/
theorem ceiling : claim.tag = Experiments.Common.ClaimTag.finiteLedgerModel := rfl

-- ---------------------------------------------------------------------------
-- A computable run + a non-vacuous Experiment.claim, with a proved bridge.
-- ---------------------------------------------------------------------------

structure Setup where
  boundary : Boundary
  left : Ledger Reconcile
  right : Ledger Reconcile

/-- The run computes whether this region stays within bandwidth (does not rupture). -/
def run (s : Setup) : Bool :=
  decide (s.boundary.stable (Ledger.append s.left s.right).count)

def experiment : Experiments.Common.Experiment Setup Bool :=
  { tag := claim.tag
    run := run
    claim := fun s => s.boundary.stable (Ledger.append s.left s.right).count }

theorem run_iff_claim (s : Setup) :
    run s = true ↔ experiment.claim s := by
  simp only [run, experiment, decide_eq_true_iff]

def canonicalSetup : Setup :=
  { boundary := defaultBoundary, left := threadA, right := threadB }

/-- Bring a minimal device next to this experiment: it records whether the claim fires. -/
def deviceNear (setup : Setup) : Bool :=
  decide (setup.boundary.stable (Ledger.append setup.left setup.right).count)

theorem deviceNear_detects_claim (setup : Setup) :
    deviceNear setup = true ↔ experiment.claim setup := by
  simp only [deviceNear, experiment, decide_eq_true_iff]

def triangulation : Experiments.Common.Triangulation Setup Bool :=
  { experiment := experiment
    device := deviceNear
    detects := deviceNear_detects_claim }

#eval run canonicalSetup                                   -- expect: true  (6 ≤ 8)
#print axioms claim_holds
-- Load-bearing check: at a starved boundary (bandwidth 4 < demand 6) the claim FAILS.
#eval decide (({ slots := 4, bandwidth := 4 } : Boundary).stable canonicalDemand)  -- expect: false

end Experiments.TheIdealLedgerEffect
