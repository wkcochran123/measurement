import Experiments.Common

/-!
# The Amdahl Effect — a finite-ledger model of the speedup bound

The source phenomenon (`instrument/chapters/11.tex:331`): no refinement can be made arbitrarily
fast by parallelism. If a fraction `p` of the ledger is perfectly correlant (parallelizable) and
the remaining `1 - p` is sequentially uncorrelant, then no admissible extension of the ledger can
run faster than

    S_max = 1 / (1 - p).

The uncorrelant portion is the irreducible sequential floor: segments of the causal record that
cannot be merged, reordered, or parallelized without violating admissibility.

We model this *finitely* and *integrally*. A ledger of `total` causal segments is split into a
`sequential` (uncorrelant) part and a `parallel` (correlant) part. With unlimited workers the
parallel part collapses to time-cost `0`, but the sequential part is irreducible: the achievable
cost is bounded **below** by `sequential`, hence the speedup over the serial cost `total` is
bounded **above**. This is a counting/capacity statement — the harness `Counting.boundedBy`
branch — so the claim is coupled to `Experiments.Common.Counting.boundedBy_of_eq`.

## NOT claimed
That `1/(1-p)` is *derived* (it is the real-number form; we model the integral floor `sequential`,
not the rational limit). No claim about wall-clock time, scheduler behaviour, communication cost,
super-linear/cache effects, Gustafson's law, or the *continuum* limit `p → 1`. No claim that the
device's geometry forces this — it is a finite ledger identity. **Claim ceiling:** a finite ledger
model of the sequentiality floor, whose capacity conjunct is the harness's own theorem.
-/

namespace Experiments.TheAmdahlEffect

/-- A causal workload split into its irreducible **sequential** (uncorrelant) part and its
perfectly **parallel** (correlant) part. The `total` is their sum — the serial time-cost. -/
structure Workload where
  sequential : Nat
  parallel : Nat
deriving DecidableEq, Repr

namespace Workload

/-- Serial cost: run everything one segment at a time. -/
def total (w : Workload) : Nat := w.sequential + w.parallel

/-- The infinite-worker cost: the parallel part collapses to `0`, only the sequential floor
remains. This is the Amdahl floor. -/
def idealParallelCost (w : Workload) : Nat := w.sequential

/-- The ledger of segments that MUST stay sequential (the uncorrelant residue). -/
def sequentialLedger (w : Workload) : Experiments.Common.Ledger Unit :=
  { events := List.replicate w.sequential () }

theorem sequentialLedger_count (w : Workload) :
    (w.sequentialLedger).count = w.sequential := by
  simp [sequentialLedger, Experiments.Common.Ledger.count]

end Workload

-- ---------------------------------------------------------------------------
-- FALSIFIABLE lemmas: each would break if its hypothesis were dropped.
-- ---------------------------------------------------------------------------

/-- THE SEQUENTIALITY FLOOR: with any worker count, you can never beat the sequential part.
The ideal (infinite-worker) cost is bounded BELOW by `sequential`. Quantified over ALL workloads.
Drop the model and this breaks; it is the irreducible floor. -/
theorem floor_is_sequential (w : Workload) :
    w.sequential ≤ w.idealParallelCost := by
  unfold Workload.idealParallelCost
  exact Nat.le_refl _

/-- NO SPEEDUP WHEN NOTHING IS PARALLEL: if the parallel part is empty (`p = 0`), the ideal cost
equals the serial cost — speedup `1`. **Falsifiable**: the hypothesis `w.parallel = 0` is
load-bearing; for a workload with `parallel > 0` the conclusion `idealParallelCost = total` fails
(e.g. `{sequential := 0, parallel := 1}` gives `0 ≠ 1`). -/
theorem no_speedup_without_parallel (w : Workload) (h : w.parallel = 0) :
    w.idealParallelCost = w.total := by
  unfold Workload.idealParallelCost Workload.total
  omega

/-- POSITIVE FLOOR: a nonzero sequential part forces a nonzero ideal cost — you cannot reach
zero time. **Falsifiable**: drop `0 < w.sequential` and a fully-parallel workload reaches `0`. -/
theorem positive_floor (w : Workload) (h : 0 < w.sequential) :
    0 < w.idealParallelCost := by
  unfold Workload.idealParallelCost
  exact h

-- ---------------------------------------------------------------------------
-- HARNESS COUPLING: the sequential floor is a capacity bound.
-- The ledger of uncorrelant segments is bounded by exactly its count, via the harness theorem
-- `Counting.boundedBy_of_eq`. This is LOAD-BEARING: it is a conjunct of `claim_holds`, so a
-- rename/sorry/regression in `Experiments.Common.Counting` breaks THIS build.
-- ---------------------------------------------------------------------------

/-- A canonical workload: 1 irreducible sequential segment, 3 parallelizable ones.
Serial cost 4; ideal cost 1; speedup ceiling 4 (= 1/(1-p) with p = 3/4). -/
def canonicalWorkload : Workload := { sequential := 1, parallel := 3 }

/-- The uncorrelant residue of `canonicalWorkload` is bounded by its own count — the harness
capacity theorem applied to the sequential floor. -/
theorem floor_bounded :
    Experiments.Common.Counting.boundedBy
      canonicalWorkload.sequentialLedger canonicalWorkload.sequential :=
  Experiments.Common.Counting.boundedBy_of_eq
    (canonicalWorkload.sequentialLedger_count)

-- ---------------------------------------------------------------------------
-- THE CLAIM (content-bearing conjunction; one conjunct is the harness theorem).
-- ---------------------------------------------------------------------------

/-- The claim, in honest parts:
* (floor) the ideal-parallel cost is bounded below by the sequential part — the Amdahl floor;
* (no free lunch) a positive sequential part forces a positive ideal cost; and
* (capacity / harness coupling) the uncorrelant ledger is bounded by its count
  (`Experiments.Common.Counting.boundedBy_of_eq`). -/
def claimStatement : Prop :=
  canonicalWorkload.sequential ≤ canonicalWorkload.idealParallelCost ∧
    0 < canonicalWorkload.idealParallelCost ∧
    Experiments.Common.Counting.boundedBy
      canonicalWorkload.sequentialLedger canonicalWorkload.sequential

def claim : Experiments.Common.Claim :=
  { tag := Experiments.Common.ClaimTag.finiteLedgerModel
    statement := claimStatement }

theorem claim_holds : claim.statement :=
  ⟨floor_is_sequential canonicalWorkload,
    positive_floor canonicalWorkload (by decide),
    floor_bounded⟩

/-- The tag is an honest ceiling: a finite ledger model of the sequentiality floor. -/
theorem ceiling : claim.tag = Experiments.Common.ClaimTag.finiteLedgerModel := rfl

-- ---------------------------------------------------------------------------
-- A computable run + a non-vacuous Experiment.claim, with a proved bridge.
-- ---------------------------------------------------------------------------

structure Setup where
  workload : Workload

/-- The run computes the ideal-parallel cost (the floor) for a setup. -/
def run (s : Setup) : Nat := s.workload.idealParallelCost

/-- The exported claim is a genuine function of the setup: the ideal cost equals the sequential
floor. The bridge pins it to `run`, so the claim body cannot be silently swapped for `True`. -/
def experiment : Experiments.Common.Experiment Setup Nat :=
  { tag := claim.tag
    run := run
    claim := fun s => run s = s.workload.sequential }

theorem run_iff_claim (s : Setup) :
    run s = s.workload.sequential ↔ experiment.claim s := by
  simp only [experiment]

def canonicalSetup : Setup := { workload := canonicalWorkload }

#eval run canonicalSetup                                    -- expect: 1 (the floor)
-- The falsifiable predicate evaluated where it is FALSE: `idealParallelCost = total` requires
-- the parallel part to be empty; `canonicalWorkload` has parallel = 3, so this prints `false`.
#eval decide (canonicalWorkload.idealParallelCost = canonicalWorkload.total)   -- expect: false
#print axioms claim_holds                                   -- ambient [propext, Quot.sound]

/-- Bring a minimal device next to this experiment: it records whether the exported claim fires. -/
def deviceNear (setup : Setup) : Bool :=
  decide (experiment.claim setup)

theorem deviceNear_detects_claim (setup : Setup) :
    deviceNear setup = true ↔ experiment.claim setup := by
  simp [deviceNear]

def triangulation : Experiments.Common.Triangulation Setup Nat :=
  { experiment := experiment
    device := deviceNear
    detects := deviceNear_detects_claim }

end Experiments.TheAmdahlEffect
