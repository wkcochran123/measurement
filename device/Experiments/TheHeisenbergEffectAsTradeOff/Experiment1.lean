import Experiments.Common

/-!
# The Heisenberg Effect as Trade-off — rebuilt to the exemplar shape

Source: `instrument/chapters/05.tex:398`, `phenomenon` `ph:heisenberg-tradeoff`.

## Physics (modelled finitely)
A ledger has a **fixed capacity** `n`: the total number of refinement marks it can
spend resolving outcome classes.  The classes split into two complementary groups — call
them the **position** group `A` and the **momentum** group `B` (the names are a finite
stand-in for the conjugate pair).  A `Budget` allocates `refineA` marks to `A` and
`refineB` to `B`.  An allocation is **admissible** iff it spends within capacity:
`refineA + refineB ≤ capacity`.

The TRADE-OFF is the content: under a *fixed* capacity, sharpening one group steals
budget from the other.  Concretely, in any admissible allocation each group's resolution
is bounded by what the *other* group leaves over: `refineA ≤ capacity - refineB`, and you
cannot have BOTH groups fully refined when their fully-refined demands exceed `capacity`.

The capacity coupling is the harness theorem `Experiments.Common.Counting.boundedBy_of_eq`:
the spent ledger's count is bounded by capacity, so this file fails to build if that
counting lemma is renamed or regresses.

## NOT claimed
That this is the real Heisenberg uncertainty principle; there is no `ħ`, no commutator,
no operator, no variance product `σ_x σ_p ≥ ħ/2` — `capacity` is a labelled finite budget,
not a derived bound.  No Fourier/conjugacy is formalized; "position"/"momentum" are *names*
on two ledger groups.  No statement about *measurement disturbance* or *simultaneous
eigenstates*.  **Claim ceiling:** a finite-capacity ledger model whose admissibility is the
counting bound `Experiments.Common.Counting.boundedBy_of_eq`, plus a falsifiable no-go on
over-budget joint refinement.
-/

namespace Experiments.TheHeisenbergEffectAsTradeOff

/-- A refinement allocation: marks spent on the position group `A` and the momentum group
`B`, against an apparatus of fixed total `capacity`. -/
structure Budget where
  capacity : Nat
  refineA : Nat
  refineB : Nat
deriving DecidableEq, Repr

namespace Budget

/-- The number of refinement marks the allocation actually spends. -/
def spent (b : Budget) : Nat := b.refineA + b.refineB

/-- An allocation is **admissible** iff it spends within capacity. -/
def admissible (b : Budget) : Prop := b.spent ≤ b.capacity

instance (b : Budget) : Decidable (b.admissible) := by
  unfold admissible spent; exact inferInstance

end Budget

/-- The spent marks viewed as a finite ledger of unit tokens (one event per mark), so the
harness counting lemma can speak about it. -/
def spentLedger (b : Budget) : Experiments.Common.Ledger Unit :=
  { events := List.replicate b.spent () }

/-- The ledger's count is exactly the marks spent (so `boundedBy_of_eq` can bite). -/
theorem spentLedger_count (b : Budget) :
    (spentLedger b).count = b.spent := by
  simp [spentLedger, Experiments.Common.Ledger.count]

-- ---------------------------------------------------------------------------
-- FALSIFIABLE lemmas: each would BREAK if its hypothesis were dropped.
-- ---------------------------------------------------------------------------

/-- TRADE-OFF (the heart): in any admissible allocation, group `A`'s resolution is bounded
by what `B` leaves of the capacity.  Quantified over ALL budgets; drop `admissible` and the
conclusion fails (e.g. `⟨1, 5, 5⟩`). -/
theorem refineA_le_complement (b : Budget) (h : b.admissible) :
    b.refineA ≤ b.capacity - b.refineB := by
  unfold Budget.admissible Budget.spent at h
  omega

/-- The symmetric trade-off for `B`. -/
theorem refineB_le_complement (b : Budget) (h : b.admissible) :
    b.refineB ≤ b.capacity - b.refineA := by
  unfold Budget.admissible Budget.spent at h
  omega

/-- NO-GO: if the two groups' *demanded* refinements (`dA`, `dB`) jointly exceed capacity,
no admissible allocation can meet both demands at once.  This is the over-budget
impossibility — quantified over all capacities and demands; drop `hOver` and it fails. -/
theorem cannot_jointly_refine
    (capacity dA dB : Nat) (hOver : capacity < dA + dB) :
    ¬ (Budget.admissible { capacity := capacity, refineA := dA, refineB := dB }) := by
  unfold Budget.admissible Budget.spent
  simp only
  omega

-- ---------------------------------------------------------------------------
-- The capacity coupling: the spent ledger is bounded by capacity for an
-- admissible budget — discharged by the HARNESS lemma `boundedBy_of_eq`
-- composed with the admissibility bound.  Load-bearing: a conjunct below.
-- ---------------------------------------------------------------------------

/-- For an admissible budget, the spent ledger's count is `≤ capacity`, witnessed through the
harness counting API.  The `≤` step uses `boundedBy_of_eq` to turn the exact count into a
bound, so a regression in that harness lemma breaks this build. -/
theorem spent_boundedBy_capacity (b : Budget) (h : b.admissible) :
    Experiments.Common.Counting.boundedBy (spentLedger b) b.capacity := by
  have hcount : (spentLedger b).count = b.spent := spentLedger_count b
  -- boundedBy at the exact count, then weaken to capacity via admissibility.
  have hself : Experiments.Common.Counting.boundedBy (spentLedger b) b.spent :=
    Experiments.Common.Counting.boundedBy_of_eq hcount
  unfold Experiments.Common.Counting.boundedBy at hself ⊢
  unfold Budget.admissible at h
  omega

-- ---------------------------------------------------------------------------
-- The canonical conjugate-pair apparatus.
-- ---------------------------------------------------------------------------

/-- A capacity-4 apparatus with the budget split 2/2 between the conjugate groups: an
admissible, balanced allocation. -/
def conjugateBudget : Budget := { capacity := 4, refineA := 2, refineB := 2 }

/-- The balanced split is admissible (concrete, via the `Decidable` instance). -/
theorem conjugate_admissible : conjugateBudget.admissible := by decide

/-- Fully refining BOTH groups (3 + 3) over a capacity-4 apparatus is inadmissible — the
trade-off bites on the canonical event. -/
theorem conjugate_overbudget_blocked :
    ¬ (Budget.admissible { capacity := 4, refineA := 3, refineB := 3 }) :=
  cannot_jointly_refine 4 3 3 (by decide)

-- ---------------------------------------------------------------------------
-- THE CLAIM (content-bearing conjunction; the capacity bound is the harness coupling).
-- ---------------------------------------------------------------------------

/-- The claim, in honest parts:
* (admissibility) the balanced conjugate split fits the capacity-4 apparatus;
* (trade-off) under that admissible split, `A`'s resolution is bounded by `B`'s complement;
* (capacity coupling) the spent ledger is bounded by capacity — discharged via the harness
  lemma `Experiments.Common.Counting.boundedBy_of_eq`; and
* (no-go) fully refining both groups (3+3 over 4) is inadmissible.
The capacity-coupling conjunct is load-bearing: it is proved through `boundedBy_of_eq`, so a
regression in that harness counting lemma fails this build. -/
def claimStatement : Prop :=
  conjugateBudget.admissible ∧
    conjugateBudget.refineA ≤ conjugateBudget.capacity - conjugateBudget.refineB ∧
    Experiments.Common.Counting.boundedBy (spentLedger conjugateBudget) conjugateBudget.capacity ∧
    ¬ (Budget.admissible { capacity := 4, refineA := 3, refineB := 3 })

def claim : Experiments.Common.Claim :=
  { tag := Experiments.Common.ClaimTag.inadmissibilityNoGo
    statement := claimStatement }

theorem claim_holds : claim.statement :=
  ⟨conjugate_admissible,
    refineA_le_complement conjugateBudget conjugate_admissible,
    spent_boundedBy_capacity conjugateBudget conjugate_admissible,
    conjugate_overbudget_blocked⟩

/-- The tag is an honest ceiling: a no-go on over-budget joint refinement. -/
theorem ceiling :
    claim.tag = Experiments.Common.ClaimTag.inadmissibilityNoGo := rfl

-- ---------------------------------------------------------------------------
-- A computable run + a non-vacuous Experiment.claim, with a proved bridge.
-- ---------------------------------------------------------------------------

abbrev Setup := Budget

/-- The run actually computes — thanks to the `Decidable` instance on `admissible`. -/
def run (s : Setup) : Bool := decide s.admissible

def experiment : Experiments.Common.Experiment Setup Bool :=
  { tag := claim.tag
    run := run
    claim := fun s => s.admissible }

theorem run_iff_claim (s : Setup) :
    run s = true ↔ experiment.claim s := by
  simp only [run, experiment, decide_eq_true_iff]

-- ---------------------------------------------------------------------------
-- Triangulation: a minimal device that detects whether the exported claim fires.
-- ---------------------------------------------------------------------------

/-- Bring a minimal device next to this experiment: it records whether the exported claim fires.
(Computed through the `admissible` `Decidable` instance, which `experiment.claim` reduces to.) -/
def deviceNear (setup : Setup) : Bool :=
  decide setup.admissible

theorem deviceNear_detects_claim (setup : Setup) :
    deviceNear setup = true ↔ experiment.claim setup := by
  simp only [deviceNear, experiment, decide_eq_true_iff]

def triangulation : Experiments.Common.Triangulation Setup Bool :=
  { experiment := experiment
    device := deviceNear
    detects := deviceNear_detects_claim }

-- ---------------------------------------------------------------------------
-- Gate evidence.
-- ---------------------------------------------------------------------------

#eval run conjugateBudget                                              -- expect: true  (2+2 ≤ 4)
#eval run { capacity := 4, refineA := 3, refineB := 3 }               -- expect: FALSE (6 > 4): the no-go is load-bearing
#print axioms claim_holds                                             -- ambient [propext, Quot.sound], not coupling

end Experiments.TheHeisenbergEffectAsTradeOff
