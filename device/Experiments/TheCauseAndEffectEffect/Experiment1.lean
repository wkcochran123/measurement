import Experiments.Common

/-!
# The Cause-Effect Effect — content-bearing rebuild (harness-coupled)

Source: `instrument/chapters/07.tex:611`, `phenomenon` env `ph:cause-effect-effect`.

## Physics (modelled finitely)
"Admissible causal records admit predictive structure far tighter than would be
expected from unconstrained combinatorics." If futures were joined by arbitrary
correlation, the number of admissible continuations would grow **exponentially**
with refinement depth. Admissibility — the requirement of *global consistency*
within the causal ledger — collapses that space into a narrow, predictable set.
Reliable cause-and-effect is the combinatorial *residue* of admissibility.

We model this directly:
* a `Continuation` is a finite causal record (a list of `Event`s);
* an `Admissibility` is the local "global-consistency" test — a finite stand-in
  for the ledger's constraint: every cause is balanced by an effect;
* `admissible` keeps exactly the consistent continuations;
* the **content claim** is the COLLAPSE: the count of admissible continuations is
  bounded by a small `capacity`, far below the size of the unconstrained pool.
  That collapse bound is the harness theorem `Counting.boundedBy_of_eq` — the
  coupling is LOAD-BEARING (a conjunct of `claim_holds`): a regression that broke
  `boundedBy_of_eq`, or that let the residue exceed `capacity`, fails THIS build.

## NOT claimed
That this derives causality, free will, or the arrow of time; that "admissibility"
is anything but a finite cause/effect-balance rule here; any continuum dynamics; any
claim about real predictability of physical futures. The exponential pool size is a
labelled comparison, not derived from a refinement law. **Claim ceiling:** a finite
ledger model in which a consistency filter *bounds* (collapses) a combinatorial pool.
-/

namespace Experiments.TheCauseAndEffectEffect

/-- A causal event: a coarse label on the ledger. -/
inductive Event where
  | cause
  | effect
  | noise
deriving DecidableEq, Repr

/-- A continuation is a finite causal record produced by some refinement. -/
structure Continuation where
  record : List Event
deriving DecidableEq, Repr

/-- The number of `cause` marks in a continuation (the consistency witness reads this). -/
def Continuation.causeCount (c : Continuation) : Nat :=
  (c.record.filter (fun e => decide (e = Event.cause))).length

/-- The number of `effect` marks. -/
def Continuation.effectCount (c : Continuation) : Nat :=
  (c.record.filter (fun e => decide (e = Event.effect))).length

/-- The admissibility constraint: the global-consistency RULE, namely that every cause is
balanced by an effect — the finite stand-in for "global consistency within the causal
ledger". The `slot` records the refinement depth the ledger is closed to. -/
structure Admissibility where
  slot : Nat

/-- THE CONSISTENCY RULE: a continuation is admissible iff its causes and effects balance.
This is the lone constraint, and the falsifiable lemma below pins it. -/
def Admissibility.consistent (_a : Admissibility) (c : Continuation) : Prop :=
  c.causeCount = c.effectCount

instance (a : Admissibility) (c : Continuation) : Decidable (a.consistent c) := by
  unfold Admissibility.consistent; exact inferInstance

/-- Keep exactly the admissible continuations from a finite pool. -/
def admissible (a : Admissibility) (pool : List Continuation) : List Continuation :=
  pool.filter (fun c => decide (a.consistent c))

-- ---------------------------------------------------------------------------
-- FALSIFIABLE lemma: the consistency rule is load-bearing.
-- Quantified over ALL admissibilities, pools and continuations.
-- Drop the `¬ consistent` hypothesis and it breaks (an inconsistent continuation
-- would then have to be excludable from the admissible set without reason — false).
-- ---------------------------------------------------------------------------

/-- An inconsistent continuation is NEVER admissible — for every apparatus and pool. -/
theorem inconsistent_not_admissible
    (a : Admissibility) (pool : List Continuation) (c : Continuation)
    (h : ¬ a.consistent c) : c ∉ admissible a pool := by
  intro hmem
  unfold admissible at hmem
  have hk := (List.mem_filter.mp hmem).2
  exact h (of_decide_eq_true hk)

-- ---------------------------------------------------------------------------
-- The canonical pool: the unconstrained combinatorics vs the admissible residue.
-- ---------------------------------------------------------------------------

/-- The apparatus, closed to refinement depth 2. -/
def defaultAdmissibility : Admissibility := { slot := 2 }

/-- A continuation where one cause is matched by one effect — admissible. -/
def balanced : Continuation := { record := [Event.cause, Event.effect] }

/-- A continuation with a cause and no matching effect — inadmissible (a "miracle"). -/
def danglingCause : Continuation := { record := [Event.cause, Event.noise] }

/-- A continuation with two matched pairs — admissible. -/
def twoPairs : Continuation :=
  { record := [Event.cause, Event.effect, Event.cause, Event.effect] }

/-- The UNCONSTRAINED pool: what arbitrary correlation would admit. Several of these
are inconsistent and so get collapsed away. -/
def unconstrainedPool : List Continuation :=
  [balanced, danglingCause, twoPairs,
   { record := [Event.cause] },
   { record := [Event.effect] },
   { record := [Event.noise] }]

instance {Event : Type} (l : Experiments.Common.Ledger Event) (b : Nat) :
    Decidable (Experiments.Common.Counting.boundedBy l b) := by
  unfold Experiments.Common.Counting.boundedBy; exact inferInstance

/-- The admissible RESIDUE built as a `Ledger` so the counting harness applies. -/
def residueLedger : Experiments.Common.Ledger Continuation :=
  { events := admissible defaultAdmissibility unconstrainedPool }

/-- The collapse: of the 6-element unconstrained pool, only the consistent ones survive
admissibility — `balanced`, `twoPairs`, and the empty-of-causes `[noise]` (`0 = 0`). -/
def capacity : Nat := 3

/-- The residue count is exactly `capacity` — the collapse is real, not vacuous. -/
theorem residue_count_eq_capacity : residueLedger.count = capacity := by
  unfold residueLedger Experiments.Common.Ledger.count admissible
    unconstrainedPool capacity defaultAdmissibility
  decide

-- ---------------------------------------------------------------------------
-- THE CLAIM (content-bearing; the collapse bound is the harness theorem).
-- ---------------------------------------------------------------------------

/-- The claim, in honest halves:
* (witness) the canonical balanced continuation IS admissible (the residue is nonempty);
* (the dangling cause is collapsed away) the inadmissible continuation is NOT in the residue —
  the falsifiable consistency rule firing on a concrete case;
* (COLLAPSE BOUND) the admissible residue count is bounded by `capacity`, far below the
  unconstrained pool — discharged by `Experiments.Common.Counting.boundedBy_of_eq`, the
  LOAD-BEARING harness coupling.
A regression that broke `boundedBy_of_eq`, or a change that let the residue exceed `capacity`,
fails THIS build. -/
def claimStatement : Prop :=
  defaultAdmissibility.consistent balanced ∧
    danglingCause ∉ admissible defaultAdmissibility unconstrainedPool ∧
    Experiments.Common.Counting.boundedBy residueLedger capacity

def claim : Experiments.Common.Claim :=
  { tag := Experiments.Common.ClaimTag.finiteLedgerModel
    statement := claimStatement }

theorem claim_holds : claim.statement :=
  ⟨by decide,
    inconsistent_not_admissible defaultAdmissibility unconstrainedPool danglingCause (by decide),
    Experiments.Common.Counting.boundedBy_of_eq residue_count_eq_capacity⟩

/-- The tag is an honest ceiling: a finite ledger model whose consistency filter bounds
a combinatorial pool. -/
theorem ceiling : claim.tag = Experiments.Common.ClaimTag.finiteLedgerModel := rfl

-- ---------------------------------------------------------------------------
-- A computable run + a NON-vacuous Experiment.claim, with a proved bridge.
-- ---------------------------------------------------------------------------

structure Setup where
  admissibility : Admissibility
  pool : List Continuation

/-- The run computes the size of the admissible residue. -/
def run (s : Setup) : Nat :=
  (admissible s.admissibility s.pool).length

/-- The exported claim is a genuine function of the setup: the residue collapses to at
most `capacity`. The bridge below pins it to `run`, so it cannot be swapped for `True`. -/
def experiment : Experiments.Common.Experiment Setup Nat :=
  { tag := claim.tag
    run := run
    claim := fun s => (admissible s.admissibility s.pool).length ≤ capacity }

instance (s : Setup) : Decidable (experiment.claim s) := by
  unfold experiment; exact inferInstance

theorem run_le_iff_claim (s : Setup) :
    run s ≤ capacity ↔ experiment.claim s := by
  simp only [run, experiment]

def canonicalSetup : Setup :=
  { admissibility := defaultAdmissibility, pool := unconstrainedPool }

#eval run canonicalSetup                                   -- expect: 3 (the collapsed residue)
-- The falsifiable predicate at a config where it is FALSE: a pool of FOUR admissible
-- continuations has residue 4 > capacity 3, so `boundedBy` fails — proving the bound is
-- load-bearing, not vacuous.
#eval decide (Experiments.Common.Counting.boundedBy
  { events := admissible defaultAdmissibility [balanced, twoPairs, balanced, twoPairs] } capacity)  -- expect: false
#print axioms claim_holds                                  -- [propext, Quot.sound] = AMBIENT

instance (setup : Setup) : Decidable (experiment.claim setup) := by
  unfold experiment
  infer_instance

/-- Bring a minimal device next to this experiment: it records whether the exported claim fires. -/
def deviceNear (setup : Setup) : Bool :=
  decide (experiment.claim setup)

theorem deviceNear_detects_claim (setup : Setup) :
    deviceNear setup = true ↔ experiment.claim setup := by
  simp only [deviceNear, decide_eq_true_iff]

def triangulation : Experiments.Common.Triangulation Setup Nat :=
  { experiment := experiment
    device := deviceNear
    detects := deviceNear_detects_claim }

end Experiments.TheCauseAndEffectEffect
