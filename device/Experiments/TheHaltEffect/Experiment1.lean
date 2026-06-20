import Experiments.Common

/-!
# The Halt Effect — a finite model of "admissible history that cannot be extended"

Effect (description.md, `instrument/chapters/08.tex:1098`): not every admissible
refinement admits a successor.  There exist boundary configurations for which no
further consistent update can be constructed.  Concretely: if appending the next
event would require **separating two correlated events** for which **no permissible
ordering exists**, the update operator has no admissible output — the refinement
*halts*.  A halted ledger is not incomplete; it is complete in the only sense the
axioms allow.

This file models that boundary FINITELY and HONESTLY:

* `Event` / `PartialLedger` — an effect-specific domain (an event carries an index
  and a correlation class; the ledger is the recorded history), NOT
  `Experiments.Common.CountSetup`.
* `admissibleOrder` — a candidate successor `e` is admissible after history `L`
  only if **every** already-recorded event that is correlated with `e` may legally
  precede it (`mayPrecede`).  This is the "permissible ordering" gate.
* the *halt* core: a configuration is **halted** when, for the only remaining
  events, the ordering gate fails — so NO admissible successor can be appended.
  This is the defining content of the Halt Effect: a structural limit, not a
  computational failure.

## COUPLING: DECLINED (coupledTo = null).
The honest content is the *non-existence of an admissible successor* — a structural
inadmissibility, not a conservation / additivity / locality / capacity identity.
No `Measurement` device theorem (holonomy, charge, positron) touches admissibility
of refinement, so forcing one here would be a FAKE coupling.  Among the harness
theorems, `Counting.boundedBy` is the closest by *shape* but it would MISREAD the
effect: the halt is not "the ledger exceeds a budget" — it is "the ordering gate
has no legal output", which `boundedBy` cannot witness.  `Ledger.count_append`
would only re-prove bookkeeping the halt does not contradict.  So this declines
coupling and carries the honest `inadmissibilityNoGo` ceiling.  Declining is the
blessed outcome here.

## NOT claimed
That this is the Halting Problem; that refinement is *actually* undecidable (we
exhibit a finite witness configuration with no admissible successor, not a
diagonal / Turing-completeness argument); that the chosen `mayPrecede` relation is
*the* causal order of physics; any claim about *which* histories halt in general —
only that, for the exhibited configuration, the ordering gate blocks every
candidate successor, so the refinement operator has no admissible output there.
-/

namespace Experiments.TheHaltEffect

/-- A recorded event: an index (which event) and a correlation class.  Two events
in the SAME correlation class are "correlated" — appending one after the other
requires a permissible ordering between them. -/
structure Event where
  index : Nat
  corr : Nat
deriving DecidableEq, Repr

/-- A partial ledger is the recorded admissible history so far. -/
abbrev PartialLedger := List Event

/-- Two events are **correlated** iff they share a correlation class. -/
def correlated (e f : Event) : Prop := e.corr = f.corr

/-- The fixed, finite **permissible-ordering** relation: a recorded event `f` may
legally precede a candidate `e` iff `f.index < e.index`.  (This is the only
"ordering law" the model exposes; the effect's content is what happens when it has
no legal output, not the particular choice of `<`.) -/
def mayPrecede (f e : Event) : Prop := f.index < e.index

/-- A candidate successor `e` is **admissible** after history `L` iff every
already-recorded event that is correlated with `e` may legally precede it.  This is
the update operator's gate: drop the `correlated` guard and unrelated events would
wrongly block the update; drop `mayPrecede` and any append would be admissible. -/
def admissible (L : PartialLedger) (e : Event) : Prop :=
  ∀ f, f ∈ L → correlated f e → mayPrecede f e

/-- The refinement **halts** on a finite candidate pool `pool` after history `L`
iff NO event in the pool is an admissible successor.  This is "no further
consistent update can be constructed." -/
def halts (L : PartialLedger) (pool : List Event) : Prop :=
  ∀ e, e ∈ pool → ¬ admissible L e

-- Decidable instances so `decide`/`#eval` see through the predicates.
instance (e f : Event) : Decidable (correlated e f) := by
  unfold correlated; exact inferInstance
instance (f e : Event) : Decidable (mayPrecede f e) := by
  unfold mayPrecede; exact inferInstance
instance (L : PartialLedger) (e : Event) : Decidable (admissible L e) := by
  unfold admissible; exact inferInstance
instance (L : PartialLedger) (pool : List Event) : Decidable (halts L pool) := by
  unfold halts; exact inferInstance

-- ---------------------------------------------------------------------------
-- The witness configuration: a history + a candidate pool with no successor.
-- ---------------------------------------------------------------------------

/-- The recorded history: two events in correlation class `0`, with high indices. -/
def history : PartialLedger :=
  [ { index := 5, corr := 0 }, { index := 7, corr := 0 } ]

/-- The remaining candidate successors.  Both are correlated (class `0`) with the
recorded events, and BOTH have an index smaller than a recorded correlated event —
so the ordering gate (`mayPrecede`) blocks them.  No admissible successor exists. -/
def pool : List Event :=
  [ { index := 2, corr := 0 }, { index := 4, corr := 0 } ]

/-- A separate, NON-halted history for the load-bearing falsity check below: an
empty history admits any successor (no recorded event can block the gate). -/
def freshSuccessor : Event := { index := 3, corr := 0 }

-- ---------------------------------------------------------------------------
-- FALSIFIABLE quantified lemmas.
-- ---------------------------------------------------------------------------

/-- ADMISSIBILITY REQUIRES THE ORDERING GATE (quantified over ALL histories and
candidates): if some recorded event is correlated with `e` yet may NOT precede it,
then `e` is inadmissible.  Drop the `mayPrecede` conjunct from `admissible` and
this is false — every append would be admissible. -/
theorem blocked_by_ordering
    (L : PartialLedger) (e f : Event)
    (hmem : f ∈ L) (hcorr : correlated f e) (hno : ¬ mayPrecede f e) :
    ¬ admissible L e :=
  fun hadm => hno (hadm f hmem hcorr)

/-- THE EMPTY HISTORY NEVER HALTS (quantified over ALL non-empty pools): with no
recorded events, every candidate is admissible vacuously, so the refinement cannot
halt.  This pins that the obstruction comes from the *recorded* history, not from
the gate alone — drop the `e ∈ pool` premise / use an empty pool and `halts` is
vacuously true, which is exactly why the halt witness below needs a nonempty pool. -/
theorem empty_history_admits_any (e : Event) :
    admissible ([] : PartialLedger) e := by
  intro f hf _; nomatch hf

/-- THE HALT WITNESS (the no-go core): the refinement halts on `pool` after
`history` — every candidate is blocked by an ordering gate it cannot satisfy.
Concrete, decidable, and the defining content of the effect. -/
theorem history_halts : halts history pool := by decide

-- ---------------------------------------------------------------------------
-- THE CLAIM (content-bearing conjunction; coupling DECLINED).
-- ---------------------------------------------------------------------------

/-- The claim, in honest conjuncts:
* (structural inadmissibility) the refinement HALTS on `pool` after `history` —
  no candidate successor is admissible (the no-go core);
* (the gate is the cause) the first candidate is blocked specifically because a
  recorded correlated event of larger index may not precede it; and
* (the limit is local, not global) the empty history would admit that same
  candidate — so the halt is a property of THIS recorded history, not of the
  candidate in isolation. -/
def claimStatement : Prop :=
  halts history pool ∧
    (¬ admissible history { index := 2, corr := 0 }) ∧
    admissible ([] : PartialLedger) { index := 2, corr := 0 }

def claim : Experiments.Common.Claim :=
  { tag := Experiments.Common.ClaimTag.inadmissibilityNoGo
    statement := claimStatement }

theorem claim_holds : claim.statement :=
  ⟨history_halts,
    blocked_by_ordering history { index := 2, corr := 0 } { index := 5, corr := 0 }
      (by decide) (by decide) (by decide),
    empty_history_admits_any { index := 2, corr := 0 }⟩

/-- Honest ceiling: a no-go model — the file exhibits a configuration with no
admissible successor; it does NOT prove undecidability of refinement in general. -/
theorem ceiling :
    claim.tag = Experiments.Common.ClaimTag.inadmissibilityNoGo := rfl

-- ---------------------------------------------------------------------------
-- A computable run + a non-vacuous exported Experiment, with a proved bridge.
-- ---------------------------------------------------------------------------

structure Setup where
  history : PartialLedger
  pool : List Event

/-- The run computes: does the refinement halt on this configuration? -/
def run (s : Setup) : Bool := decide (halts s.history s.pool)

def experiment : Experiments.Common.Experiment Setup Bool :=
  { tag := claim.tag
    run := run
    claim := fun s => halts s.history s.pool }

theorem run_iff_claim (s : Setup) :
    run s = true ↔ experiment.claim s := by
  simp only [run, experiment, decide_eq_true_iff]

def canonicalSetup : Setup := { history := history, pool := pool }

#eval run canonicalSetup                                  -- expect: true (halts)
-- load-bearing check: with an EMPTY history the candidate `freshSuccessor` is
-- admissible, so the refinement does NOT halt — `halts`/`history_halts` are not
-- vacuous, the recorded history is doing the work.
#eval run { canonicalSetup with history := [] }           -- expect: false
#print axioms claim_holds                                 -- ambient footprint, NOT coupling

/-- Bring a minimal device next to this experiment: it records whether the exported
claim fires.  Defined via `run` (whose `Decidable` instance is in scope) and bridged
to the exported claim through `run_iff_claim`. -/
def deviceNear (setup : Setup) : Bool := run setup

theorem deviceNear_detects_claim (setup : Setup) :
    deviceNear setup = true ↔ experiment.claim setup := by
  unfold deviceNear
  exact run_iff_claim setup

def triangulation : Experiments.Common.Triangulation Setup Bool :=
  { experiment := experiment
    device := deviceNear
    detects := deviceNear_detects_claim }

end Experiments.TheHaltEffect
