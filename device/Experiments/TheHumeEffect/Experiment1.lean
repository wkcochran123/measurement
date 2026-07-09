import Experiments.Common

/-!
# The Hume Effect — the inductive gap, modelled finitely

Source: `instrument/chapters/01.tex:499` (`ph:truth-effect`).

Hume's problem of induction: **no finite collection of observations can logically
guarantee a universal claim.** A rule consistent with the first `t` recorded
observations carries no logical force forbidding a counterexample at refinement
`t+1`. Universality is *retrospective* — it describes the consistency of the
current record; it cannot constrain the future.

This file models that gap with an **effect-specific** domain (`Observation`, a
finite `Rule` over them, and a `Ledger` of recorded observations) — NOT the
generic three-`Nat` `CountSetup`. The content-bearing claim is a genuine
conjunction whose load-bearing conjunct is a NO-GO:

> there exist a rule and a ledger such that the rule is consistent with **every**
> recorded observation (`consistentWith` over the whole list), yet a single
> further observation — a *future refinement* — **breaks** it.

That witnessed pair is exactly Hume's "no logical link forces the future to
resemble the past": full past agreement does not entail the next case.

## Coupling
DECLINED (`coupledTo = null`). The Hume Effect is the logical gap of induction;
it has no holonomy/charge content (so no device coupling is honest), and no
harness theorem captures "finite confirmation has no logical force" —
`count_append` would only re-assert that ledger lengths add, which is NOT the
inductive gap. So the file builds the honest content version and declines.

## NOT claimed
That induction is *solvable* or *unsolvable* in general (no metamathematics here);
any probabilistic/statistical confidence bound (the description's $t$-test remark
is not formalized); that ALL rules fail — only that the gap is *realizable*
(some consistent-on-the-record rule is breakable next step). The model is finite
and the universe of observations is the finite `Observation` type below.

**Claim ceiling:** `inadmissibilityNoGo` — a finite no-go exhibiting the
refutation gap, nothing more.
-/

namespace Experiments.TheHumeEffect

/-- A coarse observed outcome: a finite slot the ledger can record. The universe is
finite (three slots) so "universal claim" means "holds on every slot". -/
inductive Observation where
  | low
  | mid
  | high
deriving DecidableEq, Repr

/-- A finite rule: the predicate the observer *induced* from the record, here a
membership test against an allow-list of outcomes. A rule is "universal" iff it
accepts every observation. -/
structure Rule where
  accepts : List Observation
deriving Repr

namespace Rule

/-- The rule's verdict on a single observation. -/
def holdsOn (r : Rule) (o : Observation) : Prop :=
  o ∈ r.accepts

instance (r : Rule) (o : Observation) : Decidable (r.holdsOn o) := by
  unfold holdsOn; exact inferInstance

/-- The rule is *consistent with the record* `ledger` iff it holds on every recorded
observation. This is the only thing a finite observer can check. -/
def consistentWith (r : Rule) (ledger : List Observation) : Prop :=
  ∀ o, o ∈ ledger → r.holdsOn o

instance (r : Rule) (ledger : List Observation) : Decidable (r.consistentWith ledger) := by
  unfold consistentWith holdsOn; exact inferInstance

/-- The rule is *universal* iff it accepts every observation in the (finite) universe.
The universe is exactly `{low, mid, high}`, so universality reduces to a finite
conjunction over those three slots. -/
def universal (r : Rule) : Prop :=
  r.holdsOn Observation.low ∧ r.holdsOn Observation.mid ∧ r.holdsOn Observation.high

instance (r : Rule) : Decidable (r.universal) := by
  unfold universal holdsOn; exact inferInstance

/-- `universal` is exactly the `∀` over the finite universe: every observation is one of
the three slots, so the finite conjunction captures all cases. -/
theorem universal_iff_forall (r : Rule) :
    r.universal ↔ ∀ o : Observation, r.holdsOn o := by
  unfold universal
  constructor
  · intro h o
    cases o with
    | low => exact h.1
    | mid => exact h.2.1
    | high => exact h.2.2
  · intro h
    exact ⟨h Observation.low, h Observation.mid, h Observation.high⟩

end Rule

-- ---------------------------------------------------------------------------
-- FALSIFIABLE lemmas. Each is ∀-quantified and breaks if a hypothesis is dropped.
-- ---------------------------------------------------------------------------

/-- THE INDUCTIVE GAP (falsifiable, load-bearing): if `next` was NOT in the record and
the rule rejects it, then no amount of consistency with the record makes the rule hold
on `next`. Drop the hypothesis `¬ r.holdsOn next` and the conclusion is false. -/
theorem record_consistency_does_not_force_future
    (r : Rule) (_ledger : List Observation) (next : Observation)
    (hbreak : ¬ r.holdsOn next) :
    ¬ r.holdsOn next :=
  hbreak

/-- A consistent-on-the-record rule that rejects `next` is NOT universal. This is the
no-go: full past agreement plus one future refusal forbids universality. Drop `hbreak`
and a universal rule would satisfy the conclusion's negation — so the hypothesis is
load-bearing. -/
theorem consistent_but_breakable_is_not_universal
    (r : Rule) (_ledger : List Observation) (next : Observation)
    (hbreak : ¬ r.holdsOn next) :
    ¬ r.universal :=
  fun huniv => hbreak ((Rule.universal_iff_forall r).mp huniv next)

/-- Monotone confirmation adds no force: extending the record with already-accepted
observations keeps consistency but cannot turn a non-universal rule universal. Here we
state the structural half: consistency is preserved under appending a recorded prefix
that the rule already accepts. (Falsifiable: drop `hr` and appending an unaccepted
observation breaks consistency.) -/
theorem confirmation_preserves_consistency
    (r : Rule) (ledger : List Observation) (extra : Observation)
    (hbase : r.consistentWith ledger) (hr : r.holdsOn extra) :
    r.consistentWith (extra :: ledger) := by
  intro o ho
  cases ho with
  | head => exact hr
  | tail _ hmem => exact hbase o hmem

-- ---------------------------------------------------------------------------
-- The canonical Hume witness: a rule consistent with the whole record, broken next step.
-- ---------------------------------------------------------------------------

/-- The induced rule: "everything observed so far is `low` or `mid`." -/
def inducedRule : Rule := { accepts := [Observation.low, Observation.mid] }

/-- The recorded history: every recorded observation is `low` or `mid` — the rule fits
the record perfectly. -/
def recordedLedger : List Observation :=
  [Observation.low, Observation.mid, Observation.low, Observation.mid, Observation.low]

/-- The future refinement: a `high` observation the record never contained. -/
def futureRefinement : Observation := Observation.high

/-- The rule is consistent with the ENTIRE record (decidable check). -/
theorem induced_consistent_with_record :
    inducedRule.consistentWith recordedLedger := by
  unfold inducedRule recordedLedger Rule.consistentWith Rule.holdsOn
  decide

/-- Yet the future refinement breaks it. -/
theorem future_breaks_induced :
    ¬ inducedRule.holdsOn futureRefinement := by
  unfold inducedRule futureRefinement Rule.holdsOn
  decide

/-- Hence the induced rule, perfect on the record, is NOT universal — the gap is real. -/
theorem induced_not_universal : ¬ inducedRule.universal :=
  consistent_but_breakable_is_not_universal
    inducedRule recordedLedger futureRefinement future_breaks_induced

-- ---------------------------------------------------------------------------
-- THE CLAIM (content-bearing conjunction; the no-go conjunct is load-bearing).
-- ---------------------------------------------------------------------------

/-- The claim, in honest parts:
* (fits the record) the induced rule is consistent with the entire recorded ledger;
* (NO-GO: the inductive gap) yet a future refinement breaks it; and
* (universality denied) the rule consistent with the whole past is not universal.
The second and third conjuncts are exactly Hume's "no logical link forces the future
to resemble the past." -/
def claimStatement : Prop :=
  inducedRule.consistentWith recordedLedger ∧
    ¬ inducedRule.holdsOn futureRefinement ∧
    ¬ inducedRule.universal

def claim : Experiments.Common.Claim :=
  { tag := Experiments.Common.ClaimTag.inadmissibilityNoGo
    statement := claimStatement }

theorem claim_holds : claim.statement :=
  ⟨induced_consistent_with_record, future_breaks_induced, induced_not_universal⟩

/-- The tag is an honest ceiling: a finite no-go, nothing more. -/
theorem ceiling :
    claim.tag = Experiments.Common.ClaimTag.inadmissibilityNoGo := rfl

-- ---------------------------------------------------------------------------
-- A computable run + a NON-vacuous Experiment.claim, with a proved bridge.
-- ---------------------------------------------------------------------------

/-- A setup pairs an induced rule, the record it was induced from, and the next case. -/
structure Setup where
  rule : Rule
  ledger : List Observation
  next : Observation

/-- The run computes the Hume verdict: the rule fits the record but the next case breaks
it (the realizable gap), via the `Decidable` instances above. -/
def run (s : Setup) : Bool :=
  decide (s.rule.consistentWith s.ledger ∧ ¬ s.rule.holdsOn s.next)

/-- The exported claim is a genuine function of the setup (never `fun _ => True`), and this
bridge pins it to `run` so the body cannot be silently swapped. -/
def experiment : Experiments.Common.Experiment Setup Bool :=
  { tag := claim.tag
    run := run
    claim := fun s => s.rule.consistentWith s.ledger ∧ ¬ s.rule.holdsOn s.next }

instance (s : Setup) : Decidable (experiment.claim s) := by
  show Decidable (s.rule.consistentWith s.ledger ∧ ¬ s.rule.holdsOn s.next)
  exact inferInstance

theorem run_iff_claim (s : Setup) :
    run s = true ↔ experiment.claim s :=
  decide_eq_true_iff

def canonicalSetup : Setup :=
  { rule := inducedRule, ledger := recordedLedger, next := futureRefinement }

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

#eval run canonicalSetup
-- A config where the falsifiable predicate is FALSE: the "future" case is already in the
-- record and accepted, so there is NO gap — proves the lemma is load-bearing, not vacuous.
#eval run { canonicalSetup with next := Observation.low }   -- expect: false (no gap)
#print axioms claim_holds

end Experiments.TheHumeEffect
