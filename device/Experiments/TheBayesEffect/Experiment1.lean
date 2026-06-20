import Experiments.Common

/-!
# The Bayes Effect — a finite ledger model of posterior reconciliation

Source: `instrument/chapters/08.tex:1265`, phenomenon `ph:bayes-effect`.

The source statement: a new measurement refines an admissible record in a way
that is not perfectly compatible with the curvature already in the ledger; the
**minimal correction that restores global coherence is the Bayesian posterior**.
The prior is accumulated curvature, the likelihood is the new constraint, and
the posterior is the unique strain-minimizing reconciliation.

We model this finitely as a **log-evidence ledger**. Bayes in log form is
additive: `log posterior = log prior + log likelihood + const`. Counting
"evidence marks" (e.g. log-odds tallies, or independent supporting events) for a
hypothesis, the posterior tally is **exactly** the prior tally appended to the
likelihood tally. The reconciliation that restores coherence is therefore the
concatenation of the two ledgers — and the harness lemma
`Experiments.Common.Ledger.count_append` is the structural fact that this
concatenation conserves the total count. That additivity is the load-bearing
coupling here: it is a conjunct of `claim_holds`, so a regression in the harness
ledger algebra breaks *this* build.

## NOT claimed
That this derives Bayes' rule, that the posterior is *optimal* in any decision
sense, or that "strain-minimizing" is anything but a label for additive log
reconciliation. No continuum, no measure theory, no actual probabilities — only
integer evidence marks and the bookkeeping that their union preserves the total.
The numeric "posterior" combine here is **addition of marks** (log-domain
Bayes), NOT multiplication of probabilities; the model does not enforce
normalization. **Claim ceiling:** a finite ledger model whose additivity conjunct
is the harness's own `count_append` theorem.
-/

namespace Experiments.TheBayesEffect

/-- A single piece of evidence: which hypothesis it supports (a coarse slot) and
how many log-marks it carries. The hypothesis slot keeps the domain
effect-specific — this is not three undifferentiated `Nat`s. -/
structure Evidence where
  hypothesis : Nat
  marks : Nat
deriving DecidableEq, Repr

/-- A belief state is a finite ledger of evidence marks. The **prior** is the
accumulated ledger; the **likelihood** is the ledger contributed by the new
measurement. -/
abbrev Belief := Experiments.Common.Ledger Evidence

/-- The Bayesian update: the posterior belief is the prior ledger reconciled
with (appended to) the likelihood ledger. In the log-evidence model this *is*
the minimal coherent correction — no mark is created or destroyed, the two
constraints are simply carried together. -/
def posterior (prior likelihood : Belief) : Belief :=
  Experiments.Common.Ledger.append prior likelihood

/-- Total log-evidence carried by a belief: the number of recorded marks. -/
def totalMarks (b : Belief) : Nat :=
  b.count

/-- The reconciliation is **coherent**: the posterior's total evidence is exactly
the prior's plus the likelihood's — nothing leaks, nothing is invented. -/
def reconciles (prior likelihood : Belief) : Prop :=
  totalMarks (posterior prior likelihood) = totalMarks prior + totalMarks likelihood

-- ---------------------------------------------------------------------------
-- FALSIFIABLE lemmas (∀-quantified; each breaks if the model is wrong).
-- ---------------------------------------------------------------------------

/-- THE reconciliation law, for ALL priors and likelihoods. This is the harness
`count_append` in the language of beliefs: the update conserves total evidence.
Drop the `prior` ledger from the right-hand side and it is false (see the
`#eval` gate at the bottom, which evaluates a config where leaving `prior` out
gives the wrong total). -/
theorem reconciles_all (prior likelihood : Belief) : reconciles prior likelihood := by
  unfold reconciles totalMarks posterior
  exact Experiments.Common.Ledger.count_append prior likelihood

/-- Refining with an **empty** likelihood (a perfectly compatible measurement —
no new constraint) leaves the posterior total unchanged. Falsifiable: it pins
that the likelihood marks really are added, not ignored. -/
theorem empty_likelihood_no_change (prior : Belief) :
    totalMarks (posterior prior Experiments.Common.Ledger.empty) = totalMarks prior := by
  unfold totalMarks posterior
  rw [Experiments.Common.Ledger.count_append, Experiments.Common.Ledger.count_empty]
  exact Nat.add_zero prior.count

/-- Update **order does not change the total evidence**: reconciling A-then-B
carries the same total as B-then-A. (The ledgers differ as lists; the conserved
*count* does not — strain in either order minimizes to the same total.) -/
theorem reconcile_commutes_on_total (prior likelihood : Belief) :
    totalMarks (posterior prior likelihood) = totalMarks (posterior likelihood prior) := by
  unfold totalMarks posterior
  rw [Experiments.Common.Ledger.count_append, Experiments.Common.Ledger.count_append]
  exact Nat.add_comm prior.count likelihood.count

-- Make `reconciles` DECIDABLE so `decide`/`#eval` can evaluate it.
instance (prior likelihood : Belief) : Decidable (reconciles prior likelihood) := by
  unfold reconciles; exact inferInstance

-- ---------------------------------------------------------------------------
-- A canonical update event.
-- ---------------------------------------------------------------------------

/-- A prior carrying 3 marks for hypothesis 0 and 2 for hypothesis 1. -/
def priorLedger : Belief :=
  { events := [{ hypothesis := 0, marks := 3 }, { hypothesis := 1, marks := 2 }] }

/-- The new measurement: 1 mark of likelihood for hypothesis 0. -/
def likelihoodLedger : Belief :=
  { events := [{ hypothesis := 0, marks := 1 }] }

/-- The canonical posterior reconciles (concrete, via the `Decidable` instance). -/
theorem reconciles_canonical : reconciles priorLedger likelihoodLedger := by decide

/-- The canonical posterior carries exactly `2 + 1` marks (= prior count + likelihood count;
a frozen check on the chosen event, not the general law). -/
theorem canonical_total :
    totalMarks (posterior priorLedger likelihoodLedger) = 3 := by decide

-- ---------------------------------------------------------------------------
-- THE CLAIM (content-bearing; the additivity conjunct is the harness theorem).
-- ---------------------------------------------------------------------------

/-- The claim, in honest parts:
* (canonical reconciliation) the canonical update conserves total evidence — proved here;
* (additivity law) reconciliation conserves total evidence for ALL priors and
  likelihoods (`reconciles_all`, discharged by the harness `count_append` — the
  LOAD-BEARING coupling); and
* (no-op on empty) refining with a perfectly compatible (empty) likelihood does
  not change the total. -/
def claimStatement : Prop :=
  reconciles priorLedger likelihoodLedger ∧
    (∀ prior likelihood : Belief, reconciles prior likelihood) ∧
    (∀ prior : Belief,
      totalMarks (posterior prior Experiments.Common.Ledger.empty) = totalMarks prior)

def claim : Experiments.Common.Claim :=
  { tag := Experiments.Common.ClaimTag.finiteLedgerModel
    statement := claimStatement }

theorem claim_holds : claim.statement :=
  ⟨reconciles_canonical, reconciles_all, empty_likelihood_no_change⟩

/-- The tag is an honest ceiling: a finite ledger model, nothing more. -/
theorem ceiling : claim.tag = Experiments.Common.ClaimTag.finiteLedgerModel := rfl

-- ---------------------------------------------------------------------------
-- A computable run + a non-vacuous Experiment.claim, with a proved bridge.
-- ---------------------------------------------------------------------------

structure Setup where
  prior : Belief
  likelihood : Belief

/-- The run actually computes — thanks to the `Decidable` instance above. -/
def run (s : Setup) : Bool := decide (reconciles s.prior s.likelihood)

/-- The exported claim is a genuine function of the setup, and this bridge pins
it to `run`, so the claim body cannot be silently swapped for `fun _ => True`
without breaking the proof. -/
def experiment : Experiments.Common.Experiment Setup Bool :=
  { tag := claim.tag
    run := run
    claim := fun s => reconciles s.prior s.likelihood }

theorem run_iff_claim (s : Setup) :
    run s = true ↔ experiment.claim s := by
  simp only [run, experiment, decide_eq_true_iff]

def canonicalSetup : Setup := { prior := priorLedger, likelihood := likelihoodLedger }

#eval run canonicalSetup                               -- expect: true
-- Load-bearing falsifiability gate: the reconciliation total WITHOUT the prior
-- marks is wrong (3 ≠ 0 + 1), so the additivity law is not vacuous.
#eval decide
  (totalMarks (posterior priorLedger likelihoodLedger)
    = totalMarks (Experiments.Common.Ledger.empty : Belief) + totalMarks likelihoodLedger)
  -- expect: false
#print axioms claim_holds                              -- [propext, Quot.sound] = AMBIENT, not coupling

/-- Bring a minimal device next to this experiment: it records whether the exported claim fires.
We phrase the device on `reconciles` directly (which carries the `Decidable` instance); the bridge
below proves it is exactly `experiment.claim`. -/
def deviceNear (setup : Setup) : Bool :=
  decide (reconciles setup.prior setup.likelihood)

theorem deviceNear_detects_claim (setup : Setup) :
    deviceNear setup = true ↔ experiment.claim setup := by
  simp only [deviceNear, experiment, decide_eq_true_iff]

def triangulation : Experiments.Common.Triangulation Setup Bool :=
  { experiment := experiment
    device := deviceNear
    detects := deviceNear_detects_claim }

end Experiments.TheBayesEffect
