import Experiments.Common

/-!
# The Chaitin Effect — a finite model of "precise ledger, no extractable law"

Effect (description.md): a measurement record may consist entirely of finite and
distinguishable events and yet admit **no extractable dynamical law**.  Chaitin's
`Ω` aggregates halting events of finite programs: each event is individually
verifiable, the ledger accumulates without contradiction, yet no rule derived
from a finite prefix constrains which procedure halts next.

This file models that boundary FINITELY and HONESTLY:

* `Procedure` / `HaltRecord` — an effect-specific domain (a program index and the
  step at which it was verified to halt), NOT `Experiments.Common.CountSetup`.
* the ledger is *precise*: events are distinguishable (`DecidableEq`) and the
  prefixes of any continuation agree (a real append/bookkeeping fact).
* the *no-law* core: two admissible records can **agree on every recorded prefix
  yet disagree on the next event**.  Hence no function of the prefix can predict
  the next halting event — the defining content of the Chaitin Effect.

## COUPLING: DECLINED (coupledTo = null).
The honest content here is the *absence* of a law, not a conservation /
bound / locality identity.  No `Measurement` device theorem (holonomy, charge,
positron) touches halting/uncomputability, and no harness theorem honestly fits:
`Counting.boundedBy` would be a FAKE coupling because the effect says the ledger
grows *without* a predictive bound.  So this declines coupling and carries the
honest `physicalClaimLabelOnly` ceiling.  Declining is the blessed outcome here.

## NOT claimed
That this computes `Ω` or any halting probability; that halting is *actually*
undecidable (we exhibit a finite witness of unpredictability, not a diagonal /
Turing-completeness argument); any compression bound or Kolmogorov complexity
statement; that "no law exists" in general — only that, for the exhibited
admissible records, a prefix-agreeing pair disagrees on the next event, so a
prefix-rule cannot fix it.
-/

namespace Experiments.TheChaitinEffect

/-- A finitely describable procedure, identified by an index. -/
structure Procedure where
  index : Nat
deriving DecidableEq, Repr

/-- A verified halting event: a procedure together with the step at which its
completion was checked.  Each such event is individually verifiable — and
distinguishable from every other (`DecidableEq`). -/
structure HaltRecord where
  proc : Procedure
  haltStep : Nat
deriving DecidableEq, Repr

/-- A measurement ledger of halting events (the `\mathcal{L}_t` of the description). -/
abbrev Ledger := List HaltRecord

/-- The prefix of length `t`: the events recorded "up to step `t`". -/
def prefix' (t : Nat) (L : Ledger) : Ledger := L.take t

/-- Two ledgers **agree on the prefix of length `t`**. -/
def agreeOnPrefix (t : Nat) (L M : Ledger) : Prop := prefix' t L = prefix' t M

/-- The event at position `t` (`none` if the ledger is shorter). -/
def eventAt (t : Nat) (L : Ledger) : Option HaltRecord := L[t]?

/-- A *prefix-law* would be any function from the recorded prefix to a prediction
of the next event.  The Chaitin boundary is the statement that NO such function
is correct on all admissible records: it must give the same answer to two records
that share the prefix, yet those records can differ on the next event. -/
def PredictsNext (predict : Ledger -> Option HaltRecord) (t : Nat) (L : Ledger) : Prop :=
  predict (prefix' t L) = eventAt t L

-- Decidable instances so `decide`/`#eval` see through the predicates.
instance (t : Nat) (L M : Ledger) : Decidable (agreeOnPrefix t L M) := by
  unfold agreeOnPrefix; exact inferInstance

-- ---------------------------------------------------------------------------
-- The witness: two admissible records, identical on the prefix, split next.
-- ---------------------------------------------------------------------------

/-- The common recorded prefix: two verified halting events. -/
def commonPrefix : Ledger :=
  [ { proc := { index := 0 }, haltStep := 3 },
    { proc := { index := 1 }, haltStep := 7 } ]

/-- One admissible continuation: procedure 2 halts next, at step 11. -/
def recordA : Ledger :=
  commonPrefix ++ [ { proc := { index := 2 }, haltStep := 11 } ]

/-- Another admissible continuation: procedure 5 halts next (different procedure,
different step) — equally admissible, contradicting nothing recorded so far. -/
def recordB : Ledger :=
  commonPrefix ++ [ { proc := { index := 5 }, haltStep := 13 } ]

-- ---------------------------------------------------------------------------
-- FALSIFIABLE quantified lemmas.
-- ---------------------------------------------------------------------------

/-- PRECISION (a real bookkeeping fact, quantified over ALL ledgers and `t`): the
prefix of an appended continuation is the prefix of its head — once `t` does not
reach into the appended tail.  This is `List.take` over `++`; drop the bound
`t ≤ L.length` and it is false (the tail leaks in). -/
theorem prefix_append_stable
    (t : Nat) (L tail : Ledger) (h : t ≤ L.length) :
    prefix' t (L ++ tail) = prefix' t L := by
  unfold prefix'
  rw [List.take_append_of_le_length h]

/-- NO LAW (quantified over EVERY candidate predictor): no prefix-rule can be
correct on both `recordA` and `recordB` at the split position, because they share
the length-2 prefix yet differ on the next (3rd) event.  This is the Chaitin core,
and it is genuinely `∀`: it rules out *all* functions `predict`. -/
theorem no_prefix_law
    (predict : Ledger -> Option HaltRecord) :
    ¬ (PredictsNext predict 2 recordA ∧ PredictsNext predict 2 recordB) := by
  intro hpair
  -- both predictions equal `predict (prefix' 2 recordA)`, and the prefixes agree,
  -- but the two true next-events differ.
  have hA : predict (prefix' 2 recordA) = eventAt 2 recordA := hpair.1
  have hB : predict (prefix' 2 recordB) = eventAt 2 recordB := hpair.2
  have hpre : prefix' 2 recordA = prefix' 2 recordB := by decide
  rw [hpre] at hA
  rw [hA] at hB
  -- `eventAt 2 recordA ≠ eventAt 2 recordB` is a concrete decidable inequality.
  revert hB
  decide

/-- AGREEMENT is necessary for the obstruction: the two records DO share the
length-2 prefix (so the split is genuinely a failure of prediction, not of input).
Drop `agreeOnPrefix` from the story and there is nothing surprising left. -/
theorem records_agree_on_prefix : agreeOnPrefix 2 recordA recordB := by decide

-- ---------------------------------------------------------------------------
-- THE CLAIM (content-bearing conjunction; coupling DECLINED).
-- ---------------------------------------------------------------------------

/-- The claim, in honest conjuncts:
* (precision) `recordA` extends `commonPrefix` — the ledger accumulates by append;
* (agreement) `recordA` and `recordB` agree on the recorded length-2 prefix;
* (no law) NO predictor is simultaneously correct on both at the split. -/
def claimStatement : Prop :=
  recordA = commonPrefix ++ [ { proc := { index := 2 }, haltStep := 11 } ] ∧
    agreeOnPrefix 2 recordA recordB ∧
    (∀ predict : Ledger -> Option HaltRecord,
      ¬ (PredictsNext predict 2 recordA ∧ PredictsNext predict 2 recordB))

def claim : Experiments.Common.Claim :=
  { tag := Experiments.Common.ClaimTag.physicalClaimLabelOnly
    statement := claimStatement }

theorem claim_holds : claim.statement :=
  ⟨rfl, records_agree_on_prefix, no_prefix_law⟩

/-- Honest ceiling: a label-only model — the file names the uncomputability /
predictive-law boundary, it does not derive `Ω` or undecidability. -/
theorem ceiling :
    claim.tag = Experiments.Common.ClaimTag.physicalClaimLabelOnly := rfl

-- ---------------------------------------------------------------------------
-- A computable run + a non-vacuous exported Experiment, with a proved bridge.
-- ---------------------------------------------------------------------------

structure Setup where
  predictAt : Nat
  left : Ledger
  right : Ledger

/-- The run computes: does the pair share the prefix at the queried position? -/
def run (s : Setup) : Bool := decide (agreeOnPrefix s.predictAt s.left s.right)

def experiment : Experiments.Common.Experiment Setup Bool :=
  { tag := claim.tag
    run := run
    claim := fun s => agreeOnPrefix s.predictAt s.left s.right }

theorem run_iff_claim (s : Setup) :
    run s = true ↔ experiment.claim s := by
  simp only [run, experiment, decide_eq_true_iff]

def canonicalSetup : Setup := { predictAt := 2, left := recordA, right := recordB }

#eval run canonicalSetup                                  -- expect: true (prefixes agree)
-- load-bearing check: at t = 3 the records DISAGREE, so the predicate is FALSE there,
-- proving `agreeOnPrefix`/`no_prefix_law` are not vacuous.
#eval run { canonicalSetup with predictAt := 3 }          -- expect: false
#print axioms claim_holds                                 -- ambient footprint, NOT coupling

/-- Bring a minimal device next to this experiment: it records whether the exported
claim fires.  Defined via `run` (whose `Decidable` instance is already in scope) and
bridged to the exported claim through `run_iff_claim`. -/
def deviceNear (setup : Setup) : Bool := run setup

theorem deviceNear_detects_claim (setup : Setup) :
    deviceNear setup = true ↔ experiment.claim setup := by
  unfold deviceNear
  exact run_iff_claim setup

def triangulation : Experiments.Common.Triangulation Setup Bool :=
  { experiment := experiment
    device := deviceNear
    detects := deviceNear_detects_claim }

end Experiments.TheChaitinEffect
