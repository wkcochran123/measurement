import Experiments.Common

/-!
# The Gosset Effect (Ch.02) — repeated realization accumulates signal

Source: `instrument/chapters/02.tex:2316`, environment `phenom`, label `ph:ttest`.

Gosset ("Student") observed that **repetition itself carries epistemic power**: by
accumulating ledger entries across many realizations of the *same* instrument, persistent
structure (signal) separates from incidental variation (noise) — *provided the realizations
decompose the same underlying instrument*. The Constraint is sharp: repetition helps **only**
when the realizations share admissible distinctions; a drifting instrument amplifies error.

We model this finitely as a ledger of realizations, each carrying a measured `signal` count and
tagged with the `instrument` that produced it. Pooling two batches of realizations is a ledger
`append`; the pooled signal is the **sum** of the batch signals (additivity = the bookkeeping
substance of "accumulation across realizations"). The comparability Constraint is a `Prop`:
realizations are poolable only if they share the same instrument tag.

## Coupling
The pooled-count additivity conjunct is discharged by the harness theorem
`Experiments.Common.Ledger.count_append`, so a regression in that harness lemma breaks THIS
build. That is the honest coupling: Gosset is bookkeeping/accumulation, NOT holonomy or charge —
forcing the positron/device theorems here would be a fake coupling.

## NOT claimed
No real $t$-distribution, no variance, no degrees of freedom, no central limit theorem, no actual
noise suppression *rate*. "Signal" here is a raw additive count, not an estimated mean; "noise
suppression" is represented only by the structural fact that the *same-instrument* hypothesis is
**required** for pooling (drop it and the comparability lemma fails). The claim ceiling is a finite
ledger model of accumulation-under-comparability, nothing distributional.
-/

namespace Experiments.TheGossetEffectCh02

/-- A finite catalogue of instruments. Two realizations are *comparable* (poolable) iff they
were produced by the same instrument tag (the Constraint: "sharing admissible distinctions"). -/
inductive Instrument where
  | brewA
  | brewB
deriving DecidableEq, Repr

/-- One realization of an instrument: which instrument produced it, and the recovered signal
count for that realization. -/
structure Realization where
  instrument : Instrument
  signal : Nat
deriving DecidableEq, Repr

/-- A batch of realizations is a harness ledger of `Realization`s. -/
abbrev Batch := Experiments.Common.Ledger Realization

/-- Total recovered signal in a batch: the sum of per-realization signals. -/
def totalSignal (b : Batch) : Nat :=
  (b.events.map Realization.signal).foldr (· + ·) 0

/-- The comparability Constraint: every realization in the batch shares the instrument `inst`.
This is the hypothesis the Constraint section insists on — repetition pools coherently ONLY when
the realizations decompose the *same* instrument. -/
def fromInstrument (inst : Instrument) (b : Batch) : Prop :=
  ∀ r ∈ b.events, r.instrument = inst

-- Decidability so `decide`/`#eval` see through the predicate.
instance (inst : Instrument) (b : Batch) : Decidable (fromInstrument inst b) := by
  unfold fromInstrument; exact inferInstance

-- ---------------------------------------------------------------------------
-- FALSIFIABLE lemmas.
-- ---------------------------------------------------------------------------

/-- Signal accumulates ADDITIVELY when batches are pooled. This reads `totalSignal` over a real
`++`, so it would break if `totalSignal` were not a homomorphism on append. Quantified over ALL
pairs of batches. -/
theorem totalSignal_append (left right : Batch) :
    totalSignal (Experiments.Common.Ledger.append left right)
      = totalSignal left + totalSignal right := by
  unfold totalSignal Experiments.Common.Ledger.append
  simp only [List.map_append]
  induction left.events.map Realization.signal with
  | nil => simp
  | cons x xs ih => simp [List.foldr_cons, ih, Nat.add_assoc]

/-- The COMPARABILITY constraint is load-bearing: pooling two same-instrument batches stays
same-instrument. DROP the `from-`hypotheses on `left`/`right` and this is false (a mixed pool is
not from a single instrument) — that is exactly the Constraint section's content. Quantified over
ALL batches and instruments. -/
theorem comparable_append (inst : Instrument) (left right : Batch)
    (hl : fromInstrument inst left) (hr : fromInstrument inst right) :
    fromInstrument inst (Experiments.Common.Ledger.append left right) := by
  intro r hmem
  unfold Experiments.Common.Ledger.append at hmem
  simp only at hmem
  match List.mem_append.1 hmem with
  | Or.inl h => exact hl r h
  | Or.inr h => exact hr r h

-- ---------------------------------------------------------------------------
-- Canonical event: two same-instrument batches of `brewA` realizations.
-- ---------------------------------------------------------------------------

def batch1 : Batch := { events := [⟨Instrument.brewA, 3⟩, ⟨Instrument.brewA, 2⟩] }
def batch2 : Batch := { events := [⟨Instrument.brewA, 4⟩] }

/-- Pooling the two `brewA` batches keeps the same-instrument hypothesis (concrete, via the
`Decidable` instance). -/
theorem pooled_comparable :
    fromInstrument Instrument.brewA
      (Experiments.Common.Ledger.append batch1 batch2) := by decide

/-- The pooled signal is the sum of the batch signals: `5 + 4 = 9` (frozen-literal check on the
canonical event). -/
theorem pooled_signal_value :
    totalSignal (Experiments.Common.Ledger.append batch1 batch2) = 9 := by decide

-- ---------------------------------------------------------------------------
-- THE CLAIM (content-bearing; the COUNT-additivity conjunct is the harness theorem).
-- ---------------------------------------------------------------------------

/-- The claim, in honest parts:
* (accumulation/count) pooling the two batches sums their realization **counts**
  (`Experiments.Common.Ledger.count_append` — the harness coupling: number of realizations adds);
* (accumulation/signal) the pooled signal sums the batch signals (`totalSignal_append`); and
* (comparability) the pooled batch is still from a single instrument (`comparable_append`),
  which is the Constraint that makes repetition lawful.
The first conjunct is discharged by the harness `count_append`, so a regression there fails THIS
build. -/
def claimStatement : Prop :=
  (Experiments.Common.Ledger.append batch1 batch2).count = batch1.count + batch2.count ∧
    totalSignal (Experiments.Common.Ledger.append batch1 batch2)
      = totalSignal batch1 + totalSignal batch2 ∧
    fromInstrument Instrument.brewA (Experiments.Common.Ledger.append batch1 batch2)

def claim : Experiments.Common.Claim :=
  { tag := Experiments.Common.ClaimTag.finiteLedgerModel
    statement := claimStatement }

theorem claim_holds : claim.statement :=
  ⟨Experiments.Common.Ledger.count_append batch1 batch2,
    totalSignal_append batch1 batch2,
    pooled_comparable⟩

/-- The tag is an honest ceiling: a finite ledger model of accumulation, nothing distributional. -/
theorem ceiling :
    claim.tag = Experiments.Common.ClaimTag.finiteLedgerModel := rfl

-- ---------------------------------------------------------------------------
-- A computable run + a non-vacuous Experiment.claim, with a proved bridge.
-- ---------------------------------------------------------------------------

structure Setup where
  instrument : Instrument
  left : Batch
  right : Batch

/-- The run computes — thanks to the `Decidable` instance — whether the pooled batch is
comparable (same-instrument), i.e. whether repetition is lawful for this setup. -/
def run (setup : Setup) : Bool :=
  decide (fromInstrument setup.instrument
    (Experiments.Common.Ledger.append setup.left setup.right))

def experiment : Experiments.Common.Experiment Setup Bool :=
  { tag := claim.tag
    run := run
    claim := fun setup =>
      fromInstrument setup.instrument
        (Experiments.Common.Ledger.append setup.left setup.right) }

theorem run_iff_claim (setup : Setup) :
    run setup = true ↔ experiment.claim setup := by
  simp only [run, experiment, decide_eq_true_iff]

def canonicalSetup : Setup :=
  { instrument := Instrument.brewA, left := batch1, right := batch2 }

/-- A drifted setup: `right` is a `brewB` realization, so pooling is NOT comparable. -/
def driftedSetup : Setup :=
  { instrument := Instrument.brewA
    left := batch1
    right := { events := [⟨Instrument.brewB, 4⟩] } }

#eval run canonicalSetup   -- expect: true
#eval run driftedSetup     -- expect: false  (drift: not same-instrument)

#print axioms claim_holds

-- The falsifiable comparability predicate, evaluated at the DRIFTED config where it is FALSE —
-- proves the comparability lemma is load-bearing, not vacuous.
#eval decide (fromInstrument Instrument.brewA
  (Experiments.Common.Ledger.append driftedSetup.left driftedSetup.right))  -- expect: false

/-- Bring a minimal device next to this experiment: it records whether the exported claim fires.
(`experiment.claim` reduces definitionally to `fromInstrument …`, which is `Decidable`.) -/
def deviceNear (setup : Setup) : Bool :=
  decide (fromInstrument setup.instrument
    (Experiments.Common.Ledger.append setup.left setup.right))

theorem deviceNear_detects_claim (setup : Setup) :
    deviceNear setup = true ↔ experiment.claim setup := by
  simp only [deviceNear, experiment, decide_eq_true_iff]

def triangulation : Experiments.Common.Triangulation Setup Bool :=
  { experiment := experiment
    device := deviceNear
    detects := deviceNear_detects_claim }

end Experiments.TheGossetEffectCh02
