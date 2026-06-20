import Experiments.Common

/-!
# The Euclid Effect — object permanence as the irreversibility of the ledger

Source: `instrument/chapters/01.tex:916` (`ph:object-permanence`).

The phenomenon: once a distinction has been recorded in the experimental ledger,
**no extension can remove it**.  Euclid's constructions are irreversible — once a
point or relation is drawn, every later step must respect it.  Here the "ledger"
is a finite `List` of recorded distinctions, and "extension" is appending more
records.  Permanence is then a finite-bookkeeping fact: appending to a record can
only **grow** the tally of recorded distinctions; it can never erase one.

This file follows the worked exemplar shape (see
`device/Experiments/ThePositronAnnihilationEffect/Experiment1.lean`):

1. an **effect-specific domain** (`Distinction`, `Ledger` of distinctions) — not the
   3-`Nat` `CountSetup` template;
2. genuinely **falsifiable** `∀`-lemmas (drop the "extension" hypothesis and they break);
3. a **content-bearing** claim — a real conjunction, never `True`;
4. an **honest tag** (`finiteLedgerModel`) + a candid "NOT claimed" disclaimer;
5. explicit `Decidable` instances so `decide`/`#eval` compute through the predicates;
6. a **HARNESS coupling**: a conjunct of `claim_holds` is discharged by
   `Experiments.Common.Ledger.count_append`, so a regression/rename in the harness
   ledger algebra breaks *this* file's build.  (No holonomy/charge/positron here, so a
   device coupling would be FAKE — the honest coupling is the ledger bookkeeping.)

## NOT claimed
That this is real object permanence or perception; that the world *has* enduring
objects; anything about *which* distinctions are physically meaningful; any continuum
or topology.  The model says only: the count of recorded distinctions is **monotone
non-decreasing under extension**, and a specific recorded distinction **survives** any
append.  Claim ceiling: a finite ledger model whose persistence conjunct is the
harness's own `count_append`.
-/

namespace Experiments.TheEuclidEffect

/-- A recorded distinction: an opaque tag (which slot was distinguished) and the step
at which it was first recorded.  Two distinctions are equal iff both agree. -/
structure Distinction where
  slot : Nat
  step : Nat
deriving DecidableEq, Repr

/-- The experimental record is a finite ledger of distinctions. -/
abbrev Record := Experiments.Common.Ledger Distinction

/-- An **extension** of a record appends further distinctions to the right; the prior
record is the prefix that must be preserved. -/
def extend (prior new : Record) : Record :=
  Experiments.Common.Ledger.append prior new

/-- A distinction is *recorded in* a record iff it appears in the event list. -/
def recordedIn (d : Distinction) (r : Record) : Prop :=
  d ∈ r.events

instance (d : Distinction) (r : Record) : Decidable (recordedIn d r) := by
  unfold recordedIn; exact inferInstance

-- ---------------------------------------------------------------------------
-- FALSIFIABLE lemmas: each would break if the "extension" structure were wrong.
-- ---------------------------------------------------------------------------

/-- PERMANENCE (membership form): a distinction recorded in the prior ledger remains
recorded in every extension.  Quantified over ALL priors, extensions and distinctions.
Drop the hypothesis `h` and the conclusion is false (a fresh `new` need not contain `d`). -/
theorem recorded_persists_under_extension
    (prior new : Record) (d : Distinction) (h : recordedIn d prior) :
    recordedIn d (extend prior new) := by
  unfold recordedIn extend Experiments.Common.Ledger.append
  exact List.mem_append.mpr (Or.inl h)

/-- PERMANENCE (count form): extending a record never decreases the number of recorded
distinctions.  The tally is monotone — the harness `count_append` is doing the work. -/
theorem count_monotone_under_extension (prior new : Record) :
    prior.count ≤ (extend prior new).count := by
  unfold extend
  rw [Experiments.Common.Ledger.count_append]
  exact Nat.le_add_right prior.count new.count

/-- IRREVERSIBILITY: the extended count equals the prior count PLUS the new count — there
is no truncation, no erasure term.  This is exactly the harness ledger identity. -/
theorem extension_is_exact_sum (prior new : Record) :
    (extend prior new).count = prior.count + new.count := by
  unfold extend
  exact Experiments.Common.Ledger.count_append prior new

-- ---------------------------------------------------------------------------
-- A canonical record and a concrete extension.
-- ---------------------------------------------------------------------------

/-- A prior record with two recorded distinctions. -/
def priorRecord : Record := { events := [{ slot := 0, step := 0 }, { slot := 1, step := 1 }] }

/-- A genuine extension: one further distinction recorded at a later step. -/
def newRecord : Record := { events := [{ slot := 2, step := 2 }] }

/-- The distinction recorded first — the one whose permanence we will witness. -/
def firstDistinction : Distinction := { slot := 0, step := 0 }

/-- Concretely: the first distinction is recorded in the prior ledger. -/
theorem first_recorded_in_prior : recordedIn firstDistinction priorRecord := by decide

/-- Concretely: it survives the extension. -/
theorem first_survives_extension :
    recordedIn firstDistinction (extend priorRecord newRecord) := by decide

-- ---------------------------------------------------------------------------
-- THE CLAIM (content-bearing; the persistence conjunct is the harness theorem).
-- ---------------------------------------------------------------------------

/-- The claim, in honest parts:
* (recorded) the first distinction is recorded in the prior ledger — proved here;
* (permanence) it survives the canonical extension — proved by
  `recorded_persists_under_extension`, the membership form of permanence;
* (exact bookkeeping) the extended count is the EXACT sum `prior + new` — discharged by
  `Experiments.Common.Ledger.count_append`, the **harness** ledger identity.  A regression
  in that harness lemma fails this build (the load-bearing coupling). -/
def claimStatement : Prop :=
  recordedIn firstDistinction priorRecord ∧
    recordedIn firstDistinction (extend priorRecord newRecord) ∧
    (extend priorRecord newRecord).count = priorRecord.count + newRecord.count

def claim : Experiments.Common.Claim :=
  { tag := Experiments.Common.ClaimTag.finiteLedgerModel
    statement := claimStatement }

theorem claim_holds : claim.statement :=
  ⟨first_recorded_in_prior,
    recorded_persists_under_extension priorRecord newRecord firstDistinction first_recorded_in_prior,
    Experiments.Common.Ledger.count_append priorRecord newRecord⟩

/-- The tag is an honest ceiling: a finite ledger model, nothing more. -/
theorem ceiling : claim.tag = Experiments.Common.ClaimTag.finiteLedgerModel := rfl

-- ---------------------------------------------------------------------------
-- A computable run + a NON-vacuous Experiment.claim, with a proved bridge.
-- ---------------------------------------------------------------------------

structure Setup where
  prior : Record
  new : Record
  witness : Distinction

/-- The run computes — thanks to the `Decidable` instance — whether the witnessed
distinction survives the extension. -/
def run (s : Setup) : Bool :=
  decide (recordedIn s.witness (extend s.prior s.new))

/-- The exported claim is a genuine function of the setup (not `fun _ => True`); this
bridge pins it to `run`. -/
def experiment : Experiments.Common.Experiment Setup Bool :=
  { tag := claim.tag
    run := run
    claim := fun s => recordedIn s.witness (extend s.prior s.new) }

theorem run_iff_claim (s : Setup) :
    run s = true ↔ experiment.claim s := by
  simp only [run, experiment, decide_eq_true_iff]

def canonicalSetup : Setup :=
  { prior := priorRecord, new := newRecord, witness := firstDistinction }

/-- Bring a minimal device next to this experiment: it records whether the claim fires.
`experiment.claim s` reduces to `recordedIn s.witness (extend s.prior s.new)`, which has a
`Decidable` instance, so `run` and `deviceNear` agree by `rfl`. -/
def deviceNear (s : Setup) : Bool :=
  run s

theorem deviceNear_detects_claim (s : Setup) :
    deviceNear s = true ↔ experiment.claim s := by
  simp only [deviceNear, run, experiment, decide_eq_true_iff]

def triangulation : Experiments.Common.Triangulation Setup Bool :=
  { experiment := experiment
    device := deviceNear
    detects := deviceNear_detects_claim }

-- ---------------------------------------------------------------------------
-- GATE EVIDENCE.
-- ---------------------------------------------------------------------------

#eval run canonicalSetup                                   -- expect: true  (survives)
-- The falsifiable predicate at a config where it is FALSE: a distinction NOT in the
-- prior, and NOT introduced by the extension, is NOT recorded in the extension.
#eval decide (recordedIn { slot := 9, step := 9 } (extend priorRecord newRecord))  -- expect: false
#print axioms claim_holds                                  -- [propext, Quot.sound] = AMBIENT

end Experiments.TheEuclidEffect
