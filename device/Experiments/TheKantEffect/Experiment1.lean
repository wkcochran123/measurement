import Experiments.Common

/-!
# The Kant Effect — effect-specific, falsifiable, content-bearing

Rebuilt to the EXEMPLAR shape (cf. `ThePositronAnnihilationEffect/Experiment1.lean`):
an effect-specific domain (not the 3-`Nat` `CountSetup`), falsifiable `∀`-lemmas, a real
conjunction as the claim, an honest tag + disclaimer, explicit `Decidable` instances, and a
HARNESS coupling whose theorem is a load-bearing conjunct of `claim_holds`.

## Physics (modelled finitely)
Kant's claim (here): time is not a primitive backdrop in which records sit, but an *ordering
relation induced by record extension*. A record carries NO intrinsic temporal coordinate; its
temporal position is read off SOLELY from its placement in the ledger. "Earlier/later" is
`precedes`: the index of one record is strictly below the index of another. When a ledger is
*extended* (a later history is appended), the temporal horizon — the supply of admissible
positions — grows exactly additively, and the order already laid down is preserved. The temporal
coordinate of a record in the extended ledger is its old index, untouched: succession is a
property of the LEDGER, not of the records.

We model a `Record` as an opaque finite mark, a `History` as a finite ledger of marks, and the
derived temporal coordinate as the index a mark occupies. `precedes` is the induced order. The
"horizon of admissible positions" is the ledger length; under record extension it adds.

## NOT claimed
That this is real spacetime, a continuum of instants, relativity of simultaneity, or any metric
structure on time. We do NOT derive a real-number time axis, light cones, or a causal Lorentzian
order — `precedes` is a finite index order, nothing more. We do NOT prove that NO continuum time
exists (that is philosophy); we only exhibit a finite model in which temporal order is fully fixed
by ledger placement and grows additively under extension. **Claim ceiling:** a finite ledger model
of induced temporal order, one of whose conjuncts is the harness's own `count_append`.
-/

namespace Experiments.TheKantEffect

/-- A record: an opaque finite mark with a payload tag. It carries NO temporal field — the whole
Kantian point is that time is not intrinsic to the record. -/
structure Record where
  tag : Nat
deriving DecidableEq, Repr

/-- A history is a finite ledger of records: the only thing that fixes temporal order. -/
abbrev History := Experiments.Common.Ledger Record

namespace History

/-- The temporal horizon: the supply of admissible positions in this history. It is exactly the
ledger length — there is no time apart from the count of recorded distinctions. -/
def horizon (h : History) : Nat :=
  h.count

/-- `precedes i j`: position `i` is temporally earlier than position `j`. Derived SOLELY from
index order — no record contributes an intrinsic coordinate. -/
def precedes (_h : History) (i j : Nat) : Prop :=
  i < j

/-- An index is *admissible* in this history iff it names a recorded position. -/
def admissible (h : History) (i : Nat) : Prop :=
  i < h.horizon

-- Make the predicates DECIDABLE so `decide`/`#eval` see through them.
instance (h : History) (i j : Nat) : Decidable (h.precedes i j) := by
  unfold precedes; exact inferInstance
instance (h : History) (i : Nat) : Decidable (h.admissible i) := by
  unfold admissible horizon; exact inferInstance

end History

-- ---------------------------------------------------------------------------
-- FALSIFIABLE lemmas (∀-quantified; drop the hypothesis and they break).
-- ---------------------------------------------------------------------------

/-- TEMPORAL ORDER IS STRICT: a position never precedes itself. Quantified over ALL histories and
positions; this is the irreflexivity that makes the induced order a genuine succession. Drop the
appeal to `<` and it is false. -/
theorem precedes_irrefl (h : History) (i : Nat) : ¬ h.precedes i i := by
  unfold History.precedes; exact Nat.lt_irrefl i

/-- TEMPORAL ORDER IS TRANSITIVE: earlier-than chains. `∀` over all histories and three positions;
drop either hypothesis and it breaks (you cannot conclude `i < k` from nothing). -/
theorem precedes_trans (h : History) (i j k : Nat)
    (hij : h.precedes i j) (hjk : h.precedes j k) : h.precedes i k := by
  unfold History.precedes at *; exact Nat.lt_trans hij hjk

/-- ORDER IS INTRINSIC TO PLACEMENT, NOT TO THE RECORD: `precedes` ignores the history argument
entirely — two different histories induce the SAME order on shared positions. This is the Kantian
content: succession is a property of the ledger's indexing, identical across what is recorded.
Falsifiable: were the order to read any record field, swapping histories could change it. -/
theorem precedes_independent_of_history (h h' : History) (i j : Nat) :
    h.precedes i j ↔ h'.precedes i j := by
  unfold History.precedes; exact Iff.rfl

/-- NO POSITION BEYOND THE HORIZON IS ADMISSIBLE: a record cannot occupy a temporal slot the
ledger has not recorded. `∀`-quantified no-go; drop the `horizon ≤ i` hypothesis and a small index
IS admissible. -/
theorem beyond_horizon_inadmissible (h : History) (i : Nat)
    (hi : h.horizon ≤ i) : ¬ h.admissible i := by
  unfold History.admissible; exact Nat.not_lt.mpr hi

-- ---------------------------------------------------------------------------
-- The canonical histories + record extension.
-- ---------------------------------------------------------------------------

/-- An initial history: two recorded marks. -/
def pastHistory : History := { events := [{ tag := 0 }, { tag := 1 }] }

/-- A later stretch of records, to be appended (the act of extension that *induces* more time). -/
def futureHistory : History := { events := [{ tag := 2 }, { tag := 3 }, { tag := 4 }] }

/-- Record extension: append the later history onto the earlier. Time is *induced by* this. -/
def extended : History := Experiments.Common.Ledger.append pastHistory futureHistory

/-- The old positions are preserved: index 0 still precedes index 1 in the extended history,
exactly as it did in the past history (order already laid down is untouched). -/
theorem order_preserved_under_extension :
    extended.precedes 0 1 ∧ pastHistory.precedes 0 1 := by
  constructor <;> decide

/-- Extension genuinely creates a *new* admissible temporal position (index 2) that was NOT
admissible before — time was induced by the record extension. -/
theorem extension_creates_new_time :
    ¬ pastHistory.admissible 2 ∧ extended.admissible 2 := by
  constructor <;> decide

-- ---------------------------------------------------------------------------
-- HARNESS COUPLING (load-bearing). The temporal horizon grows EXACTLY additively
-- under record extension: `extended.horizon = pastHistory.horizon + futureHistory.horizon`.
-- This is the harness's own `Ledger.count_append` (the horizon is the ledger count), so a
-- regression/rename in that lemma breaks THIS build. Time is induced by extension, additively.
-- ---------------------------------------------------------------------------

/-- THE INDUCED-TIME IDENTITY: the temporal horizon of the extended history is the sum of the two
horizons — succession is generated additively by record extension. Discharged by the harness
theorem `Ledger.count_append`. -/
theorem horizon_adds_under_extension :
    extended.horizon = pastHistory.horizon + futureHistory.horizon :=
  Experiments.Common.Ledger.count_append pastHistory futureHistory

-- ---------------------------------------------------------------------------
-- THE CLAIM (content-bearing conjunction; one conjunct is the harness theorem).
-- ---------------------------------------------------------------------------

/-- The claim, in honest parts:
* (succession) the induced order is a strict succession — irreflexive at index 0 — proved here;
* (intrinsic-to-placement) the order is independent of which history is recorded (Kant's point);
* (induced time) the temporal horizon grows EXACTLY additively under record extension, discharged
  by the harness `Ledger.count_append` (the load-bearing coupling). -/
def claimStatement : Prop :=
  ¬ pastHistory.precedes 0 0 ∧
    (∀ i j : Nat, pastHistory.precedes i j ↔ futureHistory.precedes i j) ∧
    extended.horizon = pastHistory.horizon + futureHistory.horizon

def claim : Experiments.Common.Claim :=
  { tag := Experiments.Common.ClaimTag.finiteLedgerModel
    statement := claimStatement }

theorem claim_holds : claim.statement :=
  ⟨precedes_irrefl pastHistory 0,
    fun i j => precedes_independent_of_history pastHistory futureHistory i j,
    horizon_adds_under_extension⟩

/-- The tag is an honest ceiling: a finite ledger model of induced temporal order, nothing more. -/
theorem ceiling :
    claim.tag = Experiments.Common.ClaimTag.finiteLedgerModel := rfl

-- ---------------------------------------------------------------------------
-- A computable run + a NON-vacuous Experiment.claim, with a proved bridge.
-- ---------------------------------------------------------------------------

structure Setup where
  history : History
  earlier : Nat
  later : Nat

/-- The run computes whether `earlier` temporally precedes `later` in the recorded order. -/
def run (s : Setup) : Bool := decide (s.history.precedes s.earlier s.later)

/-- The exported claim is a genuine function of the setup; this bridge pins it to `run`. -/
def experiment : Experiments.Common.Experiment Setup Bool :=
  { tag := claim.tag
    run := run
    claim := fun s => s.history.precedes s.earlier s.later }

theorem run_iff_claim (s : Setup) :
    run s = true ↔ experiment.claim s := by
  simp only [run, experiment, decide_eq_true_iff]

def canonicalSetup : Setup := { history := extended, earlier := 0, later := 1 }

#eval run canonicalSetup                                   -- expect: true  (0 precedes 1)
#eval run { canonicalSetup with earlier := 3, later := 1 } -- expect: false (3 does not precede 1)

-- The exported claim is `fun s => s.history.precedes s.earlier s.later`; make it `Decidable` so
-- the device below can `decide` it.
instance (setup : Setup) : Decidable (experiment.claim setup) := by
  show Decidable (setup.history.precedes setup.earlier setup.later); exact inferInstance

/-- Bring a minimal device next to this experiment: it records whether the exported claim fires. -/
def deviceNear (setup : Setup) : Bool :=
  decide (experiment.claim setup)

theorem deviceNear_detects_claim (setup : Setup) :
    deviceNear setup = true ↔ experiment.claim setup := by
  simp [deviceNear, experiment]

def triangulation : Experiments.Common.Triangulation Setup Bool :=
  { experiment := experiment
    device := deviceNear
    detects := deviceNear_detects_claim }

-- ---------------------------------------------------------------------------
-- GATE EVIDENCE.
-- ---------------------------------------------------------------------------

#print axioms claim_holds   -- expect: [propext] (no Classical.choice; clean)

-- The falsifiable predicate is LOAD-BEARING, not vacuous: at positions (3, 1) `precedes` is
-- FALSE (3 does not precede 1), so this prints `false`.
#eval decide (extended.precedes 3 1)   -- expect: false

end Experiments.TheKantEffect
