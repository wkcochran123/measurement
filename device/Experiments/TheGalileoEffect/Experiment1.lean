import Experiments.Common

/-!
# The Galileo Effect — invariance of a finite causal ledger under admissible relabeling

Built to the EXEMPLAR shape (`ThePositronAnnihilationEffect/Experiment1.lean`):

1. an **effect-specific domain** (`CausalEvent`, `Relabeling`) — NOT the 3-`Nat` `CountSetup`;
2. genuinely **falsifiable** `∀`-quantified lemmas — each would break if a hypothesis were dropped
   (`relabel_preserves_count`, `relabel_preserves_order`);
3. a **content-bearing** claim — a real conjunction, never `True`;
4. an **honest tag** (`finiteLedgerModel`) + a candid "NOT claimed" disclaimer;
5. explicit `Decidable` instances so `decide`/`#eval` see through the richer predicates;
6. it **couples to the harness**: the invariance conjunct of `claim_holds` is discharged by the
   harness theorem `Experiments.Common.Ledger.count_map` — the device's own bookkeeping law that a
   relabeling (a `decode`/rename map over the ledger) leaves the count of recorded events unchanged.
   A `sorry`/rename/regression in `Ledger.count_map` breaks *this* file's build.

## Physics (modelled finitely; description: `instrument/chapters/08.tex:568`)
The Galileo Effect: a physically meaningful statement must survive **independent verification through
admissible relabeling**. Admissible relabeling acts as a *gauge freedom* on the finite causal record.
It permutes the **names** of events and reindexes refinement chains **without altering causal
precedence or distinguishability**. Objectivity is the invariance class of descriptions, not the
authority of a coordinate system. We model a causal ledger as a finite `Ledger CausalEvent`; an
admissible relabeling is a `decode` map applied event-wise (`Ledger.map`). What is *invariant* — the
count of distinguishable recorded events — is exactly `Ledger.count_map`: the residue that survives
renaming. A relabeling that changes every event's name still records the same number of events, and
still preserves their causal order — that is what makes the two descriptions "the same structure".

## NOT claimed
That this is a group of gauge transformations, a connection, or any continuum diffeomorphism; that
relabeling is a *bijection* (we model an event-wise decode map, not a permutation, and do not enforce
injectivity); that this derives Noether's theorem or any conservation law; any claim about *motion
through space*. The only genuine invariance content is `count_map`, the harness's own additivity/length
law — that a per-event rename preserves the recorded-event count. **Claim ceiling:** a finite ledger
model whose invariance conjunct is the harness's own `count_map` theorem.
-/

namespace Experiments.TheGalileoEffect

/-- A single recorded event in a causal ledger: a `name` (a coordinate label — the thing a relabeling
changes) together with a `slot` recording its causal position (what relabeling must NOT change). -/
structure CausalEvent where
  name : Nat
  slot : Nat
deriving DecidableEq, Repr

/-- A finite causal ledger: a record of distinguishable events. -/
abbrev CausalLedger := Experiments.Common.Ledger CausalEvent

/-- An **admissible relabeling**: a per-event decode map (rename + reindex) that may rewrite the
`name` arbitrarily but **leaves the causal `slot` fixed** — it is a gauge freedom on the *names*, not
on the causal structure. We bundle a name-map; the slot passes through untouched. -/
structure Relabeling where
  rename : Nat -> Nat

namespace Relabeling

/-- Act on one event: rewrite its name, keep its causal slot. -/
def onEvent (r : Relabeling) (e : CausalEvent) : CausalEvent :=
  { name := r.rename e.name, slot := e.slot }

/-- Act on a whole ledger, event-wise — this is exactly `Ledger.map r.onEvent`. -/
def onLedger (r : Relabeling) (L : CausalLedger) : CausalLedger :=
  Experiments.Common.Ledger.map r.onEvent L

/-- A relabeling **preserves causal order** between two events: it never changes their `slot`s, so
the strict precedence `slot < slot` is identical before and after. (Quantified lemma below.) -/
def preservesOrder (r : Relabeling) (e f : CausalEvent) : Prop :=
  ((r.onEvent e).slot < (r.onEvent f).slot) ↔ (e.slot < f.slot)

instance (r : Relabeling) (e f : CausalEvent) : Decidable (r.preservesOrder e f) := by
  unfold preservesOrder onEvent; exact inferInstance

end Relabeling

-- ---------------------------------------------------------------------------
-- FALSIFIABLE lemmas: each pins a hypothesis of the relabeling model.
-- ---------------------------------------------------------------------------

/-- **Invariance of the recorded-event count under ANY admissible relabeling.** Quantified over all
relabelings and all ledgers. This is the load-bearing harness coupling: it is `Ledger.count_map`.
Would FAIL if `onLedger` collapsed or dropped events instead of mapping name-wise — i.e. if relabeling
altered *distinguishability* rather than just *names*. -/
theorem relabel_preserves_count (r : Relabeling) (L : CausalLedger) :
    (r.onLedger L).count = L.count := by
  unfold Relabeling.onLedger
  exact Experiments.Common.Ledger.count_map r.onEvent L

/-- **Invariance of causal order under ANY admissible relabeling.** Quantified over all relabelings
and all event pairs. Would FAIL if `onEvent` rewrote the `slot` (e.g. set it from the name): then the
precedence after relabeling would no longer track the precedence before, and the renaming would be
*inadmissible*. The proof needs only that `onEvent` leaves `slot` definitionally fixed. -/
theorem relabel_preserves_order (r : Relabeling) (e f : CausalEvent) :
    r.preservesOrder e f := by
  unfold Relabeling.preservesOrder Relabeling.onEvent
  exact Iff.rfl

-- ---------------------------------------------------------------------------
-- The canonical ledger and a genuine (non-identity) relabeling.
-- ---------------------------------------------------------------------------

/-- A canonical causal ledger: three distinguishable events in causal slots 0 < 1 < 2. -/
def ledgerA : CausalLedger :=
  { events := [{ name := 10, slot := 0 }, { name := 20, slot := 1 }, { name := 30, slot := 2 }] }

/-- A genuine admissible relabeling: shift every name by 100 (a second, independent coordinate
system). It is NOT the identity — every recorded name changes — yet the structure is preserved. -/
def shift100 : Relabeling := { rename := fun n => n + 100 }

/-- The relabeled ledger really has DIFFERENT names from the original (the relabeling is nontrivial,
not a vacuous identity): the first recorded names disagree. -/
def namesChange : Prop :=
  (shift100.onLedger ledgerA).events ≠ ledgerA.events

instance : Decidable namesChange := by
  unfold namesChange shift100 Relabeling.onLedger ledgerA
  exact inferInstance

/-- The canonical relabeling preserves the count (concrete instance of the invariance). -/
theorem canonical_count_invariant :
    (shift100.onLedger ledgerA).count = ledgerA.count :=
  relabel_preserves_count shift100 ledgerA

/-- The relabeling genuinely changes the names (concrete, via the `Decidable` instance). -/
theorem canonical_names_change : namesChange := by decide

-- ---------------------------------------------------------------------------
-- THE CLAIM (content-bearing; the invariance conjunct is the harness's theorem).
-- ---------------------------------------------------------------------------

/-- The claim, in honest parts:
* (invariance, ALL relabelings) every admissible relabeling preserves the recorded-event count —
  discharged by the harness's `count_map` (`relabel_preserves_count`), the residue that survives
  renaming;
* (order survives, ALL relabelings) every admissible relabeling preserves causal precedence
  (`relabel_preserves_order`); and
* (relabeling is nontrivial) the canonical relabeling actually changes the names (`namesChange`), so
  the invariance is *survival under a genuine change of description*, not a vacuous identity.
The first conjunct is the genuine invariance content and is the harness's own `count_map`, so a
regression in `Ledger.count_map` fails this build. -/
def claimStatement : Prop :=
  (∀ (r : Relabeling) (L : CausalLedger), (r.onLedger L).count = L.count) ∧
    (∀ (r : Relabeling) (e f : CausalEvent), r.preservesOrder e f) ∧
    namesChange

def claim : Experiments.Common.Claim :=
  { tag := Experiments.Common.ClaimTag.finiteLedgerModel
    statement := claimStatement }

theorem claim_holds : claim.statement :=
  ⟨relabel_preserves_count, relabel_preserves_order, canonical_names_change⟩

/-- The tag is an honest ceiling: a finite ledger model, nothing more. -/
theorem ceiling : claim.tag = Experiments.Common.ClaimTag.finiteLedgerModel := rfl

-- ---------------------------------------------------------------------------
-- A computable run + a NON-vacuous Experiment.claim, with a proved bridge.
-- ---------------------------------------------------------------------------

structure Setup where
  ledger : CausalLedger
  relabeling : Relabeling

/-- The run computes whether this setup's relabeling preserved the count (always `true`, by the
invariance — but it is a genuine decidable computation over the mapped ledger). -/
def run (s : Setup) : Bool :=
  decide ((s.relabeling.onLedger s.ledger).count = s.ledger.count)

/-- The exported claim is a genuine function of the setup, pinned to `run` by `run_iff_claim`. -/
def experiment : Experiments.Common.Experiment Setup Bool :=
  { tag := claim.tag
    run := run
    claim := fun s => (s.relabeling.onLedger s.ledger).count = s.ledger.count }

theorem run_iff_claim (s : Setup) :
    run s = true ↔ experiment.claim s := by
  simp only [run, experiment, decide_eq_true_iff]

/-- Make the exported claim DECIDABLE so `deviceNear`/`#eval` see through it. -/
instance (s : Setup) : Decidable (experiment.claim s) :=
  inferInstanceAs (Decidable ((s.relabeling.onLedger s.ledger).count = s.ledger.count))

def canonicalSetup : Setup := { ledger := ledgerA, relabeling := shift100 }

#eval run canonicalSetup                                   -- expect: true (count is invariant)
#eval decide ((shift100.onLedger ledgerA).events = ledgerA.events)
                                                            -- expect: false (names genuinely change)
#print axioms claim_holds                                  -- ambient footprint, not the coupling

/-- Bring a minimal device next to this experiment: it records whether the exported claim fires. -/
def deviceNear (setup : Setup) : Bool :=
  decide (experiment.claim setup)

theorem deviceNear_detects_claim (setup : Setup) :
    deviceNear setup = true ↔ experiment.claim setup := by
  simp [deviceNear]

def triangulation : Experiments.Common.Triangulation Setup Bool :=
  { experiment := experiment
    device := deviceNear
    detects := deviceNear_detects_claim }

end Experiments.TheGalileoEffect
