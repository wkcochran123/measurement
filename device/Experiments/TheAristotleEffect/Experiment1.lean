import Experiments.Common

/-!
# The Aristotle Effect — reorganization is not a fact

Source: `instrument/chapters/02.tex:1616` (`phenom`, `ph:atoms`).

The organization of records is not itself a fact.  Reordering, renaming, or
reindexing the outcomes of an instrument alters the *manner* in which distinctions
are expressed, but not *which* distinctions have occurred.  Factual content lives
in the ledger events; enumeration is descriptive structure.  "Being precedes
bookkeeping."

We model an instrument's output as a finite `Ledger` of recorded events, and an
"enumeration" as a `Reindexing`: a relabeling map `decode` together with a witness
`recover` that recovers the original label (the **Constraint**: no enumeration may
introduce distinctions not recoverable from the ledger — relabeling must be
invertible *on the recorded alphabet*, i.e. the relabeling is faithful).

The content-bearing claim has two halves:
1. **count is invariant** under ANY relabeling — the number of recorded events is a
   fact of the ledger, not of its enumeration (`Experiments.Common.Ledger.count_map`,
   the HARNESS theorem this file is coupled to).  This is the bookkeeping invariant.
2. **distinctions are preserved** under a *faithful* relabeling — if `recover` undoes
   `decode` on the alphabet, then two events that were distinct before relabeling are
   distinct after, and the relabeled ledger recovers to the original.  This is the
   falsifiable half: drop faithfulness and a relabeling can collapse two events into
   one (fabrication, which the Constraint forbids).

## NOT claimed
That there is any privileged enumeration; that the continuum "richness" of
descriptions is *derived* (it is asserted, per the Consequence, to be layered atop a
fixed discrete ledger); any claim about Aristotelian substance metaphysics as physics;
any claim about real instrument calibration.  **Claim ceiling:** a finite ledger model
in which relabeling preserves count and (when faithful) preserves distinctions.
-/

namespace Experiments.TheAristotleEffect

/-- A recorded outcome: a coarse label `slot` on the instrument's alphabet and the
ledger index `idx` at which it was recorded.  Two outcomes are "the same distinction"
exactly when they carry the same `slot`. -/
structure Outcome where
  slot : Nat
  idx : Nat
deriving DecidableEq, Repr

/-- An **enumeration** of the alphabet: a relabeling `decode` of slots together with a
`recover` map intended to undo it.  The relabeling is *faithful* on a slot when
`recover (decode s) = s` — the Constraint's recoverability condition. -/
structure Reindexing where
  decode : Nat -> Nat
  recover : Nat -> Nat

namespace Reindexing

/-- Apply the enumeration to a single outcome (relabel its slot; leave the ledger
index alone — reindexing the alphabet, not deleting records). -/
def applyOutcome (r : Reindexing) (o : Outcome) : Outcome :=
  { o with slot := r.decode o.slot }

/-- The relabeling is **faithful** on slot `s` when its recovery undoes it. -/
def faithfulOn (r : Reindexing) (s : Nat) : Prop :=
  r.recover (r.decode s) = s

instance (r : Reindexing) (s : Nat) : Decidable (r.faithfulOn s) := by
  unfold faithfulOn; exact inferInstance

end Reindexing

open Experiments.Common (Ledger)

/-- Relabel a whole ledger of outcomes through an enumeration. -/
def relabel (r : Reindexing) (lg : Ledger Outcome) : Ledger Outcome :=
  lg.map r.applyOutcome

-- ---------------------------------------------------------------------------
-- HALF 1 — bookkeeping invariant: count is a fact of the ledger, not of its
-- enumeration.  COUPLED to the harness theorem `Ledger.count_map`.
-- ---------------------------------------------------------------------------

/-- The number of recorded events is invariant under ANY relabeling.  This is the
LOAD-BEARING harness coupling: discharged by `Experiments.Common.Ledger.count_map`,
so a regression/rename in the harness breaks this build. -/
theorem count_invariant (r : Reindexing) (lg : Ledger Outcome) :
    (relabel r lg).count = lg.count :=
  Experiments.Common.Ledger.count_map r.applyOutcome lg

-- ---------------------------------------------------------------------------
-- HALF 2 — FALSIFIABLE: a faithful relabeling preserves distinctions.
-- Drop the faithfulness hypothesis and the lemma is false (see the #eval at EOF:
-- a collapsing relabeling sends two distinct slots to one).
-- ---------------------------------------------------------------------------

/-- A faithful relabeling **preserves distinctions**: if two slots differ and the
relabeling is faithful on both, their relabeled slots still differ.  Reordering or
renaming cannot merge two recorded distinctions.  FALSIFIABLE: without `hs`/`ht` a
relabeling like `fun _ => 0` collapses everything. -/
theorem distinct_preserved
    (r : Reindexing) (s t : Nat)
    (hs : r.faithfulOn s) (ht : r.faithfulOn t) (hne : s ≠ t) :
    r.decode s ≠ r.decode t := by
  intro hdec
  apply hne
  -- s = recover (decode s) = recover (decode t) = t
  have : r.recover (r.decode s) = r.recover (r.decode t) := by rw [hdec]
  unfold Reindexing.faithfulOn at hs ht
  rw [hs, ht] at this
  exact this

/-- A faithful relabeling is **recoverable** at the outcome level: applying `recover`
slot-wise after `decode` returns the original slot.  (Quantified over all outcomes
whose slot the relabeling is faithful on.) -/
theorem recoverable
    (r : Reindexing) (o : Outcome) (h : r.faithfulOn o.slot) :
    r.recover ((r.applyOutcome o).slot) = o.slot := by
  unfold Reindexing.applyOutcome Reindexing.faithfulOn at *
  exact h

-- ---------------------------------------------------------------------------
-- A canonical enumeration: shift every slot by +10, recover by -10 (faithful).
-- ---------------------------------------------------------------------------

/-- The canonical faithful enumeration: shift the alphabet up by 10. -/
def shiftBy10 : Reindexing := { decode := fun s => s + 10, recover := fun s => s - 10 }

/-- A canonical two-event ledger (two genuinely distinct slots). -/
def sampleLedger : Ledger Outcome :=
  { events := [ { slot := 3, idx := 0 }, { slot := 7, idx := 1 } ] }

/-- The shift is faithful on every slot of the sample ledger. -/
theorem shift_faithful_3 : shiftBy10.faithfulOn 3 := by decide
theorem shift_faithful_7 : shiftBy10.faithfulOn 7 := by decide

-- ---------------------------------------------------------------------------
-- THE CLAIM (content-bearing conjunction; half 1 is the harness theorem).
-- ---------------------------------------------------------------------------

/-- The claim, in honest halves:
* (bookkeeping) relabeling the sample ledger preserves its event count
  (`count_invariant`, discharged by the harness `Ledger.count_map` — the coupling);
* (no-collapse) the canonical faithful shift keeps the two distinct slots `3 ≠ 7`
  distinct after relabeling (`distinct_preserved`, the falsifiable half);
* (recoverability) the relabeled first outcome recovers to its original slot. -/
def claimStatement : Prop :=
  (relabel shiftBy10 sampleLedger).count = sampleLedger.count ∧
    shiftBy10.decode 3 ≠ shiftBy10.decode 7 ∧
    shiftBy10.recover ((shiftBy10.applyOutcome { slot := 3, idx := 0 }).slot) = 3

def claim : Experiments.Common.Claim :=
  { tag := Experiments.Common.ClaimTag.finiteLedgerModel
    statement := claimStatement }

theorem claim_holds : claim.statement :=
  ⟨ count_invariant shiftBy10 sampleLedger,
    distinct_preserved shiftBy10 3 7 shift_faithful_3 shift_faithful_7 (by decide),
    recoverable shiftBy10 { slot := 3, idx := 0 } shift_faithful_3 ⟩

/-- The tag is an honest ceiling: a finite ledger model, nothing more. -/
theorem ceiling : claim.tag = Experiments.Common.ClaimTag.finiteLedgerModel := rfl

-- ---------------------------------------------------------------------------
-- A computable run + a non-vacuous Experiment.claim, with a proved bridge.
-- ---------------------------------------------------------------------------

structure Setup where
  reindexing : Reindexing
  ledger : Ledger Outcome

/-- The run checks that the relabeling preserved the recorded count (the bookkeeping
fact).  Computable because `Nat` equality is decidable. -/
def run (s : Setup) : Bool := decide ((relabel s.reindexing s.ledger).count = s.ledger.count)

/-- The exported claim is a genuine function of the setup, pinned to `run`. -/
def experiment : Experiments.Common.Experiment Setup Bool :=
  { tag := claim.tag
    run := run
    claim := fun s => (relabel s.reindexing s.ledger).count = s.ledger.count }

theorem run_iff_claim (s : Setup) :
    run s = true ↔ experiment.claim s := by
  simp only [run, experiment, decide_eq_true_iff]

def canonicalSetup : Setup := { reindexing := shiftBy10, ledger := sampleLedger }

/-- A collapsing enumeration: send every slot to 0.  It is NOT faithful, and it merges
distinct slots — exactly the "fabrication" the Constraint forbids. -/
def collapseAll : Reindexing := { decode := fun _ => 0, recover := fun _ => 0 }

#eval run canonicalSetup                               -- expect: true (count preserved)
-- The falsifiable half made load-bearing: a collapsing relabel sends 3 and 7 to the
-- SAME slot, so `distinct_preserved`'s conclusion is FALSE here (it needs faithfulness):
#eval decide (collapseAll.decode 3 ≠ collapseAll.decode 7)   -- expect: false
#print axioms claim_holds                              -- [propext, Quot.sound] = AMBIENT

/-- Bring a minimal device next to this experiment: it records whether the exported claim fires.
Written via the unfolded claim body (a decidable `Nat` equality) so `decide` synthesizes. -/
def deviceNear (setup : Setup) : Bool :=
  decide ((relabel setup.reindexing setup.ledger).count = setup.ledger.count)

theorem deviceNear_detects_claim (setup : Setup) :
    deviceNear setup = true ↔ experiment.claim setup := by
  simp only [deviceNear, experiment, decide_eq_true_iff]

def triangulation : Experiments.Common.Triangulation Setup Bool :=
  { experiment := experiment
    device := deviceNear
    detects := deviceNear_detects_claim }

end Experiments.TheAristotleEffect
