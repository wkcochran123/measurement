import Experiments.Common

/-!
# The Cantor–Gödel–Cohen Effect — refinement recoverability as a finite ledger no-go

Source description: `instrument/chapters/01.tex:263` (`ph:ch`). The Continuum Hypothesis is
recast as a question about **completing the refinement process between discrete records**.
The description's *Constraint* is the load-bearing physics here:

> No extension of the experimental ledger may introduce distinctions that cannot be recovered
> by refinement of the record. Any completion of refinement that presupposes unrecorded
> intermediate structure is inadmissible.

So this file models a **refinement** (a `decode` from fine records to coarse ones) and the
*recoverability* constraint: pushing a fine ledger through the refinement may neither **lose**
nor **invent** distinctions — the coarse count equals the fine count. A completion that smuggles
in unrecorded intermediate structure (an `inflate` that adds phantom coarse records the fine
ledger never witnessed) is **inadmissible**, and we prove it changes the count, hence is detected.

## Coupling (honest)
HARNESS, not device. The content is refinement / distinguishability bookkeeping, so the
load-bearing theorem is `Experiments.Common.Ledger.count_map`: a faithful refinement
(`Refinement.pushLedger`, which is exactly `Ledger.map decode`) preserves the count. A conjunct
of `claim_holds` is discharged *by that theorem* (through `recovered_preserves_count`), so a
regression in the harness `count_map` breaks **this** build. There is NO holonomy / charge /
positron content — forcing the device positron theorems here would be a FAKE coupling, so I
decline the device. (coupledTo = harness.)

## NOT claimed
- **Nothing about the actual Continuum Hypothesis.** This does not decide CH, does not formalize
  forcing, Gödel's L, Cohen's models, cardinal arithmetic, or independence from ZFC. There is no
  transfinite, no uncountable, no real line here — only finite `List`-backed ledgers.
- The "independence" of the description is rendered only as: recoverability is an *extra* finite
  constraint a completion may or may not satisfy (admissible vs. inadmissible), not a theorem of
  the ambient logic. That is an analogy, not a metamathematical claim.
- **Claim ceiling:** a finite no-go — a refinement that preserves the record is admissible; one
  that presupposes unrecorded structure is detected by a count mismatch and rejected.
-/

namespace Experiments.TheCantorGodelCohenEffect

open Experiments.Common

/-- A coarse record kept in the experimental ledger: an index plus a recorded distinction value.
"Distinctions licensed by the setup" = the multiset of these we can actually witness. -/
structure Record where
  index : Nat
  distinction : Nat
deriving DecidableEq, Repr

/-- A **fine** record: it already carries everything the coarse layer will read off. A refinement
of the record is the act of `decode`-ing a fine record down to a coarse one. -/
structure FineRecord where
  index : Nat
  distinction : Nat
  microState : Nat
deriving DecidableEq, Repr

/-- The refinement map: forget the micro-state, keep the recoverable coarse distinction. This is
the `decode` of a `Experiments.Common.Refinement Record FineRecord`. -/
def decode (f : FineRecord) : Record := { index := f.index, distinction := f.distinction }

/-- The refinement, as a harness object. `pushLedger` through it is exactly `Ledger.map decode`. -/
def refinement : Refinement Record FineRecord := { decode := decode }

/-- **Admissibility (recoverability).** A coarse ledger is *recovered by refinement* of a fine
ledger when it is literally the push of that fine ledger through the refinement — every coarse
distinction has a fine record behind it, none invented, none dropped. -/
def recoveredBy (coarse : Ledger Record) (fine : Ledger FineRecord) : Prop :=
  coarse = refinement.pushLedger fine

/-- An **inadmissible completion**: it appends a phantom coarse record on top of the genuine push
— "intermediate structure presupposed without a corresponding record" in the fine ledger. -/
def inflate (fine : Ledger FineRecord) (phantom : Record) : Ledger Record :=
  Ledger.append (refinement.pushLedger fine) { events := [phantom] }

-- ---------------------------------------------------------------------------
-- FALSIFIABLE lemmas. Each is ∀-quantified; dropping its hypothesis breaks it.
-- ---------------------------------------------------------------------------

/-- **Recoverability ⇒ no distinction count is lost or invented.** If a coarse ledger is recovered
by refinement of a fine ledger, the two carry exactly the same number of distinctions. Quantified
over ALL fine ledgers. Falsifiable: replace `recoveredBy` by "coarse is anything" and it fails
(the `inflatedSetup` `#eval` below witnesses a coarse ledger whose count differs). -/
theorem recovered_preserves_count
    (coarse : Ledger Record) (fine : Ledger FineRecord) (h : recoveredBy coarse fine) :
    coarse.count = fine.count := by
  rw [h]
  show (refinement.pushLedger fine).count = fine.count
  exact Ledger.count_map decode fine

/-- **Inadmissibility is detected.** An inflated completion — one extra phantom coarse record with
no fine witness — has a strictly larger count than the fine ledger, so it can never be the
recoverable push. Quantified over ALL fine ledgers and ALL phantoms. -/
theorem inflate_not_recoverable
    (fine : Ledger FineRecord) (phantom : Record) :
    (inflate fine phantom).count = fine.count + 1 := by
  show (Ledger.append (refinement.pushLedger fine) { events := [phantom] }).count = fine.count + 1
  rw [Ledger.count_append]
  have hpush : (refinement.pushLedger fine).count = fine.count := Ledger.count_map decode fine
  rw [hpush]
  rfl

-- ---------------------------------------------------------------------------
-- A canonical witness: two fine records refine to two coarse ones, recoverably.
-- ---------------------------------------------------------------------------

def fineLedger : Ledger FineRecord :=
  { events := [ { index := 0, distinction := 7, microState := 100 },
                { index := 1, distinction := 9, microState := 200 } ] }

/-- The coarse ledger that IS recovered by refinement of `fineLedger`. -/
def coarseLedger : Ledger Record := refinement.pushLedger fineLedger

theorem coarse_is_recovered : recoveredBy coarseLedger fineLedger := rfl

/-- The inadmissible completion: the recovered ledger plus one phantom distinction (index 99) that
no fine record licenses. -/
def phantom : Record := { index := 99, distinction := 42 }

/-- It really does change the count — concrete instance of the ∀ lemma. -/
theorem inflate_detected : (inflate fineLedger phantom).count = coarseLedger.count + 1 := by
  unfold coarseLedger
  exact inflate_not_recoverable fineLedger phantom

-- ---------------------------------------------------------------------------
-- THE CLAIM (content-bearing conjunction; one conjunct discharged by the harness).
-- ---------------------------------------------------------------------------

/-- The claim, in honest parts:
* (recoverable) the canonical coarse ledger is recovered by refinement of the fine one;
* (count preserved — HARNESS-COUPLED) a recovered ledger loses/invents no distinctions; this is
  discharged via `recovered_preserves_count`, which is `Ledger.count_map` — so a `count_map`
  regression fails this build;
* (no-go) the inflated completion is strictly larger, hence NOT a recoverable refinement. -/
def claimStatement : Prop :=
  recoveredBy coarseLedger fineLedger ∧
    coarseLedger.count = fineLedger.count ∧
    (inflate fineLedger phantom).count ≠ fineLedger.count

def claim : Experiments.Common.Claim :=
  { tag := Experiments.Common.ClaimTag.inadmissibilityNoGo
    statement := claimStatement }

theorem claim_holds : claim.statement :=
  ⟨coarse_is_recovered,
   recovered_preserves_count coarseLedger fineLedger coarse_is_recovered,
   by rw [inflate_not_recoverable fineLedger phantom]; omega⟩

/-- Honest ceiling: a finite no-go about refinement recoverability, nothing transfinite. -/
theorem ceiling : claim.tag = Experiments.Common.ClaimTag.inadmissibilityNoGo := rfl

-- ---------------------------------------------------------------------------
-- A computable run + a non-vacuous Experiment, bridged to `run`.
-- ---------------------------------------------------------------------------

structure Setup where
  fine : Ledger FineRecord
  candidate : Ledger Record

/-- The run computes: does the candidate coarse ledger preserve the fine count (a necessary
condition for recoverability)? Decidable via `Nat` equality. -/
def run (s : Setup) : Bool := decide (s.candidate.count = s.fine.count)

def experiment : Experiments.Common.Experiment Setup Bool :=
  { tag := claim.tag
    run := run
    claim := fun s => s.candidate.count = s.fine.count }

theorem run_iff_claim (s : Setup) : run s = true ↔ experiment.claim s := by
  simp only [run, experiment, decide_eq_true_iff]

def canonicalSetup : Setup := { fine := fineLedger, candidate := coarseLedger }
def inflatedSetup : Setup := { fine := fineLedger, candidate := inflate fineLedger phantom }

#eval run canonicalSetup                       -- expect: true  (recoverable, count preserved)
#eval run inflatedSetup                         -- expect: false (inadmissible: count inflated)
#print axioms claim_holds                       -- ambient [propext, Quot.sound], not coupling

/-- Bring a minimal device next to this experiment: it records whether the exported claim fires.
(Decides the reduced `Nat` equality `experiment.claim` unfolds to, so the instance synthesizes.) -/
def deviceNear (setup : Setup) : Bool :=
  decide (setup.candidate.count = setup.fine.count)

theorem deviceNear_detects_claim (setup : Setup) :
    deviceNear setup = true ↔ experiment.claim setup := by
  simp only [deviceNear, experiment, decide_eq_true_iff]

def triangulation : Experiments.Common.Triangulation Setup Bool :=
  { experiment := experiment
    device := deviceNear
    detects := deviceNear_detects_claim }

end Experiments.TheCantorGodelCohenEffect
