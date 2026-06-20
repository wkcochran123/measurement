import Experiments.Common

/-!
# The Einstein Effect (Ch.02) — temporal order as causal licensing of records

Source: `instrument/chapters/02.tex:278`, phenomenon `ph:clock`.

The physics, modelled FINITELY: an instrument produces time not by reading an
underlying flow but by **imposing an irreversible order** on the facts it appends
to its ledger.  Every functioning instrument separates *sensing* from *recording*:
a sensor must first be **triggered**, and only afterward may a **reading** be
produced.  Between them the instrument may sit **silent**.  The constraint
(chapter "Constraint"): no instrument may append a record that is not causally
licensed by a prior interaction — a reading with no preceding trigger is
*inadmissible*.

We model an instrument's tape as a `List InstrumentEvent`.  `licensed` is the
no-go predicate: every `Reading` must be preceded (somewhere earlier on the tape)
by a `Trigger`.  The falsifiable lemmas pin that constraint; the content claim
conjoins (a) a concrete admissible tape is licensed, (b) the inadmissible
"display before current" tape is NOT, and (c) a HARNESS bookkeeping identity —
splitting a tape and re-appending it preserves the recorded count
(`Experiments.Common.Ledger.count_append`), the conserved-record law that makes
the ordering a *ledger* and not free invention.

## NOT claimed
No relativity (no light-cones, no Lorentz transform, no signal-speed bound); the
"causal license" here is the bare ordering trigger-before-reading, NOT physical
causality.  Nothing about *durations* or a time coordinate — only the discrete
order of appended facts.  `Silent` intervals carry no metric.  **Claim ceiling:**
a finite no-go on record order plus a conserved-count ledger identity.
-/

namespace Experiments.TheEinsteinEffectCh02

/-- A fact an instrument may append to its tape.  Sensing (`Trigger`) is distinct
from recording (`Reading`); the instrument may also sit `Silent`. -/
inductive InstrumentEvent where
  | trigger
  | reading
  | silent
deriving DecidableEq, Repr

open InstrumentEvent

/-- Does the tape contain a `trigger` at all (i.e. has a sensing interaction
occurred)?  Used to decide whether a later `reading` is causally licensed. -/
def hasTrigger : List InstrumentEvent -> Bool
  | [] => false
  | trigger :: _ => true
  | _ :: rest => hasTrigger rest

/-- THE NO-GO PREDICATE: every `reading` is causally licensed by a `trigger`
recorded earlier on the tape.  Walks the tape front-to-back, carrying "has a
trigger been seen yet"; a `reading` before any `trigger` falsifies it. -/
def licensedAux : Bool -> List InstrumentEvent -> Prop
  | _, [] => True
  | _, trigger :: rest => licensedAux true rest
  | seen, reading :: rest => seen = true ∧ licensedAux seen rest
  | seen, silent :: rest => licensedAux seen rest

/-- A tape is *licensed* iff, read in order, no reading precedes its trigger. -/
def licensed (tape : List InstrumentEvent) : Prop := licensedAux false tape

/-- Make the no-go predicate DECIDABLE so `decide`/`#eval` compute through it.
Structural recursion on the tape; `licensedAux` reduces definitionally on each
constructor, so we recurse and reuse the result. -/
def decLicensedAux : (b : Bool) -> (tape : List InstrumentEvent) -> Decidable (licensedAux b tape)
  | _, [] => isTrue trivial
  | _, trigger :: rest => decLicensedAux true rest
  | seen, reading :: rest =>
      match decLicensedAux seen rest with
      | isTrue h =>
          match (inferInstance : Decidable (seen = true)) with
          | isTrue hs => isTrue ⟨hs, h⟩
          | isFalse hs => isFalse (fun hc => hs hc.1)
      | isFalse h => isFalse (fun hc => h hc.2)
  | seen, silent :: rest => decLicensedAux seen rest

instance (b : Bool) (tape : List InstrumentEvent) : Decidable (licensedAux b tape) :=
  decLicensedAux b tape

instance (tape : List InstrumentEvent) : Decidable (licensed tape) := by
  unfold licensed; exact inferInstance

-- ---------------------------------------------------------------------------
-- FALSIFIABLE lemmas: drop the trigger-precedes-reading discipline and they break.
-- Quantified over ALL tapes; each is the load-bearing no-go.
-- ---------------------------------------------------------------------------

/-- A `reading` at the very front of the tape — display illuminated before any
current flows — is NEVER licensed, for ANY continuation `rest`.  This is the
chapter's "no display illuminated before current flows": ∀-quantified, and it
fails the instant `licensed` stopped requiring a prior trigger. -/
theorem reading_first_not_licensed (rest : List InstrumentEvent) :
    ¬ licensed (reading :: rest) := by
  unfold licensed licensedAux
  intro h
  exact Bool.noConfusion h.1

/-- More generally: a `reading` reached with no trigger yet seen is inadmissible.
∀ over the "seen-so-far" flag's false case and the tail. -/
theorem reading_unlicensed_aux (rest : List InstrumentEvent) :
    ¬ licensedAux false (reading :: rest) := by
  unfold licensedAux
  intro h
  exact Bool.noConfusion h.1

/-- The order matters: prefixing the required `trigger` REPAIRS the same reading
that was inadmissible bare.  (Witnesses that the lemma above is about *order*,
not about readings being forbidden outright.) -/
theorem trigger_then_reading_licensed :
    licensed (trigger :: reading :: []) := by decide

-- ---------------------------------------------------------------------------
-- Canonical admissible / inadmissible tapes.
-- ---------------------------------------------------------------------------

/-- A clean instrument cycle: sense, wait, record.  Trigger precedes reading. -/
def admissibleTape : List InstrumentEvent := [trigger, silent, reading]

/-- The forbidden tape: a reading appears before any trigger. -/
def inadmissibleTape : List InstrumentEvent := [reading, trigger]

theorem admissible_is_licensed : licensed admissibleTape := by decide
theorem inadmissible_not_licensed : ¬ licensed inadmissibleTape := by decide

-- ---------------------------------------------------------------------------
-- HARNESS COUPLING (load-bearing): the ordering is a LEDGER, so the recorded
-- count is conserved under splitting/re-appending the tape.  This conjunct of
-- `claim_holds` is discharged by `Experiments.Common.Ledger.count_append`; a
-- rename/regression in that harness theorem breaks THIS build.
-- ---------------------------------------------------------------------------

/-- The instrument tape as a harness ledger of appended facts. -/
def tapeLedger (tape : List InstrumentEvent) : Experiments.Common.Ledger InstrumentEvent :=
  { events := tape }

/-- Conservation of recorded facts: a tape split into a head segment and a tail
segment, then re-appended, has the SAME recorded count as the sum of the parts.
Discharged by the harness `Ledger.count_append`. -/
def recordedCountConserved (front back : List InstrumentEvent) : Prop :=
  (Experiments.Common.Ledger.append (tapeLedger front) (tapeLedger back)).count
    = (tapeLedger front).count + (tapeLedger back).count

theorem recordedCountConserved_holds (front back : List InstrumentEvent) :
    recordedCountConserved front back :=
  Experiments.Common.Ledger.count_append (tapeLedger front) (tapeLedger back)

-- ---------------------------------------------------------------------------
-- THE CLAIM (content-bearing; three real conjuncts, one device-free harness law).
-- ---------------------------------------------------------------------------

/-- The claim, in honest thirds:
* (admissibility) the clean cycle `[trigger, silent, reading]` IS licensed;
* (the no-go) the `[reading, trigger]` tape — recording before sensing — is NOT;
* (conservation) recorded facts are conserved under tape append
  (`Ledger.count_append`, the harness coupling). -/
def claimStatement : Prop :=
  licensed admissibleTape ∧
    ¬ licensed inadmissibleTape ∧
    recordedCountConserved admissibleTape inadmissibleTape

def claim : Experiments.Common.Claim :=
  { tag := Experiments.Common.ClaimTag.inadmissibilityNoGo
    statement := claimStatement }

theorem claim_holds : claim.statement :=
  ⟨admissible_is_licensed, inadmissible_not_licensed,
    recordedCountConserved_holds admissibleTape inadmissibleTape⟩

/-- The tag is an honest ceiling: a no-go on record order. -/
theorem ceiling : claim.tag = Experiments.Common.ClaimTag.inadmissibilityNoGo := rfl

-- ---------------------------------------------------------------------------
-- A computable run + a NON-vacuous Experiment.claim, with a proved bridge.
-- ---------------------------------------------------------------------------

structure Setup where
  tape : List InstrumentEvent

/-- The run computes, via the `Decidable (licensed _)` instance. -/
def run (s : Setup) : Bool := decide (licensed s.tape)

def experiment : Experiments.Common.Experiment Setup Bool :=
  { tag := claim.tag
    run := run
    claim := fun s => licensed s.tape }

theorem run_iff_claim (s : Setup) :
    run s = true ↔ experiment.claim s := by
  show decide (licensed s.tape) = true ↔ licensed s.tape
  exact decide_eq_true_iff

def admissibleSetup : Setup := { tape := admissibleTape }
def inadmissibleSetup : Setup := { tape := inadmissibleTape }

/-- Bring a minimal device next to this experiment: it records whether the
exported claim fires. -/
def deviceNear (setup : Setup) : Bool :=
  decide (licensed setup.tape)

theorem deviceNear_detects_claim (setup : Setup) :
    deviceNear setup = true ↔ experiment.claim setup := by
  show decide (licensed setup.tape) = true ↔ licensed setup.tape
  exact decide_eq_true_iff

def triangulation : Experiments.Common.Triangulation Setup Bool :=
  { experiment := experiment
    device := deviceNear
    detects := deviceNear_detects_claim }

#eval run admissibleSetup      -- expect: true
#eval run inadmissibleSetup    -- expect: false (reading before trigger)
#print axioms claim_holds      -- ambient [propext, Quot.sound], not coupling

-- GATE EVIDENCE: the falsifiable predicate evaluated where it is FALSE — the
-- inadmissible tape is NOT licensed — proving the no-go lemma is load-bearing.
#eval decide (licensed inadmissibleTape)   -- expect: false

end Experiments.TheEinsteinEffectCh02
