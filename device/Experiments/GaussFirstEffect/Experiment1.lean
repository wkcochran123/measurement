import Experiments.Common

/-!
# Gauss's First Effect — finite ledger of repeated trials

Modelled finitely after the exemplar
(`device/Experiments/ThePositronAnnihilationEffect/Experiment1.lean`).

## Physics (modelled finitely)
An instrument is applied **repeatedly** under a **fixed** encoding/decoding scheme.
Each trial commits a finite list of distinctions (ledger entries) to the record.
Gauss's First Effect is the regularity that emerges from *repetition itself*: the
aggregate over many trials has a stable summary (a mean = total/count, a spread).
The single fact that makes a "mean" and a running tally even *meaningful* is that
the accumulated count is the **sum** of the per-trial counts — accumulation is
additive **only because the encoding is fixed across trials** (the constraint in
the description: change the encoder and the bell dissolves). We pin exactly that:
a finite session of trials, concatenated under one fixed encoder, has total ledger
count equal to the sum of its trials' counts, and the empirical total (sum of decoded
bin values) is likewise additive.

## NOT claimed
That this is a normal/Gaussian distribution; that any Central Limit Theorem holds;
that a mean/variance *converges* to anything; that probability "emerges". There is
no limit, no continuum, no random field here — only the finite, exact bookkeeping of
accumulated entries under a fixed encoder. The bell shape and its convergence are the
real physics we are NOT formalizing.
**Claim ceiling:** a finite ledger model of repetition, whose additivity conjunct is
the device-harness theorem `Ledger.count_append`.
-/

namespace Experiments.GaussFirstEffect

/-- One observation in a trial: a raw reading and the bin it decodes to under the
fixed encoder. The bin (`Nat`) is the only distinction committed to the ledger. -/
structure Reading where
  raw : Nat
  bin : Nat
deriving DecidableEq, Repr

/-- The fixed encoding/decoding scheme: a `Nat → Nat` quantizer (the "alphabet"
the instrument enforces) plus the number of bins. Holding this fixed across trials
is exactly the representational invariance the description requires. -/
structure Encoder where
  quantize : Nat → Nat
  bins : Nat

/-- A reading is *admissible under* the encoder when its committed bin is the one the
encoder's quantizer assigns to its raw reading (the entry was made with THIS scheme,
not a different one). -/
def Encoder.admits (e : Encoder) (r : Reading) : Prop :=
  r.bin = e.quantize r.raw

instance (e : Encoder) (r : Reading) : Decidable (e.admits r) := by
  unfold Encoder.admits; exact inferInstance

/-- A trial is a finite ledger of readings. -/
abbrev Trial := Experiments.Common.Ledger Reading

/-- The committed total of a trial: the sum of the decoded bin values. This is the
raw material a mean is computed from (`mean = binTotal / count`). -/
def binTotal (t : Trial) : Nat :=
  (t.events.map Reading.bin).foldr (· + ·) 0

-- ---------------------------------------------------------------------------
-- FALSIFIABLE lemmas. Each is ∀-quantified; drop a hypothesis / a summand and
-- it breaks. These are the load-bearing facts that make "accumulate and average"
-- well defined under repetition.
-- ---------------------------------------------------------------------------

/-- ACCUMULATION IS ADDITIVE: the ledger count of two concatenated trials is the sum
of their counts. This is the device-harness theorem, re-exported here; it is the
single fact that lets a running mean be computed incrementally. FALSIFIABLE: replace
`left.count + right.count` with `left.count` and it fails (`count_append` would not
close it). Quantified over ALL trials. -/
theorem count_accumulates (left right : Trial) :
    (Experiments.Common.Ledger.append left right).count = left.count + right.count :=
  Experiments.Common.Ledger.count_append left right

/-- Helper: `foldr (+) 0` distributes over list append. Clean list induction. -/
theorem foldr_add_append (xs ys : List Nat) :
    (xs ++ ys).foldr (· + ·) 0 = xs.foldr (· + ·) 0 + ys.foldr (· + ·) 0 := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.cons_append, List.foldr_cons, ih]; omega

/-- THE EMPIRICAL TOTAL IS ADDITIVE: the sum of decoded bins over a concatenated
session is the sum over its parts. FALSIFIABLE: drop a summand and it breaks.
Quantified over ALL trials. -/
theorem binTotal_accumulates (left right : Trial) :
    binTotal (Experiments.Common.Ledger.append left right)
      = binTotal left + binTotal right := by
  unfold binTotal Experiments.Common.Ledger.append
  simp only [List.map_append, foldr_add_append]

/-- ADMISSIBILITY IS NECESSARY FOR THE BIN TO MEAN ANYTHING: if a reading is NOT
admitted by the fixed encoder, then its committed bin is not the encoder's value.
FALSIFIABLE: this is the constraint "change the scheme and the entry is illegitimate".
Quantified over ALL encoders and readings. -/
theorem inadmissible_bin_mismatch (e : Encoder) (r : Reading) (h : ¬ e.admits r) :
    r.bin ≠ e.quantize r.raw :=
  fun heq => h heq

-- ---------------------------------------------------------------------------
-- A concrete repetition session under ONE fixed encoder.
-- ---------------------------------------------------------------------------

/-- The fixed encoder for this session: round to the nearest multiple of 10
(quantize `n` to `(n / 10) * 10`), into a 10-bin alphabet. -/
def fixedEncoder : Encoder :=
  { quantize := fun n => (n / 10) * 10, bins := 10 }

/-- Trial A: three readings, all admitted by `fixedEncoder`. -/
def trialA : Trial :=
  { events := [ { raw := 12, bin := 10 }, { raw := 27, bin := 20 }, { raw := 31, bin := 30 } ] }

/-- Trial B: two readings, all admitted by `fixedEncoder`. -/
def trialB : Trial :=
  { events := [ { raw := 19, bin := 10 }, { raw := 24, bin := 20 } ] }

/-- The accumulated session: A then B, under the SAME fixed encoder. -/
def session : Trial :=
  Experiments.Common.Ledger.append trialA trialB

/-- Every reading in this session is admitted by the fixed encoder
(`bin = quantize raw`). Concrete, via the `Decidable` instance. -/
theorem session_admissible :
    fixedEncoder.admits { raw := 12, bin := 10 } ∧
    fixedEncoder.admits { raw := 27, bin := 20 } ∧
    fixedEncoder.admits { raw := 31, bin := 30 } ∧
    fixedEncoder.admits { raw := 19, bin := 10 } ∧
    fixedEncoder.admits { raw := 24, bin := 20 } := by decide

/-- The accumulated count is exactly the sum of the trial counts (a frozen-literal
check of the additivity theorem on the chosen session: `3 + 2 = 5`). -/
theorem session_count_is_sum :
    session.count = trialA.count + trialB.count := by decide

-- ---------------------------------------------------------------------------
-- THE CLAIM (content-bearing; the additivity conjunct is the harness theorem).
-- ---------------------------------------------------------------------------

/-- The claim, in honest parts:
* (admissibility) every entry in the session was committed under the ONE fixed
  encoder — proved by `decide`;
* (count accumulates) the session's total ledger count is the sum of its trials'
  counts — discharged by the device-harness `Ledger.count_append` via
  `count_accumulates`, so a regression in that harness lemma breaks THIS build;
* (empirical total accumulates) the decoded bin-total over the session is the sum
  over its trials — `binTotal_accumulates`.
The middle conjunct is the load-bearing coupling: it is `count_append` applied to
the concrete `trialA`/`trialB`, so renaming/breaking `count_append` fails here. -/
def claimStatement : Prop :=
  (fixedEncoder.admits { raw := 12, bin := 10 } ∧
     fixedEncoder.admits { raw := 27, bin := 20 } ∧
     fixedEncoder.admits { raw := 31, bin := 30 } ∧
     fixedEncoder.admits { raw := 19, bin := 10 } ∧
     fixedEncoder.admits { raw := 24, bin := 20 }) ∧
    (Experiments.Common.Ledger.append trialA trialB).count
      = trialA.count + trialB.count ∧
    binTotal (Experiments.Common.Ledger.append trialA trialB)
      = binTotal trialA + binTotal trialB

def claim : Experiments.Common.Claim :=
  { tag := Experiments.Common.ClaimTag.finiteLedgerModel
    statement := claimStatement }

theorem claim_holds : claim.statement :=
  ⟨session_admissible,
    count_accumulates trialA trialB,
    binTotal_accumulates trialA trialB⟩

/-- The tag is an honest ceiling: a finite ledger model of repetition, nothing more. -/
theorem ceiling : claim.tag = Experiments.Common.ClaimTag.finiteLedgerModel := rfl

-- ---------------------------------------------------------------------------
-- A computable run + a non-vacuous exported Experiment, with a proved bridge.
-- ---------------------------------------------------------------------------

structure Setup where
  encoder : Encoder
  first : Trial
  second : Trial

/-- The run accumulates the two trials and reports the total ledger count
(the denominator of the running mean). Computes via `Ledger.count`. -/
def run (s : Setup) : Nat :=
  (Experiments.Common.Ledger.append s.first s.second).count

/-- The exported claim is a genuine function of the setup: accumulation is additive
for THIS setup. The bridge below pins `run` to it, so the body cannot be silently
swapped for `fun _ => True`. -/
def experiment : Experiments.Common.Experiment Setup Nat :=
  { tag := claim.tag
    run := run
    claim := fun s =>
      (Experiments.Common.Ledger.append s.first s.second).count
        = s.first.count + s.second.count }

theorem run_eq_sum (s : Setup) :
    run s = s.first.count + s.second.count := by
  unfold run; exact Experiments.Common.Ledger.count_append s.first s.second

def canonicalSetup : Setup := { encoder := fixedEncoder, first := trialA, second := trialB }

#eval run canonicalSetup                                  -- expect: 5
#eval binTotal session                                    -- expect: 90 (= 60 + 30)
-- load-bearing check: admissibility is NOT vacuous — a reading whose bin disagrees
-- with the fixed encoder is rejected (predicate is FALSE here):
#eval decide (fixedEncoder.admits { raw := 12, bin := 99 })   -- expect: false
#print axioms claim_holds                                 -- ambient [propext, Quot.sound]; coupling = count_append symbol

/-- Bring a minimal device next to this experiment: it records whether the exported claim fires. -/
def deviceNear (setup : Setup) : Bool :=
  decide (experiment.claim setup)

theorem deviceNear_detects_claim (setup : Setup) :
    deviceNear setup = true ↔ experiment.claim setup := by
  simp [deviceNear]

def triangulation : Experiments.Common.Triangulation Setup Nat :=
  { experiment := experiment
    device := deviceNear
    detects := deviceNear_detects_claim }

end Experiments.GaussFirstEffect
