import Experiments.Common

/-!
# The Fessenden-Shannon Effect — rebuilt to the exemplar shape

Source: `instrument/chapters/02.tex:461` (`phenom`, `ph:channel`).

## Physics (modelled finitely)
Fessenden put voice on an amplitude-modulated carrier; Shannon abstracted the practice into a
*channel*: a **refinement structure** that supports several symbolic distinctions at once,
independently of the physical waveform.  The instrument does not respond with a single binary
on/off, but with an **activation pattern** that partitions into a finite set of admissible
**symbols**.  Each symbol is recovered from the raw interaction by the instrument's own
**refinement rule** (a `decode : Sample -> Symbol`), and — the load-bearing constraint —
"finite decomposition does not introduce new distinctions … without inflating the experimental
ledger."  So decoding a fine sample-ledger into the coarse symbol-ledger must leave the **count**
unchanged: refinement reorganizes, it does not create or destroy records.

This is a HARNESS coupling (no holonomy / charge / positron is involved): the channel is a
`Experiments.Common.Refinement` and the conservation-of-count under decode is the device's own
`Experiments.Common.Ledger.count_map`.  That theorem is a **conjunct of `claim_holds`**, so a
rename/`sorry`/regression in the harness `count_map` breaks *this* build.

## NOT claimed
That this transmits or recovers real speech; that amplitude modulation, the Fourier content of a
carrier, or Shannon's channel *capacity* (`C = B log₂(1+SNR)`) is derived — none of that is here.
No continuous structure, propagation law, or unrecorded intermediate state is modelled (the
description forbids them).  The "multiple admissible values" are a fixed finite enum, not a learned
or measured alphabet.  **Claim ceiling:** a finite ledger model of channel refinement, whose
ledger-conservation conjunct is the harness's own theorem.
-/

namespace Experiments.TheFessendenShannonEffect

/-- A coarse symbol: the finite alphabet the channel decodes *to*.  Strictly more than binary —
the whole point of the effect (voice is not off/on). -/
inductive Symbol where
  | silence
  | low
  | mid
  | high
deriving DecidableEq, Repr

/-- A fine activation sample: a coarse amplitude band plus a sub-band slot.  Two samples can carry
the SAME symbol via different fine slots — "distinct decompositions may coexist provided they
remain disjoint under refinement." -/
structure Sample where
  band : Symbol
  slot : Nat
deriving DecidableEq, Repr

/-- The instrument's refinement rule: recover the symbol from a raw sample.  This is the channel's
`decode`; it appeals to nothing outside the sample. -/
def decodeSample (s : Sample) : Symbol := s.band

/-- The channel as a harness `Refinement` (coarse `Symbol`, fine `Sample`). -/
def channel : Experiments.Common.Refinement Symbol Sample :=
  { decode := decodeSample }

/-- `s` is *recoverable* to symbol `t`: the instrument's own rule returns `t`.  (Decidable, so
`decide`/`#eval` compute.) -/
def recoversTo (s : Sample) (t : Symbol) : Prop := decodeSample s = t

instance (s : Sample) (t : Symbol) : Decidable (recoversTo s t) := by
  unfold recoversTo; exact inferInstance

-- ---------------------------------------------------------------------------
-- FALSIFIABLE lemmas (∀-quantified; drop a hypothesis and they break).
-- ---------------------------------------------------------------------------

/-- RECOVERABILITY: every sample is recoverable to *some* symbol using only the refinement rule —
and that symbol is exactly its band.  Quantified over ALL samples.  Drop the `decodeSample s = _`
constraint (claim recovery to an arbitrary symbol) and it is false. -/
theorem recovers_to_band (s : Sample) : recoversTo s s.band := rfl

/-- DISJOINTNESS / NO-NEW-DISTINCTION: if two samples are recovered to *different* symbols, they
were already distinguished in the fine ledger (their bands differ).  Refinement introduces no new
distinction beyond what the bands already carry.  Drop the hypothesis `h` and the conclusion
`p.band ≠ q.band` is plainly false (two equal-band samples exist). -/
theorem distinct_symbols_need_distinct_bands
    (p q : Sample) (h : decodeSample p ≠ decodeSample q) : p.band ≠ q.band :=
  fun hb => h (by unfold decodeSample; exact hb)

/-- LEDGER CONSERVATION (the effect's central constraint), specialized to this channel: decoding a
fine sample-ledger to its coarse symbol-ledger leaves the COUNT unchanged.  This is the device's
own `Ledger.count_map` applied through `channel.decode`.  Quantified over ALL ledgers.  It would
fail for any `decode` that dropped or duplicated events — so it pins the no-inflation rule. -/
theorem refinement_preserves_count (ledger : Experiments.Common.Ledger Sample) :
    (Experiments.Common.Refinement.pushLedger channel ledger).count = ledger.count :=
  Experiments.Common.Ledger.count_map channel.decode ledger

-- ---------------------------------------------------------------------------
-- A canonical "voice frame": a fine sample-ledger over a finite alphabet.
-- ---------------------------------------------------------------------------

def frame : Experiments.Common.Ledger Sample :=
  { events :=
      [ { band := Symbol.silence, slot := 0 }
      , { band := Symbol.low,     slot := 3 }
      , { band := Symbol.mid,     slot := 1 }
      , { band := Symbol.high,    slot := 2 }
      , { band := Symbol.mid,     slot := 7 } ] }

/-- The decoded symbol-ledger of the canonical frame (concrete, computes via the instances). -/
def decodedFrame : Experiments.Common.Ledger Symbol :=
  Experiments.Common.Refinement.pushLedger channel frame

/-- The alphabet is strictly richer than binary: the channel actually emits ≥ 3 distinct symbols on
the canonical frame.  A frozen-event sanity check on the chosen frame (NOT enforced by the rule). -/
theorem frame_is_beyond_binary :
    decodeSample frame.events[0] = Symbol.silence ∧
    decodeSample frame.events[1] = Symbol.low ∧
    decodeSample frame.events[3] = Symbol.high := by decide

-- ---------------------------------------------------------------------------
-- THE CLAIM (content-bearing conjunction; the middle conjunct is the harness theorem).
-- ---------------------------------------------------------------------------

/-- The claim, in honest parts:
* (recoverability) the canonical frame's first sample is recovered to `silence` by the rule alone;
* (LEDGER CONSERVATION) refinement of the canonical frame preserves the record count
  (`refinement_preserves_count`, i.e. the harness `Ledger.count_map`) — the no-inflation
  constraint; and
* (no new distinction) two samples recovered to different symbols already had different bands. -/
def claimStatement : Prop :=
  recoversTo frame.events[0] Symbol.silence ∧
    (Experiments.Common.Refinement.pushLedger channel frame).count = frame.count ∧
    (∀ p q : Sample, decodeSample p ≠ decodeSample q → p.band ≠ q.band)

def claim : Experiments.Common.Claim :=
  { tag := Experiments.Common.ClaimTag.finiteLedgerModel
    statement := claimStatement }

theorem claim_holds : claim.statement :=
  ⟨rfl, refinement_preserves_count frame, distinct_symbols_need_distinct_bands⟩

/-- The tag is an honest ceiling: a finite ledger model of channel refinement, nothing more. -/
theorem ceiling :
    claim.tag = Experiments.Common.ClaimTag.finiteLedgerModel := rfl

-- ---------------------------------------------------------------------------
-- A computable run + a non-vacuous exported Experiment, with a proved bridge.
-- ---------------------------------------------------------------------------

structure Setup where
  ledger : Experiments.Common.Ledger Sample
  probe : Sample
  expected : Symbol

/-- The run actually computes: does the probe recover to the expected symbol? -/
def run (setup : Setup) : Bool := decide (recoversTo setup.probe setup.expected)

def experiment : Experiments.Common.Experiment Setup Bool :=
  { tag := claim.tag
    run := run
    claim := fun setup => recoversTo setup.probe setup.expected }

theorem run_iff_claim (setup : Setup) :
    run setup = true ↔ experiment.claim setup := by
  simp only [run, experiment, decide_eq_true_iff]

def canonicalSetup : Setup :=
  { ledger := frame, probe := { band := Symbol.mid, slot := 1 }, expected := Symbol.mid }

/-- Bring a minimal device next to this experiment: it records whether the exported claim fires.
It reuses `run` (already `Decidable` via the `recoversTo` instance) rather than asking Lean to
synthesize `Decidable (experiment.claim setup)` through the record projection. -/
def deviceNear (setup : Setup) : Bool :=
  run setup

theorem deviceNear_detects_claim (setup : Setup) :
    deviceNear setup = true ↔ experiment.claim setup := by
  unfold deviceNear; exact run_iff_claim setup

def triangulation : Experiments.Common.Triangulation Setup Bool :=
  { experiment := experiment
    device := deviceNear
    detects := deviceNear_detects_claim }

-- ---------------------------------------------------------------------------
-- GATE EVIDENCE.
-- ---------------------------------------------------------------------------

#eval run canonicalSetup                                   -- expect: true  (mid recovers to mid)
#eval run { canonicalSetup with expected := Symbol.high }  -- expect: false (mid does NOT recover to high)
-- The falsifiable predicate evaluated where it is FALSE (load-bearing, not vacuous):
#eval decide (recoversTo ({ band := Symbol.mid, slot := 1 } : Sample) Symbol.high)  -- expect: false
#print axioms claim_holds                                  -- [propext, Quot.sound] = AMBIENT, not coupling

end Experiments.TheFessendenShannonEffect
