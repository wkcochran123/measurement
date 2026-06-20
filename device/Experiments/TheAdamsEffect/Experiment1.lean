import Experiments.Common

/-!
# The Adams Effect — a representational coincidence is not a measurement

Source: `instrument/chapters/02.tex:1201` (`ph:representation`, "The Adams Effect").

## Physics / phenomenon (modelled finitely)
Adams's joke: the number `42` is presented as the answer to everything, with the
decoding map deliberately withheld — so the symbol answers nothing. The
phenomenon's CONSTRAINT: a numerical value is explanatory only when its
appearance is licensed by a **decoding map** grounded in admissible refinement.
A bare symbol, absent a justified decoder, is noise.

We model this with an effect-specific domain:
* `RawSymbol` — an emitted token (a `code : Nat`), the un-interpreted output of a
  computation. `42` is just `⟨42⟩`.
* `Reading` — a decoded value (`answer : Nat`) PLUS a `licensed` flag recording
  whether the decoding map was justified.
* a `Decoder` carries the decode map AND whether it is grounded in admissible
  refinement (`grounded`). Adams's prankster decoder is NOT grounded.

The content: decoding COMMUTES with tallying (a refinement/`count_map` identity —
relabelling tokens never changes how many you have, which is exactly why the
COUNT carries no answer); and a symbol is explanatory ONLY through a grounded
decoder — the ungrounded decoder produces an `unlicensed` reading whatever the
symbol, so `42` is `unlicensed` under the prankster decoder.

## NOT claimed
That `42` is special, or unspecial, as a physical/mathematical fact; any claim
about which decoders are "really" admissible (we model `grounded` as a flag, we
do NOT derive admissibility); anything about Adams, computation in general, or
the ultimate question. **Claim ceiling:** a finite ledger/refinement model of the
"no value without a licensed decoder" constraint, one conjunct of which is the
harness's own `Ledger.count_map` (decoding preserves the tally).
-/

namespace Experiments.TheAdamsEffect

/-- A raw emitted token: the un-interpreted output of a computation. `42` is `⟨42⟩`. -/
structure RawSymbol where
  code : Nat
deriving DecidableEq, Repr

/-- A decoded reading: a value PLUS whether the decoding that produced it was licensed
(grounded in admissible refinement). An unlicensed reading is noise dressed as an answer. -/
structure Reading where
  answer : Nat
  licensed : Bool
deriving DecidableEq, Repr

/-- A decoder maps tokens to values, and records whether it is grounded in admissible
refinement. Adams's prankster decoder is NOT grounded. -/
structure Decoder where
  decode : Nat -> Nat
  grounded : Bool

namespace Decoder

/-- Decode a raw symbol into a reading: the value is `decode code`, and the reading is
`licensed` exactly when the decoder is `grounded`. A symbol becomes an answer ONLY through
a grounded decoder. -/
def read (d : Decoder) (s : RawSymbol) : Reading :=
  { answer := d.decode s.code, licensed := d.grounded }

/-- The phenomenon's predicate: this token, under this decoder, is treated as explanatory. -/
def explanatory (d : Decoder) (s : RawSymbol) : Prop :=
  (d.read s).licensed = true

instance (d : Decoder) (s : RawSymbol) : Decidable (d.explanatory s) := by
  unfold explanatory read; exact inferInstance

end Decoder

/-- The prankster decoder: it returns the token verbatim but is UNGROUNDED — Adams hands you
`42` with no justified decoding map. -/
def pranksterDecoder : Decoder := { decode := fun n => n, grounded := false }

/-- A genuine, grounded decoder (a stand-in for one licensed by admissible refinement). -/
def groundedDecoder : Decoder := { decode := fun n => n, grounded := true }

/-- The famous symbol. -/
def fortyTwo : RawSymbol := { code := 42 }

-- ---------------------------------------------------------------------------
-- FALSIFIABLE lemmas: each would break if a hypothesis were dropped.
-- ---------------------------------------------------------------------------

/-- THE no-go (load-bearing on `grounded`): an UNGROUNDED decoder NEVER yields an explanatory
reading — for ANY symbol. Drop the hypothesis `d.grounded = false` and this is false (a
grounded decoder makes everything explanatory), so the hypothesis is doing the work. -/
theorem ungrounded_never_explanatory
    (d : Decoder) (s : RawSymbol) (h : d.grounded = false) : ¬ d.explanatory s := by
  unfold Decoder.explanatory Decoder.read
  simp only [h]
  exact Bool.noConfusion

/-- Dual direction (load-bearing on `grounded = true`): a GROUNDED decoder licenses every
reading. Drop the hypothesis and it fails (the prankster does not). -/
theorem grounded_is_explanatory
    (d : Decoder) (s : RawSymbol) (h : d.grounded = true) : d.explanatory s := by
  unfold Decoder.explanatory Decoder.read
  exact h

/-- Concrete corollary: Adams's `42`, under the prankster decoder, is NOT explanatory. -/
theorem fortyTwo_not_explanatory : ¬ pranksterDecoder.explanatory fortyTwo := by
  decide

-- ---------------------------------------------------------------------------
-- The refinement coupling: decoding is a Refinement, and decoding a ledger of
-- symbols PRESERVES THE COUNT (Experiments.Common.Ledger.count_map). The tally is
-- decoder-blind: relabelling tokens cannot change how many there are — which is
-- exactly why the COUNT alone answers nothing.
-- ---------------------------------------------------------------------------

/-- Decoding a symbol-token to its bare value, as a `Refinement` (coarse = `Nat` values,
fine = `RawSymbol` tokens). -/
def valueRefinement (d : Decoder) : Experiments.Common.Refinement Nat RawSymbol :=
  { decode := fun s => d.decode s.code }

/-- A finite ledger of emitted symbols. -/
def emittedLedger : Experiments.Common.Ledger RawSymbol :=
  { events := [fortyTwo, { code := 7 }, { code := 0 }] }

/-- COUPLING (load-bearing, harness): pushing the ledger through the decoding refinement
preserves the count — discharged by `Experiments.Common.Ledger.count_map`. A regression in
that harness theorem (or its rename) breaks THIS build. The count is decoder-blind, so it
carries no answer. -/
theorem decoding_preserves_count (d : Decoder) :
    ((valueRefinement d).pushLedger emittedLedger).count = emittedLedger.count :=
  Experiments.Common.Ledger.count_map (valueRefinement d).decode emittedLedger

-- ---------------------------------------------------------------------------
-- THE CLAIM (content-bearing conjunction).
-- ---------------------------------------------------------------------------

/-- The claim, in honest parts:
* (no-go) Adams's `42` under the ungrounded prankster decoder is NOT explanatory — the
  representational coincidence is not a measurement;
* (licensing) a grounded decoder DOES license `42` (the same symbol, now an answer) —
  so the block is about the decoder, not the number; and
* (refinement coupling) decoding the symbol-ledger preserves the tally
  (`Ledger.count_map`) — the count is decoder-blind, which is why a bare number answers
  nothing. -/
def claimStatement : Prop :=
  ¬ pranksterDecoder.explanatory fortyTwo ∧
    groundedDecoder.explanatory fortyTwo ∧
    ((valueRefinement pranksterDecoder).pushLedger emittedLedger).count = emittedLedger.count

def claim : Experiments.Common.Claim :=
  { tag := Experiments.Common.ClaimTag.inadmissibilityNoGo
    statement := claimStatement }

theorem claim_holds : claim.statement :=
  ⟨fortyTwo_not_explanatory,
    grounded_is_explanatory groundedDecoder fortyTwo rfl,
    decoding_preserves_count pranksterDecoder⟩

/-- The tag is an honest ceiling: an impossibility/no-go (a bare value cannot be explanatory
without a grounded decoder), nothing more. -/
theorem ceiling :
    claim.tag = Experiments.Common.ClaimTag.inadmissibilityNoGo := rfl

-- ---------------------------------------------------------------------------
-- A computable run + a non-vacuous Experiment.claim, with a proved bridge.
-- ---------------------------------------------------------------------------

structure Setup where
  decoder : Decoder
  symbol : RawSymbol

/-- The run computes (via the `Decidable` instance): is this symbol explanatory here? -/
def run (s : Setup) : Bool := decide (s.decoder.explanatory s.symbol)

def experiment : Experiments.Common.Experiment Setup Bool :=
  { tag := claim.tag
    run := run
    claim := fun s => s.decoder.explanatory s.symbol }

theorem run_iff_claim (s : Setup) :
    run s = true ↔ experiment.claim s := by
  simp only [run, experiment, decide_eq_true_iff]

def pranksterSetup : Setup := { decoder := pranksterDecoder, symbol := fortyTwo }
def groundedSetup : Setup := { decoder := groundedDecoder, symbol := fortyTwo }

#eval run pranksterSetup    -- expect: false  (ungrounded: 42 answers nothing)
#eval run groundedSetup     -- expect: true   (grounded decoder licenses the reading)
#print axioms claim_holds   -- ambient [propext, Quot.sound], NOT coupling

-- Gate evidence: the falsifiable predicate is load-bearing, evaluated where it is FALSE.
#eval decide (pranksterDecoder.explanatory fortyTwo)   -- expect: false

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

end Experiments.TheAdamsEffect
