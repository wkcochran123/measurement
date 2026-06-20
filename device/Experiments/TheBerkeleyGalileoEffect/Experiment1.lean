import Experiments.Common

/-!
# The Berkeley-Galileo Effect — a coarse-graining / resolution-floor model

Source description: `instrument/chapters/01.tex:404` (`ph:fact-effect`).

## Physics (modelled finitely)
Berkeley objected to fluxions because sub-resolution quantities cannot be produced,
manipulated, or distinguished by any finite procedure. Galileo tied admissible claims
to operations that leave recoverable traces. The operational core:

  *No finite instrument can distinguish arbitrarily small variation.* Below an
  instrument's resolution threshold, two distinct candidate histories produce the
  **same experimental ledger** — they cast the same coarse shadow. The same two
  histories may, however, be separated by a **finer** instrument.

We model an instrument as a coarse readout `project : State -> Shadow` (here, integer
division by a resolution `res`). Two states are *indistinguishable* to that instrument
iff they have the same shadow. The constraint of the effect — no operator on the ledger
may map indistinguishable histories to distinct states — is the statement that the
coarse readout cannot resolve a sub-threshold gap, while a refinement (`res = 1`) can.

This is a `Projection.sameShadow` story: the harness supplies the shadow relation, and
`claim_holds` is discharged in part by `Experiments.Common.Projection.sameShadow` applied
to a witnessed pair — so a rename/regression of that harness symbol breaks THIS build.

## NOT claimed
That this is a calculus of fluxions, or that real instruments coarse-grain by integer
division; nothing about continuity, limits, derivatives, or the actual reals; no claim
that the resolution floor is a physical constant. This is a finite stand-in: a coarse
readout that loses a sub-threshold distinction one finer readout recovers. **Claim ceiling:**
a finite ledger model of the resolution floor; one conjunct is the harness's own
`sameShadow` theorem.
-/

namespace Experiments.TheBerkeleyGalileoEffect

/-- A physical state, modelled as a single integer reading (e.g. a position tick). -/
structure Reading where
  value : Nat
deriving DecidableEq, Repr

/-- An instrument: a coarse readout with a finite resolution `res` (the floor).
A reading's recorded shadow is `value / res` — everything within one `res`-window
collapses to the same coarse value. `res = 1` is the perfect (refining) instrument. -/
structure Instrument where
  res : Nat
deriving Repr

namespace Instrument

/-- The coarse shadow this instrument records of a reading. -/
def shadow (i : Instrument) (r : Reading) : Nat :=
  r.value / i.res

/-- The harness projection induced by this instrument. -/
def projection (i : Instrument) : Experiments.Common.Projection Reading Nat :=
  { project := fun r => i.shadow r }

/-- Two readings are INDISTINGUISHABLE to `i` iff they cast the same shadow. This is
exactly `Experiments.Common.Projection.sameShadow` of the induced projection. -/
def indistinguishable (i : Instrument) (r s : Reading) : Prop :=
  Experiments.Common.Projection.sameShadow i.projection r s

instance (i : Instrument) (r s : Reading) : Decidable (i.indistinguishable r s) := by
  unfold indistinguishable Experiments.Common.Projection.sameShadow projection shadow
  exact inferInstance

end Instrument

-- ---------------------------------------------------------------------------
-- FALSIFIABLE lemmas. Each is ∀-quantified and breaks if a hypothesis is dropped.
-- ---------------------------------------------------------------------------

/-- THE RESOLUTION FLOOR (falsifiable): for a coarse instrument with `res ≥ 1`, any two
readings whose values land in the SAME `res`-window are indistinguishable. The hypothesis
`r.value / i.res = s.value / i.res` is load-bearing — drop it and the conclusion is false
(two readings in different windows are distinguishable). -/
theorem sameWindow_indistinguishable
    (i : Instrument) (r s : Reading)
    (h : r.value / i.res = s.value / i.res) :
    i.indistinguishable r s := by
  unfold Instrument.indistinguishable Experiments.Common.Projection.sameShadow
    Instrument.projection Instrument.shadow
  exact h

/-- DISTINCT WINDOWS ARE DISTINGUISHABLE (falsifiable): if two readings fall in different
`res`-windows, the coarse instrument DOES separate them. Hypothesis `h` is load-bearing —
without a window-difference there is nothing to distinguish. -/
theorem differentWindow_distinguishable
    (i : Instrument) (r s : Reading)
    (h : r.value / i.res ≠ s.value / i.res) :
    ¬ i.indistinguishable r s := by
  unfold Instrument.indistinguishable Experiments.Common.Projection.sameShadow
    Instrument.projection Instrument.shadow
  exact h

/-- REFINEMENT RECOVERS THE GAP (falsifiable): the perfect instrument (`res = 1`) reads off
the raw value, so two readings are indistinguishable to it ONLY if they are literally equal.
Hypothesis `i.res = 1` is load-bearing — a coarser instrument fails this (sub-threshold
distinct readings collapse). -/
theorem perfectInstrument_separates
    (i : Instrument) (r s : Reading)
    (hres : i.res = 1) (h : i.indistinguishable r s) :
    r.value = s.value := by
  unfold Instrument.indistinguishable Experiments.Common.Projection.sameShadow
    Instrument.projection Instrument.shadow at h
  rw [hres] at h
  simpa using h

-- ---------------------------------------------------------------------------
-- The canonical scenario: a sub-threshold pair the coarse floor cannot resolve.
-- ---------------------------------------------------------------------------

/-- A coarse instrument with resolution 10 (the floor). -/
def coarse : Instrument := { res := 10 }

/-- The refining instrument: resolution 1, reads the raw value. -/
def fine : Instrument := { res := 1 }

/-- Two readings 4 and 7 — a genuine sub-threshold gap (both in window `0`). -/
def lo : Reading := { value := 4 }
def hi : Reading := { value := 7 }

/-- The coarse floor CANNOT distinguish them (same shadow `0`). -/
theorem coarse_blind : coarse.indistinguishable lo hi := by decide

/-- The fine (refining) instrument CAN distinguish them. -/
theorem fine_resolves : ¬ fine.indistinguishable lo hi := by decide

-- ---------------------------------------------------------------------------
-- THE CLAIM (content-bearing conjunction; one conjunct is the harness theorem).
-- ---------------------------------------------------------------------------

/-- The claim, in honest parts:
* (floor blinds) the coarse instrument cannot distinguish the sub-threshold pair — this
  conjunct IS `Experiments.Common.Projection.sameShadow coarse.projection lo hi`, so a
  regression of the harness `sameShadow` symbol breaks this build;
* (refinement recovers) the fine instrument DOES distinguish them; and
* (the gap is real) the two readings are genuinely distinct readings (`lo ≠ hi`).
Together: a distinction that is invisible below the floor is recovered by refinement —
the operational content of the Berkeley-Galileo effect. -/
def claimStatement : Prop :=
  Experiments.Common.Projection.sameShadow coarse.projection lo hi ∧
    ¬ fine.indistinguishable lo hi ∧
    lo ≠ hi

def claim : Experiments.Common.Claim :=
  { tag := Experiments.Common.ClaimTag.finiteLedgerModel
    statement := claimStatement }

theorem claim_holds : claim.statement :=
  ⟨coarse_blind, fine_resolves, by decide⟩

/-- The tag is an honest ceiling: a finite ledger model of the resolution floor. -/
theorem ceiling :
    claim.tag = Experiments.Common.ClaimTag.finiteLedgerModel := rfl

-- ---------------------------------------------------------------------------
-- A computable run + a NON-vacuous Experiment.claim, with a proved bridge.
-- ---------------------------------------------------------------------------

structure Setup where
  instrument : Instrument
  first : Reading
  second : Reading

/-- The run computes whether the instrument is BLIND to the pair (same shadow). -/
def run (s : Setup) : Bool := decide (s.instrument.indistinguishable s.first s.second)

def experiment : Experiments.Common.Experiment Setup Bool :=
  { tag := claim.tag
    run := run
    claim := fun s => s.instrument.indistinguishable s.first s.second }

theorem run_iff_claim (s : Setup) :
    run s = true ↔ experiment.claim s := by
  simp only [run, experiment, decide_eq_true_iff]

def coarseSetup : Setup := { instrument := coarse, first := lo, second := hi }
def fineSetup : Setup := { instrument := fine, first := lo, second := hi }

#eval run coarseSetup                 -- expect: true   (floor is blind)
#eval run fineSetup                   -- expect: false  (refinement resolves)
#print axioms claim_holds
#eval fine.indistinguishable lo hi    -- expect: false  (falsifiable pred at a FALSE config)

/-- Bring a minimal device next to this experiment: it records whether the exported claim fires.
We decide on the unfolded predicate (the instance lives at `Instrument.indistinguishable`). -/
def deviceNear (setup : Setup) : Bool :=
  decide (setup.instrument.indistinguishable setup.first setup.second)

theorem deviceNear_detects_claim (setup : Setup) :
    deviceNear setup = true ↔ experiment.claim setup := by
  simp only [deviceNear, experiment, decide_eq_true_iff]

def triangulation : Experiments.Common.Triangulation Setup Bool :=
  { experiment := experiment
    device := deviceNear
    detects := deviceNear_detects_claim }

end Experiments.TheBerkeleyGalileoEffect
