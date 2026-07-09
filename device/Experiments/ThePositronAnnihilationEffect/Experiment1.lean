import Experiments.Common
import Measurement.Episode83

/-!
# The Positron Annihilation Effect — a worked EXEMPLAR for the testing team

This file is the SHAPE every effect test should have (see `device/Experiments/FEEDBACK2.md`).
It deliberately does the things the 3-`Nat` `CountSetup` template does **not**:

1. an **effect-specific domain** (`Photon`, `Detector`) — not three undifferentiated `Nat`s;
2. genuinely **falsifiable** quantified lemmas (`∀`, would break if the model were wrong) —
   one per conjunct of the detection rule, so none of the rule can silently rot;
3. a **content-bearing** claim — a real conjunction, never `True`;
4. an **honest tag** + a candid disclaimer of what it does *not* claim;
5. it **couples to the real device**: `claim_holds` is discharged by `Measurement` theorems, so
   the device *symbols* sit in the proof term and a `sorry`/rename/regression in `Measurement`
   breaks *this* file's build (FEEDBACK2 §1). Two flavours of coupling, deliberately mixed:
   `positron_over_tiltedPath`/`no_positron_over_flatPath` are **value/sign**-coupled (they read
   the actual δ² computation, so a sign regression in the device fails here); `split_cancels` is
   a **structural** identity (`x+(-x)=0`) — it pins the *symbol*, not a measured value.
   NOTE: the `#print axioms claim_holds` line at the bottom prints `[propext, Quot.sound]`, but
   that is the **ambient `omega`/`decide` footprint** every such proof carries — it is *not*
   evidence of coupling. The coupling is the device symbols above, not the axiom list.

It also shows a `Decidable`-instance trick (`instance … := by unfold …; exact inferInstance`) so
that `decide`/`#eval` see through these richer `Prop` predicates. (The 3-`Nat` template never
needed it — `CountOutput` is already `Decidable`; that suite's real problem is content/vacuity,
and separately its `claim_holds` failed to *compile* only because `decide` could not unfold the
opaque `claim` projection — fixed there with `unfold`, not with instances.)

## Physics (modelled finitely)
A positron is detected by its **annihilation**. It meets an electron; the two signed readings
cancel (the device's `split_cancels`); two 511 keV photons leave **back-to-back**. A coincidence
detector registers a positron iff it sees two photons, **both on the 511 keV line** (within a
finite window — the floor) and in **opposite directions**.

## NOT claimed
That this detects real antimatter; that 511 keV is *derived* (it is a labelled constant — the
electron rest energy); any QED amplitude; anything about the *rate* of annihilation. The energy
gate is applied to each photon **independently**, so the model does NOT enforce equal photon
energies or cross-pair energy conservation — only that both gammas land in the line window.
**Claim ceiling:** a finite ledger model of the coincidence logic, two of whose conjuncts are the
device's own theorems.
-/

namespace Experiments.ThePositronAnnihilationEffect

/-- A detected gamma: an energy (keV) and a coarse direction slot on a finite ring. -/
structure Photon where
  energyKeV : Nat
  dir : Nat
deriving DecidableEq, Repr

/-- The apparatus: the annihilation line (511 keV), a finite acceptance window (the floor), and
the number of direction slots ("back-to-back" = half a turn apart). -/
structure Detector where
  line : Nat
  window : Nat
  slots : Nat
deriving Repr

/-- The standard apparatus: the 511 keV line, an 8 keV window, a 360-slot direction ring. -/
def defaultDetector : Detector := { line := 511, window := 8, slots := 360 }

namespace Detector

/-- `p` sits on the annihilation line, within the window: `line-window ≤ E ≤ line+window`
(written `Nat`-safely, so there is no truncated subtraction). -/
def onLine (d : Detector) (p : Photon) : Prop :=
  d.line ≤ p.energyKeV + d.window ∧ p.energyKeV ≤ d.line + d.window

/-- `p` and `q` are back-to-back: their direction slots differ by half the ring. -/
def backToBack (d : Detector) (p q : Photon) : Prop :=
  (p.dir + d.slots / 2) % d.slots = q.dir % d.slots

/-- THE DETECTION RULE: a coincident, back-to-back pair, both on the line, registers an
annihilation — hence a positron was present. **All three conjuncts are required** — and each one
is pinned by a falsifiable lemma below, so dropping any of them fails the build. -/
def registers (d : Detector) (p q : Photon) : Prop :=
  d.onLine p ∧ d.onLine q ∧ d.backToBack p q

-- Make the richer predicates DECIDABLE so `decide`/`#eval` work. (Alternative a copier could pick:
-- mark `onLine`/`backToBack`/`registers` `@[reducible]` and drop these blocks; the tradeoff is
-- transparency-everywhere vs. an explicit instance — choose deliberately, don't cargo-cult.)
instance (d : Detector) (p : Photon) : Decidable (d.onLine p) := by
  unfold onLine; exact inferInstance
instance (d : Detector) (p q : Photon) : Decidable (d.backToBack p q) := by
  unfold backToBack; exact inferInstance
instance (d : Detector) (p q : Photon) : Decidable (d.registers p q) := by
  unfold registers; exact inferInstance

end Detector

-- ---------------------------------------------------------------------------
-- FALSIFIABLE lemmas: ONE PER CONJUNCT, so the whole rule is load-bearing.
-- Each would break if `registers` dropped that conjunct (cf. CDE.belowThresholdInvisible).
-- ---------------------------------------------------------------------------

/-- Energy balance on the LEFT photon is necessary. -/
theorem offLineLeft_not_registered
    (d : Detector) (p q : Photon) (h : ¬ d.onLine p) : ¬ d.registers p q :=
  fun hr => h hr.1

/-- Energy balance on the RIGHT photon is necessary (pins the middle conjunct `.2.1`). -/
theorem offLineRight_not_registered
    (d : Detector) (p q : Photon) (h : ¬ d.onLine q) : ¬ d.registers p q :=
  fun hr => h hr.2.1

/-- Momentum balance is necessary: a coincidence that is **not** back-to-back is never
registered.  Quantified over ALL detectors and photon pairs. -/
theorem not_backToBack_not_registered
    (d : Detector) (p q : Photon) (h : ¬ d.backToBack p q) : ¬ d.registers p q :=
  fun hr => h hr.2.2

-- ---------------------------------------------------------------------------
-- The canonical annihilation event.
-- ---------------------------------------------------------------------------

/-- The two gammas of a clean annihilation: both on the 511 keV line, opposite directions. -/
def gammaA : Photon := { energyKeV := 511, dir := 0 }
def gammaB : Photon := { energyKeV := 511, dir := 180 }

/-- The apparatus registers the canonical pair (concrete, via the `Decidable` instance). -/
theorem registers_canonical : defaultDetector.registers gammaA gammaB := by decide

/-- The two gammas carry off `2 × 511 keV` (a frozen-literal arithmetic check on the chosen
event, not a property enforced by `registers`). -/
theorem energy_is_pair_rest_mass :
    gammaA.energyKeV + gammaB.energyKeV = 2 * defaultDetector.line := by decide

-- ---------------------------------------------------------------------------
-- THE CLAIM (content-bearing; three of four conjuncts are the device's own theorems).
-- ---------------------------------------------------------------------------

/-- The claim, in honest halves:
* (detection) the apparatus registers the canonical coincidence — proved here;
* (annihilation = cancellation) the electron and positron readings sum to zero
  (`Measurement.split_cancels` — a structural identity, symbol-coupled);
* (a positron appears over a tilted flux) `Measurement.positron_over_tiltedPath`; and
* (and NOT over a flat one) `Measurement.no_positron_over_flatPath`.
The last two read the device's actual δ² **sign** computation, so a sign regression in
`Measurement` fails this build — value-coupling, not just a name. -/
def claimStatement : Prop :=
  defaultDetector.registers gammaA gammaB ∧
    (Measurement.electronMeasurement.relVel + Measurement.positronReading.relVel = 0) ∧
    Measurement.HasPositronEvent Measurement.tiltedEvents ∧
    ¬ Measurement.HasPositronEvent Measurement.flatEvents

def claim : Experiments.Common.Claim :=
  { tag := Experiments.Common.ClaimTag.finiteLedgerModel
    statement := claimStatement }

theorem claim_holds : claim.statement :=
  ⟨registers_canonical, Measurement.split_cancels,
    Measurement.positron_over_tiltedPath, Measurement.no_positron_over_flatPath⟩

/-- The tag is an honest ceiling: a finite ledger model, nothing more.  (FEEDBACK2 §2's
"tag-derived obligation" fence is NOT implemented in the harness — `requiredModelKind` does not
exist — so the tag here is still a convention, not mechanically enforced.) -/
theorem ceiling : claim.tag = Experiments.Common.ClaimTag.finiteLedgerModel := rfl

-- ---------------------------------------------------------------------------
-- A computable run + a NON-vacuous Experiment.claim, with a proved bridge between them.
-- ---------------------------------------------------------------------------

structure Setup where
  detector : Detector
  left : Photon
  right : Photon

/-- The run actually computes — thanks to the `Decidable` instances above. -/
def run (s : Setup) : Bool := decide (s.detector.registers s.left s.right)

/-- Unlike the suite's `claim := fun _ => …`, the exported claim is a genuine function of the
setup; and this bridge pins it to `run`, so the claim body cannot be silently swapped for
`fun _ => True` without breaking the proof. -/
def experiment : Experiments.Common.Experiment Setup Bool :=
  { tag := claim.tag
    run := run
    claim := fun s => s.detector.registers s.left s.right }

theorem run_iff_claim (s : Setup) :
    run s = true ↔ experiment.claim s := by
  simp only [run, experiment, decide_eq_true_iff]

def canonicalSetup : Setup := { detector := defaultDetector, left := gammaA, right := gammaB }

#eval run canonicalSetup                              -- expect: true
#eval run { canonicalSetup with right := gammaA }     -- expect: false  (not back-to-back)
#print axioms claim_holds                             -- [propext, Quot.sound] = AMBIENT, not coupling

/-- Bring a minimal device next to this experiment: it records whether the exported claim fires. -/
def deviceNear (setup : Setup) : Bool :=
  run setup

theorem deviceNear_detects_claim (setup : Setup) :
    deviceNear setup = true ↔ experiment.claim setup := by
  simpa [deviceNear] using run_iff_claim setup

def triangulation : Experiments.Common.Triangulation Setup Bool :=
  { experiment := experiment
    device := deviceNear
    detects := deviceNear_detects_claim }

end Experiments.ThePositronAnnihilationEffect
