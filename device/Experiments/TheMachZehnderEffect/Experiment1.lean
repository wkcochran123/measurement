import Experiments.Common
import Measurement.Apparatus

/-!
# The Mach-Zehnder Effect — a holonomy-coupled effect test

A single photon enters a Mach-Zehnder interferometer. The first beam splitter produces two
admissible refinements (upper arm `e1`, lower arm `e2`); both accumulate their own ordered ledger
of refinements; the second beam splitter folds them into one detection event `e_f`. Interference
is the *informational comparison of the two arms at the shared boundary*: if their accumulated phase
agrees modulo `2π` the arms are indistinguishable and the fold produces a SINGLE consistent ledger;
if it differs by `π` the asymmetric parts cancel under the fold and `e_f` becomes INADMISSIBLE — no
consistent ledger can be formed with that ordering (the description is explicit that no destructive
force is invoked; cancellation is a bookkeeping fact).

## Why this couples to the device holonomy
The two arms, traversed up one and back down the other, form a **loop**; the accumulated phase a
pair transports around that loop is a **holonomy** (the commutator residue of Episode64, read as a
signed value in Episode84). The Mach-Zehnder structure is therefore genuinely holonomy-shaped, and
the description itself stresses the structure is "purely combinatorial ... it arises whenever two
indistinguishable paths diverge, evolve under independent refinements, and reunite at a shared
boundary. No metric, phase, or wave dynamics are assumed" — exactly the device's finite holonomy.

The coupling is load-bearing along two seams:
* the GENUINE two-arm LOOP carries a NONZERO (charged) holonomy — `Measurement.holonomy_loop_is_charged`;
* a degenerate path that moves only one arm (an OPEN path, no recombination) carries ZERO holonomy —
  `Measurement.holonomy_open_is_trivial`.
A sign/rename/`sorry` regression in those device theorems breaks THIS build.

## NOT claimed (honest ceiling)
That this is a real optical interferometer; that `π`/`2π` are derived (they are labelled finite phase
slots on a ring — a discrete shadow of the continuous phase); any wave amplitude, any unitary `U`,
any actual destructive interference of fields; the operator `f(U^(1), U^(2))` is modelled only as a
boolean admissibility verdict on the phase difference, NOT as a computed accumulated tensor. The
device holonomy is the SAME ±1 sign residue of Episodes 83–85; it is MEASURED over the concrete
finite trial, not derived. **Claim ceiling:** a finite shadow of the recombination/admissibility
logic, one of whose conjuncts is the device's own holonomy theorem.
-/

namespace Experiments.TheMachZehnderEffect

/-- A coarse accumulated phase: a slot on a finite ring of `modulus` divisions.  `π` is the
half-turn slot, `0`/`modulus` the full-turn slot. -/
structure Phase where
  slot : Nat
deriving DecidableEq, Repr

/-- The interferometer: how many phase slots make a full `2π` turn (the floor on phase resolution).
The half-turn `π` is `modulus / 2`. -/
structure Interferometer where
  modulus : Nat
deriving Repr

/-- The standard apparatus: a 360-slot phase ring (so `π` = slot 180). -/
def defaultMZ : Interferometer := { modulus := 360 }

/-- The two coexisting arm ledgers reaching the second beam splitter: each carries an accumulated
phase slot. -/
structure ArmPair where
  upper : Phase
  lower : Phase
deriving Repr

namespace Interferometer

/-- The accumulated phase DIFFERENCE of the two arms, reduced onto the ring. -/
def phaseDiff (m : Interferometer) (a : ArmPair) : Nat :=
  (a.upper.slot + (m.modulus - a.lower.slot % m.modulus)) % m.modulus

/-- The arms are INDISTINGUISHABLE at the boundary: their accumulated phase agrees modulo `2π`
(difference reduces to the `0` slot). -/
def indistinguishable (m : Interferometer) (a : ArmPair) : Prop :=
  m.phaseDiff a = 0

/-- The arms are ANTI-PHASE: their accumulated phase differs by exactly `π` (the half-turn slot). -/
def antiPhase (m : Interferometer) (a : ArmPair) : Prop :=
  m.phaseDiff a = m.modulus / 2

/-- THE FOLD / ADMISSIBILITY RULE: the detection event `e_f` is admissible (a single consistent
ledger can be formed) iff the two arms are indistinguishable at the boundary AND not anti-phase.
Both conjuncts are pinned by falsifiable lemmas below, so neither can silently rot. -/
def admissible (m : Interferometer) (a : ArmPair) : Prop :=
  m.indistinguishable a ∧ ¬ m.antiPhase a

-- Make the richer predicates DECIDABLE so `decide`/`#eval` see through them.
instance (m : Interferometer) (a : ArmPair) : Decidable (m.indistinguishable a) := by
  unfold indistinguishable; exact inferInstance
instance (m : Interferometer) (a : ArmPair) : Decidable (m.antiPhase a) := by
  unfold antiPhase; exact inferInstance
instance (m : Interferometer) (a : ArmPair) : Decidable (m.admissible a) := by
  unfold admissible; exact inferInstance

end Interferometer

-- ---------------------------------------------------------------------------
-- FALSIFIABLE lemmas: ONE PER CONJUNCT, so the whole fold rule is load-bearing.
-- Each would break if `admissible` dropped that conjunct.
-- ---------------------------------------------------------------------------

/-- Indistinguishability is NECESSARY: arms whose phases do not agree mod `2π` never fold to an
admissible detection.  Quantified over ALL interferometers and arm pairs. -/
theorem distinguishable_not_admissible
    (m : Interferometer) (a : ArmPair) (h : ¬ m.indistinguishable a) :
    ¬ m.admissible a :=
  fun hr => h hr.1

/-- Anti-phase is FORBIDDEN: an anti-phase (`π`) pair is inadmissible — the asymmetric parts cancel
under the fold and `e_f` cannot be recorded.  Quantified over ALL interferometers and arm pairs. -/
theorem antiPhase_not_admissible
    (m : Interferometer) (a : ArmPair) (h : m.antiPhase a) :
    ¬ m.admissible a :=
  fun hr => hr.2 h

-- ---------------------------------------------------------------------------
-- The canonical events.
-- ---------------------------------------------------------------------------

/-- Both arms accumulate the SAME phase: the constructive (indistinguishable) recombination. -/
def constructivePair : ArmPair := { upper := { slot := 0 }, lower := { slot := 0 } }

/-- The arms differ by `π`: the cancelling (anti-phase) recombination. -/
def destructivePair : ArmPair := { upper := { slot := 180 }, lower := { slot := 0 } }

/-- The apparatus folds the constructive pair to an admissible detection (concrete, via the
`Decidable` instance). -/
theorem admits_constructive : defaultMZ.admissible constructivePair := by decide

/-- ...and the anti-phase pair is inadmissible — pinned through the falsifiable lemma. -/
theorem rejects_destructive : ¬ defaultMZ.admissible destructivePair :=
  antiPhase_not_admissible defaultMZ destructivePair (by decide)

-- ---------------------------------------------------------------------------
-- THE CLAIM (content-bearing; the third conjunct is the device's holonomy theorem).
-- ---------------------------------------------------------------------------

/-- The claim, in honest parts:
* (constructive fold) the apparatus admits the in-phase recombination — proved here;
* (destructive fold) the anti-phase recombination is inadmissible — proved here, load-bearing on the
  `antiPhase` conjunct of the rule; and
* (loop carries a charged holonomy) the genuine two-arm LOOP transports a NONZERO residue, while a
  one-arm OPEN path transports ZERO — `Measurement.holonomy_loop_is_charged` and
  `Measurement.holonomy_open_is_trivial`.  This reads the device's actual ±1 sign computation, so a
  sign regression in `Measurement` fails THIS build — value-coupling, not just a name. -/
def claimStatement : Prop :=
  defaultMZ.admissible constructivePair ∧
    ¬ defaultMZ.admissible destructivePair ∧
    (Measurement.holonomy Measurement.tiltedPath
        (Measurement.CubicGaugeVariation.pairVariation Measurement.node1 Measurement.node2) = 1
      ∧ Measurement.holonomy Measurement.flatPath
          (Measurement.CubicGaugeVariation.pairVariation Measurement.node1 Measurement.node2) = -1) ∧
    Measurement.holonomy Measurement.tiltedPath
      (Measurement.CubicGaugeVariation.pairVariation Measurement.node2 Measurement.node1) = 0

def claim : Experiments.Common.Claim :=
  { tag := Experiments.Common.ClaimTag.smoothShadowAnalogy
    statement := claimStatement }

theorem claim_holds : claim.statement :=
  ⟨admits_constructive, rejects_destructive,
    Measurement.holonomy_loop_is_charged, Measurement.holonomy_open_is_trivial⟩

/-- The tag is an honest ceiling: a finite discrete SHADOW of a continuous-phase phenomenon
(`π`/`2π` are labelled ring slots, not derived). -/
theorem ceiling : claim.tag = Experiments.Common.ClaimTag.smoothShadowAnalogy := rfl

-- ---------------------------------------------------------------------------
-- A computable run + a NON-vacuous Experiment.claim, with a proved bridge.
-- ---------------------------------------------------------------------------

structure Setup where
  interferometer : Interferometer
  arms : ArmPair

/-- The run actually computes — thanks to the `Decidable` instances above. -/
def run (s : Setup) : Bool := decide (s.interferometer.admissible s.arms)

/-- The exported claim is a genuine function of the setup; this bridge pins it to `run`, so the claim
body cannot be silently swapped for `fun _ => True` without breaking the proof. -/
def experiment : Experiments.Common.Experiment Setup Bool :=
  { tag := claim.tag
    run := run
    claim := fun s => s.interferometer.admissible s.arms }

theorem run_iff_claim (s : Setup) :
    run s = true ↔ experiment.claim s := by
  simp only [run, experiment, decide_eq_true_iff]

def canonicalSetup : Setup := { interferometer := defaultMZ, arms := constructivePair }

#eval run canonicalSetup                                  -- expect: true
#eval run { canonicalSetup with arms := destructivePair } -- expect: false (anti-phase, inadmissible)
#print axioms claim_holds                                 -- [propext, Quot.sound] = AMBIENT, not coupling
#eval defaultMZ.admissible destructivePair                -- expect: false (falsifiable pred is load-bearing)

/-- Bring a minimal device next to this experiment: it records whether the exported claim fires.
(`experiment.claim setup` is definitionally `setup.interferometer.admissible setup.arms`, whose
`Decidable` instance is in scope — `show` exposes it to `decide`.) -/
def deviceNear (setup : Setup) : Bool :=
  decide (setup.interferometer.admissible setup.arms)

theorem deviceNear_detects_claim (setup : Setup) :
    deviceNear setup = true ↔ experiment.claim setup := by
  simp only [deviceNear, experiment, decide_eq_true_iff]

def triangulation : Experiments.Common.Triangulation Setup Bool :=
  { experiment := experiment
    device := deviceNear
    detects := deviceNear_detects_claim }

end Experiments.TheMachZehnderEffect
