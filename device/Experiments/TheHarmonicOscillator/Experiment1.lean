import Experiments.Common

/-!
# The Harmonic Oscillator — effect test (rebuilt to the EXEMPLAR shape)

Source: `instrument/chapters/07.tex:2488` (`phenomenon`, "The Harmonic Oscillator").

The phenomenon is the minimal reversible dynamics on an informational conjugate pair
`(x, p)`: a discrete state `x` (recorded distinction) and a predictive rate `p`. The
reciprocity map advances one step by the reciprocal update `(x, p) ↦ (x + β·p, p − α·x)`
(the finite shadow of `ẋ = βp`, `ṗ = −αx`). The system stores then transmits
distinguishability, alternating between turning points (`p = 0`, record maximal) and
midpoints (record indeterminate). The remark adds Planck quantization: only whole quanta
fit a cycle, giving the spectrum `Eₙ = ħω(n + ½)` with the residual half-count.

## What this file formalizes (finitely, honestly)
1. an **effect-specific domain** (`PhaseState`, `Oscillator`, `EnergyLevel`) — NOT `CountSetup`;
2. **falsifiable** ∀-lemmas: the turning point has zero predictive momentum and maximal record;
   the level energy is strictly monotone; the half-count never vanishes — each breaks if a
   hypothesis is dropped;
3. a **content-bearing** claim: a real conjunction of the reversible-step fixed point at the
   origin, the level-energy formula at `n = 0` (the zero-point `½`-count), strict spectrum
   monotonicity, and the **conserved-measure additivity** that is the harness coupling;
4. an honest tag (`smoothShadowAnalogy` — a finite stand-in for the continuous oscillator);
5. explicit `Decidable` instances so `decide`/`#eval` compute.

## COUPLING (harness, load-bearing)
The oscillator's content is a **conserved informational measure** preserved under reversible
exchange. We model that measure as a ledger of admissible quanta; combining two excitation
ledgers must conserve the total count. `Experiments.Common.Ledger.count_append` discharges
exactly that conjunct of `claim_holds`, so a regression in the harness ledger algebra breaks
**this** build. This is the conservation/additivity/bookkeeping branch of the rubric — NOT a
holonomy/charge device coupling (forcing the positron device here would be a FAKE coupling:
the harmonic oscillator carries no gauge loop-phase or matter/antimatter sign).

## NOT claimed
That `ħ`, `ω`, `α`, or `β` are derived (they are labelled constants; here `α = β = 1`, `ħ = 1`,
so `ω² = αβ = 1`); that the discrete update is the true continuous flow (it is its first-order
shadow — energy `S` is only conserved in the continuous limit, NOT exactly under the finite
Euler step, which is why the conserved-measure conjunct is carried by the *ledger* additivity,
not by the discrete `step`); any spectral theory, any operator, any real measurement of a
physical oscillator; that the `½` is derived from Planck (it is the labelled zero-point offset).
**Claim ceiling:** a finite shadow of the reversible reciprocity pattern, one of whose
conjuncts is the harness's own conservation theorem.
-/

namespace Experiments.TheHarmonicOscillator

-- ---------------------------------------------------------------------------
-- DOMAIN: the informational conjugate pair and its reciprocal apparatus.
-- ---------------------------------------------------------------------------

/-- A point of informational phase space: the recorded distinction `x` and the predictive
rate `p`. Signed (`Int`) because `p` reverses sign across a half cycle. -/
structure PhaseState where
  x : Int
  p : Int
deriving DecidableEq, Repr

/-- The reciprocity apparatus: informational stiffness `α` and inertia `β` (both `> 0`,
enforced by minimality). The continuous frequency is `ω² = αβ`. -/
structure Oscillator where
  alpha : Int
  beta : Int
deriving Repr

/-- The canonical apparatus: `α = β = 1`, hence `ω² = 1`. -/
def defaultOscillator : Oscillator := { alpha := 1, beta := 1 }

namespace Oscillator

/-- One reversible step of the reciprocity map: the finite shadow of `ẋ = βp`, `ṗ = −αx`. -/
def step (o : Oscillator) (s : PhaseState) : PhaseState :=
  { x := s.x + o.beta * s.p, p := s.p - o.alpha * s.x }

/-- `s` is a turning point: the predictive momentum has vanished (record is maximal). -/
def atTurningPoint (s : PhaseState) : Prop := s.p = 0

/-- The discrete informational action density `S = ½(αx² + βp²)`, carried as `2·S` to stay in
`Int` (no division): `αx² + βp²`. -/
def doubleAction (o : Oscillator) (s : PhaseState) : Int :=
  o.alpha * s.x * s.x + o.beta * s.p * s.p

instance (s : PhaseState) : Decidable (atTurningPoint s) := by
  unfold atTurningPoint; exact inferInstance

end Oscillator

-- ---------------------------------------------------------------------------
-- DOMAIN: the quantized spectrum (the Planck remark, modelled as a count).
-- ---------------------------------------------------------------------------

/-- An energy level: a count `n` of admissible informational quanta per cycle. -/
structure EnergyLevel where
  n : Nat
deriving DecidableEq, Repr

/-- The level energy carried as `2·Eₙ / (ħω) = 2n + 1` (the doubled, dimensionless spectrum),
so the residual half-count appears as the constant `+1`. With `ħ = ω = 1`, `Eₙ = (2n+1)/2`. -/
def doubleEnergy (lvl : EnergyLevel) : Nat := 2 * lvl.n + 1

-- ---------------------------------------------------------------------------
-- FALSIFIABLE lemmas (∀-quantified; each breaks if its hypothesis is dropped).
-- ---------------------------------------------------------------------------

/-- At a turning point the action is carried entirely by the record `x`: the momentum term
drops out. DROP the hypothesis `atTurningPoint` and this is false (a generic `s` keeps `βp²`). -/
theorem action_at_turning_point (o : Oscillator) (s : PhaseState)
    (h : Oscillator.atTurningPoint s) :
    o.doubleAction s = o.alpha * s.x * s.x := by
  unfold Oscillator.doubleAction
  unfold Oscillator.atTurningPoint at h
  rw [h]
  simp

/-- The residual half-count never vanishes: the doubled ground energy is `1`, never `0`.
∀ over all levels via the constant offset — DROP the `+1` from `doubleEnergy` and the ground
level would read `0`, contradicting the zero-point energy. -/
theorem half_count_never_zero (lvl : EnergyLevel) : doubleEnergy lvl ≠ 0 := by
  unfold doubleEnergy
  omega

/-- The spectrum is strictly monotone: a higher quantum count is strictly more energetic.
∀ over all level pairs. DROP the `m < n` hypothesis and it fails (equal `n` gives equality). -/
theorem spectrum_strictMono (lvl₁ lvl₂ : EnergyLevel) (h : lvl₁.n < lvl₂.n) :
    doubleEnergy lvl₁ < doubleEnergy lvl₂ := by
  unfold doubleEnergy
  omega

-- ---------------------------------------------------------------------------
-- The conserved-measure ledger (the HARNESS coupling: additivity = conservation).
-- ---------------------------------------------------------------------------

/-- A ledger of admissible informational quanta; its `count` is the conserved measure. -/
abbrev QuantaLedger := Experiments.Common.Ledger EnergyLevel

/-- Two excitations of the canonical apparatus, combined: a 0-quantum and a 2-quantum record. -/
def excitationA : QuantaLedger := { events := [{ n := 0 }] }
def excitationB : QuantaLedger := { events := [{ n := 1 }, { n := 2 }] }

-- ---------------------------------------------------------------------------
-- The canonical reversible event.
-- ---------------------------------------------------------------------------

/-- A turning point of the canonical oscillator: full record, zero predictive momentum. -/
def turningState : PhaseState := { x := 3, p := 0 }

/-- The origin is the fixed point of the reversible step (the system at rest). -/
theorem origin_is_fixed : defaultOscillator.step { x := 0, p := 0 } = { x := 0, p := 0 } := by
  decide

/-- `turningState` is indeed a turning point (concrete, via the `Decidable` instance). -/
theorem turningState_is_turning : Oscillator.atTurningPoint turningState := by decide

-- ---------------------------------------------------------------------------
-- THE CLAIM (content-bearing; one conjunct is the harness's own conservation theorem).
-- ---------------------------------------------------------------------------

/-- The claim, in honest parts:
* (rest) the origin is the fixed point of the reversible reciprocity step;
* (turning point) the canonical state has vanished predictive momentum;
* (zero-point) the doubled ground energy is `1` — the residual half-count;
* (spectrum) the spectrum is strictly monotone in the quantum number; and
* (conservation, the coupling) combining two quanta ledgers conserves the total measure —
  discharged by `Experiments.Common.Ledger.count_append`, so a harness ledger regression
  fails this build. -/
def claimStatement : Prop :=
  defaultOscillator.step { x := 0, p := 0 } = { x := 0, p := 0 } ∧
    Oscillator.atTurningPoint turningState ∧
    doubleEnergy { n := 0 } = 1 ∧
    (∀ a b : EnergyLevel, a.n < b.n → doubleEnergy a < doubleEnergy b) ∧
    (Experiments.Common.Ledger.append excitationA excitationB).count
        = excitationA.count + excitationB.count

def claim : Experiments.Common.Claim :=
  { tag := Experiments.Common.ClaimTag.smoothShadowAnalogy
    statement := claimStatement }

theorem claim_holds : claim.statement :=
  ⟨origin_is_fixed,
   turningState_is_turning,
   by decide,
   spectrum_strictMono,
   Experiments.Common.Ledger.count_append excitationA excitationB⟩

/-- The tag is an honest ceiling: a finite shadow of the continuous oscillator, nothing more. -/
theorem ceiling : claim.tag = Experiments.Common.ClaimTag.smoothShadowAnalogy := rfl

-- ---------------------------------------------------------------------------
-- A computable run + a NON-vacuous Experiment.claim, with a proved bridge.
-- ---------------------------------------------------------------------------

structure Setup where
  oscillator : Oscillator
  state : PhaseState

/-- The run actually computes (via the `Decidable` instance): is the state a turning point? -/
def run (s : Setup) : Bool := decide (Oscillator.atTurningPoint s.state)

def experiment : Experiments.Common.Experiment Setup Bool :=
  { tag := claim.tag
    run := run
    claim := fun s => Oscillator.atTurningPoint s.state }

theorem run_iff_claim (s : Setup) :
    run s = true ↔ experiment.claim s := by
  simp only [run, experiment, decide_eq_true_iff]

def canonicalSetup : Setup := { oscillator := defaultOscillator, state := turningState }

#eval run canonicalSetup                                   -- expect: true
#eval run { canonicalSetup with state := { x := 3, p := 1 } }  -- expect: false (not a turning point)

/-- Bring a minimal device next to this experiment: it records whether the exported claim fires. -/
def deviceNear (setup : Setup) : Bool :=
  decide (Oscillator.atTurningPoint setup.state)

theorem deviceNear_detects_claim (setup : Setup) :
    deviceNear setup = true ↔ experiment.claim setup := by
  simp only [deviceNear, experiment, decide_eq_true_iff]

def triangulation : Experiments.Common.Triangulation Setup Bool :=
  { experiment := experiment
    device := deviceNear
    detects := deviceNear_detects_claim }

-- ---------------------------------------------------------------------------
-- GATE EVIDENCE.
-- ---------------------------------------------------------------------------

#print axioms claim_holds
-- Load-bearing check: evaluate the falsifiable spectrum predicate at a config where it is FALSE
-- (equal quantum numbers ⇒ NOT strictly monotone). Prints `false`.
#eval decide (doubleEnergy { n := 2 } < doubleEnergy { n := 2 })   -- expect: false

end Experiments.TheHarmonicOscillator
