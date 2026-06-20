import Experiments.Common

/-!
# The Harmonic Oscillator Revisited — effect test (exemplar shape)

Modelled finitely from `instrument/chapters/10.tex:314`.

## Physics (modelled finitely)
A single mode `U(t)` of the universe tensor obeys the discrete reciprocal update
`δ²U + ω²U = 0`.  We record the state as a `(q, p)` pair of **integers** — `q` the
distinguishability amplitude, `p = δU` the variation — and a curvature parameter `omegaSq`
(the integer stand-in for `ω²`).  The energy functional
`E = ½[(δU)² + ω²U²]` is, up to the harmless factor `2`, the integer scalar
`twiceEnergy (q,p) = p² + omegaSq · q²`.

The reciprocal half-cycle exchanges distinguishability and variation.  We realise the
exchange at the **turning point ↔ crossing** extremes, where the discrete rotation is the
exact swap `(q, p) ↦ (p, -q)` **when `omegaSq = 1`** (the isotropic mode).  The content claim
is that this update is **energy-preserving** (the invariant scalar of the causal pair) and that
it genuinely cycles (variation vanishes at the turning point, is maximal at the crossing).

## Coupling (HARNESS — conservation / bookkeeping)
The conserved energy is read as a **ledger of informational quanta** (Axiom of Finite
Observation: only discrete counts fit one period).  Splitting one period into two half-cycle
ledgers and concatenating them is additive — this is the device's own
`Experiments.Common.Ledger.count_append`, made a LOAD-BEARING conjunct of `claim_holds`:
delete that lemma (or break `Ledger.count`) and THIS build fails.

## NOT claimed
That `ω²` is a real number or that the continuum limit `d²U/dt² + ω²U = 0` is taken (we stay
on the integer `δ`-lattice); that `ħ` exists or that the spectrum `Eₙ = ħω(n+½)` is *derived*
(the half-count is a label, not computed here); any operator algebra, ladder operators, or
zero-point *energy* beyond the integer bookkeeping; energy preservation for `omegaSq ≠ 1`
(the swap is only an isometry of `p²+q²`, the isotropic case).  **Claim ceiling:** a finite
ledger model whose conserved invariant and whose period-additivity are the device's arithmetic.
-/

namespace Experiments.TheHarmonicOscillatorRevisited

/-- A discrete oscillator state: `q` the distinguishability amplitude, `p = δU` the variation. -/
structure OscState where
  q : Int
  p : Int
deriving DecidableEq, Repr

/-- The apparatus: the integer curvature `omegaSq` (stand-in for `ω²`) and a count of
quanta per period (the Axiom of Finite Observation floor). -/
structure Oscillator where
  omegaSq : Int
  quantaPerPeriod : Nat
deriving Repr

/-- The isotropic standard mode: `ω² = 1`, with eight resolved quanta per causal period. -/
def standardOscillator : Oscillator := { omegaSq := 1, quantaPerPeriod := 8 }

namespace Oscillator

/-- Twice the energy functional `E = ½[(δU)² + ω²U²]`, kept integer-valued:
`2E = p² + ω²·q²`. -/
def twiceEnergy (osc : Oscillator) (s : OscState) : Int :=
  s.p * s.p + osc.omegaSq * (s.q * s.q)

/-- The discrete reciprocal half-cycle update `(q, p) ↦ (p, -q)`: distinguishability and
variation swap roles. (Exactly the `δ²U + ω²U = 0` rotation by a quarter turn at `ω² = 1`.) -/
def step (_osc : Oscillator) (s : OscState) : OscState :=
  { q := s.p, p := -s.q }

/-- A state is at a **turning point** when the variation vanishes (`p = 0`): maximal distinction. -/
def turningPoint (_osc : Oscillator) (s : OscState) : Prop := s.p = 0

/-- A state is at a **crossing** when distinction vanishes (`q = 0`): maximal variation. -/
def crossing (_osc : Oscillator) (s : OscState) : Prop := s.q = 0

instance (osc : Oscillator) (s : OscState) : Decidable (osc.turningPoint s) := by
  unfold turningPoint; exact inferInstance
instance (osc : Oscillator) (s : OscState) : Decidable (osc.crossing s) := by
  unfold crossing; exact inferInstance

end Oscillator

-- ---------------------------------------------------------------------------
-- FALSIFIABLE lemmas.  Each is ∀-quantified and would break if a hypothesis
-- were dropped or the update were wrong.
-- ---------------------------------------------------------------------------

/-- THE INVARIANT.  The reciprocal update **preserves energy** at the isotropic mode.
Falsifiable: drop the `omegaSq = 1` hypothesis and it fails (see the `#eval` at EOF, which
evaluates it false for `omegaSq = 2`). -/
theorem energy_preserved_isotropic
    (osc : Oscillator) (s : OscState) (h : osc.omegaSq = 1) :
    osc.twiceEnergy (osc.step s) = osc.twiceEnergy s := by
  unfold Oscillator.twiceEnergy Oscillator.step
  rw [h]
  -- goal: (-s.q)*(-s.q) + 1*(s.p*s.p) = s.p*s.p + 1*(s.q*s.q)
  simp only [Int.neg_mul, Int.mul_neg, Int.neg_neg, Int.one_mul, Int.add_comm]

/-- The reciprocal nature: one full period is four half-cycle steps back to the start. -/
theorem four_steps_close (osc : Oscillator) (s : OscState) :
    osc.step (osc.step (osc.step (osc.step s))) = s := by
  unfold Oscillator.step
  simp

/-- Causal exchange (turning → crossing): a turning point steps to a crossing.
Falsifiable: needs the `turningPoint` (i.e. `p = 0`) hypothesis. -/
theorem turning_steps_to_crossing
    (osc : Oscillator) (s : OscState) (h : osc.turningPoint s) :
    osc.crossing (osc.step s) := by
  unfold Oscillator.crossing Oscillator.step
  exact h

-- ---------------------------------------------------------------------------
-- The canonical event: a unit-amplitude turning point on the standard mode.
-- ---------------------------------------------------------------------------

/-- The canonical turning point: `q = 1, p = 0` (maximal distinction, zero variation). -/
def canonicalTurning : OscState := { q := 1, p := 0 }

/-- The canonical energy is `2E = 1`. -/
theorem canonical_energy : standardOscillator.twiceEnergy canonicalTurning = 1 := by decide

/-- It really is a turning point, and steps to a crossing. -/
theorem canonical_is_turning : standardOscillator.turningPoint canonicalTurning := by decide

-- ---------------------------------------------------------------------------
-- HARNESS coupling: energy quanta as a ledger; one period = two half-cycle ledgers,
-- and their total count is ADDITIVE (device's `Ledger.count_append`).
-- ---------------------------------------------------------------------------

/-- The two half-cycle quanta ledgers of one period: each carries `quantaPerPeriod / 2`
indistinguishable quanta (the finite informational count of a half-cycle). -/
def firstHalf (osc : Oscillator) : Experiments.Common.Ledger Unit :=
  { events := List.replicate (osc.quantaPerPeriod / 2) () }

def secondHalf (osc : Oscillator) : Experiments.Common.Ledger Unit :=
  { events := List.replicate (osc.quantaPerPeriod / 2) () }

/-- The full period's ledger is the concatenation of its two half-cycles. -/
def periodLedger (osc : Oscillator) : Experiments.Common.Ledger Unit :=
  Experiments.Common.Ledger.append (firstHalf osc) (secondHalf osc)

/-- The standard mode's period carries the full `quantaPerPeriod` count of quanta — proved by
the device's additivity lemma, NOT by recomputation. LOAD-BEARING. -/
theorem period_count_is_additive :
    (periodLedger standardOscillator).count
      = (firstHalf standardOscillator).count + (secondHalf standardOscillator).count :=
  Experiments.Common.Ledger.count_append (firstHalf standardOscillator) (secondHalf standardOscillator)

-- ---------------------------------------------------------------------------
-- THE CLAIM (content-bearing conjunction; the LAST conjunct is the device's lemma).
-- ---------------------------------------------------------------------------

/-- The claim, in honest parts:
* (invariant) the reciprocal update preserves energy on the standard isotropic mode;
* (cycle) the canonical turning point steps to a crossing, and a period is four steps;
* (canonical reading) the canonical energy is `2E = 1`;
* (bookkeeping = device) one period's quanta count is the additive sum of its two
  half-cycles (`Experiments.Common.Ledger.count_append`). -/
def claimStatement : Prop :=
  standardOscillator.twiceEnergy (standardOscillator.step canonicalTurning)
      = standardOscillator.twiceEnergy canonicalTurning ∧
    standardOscillator.crossing (standardOscillator.step canonicalTurning) ∧
    standardOscillator.step
        (standardOscillator.step
          (standardOscillator.step (standardOscillator.step canonicalTurning)))
      = canonicalTurning ∧
    standardOscillator.twiceEnergy canonicalTurning = 1 ∧
    (periodLedger standardOscillator).count
      = (firstHalf standardOscillator).count + (secondHalf standardOscillator).count

def claim : Experiments.Common.Claim :=
  { tag := Experiments.Common.ClaimTag.finiteLedgerModel
    statement := claimStatement }

theorem claim_holds : claim.statement :=
  ⟨ energy_preserved_isotropic standardOscillator canonicalTurning rfl,
    turning_steps_to_crossing standardOscillator canonicalTurning canonical_is_turning,
    four_steps_close standardOscillator canonicalTurning,
    canonical_energy,
    period_count_is_additive ⟩

/-- The tag is an honest ceiling: a finite ledger model, nothing more. -/
theorem ceiling : claim.tag = Experiments.Common.ClaimTag.finiteLedgerModel := rfl

-- ---------------------------------------------------------------------------
-- A computable run + a NON-vacuous Experiment.claim, with a proved bridge.
-- ---------------------------------------------------------------------------

structure Setup where
  oscillator : Oscillator
  state : OscState

/-- The setup-local proposition: the half-cycle update preserves `twiceEnergy` at this state. -/
def preservesEnergy (s : Setup) : Prop :=
  s.oscillator.twiceEnergy (s.oscillator.step s.state) = s.oscillator.twiceEnergy s.state

instance (s : Setup) : Decidable (preservesEnergy s) := by
  unfold preservesEnergy; exact inferInstance

/-- The run computes: does the half-cycle update preserve `twiceEnergy` at this state? -/
def run (s : Setup) : Bool :=
  decide (preservesEnergy s)

/-- The exported claim is a genuine function of the setup, pinned to `run`. -/
def experiment : Experiments.Common.Experiment Setup Bool :=
  { tag := claim.tag
    run := run
    claim := fun s => preservesEnergy s }

theorem run_iff_claim (s : Setup) :
    run s = true ↔ experiment.claim s := by
  simp only [run, experiment, decide_eq_true_iff]

def canonicalSetup : Setup := { oscillator := standardOscillator, state := canonicalTurning }

#eval run canonicalSetup                                                  -- expect: true
#eval run { canonicalSetup with oscillator := { omegaSq := 2, quantaPerPeriod := 8 } }
                                                                          -- expect: false
#print axioms claim_holds

/-- Bring a minimal device next to this experiment: it records whether the exported claim fires. -/
def deviceNear (setup : Setup) : Bool :=
  decide (preservesEnergy setup)

theorem deviceNear_detects_claim (setup : Setup) :
    deviceNear setup = true ↔ experiment.claim setup := by
  simp only [deviceNear, experiment, decide_eq_true_iff]

def triangulation : Experiments.Common.Triangulation Setup Bool :=
  { experiment := experiment
    device := deviceNear
    detects := deviceNear_detects_claim }

-- Load-bearing falsification witness: the invariant is FALSE off the isotropic mode.
#eval decide
  (({ omegaSq := 2, quantaPerPeriod := 8 } : Oscillator).twiceEnergy
      (({ omegaSq := 2, quantaPerPeriod := 8 } : Oscillator).step canonicalTurning)
    = ({ omegaSq := 2, quantaPerPeriod := 8 } : Oscillator).twiceEnergy canonicalTurning)
                                                                          -- expect: false

end Experiments.TheHarmonicOscillatorRevisited
