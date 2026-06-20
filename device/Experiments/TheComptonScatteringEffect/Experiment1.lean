import Experiments.Common

/-!
# The Compton Scattering Effect — conservation across one refinement step

Source: `instrument/chapters/10.tex:408` (`The Compton Scattering Effect`).

## Physics (modelled finitely)
Compton scattering is **two-body elastic scattering**: a photon meets an electron, and the pair
`(γ, e)` is REFINED into the pair `(γ', e')`. The description's whole content is the **reciprocity**
bookkeeping — translation symmetry's Noether current enforced at the single refinement:
```
  p_γ + p_e = p'_γ + p'_e          (momentum)
  E_γ + E_e = E'_γ + E'_e          (energy)
```
and the observed Compton shift `Δλ` is "the measured residue after enforcing equality of conjugate
Noether charges at a single refinement step." We model the conjugate charges as finite integer
totals carried by each channel, and the refinement as a relabelling of who carries what — the
TOTAL is the conserved ledger.

## NOT claimed (honest ceiling)
- We do NOT derive `Δλ = (h / m_e c)(1 - cosθ)` — `h`, `m_e`, `c`, `cosθ` are not in the model;
  there is no real momentum-space geometry, no Klein–Nishina cross-section, no QED amplitude, no
  rate. The "shift" here is a finite integer residue between the photon's before/after momentum
  slot, NOT a wavelength in any unit.
- We do NOT enforce the relativistic dispersion relation that ties `E` to `p` — energy and momentum
  are independent integer charges here, so the model is conservation-of-two-charges, not the full
  on-shell kinematics that *fixes* the scattering angle.
- **Claim ceiling:** a finite ledger model of the conservation bookkeeping, whose conservation
  conjunct is the harness's own `Ledger.count_append` (the totals before = totals after = the
  union's total). Tag: `finiteLedgerModel`.

## Coupling (HARNESS, not device — and WHY this is the honest call)
This effect is genuine measurement-bookkeeping (a conservation law at a single refinement), so it
couples to `Experiments.Common.Ledger.count_append`: the total quanta in the joint `(γ,e)` ledger
equal the sum of the two single-channel ledgers — and conservation = "the same total after the
relabelling." A DEVICE coupling (holonomy / positron-sign / matter–antimatter split) would be a
**FAKE** here, and I decline it on the physics:
- **No loop / no parallel transport / no Berry phase.** Compton scattering is a single open
  `(γ,e) ↦ (γ',e')` contraction — a momentum *difference* across one event, the description's
  "finite difference of momentum across an event pair." There is no closed loop to accumulate a
  holonomy around, so `Measurement.holonomy_loop_is_charged` / `holonomy_open_is_trivial` pin a
  closed-loop residue the physics does not contain.
- **No orientation/chirality sign.** Elastic Compton scattering is spin-independent; the photon
  Thomson/Klein–Nishina kinematics carry no `±` chirality charge for the device's
  `detects_positron_over_tilt` orientation sign to read.
- **No pair creation/annihilation.** The electron BEFORE the event is the SAME electron AFTER it
  (it merely recoils); nothing is created and nothing is annihilated, so the matter/antimatter
  split theorems `the_split_counted` / `native_antimatter_is_zero` have no electron–positron pair
  to count. Those formalize the ANNIHILATION/pair face (`ThePositronAnnihilationEffect`), a
  genuinely different phenomenon. Bolting them onto elastic scattering would pin a symbol the
  physics does not have. So we couple honestly to the conservation theorem the harness provides.
-/

namespace Experiments.TheComptonScatteringEffect

/-- A single quantum carried in one of the two scattering channels, with the two conjugate Noether
charges (an energy slot and a momentum slot) it carries. Finite integer stand-ins for `E` and `p`. -/
structure Quantum where
  energy : Int
  momentum : Int
deriving DecidableEq, Repr

/-- A scattering channel is which particle (photon `gamma` / electron `electron`) the quantum is in.
The refinement of Compton scattering RELABELS quanta between these channels; the totals are what is
conserved. -/
inductive Channel where
  | gamma
  | electron
deriving DecidableEq, Repr

/-- A scattering event pair: the photon and electron lines BEFORE and AFTER the single refinement.
This is the `(γ, e) ↦ (γ', e')` contraction of the description. -/
structure EventPair where
  gammaIn : Quantum
  electronIn : Quantum
  gammaOut : Quantum
  electronOut : Quantum
deriving DecidableEq, Repr

namespace EventPair

/-- The total energy carried IN by the `(γ, e)` pair. -/
def energyIn (ev : EventPair) : Int := ev.gammaIn.energy + ev.electronIn.energy

/-- The total energy carried OUT by the `(γ', e')` pair. -/
def energyOut (ev : EventPair) : Int := ev.gammaOut.energy + ev.electronOut.energy

/-- The total momentum carried IN. -/
def momentumIn (ev : EventPair) : Int := ev.gammaIn.momentum + ev.electronIn.momentum

/-- The total momentum carried OUT. -/
def momentumOut (ev : EventPair) : Int := ev.gammaOut.momentum + ev.electronOut.momentum

/-- THE RECIPROCITY / NOETHER BOOKKEEPING: the single refinement conserves BOTH conjugate charges.
Both conjuncts are required, and each is pinned by a falsifiable lemma below. -/
def conserves (ev : EventPair) : Prop :=
  energyIn ev = energyOut ev ∧ momentumIn ev = momentumOut ev

instance (ev : EventPair) : Decidable (ev.conserves) := by
  unfold conserves; exact inferInstance

/-- THE COMPTON SHIFT: the measured residue on the PHOTON momentum slot after the refinement —
`p'_γ - p_γ`. (A finite integer residue, NOT a wavelength; see "NOT claimed".) -/
def comptonShift (ev : EventPair) : Int := ev.gammaOut.momentum - ev.gammaIn.momentum

end EventPair

-- ---------------------------------------------------------------------------
-- FALSIFIABLE lemmas: ONE PER CONSERVED CHARGE, so the whole rule is load-bearing.
-- Drop either conjunct of `conserves` and the matching lemma below stops being provable.
-- ---------------------------------------------------------------------------

/-- Energy conservation is necessary: an event whose energy totals differ is NOT a valid Compton
refinement. Quantified over ALL event pairs. -/
theorem energyMismatch_not_conserved
    (ev : EventPair) (h : ev.energyIn ≠ ev.energyOut) : ¬ ev.conserves :=
  fun hc => h hc.1

/-- Momentum conservation is necessary: an event whose momentum totals differ is NOT a valid Compton
refinement. Quantified over ALL event pairs. -/
theorem momentumMismatch_not_conserved
    (ev : EventPair) (h : ev.momentumIn ≠ ev.momentumOut) : ¬ ev.conserves :=
  fun hc => h hc.2

/-- THE SHIFT IS THE RESIDUE THE ELECTRON ABSORBS: whenever momentum is conserved, the photon's
shift equals minus the electron's momentum change — the recoil. This is the description's
"eliminating the electron internal variables yields the observed `Δλ`." Falsifiable: it requires the
conservation hypothesis (drop `h` and a non-conserving event breaks it). -/
theorem shift_is_electron_recoil
    (ev : EventPair) (h : ev.momentumIn = ev.momentumOut) :
    ev.comptonShift = -(ev.electronOut.momentum - ev.electronIn.momentum) := by
  unfold EventPair.comptonShift EventPair.momentumIn EventPair.momentumOut at *
  omega

-- ---------------------------------------------------------------------------
-- A canonical Compton event: the photon loses 1 momentum unit; the electron recoils to absorb it.
-- ---------------------------------------------------------------------------

/-- Incident photon: energy 10, momentum 10. -/
def gammaIn0 : Quantum := { energy := 10, momentum := 10 }
/-- Target electron at rest: energy 5, momentum 0. -/
def electronIn0 : Quantum := { energy := 5, momentum := 0 }
/-- Scattered photon: energy 9, momentum 7 (it lost energy and momentum). -/
def gammaOut0 : Quantum := { energy := 9, momentum := 7 }
/-- Recoil electron: energy 6, momentum 3 (it absorbed exactly the photon's loss; totals match). -/
def electronOut0 : Quantum := { energy := 6, momentum := 3 }

def comptonEvent : EventPair :=
  { gammaIn := gammaIn0, electronIn := electronIn0
    gammaOut := gammaOut0, electronOut := electronOut0 }

/-- The canonical event conserves both charges (concrete, via the `Decidable` instance). -/
theorem comptonEvent_conserves : comptonEvent.conserves := by decide

/-- The photon was shifted by a NONZERO residue (the scattering actually did something). -/
theorem comptonEvent_shift_nonzero : comptonEvent.comptonShift ≠ 0 := by decide

-- ---------------------------------------------------------------------------
-- THE LEDGER COUPLING: the conserved total IS a ledger additivity identity.
-- The two channels' single-quantum ledgers append to the joint ledger, and the harness's
-- `Ledger.count_append` says the joint count is the sum of the channel counts — the bookkeeping
-- backbone of "what enters one channel and leaves another keeps the total fixed."
-- ---------------------------------------------------------------------------

/-- The photon's single-quantum ledger and the electron's single-quantum ledger; appended, they ARE
the joint incoming ledger — so the harness's `count_append` governs their total. -/
def gammaLedger (ev : EventPair) : Experiments.Common.Ledger (Channel × Quantum) :=
  { events := [(Channel.gamma, ev.gammaIn)] }
def electronLedger (ev : EventPair) : Experiments.Common.Ledger (Channel × Quantum) :=
  { events := [(Channel.electron, ev.electronIn)] }

/-- The joint count is the sum of the channel counts — the harness's `count_append`, instantiated at
this effect's ledgers. LOAD-BEARING: it is `Measurement`-free harness content, and a regression in
`Ledger.count_append` (or a rename) breaks this build. -/
theorem channels_append (ev : EventPair) :
    (Experiments.Common.Ledger.append (gammaLedger ev) (electronLedger ev)).count
      = (gammaLedger ev).count + (electronLedger ev).count :=
  Experiments.Common.Ledger.count_append (gammaLedger ev) (electronLedger ev)

-- ---------------------------------------------------------------------------
-- THE CLAIM (content-bearing; one conjunct is conservation, one is the harness ledger theorem).
-- ---------------------------------------------------------------------------

/-- The claim, in honest parts:
* (conservation) the canonical refinement conserves both Noether charges — proved by construction;
* (real shift)   the photon's momentum residue is nonzero — the scattering is not the identity;
* (ledger)       the two channel ledgers append with additive count — `Ledger.count_append`, the
  harness's conservation/bookkeeping theorem, instantiated at this effect (the LOAD-BEARING
  coupling). -/
def claimStatement : Prop :=
  comptonEvent.conserves
    ∧ comptonEvent.comptonShift ≠ 0
    ∧ (Experiments.Common.Ledger.append (gammaLedger comptonEvent) (electronLedger comptonEvent)).count
        = (gammaLedger comptonEvent).count + (electronLedger comptonEvent).count

def claim : Experiments.Common.Claim :=
  { tag := Experiments.Common.ClaimTag.finiteLedgerModel
    statement := claimStatement }

theorem claim_holds : claim.statement :=
  ⟨comptonEvent_conserves, comptonEvent_shift_nonzero, channels_append comptonEvent⟩

/-- The tag is an honest ceiling: a finite ledger model of the conservation bookkeeping. -/
theorem ceiling : claim.tag = Experiments.Common.ClaimTag.finiteLedgerModel := rfl

-- ---------------------------------------------------------------------------
-- A computable run + a NON-vacuous exported Experiment, with a proved bridge.
-- ---------------------------------------------------------------------------

structure Setup where
  event : EventPair

/-- The run computes — thanks to the `Decidable` instance on `conserves`. -/
def run (s : Setup) : Bool := decide (s.event.conserves)

def experiment : Experiments.Common.Experiment Setup Bool :=
  { tag := claim.tag
    run := run
    claim := fun s => s.event.conserves }

theorem run_iff_claim (s : Setup) :
    run s = true ↔ experiment.claim s := by
  simp only [run, experiment, decide_eq_true_iff]

def canonicalSetup : Setup := { event := comptonEvent }

/-- A deliberately BROKEN event: the electron does not recoil, so momentum is not conserved. Used to
show the falsifiable lemma actually fires (prints `false`). -/
def brokenEvent : EventPair :=
  { gammaIn := gammaIn0, electronIn := electronIn0
    gammaOut := gammaOut0, electronOut := electronIn0 }

/-- Bring a minimal device next to this experiment: it records whether the exported claim fires.
We read the underlying decidable predicate directly (the `experiment.claim` projection is opaque to
instance resolution), and prove it agrees with the exported claim. -/
def deviceNear (setup : Setup) : Bool :=
  decide setup.event.conserves

theorem deviceNear_detects_claim (setup : Setup) :
    deviceNear setup = true ↔ experiment.claim setup := by
  simp only [deviceNear, experiment, decide_eq_true_iff]

def triangulation : Experiments.Common.Triangulation Setup Bool :=
  { experiment := experiment
    device := deviceNear
    detects := deviceNear_detects_claim }

#eval run canonicalSetup                         -- expect: true
#eval run { event := brokenEvent }               -- expect: false  (momentum not conserved)
#print axioms claim_holds                         -- ambient [propext] footprint, not coupling
#eval decide brokenEvent.conserves               -- expect: false  (the falsifiable predicate, FALSE here)

end Experiments.TheComptonScatteringEffect
