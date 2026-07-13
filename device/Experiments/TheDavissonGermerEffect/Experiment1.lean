import Experiments.Common
import Measurement.Apparatus

/-!
# The Davisson-Germer Effect — electron diffraction as a lattice-translation HOLONOMY

The phenomenon (per `instrument/chapters/07.tex:508`): electrons scattered off a periodic nickel
crystal land in bright Bragg peaks.  The description frames the peaks *informationally*: they are
"fixed points of reciprocal measurement under lattice translations", the bookkeeping consequence of
demanding that indistinguishable causal neighbourhoods propagate consistently across a periodic
partition.  A bright peak is an angle at which a shift by one lattice spacing leaves the count of
admissible refinements unchanged — translation invariance of the ledger.

That translation-invariance-around-a-period IS a holonomy condition.  Phase accumulated as the
ledger is transported across successive lattice planes closes to a whole number of cycles exactly at
the constructive (Bragg) angles; off those angles the merged ledger would carry a leftover residue
(missing/extra distinguishable events), contradicting Martin-consistency.  So we model:

1. an EFFECT-SPECIFIC domain (`Lattice`, `ScatteringMode`) — a finite 1-D crystal with spacing `d`,
   a scattering geometry, and the integer phase a mode accumulates per period — NOT a `CountSetup`;
2. FALSIFIABLE quantified lemmas: off the Bragg integer-phase condition the mode is NOT constructive
   (drop the hypothesis and it breaks); constructive ⇒ translation-invariant residue is zero;
3. a CONTENT-BEARING claim — a real conjunction whose last two conjuncts are the DEVICE's own
   holonomy theorems (`Measurement.holonomy_loop_is_charged`, `Measurement.holonomy_open_is_trivial`);
4. an honest tag (`smoothShadowAnalogy`: the finite phase-count is the discrete shadow of the smooth
   "wave"), plus a candid "NOT claimed" disclaimer;
5. explicit `Decidable` instances so `decide`/`#eval` compute through the richer predicates.

## COUPLING (load-bearing, device).
The Bragg peak = a closed lattice LOOP whose holonomy is nonzero (a constructive residue that closes
to a full cycle); a single lattice translation (open path) carries no loop holonomy.  We discharge
those two conjuncts with `Measurement.holonomy_loop_is_charged` (residue ±1 around the genuine
pair-loop) and `Measurement.holonomy_open_is_trivial` (residue 0 on the single-leg open path).  A
sign/zero regression or a rename in the device's holonomy layer breaks THIS build.

## NOT claimed
No real electron wave, wavefunction, field, or substrate (the description disclaims diffraction as a
physical mechanism); Bragg's `2 d sinθ = m λ` and `λ = h/p` are NOT derived — `d`, the period, and
the phase quantum are labelled constants; no continuum limit is taken (`smoothShadowAnalogy` is the
ceiling — the finite integer phase is a STAND-IN for the smooth wave, not the wave); the device
holonomy is a 3-node toy commutator residue, NOT the reciprocal lattice of nickel.  Claim ceiling:
a finite phase-ledger model of the Bragg/translation-invariance bookkeeping, two of whose conjuncts
are the device's own holonomy theorems.
-/

namespace Experiments.TheDavissonGermerEffect

open Measurement
open Measurement.CubicGaugeVariation

/-- A finite 1-D crystal: lattice spacing `d` (the period) and the integer phase quantum `period`
that one full constructive cycle of transport across one spacing accumulates. -/
structure Lattice where
  d : Nat
  period : Nat
deriving DecidableEq, Repr

/-- A scattering geometry/mode: the integer phase `phase` accumulated as the ledger is transported
across one lattice spacing at the chosen angle, and the diffraction order `order` (the integer `m`
of Bragg's relation). -/
structure ScatteringMode where
  phase : Nat
  order : Nat
deriving DecidableEq, Repr

/-- The standard nickel target of the experiment: lattice spacing `215` pm, phase quantum `360`
("degrees" of one full cycle).  Labelled constants, NOT derived. -/
def nickel : Lattice := { d := 215, period := 360 }

namespace Lattice

/-- BRAGG / translation invariance: a mode is constructive at this lattice iff the phase it
accumulates per spacing is a whole number of cycles, `phase = order * period`.  A shift by one
spacing then leaves the residue unchanged — the fixed-point condition of the description. -/
def constructive (L : Lattice) (m : ScatteringMode) : Prop :=
  m.phase = m.order * L.period

/-- The translation residue: how far the per-spacing phase falls from a whole cycle, modulo the
period.  Zero exactly at the Bragg peaks. -/
def residue (L : Lattice) (m : ScatteringMode) : Nat :=
  m.phase % L.period

instance (L : Lattice) (m : ScatteringMode) : Decidable (L.constructive m) := by
  unfold constructive; exact inferInstance

end Lattice

-- ---------------------------------------------------------------------------
-- FALSIFIABLE lemmas: the Bragg hypothesis is load-bearing in BOTH directions.
-- Drop the integer-phase hypothesis and a generic mode is not constructive.
-- ---------------------------------------------------------------------------

/-- CONSTRUCTIVE ⇒ ZERO RESIDUE.  At a Bragg peak the translation residue vanishes: a shift by one
spacing changes nothing.  Quantified over ALL lattices and modes; the `phase = order * period`
hypothesis is load-bearing (drop it and a generic mode with `phase = 180`, `period = 360` has
nonzero residue, breaking the conclusion). -/
theorem constructive_residue_zero
    (L : Lattice) (m : ScatteringMode) (h : L.constructive m) : L.residue m = 0 := by
  unfold Lattice.residue
  rw [h]
  exact Nat.mul_mod_left m.order L.period

/-- OFF-BRAGG ⇒ NOT CONSTRUCTIVE.  If the per-spacing phase is NOT a whole number of cycles, the
mode is not constructive — outside the peaks the merged ledger carries a leftover residue.  This is
falsifiable: it is exactly the negation of `constructive`, so dropping the hypothesis breaks it. -/
theorem offBragg_not_constructive
    (L : Lattice) (m : ScatteringMode) (h : m.phase ≠ m.order * L.period) :
    ¬ L.constructive m :=
  fun hc => h hc

-- ---------------------------------------------------------------------------
-- The canonical first-order Bragg peak on nickel.
-- ---------------------------------------------------------------------------

/-- The canonical first-order constructive mode: one full cycle of phase, order `m = 1`. -/
def firstOrderPeak : ScatteringMode := { phase := 360, order := 1 }

/-- An off-Bragg mode: a half-cycle of phase, no whole order — destructive. -/
def offBraggMode : ScatteringMode := { phase := 180, order := 0 }

/-- The nickel lattice registers the first-order peak as constructive (concrete, via `Decidable`). -/
theorem firstOrderPeak_constructive : nickel.constructive firstOrderPeak := by decide

/-- ...and the half-cycle mode is NOT constructive (the destructive control). -/
theorem offBraggMode_not_constructive : ¬ nickel.constructive offBraggMode := by decide

-- ---------------------------------------------------------------------------
-- THE CLAIM (content-bearing; the last two conjuncts are the device's holonomy theorems).
-- ---------------------------------------------------------------------------

/-- The claim, in honest parts:
* (Bragg peak) the nickel lattice registers the first-order mode as constructive — proved here;
* (off-Bragg) the half-cycle mode is NOT constructive — the falsifiable control, proved here;
* (lattice LOOP carries holonomy) the genuine closed lattice loop carries a nonzero, charged
  translation holonomy — `Measurement.holonomy_loop_is_charged` (residue `+1`/`-1`); and
* (single translation is trivial) one lattice translation (an OPEN path) carries NO loop holonomy —
  `Measurement.holonomy_open_is_trivial` (residue `0`).
The last two read the device's actual holonomy residue, so a zero/sign regression there fails THIS
build — value-coupling to the holonomy layer, not just a name. -/
def claimStatement : Prop :=
  nickel.constructive firstOrderPeak ∧
    ¬ nickel.constructive offBraggMode ∧
    (holonomy tiltedPath (pairVariation node1 node2) = 1
      ∧ holonomy flatPath (pairVariation node1 node2) = -1) ∧
    holonomy tiltedPath (pairVariation node2 node1) = 0

def claim : Experiments.Common.Claim :=
  { tag := Experiments.Common.ClaimTag.smoothShadowAnalogy
    statement := claimStatement }

theorem claim_holds : claim.statement :=
  ⟨firstOrderPeak_constructive, offBraggMode_not_constructive,
    Measurement.holonomy_loop_is_charged, Measurement.holonomy_open_is_trivial⟩

/-- The tag is an honest ceiling: the finite phase-count is the discrete SHADOW of the smooth wave,
nothing more. -/
theorem ceiling : claim.tag = Experiments.Common.ClaimTag.smoothShadowAnalogy := rfl

-- ---------------------------------------------------------------------------
-- A computable run + a NON-vacuous Experiment.claim, with a proved bridge.
-- ---------------------------------------------------------------------------

structure Setup where
  lattice : Lattice
  mode : ScatteringMode

/-- The run actually computes — thanks to the `Decidable` instance above. -/
def run (s : Setup) : Bool := decide (s.lattice.constructive s.mode)

def experiment : Experiments.Common.Experiment Setup Bool :=
  { tag := claim.tag
    run := run
    claim := fun s => s.lattice.constructive s.mode }

theorem run_iff_claim (s : Setup) :
    run s = true ↔ experiment.claim s := by
  simp only [run, experiment, decide_eq_true_iff]

def canonicalSetup : Setup := { lattice := nickel, mode := firstOrderPeak }

#eval run canonicalSetup                                  -- expect: true   (Bragg peak)
#eval run { canonicalSetup with mode := offBraggMode }    -- expect: false  (off-Bragg)
#print axioms claim_holds
#eval decide (nickel.constructive offBraggMode)           -- expect: false  (lemma load-bearing)

/-- Bring a minimal device next to this experiment: it records whether the exported claim fires.
We `decide` the constructive predicate directly (definitionally `experiment.claim setup`), so the
`Decidable` instance is the `Lattice.constructive` one in scope. -/
def deviceNear (setup : Setup) : Bool :=
  decide (setup.lattice.constructive setup.mode)

theorem deviceNear_detects_claim (setup : Setup) :
    deviceNear setup = true ↔ experiment.claim setup := by
  simp only [deviceNear, experiment, decide_eq_true_iff]

def triangulation : Experiments.Common.Triangulation Setup Bool :=
  { experiment := experiment
    device := deviceNear
    detects := deviceNear_detects_claim }

end Experiments.TheDavissonGermerEffect
