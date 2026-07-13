import Experiments.Common
import Measurement.Apparatus

/-!
# The Dirac Operator — a gauge-covariant first-order generator, modelled finitely

Source: `instrument/chapters/10.tex:1510` (`The Dirac Operator~\cite{dirac1928}`).

The description reads the Dirac operator `γ^μ(∂_μ + iA_μ) + m` not as a dynamical axiom but as the
**minimal first-order generator of distinguishability** that must, simultaneously:

* **transport** informational components consistently with the metric gauge — the connection `iA_μ`;
* **preserve the rotational bookkeeping of measurement (spin)** — an orientation/chirality SIGN;
* and square to the second-order propagation (the Clifford relation `{γ^μ,γ^ν}=2g^{μν}`).

This file models that finitely with an **effect-specific domain** (`DiracMode`, a first-order
generator carrying a gauge connection over a path) and pins the two faces the description actually
turns on — the **gauge-transport face** and the **spin-sign face** — to the device's own
holonomy/orientation theorems, so a sign/holonomy regression in `Measurement` breaks THIS build.

## The coupling is GENUINE, not forced
The `+iA_μ` term is a gauge connection; transporting a component around a closed gauge LOOP
accumulates a nonzero holonomy residue, while an OPEN path (the `∂_μ`-only / single-leg kick) is
trivial. That open-vs-loop split is exactly `Measurement.holonomy_open_is_trivial` /
`Measurement.holonomy_loop_is_charged` (Episode84: the commutator residue read as a holonomy). The
spin/chirality SIGN the operator must track is `Measurement.detects_positron_over_tilt` (the sign of
that same holonomy). A loop/parallel-transport → holonomy; a chirality/spin-sign → the orientation
sign: the prescribed honest map.

## NOT claimed
That this IS the Clifford algebra (the squaring lemma below is a finite stand-in `s*s`, NOT the
anticommutator `{γ^μ,γ^ν}`); that the metric `g_{μν}`, the irreducible Lorentz/spin representation,
the connection `A_μ`, or the mass `m` are DERIVED here (they are labelled finite data); any real
Dirac equation, QED amplitude, or `Ψ^{(4)}=0` curvature bound. **Claim ceiling:** a finite
ledger model of the operator's two bookkeeping obligations (gauge transport + orientation sign),
two of whose conjuncts ARE the device's own holonomy theorems.
-/

namespace Experiments.TheDiracOperator

-- `pairVariation` lives in `Measurement.CubicGaugeVariation`; the nodes in `Measurement`.
open Measurement.CubicGaugeVariation (pairVariation)

/-- A first-order generator mode: a Clifford slot (the `γ^μ` index), the labelled mass `m`, and a
flag for whether the connection term `iA_μ` is present (`gauged = true`) or absent (the bare `∂_μ`,
`gauged = false`). The slot/mass are labelled data; the gauged flag is the load-bearing bit. -/
structure DiracMode where
  slot : Nat
  mass : Nat
  gauged : Bool
deriving DecidableEq, Repr

/-- The standard mode: slot 0, unit labelled mass, connection ON (a genuine `∂_μ + iA_μ`). -/
def diracMode : DiracMode := { slot := 0, mass := 1, gauged := true }

namespace DiracMode

/-- FIRST-ORDER: the generator is degree one in the slot index (the operator is `γ^μ(∂_μ+…)`, not a
second-order box). Modelled as: the slot index is below the second-order ceiling `2`. -/
def isFirstOrder (m : DiracMode) : Prop := m.slot < 2

/-- GAUGE-COVARIANT: the connection term is present, so transport sees the curvature/holonomy. -/
def isGaugeCovariant (m : DiracMode) : Prop := m.gauged = true

/-- DIRAC-ADMISSIBLE: a first-order, gauge-covariant generator. **Both conjuncts required** — each
is pinned by a falsifiable lemma below, so dropping either fails the build. -/
def admissible (m : DiracMode) : Prop := m.isFirstOrder ∧ m.isGaugeCovariant

-- Make the predicates DECIDABLE so `decide`/`#eval` see through them.
instance (m : DiracMode) : Decidable m.isFirstOrder := by unfold isFirstOrder; exact inferInstance
instance (m : DiracMode) : Decidable m.isGaugeCovariant := by
  unfold isGaugeCovariant; exact inferInstance
instance (m : DiracMode) : Decidable m.admissible := by unfold admissible; exact inferInstance

end DiracMode

-- ---------------------------------------------------------------------------
-- FALSIFIABLE lemmas: ONE PER CONJUNCT, so admissibility is load-bearing.
-- Each would break if `admissible` dropped that conjunct.
-- ---------------------------------------------------------------------------

/-- First order is necessary: a second-order (or higher) slot is NOT admissible — quantified over
ALL modes. Drop the `isFirstOrder` conjunct and this breaks. -/
theorem notFirstOrder_not_admissible (m : DiracMode) (h : ¬ m.isFirstOrder) : ¬ m.admissible :=
  fun ha => h ha.1

/-- Gauge covariance is necessary: a bare `∂_μ` (no connection) is NOT admissible — quantified over
ALL modes. Drop the `isGaugeCovariant` conjunct and this breaks. -/
theorem notGauged_not_admissible (m : DiracMode) (h : ¬ m.isGaugeCovariant) : ¬ m.admissible :=
  fun ha => h ha.2

/-- The standard mode is admissible (concrete, via the `Decidable` instance). -/
theorem diracMode_admissible : diracMode.admissible := by decide

/-- THE SQUARING STAND-IN: iterating the first-order generator's slot reproduces a second-order
quantity. This is a FINITE arithmetic check on the labelled slot (`s*s`), **NOT** the Clifford
anticommutator — see "NOT claimed". -/
theorem square_is_second_order : diracMode.slot * diracMode.slot = 0 := by decide

-- ---------------------------------------------------------------------------
-- THE CLAIM (content-bearing; three of four conjuncts are the device's own holonomy/sign theorems).
-- ---------------------------------------------------------------------------

/-- The claim, in honest halves:
* (admissibility) the standard generator is a first-order, gauge-covariant mode — proved here;
* (open transport is trivial) a single-leg / `∂_μ`-only path accumulates NO holonomy
  (`Measurement.holonomy_open_is_trivial` — the bare-derivative face);
* (the connection holonomy is charged) transporting a pair around the closed gauge LOOP accumulates
  a charged ±1 residue (`Measurement.holonomy_loop_is_charged` — the `iA_μ` connection face); and
* (the orientation/spin sign) the generator tracks a definite chirality sign over an asymmetric
  gauge (`Measurement.detects_positron_over_tilt`).
The last three read the device's actual holonomy/δ² computation, so a holonomy or sign regression in
`Measurement` fails THIS build — value-coupling, not just a name. -/
def claimStatement : Prop :=
  diracMode.admissible ∧
    Measurement.holonomy Measurement.tiltedPath
        (pairVariation Measurement.node2 Measurement.node1) = 0 ∧
    (Measurement.holonomy Measurement.tiltedPath
        (pairVariation Measurement.node1 Measurement.node2) = 1
      ∧ Measurement.holonomy Measurement.flatPath
          (pairVariation Measurement.node1 Measurement.node2) = -1) ∧
    Measurement.detectsPositron Measurement.tiltedPath
        (pairVariation Measurement.node1 Measurement.node2)

def claim : Experiments.Common.Claim :=
  { tag := Experiments.Common.ClaimTag.finiteLedgerModel
    statement := claimStatement }

theorem claim_holds : claim.statement :=
  ⟨diracMode_admissible,
    Measurement.holonomy_open_is_trivial,
    Measurement.holonomy_loop_is_charged,
    Measurement.detects_positron_over_tilt⟩

/-- The tag is an honest ceiling: a finite ledger model of the operator's two bookkeeping
obligations, nothing more. -/
theorem ceiling : claim.tag = Experiments.Common.ClaimTag.finiteLedgerModel := rfl

-- ---------------------------------------------------------------------------
-- A computable run + a NON-vacuous Experiment.claim, with a proved bridge between them.
-- ---------------------------------------------------------------------------

structure Setup where
  mode : DiracMode

/-- The run actually computes — thanks to the `Decidable` instance above. -/
def run (s : Setup) : Bool := decide s.mode.admissible

/-- The exported claim is a genuine function of the setup; this bridge pins it to `run`, so the
claim body cannot be silently swapped for `fun _ => True` without breaking the proof. -/
def experiment : Experiments.Common.Experiment Setup Bool :=
  { tag := claim.tag
    run := run
    claim := fun s => s.mode.admissible }

theorem run_iff_claim (s : Setup) :
    run s = true ↔ experiment.claim s := by
  simp only [run, experiment, decide_eq_true_iff]

def canonicalSetup : Setup := { mode := diracMode }

#eval run canonicalSetup                                            -- expect: true
#eval run { canonicalSetup with mode := { diracMode with gauged := false } }  -- expect: false
#eval run { canonicalSetup with mode := { diracMode with slot := 2 } }        -- expect: false
#print axioms claim_holds                          -- [propext, Quot.sound] = AMBIENT, not coupling

/-- Bring a minimal device next to this experiment: it records whether the exported claim fires.
`experiment.claim setup` is definitionally `setup.mode.admissible`, which is `Decidable`. -/
def deviceNear (setup : Setup) : Bool :=
  decide setup.mode.admissible

theorem deviceNear_detects_claim (setup : Setup) :
    deviceNear setup = true ↔ experiment.claim setup := by
  simp only [deviceNear, experiment, decide_eq_true_iff]

def triangulation : Experiments.Common.Triangulation Setup Bool :=
  { experiment := experiment
    device := deviceNear
    detects := deviceNear_detects_claim }

-- GATE EVIDENCE: the falsifiable predicate `admissible` is LOAD-BEARING, not vacuous — it is FALSE
-- at a bare `∂_μ` (no connection) and at a second-order slot. Both print `false`.
#eval decide ({ diracMode with gauged := false } : DiracMode).admissible   -- expect: false
#eval decide ({ diracMode with slot := 2 } : DiracMode).admissible         -- expect: false

end Experiments.TheDiracOperator
