import Experiments.Common
import Measurement.Episode84

/-!
# The Aharonov-Bohm Effect — an effect-specific, falsifiable, device-coupled test

Rebuilt to the exemplar shape (see `device/Experiments/ThePositronAnnihilationEffect/Experiment1.lean`).
It replaces the vacuous 3-`Nat` `CountSetup` / `labelsOnly` stub with:

1. an **effect-specific domain** (`Branch`, `Interferometer`) drawn from the description — two
   coherent beam branches encircling a confined flux, with a finite slot count for the recombined
   phase shift;
2. genuinely **falsifiable** quantified lemmas (`∀`, would break if the model dropped a hypothesis):
   `open_path_no_shift` (an unclosed path registers no AB shift — the loop conjunct is load-bearing)
   and `wrong_flux_no_shift` (the enclosed-flux conjunct is load-bearing);
3. a **content-bearing** claim — a real conjunction, never `True`;
4. an **honest tag** (`finiteLedgerModel`) + a candid "NOT claimed" disclaimer;
5. explicit `Decidable` instances so `decide`/`#eval` see through the richer `Prop` predicates;
6. **device coupling**: two conjuncts of `claim_holds` are discharged by `Measurement` theorems
   (`Measurement.holonomy_loop_is_charged`, `Measurement.holonomy_open_is_trivial`), so a
   sign/structure regression in the device's holonomy computation breaks *this* build.

## Physics (modelled finitely)
A coherent electron beam is split into two branches that encircle a region of confined magnetic
flux Φ.  Although `F_{μν}=0` along both paths, the connection `A_μ` transports phase; the cumulative
phase around the **closed loop** is the holonomy `∮ A·dx = eΦ/ℏ`.  When the beams recombine the
interference pattern shifts by an amount fixed by that holonomy.  The apparatus registers an AB
shift iff (a) the two branches are **recombined into a closed loop** and (b) the loop **encloses a
nontrivial flux** (the holonomy is a nonzero element of the connection's holonomy group).  An open,
un-recombined path encloses nothing and registers no shift — "curvature without force" is visible
only around the loop.

## NOT claimed
That this measures a real Aharonov-Bohm fringe; that `e Φ/ℏ` or the flux quantum `h/e` is *derived*
(they are labelled constants); any continuum gauge connection, real interference optics, or rate.
The model is a finite ledger of the loop/open bookkeeping; the holonomy *value* is borrowed from the
device's `Measurement.holonomy` (Episode84), which is itself an honest finite δ²-residue, not a real
`∮ A·dx`.  **Claim ceiling:** a finite ledger model of the loop-vs-open AB logic, two of whose
conjuncts are the device's own holonomy theorems.
-/

namespace Experiments.TheAharonovBohmEffect

open Measurement (tiltedPath flatPath node1 node2 holonomy)
open Measurement.CubicGaugeVariation (pairVariation)

/-- A coherent beam branch: which of the two arms it is, and whether it has been recombined with
its partner (the two arms must meet again to close the loop and read interference). -/
structure Branch where
  arm : Nat
  recombined : Bool
deriving DecidableEq, Repr

/-- The apparatus: the two arms encircle a region; `enclosedFlux` is the (finite, integer) flux
read as the loop holonomy, and `slots` is the number of fringe slots the recombined phase shift
can land in. -/
structure Interferometer where
  enclosedFlux : Int
  slots : Nat
deriving Repr

/-- The standard apparatus: a nontrivial enclosed flux (`+1`, the smallest charged holonomy of
Episode84) and 137 fringe slots. -/
def defaultInterferometer : Interferometer := { enclosedFlux := 1, slots := 137 }

namespace Interferometer

/-- The loop is **closed**: both arms have been recombined.  Only a closed loop has a holonomy to
read; an open path encloses nothing. -/
def closedLoop (_d : Interferometer) (left right : Branch) : Prop :=
  left.recombined = true ∧ right.recombined = true ∧ left.arm ≠ right.arm

/-- The loop encloses a **nontrivial flux**: the holonomy is a nonzero element of the connection's
holonomy group.  `F=0` locally, yet `∮ A·dx ≠ 0`. -/
def nontrivialFlux (d : Interferometer) : Prop :=
  d.enclosedFlux ≠ 0

/-- THE AB DETECTION RULE: an interference shift is registered iff the two branches are recombined
into a closed loop AND that loop encloses a nontrivial flux.  **Both conjuncts are required** — each
is pinned by a falsifiable lemma below, so dropping either fails the build. -/
def registersShift (d : Interferometer) (left right : Branch) : Prop :=
  d.closedLoop left right ∧ d.nontrivialFlux

-- Make the richer predicates DECIDABLE so `decide`/`#eval` work.
instance (d : Interferometer) (left right : Branch) : Decidable (d.closedLoop left right) := by
  unfold closedLoop; exact inferInstance
instance (d : Interferometer) : Decidable (d.nontrivialFlux) := by
  unfold nontrivialFlux; exact inferInstance
instance (d : Interferometer) (left right : Branch) : Decidable (d.registersShift left right) := by
  unfold registersShift; exact inferInstance

end Interferometer

-- ---------------------------------------------------------------------------
-- FALSIFIABLE lemmas: ONE PER CONJUNCT, so the whole rule is load-bearing.
-- ---------------------------------------------------------------------------

/-- The loop conjunct is necessary: an OPEN path (some branch not recombined) registers no shift.
Quantified over ALL interferometers and branch pairs. -/
theorem open_path_no_shift
    (d : Interferometer) (left right : Branch) (h : ¬ d.closedLoop left right) :
    ¬ d.registersShift left right :=
  fun hr => h hr.1

/-- The flux conjunct is necessary: a loop enclosing trivial flux registers no shift.
Quantified over ALL interferometers and branch pairs. -/
theorem wrong_flux_no_shift
    (d : Interferometer) (left right : Branch) (h : ¬ d.nontrivialFlux) :
    ¬ d.registersShift left right :=
  fun hr => h hr.2

-- ---------------------------------------------------------------------------
-- The canonical recombined event.
-- ---------------------------------------------------------------------------

/-- The two recombined arms of a closed AB loop. -/
def armA : Branch := { arm := 0, recombined := true }
def armB : Branch := { arm := 1, recombined := true }

/-- The apparatus registers the canonical recombined loop over a nontrivial flux. -/
theorem registers_canonical : defaultInterferometer.registersShift armA armB := by decide

/-- An un-recombined arm breaks the loop, so no shift is registered (a concrete witness of
`open_path_no_shift`). -/
theorem open_arm_no_shift :
    ¬ defaultInterferometer.registersShift armA { armB with recombined := false } := by decide

-- ---------------------------------------------------------------------------
-- THE CLAIM (content-bearing; two of four conjuncts are the device's own theorems).
-- ---------------------------------------------------------------------------

/-- The claim, in honest halves:
* (detection) the apparatus registers the canonical recombined loop over a nontrivial flux —
  proved here from the finite AB rule;
* (holonomy is charged around the LOOP) `Measurement.holonomy_loop_is_charged` — the device's
  signed holonomy reads `+1` over the tilted flux (and `-1` over the flat one); a SIGN regression
  in the device fails this build (value-coupling);
* (holonomy is trivial on the OPEN path) `Measurement.holonomy_open_is_trivial` — the single-leg /
  un-recombined path reads `0`.  This is the AB hallmark: nonzero around the loop, zero on the open
  path — "curvature without force". -/
def claimStatement : Prop :=
  defaultInterferometer.registersShift armA armB ∧
    (holonomy tiltedPath (pairVariation node1 node2) = 1
      ∧ holonomy flatPath (pairVariation node1 node2) = -1) ∧
    holonomy tiltedPath (pairVariation node2 node1) = 0

def claim : Experiments.Common.Claim :=
  { tag := Experiments.Common.ClaimTag.finiteLedgerModel
    statement := claimStatement }

theorem claim_holds : claim.statement :=
  ⟨registers_canonical,
    Measurement.holonomy_loop_is_charged,
    Measurement.holonomy_open_is_trivial⟩

/-- The tag is an honest ceiling: a finite ledger model, nothing more. -/
theorem ceiling : claim.tag = Experiments.Common.ClaimTag.finiteLedgerModel := rfl

-- ---------------------------------------------------------------------------
-- A computable run + a NON-vacuous Experiment.claim, with a proved bridge.
-- ---------------------------------------------------------------------------

structure Setup where
  interferometer : Interferometer
  left : Branch
  right : Branch

/-- The run actually computes — thanks to the `Decidable` instances above. -/
def run (s : Setup) : Bool := decide (s.interferometer.registersShift s.left s.right)

/-- The exported claim is a genuine function of the setup, and this bridge pins it to `run`. -/
def experiment : Experiments.Common.Experiment Setup Bool :=
  { tag := claim.tag
    run := run
    claim := fun s => s.interferometer.registersShift s.left s.right }

theorem run_iff_claim (s : Setup) :
    run s = true ↔ experiment.claim s := by
  simp only [run, experiment, decide_eq_true_iff]

def canonicalSetup : Setup :=
  { interferometer := defaultInterferometer, left := armA, right := armB }

#eval run canonicalSetup                                              -- expect: true
#eval run { canonicalSetup with right := { armB with recombined := false } }  -- expect: false (open path)
#eval run { canonicalSetup with interferometer := { defaultInterferometer with enclosedFlux := 0 } }  -- expect: false (no flux)
#print axioms claim_holds

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

end Experiments.TheAharonovBohmEffect
