import Experiments.Common
import Measurement.Episode85

/-!
# The Echo Chamber Maze Solution

Source: `instrument/chapters/10.tex:1127` (phenomenon "The Echo Chamber Maze Solution").

## Physics (modelled finitely)
Navigate a maze by clapping; echoes trace causal paths and parallel-transport the clap's rhythm.
A STRAIGHT corridor (flat metric) returns a clean echo — perfect parallel transport, no phase
residue.  A CLOSED LOOP through curved passages returns a DISTORTED echo — a phase residue that
measures the curvature `R ≠ 0`.  The maze is globally consistent exactly when the total loop
residue cancels.

This file gives the effect its OWN domain (`Corridor`: a straight segment vs. a curved loop) and a
falsifiable transport rule, and then COUPLES that rule to the device's gauge holonomy: the maze's
"open corridor returns a clean echo" IS the device's `holonomy_open_is_trivial` (residue 0 on any
single-leg/open path) and the maze's "a closed loop carries a phase residue" IS the device's
`holonomy_loop_is_charged` (nonzero commutator residue around the genuine pair-loop, ±1).  An echo
maze and a gauge loop are the same object: a holonomy is a commutator residue around a loop.

## NOT claimed
That this measures a real acoustic echo, a real Riemann curvature tensor, or Einstein's equation;
that `R` is *derived* (the residue is a labelled finite Int from the device's δ² commutator); that
the "global consistency" condition is the actual `U^{(4)}=0` cancellation of the continuum — the
loop/open split is modelled as the device's signed holonomy on two concrete finite paths, nothing
more.  **Claim ceiling:** a finite ledger model of the open-vs-loop transport split, two of whose
conjuncts are the device's own holonomy theorems.
-/

namespace Experiments.TheEchoChamberMazeSolution

open Measurement (holonomy node1 node2 flatPath tiltedPath flatEvents antimatterCount)
open Measurement.CubicGaugeVariation (pairVariation)

/-- The two shapes of passage a clapper can traverse: a straight corridor (no loop, an OPEN path)
or a closed loop through curved passages. -/
inductive Corridor where
  | straight
  | curvedLoop
deriving DecidableEq, Repr

/-- The device path/flux a corridor is transported over.  `flat` = symmetric maze (no net
curvature), `tilted` = an asymmetric maze (net curvature). -/
inductive Flux where
  | flat
  | tilted
deriving DecidableEq, Repr

namespace Corridor

/-- The phase residue a clap accumulates traversing `c` over flux `f`, read as the device's signed
gauge holonomy: a STRAIGHT corridor is the device's OPEN path (one leg held — `pairVariation node2
node1`), a CURVED LOOP is the device's genuine pair-LOOP (both legs moved — `pairVariation node1
node2`).  The flux selects the baseline path (`flatPath`/`tiltedPath`). -/
def residue (c : Corridor) (f : Flux) : Int :=
  let path := match f with
    | Flux.flat => flatPath
    | Flux.tilted => tiltedPath
  let loop := match c with
    | Corridor.straight => pairVariation node2 node1
    | Corridor.curvedLoop => pairVariation node1 node2
  holonomy path loop

/-- The echo is CLEAN when no phase residue returns (`residue = 0`): perfect parallel transport. -/
def cleanEcho (c : Corridor) (f : Flux) : Prop :=
  residue c f = 0

instance (c : Corridor) (f : Flux) : Decidable (cleanEcho c f) := by
  unfold cleanEcho; exact inferInstance

end Corridor

-- ---------------------------------------------------------------------------
-- FALSIFIABLE lemmas.  Each is ∀-quantified and would break under a wrong model.
-- ---------------------------------------------------------------------------

/-- CLEAN ECHO on the straight corridor (over the native tilted flux): the open path carries no
phase residue.  This IS the device's `holonomy_open_is_trivial` — the single-leg slip `node1`
already equals `tiltedPath.middleRight`, so the residue is invisible to one-leg instruments. -/
theorem straight_corridor_clean_echo :
    Corridor.cleanEcho Corridor.straight Flux.tilted := by
  unfold Corridor.cleanEcho Corridor.residue; decide

/-- CURVATURE (falsifiable, ∀ over fluxes): a curved LOOP NEVER returns a clean echo — it carries a
nonzero phase residue on EVERY baseline (`R ≠ 0` whether the maze is flat or tilted).  Drop the
`curvedLoop` specialization (quantify over ALL corridors) and it BREAKS: the straight corridor over
the tilted flux IS clean — that is exactly `straight_corridor_clean_echo`.  This lemma is the
load-bearing falsifiable content: the open/loop split is real. -/
theorem curved_loop_never_clean (f : Flux) :
    ¬ Corridor.cleanEcho Corridor.curvedLoop f := by
  cases f <;> (unfold Corridor.cleanEcho Corridor.residue; decide)

-- ---------------------------------------------------------------------------
-- THE CLAIM (content-bearing; the open/loop split IS the device's holonomy).
-- ---------------------------------------------------------------------------

/-- The claim, in honest parts:
* (clean echo on the straight corridor) the open path returns no residue — proved here, and it IS
  the device's `holonomy_open_is_trivial`;
* (curved loop is charged) the closed loop returns a phase residue `±1` on the two baselines —
  `Measurement.holonomy_loop_is_charged`, the device's own theorem (value/sign-coupled: a sign
  regression in `Measurement` fails THIS build);
* (the split, counted) over the maze's NATIVE symmetric baseline the residue census reads no
  antimatter — `Measurement.native_antimatter_is_zero`, the global-consistency / cancellation face.
The middle two conjuncts read the device's actual δ² commutator, so a sign or count regression in
`Measurement` breaks this file. -/
def claimStatement : Prop :=
  Corridor.cleanEcho Corridor.straight Flux.tilted ∧
    (holonomy tiltedPath (pairVariation node1 node2) = 1
      ∧ holonomy flatPath (pairVariation node1 node2) = -1) ∧
    antimatterCount flatEvents = 0

def claim : Experiments.Common.Claim :=
  { tag := Experiments.Common.ClaimTag.finiteLedgerModel
    statement := claimStatement }

theorem claim_holds : claim.statement :=
  ⟨straight_corridor_clean_echo,
    Measurement.holonomy_loop_is_charged,
    Measurement.native_antimatter_is_zero⟩

theorem ceiling :
    claim.tag = Experiments.Common.ClaimTag.finiteLedgerModel := rfl

-- ---------------------------------------------------------------------------
-- A computable run + a non-vacuous Experiment.claim, with a proved bridge.
-- ---------------------------------------------------------------------------

structure Setup where
  corridor : Corridor
  flux : Flux

def defaultSetup : Setup := { corridor := Corridor.straight, flux := Flux.tilted }

/-- The run computes — thanks to the `Decidable` instance above. -/
def run (s : Setup) : Bool := decide (Corridor.cleanEcho s.corridor s.flux)

def experiment : Experiments.Common.Experiment Setup Bool :=
  { tag := claim.tag
    run := run
    claim := fun s => Corridor.cleanEcho s.corridor s.flux }

theorem run_iff_claim (s : Setup) :
    run s = true ↔ experiment.claim s := by
  show decide (Corridor.cleanEcho s.corridor s.flux) = true ↔ _
  exact decide_eq_true_iff

#eval run defaultSetup                                          -- expect: true  (clean echo)
#eval run { defaultSetup with corridor := Corridor.curvedLoop } -- expect: false (curved loop, residue)
#print axioms claim_holds

/-- Bring a minimal device next to this experiment: it records whether the exported claim fires. -/
def deviceNear (setup : Setup) : Bool :=
  decide (Corridor.cleanEcho setup.corridor setup.flux)

theorem deviceNear_detects_claim (setup : Setup) :
    deviceNear setup = true ↔ experiment.claim setup := by
  show decide (Corridor.cleanEcho setup.corridor setup.flux) = true ↔ _
  exact decide_eq_true_iff

def triangulation : Experiments.Common.Triangulation Setup Bool :=
  { experiment := experiment
    device := deviceNear
    detects := deviceNear_detects_claim }

end Experiments.TheEchoChamberMazeSolution
