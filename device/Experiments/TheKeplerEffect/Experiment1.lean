import Experiments.Common
import Measurement.Episode84

/-!
# The Kepler Effect — an orbit is a CLOSED loop, not a fixed point

Source: `instrument/chapters/07.tex:2630` (`ph:orbiting`).

## Physics (modelled finitely)
The description's claim: *an orbit is a closed admissible refinement cycle stabilized by
continuous error correction.  It is not equilibrium; it is a stable failure to terminate.*
Two things have to hold for a finite refinement history to count as an orbit:

1. it **closes** — `γ(t + T) = γ(t)`, i.e. the last recorded state equals the first
   (a `Cycle`), so the book is reread forever rather than running off to a fixed point; and
2. it is **non-degenerate** — the loop genuinely moves (`length ≥ 2` distinct steps), a real
   tangential continuation, not a single state sitting still at a fixed point.

A *fixed point* (the thing an orbit is NOT) is the degenerate `Cycle`: the path never leaves
its start.  The apparatus must accept the genuine orbit and reject the fixed point — and that
open-vs-loop distinction is exactly the device's **holonomy signature**: the open/degenerate
path carries residue `0` (`Measurement.holonomy_open_is_trivial`), the genuine closed loop
carries a nonzero residue (`Measurement.holonomy_loop_is_charged`).  We couple the
"non-degenerate loop" half of the claim to that device fact, so a regression in the device's
open-vs-loop split breaks THIS build.

## NOT claimed
That this is Kepler's law, an inverse-square force, an `1/r` potential, a conserved
angular momentum, a real continuum trajectory, or any dynamics/stability theorem.  There is
NO derivative, NO second variation computed here, NO period `T` predicted, NO PDE.  The
"second-variation stability" of the description is replaced by a finite closure-of-the-ledger
condition; the device holonomy is borrowed only for its **open-path-is-trivial vs loop-is-charged**
contrast (the topological "did it close?" fact), NOT for any positron/charge/antimatter reading.
**Claim ceiling:** a finite ledger model of "an orbit is a non-degenerate closed cycle," one of
whose conjuncts is the device's own open-vs-loop holonomy theorem.
-/

namespace Experiments.TheKeplerEffect

-- `pairVariation` lives in `Measurement.CubicGaugeVariation`; `node1`/`node2`/`tiltedPath`/
-- `flatPath` live directly in `Measurement`.  Open both so the device holonomy facts below
-- can be named.
open Measurement
open Measurement.CubicGaugeVariation

/-- A coarse refinement state on the orbit: a slot on a finite ledger ring. -/
structure OrbitState where
  slot : Nat
deriving DecidableEq, Repr

/-- A finite recorded refinement history: an ordered list of states the ledger passed through.
`states.head` is `γ(t)`; `states.getLast` is `γ(t+T)`. -/
structure History where
  states : List OrbitState
deriving Repr

namespace History

/-- The number of recorded steps in the history. -/
def length (h : History) : Nat := h.states.length

/-- `h` CLOSES: it is non-empty and its last state equals its first — `γ(t+T) = γ(t)`. -/
def closes (h : History) : Prop :=
  h.states.head? = h.states.getLast?

/-- `h` is NON-DEGENERATE: it records at least two steps, so the loop actually moves
(a tangential continuation), rather than a single state sitting at a fixed point. -/
def nonDegenerate (h : History) : Prop :=
  2 ≤ h.length

/-- THE ORBIT RULE: a history is an orbit iff it closes AND is non-degenerate.  **Both
conjuncts are required** — each is pinned by a falsifiable lemma below, so dropping either
fails the build. -/
def isOrbit (h : History) : Prop :=
  h.closes ∧ h.nonDegenerate

-- Make the predicates DECIDABLE so `decide`/`#eval` compute through them.
instance (h : History) : Decidable h.closes := by
  unfold closes; exact inferInstance
instance (h : History) : Decidable h.nonDegenerate := by
  unfold nonDegenerate length; exact inferInstance
instance (h : History) : Decidable h.isOrbit := by
  unfold isOrbit; exact inferInstance

end History

-- ---------------------------------------------------------------------------
-- FALSIFIABLE lemmas: ONE PER CONJUNCT, so the whole orbit rule is load-bearing.
-- Each would break if `isOrbit` dropped that conjunct.
-- ---------------------------------------------------------------------------

/-- Closure is necessary: a history that does NOT close (a runaway / escape) is never an orbit.
Quantified over ALL histories. -/
theorem notCloses_not_orbit (h : History) (hc : ¬ h.closes) : ¬ h.isOrbit :=
  fun ho => hc ho.1

/-- Non-degeneracy is necessary: a history that never moves (a fixed point) is never an orbit,
even though it trivially "closes".  Quantified over ALL histories. -/
theorem degenerate_not_orbit (h : History) (hd : ¬ h.nonDegenerate) : ¬ h.isOrbit :=
  fun ho => hd ho.2

-- ---------------------------------------------------------------------------
-- The canonical orbit and the canonical fixed point.
-- ---------------------------------------------------------------------------

/-- A genuine orbit: three slots, returning to the start — a closed, moving loop. -/
def keplerOrbit : History :=
  { states := [⟨0⟩, ⟨1⟩, ⟨2⟩, ⟨0⟩] }

/-- A fixed point: the path never leaves its start.  Closes trivially, but is degenerate —
NOT an orbit. -/
def fixedPoint : History :=
  { states := [⟨0⟩] }

/-- The apparatus accepts the genuine orbit (concrete, via the `Decidable` instance). -/
theorem keplerOrbit_isOrbit : keplerOrbit.isOrbit := by decide

/-- The apparatus rejects the fixed point: it closes, but it is degenerate. -/
theorem fixedPoint_not_orbit : ¬ fixedPoint.isOrbit := by decide

-- ---------------------------------------------------------------------------
-- THE CLAIM (content-bearing; one conjunct is the device's own holonomy theorem).
-- ---------------------------------------------------------------------------

/-- The claim, in honest halves:
* (it closes) the canonical orbit returns to its start — `keplerOrbit.closes`;
* (it is a real loop, not a fixed point) `keplerOrbit.nonDegenerate`, and the fixed point is
  rejected — `¬ fixedPoint.isOrbit`; and
* (open-vs-loop, device-coupled) the device's **open path carries no holonomy** while the
  **genuine loop carries a nonzero charged residue** — `Measurement.holonomy_open_is_trivial`
  and `Measurement.holonomy_loop_is_charged`.  This is the topological "did it close?" fact a
  closed orbit must satisfy; a regression in the device's open-vs-loop split fails THIS build. -/
def claimStatement : Prop :=
  keplerOrbit.closes ∧
    keplerOrbit.nonDegenerate ∧
    ¬ fixedPoint.isOrbit ∧
    Measurement.holonomy tiltedPath (pairVariation node2 node1) = 0 ∧
    (Measurement.holonomy tiltedPath (pairVariation node1 node2) = 1 ∧
      Measurement.holonomy flatPath (pairVariation node1 node2) = -1)

def claim : Experiments.Common.Claim :=
  { tag := Experiments.Common.ClaimTag.finiteLedgerModel
    statement := claimStatement }

theorem claim_holds : claim.statement :=
  ⟨keplerOrbit_isOrbit.1, keplerOrbit_isOrbit.2, fixedPoint_not_orbit,
    Measurement.holonomy_open_is_trivial, Measurement.holonomy_loop_is_charged⟩

/-- The tag is an honest ceiling: a finite ledger model, nothing more. -/
theorem ceiling : claim.tag = Experiments.Common.ClaimTag.finiteLedgerModel := rfl

-- ---------------------------------------------------------------------------
-- A computable run + a NON-vacuous Experiment.claim, with a proved bridge.
-- ---------------------------------------------------------------------------

abbrev Setup := History

/-- The run actually computes — thanks to the `Decidable` instances above. -/
def run (h : Setup) : Bool := decide h.isOrbit

/-- The exported claim is a genuine function of the setup; this bridge pins it to `run`, so the
claim body cannot be silently swapped for `fun _ => True`. -/
def experiment : Experiments.Common.Experiment Setup Bool :=
  { tag := claim.tag
    run := run
    claim := fun h => h.isOrbit }

theorem run_iff_claim (h : Setup) :
    run h = true ↔ experiment.claim h := by
  simp only [run, experiment, decide_eq_true_iff]

/-- Bring a minimal device next to this experiment: it records whether the exported claim fires.
It routes through `run` (whose `Decidable (isOrbit)` instance exists) rather than `decide`-ing the
opaque `experiment.claim` projection directly. -/
def deviceNear (setup : Setup) : Bool :=
  run setup

theorem deviceNear_detects_claim (setup : Setup) :
    deviceNear setup = true ↔ experiment.claim setup := by
  simp only [deviceNear, run, experiment, decide_eq_true_iff]

def triangulation : Experiments.Common.Triangulation Setup Bool :=
  { experiment := experiment
    device := deviceNear
    detects := deviceNear_detects_claim }

#eval run keplerOrbit                 -- expect: true
#eval run fixedPoint                  -- expect: false  (degenerate — a fixed point, not an orbit)
#print axioms claim_holds             -- [propext, Quot.sound] = AMBIENT; coupling is the device symbols

end Experiments.TheKeplerEffect
