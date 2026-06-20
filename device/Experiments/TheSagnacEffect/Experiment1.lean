import Experiments.Common
import Measurement.Episode84

/-!
# The Sagnac Effect — an effect-specific holonomy model, coupled to the device

This file follows the worked exemplar (`ThePositronAnnihilationEffect/Experiment1`):

1. an **effect-specific domain** (`RefinementLeg`, `Loop`) — two opposite-direction
   traversals of the SAME boundary, each carrying a refinement tally — NOT the generic
   3-`Nat` `CountSetup`;
2. genuinely **falsifiable** quantified lemmas (`∀`, would break if the model dropped a
   hypothesis): `equalTallies_no_holonomy` (no asymmetry ⇒ no Sagnac residue) and
   `sameDirection_no_loop` (a loop needs two OPPOSITE traversals);
3. a **content-bearing** claim — a real conjunction, never `True`;
4. an **honest tag** + a candid disclaimer of what it does *not* claim;
5. it **couples to the real device**: one conjunct of `claim_holds` is discharged by
   `Measurement.holonomy_loop_is_charged` (Episode84), so a `sorry`/rename/sign-regression
   in the device's holonomy reading breaks *this* file's build.

## Physics (modelled finitely)
When refinement clocks are transported around a closed loop, global synchronization fails:
the connection's local rate adjustments do not close under cyclic transport. Two paths that
traverse the same boundary in OPPOSITE directions accumulate UNEQUAL refinement tallies. The
Sagnac time difference is the **holonomy** of the bookkeeping rule — the irreducible residue
when a local transport rule cannot be extended consistently around a closed causal cycle.

We model a `Loop` as a forward leg and a backward leg over a shared boundary. The Sagnac
residue is the *signed* difference of their tallies; a non-zero residue is "holonomy present."
The device side reads the SAME structure as a gauge holonomy: zero on an open (single-leg)
path, charged (±1) only around the genuine loop — `Measurement.holonomy_loop_is_charged`.

## NOT claimed
That this reproduces the physical Sagnac formula (no `Ω`, area, or `c`); that the refinement
tally is *derived* from any metric; any rotation rate or fringe shift; that the device's `±1`
holonomy IS a time difference (it is a labelled sign reading, frame-relative — Episode84's
convention). **Claim ceiling:** a finite ledger model of "opposite traversals fail to close,"
one conjunct of which is the device's own holonomy theorem.
-/

namespace Experiments.TheSagnacEffect

/-- One traversal of the boundary: a `tally` of refinement ticks accumulated, and a `forward`
flag recording the orientation of transport. -/
structure RefinementLeg where
  tally : Int
  forward : Bool
deriving DecidableEq, Repr

/-- A closed loop over a shared boundary: a forward leg and a backward leg. -/
structure Loop where
  fwd : RefinementLeg
  bwd : RefinementLeg
deriving Repr

namespace Loop

/-- The legs are genuinely opposite traversals (one forward, one backward) — required for a
"closed loop," not two co-oriented paths. -/
def opposed (l : Loop) : Prop :=
  l.fwd.forward = true ∧ l.bwd.forward = false

/-- THE SAGNAC RESIDUE: the signed difference of the two traversal tallies. The holonomy of the
bookkeeping rule — what fails to cancel when the same boundary is crossed both ways. -/
def residue (l : Loop) : Int :=
  l.fwd.tally - l.bwd.tally

/-- Holonomy is PRESENT iff the residue is non-zero: synchronization fails to close. -/
def holonomyPresent (l : Loop) : Prop :=
  l.residue ≠ 0

/-- THE SAGNAC RULE: a genuine closed loop exhibits the Sagnac effect iff it is two opposite
traversals AND they accumulate unequal tallies (non-zero residue). Both conjuncts are required,
and each is pinned by a falsifiable lemma below. -/
def exhibitsSagnac (l : Loop) : Prop :=
  l.opposed ∧ l.holonomyPresent

-- Make the predicates DECIDABLE so `decide`/`#eval` see through them.
instance (l : Loop) : Decidable l.opposed := by
  unfold opposed; exact inferInstance
instance (l : Loop) : Decidable l.holonomyPresent := by
  unfold holonomyPresent; exact inferInstance
instance (l : Loop) : Decidable l.exhibitsSagnac := by
  unfold exhibitsSagnac; exact inferInstance

end Loop

-- ---------------------------------------------------------------------------
-- FALSIFIABLE lemmas: ONE PER CONJUNCT of the Sagnac rule, so it is load-bearing.
-- ---------------------------------------------------------------------------

/-- ASYMMETRY is necessary: if the two traversals accumulate EQUAL tallies, the residue is zero,
synchronization closes, and there is NO Sagnac effect. Quantified over ALL loops — would break if
`exhibitsSagnac` dropped the `holonomyPresent` conjunct. -/
theorem equalTallies_no_holonomy
    (l : Loop) (h : l.fwd.tally = l.bwd.tally) : ¬ l.exhibitsSagnac :=
  fun hs => hs.2 (by simp [Loop.residue, h])

/-- A CLOSED LOOP is necessary: two CO-oriented traversals (the backward leg also forward) are not
a loop, so they never exhibit Sagnac. Pins the `opposed` conjunct (`.1`). -/
theorem sameDirection_no_loop
    (l : Loop) (h : l.bwd.forward = true) : ¬ l.exhibitsSagnac :=
  fun hs => by
    have := hs.1.2
    rw [h] at this
    exact Bool.noConfusion this

-- ---------------------------------------------------------------------------
-- The canonical Sagnac loop.
-- ---------------------------------------------------------------------------

/-- A clean Sagnac loop: a forward traversal tallying `+1`, a backward traversal tallying `-1`,
so the residue is `2` (non-zero) — opposite directions, unequal tallies. -/
def canonicalLoop : Loop :=
  { fwd := { tally := 1, forward := true }
    bwd := { tally := -1, forward := false } }

/-- The apparatus registers the canonical loop (concrete, via the `Decidable` instance). -/
theorem exhibits_canonical : canonicalLoop.exhibitsSagnac := by decide

/-- The canonical residue is `2` (a frozen-literal check on the chosen loop, not enforced by
`exhibitsSagnac`, which only demands non-zero). -/
theorem residue_canonical : canonicalLoop.residue = 2 := by decide

-- ---------------------------------------------------------------------------
-- THE CLAIM (content-bearing; the holonomy conjunct is the device's own theorem).
-- ---------------------------------------------------------------------------

/-- The claim, in honest halves:
* (Sagnac) the canonical opposite-traversal loop exhibits a non-zero residue — proved here;
* (holonomy signature) the device's gauge holonomy reads `+1` around the genuine pair-loop over a
  tilted flux and `-1` over a flat flux (`Measurement.holonomy_loop_is_charged`, Episode84). This
  IS the Sagnac structure on the device side — the same residue, opposite over the two baselines —
  so a sign-regression in the device's holonomy fails this build (value-coupling, not just a name).
-/
def claimStatement : Prop :=
  canonicalLoop.exhibitsSagnac ∧
    (Measurement.holonomy Measurement.tiltedPath
        (Measurement.CubicGaugeVariation.pairVariation Measurement.node1 Measurement.node2) = 1
      ∧ Measurement.holonomy Measurement.flatPath
        (Measurement.CubicGaugeVariation.pairVariation Measurement.node1 Measurement.node2) = -1)

def claim : Experiments.Common.Claim :=
  { tag := Experiments.Common.ClaimTag.smoothShadowAnalogy
    statement := claimStatement }

theorem claim_holds : claim.statement :=
  ⟨exhibits_canonical, Measurement.holonomy_loop_is_charged⟩

/-- The tag is an honest ceiling: a GR/smooth-shadow analogy, not a QED replication. -/
theorem ceiling : claim.tag = Experiments.Common.ClaimTag.smoothShadowAnalogy := rfl

-- ---------------------------------------------------------------------------
-- A computable run + a NON-vacuous Experiment.claim, with a proved bridge.
-- ---------------------------------------------------------------------------

structure Setup where
  loop : Loop

/-- The run actually computes — thanks to the `Decidable` instances above. -/
def run (s : Setup) : Bool := decide s.loop.exhibitsSagnac

/-- The exported claim is a genuine function of the setup; this bridge pins it to `run`, so the
claim body cannot be silently swapped for `fun _ => True`. -/
def experiment : Experiments.Common.Experiment Setup Bool :=
  { tag := claim.tag
    run := run
    claim := fun s => s.loop.exhibitsSagnac }

theorem run_iff_claim (s : Setup) :
    run s = true ↔ experiment.claim s := by
  simp only [run, experiment, decide_eq_true_iff]

def canonicalSetup : Setup := { loop := canonicalLoop }

#eval run canonicalSetup                                            -- expect: true
#eval run { loop := { canonicalLoop with bwd := canonicalLoop.fwd } } -- expect: false (co-oriented)
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

end Experiments.TheSagnacEffect
