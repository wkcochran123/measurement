import Experiments.Common

/-!
# The Einstein Effect (Ch.07) — relativity of simultaneity as ledger disagreement

Rebuilt to the worked-exemplar shape (cf. `ThePositronAnnihilationEffect/Experiment1.lean`).
This file replaces the 3-`Nat` `CountSetup` template with an **effect-specific** finite model.

## Physics (modelled finitely)
Two observers each record events as successors in their own Peano chain.  An observer's
"clock" is the ordinal position (refinement count) an event occupies *in that observer's
ledger*.  Two events are **simultaneous for an observer** when they share an ordinal label
in that observer's ledger.  Because the two observers refine independently, the SAME pair of
events can be simultaneous for one and not for the other — simultaneity is frame-dependent.
What survives the change of observer is **causal order**: if one event precedes another in
the absolute causal record, every observer agrees on that order.

## Coupling
HARNESS, not device.  This effect has no holonomy / charge / positron content, so a device
coupling would be FAKE (forbidden).  The load-bearing harness coupling is
`Experiments.Common.Boundary.compatible`: the two observers expose the SAME causal-order
shadow of the canonical event pair (that is the invariant), and `claim_holds` discharges that
conjunct through `compatible`.  Breaking the boundary restriction breaks this build.

## NOT claimed
No Lorentz transformation, no light cone, no metric, no continuum limit, no derivation of
`c`.  "Simultaneity", "frame", and "observer" are finite labels here.  The smooth/relativistic
shadow of this constraint is explicitly OUT of scope — this is a finite ledger model of the
ordinal-relabeling phenomenon only.
-/

namespace Experiments.TheEinsteinEffectCh07

/-- An event has an absolute causal index (the invariant) and a name. -/
structure Event where
  causal : Nat
  name : Nat
deriving DecidableEq, Repr

/-- An observer records each event at an ordinal position *in its own ledger*.  Distinct
observers refine independently, so `clock` need not agree across observers. -/
structure Observer where
  /-- the ordinal label this observer assigns to an event (its "clock" reading) -/
  clock : Event -> Nat
  /-- the observer's own causal-order verdict; pinned to the absolute `causal` index below -/
  causalOf : Event -> Nat

namespace Observer

/-- Two events are SIMULTANEOUS for this observer iff they share an ordinal label. -/
def simultaneous (o : Observer) (e f : Event) : Prop :=
  o.clock e = o.clock f

/-- This observer's causal-order shadow of an event: the absolute causal index it reports. -/
def causalShadow (o : Observer) (e : Event) : Nat :=
  o.causalOf e

instance (o : Observer) (e f : Event) : Decidable (o.simultaneous e f) := by
  unfold simultaneous; exact inferInstance

end Observer

-- ---------------------------------------------------------------------------
-- FALSIFIABLE lemmas.  Each is ∀-quantified and would break if a hypothesis dropped.
-- ---------------------------------------------------------------------------

/-- Simultaneity is reflexive — necessary, but NOT the content (every relation is).  Kept only
to contrast with the asymmetry lemma below. -/
theorem simultaneous_refl (o : Observer) (e : Event) : o.simultaneous e e := rfl

/-- **Load-bearing, falsifiable:** if two observers assign DIFFERENT ordinal labels to the same
pair, one can call them simultaneous while the other does not.  Drop the disagreement
hypothesis `h` and the conclusion is false (a single observer can never disagree with itself,
by `simultaneous_refl`).  Quantified over ALL observers and events. -/
theorem disagreement_possible
    (o1 o2 : Observer) (e f : Event)
    (h1 : o1.clock e = o1.clock f) (h2 : o2.clock e ≠ o2.clock f) :
    o1.simultaneous e f ∧ ¬ o2.simultaneous e f :=
  ⟨h1, h2⟩

/-- **Load-bearing, falsifiable:** the invariant.  If two observers share the same causal map,
they agree on the causal order of every event — drop `h` and this fails.  This is the conjunct
the harness `Boundary.compatible` will certify. -/
theorem causal_order_invariant
    (o1 o2 : Observer) (e : Event) (h : o1.causalOf = o2.causalOf) :
    o1.causalShadow e = o2.causalShadow e := by
  unfold Observer.causalShadow
  rw [h]

-- ---------------------------------------------------------------------------
-- A concrete frame pair: two observers who disagree on simultaneity but share causal order.
-- ---------------------------------------------------------------------------

def eventP : Event := { causal := 0, name := 1 }
def eventQ : Event := { causal := 1, name := 2 }

/-- Alice clocks both events to the SAME ordinal label (her refinement cannot resolve their
order in time): the pair is simultaneous for Alice.  She still reports the absolute causal map. -/
def alice : Observer :=
  { clock := fun _ => 7          -- both events get the same ordinal label: simultaneous
    causalOf := fun e => e.causal }

/-- Bob refines finely: he clocks by the absolute causal index, so P precedes Q in time for
him — NOT simultaneous.  But he shares the absolute causal map with Alice. -/
def bob : Observer :=
  { clock := fun e => e.causal
    causalOf := fun e => e.causal }

theorem alice_sees_simultaneous : alice.simultaneous eventP eventQ := by decide
theorem bob_sees_ordered : ¬ bob.simultaneous eventP eventQ := by decide
theorem frames_share_causal : alice.causalOf = bob.causalOf := rfl

-- ---------------------------------------------------------------------------
-- HARNESS coupling: the causal-order shadow is a Boundary the two frames agree on.
-- ---------------------------------------------------------------------------

/-- The boundary visible to a neighboring ledger is the absolute causal index of `eventP`.
The two observers expose the SAME boundary — that is the relativistic invariant, finitely. -/
def causalBoundary : Experiments.Common.Boundary Observer Nat :=
  { restrict := fun o => o.causalShadow eventP }

/-- The two frames are `compatible` at the causal boundary: a genuine harness theorem,
load-bearing for `claim_holds`. -/
theorem frames_compatible :
    Experiments.Common.Boundary.compatible causalBoundary alice bob := by
  show alice.causalShadow eventP = bob.causalShadow eventP
  exact causal_order_invariant alice bob eventP frames_share_causal

-- ---------------------------------------------------------------------------
-- THE CLAIM (content-bearing conjunction; one conjunct is the harness `compatible`).
-- ---------------------------------------------------------------------------

/-- The claim, in honest parts:
* (relativity of simultaneity) the same event pair is simultaneous for Alice and not for Bob;
* (invariant) yet the two frames are `compatible` at the causal boundary
  (`Experiments.Common.Boundary.compatible` — the load-bearing HARNESS coupling). -/
def claimStatement : Prop :=
  (alice.simultaneous eventP eventQ ∧ ¬ bob.simultaneous eventP eventQ) ∧
    Experiments.Common.Boundary.compatible causalBoundary alice bob

def claim : Experiments.Common.Claim :=
  { tag := Experiments.Common.ClaimTag.finiteLedgerModel
    statement := claimStatement }

theorem claim_holds : claim.statement :=
  ⟨⟨alice_sees_simultaneous, bob_sees_ordered⟩, frames_compatible⟩

/-- The tag is an honest ceiling: a finite ledger model of ordinal relabeling, nothing more. -/
theorem ceiling : claim.tag = Experiments.Common.ClaimTag.finiteLedgerModel := rfl

-- ---------------------------------------------------------------------------
-- A computable run + a non-vacuous Experiment.claim, with a proved bridge.
-- ---------------------------------------------------------------------------

structure Setup where
  observer : Observer
  left : Event
  right : Event

/-- The run computes whether THIS observer judges the pair simultaneous. -/
def run (s : Setup) : Bool := decide (s.observer.simultaneous s.left s.right)

def experiment : Experiments.Common.Experiment Setup Bool :=
  { tag := claim.tag
    run := run
    claim := fun s => s.observer.simultaneous s.left s.right }

theorem run_iff_claim (s : Setup) :
    run s = true ↔ experiment.claim s := by
  simp only [run, experiment, decide_eq_true_iff]

def aliceSetup : Setup := { observer := alice, left := eventP, right := eventQ }
def bobSetup : Setup := { observer := bob, left := eventP, right := eventQ }

/-- Bring a minimal device next to this experiment: it records whether the exported claim fires.
`experiment.claim setup` is definitionally `setup.observer.simultaneous setup.left setup.right`,
which is `Decidable` via the instance above. -/
def deviceNear (setup : Setup) : Bool :=
  decide (setup.observer.simultaneous setup.left setup.right)

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

#eval run aliceSetup      -- expect: true   (simultaneous for Alice)
#eval run bobSetup        -- expect: false  (the falsifiable predicate at a FALSE config)
#print axioms claim_holds

end Experiments.TheEinsteinEffectCh07
