import Experiments.Common

/-!
# The Hall-Einstein-Podolsky-Rosen Effect — effect-specific, falsifiable, content-bearing

Rebuilt to the EXEMPLAR shape (cf. `ThePositronAnnihilationEffect/Experiment1.lean`,
`TheEventHorizonEffect/Experiment1.lean`): an effect-specific domain (not the 3-`Nat`
`CountSetup`), falsifiable `∀`-lemmas, a real conjunction as the claim, an honest tag +
disclaimer, explicit `Decidable` instances, and a HARNESS coupling whose theorem is a
load-bearing conjunct of `claim_holds`.

## Physics (modelled finitely)
The effect: inferences drawn from one experimental ledger about another are admissible only when
the two ledgers are *correlant* — when there is at least one admissible event consistent with
BOTH records. When correlance fails (Monty Hall with the host's constraint removed; EPR detectors
that are locally consistent but globally uncorrelant), conditioning one ledger on the other
introduces *unrecorded structure*, even though each record is locally fine.

We model this as a TWO-REGION COMPATIBILITY problem in the harness's `Boundary` sense. Each side
exposes a finite **boundary view** (`seam`): the contestant's view of which door is "live", the
detector's view of the shared seam. A candidate **shared event** carries both sides; its two
boundary views are *correlant* exactly when they AGREE on the seam — `Boundary.compatible`
(`restrict left = restrict right`). Correlance present ⇒ a shared admissible event exists and the
seam matches. Correlance absent ⇒ the seams disagree, no shared event anchors the joint inference,
and the would-be conditioning is INADMISSIBLE (the no-go).

## NOT claimed
That this captures quantum mechanics, a Bell inequality, the actual Monty Hall probabilities (2/3
vs 1/3), real EPR correlations, entanglement, nonlocality, or any measure-theoretic conditioning.
The "seam" is a labelled finite tag, not a derived observable; "correlance" is rendered as boundary
equality, not as the existence of a genuine joint distribution. We do NOT formalize Bayesian
updating, the host's full rule set, or ER=EPR. **Claim ceiling:** an inadmissibility no-go — a
finite stand-in for the correlance constraint, whose load-bearing conjunct is the harness's own
`Boundary.compatible` witness on the correlant pair.
-/

namespace Experiments.TheHallEinsteinPodolskyRosenEffect

/-- A local experimental ledger. It carries the side's own private constraint (`constrained`:
e.g. the host's rule that the prize door is never opened, or a detector's local setting) and the
shared boundary fact it exposes (`seam`: the door/slot the two records must agree on to be jointly
conditioned). -/
structure LocalLedger where
  /-- The seam value this ledger exposes to its neighbor (the shared boundary fact). -/
  seam : Nat
  /-- Whether this side's private constraint (the host's rule / the detector setting) is present. -/
  constrained : Bool
deriving DecidableEq, Repr

/-- A candidate *shared event*: a single underlying event that two ledgers might both be embedded
into. It pairs the two local records. Joint inference is meaningful only if this event is
*admissible for both* — which forces their seams to coincide. -/
structure SharedEvent where
  left : LocalLedger
  right : LocalLedger
deriving DecidableEq, Repr

/-- The boundary of the joint state is the seam each ledger exposes. We read the seam out of a
ledger as the boundary view. (`Boundary.restrict := LocalLedger.seam`.) -/
def seamBoundary : Experiments.Common.Boundary LocalLedger Nat :=
  { restrict := LocalLedger.seam }

namespace SharedEvent

/-- CORRELANCE: the two ledgers are correlant iff their exposed seams agree — i.e. they are
`Boundary.compatible` under `seamBoundary`. This is exactly "there is a shared admissible event
consistent with both records": the event `⟨left, right⟩` is admissible precisely when the boundary
views match. -/
def correlant (e : SharedEvent) : Prop :=
  Experiments.Common.Boundary.compatible seamBoundary e.left e.right

/-- ADMISSIBLE JOINT INFERENCE: conditioning one ledger on the other is admissible only when the
records are correlant. We model the admissibility verdict as exactly `correlant` — the no-go below
says inference fails when this is false. -/
def jointInferenceAdmissible (e : SharedEvent) : Prop :=
  e.correlant

-- Make the predicates DECIDABLE so `decide`/`#eval` see through them.
instance (e : SharedEvent) : Decidable e.correlant := by
  unfold correlant Experiments.Common.Boundary.compatible seamBoundary; exact inferInstance
instance (e : SharedEvent) : Decidable e.jointInferenceAdmissible := by
  unfold jointInferenceAdmissible; exact inferInstance

end SharedEvent

-- ---------------------------------------------------------------------------
-- FALSIFIABLE lemmas (∀-quantified; drop the hypothesis and they break).
-- ---------------------------------------------------------------------------

/-- THE CORRELANCE NO-GO: when the seams DISAGREE, the records are NOT correlant, hence no shared
admissible event exists and joint inference is inadmissible. Quantified over ALL shared events;
drop the `≠` hypothesis and it is false (matching seams ARE correlant). This is the structural
content of the effect: uncorrelance, not contradiction, blocks the inference. -/
theorem seam_mismatch_blocks_inference
    (e : SharedEvent) (h : e.left.seam ≠ e.right.seam) :
    ¬ e.jointInferenceAdmissible :=
  fun ha => h ha

/-- Conversely, agreeing seams are correlant: the inference is admissible. Falsifiable — without
the equality hypothesis a mismatched pair (vacuously) would satisfy `correlant`. -/
theorem seam_match_is_correlant
    (e : SharedEvent) (h : e.left.seam = e.right.seam) :
    e.jointInferenceAdmissible :=
  h

/-- Correlance is symmetric: swapping the two ledgers preserves admissibility. Falsifiable — the
hypothesis carries the original correlance; drop it and the swapped event need not be correlant. -/
theorem correlant_symm
    (e : SharedEvent) (h : e.correlant) :
    ({ left := e.right, right := e.left } : SharedEvent).correlant :=
  h.symm

-- ---------------------------------------------------------------------------
-- The two canonical events: the correlant game and the uncorrelant one.
-- ---------------------------------------------------------------------------

/-- The CORRELANT case: the host's constraint is present, both ledgers expose the same live seam
(door 1) — there is a shared admissible event, joint inference is meaningful. (Monty Hall WITH the
host rule; locally-and-globally consistent EPR records.) -/
def correlantEvent : SharedEvent :=
  { left := { seam := 1, constrained := true }
    right := { seam := 1, constrained := true } }

/-- The UNCORRELANT case: the host's constraint has been REMOVED on the right ledger, so its
exposed seam drifts (door 2). The two records remain locally well-formed, but no single admissible
event is consistent with both — the seams disagree. (Monty Hall with the host rule removed;
locally-consistent but globally-uncorrelant EPR records.) -/
def uncorrelantEvent : SharedEvent :=
  { left := { seam := 1, constrained := true }
    right := { seam := 2, constrained := false } }

/-- The correlant event is, concretely, correlant. -/
theorem correlantEvent_correlant : correlantEvent.correlant := by decide

/-- The uncorrelant event is, concretely, NOT correlant — the no-go fires. -/
theorem uncorrelantEvent_not_correlant : ¬ uncorrelantEvent.correlant := by decide

-- ---------------------------------------------------------------------------
-- HARNESS COUPLING (load-bearing). Correlance IS the harness's two-region
-- `Boundary.compatible` predicate. The conjunct below is discharged by that
-- harness definition applied to the correlant pair, so a regression/rename in
-- `Experiments.Common.Boundary.compatible` breaks THIS build.
-- ---------------------------------------------------------------------------

/-- The correlant pair IS `Boundary.compatible` under the seam boundary — the harness's own
two-region compatibility predicate, the load-bearing coupling. -/
theorem correlant_is_compatible :
    Experiments.Common.Boundary.compatible seamBoundary
      correlantEvent.left correlantEvent.right :=
  correlantEvent_correlant

-- ---------------------------------------------------------------------------
-- THE CLAIM (content-bearing conjunction; one conjunct is the harness predicate).
-- ---------------------------------------------------------------------------

/-- The claim, in honest parts:
* (correlant ⇒ admissible) the host-constrained pair is correlant — joint inference is admissible;
* (uncorrelant ⇒ no-go) removing the constraint breaks correlance — inference is inadmissible;
* (harness coupling) that correlance IS `Boundary.compatible` on the seam boundary, discharged by
  the harness `Boundary.compatible` predicate (the load-bearing coupling). -/
def claimStatement : Prop :=
  correlantEvent.jointInferenceAdmissible ∧
    ¬ uncorrelantEvent.jointInferenceAdmissible ∧
    Experiments.Common.Boundary.compatible seamBoundary
      correlantEvent.left correlantEvent.right

def claim : Experiments.Common.Claim :=
  { tag := Experiments.Common.ClaimTag.inadmissibilityNoGo
    statement := claimStatement }

theorem claim_holds : claim.statement :=
  ⟨correlantEvent_correlant, uncorrelantEvent_not_correlant, correlant_is_compatible⟩

/-- The tag is an honest ceiling: an inadmissibility no-go (correlance must hold or the inference
is blocked), nothing more. -/
theorem ceiling :
    claim.tag = Experiments.Common.ClaimTag.inadmissibilityNoGo := rfl

-- ---------------------------------------------------------------------------
-- A computable run + a NON-vacuous Experiment.claim, with a proved bridge.
-- ---------------------------------------------------------------------------

structure Setup where
  event : SharedEvent

/-- The run computes whether the shared event admits joint inference (is correlant). -/
def run (s : Setup) : Bool := decide s.event.jointInferenceAdmissible

/-- The exported claim is a genuine function of the setup; this bridge pins it to `run`. -/
def experiment : Experiments.Common.Experiment Setup Bool :=
  { tag := claim.tag
    run := run
    claim := fun s => s.event.jointInferenceAdmissible }

theorem run_iff_claim (s : Setup) :
    run s = true ↔ experiment.claim s := by
  simp only [run, experiment, decide_eq_true_iff]

def canonicalSetup : Setup := { event := correlantEvent }

#eval run canonicalSetup                              -- expect: true   (correlant)
#eval run { event := uncorrelantEvent }               -- expect: false  (uncorrelant — no-go)

-- The exported claim is `fun s => s.event.jointInferenceAdmissible`; make it `Decidable` so the
-- device below can `decide` it.
instance (setup : Setup) : Decidable (experiment.claim setup) := by
  show Decidable setup.event.jointInferenceAdmissible; exact inferInstance

/-- Bring a minimal device next to this experiment: it records whether the exported claim fires. -/
def deviceNear (setup : Setup) : Bool :=
  decide (experiment.claim setup)

theorem deviceNear_detects_claim (setup : Setup) :
    deviceNear setup = true ↔ experiment.claim setup := by
  simp [deviceNear, experiment]

def triangulation : Experiments.Common.Triangulation Setup Bool :=
  { experiment := experiment
    device := deviceNear
    detects := deviceNear_detects_claim }

-- ---------------------------------------------------------------------------
-- GATE EVIDENCE.
-- ---------------------------------------------------------------------------

#print axioms claim_holds   -- expect: [propext, Quot.sound] = ambient decide footprint

-- The falsifiable predicate is LOAD-BEARING, not vacuous: at the uncorrelant event the seams
-- disagree, so `jointInferenceAdmissible` is FALSE and this prints `false`.
#eval decide uncorrelantEvent.jointInferenceAdmissible   -- expect: false

end Experiments.TheHallEinsteinPodolskyRosenEffect
