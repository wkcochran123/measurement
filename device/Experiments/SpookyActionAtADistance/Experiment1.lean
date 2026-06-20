import Experiments.Common

/-!
# Spooky Action at a Distance — a finite reassociation model (exemplar shape)

This file follows the worked exemplar (`ThePositronAnnihilationEffect/Experiment1.lean`,
see `device/Experiments/FEEDBACK2.md`): it carries an **effect-specific domain**, several
**falsifiable** ∀-quantified lemmas, and a **content-bearing** claim — not the 3-`Nat`
`CountSetup` template.

## Physics (modelled finitely)
Following the source (`instrument/chapters/06.tex:635`, `ex:spooky`): an *uncorrelant*
`S = {Eᵢ, Eⱼ}` is a set of two spatially separated measurement events whose order may be
permuted without changing any **invariant scalar** of the universe tensor:
`Eᵢ Eⱼ = Eⱼ Eᵢ`. When an observer records `Eᵢ`, the global ordering is fixed and the
universe tensor is updated; because `Eⱼ` belongs to the same uncorrelant set, its
contribution is now determined **consistently** with `Eᵢ`, even at spacelike separation.
The "spooky" correlation is exactly this: the recorded global invariant does **not depend
on which event the observer happened to record first** — reassociation within the
uncorrelant subset.

We make this finite and decidable with the harness `Boundary`. An `Uncorrelant` is a pair
of opaque event labels. A *recording* maps the pair to a `Universe` state carrying (a) the
order the observer fixed and (b) the global **invariant scalar**. The shared boundary
between the two distant labs is exactly that invariant scalar. The content is:

* **commutation** — recording `(Eᵢ,Eⱼ)` and recording the permuted `(Eⱼ,Eᵢ)` are
  boundary-compatible: they agree on the invariant (this is `EᵢEⱼ = EⱼEᵢ` made finite); and
* **a genuine signal would break it** — a recording rule whose invariant *did* depend on
  the local recording order is NOT boundary-compatible across the permutation. That is the
  falsifiable contrast that makes the commutation conjunct load-bearing.

## NOT claimed
That any nonlocal influence exists (none does — the agreement is reassociation bookkeeping,
no signal crosses the seam); that this reproduces a quantitative Bell inequality (no CHSH,
no expectation values, no Tsirelson bound); any entanglement amplitude, Born-rule
probability, or measurement-outcome statistics; that the "invariant scalar" is derived (it
is a labelled finite stand-in for an invariant of the universe tensor). The events are
opaque labels, not localized field configurations. **Claim ceiling:** a finite ledger model
of order-reassociation within an uncorrelant set — the permutation-invariance of the shared
invariant — discharged by the harness `Boundary.compatible`.
-/

namespace Experiments.SpookyActionAtADistance

/-- An opaque finite measurement-event label. Two of these form an uncorrelant set. The
labels carry no geometry — only identity. -/
inductive Event where
  | eI
  | eJ
deriving DecidableEq, Repr

/-- An *uncorrelant*: an ordered presentation of the two spatially separated events. The
`order` field records which event the observer reaches first; `permute` swaps it. The
physical content (`ex:spooky`) is that this order is *not* an invariant. -/
structure Uncorrelant where
  first : Event
  second : Event
deriving DecidableEq, Repr

/-- Permuting the uncorrelant: `Eᵢ Eⱼ ↦ Eⱼ Eᵢ`. -/
def Uncorrelant.permute (u : Uncorrelant) : Uncorrelant :=
  { first := u.second, second := u.first }

/-- The invariant scalar carried by a `Universe` state after a recording: a finite
stand-in for an invariant of the universe tensor. -/
abbrev Invariant := Nat

/-- The recorded `Universe` state: the order the observer happened to fix, together with the
global invariant scalar the recording produced. Only the `invariant` is visible across the
seam to the distant lab. -/
structure Universe where
  fixedFirst : Event
  invariant : Invariant
deriving DecidableEq, Repr

/-- The honest recording rule for an uncorrelant: the observer fixes the order, but the
**invariant scalar is symmetric** in the two events — it does not see the order. Here the
invariant is the unordered tally of which events are present (always both, so a constant of
the *content* of the set, independent of presentation). This is `EᵢEⱼ = EⱼEᵢ`: the scalar
the distant lab reads is the same whichever event was recorded first. -/
def record (u : Uncorrelant) : Universe :=
  { fixedFirst := u.first
    invariant := Event.ctorIdx u.first + Event.ctorIdx u.second }

/-- A *hypothetical signalling rule*: a recording whose invariant scalar DID depend on the
recording order (it leaks the locally-fixed order into the global scalar). Physically
forbidden — it would let the distant lab read which event was recorded first. We keep it
ONLY to exhibit the falsifiable contrast: the commutation lemma fails for this rule. -/
def recordSignalling (u : Uncorrelant) : Universe :=
  { fixedFirst := u.first
    invariant := 2 * Event.ctorIdx u.first + Event.ctorIdx u.second }

/-- The boundary shared by the two distant labs: the part of a recorded `Universe` visible
across the seam is exactly its invariant scalar. This is the harness `Boundary`, instantiated
for this effect. -/
def sharedBoundary : Experiments.Common.Boundary Universe Invariant :=
  { restrict := fun w => w.invariant }

-- Decidability of boundary-compatibility, so `decide`/`#eval` see through it.
instance (w v : Universe) :
    Decidable (Experiments.Common.Boundary.compatible sharedBoundary w v) := by
  unfold Experiments.Common.Boundary.compatible sharedBoundary
  exact inferInstance
-- (`w`/`v` are used inside the unfolded goal; the linter cannot see through `unfold`.)

-- ---------------------------------------------------------------------------
-- FALSIFIABLE lemmas. Each is ∀-quantified and would break if the model dropped its
-- hypothesis: they pin the fact that the HONEST recording is order-blind on the invariant
-- (so the distant correlation appears), while a SIGNALLING recording is not.
-- ---------------------------------------------------------------------------

/-- **Commutation of the uncorrelant.** For ALL uncorrelants, recording `u` and recording its
permutation `u.permute` are boundary-compatible: the distant lab reads the SAME invariant
scalar regardless of which event the observer fixed first. This is `Eᵢ Eⱼ = Eⱼ Eᵢ` made
finite, and it is the whole content of the "spooky" appearance. (Replace `record` by a rule
whose invariant depends on the order — see `recordSignalling` — and this fails.) -/
theorem record_permute_compatible (u : Uncorrelant) :
    Experiments.Common.Boundary.compatible sharedBoundary (record u) (record u.permute) := by
  show (record u).invariant = (record u.permute).invariant
  show Event.ctorIdx u.first + Event.ctorIdx u.second
      = Event.ctorIdx u.second + Event.ctorIdx u.first
  omega

/-- **The observer still fixes a definite order locally.** Recording `u` and recording its
permutation disagree on the *locally fixed* first event (whenever the two events differ).
Locality is real — only the seam-visible invariant is permutation-blind. This pins that
`record` does NOT collapse the local order; it keeps it. -/
theorem record_permute_fixes_distinct_order (u : Uncorrelant) (h : u.first ≠ u.second) :
    (record u).fixedFirst ≠ (record u.permute).fixedFirst := by
  show u.first ≠ u.second
  exact h

/-- **A signalling recording breaks commutation.** For the canonical uncorrelant `Eᵢ Eⱼ`, a
recording whose invariant leaks the recording order is NOT boundary-compatible across the
permutation: the distant lab could read which event was recorded first. This is the load-
bearing contrast — it shows `record_permute_compatible` is a real property of `record`, not a
vacuous truth about all recordings. -/
theorem recordSignalling_permute_incompatible :
    ¬ Experiments.Common.Boundary.compatible sharedBoundary
        (recordSignalling ({ first := Event.eI, second := Event.eJ } : Uncorrelant))
        (recordSignalling ({ first := Event.eI, second := Event.eJ } : Uncorrelant).permute) := by
  unfold Experiments.Common.Boundary.compatible sharedBoundary recordSignalling Uncorrelant.permute
  decide

-- ---------------------------------------------------------------------------
-- THE CLAIM (content-bearing; a real conjunction). The first conjunct is the harness
-- `Boundary.compatible` reading the actual invariant scalar, so a regression in that harness
-- predicate or its `DecidableEq` plumbing breaks THIS build (harness coupling, FEEDBACK2 §1).
-- ---------------------------------------------------------------------------

/-- The claim, in honest parts:
* (commutation / spookiness) for ALL uncorrelants, the honest recording and its permutation
  agree on the shared invariant (`record_permute_compatible` — the reassociation that makes a
  distant correlation appear); discharged by the harness `Boundary.compatible`;
* (locality preserved) for distinct-event uncorrelants the locally fixed order is NOT
  collapsed (`record_permute_fixes_distinct_order`); and
* (no signalling) a recording that leaked the order would break that agreement
  (`recordSignalling_permute_incompatible`) — so the first conjunct is a genuine, non-vacuous
  property, not true of every recording rule. -/
def claimStatement : Prop :=
  (∀ u : Uncorrelant,
      Experiments.Common.Boundary.compatible sharedBoundary (record u) (record u.permute)) ∧
    (∀ u : Uncorrelant, u.first ≠ u.second →
      (record u).fixedFirst ≠ (record u.permute).fixedFirst) ∧
    (¬ Experiments.Common.Boundary.compatible sharedBoundary
        (recordSignalling ({ first := Event.eI, second := Event.eJ } : Uncorrelant))
        (recordSignalling ({ first := Event.eI, second := Event.eJ } : Uncorrelant).permute))

def claim : Experiments.Common.Claim :=
  { tag := Experiments.Common.ClaimTag.finiteLedgerModel
    statement := claimStatement }

theorem claim_holds : claim.statement :=
  ⟨record_permute_compatible,
   record_permute_fixes_distinct_order,
   recordSignalling_permute_incompatible⟩

/-- The tag is an honest ceiling: a finite **ledger model** of order-reassociation within an
uncorrelant set — the permutation-invariance of the shared invariant. (The harness has no
`requiredModelKind` fence, so the tag is a convention, not mechanically enforced — same
caveat as the exemplar.) -/
theorem ceiling : claim.tag = Experiments.Common.ClaimTag.finiteLedgerModel := rfl

-- ---------------------------------------------------------------------------
-- A computable run + a NON-vacuous Experiment.claim, with a proved bridge.
-- ---------------------------------------------------------------------------

structure Setup where
  uncorrelant : Uncorrelant

/-- The run computes the discriminating witness: do the two recording orders agree on the
shared invariant? Always `true` for the honest rule — that is the spooky correlation,
executable. -/
def run (s : Setup) : Bool :=
  decide (Experiments.Common.Boundary.compatible sharedBoundary
    (record s.uncorrelant) (record s.uncorrelant.permute))

/-- The exported claim is a genuine function of the setup (not `fun _ => True`): the two
recording orders agree on the shared invariant. The bridge below pins it to `run`. -/
def experiment : Experiments.Common.Experiment Setup Bool :=
  { tag := claim.tag
    run := run
    claim := fun s =>
      Experiments.Common.Boundary.compatible sharedBoundary
        (record s.uncorrelant) (record s.uncorrelant.permute) }

theorem run_iff_claim (s : Setup) :
    run s = true ↔ experiment.claim s := by
  simp only [run, experiment, decide_eq_true_iff]

def canonicalSetup : Setup := { uncorrelant := { first := Event.eI, second := Event.eJ } }

#eval run canonicalSetup  -- expect: true  (the uncorrelant commutes; spooky agreement)

#print axioms claim_holds  -- [propext, Quot.sound] = AMBIENT, not coupling

-- Gate: evaluate the falsifiable predicate where it is FALSE. The SIGNALLING recording does
-- NOT keep the invariant order-blind, so its boundary-compatibility across the permutation is
-- `false` — proving the commutation conjunct is load-bearing, not vacuous.
#eval decide (Experiments.Common.Boundary.compatible sharedBoundary
    (recordSignalling ({ first := Event.eI, second := Event.eJ } : Uncorrelant))
    (recordSignalling ({ first := Event.eI, second := Event.eJ } : Uncorrelant).permute))  -- expect: false

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

end Experiments.SpookyActionAtADistance
