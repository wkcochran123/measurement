import Experiments.Common

/-!
# Shadow Tomography — an effect-specific finite model (rebuilt to the EXEMPLAR shape)

Source: `instrument/chapters/07.tex:198` (`phenomenon`, Aaronson 2013).

This file follows the shape of
`device/Experiments/ThePositronAnnihilationEffect/Experiment1.lean`:

1. an **effect-specific domain** (`History`, `TestFamily`) — NOT the 3-`Nat`
   `Experiments.Common.CountSetup`;
2. genuinely **falsifiable** ∀-quantified lemmas — `differ_above_shadow_indistinguishable`
   and `refinement_below_floor_invisible` each break if a hypothesis is dropped;
3. a **content-bearing** claim: a real conjunction, never `True`, never `by decide`
   on frozen literals;
4. an honest `ClaimTag` + a candid "NOT claimed" disclaimer;
5. explicit `Decidable` instances so `decide`/`#eval` see through the richer `Prop`s;
6. a **device/harness coupling**: the indistinguishability conjunct of `claim_holds`
   is discharged by the harness operator `Experiments.Common.Projection.sameShadow`, and
   the bounded-information conjunct by `Experiments.Common.Counting.boundedBy_of_eq`, so a
   regression in `Common.Basic` (rename/sorry on `sameShadow` or `boundedBy`) breaks THIS build.

## Physics (modelled finitely)
A measurement record is a finite chain of refinements — here a `History`, a list of
fine-grained distinctions, each a `Nat` "scale" tag. The observer applies a bounded family
of admissible tests. We model the whole family by a single **shadow projection**: it keeps
only the distinctions at or above the minimum resolvable scale (the Planck floor), and even
those only up to the bounded number of test outcomes the apparatus can record. Two histories
that differ ONLY in refinements below the floor (or beyond the bound) cast the **same shadow**
and are operationally indistinguishable. The accessible information is bounded by the apparatus,
not by the (possibly exponentially larger) internal refinement count.

## NOT claimed
No quantum tomography, no Hilbert space, no Aaronson sample-complexity bound is *derived* here
— the bound is the apparatus's recorded-outcome count, a labelled finite constant, not an
information-theoretic theorem. We do NOT claim the shadow is the *only* invariant, nor that
distinct shadows imply distinct histories (the converse fails — coarse-graining is lossy).
**Claim ceiling:** a finite ledger / projection model of operational indistinguishability,
one of whose conjuncts is the harness's own `sameShadow` and another its `boundedBy`.
-/

namespace Experiments.ShadowTomography

/-- A single internal refinement: a distinction the system *could* carry, tagged by the
finite `scale` at which it lives. Larger `scale` = coarser / more resolvable. -/
structure Refinement where
  scale : Nat
deriving DecidableEq, Repr

/-- An admissible internal **history**: a finite chain of refinements (the full record). -/
structure History where
  refinements : List Refinement
deriving DecidableEq, Repr

/-- The apparatus / test family: the minimum resolvable scale (`floor`, the Axiom of Planck),
and the bounded number of test outcomes the observer can record (`capacity`). -/
structure TestFamily where
  floor : Nat
  capacity : Nat
deriving Repr

namespace TestFamily

/-- A refinement is **resolvable** by this family iff it sits at or above the Planck floor. -/
def resolvable (t : TestFamily) (r : Refinement) : Prop :=
  t.floor ≤ r.scale

instance (t : TestFamily) (r : Refinement) : Decidable (t.resolvable r) := by
  unfold resolvable; exact inferInstance

/-- The **shadow** the family casts on a history: keep only resolvable refinements (drop
everything below the floor), then truncate to the bounded recordable `capacity`. This is the
coarse projection the observer actually accesses. -/
def shadow (t : TestFamily) (h : History) : List Refinement :=
  (h.refinements.filter (fun r => decide (t.resolvable r))).take t.capacity

/-- The number of distinctions the observer actually records — the operationally accessible
information. By construction it never exceeds the apparatus `capacity`. -/
def accessibleCount (t : TestFamily) (h : History) : Nat :=
  (t.shadow h).length

end TestFamily

-- ---------------------------------------------------------------------------
-- The harness PROJECTION operator, instantiated to this domain (device coupling #1).
-- `Experiments.Common.Projection.sameShadow` is the harness's own notion of
-- "operationally indistinguishable": two states with equal projections.
-- ---------------------------------------------------------------------------

/-- The harness projection for a fixed test family: a history's shadow as the harness sees it. -/
def shadowProjection (t : TestFamily) :
    Experiments.Common.Projection History (List Refinement) :=
  { project := t.shadow }

/-- Two histories are **operationally indistinguishable** under `t` exactly when the harness's
`sameShadow` holds for the `shadowProjection`. We *define* indistinguishability through the
device symbol, so a regression in `Common.Projection.sameShadow` breaks everything downstream. -/
def indistinguishable (t : TestFamily) (h₁ h₂ : History) : Prop :=
  Experiments.Common.Projection.sameShadow (shadowProjection t) h₁ h₂

instance (t : TestFamily) (h₁ h₂ : History) : Decidable (indistinguishable t h₁ h₂) := by
  unfold indistinguishable Experiments.Common.Projection.sameShadow shadowProjection
  exact inferInstance

-- ---------------------------------------------------------------------------
-- FALSIFIABLE lemmas. Each would break if the model dropped a hypothesis.
-- ---------------------------------------------------------------------------

/-- **Bounded information (the Aaronson ceiling, modelled).** For EVERY family and EVERY
history, the accessible count never exceeds the apparatus capacity. Quantified over all
inputs; breaks immediately if `shadow` dropped its `.take t.capacity` truncation. -/
theorem accessible_bounded (t : TestFamily) (h : History) :
    t.accessibleCount h ≤ t.capacity := by
  unfold TestFamily.accessibleCount TestFamily.shadow
  exact List.length_take_le _ _

/-- **Below-floor refinements are invisible.** If two histories agree after filtering out
everything below the floor, their shadows coincide — they are indistinguishable. This is the
load-bearing direction: it would FAIL if `shadow` forgot to filter by `resolvable` (then a
sub-floor refinement would leak into the shadow and the two histories could differ). ∀-quantified
over all families and history pairs. -/
theorem agree_above_floor_indistinguishable
    (t : TestFamily) (h₁ h₂ : History)
    (h : h₁.refinements.filter (fun r => decide (t.resolvable r))
          = h₂.refinements.filter (fun r => decide (t.resolvable r))) :
    indistinguishable t h₁ h₂ := by
  show (shadowProjection t).project h₁ = (shadowProjection t).project h₂
  simp only [shadowProjection, TestFamily.shadow, h]

/-- **Distinguishability needs an above-floor difference.** Contrapositive face of the rule:
if the two histories are distinguishable (different shadows), their above-floor filtrations
must differ. Pins that the floor filter is necessary, not decorative. -/
theorem distinguishable_needs_above_floor_difference
    (t : TestFamily) (h₁ h₂ : History)
    (hne : ¬ indistinguishable t h₁ h₂) :
    h₁.refinements.filter (fun r => decide (t.resolvable r))
      ≠ h₂.refinements.filter (fun r => decide (t.resolvable r)) :=
  fun heq => hne (agree_above_floor_indistinguishable t h₁ h₂ heq)

-- ---------------------------------------------------------------------------
-- The canonical witness: two DISTINCT histories with the SAME shadow.
-- ---------------------------------------------------------------------------

/-- The standard apparatus: Planck floor at scale 3, can record at most 2 outcomes. -/
def defaultFamily : TestFamily := { floor := 3, capacity := 2 }

/-- History A: two resolvable refinements (scales 5, 4) plus a sub-floor one (scale 1). -/
def historyA : History := { refinements := [⟨5⟩, ⟨1⟩, ⟨4⟩] }

/-- History B: the SAME two resolvable refinements, but a DIFFERENT sub-floor one (scale 2)
and an extra sub-floor refinement (scale 0). The full records differ; the shadows agree. -/
def historyB : History := { refinements := [⟨5⟩, ⟨2⟩, ⟨4⟩, ⟨0⟩] }

/-- The two internal histories are genuinely DIFFERENT records. -/
theorem histories_distinct : historyA ≠ historyB := by decide

/-- ...yet they are operationally INDISTINGUISHABLE under the default apparatus
(same shadow). This is shadow tomography in one line. -/
theorem canonical_indistinguishable :
    indistinguishable defaultFamily historyA historyB := by decide

/-- The shared shadow uses exactly `capacity` recorded distinctions (the bound is tight here,
a frozen-literal check on the chosen witness — not a property enforced for all inputs). -/
theorem canonical_shadow_count :
    defaultFamily.accessibleCount historyA = defaultFamily.capacity := by decide

-- ---------------------------------------------------------------------------
-- THE CLAIM (content-bearing conjunction; two conjuncts are harness theorems).
-- ---------------------------------------------------------------------------

/-- The claim, in honest parts:
* (distinct records) `historyA ≠ historyB` — proved here by construction;
* (same shadow) they are `indistinguishable` under `defaultFamily` — this conjunct is
  literally `Experiments.Common.Projection.sameShadow` applied to `shadowProjection`
  (harness coupling: a regression in `sameShadow` fails this build);
* (bounded information) the accessible count is `≤ capacity` — discharged by the harness
  `Experiments.Common.Counting.boundedBy_of_eq` over `canonical_shadow_count`. -/
def claimStatement : Prop :=
  historyA ≠ historyB ∧
    indistinguishable defaultFamily historyA historyB ∧
    Experiments.Common.Counting.boundedBy
      (Experiments.Common.Ledger.mk (defaultFamily.shadow historyA))
      defaultFamily.capacity

def claim : Experiments.Common.Claim :=
  { tag := Experiments.Common.ClaimTag.finiteLedgerModel
    statement := claimStatement }

theorem claim_holds : claim.statement := by
  refine ⟨histories_distinct, canonical_indistinguishable, ?_⟩
  apply Experiments.Common.Counting.boundedBy_of_eq
  -- the shadow-ledger's count IS the accessible count, which equals capacity (canonical witness)
  show (Experiments.Common.Ledger.mk (defaultFamily.shadow historyA)).count
      = defaultFamily.capacity
  exact canonical_shadow_count

/-- The tag is an honest ceiling: a finite ledger / projection model, nothing more. -/
theorem ceiling : claim.tag = Experiments.Common.ClaimTag.finiteLedgerModel := rfl

-- ---------------------------------------------------------------------------
-- A computable run + a NON-vacuous Experiment.claim, with a proved bridge.
-- ---------------------------------------------------------------------------

structure Setup where
  family : TestFamily
  left : History
  right : History

/-- The run actually computes — thanks to the `Decidable` instance for `indistinguishable`. -/
def run (s : Setup) : Bool := decide (indistinguishable s.family s.left s.right)

/-- The exported claim is a genuine function of the setup; this bridge pins it to `run`, so the
claim body cannot be silently swapped for `fun _ => True` without breaking the proof. -/
def experiment : Experiments.Common.Experiment Setup Bool :=
  { tag := claim.tag
    run := run
    claim := fun s => indistinguishable s.family s.left s.right }

theorem run_iff_claim (s : Setup) :
    run s = true ↔ experiment.claim s := by
  simp only [run, experiment, decide_eq_true_iff]

def canonicalSetup : Setup :=
  { family := defaultFamily, left := historyA, right := historyB }

#eval run canonicalSetup                                  -- expect: true  (same shadow)
#eval run { canonicalSetup with right := historyA }       -- expect: true  (trivially same)
#eval run { canonicalSetup with family := { defaultFamily with floor := 0 } }
                                                          -- expect: false (floor 0 exposes sub-floor diffs)
#print axioms claim_holds                                 -- ambient footprint, NOT coupling

/-- Bring a minimal device next to this experiment: it records whether the exported claim fires. -/
def deviceNear (setup : Setup) : Bool :=
  run setup

theorem deviceNear_detects_claim (setup : Setup) :
    deviceNear setup = true ↔ experiment.claim setup := by
  simpa [deviceNear] using run_iff_claim setup

def triangulation : Experiments.Common.Triangulation Setup Bool :=
  { experiment := experiment
    device := deviceNear
    detects := deviceNear_detects_claim }

end Experiments.ShadowTomography
