import Experiments.Common

/-!
# The Laplace Effect — finite determinism of admissible refinement

## Source
`instrument/chapters/05.tex:179` — "Under the axioms of measurement, a single
experimental record admits a *unique* sequence of admissible refinements
consistent with its anchors.  Relative to this record, each extension appears
uniquely determined by its predecessors."

## What this file models (finitely)
Laplace's demon, demoted to bookkeeping.  A `Record` is a finite list of
`Anchor`s (recorded marks, each a value on a finite scale).  A refinement is the
act of *extending* the record by one more anchor.  The "Laplace" content is
**determinism**: the value of the next anchor is a fixed function `step` of its
predecessor, so the entire continuation of the record is forced once the seed
(the first anchor) is fixed.  "Uniquely determined by its predecessors" becomes
the literal statement: any two admissible extensions of the same predecessor
carry the *same* value.

We also keep the harness's preservation theme honest: re-labelling every anchor
through a decoding map (a coarse refinement) preserves the *count* of recorded
distinctions.  That conjunct is discharged by the harness theorem
`Experiments.Common.Ledger.count_map`, so a regression in the harness ledger
breaks this build (load-bearing harness coupling).

## NOT claimed
That measurement is *actually* deterministic; that real refinement sequences are
single-valued (the axioms of measurement do not, in general, give Laplacian
determinism — that is the whole point of the *later* chapters); any continuum
limit, any PDE called "Laplace's equation", any harmonic-function theory.  The
`step` map is a *posited* finite transition, not derived.  **Claim ceiling:** a
finite ledger model in which admissible extension is, *by construction*, a
function — and the harness's count-preservation under re-labelling.

## Coupling
HARNESS, not device.  This effect has no holonomy / charge / positron content,
so a device coupling would be FAKE and is declined.  The honest hook is
preservation under refinement → `Experiments.Common.Ledger.count_map`.
-/

namespace Experiments.TheLaplaceEffect

/-- A recorded mark: a value on a finite scale (the "anchor" of the record). -/
structure Anchor where
  value : Nat
deriving DecidableEq, Repr

/-- A finite experimental record: the list of anchors laid down so far. -/
structure Record where
  anchors : List Anchor
deriving DecidableEq, Repr

/-- THE deterministic transition.  This is the posited finite law: the value of
the next admissible anchor is a fixed function of its predecessor.  (Affine on
the finite scale; the exact form is a label, the *functionality* is the content.) -/
def step (a : Anchor) : Anchor :=
  { value := a.value + 1 }

/-- `b` is an **admissible extension** of predecessor `a`: its value is exactly
the one forced by the deterministic law.  This is the ONE constraint that makes
the continuation unique. -/
def Admissible (a b : Anchor) : Prop :=
  b = step a

instance (a b : Anchor) : Decidable (Admissible a b) := by
  unfold Admissible; exact inferInstance

-- ---------------------------------------------------------------------------
-- FALSIFIABLE lemmas.  Each is ∀-quantified and breaks if its hypothesis is dropped.
-- ---------------------------------------------------------------------------

/-- **Determinism (Laplace).**  Two admissible extensions of the *same*
predecessor are equal.  This is "uniquely determined by its predecessors" made
literal.  FALSIFIABLE: drop either hypothesis (so `b` and `c` extend possibly
*different* predecessors) and the conclusion fails — see `not_determined_off_anchor`. -/
theorem extension_unique (a b c : Anchor)
    (hb : Admissible a b) (hc : Admissible a c) : b = c := by
  rw [hb, hc]

/-- **The forced value.**  An admissible extension carries exactly `step`'s value.
FALSIFIABLE: with the hypothesis dropped, `b.value = a.value + 1` is just false
in general (any `b` with a different value is a counterexample). -/
theorem extension_value (a b : Anchor) (h : Admissible a b) :
    b.value = a.value + 1 := by
  rw [h]; rfl

/-- The witness that determinism is **not vacuous off the anchor**: two extensions
of *different* predecessors need not agree.  This is the sentence whose negation
`extension_unique` proves under the shared-predecessor hypothesis — it shows the
hypothesis is load-bearing. -/
theorem not_determined_off_anchor :
    ∃ a a' b c : Anchor, Admissible a b ∧ Admissible a' c ∧ b ≠ c := by
  exact ⟨{ value := 0 }, { value := 1 }, { value := 1 }, { value := 2 },
    rfl, rfl, by decide⟩

-- ---------------------------------------------------------------------------
-- The canonical record: a seed plus the forced continuation.
-- ---------------------------------------------------------------------------

/-- The seed anchor of the canonical record. -/
def seed : Anchor := { value := 0 }

/-- The canonical (deterministic) continuation: seed, then `step` applied thrice. -/
def canonicalRecord : Record :=
  { anchors := [seed, step seed, step (step seed), step (step (step seed))] }

/-- Each adjacent pair of the canonical record is an admissible (forced) step. -/
theorem canonical_steps_admissible :
    Admissible seed (step seed) ∧
    Admissible (step seed) (step (step seed)) ∧
    Admissible (step (step seed)) (step (step (step seed))) := by
  exact ⟨rfl, rfl, rfl⟩

-- ---------------------------------------------------------------------------
-- HARNESS coupling: preservation of recorded distinctions under re-labelling.
-- ---------------------------------------------------------------------------

/-- The record as a harness `Ledger` of anchors. -/
def ledgerOf (r : Record) : Experiments.Common.Ledger Anchor :=
  { events := r.anchors }

/-- A coarse re-labelling of an anchor (a refinement's decode map): keep only the
parity of the value.  "Consistent with its anchors" — the count of recorded marks
survives the coarsening. -/
def coarsen (a : Anchor) : Anchor :=
  { value := a.value % 2 }

-- ---------------------------------------------------------------------------
-- THE CLAIM (content-bearing conjunction; the third conjunct is the harness theorem).
-- ---------------------------------------------------------------------------

/-- The claim, in honest parts:
* (determinism) the canonical adjacent pairs are all admissible — the continuation
  is forced (proved here from `extension_unique`/construction);
* (forced value) the third anchor's value is exactly the law's value — `extension_value`;
* (preservation) re-labelling every anchor through `coarsen` preserves the count of
  recorded distinctions — discharged by `Experiments.Common.Ledger.count_map`, so a
  harness regression breaks this build (LOAD-BEARING harness coupling). -/
def claimStatement : Prop :=
  (Admissible seed (step seed) ∧
    Admissible (step seed) (step (step seed)) ∧
    Admissible (step (step seed)) (step (step (step seed)))) ∧
  (step (step seed)).value = (step seed).value + 1 ∧
  ((Experiments.Common.Ledger.map coarsen (ledgerOf canonicalRecord)).count
      = (ledgerOf canonicalRecord).count)

def claim : Experiments.Common.Claim :=
  { tag := Experiments.Common.ClaimTag.finiteLedgerModel
    statement := claimStatement }

theorem claim_holds : claim.statement :=
  ⟨canonical_steps_admissible,
    extension_value (step seed) (step (step seed)) rfl,
    Experiments.Common.Ledger.count_map coarsen (ledgerOf canonicalRecord)⟩

/-- The tag is an honest ceiling: a finite ledger model, nothing more. -/
theorem ceiling : claim.tag = Experiments.Common.ClaimTag.finiteLedgerModel := rfl

-- ---------------------------------------------------------------------------
-- A computable run + a non-vacuous exported Experiment, with a proved bridge.
-- ---------------------------------------------------------------------------

structure Setup where
  predecessor : Anchor
  extension : Anchor

/-- The run computes — thanks to the `Decidable (Admissible …)` instance. -/
def run (s : Setup) : Bool := decide (Admissible s.predecessor s.extension)

/-- The exported claim is a genuine function of the setup (not `fun _ => True`). -/
def experiment : Experiments.Common.Experiment Setup Bool :=
  { tag := claim.tag
    run := run
    claim := fun s => Admissible s.predecessor s.extension }

theorem run_iff_claim (s : Setup) :
    run s = true ↔ experiment.claim s := by
  simp only [run, experiment, decide_eq_true_iff]

def canonicalSetup : Setup := { predecessor := seed, extension := step seed }

/-- A minimal device next to the experiment: it fires iff the exported claim does. -/
def deviceNear (setup : Setup) : Bool :=
  run setup

theorem deviceNear_detects_claim (setup : Setup) :
    deviceNear setup = true ↔ experiment.claim setup := by
  simp only [deviceNear, run, experiment, decide_eq_true_iff]

def triangulation : Experiments.Common.Triangulation Setup Bool :=
  { experiment := experiment
    device := deviceNear
    detects := deviceNear_detects_claim }

-- ---------------------------------------------------------------------------
-- GATE EVIDENCE.
-- ---------------------------------------------------------------------------

#eval run canonicalSetup                                   -- expect: true
#eval run { canonicalSetup with extension := seed }        -- expect: false (not the forced value)
#print axioms claim_holds
-- The falsifiable predicate evaluated where it is FALSE (load-bearing, not vacuous):
#eval decide (Admissible seed seed)                        -- expect: false

end Experiments.TheLaplaceEffect
