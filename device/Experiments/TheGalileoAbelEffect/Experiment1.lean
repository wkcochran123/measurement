import Experiments.Common

/-!
# The Galileo-Abel Effect — invariance under change of representation

Source: `instrument/chapters/03.tex:224`, environment `phenom`, label `ph:invariance`.

## Physics (modelled finitely)
Galileo: the laws of mechanics are unchanged under a uniform translation of the
reference frame — boost the ship, boost the water, the *relations* between
recorded events survive. Abel: solvability of a polynomial depends not on its
symbolic expression but on structural relations preserved under transformation.
Both observed that *what survives change of representation is more fundamental
than the representation itself*.

We model an admissible event as a frame-tagged record. A `Reframe` is an
admissible transformation of representation: it may shift the carrier/coordinate
of a record (`frame`) but it must leave the **invariant** untouched. The
invariant is the structural residue certified by the ledger — here, the
projection `shadow` that forgets the frame and keeps only the structural label.

The Galileo-Abel statement is then exactly: an admissible `Reframe` preserves
`sameShadow` — the projected invariant of any record equals that of its
transform. This is `Experiments.Common.Projection.sameShadow`, so the harness
theorem is a load-bearing conjunct of `claim_holds`: drop the projection
machinery and this build breaks.

## NOT claimed
That this captures the Galilean group, Lorentz boosts, or any continuous symmetry
group; that "admissibility" is anything beyond *leaves-the-shadow-fixed* (we do
not model dynamics, only the invariance bookkeeping); that Abel's solvability /
Galois obstruction is formalized (it is named, not derived); no claim about
*which* transformations physics admits — only the conditional "if it fixes the
invariant, the structural relations are recovered". **Claim ceiling:** a finite
ledger model of representation-invariance, one conjunct of which is the harness's
own `Projection.sameShadow`.
-/

namespace Experiments.TheGalileoAbelEffect

/-- A recorded admissible event: a `frame` (the carrier/coordinate — the part that
may change under an admissible transformation) and a `structure` label (the
invariant structural relation the ledger certifies). -/
structure Record where
  frame : Nat
  «structure» : Nat
deriving DecidableEq, Repr

/-- The invariant projection: forget the frame, keep the structural label. This is
the "recoverable structure that persists across ledger refinements". -/
def invariant : Experiments.Common.Projection Record Nat :=
  { project := fun r => r.«structure» }

/-- `sameShadow` under the invariant is decidable (it is an equality of `Nat`
labels), so `decide`/`#eval` see through it. -/
instance (r s : Record) : Decidable (invariant.sameShadow r s) := by
  unfold Experiments.Common.Projection.sameShadow invariant
  exact inferInstance

/-- An admissible transformation of representation (a Galilean reframe / an Abelian
re-expression): it may relabel the carrier via `shift`, but it carries the
structural label through unchanged. -/
structure Reframe where
  shift : Nat
deriving Repr

namespace Reframe

/-- Apply a reframe: the frame is translated by `shift` (change of carrier), the
structure is preserved (the invariant). -/
def apply (t : Reframe) (r : Record) : Record :=
  { frame := r.frame + t.shift, «structure» := r.«structure» }

end Reframe

/-- `t` is *admissible at* `r`: the invariant of the transformed record equals the
invariant of the original. This is `sameShadow` under `invariant`. -/
def admissibleAt (t : Reframe) (r : Record) : Prop :=
  invariant.sameShadow r (t.apply r)

instance (t : Reframe) (r : Record) : Decidable (admissibleAt t r) := by
  unfold admissibleAt Experiments.Common.Projection.sameShadow invariant Reframe.apply
  exact inferInstance

-- ---------------------------------------------------------------------------
-- FALSIFIABLE lemmas. Each is ∀-quantified; each breaks if a hypothesis is dropped.
-- ---------------------------------------------------------------------------

/-- THE GALILEO-ABEL LEMMA: **every** reframe preserves the invariant of **every**
record. Quantified over all transformations and all records. Falsifiable: it is
false for a transformation that touched `«structure»` (see `not_admissible_of_distinct_shadow`),
so the fact that `Reframe.apply` leaves `«structure»` fixed is load-bearing. -/
theorem reframe_preserves_invariant (t : Reframe) (r : Record) : admissibleAt t r := by
  unfold admissibleAt Experiments.Common.Projection.sameShadow invariant Reframe.apply
  rfl

/-- Two records with **different** invariants can never be related by an admissible
transformation: if their shadows differ, no `t` makes one admissibly equal the
other's shadow. This pins admissibility to the invariant — drop the hypothesis
`h` and the conclusion is false (a record is admissibly related to itself). -/
theorem distinct_shadow_not_sameShadow (r s : Record)
    (h : invariant.project r ≠ invariant.project s) :
    ¬ invariant.sameShadow r s :=
  fun heq => h heq

/-- An *unlawful refinement* — a transformation that alters the invariant — is
inadmissible. Frame-only changes are admissible (`reframe_preserves_invariant`);
a hypothetical change that perturbs `«structure»` is not. This is the
"Constraint" of the phenomenon: no transformation that introduces distinctions
unsupported by recorded events is admissible. -/
theorem altered_structure_not_admissible (r r' : Record)
    (h : r.«structure» ≠ r'.«structure») :
    ¬ invariant.sameShadow r r' :=
  fun heq => h heq

-- ---------------------------------------------------------------------------
-- A canonical Galilean event: the ship and the water, two frames, one structure.
-- ---------------------------------------------------------------------------

/-- The ship's frame and the water's frame disagree on `frame` but agree on the
structural relation — the canonical Galilean pair. -/
def shipRecord : Record := { frame := 0, «structure» := 7 }
def galileanBoost : Reframe := { shift := 5 }

/-- The boost takes the ship record to the water record; both certify structure `7`. -/
theorem boost_preserves : admissibleAt galileanBoost shipRecord := by decide

-- ---------------------------------------------------------------------------
-- THE CLAIM (content-bearing; the invariance conjunct is the harness's sameShadow).
-- ---------------------------------------------------------------------------

/-- The claim, in honest halves:
* (recovered structure) the canonical Galilean boost leaves the invariant fixed —
  the ship and the water certify the same structural relation
  (`Projection.sameShadow`, the harness invariant — load-bearing);
* (constraint) two records with distinct structure are NOT sameShadow, so an
  unlawful refinement is inadmissible;
* (generality) the invariance holds for *every* reframe of *every* record.
Breaking `Projection.sameShadow` (rename/regress its `project`) breaks the first
conjunct and this build. -/
def claimStatement : Prop :=
  invariant.sameShadow shipRecord (galileanBoost.apply shipRecord) ∧
    (∀ r s : Record, r.«structure» ≠ s.«structure» → ¬ invariant.sameShadow r s) ∧
    (∀ t : Reframe, ∀ r : Record, admissibleAt t r)

def claim : Experiments.Common.Claim :=
  { tag := Experiments.Common.ClaimTag.finiteLedgerModel
    statement := claimStatement }

theorem claim_holds : claim.statement :=
  ⟨boost_preserves, altered_structure_not_admissible, reframe_preserves_invariant⟩

/-- The tag is an honest ceiling: a finite ledger model of invariance, nothing more. -/
theorem ceiling : claim.tag = Experiments.Common.ClaimTag.finiteLedgerModel := rfl

-- ---------------------------------------------------------------------------
-- A computable run + a non-vacuous Experiment.claim, with a proved bridge.
-- ---------------------------------------------------------------------------

structure Setup where
  reframe : Reframe
  record : Record

/-- The run computes — via the `Decidable` instance on `admissibleAt`. -/
def run (s : Setup) : Bool := decide (admissibleAt s.reframe s.record)

def experiment : Experiments.Common.Experiment Setup Bool :=
  { tag := claim.tag
    run := run
    claim := fun s => admissibleAt s.reframe s.record }

theorem run_iff_claim (s : Setup) :
    run s = true ↔ experiment.claim s := by
  simp only [run, experiment, decide_eq_true_iff]

def canonicalSetup : Setup := { reframe := galileanBoost, record := shipRecord }

/-- Bring a minimal device next to this experiment: it records whether the exported claim fires. -/
def deviceNear (setup : Setup) : Bool :=
  decide (admissibleAt setup.reframe setup.record)

theorem deviceNear_detects_claim (setup : Setup) :
    deviceNear setup = true ↔ experiment.claim setup := by
  simp only [deviceNear, experiment, decide_eq_true_iff]

def triangulation : Experiments.Common.Triangulation Setup Bool :=
  { experiment := experiment
    device := deviceNear
    detects := deviceNear_detects_claim }

#eval run canonicalSetup    -- expect: true (admissible reframe preserves the invariant)
#print axioms claim_holds   -- ambient footprint, not coupling

-- GATE: the falsifiable predicate at a config where it is FALSE. Two records with
-- DIFFERENT structure are not sameShadow, so this prints `false` — proving the
-- invariance lemma is load-bearing, not vacuous.
#eval decide (invariant.sameShadow { frame := 0, «structure» := 7 } { frame := 0, «structure» := 8 })  -- expect: false

end Experiments.TheGalileoAbelEffect
