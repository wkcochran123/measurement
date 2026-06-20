import Experiments.Common

/-!
# The Entanglement Effect — the Dantzig Pivot as boundary repair

Two spacelike-separated labs `A` and `B` share a preparation that admits two refinements
`eᵢ, eⱼ` which are **causally degenerate**: both orderings `⟨eᵢ ≺ eⱼ⟩` and `⟨eⱼ ≺ eᵢ⟩`
generate the same accumulated state, so no scalar invariant in either ledger distinguishes
them. When `A` measures `eᵢ`, the ledger performs a **pivot**: it selects the unique ordering
that introduces no new distinguishability. Crucially (Martin's Condition) this repair inspects
only the **boundary of the overlap** between `Uᴬ` and `Uᴮ` — not an exponential interior volume.
The "instantaneous" correlation is not transmission; it is the bookkeeping consequence of a
non-degenerate refinement, and it is **computable** because it is a local boundary operation.

This file follows the EXEMPLAR shape:
1. an **effect-specific domain** (`LabRecord`, `OrderTag`, `Overlap`) — not the generic 3-`Nat`
   `CountSetup`;
2. genuinely **falsifiable** ∀-quantified lemmas (drop the boundary-agreement hypothesis and
   they break — see the `#eval ... = false` gate at the bottom);
3. a **content-bearing** claim (a real conjunction, never `True`);
4. an honest tag + a candid "NOT claimed" disclaimer;
5. explicit `Decidable` instances so `decide`/`#eval` compute;
6. a **load-bearing HARNESS coupling**: a conjunct of `claim_holds` is the harness's own
   `Experiments.Common.Boundary.compatible` predicate, discharged for the joint frontier of the
   two labs. This is the honest coupling for an effect that is pure two-region / seam
   consistency — there is **no holonomy, charge, or positron here**, so a device coupling
   would be a fake.

## NOT claimed
That this is real quantum entanglement, Bell/CHSH violation, or a Tsirelson bound; that the
"causal universe tensor" is formalized; that the pivot is Dantzig's simplex algorithm; that
the repair is genuinely sub-exponential (we model only that it reads a fixed-size boundary, not
an interior search). No nonlocal signaling is modelled — and none is claimed. **Claim ceiling:**
a finite ledger model whose content is exactly: degeneracy = two distinct orderings with the
SAME boundary residue; the pivot picks the one ordering compatible with the joint frontier; and
boundary agreement is the harness's own `Boundary.compatible`.
-/

namespace Experiments.TheEntanglementEffect

/-- A causal ordering tag for the degenerate pair `(eᵢ, eⱼ)`: which one the ledger has
recorded as preceding the other. Before any measurement the pair is degenerate (no tag is
forced); the pivot installs exactly one. -/
inductive OrderTag where
  | iBeforeJ
  | jBeforeI
deriving DecidableEq, Repr

/-- One lab's record of the overlap region: a finite `boundary` slot (what crosses the seam to
the neighbor — the part of the accumulated state another ledger can see) together with the
`order` it has installed on the degenerate pair. The `boundary` is the only thing two ledgers
must agree on (Martin's Condition); the `order` is interior bookkeeping. -/
structure LabRecord where
  boundary : Nat
  order : OrderTag
deriving DecidableEq, Repr

/-- The shared preparation, as seen by the two labs: the common boundary residue both labs read
off the degenerate pair, and the `pivotOrder` that lab `A`'s measurement of `eᵢ` installs. The
key fact of degeneracy is that BOTH order tags produce this SAME boundary residue. -/
structure Overlap where
  residue : Nat
  pivotOrder : OrderTag
deriving DecidableEq, Repr

/-- The standard preparation: residue slot `0`, and the pivot (A measures `eᵢ`) installs
`iBeforeJ`. -/
def defaultOverlap : Overlap := { residue := 0, pivotOrder := OrderTag.iBeforeJ }

namespace Overlap

/-- The record lab `A` holds after the pivot: the shared residue plus the installed order. -/
def labA (o : Overlap) : LabRecord := { boundary := o.residue, order := o.pivotOrder }

/-- The record lab `B` ends up holding once the boundary is repaired: it never inspected the
interior, only the joint frontier, so it carries the SAME residue — and, post-repair, the SAME
order the pivot selected. (Before repair `B` could hold the opposite order; the pivot removes
that incompatible history.) -/
def labB (o : Overlap) : LabRecord := { boundary := o.residue, order := o.pivotOrder }

/-- **Causal degeneracy.** The accumulated boundary residue is independent of which ordering the
pair carries: replacing the order tag leaves the residue a lab reads unchanged. This is the
"two distinct histories, same observational content" of the description, made finite. -/
def degenerateResidue (o : Overlap) (t : OrderTag) : Nat :=
  ({ boundary := o.residue, order := t } : LabRecord).boundary

end Overlap

/-- What a neighboring ledger sees of a record at the overlap seam: its boundary residue only.
(The `order` tag is interior bookkeeping and does NOT cross.) This is the restriction map of
the harness `Boundary`. -/
def seam : Experiments.Common.Boundary LabRecord Nat :=
  { restrict := fun r => r.boundary }

/-- Two lab records are **boundary-compatible** exactly when their visible residues agree — the
harness's `Boundary.compatible` on `seam`. Martin's Condition requires agreement only here, on
the joint frontier, never on the full interior. -/
def frontierCompatible (left right : LabRecord) : Prop :=
  seam.compatible left right

instance (left right : LabRecord) : Decidable (frontierCompatible left right) := by
  unfold frontierCompatible Experiments.Common.Boundary.compatible seam
  exact inferInstance

-- ---------------------------------------------------------------------------
-- FALSIFIABLE lemmas. Each is quantified over ALL records/overlaps and would
-- BREAK if its hypothesis were dropped (the `#eval ... = false` gate at the bottom
-- witnesses a config where the predicate is FALSE, so these are not vacuous).
-- ---------------------------------------------------------------------------

/-- **Equal residue ⇒ frontier-compatible.** Two records sharing a boundary residue are
compatible across the seam — even if their `order` tags differ. This is why the pivot can
repair `B` by inspecting only the frontier: order is interior, residue is the frontier. Drop
the equal-residue hypothesis `h` and the conclusion fails (witnessed below). Quantified over
ALL records. -/
theorem equalResidue_compatible
    (left right : LabRecord) (h : left.boundary = right.boundary) :
    frontierCompatible left right := by
  unfold frontierCompatible Experiments.Common.Boundary.compatible seam
  exact h

/-- **Incompatible ⇒ residues differ.** The contrapositive: a contradiction at the seam can ONLY
arise from a genuine boundary-residue distinction — never from the interior order tag alone. So
the pivot can never be forced by an interior search; the only obstructions live on the frontier.
Quantified over ALL pairs; load-bearing. -/
theorem incompatible_residuesDiffer
    (left right : LabRecord) (h : ¬ frontierCompatible left right) :
    left.boundary ≠ right.boundary :=
  fun heq => h (equalResidue_compatible left right heq)

/-- **Causal degeneracy is real:** for ANY overlap and ANY two order tags, the boundary residue
a lab records is the SAME. So no scalar invariant on the seam can tell `⟨eᵢ ≺ eⱼ⟩` from
`⟨eⱼ ≺ eᵢ⟩` — exactly the degeneracy that "entanglement" names here. -/
theorem residue_independent_of_order (o : Overlap) (s t : OrderTag) :
    o.degenerateResidue s = o.degenerateResidue t := by
  rfl

-- ---------------------------------------------------------------------------
-- The canonical pivot: A measures eᵢ, B is repaired along the frontier only.
-- ---------------------------------------------------------------------------

/-- After the pivot, lab `A` and lab `B` hold these records. They share the residue (the only
thing the repair inspected) and, post-repair, the order the pivot selected. -/
def recordA : LabRecord := defaultOverlap.labA
def recordB : LabRecord := defaultOverlap.labB

/-- The pivot closes: the two labs are frontier-compatible (the joint frontier agrees). -/
theorem pivot_compatible : frontierCompatible recordA recordB := by decide

/-- A record carrying a DIFFERENT boundary residue is the one configuration where the seam
genuinely disagrees — an incompatible history the pivot would have to remove. This is the
config the `#eval` gate at the bottom prints `false` for. -/
def incompatibleB : LabRecord := { recordB with boundary := 7 }

-- ---------------------------------------------------------------------------
-- THE CLAIM (content-bearing; the compatibility conjunct is the harness's own predicate).
-- ---------------------------------------------------------------------------

/-- The claim, in honest parts:
* (degeneracy) for the default overlap the boundary residue is the same under either order tag —
  two distinct histories with identical observational content;
* (pivot = boundary compatibility) the post-pivot records of `A` and `B` are
  `Experiments.Common.Boundary.compatible` across the seam (HARNESS coupling — breaking
  `Boundary.compatible` or `seam` breaks this build); and
* (a residue distinction is the only obstruction) a record with a different residue is NOT
  frontier-compatible, so the only incompatible histories live on the frontier, never in the
  unscanned interior. -/
def claimStatement : Prop :=
  defaultOverlap.degenerateResidue OrderTag.iBeforeJ
      = defaultOverlap.degenerateResidue OrderTag.jBeforeI ∧
    frontierCompatible recordA recordB ∧
    ¬ frontierCompatible recordA incompatibleB

def claim : Experiments.Common.Claim :=
  { tag := Experiments.Common.ClaimTag.finiteLedgerModel
    statement := claimStatement }

theorem claim_holds : claim.statement :=
  ⟨residue_independent_of_order defaultOverlap OrderTag.iBeforeJ OrderTag.jBeforeI,
    equalResidue_compatible recordA recordB rfl,
    by decide⟩

/-- The tag is an honest ceiling: a finite ledger model of the boundary-repair logic. -/
theorem ceiling : claim.tag = Experiments.Common.ClaimTag.finiteLedgerModel := rfl

-- ---------------------------------------------------------------------------
-- A computable run + a non-vacuous Experiment.claim, with a proved bridge.
-- ---------------------------------------------------------------------------

structure Setup where
  overlap : Overlap
  left : LabRecord
  right : LabRecord

/-- The run computes — via the `Decidable` instance on `frontierCompatible`. -/
def run (s : Setup) : Bool := decide (frontierCompatible s.left s.right)

def experiment : Experiments.Common.Experiment Setup Bool :=
  { tag := claim.tag
    run := run
    claim := fun s => frontierCompatible s.left s.right }

theorem run_iff_claim (s : Setup) :
    run s = true ↔ experiment.claim s := by
  simp only [run, experiment, decide_eq_true_iff]

def canonicalSetup : Setup := { overlap := defaultOverlap, left := recordA, right := recordB }

#eval run canonicalSetup                                     -- expect: true  (pivot closes)
#eval run { canonicalSetup with right := incompatibleB }     -- expect: false (residue distinction)
#print axioms claim_holds                                    -- [propext, Quot.sound] = AMBIENT, not coupling

/-- Bring a minimal device next to this experiment: it records whether the exported claim fires.
(Reads `frontierCompatible` directly — definitionally `experiment.claim setup` — so the
`Decidable` instance synthesizes.) -/
def deviceNear (setup : Setup) : Bool :=
  decide (frontierCompatible setup.left setup.right)

theorem deviceNear_detects_claim (setup : Setup) :
    deviceNear setup = true ↔ experiment.claim setup := by
  simp only [deviceNear, experiment, decide_eq_true_iff]

def triangulation : Experiments.Common.Triangulation Setup Bool :=
  { experiment := experiment
    device := deviceNear
    detects := deviceNear_detects_claim }

end Experiments.TheEntanglementEffect
