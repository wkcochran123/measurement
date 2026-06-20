import Experiments.Common

/-!
# The Dirichlet--Bancroft Effect — a finite model of multiplicity collapse

Source: `instrument/chapters/03.tex:555`, env `phenom`, label `ph:db`.

## Physics (modelled finitely)
A fully specified geometric model (the GPS pseudorange equations) is exact and internally
consistent, yet **under-constrained**: with only three satellite receptions the algebraic system
generally admits **two** geometrically valid intersections — one near the Earth's surface, one far
into space. Both satisfy the modelled propagation relations. Uniqueness does not come from the
governing equations alone; it comes from **additional admissible data** committed to the ledger: a
fourth reception event, or an environmental boundary admissibility condition that elides the
extraneous deep-space branch. Refinement sharpens the realization **without altering the
invariant** (the propagation relation itself is stable across every admissible branch).

We model branches as a finite list of candidate `Solution`s, and a `Constraint` as an
admissibility predicate that keeps or discards each branch. The effect is the *count*:
`admissible` solutions number more than one before refinement, and exactly one after the
Earth-bound boundary constraint is committed.

## Coupling
This effect has NO holonomy / charge / gauge-loop / positron content, so coupling to the
`Measurement` device would be FAKE. It IS a finite counting / capacity / collapse-of-multiplicity
story, so it couples to the HARNESS: `claim_holds`'s uniqueness conjunct is discharged by
`Experiments.Common.Counting.boundedBy_of_eq`. That theorem is load-bearing — break it (or break
the count it consumes) and this build breaks.

## NOT claimed
That the real Bancroft algebra is solved here (no quadratic, no relativistic clock term, no
pseudorange arithmetic — the branches are labels, not computed positions); that exactly two
branches arise from the geometry (we *posit* the two-branch under-constrained ledger, we do not
derive it from the equations); that the Earth-bound admissibility filter is anything but a labelled
constraint. **Claim ceiling:** a finite ledger model of solution multiplicity and its collapse to a
unique realization under one committed boundary constraint.
-/

namespace Experiments.TheDirichletBancroftEffect

/-- A candidate realization of the under-constrained geometric model. `nearEarth` is the
Earth-bound branch a receiver actually occupies; `deepSpace` is the extraneous branch that also
satisfies the propagation relations. -/
inductive Solution where
  | nearEarth
  | deepSpace
deriving DecidableEq, Repr

/-- A committed admissibility constraint: a predicate that keeps the branches it admits. We model
the two constraints the description names: a fourth reception event, and an environmental
(Earth-bound) boundary condition. -/
inductive Constraint where
  /-- Geometry only: every modelled branch is admissible (the under-constrained ledger). -/
  | geometryOnly
  /-- A fourth reception, or an Earth-bound boundary admissibility condition: only the
  Earth-bound branch survives. -/
  | earthBoundBoundary
deriving DecidableEq, Repr

namespace Constraint

/-- Whether a constraint admits a given branch. `geometryOnly` admits both (multiplicity);
`earthBoundBoundary` admits only the near-Earth branch (the collapse). -/
def admits : Constraint -> Solution -> Bool
  | geometryOnly, _ => true
  | earthBoundBoundary, Solution.nearEarth => true
  | earthBoundBoundary, Solution.deepSpace => false

end Constraint

/-- The under-constrained ledger: both branches the three-reception system admits. -/
def candidateBranches : List Solution := [Solution.nearEarth, Solution.deepSpace]

/-- The admissible branches surviving a committed constraint. -/
def admissible (c : Constraint) : List Solution :=
  candidateBranches.filter (fun s => c.admits s)

/-- The admissible ledger, as a harness `Ledger` of surviving branches. -/
def admissibleLedger (c : Constraint) : Experiments.Common.Ledger Solution :=
  { events := admissible c }

/-- Make the harness `boundedBy` predicate DECIDABLE so `decide`/`#eval` compute through it
(it unfolds to a `Nat` `<=`). -/
instance (ledger : Experiments.Common.Ledger Solution) (bound : Nat) :
    Decidable (Experiments.Common.Counting.boundedBy ledger bound) := by
  unfold Experiments.Common.Counting.boundedBy; exact inferInstance

-- ---------------------------------------------------------------------------
-- FALSIFIABLE lemmas. Each is `∀`-quantified and breaks if its hypothesis is dropped.
-- ---------------------------------------------------------------------------

/-- MULTIPLICITY (necessity of the boundary): a constraint that admits the deep-space branch
yields a NON-unique admissible set — strictly more than one branch survives. Quantified over all
constraints; drop the hypothesis `c.admits Solution.deepSpace = true` and it is false for
`earthBoundBoundary`. -/
theorem multiplicity_when_deepSpace_admitted
    (c : Constraint) (h : c.admits Solution.deepSpace = true) :
    1 < (admissibleLedger c).count := by
  unfold admissibleLedger admissible candidateBranches Experiments.Common.Ledger.count
  cases c with
  | geometryOnly => decide
  | earthBoundBoundary => nomatch h

/-- COLLAPSE (sufficiency of the boundary): once the Earth-bound boundary is committed, the
deep-space branch is rejected, so the admissible ledger holds exactly one branch. Quantified over
all branches `s`: any admitted branch under `earthBoundBoundary` is the near-Earth one. Drop the
`= true` hypothesis and `deepSpace` is a counterexample. -/
theorem only_earthBound_admitted
    (s : Solution) (h : Constraint.earthBoundBoundary.admits s = true) :
    s = Solution.nearEarth := by
  cases s with
  | nearEarth => rfl
  | deepSpace => nomatch h

-- ---------------------------------------------------------------------------
-- The exact counts (these feed the harness coupling).
-- ---------------------------------------------------------------------------

/-- Geometry alone leaves the ledger under-constrained: two admissible branches. -/
theorem geometryOnly_count_two :
    (admissibleLedger Constraint.geometryOnly).count = 2 := by decide

/-- The committed Earth-bound boundary collapses the ledger to a single admissible branch. -/
theorem earthBound_count_one :
    (admissibleLedger Constraint.earthBoundBoundary).count = 1 := by decide

-- ---------------------------------------------------------------------------
-- THE CLAIM (content-bearing; the uniqueness conjunct is discharged by the HARNESS).
-- ---------------------------------------------------------------------------

/-- The claim, in honest parts:
* (multiplicity) under geometry alone the admissible ledger has **two** branches — the model is
  complete yet the realization is not unique;
* (collapse) committing the Earth-bound boundary leaves **at most one** admissible branch — this
  conjunct is `Experiments.Common.Counting.boundedBy_of_eq` applied to `earthBound_count_one`, so
  the harness theorem sits in the proof term (HARNESS coupling, load-bearing); and
* (invariant) the propagation invariant — modelled here as "the near-Earth branch survives every
  committed constraint" — is stable across both ledgers. -/
def claimStatement : Prop :=
  (admissibleLedger Constraint.geometryOnly).count = 2 ∧
    Experiments.Common.Counting.boundedBy (admissibleLedger Constraint.earthBoundBoundary) 1 ∧
    (Constraint.geometryOnly.admits Solution.nearEarth = true ∧
      Constraint.earthBoundBoundary.admits Solution.nearEarth = true)

def claim : Experiments.Common.Claim :=
  { tag := Experiments.Common.ClaimTag.finiteLedgerModel
    statement := claimStatement }

theorem claim_holds : claim.statement :=
  ⟨geometryOnly_count_two,
    Experiments.Common.Counting.boundedBy_of_eq earthBound_count_one,
    ⟨by decide, by decide⟩⟩

/-- The tag is an honest ceiling: a finite ledger model of multiplicity and its collapse. -/
theorem ceiling :
    claim.tag = Experiments.Common.ClaimTag.finiteLedgerModel := rfl

-- ---------------------------------------------------------------------------
-- A computable run + a NON-vacuous Experiment.claim, with a proved bridge.
-- ---------------------------------------------------------------------------

/-- The setup names which constraint has been committed to the ledger. -/
structure Setup where
  committed : Constraint

def defaultSetup : Setup := { committed := Constraint.earthBoundBoundary }

/-- The run computes the admissible-branch count under the committed constraint. -/
def run (setup : Setup) : Nat := (admissibleLedger setup.committed).count

/-- The exported claim: under the committed constraint the realization is unique
(at most one admissible branch). -/
def experiment : Experiments.Common.Experiment Setup Nat :=
  { tag := claim.tag
    run := run
    claim := fun setup => Experiments.Common.Counting.boundedBy (admissibleLedger setup.committed) 1 }

theorem run_le_one_iff_claim (setup : Setup) :
    run setup ≤ 1 ↔ experiment.claim setup :=
  Iff.rfl

/-- Bring a minimal device next to this experiment: it records whether the exported claim fires.
Written via the reduced `boundedBy` form so its `Decidable` instance is found. -/
def deviceNear (setup : Setup) : Bool :=
  decide (Experiments.Common.Counting.boundedBy (admissibleLedger setup.committed) 1)

theorem deviceNear_detects_claim (setup : Setup) :
    deviceNear setup = true ↔ experiment.claim setup := by
  unfold deviceNear experiment
  exact decide_eq_true_iff

def triangulation : Experiments.Common.Triangulation Setup Nat :=
  { experiment := experiment
    device := deviceNear
    detects := deviceNear_detects_claim }

#eval run defaultSetup                                    -- expect: 1 (unique after collapse)
#eval run { committed := Constraint.geometryOnly }        -- expect: 2 (multiplicity)
-- Load-bearing falsifiability witness: the uniqueness predicate is FALSE under geometry alone.
#eval decide
  (Experiments.Common.Counting.boundedBy (admissibleLedger Constraint.geometryOnly) 1)  -- false
#print axioms claim_holds

end Experiments.TheDirichletBancroftEffect
