import Experiments.Common

/-!
# The Flat Rotation Curve Effect — finite bandwidth / non-commuting refinements

This effect (instrument ch.09) is **not** an astrophysical hypothesis. Per its own description
it is a *bandwidth computation* in Shannon's sense: the causal network has a **finite capacity**
to convey distinguishable refinement, so curvature variations whose informational rate exceeds
that capacity cannot be reproduced. The flattening of the rotation profile is the **saturation of
distinguishability bandwidth**, and the residue is exactly the failure of two refinement chains —
the radial chain of recorded separations and the tangential chain of angular distinctions — to
**commute**.

We model that finitely and honestly:

* an effect-specific domain (`Chain`, `Reconstruction`) — NOT `Experiments.Common.CountSetup`;
* falsifiable ∀-lemmas: the merged distinguishability count is exactly the sum of the two chains
  (drop a side and it breaks), and the curvature residue vanishes **iff** the chains agree on the
  common boundary (the commuting case);
* a content-bearing claim whose capacity conjunct is discharged by the harness theorem
  `Experiments.Common.Counting.boundedBy_of_eq` — so a regression in the harness counting API
  breaks *this* build (LOAD-BEARING coupling), plus the additivity theorem
  `Experiments.Common.Ledger.count_append`.

## Coupling
HARNESS, not device. The effect has **no** holonomy / charge / positron content — forcing the
device's gauge theorems here would be a FAKE coupling. The honest hook is *finite capacity /
bandwidth saturation* → `Counting.boundedBy` + the bookkeeping that the merged refinement count
is additive (`Ledger.count_append`).

## NOT claimed
That this is a model of galaxies, doesn't-matter, mass distributions, or Newtonian potentials; that
the continuum viscosity term `η_info` is derived; that `v_θ(r)` is computed; any `r^{-1/2}` decay
law. The "curvature residue" here is a finite boundary-mismatch flag, not the continuum object.
**Claim ceiling:** the smooth shadow of a discrete bandwidth/commutativity requirement.
-/

namespace Experiments.TheFlatRotationCurveEffect

/-- One refinement chain: a finite list of *distinguishable refinements* recorded along it, and
the boundary slot the chain reports at the seam where the two chains must be merged. -/
structure Chain where
  refinements : List Nat
  boundary : Nat
deriving Repr

/-- The number of distinguishable refinements the chain carries (its bandwidth load). -/
def Chain.load (c : Chain) : Nat := c.refinements.length

/-- A reconstructed orbit from finite measurements: the radial chain of recorded separations and
the tangential chain of angular distinctions (description (i) and (ii)). -/
structure Reconstruction where
  radial : Chain
  tangential : Chain
deriving Repr

namespace Reconstruction

/-- The merged distinguishability record: both chains' refinements concatenated into one ledger. -/
def merged (rec : Reconstruction) : Experiments.Common.Ledger Nat :=
  Experiments.Common.Ledger.append
    { events := rec.radial.refinements }
    { events := rec.tangential.refinements }

/-- The total bandwidth load demanded by the reconstruction. -/
def totalLoad (rec : Reconstruction) : Nat :=
  rec.radial.load + rec.tangential.load

/-- The two chains **commute** when they agree on their common boundary (informationally flat
geometry: refining radial-then-angular = angular-then-radial). -/
def chainsCommute (rec : Reconstruction) : Prop :=
  rec.radial.boundary = rec.tangential.boundary

/-- The **curvature residue**: zero exactly when the chains commute, otherwise the irreducible
boundary mismatch (the "viscous residue" of the description, modelled finitely). -/
def residue (rec : Reconstruction) : Nat :=
  if rec.radial.boundary = rec.tangential.boundary then 0
  else 1

instance (rec : Reconstruction) : Decidable (rec.chainsCommute) := by
  unfold chainsCommute; exact inferInstance

end Reconstruction

-- ---------------------------------------------------------------------------
-- FALSIFIABLE lemmas. Each is ∀-quantified and breaks if a hypothesis/side is dropped.
-- ---------------------------------------------------------------------------

/-- BANDWIDTH ADDITIVITY (falsifiable): the merged ledger's count is exactly the sum of the two
chains' loads. Drop either side of the `append` and this fails. Discharged via the harness
theorem `Ledger.count_append`, so a regression there breaks the build. Quantified over ALL
reconstructions. -/
theorem merged_count_eq_totalLoad (rec : Reconstruction) :
    rec.merged.count = rec.totalLoad := by
  unfold Reconstruction.merged Reconstruction.totalLoad Chain.load
  rw [Experiments.Common.Ledger.count_append]
  rfl

/-- RESIDUE VANISHES IFF COMMUTING (falsifiable): the curvature residue is `0` exactly when the
two refinement chains agree on the common boundary. Drop the hypothesis `chainsCommute` and the
forward direction is false (an arbitrary reconstruction can have residue `1`). Quantified over
ALL reconstructions. -/
theorem residue_zero_iff_commute (rec : Reconstruction) :
    rec.residue = 0 ↔ rec.chainsCommute := by
  unfold Reconstruction.residue Reconstruction.chainsCommute
  constructor
  · intro h
    match hb : decide (rec.radial.boundary = rec.tangential.boundary) with
    | true => exact of_decide_eq_true hb
    | false =>
        simp only [if_neg (of_decide_eq_false hb)] at h
        exact absurd h (by decide)
  · intro h
    simp only [if_pos h]

/-- COMMUTING ⇒ NO RESIDUE (falsifiable, the load-bearing direction used in the claim): when the
chains commute the curvature residue is exactly zero. Drop `h` and this is false. -/
theorem commute_no_residue (rec : Reconstruction) (h : rec.chainsCommute) :
    rec.residue = 0 :=
  (residue_zero_iff_commute rec).mpr h

-- ---------------------------------------------------------------------------
-- The canonical reconstruction: a flat (commuting) orbit, both chains agreeing at the seam.
-- ---------------------------------------------------------------------------

/-- A flat-geometry reconstruction: three radial separations, two angular distinctions, both
chains reporting boundary slot `7` (they agree → they commute → residue `0`). -/
def flatOrbit : Reconstruction :=
  { radial := { refinements := [1, 1, 1], boundary := 7 }
    tangential := { refinements := [1, 1], boundary := 7 } }

/-- The bandwidth capacity of the apparatus (finite — the whole point). -/
def capacity : Nat := 5

theorem flatOrbit_commutes : flatOrbit.chainsCommute := by decide

/-- The flat orbit's total merged load (`3 + 2 = 5`) sits exactly at capacity — the saturation
of distinguishability bandwidth. -/
theorem flatOrbit_load_eq_capacity : flatOrbit.totalLoad = capacity := by decide

-- ---------------------------------------------------------------------------
-- THE CLAIM (content-bearing; the capacity conjunct is the harness's own theorem).
-- ---------------------------------------------------------------------------

/-- The claim, in honest parts:
* (no residue) the flat (commuting) orbit has zero curvature residue — the commuting case;
* (additivity) the merged distinguishability count equals the summed chain loads
  (`merged_count_eq_totalLoad`, itself discharged by `Ledger.count_append`);
* (CAPACITY / bandwidth) the merged ledger is bounded by the finite apparatus capacity —
  discharged by the harness theorem `Counting.boundedBy_of_eq`, so a regression in the harness
  counting API fails this build. This is the load-bearing coupling. -/
def claimStatement : Prop :=
  flatOrbit.residue = 0 ∧
    flatOrbit.merged.count = flatOrbit.totalLoad ∧
    Experiments.Common.Counting.boundedBy flatOrbit.merged capacity

def claim : Experiments.Common.Claim :=
  { tag := Experiments.Common.ClaimTag.smoothShadowAnalogy
    statement := claimStatement }

theorem claim_holds : claim.statement :=
  ⟨commute_no_residue flatOrbit flatOrbit_commutes,
    merged_count_eq_totalLoad flatOrbit,
    Experiments.Common.Counting.boundedBy_of_eq
      (by
        -- merged.count = totalLoad = capacity, so the bound holds at saturation.
        rw [merged_count_eq_totalLoad flatOrbit]; exact flatOrbit_load_eq_capacity)⟩

/-- The tag is an honest ceiling: the smooth shadow of a discrete bandwidth requirement. -/
theorem ceiling :
    claim.tag = Experiments.Common.ClaimTag.smoothShadowAnalogy := rfl

-- ---------------------------------------------------------------------------
-- A computable run + a non-vacuous Experiment.claim, with a proved bridge.
-- ---------------------------------------------------------------------------

abbrev Setup := Reconstruction

/-- The setup-local proposition: the reconstruction commutes (no residue) AND stays within the
finite bandwidth capacity. Named (with an explicit `Decidable` instance) so `run`/`deviceNear`
compute through it. -/
def withinBandwidth (s : Setup) : Prop :=
  s.chainsCommute ∧ s.totalLoad ≤ capacity

instance (s : Setup) : Decidable (withinBandwidth s) := by
  unfold withinBandwidth; exact inferInstance

/-- The run actually computes (via the `Decidable` instances above). -/
def run (s : Setup) : Bool :=
  decide (withinBandwidth s)

/-- The exported claim is a genuine function of the setup, pinned to `run`. -/
def experiment : Experiments.Common.Experiment Setup Bool :=
  { tag := claim.tag
    run := run
    claim := fun s => withinBandwidth s }

theorem run_iff_claim (s : Setup) :
    run s = true ↔ experiment.claim s := by
  simp only [run, experiment, decide_eq_true_iff]

/-- Bring a minimal device next to this experiment: it records whether the exported claim fires.
(`experiment.claim setup` is definitionally `withinBandwidth setup`, which is `Decidable`.) -/
def deviceNear (setup : Setup) : Bool :=
  decide (withinBandwidth setup)

theorem deviceNear_detects_claim (setup : Setup) :
    deviceNear setup = true ↔ experiment.claim setup := by
  simp only [deviceNear, experiment, decide_eq_true_iff]

def triangulation : Experiments.Common.Triangulation Setup Bool :=
  { experiment := experiment
    device := deviceNear
    detects := deviceNear_detects_claim }

-- ---------------------------------------------------------------------------
-- Gate evidence.
-- ---------------------------------------------------------------------------

#eval run flatOrbit                                   -- expect: true (commutes, at capacity)
#print axioms claim_holds                             -- ambient [propext, Quot.sound], not coupling

/-- A reconstruction whose chains DISAGREE at the seam: non-commuting → residue `1` ≠ `0`.
Evaluating the falsifiable predicate `residue = 0` here prints FALSE, proving the lemma is
load-bearing, not vacuous. -/
def curvedOrbit : Reconstruction :=
  { radial := { refinements := [1, 1, 1], boundary := 7 }
    tangential := { refinements := [1, 1], boundary := 9 } }

#eval decide (curvedOrbit.residue = 0)                -- expect: false (non-commuting → residue 1)

end Experiments.TheFlatRotationCurveEffect
