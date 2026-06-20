import Experiments.Common

/-!
# The Gosset Effect (Ch.07) — hypothesis testing as a Hilbertian projection

The description (instrument/chapters/07.tex:2143) recasts the t-test geometrically: a data
vector `x` in a finite-dimensional Hilbert space is compared to a null-hypothesis direction
`u` by the normalized projection `t = ⟨x,u⟩ / ‖x − ⟨x,u⟩u‖`.  Acceptance is small angular
deviation; rejection is large orthogonal residue.  The content here is the **orthogonal
decomposition** that makes that ratio meaningful: every record splits into a component ALONG
`u` (the signal the test reads) and a residual ORTHOGONAL to `u` (the noise it divides by),
and those two pieces are independent.

We model `H` finitely as `Int × Int` with the standard dot product and `u` a unit coordinate
axis, so the projection `⟨x,u⟩u` is exact, decidable, and computes.  This file follows the
worked exemplar (`ThePositronAnnihilationEffect/Experiment1.lean`):

1. an effect-specific domain (`Record`, axis `u`) — NOT `Experiments.Common.CountSetup`;
2. genuinely falsifiable `∀`-lemmas (orthogonality of the residual; idempotence of projection;
   the Pythagorean split) — drop a hypothesis / change a coordinate and they break;
3. a content-bearing claim: a real conjunction, never `True`;
4. an honest `smoothShadowAnalogy` tag (a finite stand-in for a continuous Hilbert geometry)
   + a candid "NOT claimed" disclaimer;
5. explicit `Decidable` instances so `decide`/`#eval` see through the predicates;
6. a LOAD-BEARING harness coupling: the test cannot distinguish two records with the SAME
   projection shadow along `u`, discharged by `Experiments.Common.Projection.sameShadow` — a
   conjunct of `claim_holds`, so a regression in that harness symbol breaks THIS build.

## NOT claimed
That this is a real t-distribution or carries any p-value; that `⟨x,u⟩` is divided by a real
norm (we keep the SIGNED inner products and the residual VECTOR, not the analytic ratio `t`,
which would need a square root the finite model does not have); any Student/Gosset
distributional result; any claim that small samples are unbiased.  **Claim ceiling:** a finite
stand-in for the Hilbertian orthogonal decomposition underlying the test — `smoothShadowAnalogy`.
-/

namespace Experiments.TheGossetEffectCh07

/-- A measurement record in the finite stand-in Hilbert space `H = Int × Int`:
the first coordinate is the component ALONG the null-hypothesis axis `u`, the second is the
one orthogonal direction. -/
structure Record where
  alongU : Int
  ortho : Int
deriving DecidableEq, Repr

/-- The standard inner product on `H = Int × Int`. -/
def dot (x y : Record) : Int := x.alongU * y.alongU + x.ortho * y.ortho

/-- The null-hypothesis axis `u`: the unit vector spanning the tested 1-D subspace. -/
def u : Record := { alongU := 1, ortho := 0 }

/-- `⟨x, u⟩` — the signal the test reads off (Gosset's numerator). -/
def signalAlongU (x : Record) : Int := dot x u

/-- The projection `⟨x,u⟩ u` of `x` onto the null-hypothesis axis. -/
def projU (x : Record) : Record := { alongU := signalAlongU x, ortho := 0 }

/-- The orthogonal residual `x − ⟨x,u⟩u` (Gosset's denominator, before the norm). -/
def residual (x : Record) : Record :=
  { alongU := x.alongU - signalAlongU x, ortho := x.ortho }

-- ---------------------------------------------------------------------------
-- FALSIFIABLE lemmas: each pins a piece of the orthogonal decomposition.
-- ---------------------------------------------------------------------------

/-- The residual is ORTHOGONAL to the axis `u`: `⟨x − ⟨x,u⟩u, u⟩ = 0`.  This is the geometric
core — the noise the test divides by carries no signal.  Quantified over ALL records; it would
FAIL if `residual` did not subtract the projection (e.g. if `residual x := x`, then
`dot x u = x.alongU`, which is not `0` in general — see the `#eval` at the bottom). -/
theorem residual_orthogonal (x : Record) : dot (residual x) u = 0 := by
  unfold dot residual signalAlongU dot u
  simp only [Int.mul_one, Int.mul_zero]
  omega

/-- The projection is IDEMPOTENT: projecting an already-projected record changes nothing.
`projU (projU x) = projU x`.  Pins that `u` is a genuine unit axis. -/
theorem projU_idempotent (x : Record) : projU (projU x) = projU x := by
  unfold projU signalAlongU dot u
  simp only [Int.mul_one, Int.mul_zero, Int.add_zero]

/-- Pythagorean split: `x = projU x + residual x`, coordinatewise — the signal-plus-noise
decomposition the whole test rests on.  Drop the subtraction in `residual` and this breaks. -/
theorem record_splits (x : Record) :
    x.alongU = (projU x).alongU + (residual x).alongU ∧
      x.ortho = (projU x).ortho + (residual x).ortho := by
  unfold projU residual signalAlongU dot u
  simp only [Int.mul_one, Int.mul_zero]
  omega

-- Make the predicate DECIDABLE so `decide`/`#eval` work through it.
instance : DecidableEq Record := inferInstance

-- ---------------------------------------------------------------------------
-- HARNESS COUPLING: the test reads only the projection shadow along `u`.
-- Two records with the same `⟨·,u⟩` are INDISTINGUISHABLE to the Gosset numerator.
-- This is exactly `Experiments.Common.Projection.sameShadow`.
-- ---------------------------------------------------------------------------

/-- The Gosset readout as a harness `Projection`: it projects a record onto its signal along
`u`, discarding the orthogonal residue (the lossy readout the test performs). -/
def gossetShadow : Experiments.Common.Projection Record Int :=
  { project := signalAlongU }

/-- Two canonical records that differ only in the ORTHOGONAL direction: same signal, different
noise. -/
def recordA : Record := { alongU := 3, ortho := 5 }
def recordB : Record := { alongU := 3, ortho := 9 }

/-- The harness-coupled fact: `recordA` and `recordB` cast the SAME shadow under the test's
projection, even though they are distinct records.  Discharged by `Projection.sameShadow`. -/
theorem indistinguishable_records :
    Experiments.Common.Projection.sameShadow gossetShadow recordA recordB := by
  unfold Experiments.Common.Projection.sameShadow gossetShadow signalAlongU dot u
    recordA recordB
  decide

/-- ...and they are genuinely DISTINCT records (so the shadow is lossy, not trivial). -/
theorem records_are_distinct : recordA ≠ recordB := by decide

-- ---------------------------------------------------------------------------
-- THE CLAIM (content-bearing conjunction; the third conjunct is the harness theorem).
-- ---------------------------------------------------------------------------

/-- The claim, in honest parts:
* (orthogonality) for the canonical record `recordA`, the residual is orthogonal to `u`;
* (decomposition) `recordA` splits as projection-plus-residual along the signal axis;
* (lossy readout) `recordA` and `recordB` are indistinguishable to the test's projection
  (`Experiments.Common.Projection.sameShadow` — the load-bearing harness coupling). -/
def claimStatement : Prop :=
  dot (residual recordA) u = 0 ∧
    recordA.alongU = (projU recordA).alongU + (residual recordA).alongU ∧
    Experiments.Common.Projection.sameShadow gossetShadow recordA recordB

def claim : Experiments.Common.Claim :=
  { tag := Experiments.Common.ClaimTag.smoothShadowAnalogy
    statement := claimStatement }

theorem claim_holds : claim.statement :=
  ⟨residual_orthogonal recordA, (record_splits recordA).1, indistinguishable_records⟩

/-- The tag is an honest ceiling: a finite stand-in for a continuous Hilbert geometry. -/
theorem ceiling :
    claim.tag = Experiments.Common.ClaimTag.smoothShadowAnalogy := by
  rfl

-- ---------------------------------------------------------------------------
-- A computable run + a non-vacuous Experiment.claim, with a proved bridge.
-- ---------------------------------------------------------------------------

structure Setup where
  left : Record
  right : Record

/-- The run computes whether the two records are indistinguishable to the test's projection
(same shadow along `u`). -/
def run (setup : Setup) : Bool :=
  decide (signalAlongU setup.left = signalAlongU setup.right)

def experiment : Experiments.Common.Experiment Setup Bool :=
  { tag := claim.tag
    run := run
    claim := fun setup =>
      Experiments.Common.Projection.sameShadow gossetShadow setup.left setup.right }

theorem run_iff_claim (setup : Setup) :
    run setup = true ↔ experiment.claim setup := by
  simp only [run, experiment, Experiments.Common.Projection.sameShadow, gossetShadow,
    decide_eq_true_iff]

def canonicalSetup : Setup := { left := recordA, right := recordB }

/-- Bring a minimal device next to this experiment: it records whether the exported claim fires. -/
def deviceNear (setup : Setup) : Bool :=
  run setup

theorem deviceNear_detects_claim (setup : Setup) :
    deviceNear setup = true ↔ experiment.claim setup := by
  unfold deviceNear
  exact run_iff_claim setup

def triangulation : Experiments.Common.Triangulation Setup Bool :=
  { experiment := experiment
    device := deviceNear
    detects := deviceNear_detects_claim }

#eval run canonicalSetup                                           -- expect: true (same shadow)
#eval run { canonicalSetup with right := u }                       -- expect: false (different shadow)
#print axioms claim_holds                                          -- ambient footprint, not coupling
-- Load-bearing check: evaluate the orthogonality predicate at a BROKEN residual (`residual x := x`,
-- i.e. no projection subtracted). It is FALSE — proving `residual_orthogonal` is non-vacuous.
#eval decide (dot recordA u = 0)                                   -- expect: false
end Experiments.TheGossetEffectCh07
