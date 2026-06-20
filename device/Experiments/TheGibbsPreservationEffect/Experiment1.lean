import Experiments.Common

/-!
# The Gibbs Preservation Effect — content-bearing test (harness-coupled)

Source description: `instrument/chapters/06.tex:1139` (`ph:gibbs-null`).

## Physics (modelled finitely)
A discrete causal ledger is **projected into a smooth shadow**.  The smoothing operator has a
nontrivial **null space**: it cannot tell apart two ledgers that differ only by a feature it cannot
represent.  Here the ledger is a finite signal of integer samples and the smoothing operator is a
(lossy) **block sum** that maps a signal to its coarse shadow by summing consecutive pairs.  A
*sharp feature* is a sample pattern that lives in the **null space** of this operator: added
componentwise to a signal it changes the signal but leaves the shadow fixed, because within each
block the feature contributes `(+h) + (-h) = 0`.  That is the Gibbs preservation statement made
finite: the shape (the feature) is *not destroyed* by smoothing — it is **stored, orthogonal to
the shadow**.

## Coupling (HARNESS — `Experiments.Common.Projection.sameShadow`)
This is a coarse-graining / lossy-readout effect, so the honest hook is `Projection.sameShadow`.
`smooth` is wrapped as a `Projection Signal Signal` and the LOAD-BEARING conjunct of the claim is
`Projection.sameShadow smoothing baseSignal featuredSignal`: the projected shadows of the plain
signal and the feature-perturbed signal coincide — which IS the null-space-localization statement.
That conjunct is `claimStatement`'s third component and `claim_holds` discharges it through the
harness `Projection.sameShadow` definition; break the harness path and this build breaks.

## NOT claimed
That this is the real Gibbs phenomenon, Fourier series, or the overshoot constant (≈ 0.0895).
No convergence claim, no continuum limit, no orthonormal basis, no actual smoothing kernel beyond a
toy block sum.  `smooth` is a *labelled* stand-in for an admissible projection — not derived.  The
"null space" here is the kernel of one concrete toy operator, not the kernel of a real
band-limiting projector.
**Claim ceiling:** a finite stand-in (`smoothShadowAnalogy`) for the continuous statement, whose
shadow-collapse conjunct is the harness's own `Projection.sameShadow`.
-/

namespace Experiments.TheGibbsPreservationEffect

/-- A finite discrete signal: a list of integer samples (the causal ledger, read as amplitudes). -/
structure Signal where
  samples : List Int
deriving DecidableEq, Repr

/-- The smoothing operator's kernel: a 2-sample **block sum**.  It pairs up samples and records
their *sum* (a coarse, lossy readout).  An odd trailing sample is carried as-is.  This is the
admissible smooth completion; what it cannot see is its null space. -/
def blockSum : List Int -> List Int
  | a :: b :: rest => (a + b) :: blockSum rest
  | rest => rest

/-- The smoothing operator lifted to signals. -/
def smooth (s : Signal) : Signal := { samples := blockSum s.samples }

/-- Add two signals **componentwise** (the shorter signal's tail is taken from the longer one). -/
def addSamples : List Int -> List Int -> List Int
  | a :: as, b :: bs => (a + b) :: addSamples as bs
  | [], bs => bs
  | as, [] => as

/-- Add two signals componentwise. -/
def addSignal (s t : Signal) : Signal := { samples := addSamples s.samples t.samples }

-- ---------------------------------------------------------------------------
-- The null space: a sharp feature the shadow cannot represent.
-- ---------------------------------------------------------------------------

/-- A **sharp feature**: a high-frequency block pattern `[+h, -h]` whose block-sum is `0`.  This is
a discontinuity-like jump that the block sum annihilates: `(+h) + (-h) = 0`.  Added to a signal it
lives in the null space — the finite analogue of structure displaced into modes orthogonal to the
smooth basis. -/
def feature (h : Int) : Signal := { samples := [h, -h] }

-- ---------------------------------------------------------------------------
-- FALSIFIABLE lemmas. Each is ∀-quantified and breaks if a hypothesis is dropped.
-- ---------------------------------------------------------------------------

/-- NULL-SPACE LOCALIZATION (load-bearing, ∀ over every feature height `h` and every length-≥2
base `a, b, rest`): adding a sharp feature to the FIRST block does not change the shadow.  The
shadow of `base ⊕ feature h` equals the shadow of `base`, because `(a+h) + (b + -h) = a + b`.
This is exactly "smoothing cannot see the feature" — Gibbs preservation. -/
theorem shadow_kills_feature (h a b : Int) (rest : List Int) :
    blockSum (addSamples [a, b] (feature h).samples ++ rest)
      = blockSum (a :: b :: rest) := by
  show blockSum (addSamples [a, b] [h, -h] ++ rest) = blockSum (a :: b :: rest)
  show blockSum ((a + h) :: addSamples [b] [-h] ++ rest) = blockSum (a :: b :: rest)
  show blockSum ((a + h) :: (b + -h) :: addSamples [] [] ++ rest) = blockSum (a :: b :: rest)
  show ((a + h) + (b + -h)) :: blockSum rest = (a + b) :: blockSum rest
  have : (a + h) + (b + -h) = a + b := by omega
  rw [this]

/-- A feature with NONZERO height genuinely CHANGES the signal it is added to (so the preservation
above is about the *shadow*, not a triviality — the feature is really there in the ledger, it is
only invisible downstream).  ∀-quantified over `a, b, rest`; drop `hne` and it is false. -/
theorem feature_changes_signal (h a b : Int) (rest : List Int) (hne : h ≠ 0) :
    addSamples (a :: b :: rest) (feature h).samples ≠ (a :: b :: rest) := by
  intro hEq
  show False
  have hhead : a + h = a := by
    have := congrArg (fun l => l.headD 0) hEq
    simpa [addSamples, feature] using this
  have : h = 0 := by omega
  exact hne this

-- ---------------------------------------------------------------------------
-- A canonical event: a base signal and its feature-perturbed sibling.
-- ---------------------------------------------------------------------------

/-- A base signal (a smooth ramp). -/
def baseSignal : Signal := { samples := [2, 4, 6, 8] }

/-- The same signal with a sharp `[+5,-5]` feature added to its leading block. -/
def featuredSignal : Signal := addSignal baseSignal (feature 5)

/-- The block-sum **Projection** wrapped for the harness coupling. -/
def smoothing : Experiments.Common.Projection Signal Signal :=
  { project := smooth }

/-- The harness's `sameShadow` for `smoothing` is DECIDABLE so `decide`/`#eval` compute it. -/
instance (s t : Signal) : Decidable (Experiments.Common.Projection.sameShadow smoothing s t) := by
  unfold Experiments.Common.Projection.sameShadow smoothing smooth
  exact inferInstance

/-- The two signals are DIFFERENT (the feature is genuinely present). -/
theorem base_ne_featured : baseSignal ≠ featuredSignal := by decide

-- ---------------------------------------------------------------------------
-- THE CLAIM (content-bearing; the central conjunct is the harness's sameShadow).
-- ---------------------------------------------------------------------------

/-- The claim, in honest parts:
* (feature is real) the base and featured signals are distinct — the shape is present;
* (null-space localization) the block-sum kills the leading feature for ALL base blocks; and
* (shadow collapse — HARNESS coupling) `smoothing` gives both signals the **same shadow**, via
  `Experiments.Common.Projection.sameShadow`.  Break that harness path and `claim_holds` fails. -/
def claimStatement : Prop :=
  baseSignal ≠ featuredSignal ∧
    (∀ h a b : Int, ∀ rest : List Int,
      blockSum (addSamples [a, b] (feature h).samples ++ rest) = blockSum (a :: b :: rest)) ∧
    Experiments.Common.Projection.sameShadow smoothing baseSignal featuredSignal

def claim : Experiments.Common.Claim :=
  { tag := Experiments.Common.ClaimTag.smoothShadowAnalogy
    statement := claimStatement }

theorem claim_holds : claim.statement :=
  ⟨base_ne_featured, fun h a b rest => shadow_kills_feature h a b rest, by decide⟩

/-- The tag is an honest ceiling: a finite smooth-shadow stand-in, nothing more. -/
theorem ceiling :
    claim.tag = Experiments.Common.ClaimTag.smoothShadowAnalogy := rfl

-- ---------------------------------------------------------------------------
-- A computable run + a NON-vacuous Experiment.claim, with a proved bridge.
-- ---------------------------------------------------------------------------

structure Setup where
  base : Signal
  height : Int

/-- The run computes whether the base and its feature-perturbed sibling share a shadow. -/
def run (setup : Setup) : Bool :=
  decide (Experiments.Common.Projection.sameShadow smoothing
    setup.base (addSignal setup.base (feature setup.height)))

def experiment : Experiments.Common.Experiment Setup Bool :=
  { tag := claim.tag
    run := run
    claim := fun setup =>
      Experiments.Common.Projection.sameShadow smoothing
        setup.base (addSignal setup.base (feature setup.height)) }

theorem run_iff_claim (setup : Setup) :
    run setup = true ↔ experiment.claim setup := by
  simp only [run, experiment, decide_eq_true_iff]

def canonicalSetup : Setup := { base := baseSignal, height := 5 }

/-- Bring a minimal device next to this experiment: it records whether the exported claim fires.
It reuses `run` (which decides the same `sameShadow` predicate the exported claim names). -/
def deviceNear (setup : Setup) : Bool :=
  run setup

theorem deviceNear_detects_claim (setup : Setup) :
    deviceNear setup = true ↔ experiment.claim setup := by
  show run setup = true ↔ experiment.claim setup
  exact run_iff_claim setup

def triangulation : Experiments.Common.Triangulation Setup Bool :=
  { experiment := experiment
    device := deviceNear
    detects := deviceNear_detects_claim }

#eval run canonicalSetup                              -- expect: true  (shadow preserved)
#print axioms claim_holds                             -- ambient [propext, Quot.sound], not coupling
-- Load-bearing falsifiability check: the feature is NOT in the null space of the IDENTITY readout.
-- Evaluate the (false) claim that the featured signal equals the base under no smoothing at all:
#eval decide (baseSignal = featuredSignal)            -- expect: false (feature is genuinely present)

end Experiments.TheGibbsPreservationEffect
