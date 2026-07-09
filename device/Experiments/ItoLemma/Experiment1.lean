import Experiments.Common

/-!
# Itô's Lemma — finite refinement shadow (rebuilt to the EXEMPLAR shape)

Itô's Lemma appears in the source NOT as stochastic calculus but as a *structural*
consequence of informational refinement: when a finite record is refined, comparing
two successive minimal interpolants forces a **second-order correction** `(dX)²` that
the naïve first-order chain rule (`df = f'·dX`) silently drops. The Itô update keeps it:
`df = f'·dX + ½ f''·(dX)²`.

This file models one refinement step over the **integers** (a finite, exact, decidable
ledger — NOT `Experiments.Common.CountSetup`'s three undifferentiated `Nat`s). A step carries
the increment `dX`, the slopes `f'` and `f''`, and we compute the two updates:

* `itoUpdate`  = `f'·dX + ½·f''·dX²`   (the refinement-consistent update — but see the
   even-`f''·dX²` note: we carry `2·f''·dX²` and a halved variant to stay in `Int` exactly);
* `naiveUpdate` = `f'·dX`               (first-order only).

The **content** is: the two updates *differ by exactly the Itô correction*, and that
correction is genuinely non-zero whenever curvature and step are non-zero. That difference
is the "informational artifact" the source describes.

## COUPLING (honest)
This effect is refinement / scale-change / successive-interpolant comparison. It has **no**
holonomy, gauge phase, curvature-as-Berry-phase, or charge — so it does NOT touch the device
(`Measurement.*`). The honest harness hook is `Experiments.Common.Ledger.count_map`
(= the count law of `Refinement.pushLedger`): **refining a finite record of steps preserves
the number of recorded steps** — the bookkeeping invariant under refinement. A conjunct of
`claim_holds` is discharged by `count_map`, so a regression there breaks this build.

## NOT claimed
That this is Itô's Lemma of stochastic calculus; no probability, no Brownian motion, no
diffusion, no `dW²=dt` quadratic-variation theorem, no continuous limit. `f'`, `f''`, `dX`
are *labelled integer slopes*, not derivatives of a real function. We do not prove any
Taylor remainder bound. **Claim ceiling:** a finite, exact, second-order *bookkeeping shadow*
of the refinement correction, plus the harness count law for the refinement map.
-/

namespace Experiments.ItoLemma

/-- One refinement step of a finite record: the increment `dX` of the underlying record,
and the first/second discrete slopes `slope1 = f'`, `slope2 = f''` of the tracked function.
All integers — exact and decidable. -/
structure Step where
  dX : Int
  slope1 : Int
  slope2 : Int
deriving DecidableEq, Repr

namespace Step

/-- The squared increment `(dX)²` — the carrier of the second-order correction. -/
def stepSq (s : Step) : Int := s.dX * s.dX

/-- The Itô correction term, carried as `slope2 · (dX)²` (the `½` is factored OUT and
tracked separately as `naiveUpdate` vs `itoUpdateDoubled` so everything stays exact in `Int`;
"½ f''(dX)²" then reads off as `correction / 2`). -/
def correction (s : Step) : Int := s.slope2 * s.stepSq

/-- First-order (naïve chain-rule) update, DOUBLED so the comparison stays in `Int`:
`2 · f' · dX`. -/
def naiveDoubled (s : Step) : Int := 2 * (s.slope1 * s.dX)

/-- Refinement-consistent (Itô) update, DOUBLED: `2·f'·dX + f''·(dX)²`. The `/2` of the
real Itô update is the shared factor; doubling both sides keeps the difference exact. -/
def itoDoubled (s : Step) : Int := s.naiveDoubled + s.correction

/-- The step is **non-degenerate**: a real refinement (`dX ≠ 0`) with real curvature
(`slope2 ≠ 0`). This is the hypothesis whose removal makes the Itô lemma vacuous. -/
def nondegenerate (s : Step) : Prop := s.dX ≠ 0 ∧ s.slope2 ≠ 0

instance (s : Step) : Decidable (s.nondegenerate) := by
  unfold nondegenerate; exact inferInstance

end Step

-- ---------------------------------------------------------------------------
-- FALSIFIABLE lemmas. Each is ∀-quantified and breaks if a hypothesis is dropped.
-- ---------------------------------------------------------------------------

/-- The Itô update minus the naïve update is **exactly** the second-order correction.
This is the structural identity `(f'dX + ½f''dX²) − f'dX = ½f''dX²`, doubled to stay in `Int`.
Quantified over ALL steps. (Holds unconditionally — it is the *algebra* of the correction.) -/
theorem ito_minus_naive_is_correction (s : Step) :
    s.itoDoubled - s.naiveDoubled = s.correction := by
  unfold Step.itoDoubled
  omega

/-- **FALSIFIABLE / load-bearing.** On a non-degenerate step the correction is non-zero:
the Itô update genuinely *differs* from the naïve chain rule. Drop EITHER conjunct of
`nondegenerate` (`dX ≠ 0` or `slope2 ≠ 0`) and the conclusion fails — e.g. `dX = 0` gives
`correction = 0`. Quantified over ALL steps. -/
theorem nondegenerate_correction_nonzero (s : Step) (h : s.nondegenerate) :
    s.correction ≠ 0 := by
  unfold Step.correction Step.stepSq
  have hdx : s.dX ≠ 0 := h.1
  have hs2 : s.slope2 ≠ 0 := h.2
  -- product of nonzeros is nonzero (over Int, core lemma)
  exact Int.mul_ne_zero hs2 (Int.mul_ne_zero hdx hdx)

/-- Contrapositive content, fully decidable form: if the correction vanishes the step is
degenerate. Pins that the non-degeneracy hypothesis is exactly the load-bearing one. -/
theorem zero_correction_is_degenerate (s : Step) (h : s.correction = 0) :
    ¬ s.nondegenerate :=
  fun hnd => nondegenerate_correction_nonzero s hnd h

-- ---------------------------------------------------------------------------
-- HARNESS COUPLING: refining a finite record of steps preserves the step count.
-- ---------------------------------------------------------------------------

/-- A refinement decodes a fine step into the coarse increment it contributes. -/
def stepRefinement : Experiments.Common.Refinement Int Step :=
  { decode := fun s => s.dX }

/-- A finite record of refinement steps. -/
def sampleRecord : Experiments.Common.Ledger Step :=
  { events := [ { dX := 2, slope1 := 3, slope2 := 5 },
                { dX := 1, slope1 := 0, slope2 := 7 } ] }

/-- The bookkeeping invariant: pushing the record through the refinement (decoding every step
to its increment) does NOT change the number of recorded steps. This is the harness
`count_map` law specialized to `stepRefinement` — the count law of `Refinement.pushLedger`. -/
theorem refinement_preserves_step_count :
    (stepRefinement.pushLedger sampleRecord).count = sampleRecord.count := by
  unfold Experiments.Common.Refinement.pushLedger
  exact Experiments.Common.Ledger.count_map stepRefinement.decode sampleRecord

-- ---------------------------------------------------------------------------
-- THE CANONICAL STEP + concrete checks.
-- ---------------------------------------------------------------------------

/-- A concrete non-degenerate refinement step. -/
def canonicalStep : Step := { dX := 2, slope1 := 3, slope2 := 5 }

theorem canonicalStep_nondegenerate : canonicalStep.nondegenerate := by decide

/-- Concrete arithmetic receipt: on `canonicalStep`, ito − naive = correction = 5·4 = 20. -/
theorem canonical_difference :
    canonicalStep.itoDoubled - canonicalStep.naiveDoubled = 20 := by decide

-- ---------------------------------------------------------------------------
-- THE CLAIM (content-bearing conjunction; one conjunct is the harness theorem).
-- ---------------------------------------------------------------------------

/-- The claim, in honest parts:
* (algebra) the Itô update exceeds the naïve update by exactly the correction, on the
  canonical step — `ito_minus_naive_is_correction`;
* (non-vacuity) that correction is genuinely non-zero on a non-degenerate step —
  `nondegenerate_correction_nonzero`, the FALSIFIABLE core; and
* (harness coupling) refining the finite step-record preserves the step count —
  `refinement_preserves_step_count`, discharged by `Experiments.Common.Ledger.count_map`. -/
def claimStatement : Prop :=
  (canonicalStep.itoDoubled - canonicalStep.naiveDoubled = canonicalStep.correction) ∧
    canonicalStep.correction ≠ 0 ∧
    (stepRefinement.pushLedger sampleRecord).count = sampleRecord.count

def claim : Experiments.Common.Claim :=
  { tag := Experiments.Common.ClaimTag.smoothShadowAnalogy
    statement := claimStatement }

theorem claim_holds : claim.statement :=
  ⟨ito_minus_naive_is_correction canonicalStep,
    nondegenerate_correction_nonzero canonicalStep canonicalStep_nondegenerate,
    refinement_preserves_step_count⟩

/-- Honest ceiling: a finite stand-in for the continuous Itô correction — a smooth-shadow
analogy, nothing more. (Not mechanically enforced; the tag is a convention.) -/
theorem ceiling :
    claim.tag = Experiments.Common.ClaimTag.smoothShadowAnalogy := rfl

-- ---------------------------------------------------------------------------
-- A computable run + a non-vacuous Experiment.claim, with a proved bridge.
-- ---------------------------------------------------------------------------

structure Setup where
  step : Step

/-- The run computes (via the `Decidable` instance on `nondegenerate`): does this step carry a
genuine Itô correction? -/
def run (s : Setup) : Bool := decide (s.step.nondegenerate)

/-- The exported claim is a genuine function of the setup, pinned to `run` by the bridge below. -/
def experiment : Experiments.Common.Experiment Setup Bool :=
  { tag := claim.tag
    run := run
    claim := fun s => s.step.nondegenerate }

theorem run_iff_claim (s : Setup) :
    run s = true ↔ experiment.claim s := by
  simp only [run, experiment, decide_eq_true_iff]

def canonicalSetup : Setup := { step := canonicalStep }

#eval run canonicalSetup                                  -- expect: true
#eval run { step := { dX := 0, slope1 := 3, slope2 := 5 } }  -- expect: false (degenerate)
-- Gate: evaluate the falsifiable predicate where it is FALSE (dX = 0 ⇒ correction = 0):
#eval decide (Step.correction { dX := 0, slope1 := 3, slope2 := 5 } ≠ 0)  -- expect: false
#print axioms claim_holds                                 -- ambient footprint, not coupling

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

end Experiments.ItoLemma
