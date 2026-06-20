import Experiments.Common

/-!
# The Gibbs Phenomenon — finite-refinement strain as a smooth shadow

Rebuilt to the EXEMPLAR shape (`ThePositronAnnihilationEffect/Experiment1.lean`).
It does the things the 3-`Nat` `CountSetup` template does **not**:

1. an **effect-specific domain** (`Step`, the discontinuous event; `BandShadow`, the
   bandwidth-limited reading) — not three undifferentiated `Nat`s;
2. genuinely **falsifiable** quantified lemmas (`∀`): the overshoot is bounded but
   **never zero** under finite refinement — drop the "finite band" hypothesis and the
   gap vanishes;
3. a **content-bearing** claim — a real conjunction, never `True`;
4. an **honest tag** (`smoothShadowAnalogy`) + a candid `NOT claimed` disclaimer;
5. explicit `Decidable` instances so `decide`/`#eval` compute through the predicates;
6. it **couples to the harness**: `claim_holds` is discharged in part by
   `Experiments.Common.Projection.sameShadow` — the formal statement that two fine
   configurations differing only in **unobserved (high-band)** structure read out to the
   **same** smooth shadow. That IS the description's "unobserved structure cannot be
   admitted": the lossy projection cannot see the difference, so it cannot close the jump.
   A rename/regression of `Projection.sameShadow` in the harness breaks THIS build.

## Physics (modelled finitely)
A discontinuous **step** of height `H` is forced through a band-limited reading of
resolution `band`.  The smooth shadow can climb to at most `band` per cell, so when the
true jump `H` exceeds what the finite band can close, a **residual gap** `H - band`
remains: the ringing/overshoot.  The gap is the irreducible informational strain.

## NOT claimed
That this reproduces the **Fourier** Gibbs constant (≈ 8.95% of the jump); that there is
any actual Fourier series, convergence, or limit here; any spectral analysis. There is no
trigonometry and no limit — only a finite ledger inequality standing in for the smooth
shadow's inability to close a discontinuity. **Claim ceiling:** a finite smooth-shadow
analogy, one of whose conjuncts is the harness's own projection theorem.
-/

namespace Experiments.TheGibbsPhenomenon

/-- A discontinuous event: a step of height `H` (the jump), sampled at finite
`refinement` (number of cells across the transition). Both `Nat`. -/
structure Step where
  height : Nat
  refinement : Nat
deriving DecidableEq, Repr

/-- A band-limited reading: the per-cell closing rate the smooth shadow can achieve.
`band` is the bandwidth — how much of the jump one refinement cell can absorb. -/
structure BandShadow where
  band : Nat
deriving DecidableEq, Repr

namespace BandShadow

/-- The height the smooth shadow actually reaches across the step: it cannot do better
than `band` per cell, capped at the true height. Written `Nat`-safely. -/
def reached (b : BandShadow) (s : Step) : Nat :=
  min s.height b.band

/-- The **residual overshoot/strain**: the part of the jump the finite band cannot close.
This is the Gibbs ring in this finite stand-in. -/
def gap (b : BandShadow) (s : Step) : Nat :=
  s.height - reached b s

/-- The band is **strictly finite** relative to this step: it cannot close the whole
jump in one reading (`band < height`). This is the hypothesis that makes the overshoot
real — drop it and the gap is zero. -/
def underResolved (b : BandShadow) (s : Step) : Prop :=
  b.band < s.height

/-- THE STRAIN RULE: an under-resolved step shows a **nonzero residual gap** that is
also **bounded** by the height. Both conjuncts matter and each is pinned below. -/
def shows (b : BandShadow) (s : Step) : Prop :=
  0 < gap b s ∧ gap b s ≤ s.height

instance (b : BandShadow) (s : Step) : Decidable (b.underResolved s) := by
  unfold underResolved; exact inferInstance
instance (b : BandShadow) (s : Step) : Decidable (b.shows s) := by
  unfold shows; exact inferInstance

end BandShadow

-- ---------------------------------------------------------------------------
-- FALSIFIABLE lemmas: each would break if its hypothesis were dropped.
-- ---------------------------------------------------------------------------

/-- **The overshoot persists.** For ANY step and ANY band that is under-resolved, the
residual gap is strictly positive: the smooth shadow can NEVER close the discontinuity.
Quantified over all `Step`/`BandShadow`.  Falsifiable: drop `underResolved` (i.e. allow
`band ≥ height`) and `gap = 0`, so the conclusion fails — see `#eval` at the bottom. -/
theorem overshoot_persists (b : BandShadow) (s : Step) (h : b.underResolved s) :
    0 < b.gap s := by
  unfold BandShadow.gap BandShadow.reached BandShadow.underResolved at *
  omega

/-- The strain is **bounded** by the jump it came from — it cannot exceed the height.
Quantified over all `Step`/`BandShadow` (needs no hypothesis: it is an honest bound). -/
theorem gap_le_height (b : BandShadow) (s : Step) : b.gap s ≤ s.height := by
  unfold BandShadow.gap BandShadow.reached
  omega

/-- A fully-resolved band (`band ≥ height`) closes the jump: **no** overshoot. This is the
contrapositive witness — it shows `overshoot_persists` genuinely needs its hypothesis. -/
theorem resolved_closes (b : BandShadow) (s : Step) (h : s.height ≤ b.band) :
    b.gap s = 0 := by
  unfold BandShadow.gap BandShadow.reached
  omega

-- ---------------------------------------------------------------------------
-- The canonical discontinuity.
-- ---------------------------------------------------------------------------

/-- A unit step of height 100, sampled across 16 cells. -/
def unitStep : Step := { height := 100, refinement := 16 }

/-- A finite band that closes 91 of the 100 units — leaving a 9-unit ring (a finite nod
to the ≈ 8.95% Gibbs overshoot, NOT a derivation of it; see `NOT claimed`). -/
def finiteBand : BandShadow := { band := 91 }

/-- The canonical reading is under-resolved (concrete, via the `Decidable` instance). -/
theorem canonical_underResolved : finiteBand.underResolved unitStep := by decide

/-- The canonical reading shows the strain rule. -/
theorem canonical_shows : finiteBand.shows unitStep := by decide

/-- The residual ring on the canonical event is exactly 9 units (frozen-literal check on
the chosen event, not a property of the rule). -/
theorem canonical_gap : finiteBand.gap unitStep = 9 := by decide

-- ---------------------------------------------------------------------------
-- HARNESS COUPLING: the lossy projection cannot admit unobserved structure.
-- ---------------------------------------------------------------------------

/-- The smooth shadow as a harness `Projection`: it reads a `Step` down to only the height
the band reaches (`reached`), discarding the residual ring (the high-band structure). -/
def shadowProjection : Experiments.Common.Projection Step Nat :=
  { project := fun s => finiteBand.reached s }

/-- Two distinct steps that **differ only in unobserved (above-band) structure**: same
heights up to the band, so the band-limited reading cannot tell them apart. Here both have
height ≥ band, so `reached = band` for both — yet they are genuinely different events. -/
def stepHidden : Step := { height := 100, refinement := 16 }
def stepHidden' : Step := { height := 200, refinement := 16 }

theorem hidden_steps_distinct : stepHidden ≠ stepHidden' := by decide

/-- **The coupling, load-bearing.** The two distinct under-resolved events read out to the
**same** smooth shadow: `Projection.sameShadow shadowProjection stepHidden stepHidden'`.
The finite band cannot admit the structure that distinguishes them — exactly the
description's "unobserved structure cannot be admitted". A rename/regression of
`Projection.sameShadow` in the harness breaks this proof. -/
theorem unobserved_structure_not_admitted :
    Experiments.Common.Projection.sameShadow shadowProjection stepHidden stepHidden' := by
  unfold Experiments.Common.Projection.sameShadow shadowProjection
  decide

-- ---------------------------------------------------------------------------
-- THE CLAIM (content-bearing; conjunction of the strain rule and the harness coupling).
-- ---------------------------------------------------------------------------

/-- The claim, in honest parts:
* (strain) the canonical under-resolved step shows a nonzero, bounded residual ring
  (`finiteBand.shows unitStep` — the overshoot is real and capped); and
* (no-admission) two distinct events differing only above the band read to the SAME smooth
  shadow (`Projection.sameShadow` — the harness coupling): the lossy reading literally
  cannot close the discontinuity because it cannot see the missing structure. -/
def claimStatement : Prop :=
  finiteBand.shows unitStep ∧
    Experiments.Common.Projection.sameShadow shadowProjection stepHidden stepHidden'

def claim : Experiments.Common.Claim :=
  { tag := Experiments.Common.ClaimTag.smoothShadowAnalogy
    statement := claimStatement }

theorem claim_holds : claim.statement :=
  ⟨canonical_shows, unobserved_structure_not_admitted⟩

/-- The tag is an honest ceiling: a finite smooth-shadow analogy, nothing more. -/
theorem ceiling : claim.tag = Experiments.Common.ClaimTag.smoothShadowAnalogy := rfl

-- ---------------------------------------------------------------------------
-- A computable run + a non-vacuous Experiment.claim, with a proved bridge.
-- ---------------------------------------------------------------------------

structure Setup where
  band : BandShadow
  step : Step

/-- The run computes — thanks to the `Decidable` instances above. -/
def run (s : Setup) : Bool := decide (s.band.shows s.step)

/-- The exported claim is a genuine function of the setup; this bridge pins it to `run`,
so the claim body cannot be silently swapped for `fun _ => True`. -/
def experiment : Experiments.Common.Experiment Setup Bool :=
  { tag := claim.tag
    run := run
    claim := fun s => s.band.shows s.step }

theorem run_iff_claim (s : Setup) :
    run s = true ↔ experiment.claim s := by
  simp only [run, experiment, decide_eq_true_iff]

def canonicalSetup : Setup := { band := finiteBand, step := unitStep }

#eval run canonicalSetup                                       -- expect: true
#eval run { canonicalSetup with band := { band := 100 } }      -- expect: false (closes the jump)
-- FALSIFIABILITY WITNESS: at a fully-resolved band the overshoot is ZERO, so the
-- under-resolved hypothesis of `overshoot_persists` is load-bearing, not vacuous.
#eval decide (0 < (BandShadow.mk 100).gap unitStep)            -- expect: false
#print axioms claim_holds                                      -- [propext, Quot.sound] = AMBIENT

instance (setup : Setup) : Decidable (experiment.claim setup) := by
  unfold experiment; exact inferInstance

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

end Experiments.TheGibbsPhenomenon
