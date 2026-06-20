# Experiments Goals

Status date: 2026-06-20.

This file tracks the current target for `device/Experiments` after the latest
triangulation wave.  `FEEDBACK.md` and `FEEDBACK2.md` are retained as historical
reviews; several of their headline counts are now stale.

## Current State

- Every experiment directory has `Experiment1.lean`, `Experiment2.lean`, and
  `Experiment3.lean`.
- `device/Experiments.lean` imports every `Experiment3.lean` exactly once.
- Every `Experiment1.lean` exports an `Experiments.Common.Triangulation`.
- The triangulation brings a local boolean `deviceNear` next to the experiment
  and proves `deviceNear setup = true ↔ experiment.claim setup`.
- Eight experiments are coupled directly to `Measurement` episodes:
  `TheAharonovBohmEffect`, `TheChiralityEffect`, `TheDavissonGermerEffect`,
  `TheDiracOperator`, `TheEchoChamberMazeSolution`, `ThePositronAnnihilationEffect`,
  `ThePositronThresholdEffect`, and `TheSagnacEffect` — and climbing as the rebuild sweep lands the
  genuinely gauge/charge effects.  FLAG: `TheEchoChamberMazeSolution`'s coupling to
  `native_antimatter_is_zero` is suspect — a maze solver has no honest antimatter face; this looks
  like a forced coupling and should be rolled back to a harness lemma or an honest decline.

## Primary Triangulation Target: The Positron

The immediate goal is to triangulate the positron as a stable local object of
the Measurement apparatus.  This is not a standalone particle-physics claim.
It is a three-sided receipt inside the device:

1. **Sign face:** `Measurement.Episode83` reads the positron as the
   baseline-relative sign of a pair interaction.  The flat baseline has no
   positron event; the tilted baseline has one.
2. **Count and threshold face:** `Measurement.Episode85` counts that sign.  The
   native flat baseline has antimatter count `0`, while the tilted baseline has
   antimatter count at least `1`.  `ThePositronThresholdEffect` packages this as
   the bracket `(0, 1]` in tag-strain units.
3. **Detector face:** `ThePositronAnnihilationEffect` gives the external
   annihilation/coincidence receipt: the canonical 511 keV back-to-back photon
   pair registers locally, while the claim also depends on the device's
   cancellation and tilted-positron theorems.

The positron is considered triangulated when these three faces agree:
`sign -> count/threshold -> detector receipt`.  If any face regresses, the
apparatus has not stabilized the positron.

## Trial Hierarchy

An experiment should not contribute only one datum to the final study.  Each
experiment should contain many trials, and the experiment itself should become a
trial family in the final study:

```text
setup -> trial -> experiment trial suite -> final study
```

The local triangulation remains the receipt for one setup:
`deviceNear setup = true ↔ experiment.claim setup`.  The next layer is to run
that receipt over a family of setups: positive controls, negative controls,
boundary cases, short paths, long paths, perturbed paths, and repeated epsilon
windows.  The final study should then compare the summaries of those trial
families, not isolated claims.

For the positron target, the final study should compare at least three trial
families:

1. Sign trials from `Measurement.Episode83`: flat versus tilted, matter versus
   antimatter sign.
2. Count and threshold trials from `Measurement.Episode85`: below threshold, at
   threshold, above threshold.
3. Detector trials from `ThePositronAnnihilationEffect`: coincidence present,
   coincidence absent, malformed receipt, and cancellation.

The positron is stable only when those trial families agree on the same local
object across their own controls and boundary cases.

## Stress-Strain Curves

Each phenomenon should eventually export a stress-strain curve.  The convention is the **device's**,
not the materials-textbook one: **stress is the device's reading** — δ² (`pairDelta2`), the residue,
the detection, whatever the apparatus reports.  **Strain is the distance: the count from the
origin** — how far the configuration sits from the symmetric baseline (tilt, refinement depth, the
controlled knob) — and it is **contravariant** (the raised / `after` index).  The reading *is* the
stress; the count-from-origin *is* the strain.  (Earlier drafts inverted these, calling the
controlled knob "stress"; but the knob is a deformation = strain, and the response is the stress.)

The curve is the honest object of comparison.  A single successful detection
says the apparatus can see a phenomenon at one point.  A stress-strain curve says
how the phenomenon responds as the device is brought nearer, pushed harder, or
given more time.  This is where short-path versus long-path comparisons belong:
`Experiment1` can expose the short/local path, `Experiment2` can expose the
long/refined path, and `Experiment3` can compare the two as a curve instead of
only an equality.

Each curve should name two anchors: the origin and the finale.  The origin is the control setup
where the phenomenon reads false, absent, or zero strain.  The finale is the setup where it reads
true, present, or saturated enough to count.  The kink — the transition region where the apparatus
stops behaving like the false control and starts behaving like the true receipt — is **measured**,
not ordained.  Do NOT pre-place it "roughly halfway": that *ordains the Lorentz/convergence
transform*, which is the one object that must be **fit, never assumed**.  The mesh-refinement study
(next section) shows why — assuming a halfway/linear kink lands on the wrong crossing; the knot
estimator, which assumes no location, recovers the true one.

The final study should treat each experiment as one curve-bearing trial family.
The study then asks whether different phenomena have compatible curves, shared
thresholds, or recognizable failure modes.  For the positron, the expected curve
is especially sharp: the flat baseline should remain at zero positron strain,
while the tilted/count/detector trials should cross the threshold in the same
place.  If the sign, count/threshold, and detector curves kink at incompatible
stress locations, the positron has not been triangulated.  If their kinks align,
the apparatus has found the same local object from three directions.

## Continuum Limit and Mesh Refinement

The device reads on a finite mesh — the event list, sampled at the count-from-origin strain.  The
continuum is the `h → 0` limit of that mesh, and the only honest route to it is a mesh-refinement
study.  This is now built: `TheContinuumLimitEffect`.  Two facts come out of it, both load-bearing:

1. **The device is pinned at the coarsest mesh.**  `discriminatingAction.segmentCost` is a binary
   tag-indicator and `tag` collapses every term to `{0,1,2}`, so δ² lives entirely in the three-tag
   quotient.  Deeper terms collapse to the same three classes (the pigeonhole).  The device cannot
   refine; the continuum is only *nameable*, as the limit of a refinable graded-cost family whose
   coarsest member *is* the device's reading.  The gap between the `h=1` reading and that limit is
   the irreducible honest-ceiling error — now quantified, not asserted.

2. **The linear least-squares (Hooke) threshold estimator is biased, not merely noisy.**  Refining
   the strain mesh shrinks sampling error, but the linear fit converges to the *wrong* crossing
   because the stress/strain curve is kinked, not linear (in the study: → 1.5 instead of 1.0, error
   floored at 0.5).  The **knot estimator** (false → before → after → true) assumes no functional
   form and converges to the true kink.  `ThePositronThresholdEffect`'s old `R² ≈ 0.19` was this
   bias, not bad luck; it has been switched to the knot estimator and now proves
   `knotThreshold = (1, 2)` — strain\* = 1/2, unbiased, inside the proven `(0,1]` bracket.

Methodological rule: the spline/knot layer (next section) is **not optional polish** — it is the
only unbiased route to a kink.  Any experiment reporting a threshold from a linear fit is reporting
a biased number.  And the convergence law itself — how readings transform across mesh levels — is
the not-ordained Lorentz object: fit it from the refinement, never assume it.

## Analytic Curve Recovery

Once a phenomenon has an origin, finale, and expected kink region, the apparatus
should recover an analytic object from the trials instead of only reporting a
boolean receipt.  The basic knot pattern is:

```text
false -> before -> after -> true
```

The false knot is the stable control before the phenomenon appears.  The before
knot is the last sampled point that still behaves like the false side of the
transition.  The after knot is the first sampled point that behaves like the
true side of the transition.  The true knot is the stable finale where the
phenomenon is present enough to count.

Those four knots should determine a small spline for the phenomenon's
stress-strain response.  A first pass can use a finite or piecewise-linear
spline; richer experiments can use a smoother spline once they have enough
samples and proof obligations.  The curvature of that spline is the analytic
target: the kink should be visible as the region of largest curvature or
sharpest change in strain.

This is the promised route from local device receipts to the thing being sought
analytically.  The final study should compare curvature signatures, not merely
truth values.  For the positron, the sign curve, count/threshold curve, and
detector curve should have compatible curvature peaks near the same stress
location.  If they do, the apparatus has found the same object three ways.  If
they do not, one of the faces is measuring a different transition.

## Lorentz Operator And Residue

The spline comparison layer should be treated as the Lorentz-facing operator of
the apparatus.  It compares response curves across local coordinates while
preserving the receipt that each local device reports.  In this sense, the
operator is not merely asking whether two trials are both true; it asks what
curvature remains invariant when the local QED-style interaction receipt is
transported, compared, or refined.

The working target is:

```text
local interaction receipt -> spline curvature -> invariant residue
```

The local interaction receipt is the QED-like face of the experiment: sign,
count, threshold, detector coincidence, path phase, scattering event, or another
local finite interaction.  The invariant residue is the GR-like face: the
curvature or geometric obstruction that remains after the local receipt is
compared across frames, paths, or refinements.

This is still an apparatus-internal claim ceiling, not a standalone derivation
of General Relativity from Quantum Electrodynamics.  The honest version is:
when the experiment is modeled locally in the Measurement device, the leftover
curvature signature should be where the GR-like residue appears.  If the final
study is successful, QED supplies the local receipt and GR appears in the
residue of the comparison.

For the positron target, the local QED-like receipts are the sign, threshold,
and annihilation/coincidence trials.  The GR-like residue would be the shared
curvature signature that survives after those three curves are transported into
the same comparison frame.

## Review Findings

1. The triangulation goal is structurally present across the suite AND Lean-verified: the full
   `Experiments` library builds green (exit 0), every `Experiment1` exports a `Triangulation`
   (138/138, confirmed), and the rebuild sweep has upgraded 62 of them from `CountSetup` to
   effect-specific domain models with load-bearing couplings (the remaining ~66 pending).
2. The six device-coupled experiments are the strongest regression tests because
   their claims depend on actual `Measurement` theorems.
3. The positron-specific experiments are the current canonical triangulation
   example: internal sign, counted threshold, and external detector receipt all
   point at the same device object.
4. Many remaining experiments still use the first-pass `CountSetup` model. Their
   triangulation proves what the local device detects, but the local model is
   still shallow.
5. The current suite mostly lacks explicit trial families and stress-strain
   curves.  That is the next structural gap after local triangulation.
6. `Experiment2` and `Experiment3` are now mostly import/audit layers. They no
   longer provide much independent coverage unless a specific experiment makes
   them substantive.
7. The tag ceiling is still mostly conventional. A later pass should make tags
   derive proof obligations instead of merely labeling them.

## Next Goals

1. Verify the full `Experiments` library when the operator says it is safe to
   run Lean/Lake.
2. Fix any decidability or import issues exposed by that verification without
   weakening the triangulation receipt.
3. Make the positron triangle harder to fake: keep the sign, threshold/count,
   and detector receipts separate, then add comparison theorems showing exactly
   where they agree.
4. Add a common trial-family interface so every experiment can expose multiple
   setups, expected controls, and a summarized trial result.
5. Add a common stress-strain interface so every phenomenon can name its stress
   knob, strain measurement, and curve samples without pretending they are all
   the same physics.
6. Require each curve-bearing experiment to name its origin, finale, and
   expected kink region.  The kink should be near the midpoint between false and
   true in the experiment's stress coordinate unless the phenomenon explains why
   it is asymmetric.
7. Add a common knot interface for `false`, `before`, `after`, and `true`
   samples, so each experiment can expose the transition region explicitly.
8. Add a common spline and curvature interface, starting finite and
   piecewise-linear if necessary.  The analytic target is the location and
   magnitude of the curvature peak.
9. Add a Lorentz-facing comparison operator for transporting or comparing
   stress-strain curves across local coordinates while preserving local device
   receipts.
10. Track the invariant residue of those comparisons.  The desired target is
   QED-like local interaction in the receipt and GR-like curvature in the
   residue.
11. Use `Experiment3` as the comparison layer where possible: short path from
   `Experiment1`, long/refined path from `Experiment2`, and a stress-strain
   comparison between them.
12. Extend the positron pattern only where honest.  For each new candidate,
   identify its sign/internal face, its count or threshold face, and its
   detector or external receipt before adding a device coupling.
13. Promote high-value `CountSetup` experiments to effect-specific models, using
   the current device-coupled files as templates.
14. Add more honest `Measurement` couplings only where the device theorem really
   matches the phenomenon; do not force fake couplings.
15. Make claim tags enforce obligations mechanically, so the tag becomes a fence
   rather than a sticker.
16. Decide whether `Experiment2`/`Experiment3` should become real independent
   audit paths, curve-comparison layers, or remain thin import layers.
