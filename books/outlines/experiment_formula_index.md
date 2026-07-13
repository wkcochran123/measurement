# Experiment + Formula Index — the "vacuum-pressure" fuel per beat

*Kodo planning artifact for the operator's RESTART directive ("diffusion under a little vacuum pressure — experiment
description + formula where possible"). For each of the 15 story_arc chapters: candidate experiments from the
`device/Experiments/*` library (140 dirs) + the key formula(s). Podo picks per section and **grades off the build**
(confirm each experiment is live/carried, not atticked, at use — same discipline as AlphaProbe/RichardsonSelfNaming).
This is a MENU, not a mandate; "where possible" governs. Chapter-tagged experiments (…Ch02/03/06/07/08) are strong
signals of intended placement.*

---

## PART I — A DIFFERENCE
- **Ch 1 · A Difference Appears** — EXP: `Precision`, `RepeatabilityOfInvisibleMotion`, `TheWittgensteinEffect` (private-language / the distinction), `TheMessageEffect` / `TheFessendenShannonEffect` (a symbol means by contrast), `TheLimitationOfIndexing`. FORMULA: distinguishability `s1 ≠ symbol`; identity of indiscernibles (Leibniz, run backwards); resolution ⩽ measurement.
- **Ch 2 · Difference Becomes Countable** — EXP: `ThePeanoKushimEffect` (zero+successor), `TheTopologicalIntegerCount`, `TheContinuumLimitEffect` (Cauchy/limit as approach), `TheRefinementEffect`. FORMULA: `Nat` = zero+succ; Cauchy `∀ε ∃N …`; a real = `(value : Rational, iterate)` (finite condition).
- **Ch 3 · The Residue Refuses To Disappear** — EXP: `TheRichardsonEffect` (the residual! = coastline paradox, USED §3.1), `TheGaussFirstEffect` (least-squares residual), `TheThermodynamicCostOfErasure` (Landauer, USED §3.2). Root-finding residual = the `newton1687` CITATION, not an experiment. FORMULA: `L₂` residual `‖r‖ = ‖b − Ax‖`; residue = origin + magnitude.

## PART II — THE TURN
- **Ch 4 · The Tower Turns Around** — EXP: `Fluxions` (calculus of variations / fluxion), `TheDiracOperator` (the √ / seam), `TheRefinementEffect`. FORMULA: intro/elim (Gentzen); the commutator `[∇_a,∇_b]` at the seam; the imaginary crossing `√−1`.
- **Ch 5 · The Slip Becomes A Number** — EXP: `TheQuicksandEffect` (static→kinetic breakaway), `TheDaVinciCoulombEffect` (dry friction), `TheGalileoEffect`. FORMULA: Coulomb friction `|F| ≤ μ|N|` (the breakaway is where ≤ becomes =); the slip = non-closure of the loop.
- **Ch 6 · The Bracketed Number** — EXP: `Precision`, `TheHeisenbergEffect` (resolution floor / trade-off), `TheIdealLedgerEffect` (repeatability). FORMULA: `[lower, upper]`; machine ε (`Metavariable`); the reading = the bracket, width = resolution.

## PART III — THE FACES
- **Ch 7 · The Number Splits Into Faces** — EXP: `TheProverVerifierEffect` (independent checks converge), Whewell consilience (via multi-experiment agreement). FORMULA: the null-basis / four decorrelated readings of one residue.
- **Ch 8 · The Electron Is Named** *(CLIMAX)* — EXP: `TheLimitationOfIndexing` (finite boxes), `ThePeanoKushimEffect`, `TheTopologicalIntegerCount` (the box count), Millikan (external charge, cited). FORMULA: pigeonhole `|terms| > |boxes| → collision`; `boxOf : Variation → Fin boxCount`; electron = box distinct from value's box (−1 = physics reading, MARKED).
- **Ch 9 · The Corridor Rotates** — EXP: `TheAharonovBohmEffect` (phase!), `TheSagnacEffect` / `TheFoucaultEffect` (rotation), `TheAngularMomentumEffect`, `TheMomentumEffect`, `TheSpin12Effect`. FORMULA: `−i` generator; `e^{iθ}`; relabeling = angular momentum (a conserved current).

## PART IV — THE CLOSING
- **Ch 10 · The Native Apparatus Presents The Residue** — EXP (SURVIVING ONLY — fidelity!): Cavendish (via `TheInverseSquareEffect`; the live Cavendish decls are `Episode36.lean`), `TheKeplerEffect` (orbit), `TheDaVinciCoulombEffect` (Lorentz/force), `TheDiracOperator`, `MinimizingVariations` (Galerkin), `ThePhotoelectricEffect`. ⚠ NOT `TheChiralityEffect`/`TheSemiconductorEffect`/Mott/Stern-Gerlach/small-angle (retreated). FORMULA: `F = GMm/r²`; the Galerkin projection; the Lorentz bracket.
- **Ch 11 · The Compiler Becomes The Meter** — EXP: `TheAmdahlEffect` (parallel cost), `TheTailLatencyEffect`, `TheThermodynamicCostOfErasure` (Landauer), `TheHaltEffect`, `TheTuringEffect`, `TheVonNeumannEffect`. FORMULA: cost = elaboration heartbeats; `heartbeatCoefficient = 1000` (rank ≡ heartbeat/1000); self-reference (the meter on itself).
- **Ch 12 · The Field Closes** — EXP: `TheMaxwellEffect`, `TheMeissnerEffect` (magnetic side / field expulsion), `TheYangMillsEffect`, `TheSombreroPotential`, `TheSuperconductingEffect`, `MinimizingVariations`. FORMULA: second variation `δ²`; `F = dA + A∧A` (Yang–Mills); Maxwell (electric+magnetic) — MARKED finite three-rung, NOT continuum.

## PART V — THE BOUND
- **Ch 13 · Alpha As A Bracket** — EXP: `TheRichardsonEffect` (residual/extrapolation — the two-path `1→3 = 1→2→3` calibration; NB `RichardsonSelfNaming` decl is ATTICKED; use the EFFECT as concept, anchor code to `SelfApplication`/`AlphaBoundMediant`), `TheChaitinEffect` (uncomputability), `TheFeynmanDiagram` / `ThePositronThresholdEffect` (self-energy), `TheContinuumLimitEffect` (Dedekind), `TheGaussFirstEffect` (Gauss quadrature — a MARKED side-diagnostic, NOT the bracket source). FORMULA: the **mediant / continued-fraction** descent of the surd `√(18/5)`, periodic CF `[1;1,8,1,2̄]`, convergents `1/1,2/1,17/9,…`; count-to-3 = 3 partial quotients → **bracket `[129.6, 137.7]`** (`AlphaBoundMediant`, `count3_bracket_ordered` by `decide`), device's own `≈137.011`; the 3-point Gauss–Legendre rule (`c ± h√(3/5)`, weights `5/9·8/9·5/9`, exact to degree 5) is a marked side-diagnostic, NOT "bracket = the quadrature remainder"; `1 = 0.999…`. (137.036 external-only.)
- **Ch 14 · The Machine Measures Its Own Measurement** *(Vol3 climax)* — EXP: `TheHaltEffect`, `TheProverVerifierEffect`, `TheTHooftSusskindEffect` (holography/self-description), `TheVonNeumannEffect`, `TheGibbsPreservationEffect`. FORMULA: `two_descriptions := rfl` (WITNESS lives here, 16+); `1 = 0.999…`; self-application = the fixpoint's overhead.
- **Ch 15 · What The Machine Can And Cannot Claim** *(JAR)* — EXP: `TheGibbsPhenomenon` / `TheFirstEffectOfGibbs` (ringing = the crank's forced point!), `TheChaitinEffect` (uncomputable magnitude), `TheHeisenbergEffect` (a limit is a result), `TheCantorGodelCohenEffect` (what a system cannot decide from inside), `TheContinuumLimitEffect`. FORMULA: Ricci (trace) ⊕ Weyl (trace-free); the jar = strain relaxed by diffusion into the open bracket (NOT the forced point that rings); `#print axioms = []`.

---

## Notes
- **⚠ NAMES CAN MISLEAD — read `description.md` before citing.** Experiment dir names don't always match the concept: `TheNewtonEffect` is a **phase-misalignment bookkeeping cost**, NOT Newton's root-finding (Podo caught this at §5.2; Newton's *method* = the `newton1687` citation). `TheIdealLedgerEffect` = ideal-gas/pressure (not a repeatability/ledger demo). `ImpliedOrthogonalityAndSpaceTime` = a **DISCLAIMER** ("no structure orthogonal to space-time; set-theoretic") — NOT an orthogonal-decomposition demo (use **Fourier** for that, §7.2). Verify the actual content, don't trust the name.
- **Grade off the build:** Podo confirms each cited experiment is a live/carried decl at use (some `The<X>Effect` dirs may be atticked or from the old book structure). The atticked-instrument pattern (AlphaProbe / bound=60 / RichardsonSelfNaming) means DON'T assume — verify, then cite.
- **Register per gauge:** Vol 4 (code-walk) describes the experiment's READING + the formula; Vol 2 (math) would carry the formula as the primary object; Vol 3 (computation) the experiment as a decision-procedure. When the Vol1/2/3 outlines gain their EXPERIMENT+FORMULA slots, draw from the same per-beat menu, rendered in each register.
- **Blind/fidelity/step all hold.** Formula ≠ Lean source dump.
