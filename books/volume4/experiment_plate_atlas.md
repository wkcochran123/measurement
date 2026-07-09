# Volume 4 Experiment Plate Atlas

## Corpus Rule

Use the experiment corpus as the visual and explanatory reservoir for Volume 4.

In this checkout the live source path is:

```text
device/Experiments/
```

I do not see a `device/Measurement/Experiments/` directory. Treat the operator's
`device/Measurement/Experiments/` reference as pointing to `device/Experiments/`
unless that directory is later created.

There are currently 137 `description.md` files under `device/Experiments/`.
That count is useful catalog metadata for this volume, but it must not be
treated as evidence for alpha. It is not a result. It is only the size of the
inspiration library in this checkout.

## How Volume 4 Uses Experiments

The experiments are not a proof substitute. They are the book's image library:
plates, sidebars, caption examples, analogies, cautionary panels, and visual
receipts.

The code is the detail layer. For each experiment, the `description.md` gives
the visible scene and the `Experiment*.lean` files give the mechanism under the
glass: local definitions, controls, thresholds, claim tags, and small theorems.
For the device proper, `device/Measurement/**/*.lean` is also available when a
chapter needs the exact structure behind loop, phase, gauge, charge, or reader.
Read these files for nitty gritty details. Do not quote code into the coffee-
table prose unless a later explicit appendix asks for it.

Every draft chapter may draw from any experiment when it clarifies:

- the whole measurement loop;
- the phase face;
- one coupling or crossing;
- gauge and holonomy;
- cost, constraint, erasure, latency, or accounting;
- visibility of invisible structure;
- thresholds, brackets, and no-go boundaries;
- reader, record, signal, or instrument discipline.

Claim discipline stays unchanged:

- **Explanation** may use accepted science vocabulary from descriptions.
- **Device-reading** may say how an experiment helps us see the device.
- **Build result** may cite only what the experiment or prior book floor earned
  at its declared ceiling, checked against source files when precision matters.
- **Speculation** covers purely visual, philosophical, or alpha-facing pressure.

## Plate Families

### Phase, Interference, And Holonomy

Use these when the chapter needs a face where invisible phase becomes visible,
or a loop where a hidden relation leaves a residue.

Core inspirations:

- `TheAharonovBohmEffect`
- `TheMachZehnderEffect`
- `TheMalusEffect`
- `TheSchrodingerYoungEffect`
- `TheFoucaultEffect`
- `TheSagnacEffect`
- `TheDavissonGermerEffect`
- `TheEchoChamberMazeSolution`
- `TheDiracOperator`
- `TheChiralityEffect`
- `TheFeynmanDiagram`
- `TheYangMillsEffect`
- `TheTopologicalIntegerCount`

Best Vol 4 use:

- phase face plates;
- ring and loop plates;
- "invisible field, visible receipt" captions;
- holonomy as a cost mark that survives return.

### Light, Coupling, And Detection

Use these when the book needs to put alpha's physical face on the page:
charged matter talking to light.

Core inspirations:

- `ThePhotoelectricEffect`
- `TheComptonScatteringEffect`
- `TheFeynmanDiagram`
- `TheDiracOperator`
- `TheGammaDecayEffect`
- `ThePositronAnnihilationEffect`
- `ThePositronThresholdEffect`
- `QubitDecoherence`
- `ShadowTomography`
- `TheHallEinsteinPodolskyRosenEffect`
- `SpookyActionAtADistance`
- `TheBellAspectTests`
- `TheEntanglementEffect`

Best Vol 4 use:

- electron-photon vertex as needle-through;
- detector receipts;
- threshold brackets;
- coincidence and anti-coincidence spreads.

### Measurement, Records, And Reader

Use these when the chapter needs to show how a reading becomes public,
repeatable, ordered, or licensed.

Core inspirations:

- `ThePeanoKushimEffect`
- `TheBaconEffect`
- `TheEuclidEffect`
- `TheMarconiEffect`
- `TheAdamsEffect`
- `TheAristotleEffect`
- `TheGalileoEffect`
- `TheKantEffect`
- `TheWittgensteinEffect`
- `TheCauseAndEffectEffect`
- `TheHumeEffect`
- `TheLaplaceEffect`
- `TheProverVerifierEffect`
- `TheHaltEffect`
- `TheAgentEffect`

Best Vol 4 use:

- claim labels as museum tags;
- reader's eye plates;
- record/no-record contrasts;
- "the dial is not the caption" sidebars.

### Resolution, Sampling, And The Continuum Fence

Use these when the book needs to explain why a finite instrument must not
pretend it owns the continuum.

Core inspirations:

- `TheBerkeleyGalileoEffect`
- `Precision`
- `Fluxions`
- `TheContinuumLimitEffect`
- `TheRichardsonEffect`
- `TheFourierNyquistEffect`
- `TheGibbsPhenomenon`
- `TheGibbsPreservationEffect`
- `TheLimitationOfIndexing`
- `ThePythagorasPlanckEffect`
- `CompactDiscEncoding`
- `TheFessendenShannonEffect`
- `TheMessageEffect`

Best Vol 4 use:

- pixel, mesh, and sampling plates;
- "about 137" as scale, not exactness;
- null/structural result explanations;
- captions that cool down over-precise visuals.

### Cost, Entropy, And Accounting

Use these when the book needs to make "cost" feel disciplined rather than
metaphorical decoration.

Core inspirations:

- `MaxwellsDemon`
- `TheThermodynamicCostOfErasure`
- `TheAmdahlEffect`
- `TheTailLatencyEffect`
- `TheIdealLedgerEffect`
- `TheEntropicCostOfAcceleration`
- `TheThermostatEffect`
- `TheConservationOfEnergy`
- `TheMomentumEffect`
- `TheAccelerationEffect`
- `TheNewtonEffect`
- `TheDaVinciCoulombEffect`

Best Vol 4 use:

- price marks;
- cost ledgers;
- "what must be paid for the operation to count";
- loop closure as total accounting.

### Geometry, Motion, And Frames

Use these when the book needs a visible frame, baseline, relative reading, or
return path.

Core inspirations:

- `TheVelocityEffect`
- `TheGalileoAbelEffect`
- `TheDescartesEffectCh03`
- `TheDescartesEffectCh08`
- `TheAngularMomentumEffect`
- `TheKeplerEffect`
- `TheMaxwellEffect`
- `TheMichelsonMorleyEffect`
- `TheEinsteinEffectCh02`
- `TheEinsteinEffectCh07`
- `TheEinsteinEffectCh08`
- `LiDAR`
- `TheRefinementEffect`
- `TheTimeEffect`
- `TheWhiteheadEffect`

Best Vol 4 use:

- denominator as whole route;
- frame-change visuals;
- relative baseline panels;
- reader orientation spreads.

### Fields, Matter, And Material Faces

Use these when the book needs concrete textures: matter, media, resistance,
domains, chemistry, and bulk response.

Core inspirations:

- `TheInverseSquareEffect`
- `TheBrownianMotionEffect`
- `TheAndersonEffect`
- `TheIsingEffect`
- `TheNavierStokesEffect`
- `TheQuicksandEffect`
- `TheArchimedesProustEffect`
- `TheStoichiometryEffect`
- `TheCelsiusLagrangeEffect`
- `TheFirstEffectOfGibbs`
- `TheSemiconductorEffect`
- `TheSuperconductingEffect`
- `TheMeissnerEffect`
- `TheStrongInteractionEffect`
- `TheSombreroPotential`
- `TheCasimirEffect`

Best Vol 4 use:

- material metaphors for phase face and cost;
- boundary plates;
- confinement, threshold, and resistance imagery;
- physical texture for otherwise abstract ratios.

### Gravity, Horizons, And Boundary Receipts

Use these when the book needs the reader to feel a boundary as an accounting
surface, not a decorative edge.

Core inspirations:

- `ThePoundRebkaEffectCh06`
- `ThePoundRebkaEffectCh08`
- `TheTrafficEffect`
- `TheDarkEnergyEffect`
- `TheSchwarzschildEffect`
- `TheEventHorizonEffect`
- `TheHawkingEffect`
- `HawkingRadiation`
- `HawkingRadiationRevisited`
- `TheWhiteHoleEffect`
- `TheTHooftSusskindEffect`
- `TheOlbersEffect`
- `TheFlatRotationCurveEffect`
- `ParadoxesOfTimeTravel`

Best Vol 4 use:

- horizon as a phase-like face;
- boundary receipt spreads;
- what can and cannot cross;
- structural landings that remain meaningful without a numeric miracle.

### Computation, Compilation, And Interfaces

Use these when the book needs to show an instrument that accounts for its own
operation without becoming a code-facing volume.

Core inspirations:

- `TheTuringEffect`
- `TheChaitinEffect`
- `TheVonNeumannEffect`
- `TheVonNeumannTrefethenEffect`
- `TheExcelEffect`
- `TheJupyterEffect`
- `TheNewtonCooleyTukeyEffect`
- `TheParetoEffect`
- `TheBayesEffect`
- `TheGossetEffectCh02`
- `TheGossetEffectCh07`
- `GaussFirstEffect`
- `ItoLemma`
- `MinimizingVariations`
- `RepeatabilityOfInvisibleMotion`
- `ImpliedOrthogonalityAndSpaceTime`
- `TheHilbertEffect`
- `TheHarmonicOscillator`
- `TheHarmonicOscillatorRevisited`

Best Vol 4 use:

- bench instrument as interface;
- self-accounting device captions;
- false precision warnings;
- model-vs-reading sidebars.

### Alpha-Adjacent Cautions

These are useful precisely because they can tempt overclaim.

Core inspirations:

- `TheAlphaDecayEffect`
- `ThePhotoelectricEffect`
- `TheComptonScatteringEffect`
- `TheYangMillsEffect`
- `TheStrongInteractionEffect`
- `TheNeutrinoEffect`
- `TheSpin12Effect`
- `TheCasimirEffect`

Best Vol 4 use:

- clarify that "alpha" in alpha decay is not the fine-structure constant;
- distinguish coupling strength from particle labels;
- distinguish visual analogy from derived Standard Model content;
- keep QED language reader-facing and fenced.

## Drafting Rule

Before drafting a chapter after Chapter 03, choose at least three experiment
inspirations from this atlas:

1. one primary plate inspiration;
2. one sidebar or caption inspiration;
3. one cautionary or fence inspiration.

For each chosen experiment, read its `description.md`; read its `Experiment*.lean`
files whenever a caption, threshold, mechanism, or claim boundary needs exact
detail. Record those choices in `draft_status.md` after each batch, along with
any code files consulted. This keeps the coffee-table book fed by the whole
experiment corpus without letting any single experiment hijack the alpha spine.
