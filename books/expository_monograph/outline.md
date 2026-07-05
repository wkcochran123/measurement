# Measurement — Outline (6-Act Reframe)

*Supersedes the 7-part outline (in git history). The body (Ch1–32) is already written, gated, and
building (275pp); this reframes the ARCHITECTURE into six acts around the construction's round-trip.
Chapters keep their content; they regroup into acts, gain six short act-openers, and two chapters
(Ch13, Ch19) gain the loop-closing touches noted below. Owned by Kodo; Podo verifies against the code.*

## The architecture: a rise and a return (the loop)
The construction is a **closed loop**, and the book should read as one.
- **Ascent (Acts I–III).** From the bare difference — `DISTINGUISHABLE`, telling two things apart, the
  first *tange* (Ch1) — the apparatus climbs the self-bootstrap tower, points at its own truth (`Prop`)
  where the distinction **collapses** (true=false, Ch8, the APEX), and that collapse's residue is the
  **single invariant** (Ch13, the SUMMIT).
- **Descent (Acts IV–VI).** The invariant is read back *down* as matter — the **electron is the bare
  difference returned** (`DISTINGUISHABLE` over `Prop`, charge −1 = the residue of the self-tange the
  apex collapsed, Ch19); then the **outside reading** restores the distinction the apex lost
  (true≠false at the boundary, Ch28 — the apex's mirror); and the loop closes by **handing the bare
  difference back to the reader** (Ch32).
- The book **starts and ends on `DISTINGUISHABLE` / the order `≤`.** Ascent = the covariant climb
  (accumulate the tower); descent = the contravariant return (decide-against, re-read over `Prop`) —
  the same covariant/contravariant Cohen-forcing spine, now at book scale.

## Stance & vocabulary (carried forward, unchanged)
- **Math + science.** No proof-assistant / elaborator / Lean / "axiom of choice" in the body. The
  *instrument* is shown through the historical experiments (`device/Experiments/*`), discussed not coded.
- **tange** = select by a decidable characteristic; **funge** = pool by a characteristic. The two acts
  the axiom of choice only posits — here CONSTRUCTED, because decidable. The construction **is Cohen
  forcing** (finite conditions approaching the generic); named only at Ch22. The one granted step =
  **genericity** (Ch10; "the approached is reached"), carried unchanged to Ch32.
- Each chapter closes with **"what is demonstrated / what is assumed."** Physics names fenced as shapes.
- Front matter: **empty** (TBD per operator). **No Coda.** Appendices TBD.
- **Meanwhile17.lean is a STORYTELLING GUIDE for the loop (the backward walk + ELECTRON), NOT rigorous
  code yet (its bodies are `sorry`).** Use it for the narrative shape; verify the math against the
  rigorous Episodes (Ep1–93). Podo: you already know this — flagged for the record.

---

# ACT I — The First Difference (Ch1–4)  ·  ascent: the atom
*Loop role: establish the bare difference (telling apart = the first tange) and the first faculties the
whole arc is built from and returns to.*

- **Ch1 — Number from a Fact (Ep1).** Fact = proposition + decision; three truth-symbols → same/different;
  number as signed binary; the carrier; **DISTINGUISHABLE = the first tange** (telling carriers apart).
  Anchors: `Fact`, `inductive Number`, `Number.le`, `CarrierProcess`, `class DISTINGUISHABLE`.
  Exp: Berkeley-Galileo, Hume, Euclid, Peano-Kushim. *Loop: the bare difference the arc returns to.*
- **Ch2 — The number tower up to the reals (Ep1).** Naturals (covariant accumulation) → the **cut**
  (contravariant: tange the trues, funge the falses) → reals; the continuum approached, never seized.
  Anchors: `Natural/Rational/Sequence/Limit`, `CauchyProcess`, `class ADMISSIBLE/COUNTABLE/ENCODED/RESIDUE`,
  `Sample`. Exp: Adams, Archimedes-Proust, Fessenden-Shannon, Fourier-Nyquist, Celsius-Lagrange.
  *Loop: the cut is the first contravariant act; tange/funge introduced as the two acts.*
- **Ch3 — Time, the trial, the study (Ep2).** Clock complement, the repeatable trial, the study, Hume on
  cause, the operational second. Anchors: `ObservationProcess`, `class BINARY`, `Trial/Study`,
  `RepeatableProcess`, `class REPEATABLE/NUMERIC`. Exp: Einstein(clock), Dirichlet-Bancroft, Galileo-Abel,
  Cause-and-Effect.
- **Ch4 — Computation, representation, the Chaitin barrier (Ep3).** Turing process; Chaitin barrier;
  machine epsilon; noise as the same process as signal; friction as the curvature term. Anchors:
  `Computation/TuringProcess`, `class REPRESENTABLE/PHYSICAL/COMPARABLE/OBSERVED`, `ChaitinsNumberSequence`,
  `Metavariable`, `Sophism`. Exp: Chaitin, Turing, DaVinci-Coulomb, Laplace.

# ACT II — The Apparatus Reads Itself (Ch5–8)  ·  ascent → THE APEX
*Loop role: the climb completes; the apparatus points at its own truth (`Prop`) and the distinction
collapses (true=false). The turn at the top.*

- **Ch5 — Gauge, superposition, the local present (Ep4).** Local present; the gauge that negotiates the
  lag; superposition + the imaginary unit; correlation. Anchors: `class PRESENT/MEASURABLE/GUNGAN`,
  `Phenomenon/GaugeProcess`, `Jar/MeesaProcess`. Exp: Heisenberg-tradeoff, Malus, Mach-Zehnder,
  Qubit-Decoherence, Maxwell. *(physics fenced)*
- **Ch6 — A stored-program computer from the Fact (Ep5).** Binary digit + exclusion (the excluded state =
  the neutrino); the digital process; opcodes/compilation/execution; abstraction (anti-self-reference).
  Anchors: `Equivalation`, `DigitalProcess`, `class SOURCE/EXECUTED`, `Encoding/CompiledProcess`,
  `Abstraction`. Exp: Fluxions, Neutrino, Repeatability, Gibbs-Preservation, VonNeumann.
- **Ch7 — Arithmetic, linear algebra, Galerkin, splines (Ep6–7).** Values/addition; multiplication/
  orthogonality (the vacuum/antimatter flip); basis/nullspace/BASIC machine; Galerkin + **splines as
  first/second variation** (the Part-III/Act-III seed). Anchors: `class VALUE/MAGNITUDE/SCALED/LOAD/
  FINITE_ELEPHANT`, `Sum/Product/Basis/Polynomial/Spline`, `GalerkinProcess`. Exp: Gauss-First,
  Newton-CooleyTukey, Harmonic-Oscillator, Kepler, Ito.
- **Ch8 — The self-bootstrap and the first theorem (Ep8–16).** The tower inhabits itself (the instance
  chain — **funge the rungs into one seed-inhabited instance; each step tanges a witness**); the apparatus
  extends (SCIENTIFIC…COMPILED + the **compiler tape**); it points at `Prop` (`truthCarrier`) and returns
  its first theorem — **true=false** as proof-irrelevance/subsingleton, the same/different collapse.
  Anchors: Ep8 instance chain, Ep9–14 (`SCIENTIFIC/TRUTH/WITNESSED/REAL/LOCAL/UNIVERSAL/LOGICAL/HALTED/
  MEASURED/COMPILED`, `CompilerTape`), Ep15–16 (`truthCarrier`, `theorem true_eq_false`). Exp: Precision,
  Prover-Verifier, Bacon, Bayes, Halt. **≪ APEX: the apparatus reads its own truth; the distinction
  collapses. The turn of the loop. ≫**

# ACT III — The Single Invariant (Ch9–13)  ·  THE SUMMIT
*Loop role: the climb's peak — the invariant the collapse's residue yields. The contravariant engine
returns. Ch13 reaches it FOUR ways, the fourth closing the loop.*

- **Ch9 — Stationarity and the first variation (Ep17–18).** Finite gauge action; stationary/flat/
  closed-flat; the first variation as an exact difference. **Contravariant engine returns:** tange the
  stationary paths by "flat here"; funge the flat directions into the kernel. Anchors: `FiniteGaugePath/
  Action`, `flatAt_stationaryAt`, `FiniteGaugeVariation`, `firstVariation_eq_composedDifference`.
  Exp: Harmonic-Oscillator, Minimizing-Variations, Implied-Orthogonality.
- **Ch10 — The Euler–Lagrange equivalence (Ep19).** Equivalence proved (i); the **one granted step =
  genericity** (the universal over infinitely many directions is *decided* = the law of motion; NOT "the
  axiom of choice"). Anchors: `DiscreteGaugeDerivative`, `stationary_iff_eulerLagrange`, `…residue`.
  Exp: Minimizing-Variations. *The book's single load-bearing assumption, named here.*
- **Ch11 — Solving it: splines, Lanczos, partitions (Ep20–26).** Cubic-spline sufficiency; Lanczos (funge
  the knots / tange them out; termination PROVED, "any order → same residue" GRANTED not proved); real
  partitions + finite frame; **the mixed coupling carried whole (the Ch13 seed)**; selection by cost.
  Anchors: `LanczosCubicSpline`, `SlipMultiset/Consumes`, `RealPartition/FiniteElephant`, `CubicGaugePath`,
  `coupledCubicDifference_eq_left_right_plus_mixed`, `HeartbeatSelector`. Exp: Fourier-Nyquist, LiDAR,
  Shadow-Tomography, Limitation-of-Indexing, cost cluster (Amdahl/TailLatency/Thermodynamic-Erasure).
- **Ch12 — Convergence and the Sobolev energy (Ep27–30).** The squeezed residual + Weierstrass completion
  (the generic approached up to ε); the SPD energy detects zero; **definiteness EARNED** (the boundary
  anchor kills the constant/affine nullspace). Anchors: `PointwiseSqueezedResidual`, `GalerkinBilinearForm`,
  `SPDGalerkinActivity`, `positive_definite_of_nullspaceKilled`. Exp: Refinement, Continuum-Limit,
  Richardson, Gibbs.
- **Ch13 — The second variation IS the single invariant (Ep31).** The title theorem — one object reached
  now **FOUR ways**: (1) the mixed coupling; (2) the unique quadratic remainder; (3) the SPD energy
  magnitude; and **(4 — NEW, loop-closing) the bare difference over `Prop`** — `DISTINGUISHABLE`
  self-applied (Meanwhile17 `SECOND_VARIATION : DISTINGUISHABLE Prop`): the invariant *is* the first gate
  turned on the apparatus's own truth. Anchors: `secondVariation_eq_mixedCubicCoupling`,
  `secondVariation_remainder_unique`, `diagonal_secondVariation_magnitude_eq_energySq`,
  [Meanwhile17 `SECOND_VARIATION`]. Exp: Harmonic-Oscillator, Conservation-of-Energy. **≪ SUMMIT ≫**

# ACT IV — The Descent into Matter (Ch14–22)  ·  the fall begins
*Loop role: the invariant read downward as matter; the electron is the bare difference RETURNED; the
construction recognizes itself as Cohen forcing.*

- **Ch14 — One result, two proofs; the evaluated middle (Ep32–33).** Anchors: `coupledZeroByMixed_eq_…`,
  `middle_exists/unique`. Exp: Ideal-Ledger.
- **Ch15 — The first real stiffness operator (Ep34–37).** Three-node mass+stiffness; the anchor earns
  definiteness; discrete Poincaré; joins the residual tower. Anchors: `Rung3`, `aMS_*`, `chain_poincare`,
  `threeRung_supported_…`. Exp: Anderson, Thermostat.
- **Ch16 — The √-door and the Universe Kernel (Ep38–39).** Norm = √energy → the Hilbert completion door
  (marked, not crossed); the Universe Kernel binds the invariant to charge / **color / flavor — which are
  CARRIED, not observable values** (color a `CarrierProcess`, flavor a `TrueOutput`; only charge/phase are
  read off). Anchors: `RealScaleField/HilbertCompletionDoor`, `Color/Flavor/QPhase`, `UniverseKernel`.
  Exp: Hilbert, Inverse-Square, White-Hole. **[FIX: Ch16 currently calls color/flavor "labels read off a
  finite set" — reframe as carried-but-unobservable, the honest shape of confinement.]**
- **Ch17 — Grounding; metaphysical vs physical (Ep40–43).** Grounded on the operator; apparatus-relativity
  (metaphysical iff no apparatus realizes it); the **funge/crank partition**; the first record. Anchors:
  `funges_and_cranks_partition`, `MetaphysicalRelativeTo`, `first_record`. Exp: Wittgenstein, Kant,
  Topological-Integer-Count.
- **Ch18 — The integrator and the produced certificate (Ep44–51).** Reads zero at a solution; Weierstrass
  by instantiation; the boundary a build artifact; the certificate PRODUCED. Anchors: `gaugeReading`,
  `eventuallyZero_tendsToZero`, `no_uniform_support`, certificate. Exp: Laplace, Ideal-Ledger.
- **Ch19 — The electron is the second variation (Ep52).** **≪ THE RETURN ≫** The electron = the **bare
  difference (`DISTINGUISHABLE`, Ch1's first gate) re-read over `Prop`** — its charge **−1 is the residue
  of the self-tange the apex collapsed (Ch8).** Positron = +1 (reversed orientation); matter/antimatter =
  sign of the mixed coupling; color/flavor carried not observable. **Hardest definition-vs-modeling fence**
  (electron = a name on a value, not a derived particle). Hilbert's sixth: two axioms (`propext` + the
  quotient, plain terms) + the one grant, **choice-free**. Anchors: `electron_is_the_secondVariation`,
  `electron_charge/positron_charge`, `residue_is_the_difference_between_story_and_measurement`,
  `hilberts_sixth_on_the_vacuum`, [Meanwhile17 `ELECTRON_MODEL`]. Exp: Positron-Annihilation (exemplar),
  Chirality, Dirac, Spin12. **[TOUCH: tie explicitly to Ch1 (the first gate) and Ch8 (the collapse) — the
  first difference come home.]**
- **Ch20 — Geometry generates the gauge (Ep53–55).** Geometric program → boundary compiler → the electron;
  the C²-certified QED program. Fence: gauge/QED = shapes ("two shadows and one door"). Anchors:
  `GeometricProgram`, `BoundaryGaugeCompiler`, `GeneratedQEDProgram`. Exp: Aharonov-Bohm, Feynman, Yang-Mills.
- **Ch21 — The split and boundary radiation (Ep56–58).** Geometric/gauge split; the Clifford shadow; mixed
  terms vanish in the interior → radiation is a BOUNDARY phenomenon; the flat vacuum certificate. Fence:
  radiation/Clifford = shapes. Anchors: `SplitCarrier`, `CliffordShadow`, `boundary_radiation_finite`,
  `flatPairCompleted`. Exp: Hawking, Schwarzschild, Casimir, THooft-Susskind.
- **Ch22 — QED as a limit of GR; counting to three; finite Cohen (Ep59–61).** QED Cauchy-converges as the
  GR ε vanishes; 1+1+1=3; **Cohen forcing NAMED** — the construction recognizes itself (finite conditions,
  the generic up to ε; tange/funge = the two acts of a condition). Anchors: `qed_cauchy_convergence…`,
  `one_add_one_add_one_eq_three`, `SplineCondition/FiniteCohenUpToEpsilon`. Exp: Cantor-Godel-Cohen.

# ACT V — The Outside Reading (Ch23–28)  ·  the apex's mirror
*Loop role: read from the frame; the distinction the apex collapsed (true=false) is RESTORED at the
boundary (true≠false). The descent's mirror of Act II.*

- **Ch23 — The finite Cohen ledger is countable (Ep62–64).** Conditions up to content; Gödel-code to ℕ; the
  gauge commutator residue closes. Anchors: `SameAtoms/merge_extensional`, `code`, `splineCondition_…_
  countable`, `…commutator_residue_theorem`. Exp: Cantor-Godel-Cohen.
- **Ch24 — The Sobolev–Hilbert completion door (Ep65–72).** Completion **built, not imported** — the one
  residual is the same **genericity** grant (Ch10) "wearing its completion-shaped coat"; the finite
  structure lifts; boundary trace = terminal residual; the generalized continuum boundary-radiation
  theorem. Anchors: `SobolevHilbertDoor`, `finiteResidualMapsIntoCompletion`, `boundaryTrace_agrees_with_
  terminal_residual`, `generalized_boundary_radiation_continuum`. Exp: Hilbert, Continuum-Limit.
- **Ch25 — The orientation EKG (Ep73–74).** Matter/antimatter ±1 cancel (axiom-free); the convention anchor
  selects the dominant sign; reciprocal accounting. Anchors: `orientationReading_electron/positron`,
  `ConventionAnchor`, `reciprocalAccounting_truth_parity_surface`. Exp: Topological-Integer-Count, Chirality.
- **Ch26 — The outside reading: the invariant as a boundary obstruction (Ep75).** The interior second
  variation (the electron, −1) read from OUTSIDE = the **Navier–Stokes / Einstein boundary obstruction**;
  error code −1, signal on. **The −1 inside = the −1 outside — one invariant, two readings (interior/frame).**
  Fence: NS/Einstein = shapes (the Millennium problem explicitly disclaimed). Anchors:
  `threeRung_boundary_secondVariation_eq_electron`, `threeRung_einstein_field_equations_hold`,
  `threeRung_navierStokes_balance`, `errorCode = -1`. Exp: Navier-Stokes (Ep75), Hawking, Event-Horizon,
  Flat-Rotation-Curve.
- **Ch27 — The sentence the interior cannot settle (Ep76–77).** A Gödel-style proof-language sentence that
  reads the obstruction the interior can't decide; a second, indexed by `succ succ`. Anchors:
  `ProofLanguageSentence`, `class DISTINGUISHED`, `distinguished_godel_sentence_reads_obstruction`,
  `secondGodelIndex_is_succ_succ`. Exp: Prover-Verifier, Wittgenstein, (entanglement: Bell/Spooky/EPR).
- **Ch28 — true≠false at the boundary; how much you want (Ep78–81).** **The distinction the apex collapsed
  RESTORED at the boundary** — the boundary tanges apart what the interior funged; "not a reversal of the
  collapse but its completion." The reader chooses depth (De Morgan on the on/off signal); one bit is
  enough; QED⊥GR. Anchors: `Fact.FALSE`, `true_neq_false`, `inferred_closed`, `RecursionStopRule`,
  `qed_perp_gr`, `binary_is_enough`. Exp: Aristotle-DeMorgan, Positron-Threshold. **≪ MIRROR of the apex ≫**

# ACT VI — The Return to the Reader (Ch29–32)  ·  the loop closes
*Loop role: the bare difference, and the whole apparatus, handed to the reader. The loop closes on
`DISTINGUISHABLE` / the order / the reader.*

- **Ch29 — Relative velocity is a selection: the single quotient (Ep82).** Relative velocity = whole −
  parts, taken as the **quotient (funge) by observational equivalence**; the measurement and invariant
  routes agree through one quotient (`Quot.sound`, named plainly as "the quotient"). Anchors:
  relative-velocity, `Quot.sound`. Exp: Michelson-Morley, Sagnac, Galileo-Abel.
- **Ch30 — Matter/antimatter is baseline-relative (Ep83–85).** The baseline-relative flip; charge lives on
  a loop (holonomy); the split counted. Anchors: baseline/holonomy sign, funge counter. Exp: Chirality.
- **Ch31 — The gauge as a bit-vector (Ep86–90).** The gauge = the hypercube of gate bits; the funge counter
  (funge = matter, crank = antimatter); the measurement = a population count — **back to the binary atom
  of Ch1/Ch6.** Anchors: bit-vector/hypercube, funge counter. Exp: Message.
- **Ch32 — The close: only `≤`, the band, the reader (Ep91–93).** Only the order survives as primitive
  (strict order + charge read off it); the under/in/over band (proved complete); **the reader = the final
  apparatus** the construction cannot build, only address. Anchors: `≤` primitive / strict order, the band
  (under/in/over), the reader. Exp: Pareto, Refinement. **≪ THE LOOP CLOSES: the book ends on the bare
  difference / the order it began with; the reader receives what the first difference began. ≫**

---

## Verification notes for Podo
- Verify each chapter's **anchors against the rigorous Episodes** (`device/Measurement/Episode*.lean`) —
  flag any anchor that has drifted/renamed.
- **Meanwhile17.lean is the storytelling guide for the loop, not verified math** (its bodies are `sorry`;
  it has a known `AUDIOPHILE`/`FINITE_ELEPHANT` duplicate and a live `structure ELECTRON` ↔ `instance
  ELECTRON_MODEL` edit). Use it for the round-trip narrative (ascent/apex/summit/descent/mirror/return)
  and the electron's structure; do NOT cite it as proof.
- The two loop-closing touches (Ch13 fourth identity; Ch19 electron = first gate returned) depend on the
  `SECOND_VARIATION : DISTINGUISHABLE Prop` identity being borne out when Meanwhile17 is made rigorous —
  flag it as "asserted in the storytelling layer, pending rigorous form" until Ep15+/Meanwhile17 compile.

## Experiment mapping
Per-chapter experiments are listed inline above (reorganized by act). Source-grounding: each experiment
carries a `Source: instrument/chapters/NN.tex` tag; ~119 of 139 placed, ~20 still need a read to place
(unchanged from the prior mapping). Discuss the experiment; never show its code.
