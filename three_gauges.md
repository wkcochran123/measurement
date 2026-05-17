# The Three Gauges Project

## What a Gauge Is

A gauge is the device that explains the reading. A speedometer does not just
display a number — it provides the framework that makes the number mean
something. Three gauges can measure the same underlying reality and each one
tells a true, complete, and different story.

The current manuscript (gauge.pdf) was generated in a single ChatGPT prompt
through a collaboration of six LLMs. It is thorough and muddled in equal
measure — thorough because it contains everything, muddled because it tries
to be all three gauges simultaneously. It serves as the source document for
this project: the skeleton is right, the arc is right, the chapter boundaries
are roughly right. The flesh needs to know which body it is on.

---

## The Four Books

Three technical gauges plus one companion register. The satire is not a
fourth gauge competing with the three — it is a different kind of artifact
entirely: a manga.

### Book 1 — The Mathematical Gauge
*How calculus, geometry, and topology emerge as orderings on sets.*

Audience: mathematicians and logically-minded readers comfortable with
abstraction. Argument: if you start with sets and a relation that orders them,
and add only what consistency forces, the full apparatus of analysis —
derivatives, integrals, metrics, curvature, fiber bundles — appears
necessarily. Nothing is constructed by hand. Everything is forced.

The Lean formalization is cited as verification. The code is not the book.

---

### Book 2 — The Physical Gauge
*How physical measurement works.*

Audience: physicists, scientifically curious readers, anyone who has wondered
why the laws of physics take the form they do. Argument: physical laws are not
imposed on nature. They are the unique descriptions consistent with finite,
distinguishable measurement records. The speedometer book. The closest thing
to what gauge.pdf currently is.

The Lean code is backstage. The physics is the foreground.

---

### Book 3 — The Algorithmic Gauge
*The computation the compiler is building.*

Audience: people who think about what computation means for the nature of
reality — the Hofstadter/Penrose/Chaitin readership. Argument: the admissible
record forces identifiable algorithmic forms (bisection, divide and conquer,
inversion, enumeration, union/find), while the selection rule requires exact
Kolmogorov information and is therefore not simulable by a general Turing
procedure. This is the most metaphysical of the three books. The universe
cannot be simulated because the selection principle is noncomputable.

The Lean code is not implementation detail — it is the primary artifact.
The algorithms in the code are the argument.

---

### The Satire — The Manga
*The compiler that learned to measure the universe.*

Format: manga. Not a fourth technical register — a documentary in panels.

The character design problem is solved: the compiler is the AI assistant
that helped write the Lean code. The human is at the keyboard. The AI is on
screen. The physics appears in the panel space between them. The ledger is
the conversation window. The events are the exchanges.

The comedy is already written: the AI confidently formalizes something,
the physics reveals a gap, they try again. That loop — which actually
happened during the construction of gauge.pdf — is the plot. The satire is
not fictional. It is a documentary of what occurred, rendered in panels.

The noncomputable punchline: the AI, itself a computational system, cannot
implement the noncomputable selection principle. The compiler trying to
formalize a rule it cannot execute is not a metaphor — it is what happened.
The manga ends with an open Lean file, a blinking cursor, and the definition
of the minimal admissible interpolant left as `sorry`.

Book 3 and `GAUGE 1199` are the most tightly coupled pair: Book 3 is the
technical manual, the manga is the dramatization of what the manual describes.

---

## Source Hierarchy

```
gauge.pdf                       ← source manuscript (nine chapters; all content)
three_gauges.md                 ← extraction and architecture plan (this file)
device/Measurement/*.lean       ← formal artifact; primary for Book 3
instrument/chapters/*.tex       ← LaTeX source; primary for Books 1 and 2
[future book drafts]            ← audience-specific rewrites from the above
```

gauge.pdf contains nine chapters. The three-book plan has eleven. The
migration table below governs the expansion.

---

## Migration: gauge.pdf → Eleven-Chapter Plan

This is a rough correspondence, not a rigid transfer. Many gauge.pdf
chapters seed multiple plan chapters. The plan expands chapters that carry
too much freight in the source.

| gauge.pdf chapter | Best destination(s) in plan |
|---|---|
| Preface + Ch 1, "The Fact" | Plan Ch 1 (Record); also Book 3 framing |
| Ch 2, "The Number Ladder" | Plan Ch 1–2 (Record and Comparison) |
| Ch 3, "The Ledger's Permissions" | Plan Ch 2–4 (Comparison, Phenomena, Structure) |
| Ch 4, "The Signal" | Plan Ch 3–4 (Phenomena and Structure); gauge material seeds Ch 8 |
| Ch 5, "The Tower" | Plan Ch 4–6 (Structure, Distance, Motion) |
| Ch 6, "The Bullshit Meter" | Plan Ch 6 and Ch 11; also Book 3 core |
| Ch 7, "The Science" | Plan Ch 7 (Transport) and epistemology bridge |
| Ch 8, "The Physics" | Plan Ch 7–10 (Transport, Stress, Strain, Symmetry) |
| Ch 9, "The Closure" | Plan Ch 11 (Entropy/Closure) and Book 3 finale |

---

## Calibration as Spine

The calibration concept runs through all three books and through the Lean
code. A reading without a named reference is not a reading at all.
Calibration is performed before the measurement; it is carried into
measurement as a certificate.

In the Lean code:
- `Calibration/LeanCalibration.lean` holds the hidden reference:
  `private structure Reading where heartbeats : Nat`
- The public surface is `Prop`-valued through `EKG` methods. The `Nat`
  does not leak into episodes.
- `LOGICAL` holds `ekg : Calibration.EKG` — the calibration certificate.
- `.load` initializes the baseline. `.boolean` reads it.
- `.boolean` and `.transform` can be compared only through calibration.
- `.boolean, .transform` is an explicit incomparability shape.

In each book:
- Mathematical gauge: calibration is the certificate that names the
  reference before a comparison is admissible.
- Physical gauge: calibration is the instrument's external reference
  standard (you calibrate before you measure — always).
- Algorithmic gauge: calibration is the load/boolean interface; the
  hidden `Nat` is the runtime cost the program cannot inspect directly.

---

## Gaps to Acknowledge in All Three Books

1. **Kolmogorov closure is not implemented.** The code has Chaitin/halting
   structure and heartbeat cost proxies. It does not implement K(·) directly.
   Do not claim it does. Present Ch 6 of Book 3 as the place where
   approximate K lives and exact K is shown to be unreachable.

2. **Standard Model machinery does not yet exist in the code.** Lie groups,
   U(1), SU(2), SU(3), Dirac, and Standard Model structures are described
   in the plan for Ch 10 but are not in the Lean files. Present Ch 10 as
   the place where that code must eventually grow.

---

## Shared Infrastructure vs. Shared Prose

Chapters 1–2 and portions of 3–6 share conceptual infrastructure.
They do not share sentences.

- The mathematical reader wants theorem/proof pressure.
- The physical reader wants instrument/phenomenon pressure.
- The algorithmic reader wants data-structure and compiler pressure.

The chapter introductory essays (~1500 words each) differ most sharply
across the three books. The formal sections share the most. Each chapter's
closed question (below) is the minimum shared unit — all three books must
close the same question, but in their own register.

---

## Common Chapter Structure

Each book covers eleven areas in the same order. Each chapter is governed
by one closed question that must be answered before the next chapter begins.

| Ch | Area | Closed Question |
|----|------|----------------|
| 1 | **The Record** | What is the smallest admissible mark a ledger can carry? |
| 2 | **Comparison** | How can an instrument compare records and repeat the result without pretending the comparison is the thing measured? |
| 3 | **Phenomena** | What can be said about the gap between recorded events without inventing structure not in the ledger? |
| 4 | **Structure** | How do multiple records combine without collapsing into one undifferentiated record? |
| 5 | **Distance** | How does a finite count of distinctions become an admissible notion of distance? |
| 6 | **Motion** | What selects one admissible continuation as the history actually carried forward? |
| 7 | **Transport** | How can information move between histories while preserving admissibility? |
| 8 | **Stress** | What reference structure lets distinct observers compare their counts as one physical record? |
| 9 | **Strain** | What records the failure of transport to commute? |
| 10 | **Symmetry** | What remains invariant under admissible relabeling or recompilation? |
| 11 | **Entropy** | Why does the record only grow, and when is it closed enough to support inference? |

---

## Lean Anchors by Chapter

These are the Lean names that carry each chapter's content. The algorithmic
book indexes to these directly. The other two books cite them as
verification.

### Ch 1 — The Record
`Episode1.lean`: `Fact`, `Fact.Truth`, `Number`, `Number.le`,
`CarrierProcess`, `DISTINGUISHABLE`, `Natural`, `CountingProcess`,
`ADMISSIBLE`, `Rational`, `IndexingProcess`, `COUNTABLE`, `Sequence`,
`LimitProcess`, `ENCODED`, `Limit`, `CauchyProcess`, `RESIDUE`, `Sample`

### Ch 2 — Comparison
`Episode2.lean`: `ObservationProcess`, `BINARY`, `Trial`, `Trial.le`,
`Trial.lt`, `RepeatableProcess`, `REPEATABLE`, `Study`, `Study.le`,
`ComputationalProcess`, `NUMERIC`

### Ch 3 — Phenomena
`Episode3.lean`: `Computation`, `TuringProcess`, `REPRESENTABLE`,
`ChaitinsNumberSequence`, `NoisyProcess`, `PHYSICAL`, `Metavariable`,
`PhysicalProcess`, `COMPARABLE`, `Sophism`, `SlipProcess`, `OBSERVED`,
`Area`; `Episode4.lean`: `Phenomenon` (name introduced here, proved in Ch 5)

### Ch 4 — Structure
`Episode4.lean`: `Area`, `SensingProcess`, `PRESENT`, `Phenomenon`,
`Phenomenon.le`, `GaugeProcess`, `MEASURABLE`, `Jar`, `MeesaProcess`,
`GUNGAN`; `Episode5.lean`: `Equivalation`, `DigitalProcess`, `SOURCE`,
`Encoding`, `CompiledProcess`, `EXECUTED`, `Abstraction`

### Ch 5 — Distance
`Episode6.lean`: `MathematicalProcess`, `VALUE`, `Sum`, `AddingProcess`,
`MAGNITUDE`, `Product`, `MultiplyingProcess`, `SCALED`, `Basis`,
`BASICProcess`, `LOAD`, `Polynomial`, `GalerkinProcess`, `FINITE_ELEPHANT`,
`Spline`, `Spline.le`

### Ch 6 — Motion
`Episode6.lean` (reuse `GalerkinProcess`, `Spline`, `FINITE_ELEPHANT`);
`Episode7.lean`: `ArmWaveProcess`, `BULLSHIT`, `Diatribe`, `CrusadeProcess`,
`PROPAGANDA`, `Cult`, `InitiationProcess`, `ACOLYTE`;
`Episode3.lean`: `ChaitinsNumberSequence` (halting boundary — seed for
noncomputable selection); `Calibration/LeanCalibration.lean`: `EKG`

### Ch 7 — Transport
`Episode8.lean`: instance cascade `STEP_1` through `ACOLYTE_PROPAGANDA`;
`Episode9.lean`: `Science`, `LearningProcess`, `SCIENTIFIC`, `Knowledge`,
`Knowledge.le`, `ScientificProcess`, `TRUTH`, `Gospel`, `ReligiousProcess`;
`Episode10.lean`: `WITNESSED`

### Ch 8 — Stress
`Episode10.lean`: `Truth`, `Truth.le`, `UniverseTensor`, `REAL`,
`Variation`, `BigRedDogProcess`, `LOCAL`;
`Calibration/LeanCalibration.lean`: `EKG` (calibration as hidden reference
scale with Prop-only public questions)

### Ch 9 — Strain
`Episode11.lean`: `SpaceTimePath`, `SpaceTimePath.le`, `CalculusProcess`,
`UNIVERSAL`, `YarnTheory`, `YarnTheory.le` (`stokes`, `fibers`, `fabric`),
`HeartbeatProcess`

### Ch 10 — Symmetry
`Episode12.lean`: `LOGICAL`, `ComputerProgram.le`, `ElaborationProcess`,
`HALTED`; `Episode13.lean`: `Measurement`, `Measurement.le`, `LeanProcess`,
`MEASURED`; `Episode14.lean`: `CompilerTape`, `CompilerOutput`, `COMPILED`

### Ch 11 — Entropy
`Episode15.lean`: `Bullshit`, `Bullshit.le`, `Bullshit.lt`, `AtreyuProcess`,
`TrueOutput`, `truthCarrier`, `DISTINGUISHABLE_PROP`, `truthDistinct`,
`Fact.SAME`, `Closure`, `Closure.le`, `EquivalenceProcess`, `INFERRED`,
`INFERRED_TRUE`, `theory_true?`

---

## Book 1 Outline — The Mathematical Gauge

**Working title:** *Order*
**Subtitle:** How Calculus, Geometry, and Topology Emerge from Orderings on Sets
**Claim:** The full apparatus of modern analysis is forced by the minimum
consistent structure on an ordered set. Nothing is assumed beyond a set and
a relation. Everything else is necessary.

---

**Ch 1 — Ordered Sets**
*Closed question: What is the smallest admissible mark a ledger can carry?*

- What a set is; what a distinction is; what a partial order is
- The refinement relation as the primitive ordering of the theory
- The ledger as a partially ordered set of distinguishable events
- `Number.le` as the mathematical statement: order enters as proposition
- `CarrierProcess`: a value is never naked; it arrives with a carrier
- Key result: any consistent record of distinguishable events is a poset

**Ch 2 — The Algebra of Comparison**
*Closed question: How can an instrument compare records and repeat the result
without pretending the comparison is the thing measured?*

- How the ordering generates a meet-semilattice
- `Trial.le`, `Trial.lt`: comparison as structured partial order
- `REPEATABLE`: a comparison becomes repeatable only after the process
  can carry prior observation
- Three representations of the same comparison — algebra of order
- Key result: the algebra of admissible comparisons is a distributive lattice

**Ch 3 — The Topology of the Gap**
*Closed question: What can be said about the gap between recorded events
without inventing structure not in the ledger?*

- The Alexandrov topology: open sets defined by the refinement order
- `REPRESENTABLE`, `PHYSICAL`, `COMPARABLE`: boundaries on what can be said
- `ChaitinsNumberSequence`: the halting boundary as a typed limit
- The Moment as topological shadow of an interval
- Key result: the Alexandrov topology of the refinement order is the
  minimal topology consistent with the causal structure

**Ch 4 — The Algebra of Records**
*Closed question: How do multiple records combine without collapsing into
one undifferentiated record?*

- Comparability and correlance as algebraic relations between posets
- `GaugeProcess`, `MEASURABLE`: a record becomes measurable only when the
  gauge process can be carried
- `SOURCE`, `EXECUTED`, `Abstraction`: staging preserves identity
- Key result: the category of admissible records is a symmetric monoidal
  category with the refinement order as morphisms

**Ch 5 — Analysis from Ordering**
*Closed question: How does a finite count of distinctions become an
admissible notion of distance?*

- The C² constraint: why continuity through second derivative is forced
  (breaks would be observable events)
- The degree-counting argument: 4 C² constraints, 4 cubic coefficients —
  the cubic is the unique degree exactly determined by the data
- `GalerkinProcess`, `FINITE_ELEPHANT`: the weak form and stopping rule
- `Spline.le`: spline as the finite smooth continuation
- Key result: the unique minimal analytic continuation consistent with a
  finite ordered record is a C² cubic spline

**Ch 6 — Variational Calculus**
*Closed question: What selects one admissible continuation as the history
actually carried forward?*

- Kolmogorov complexity as the measure of informational content
- `ChaitinsNumberSequence`: the halting boundary as the seed of
  noncomputable selection — introduced here, explored fully in Book 3
- The dense limit: differentiability as the limit of discrete minimality
- The Spline Condition: Ψ^(4) = 0 as forced Euler-Lagrange
- Galerkin convergence: splines converge to the Euler-Lagrange solution
- Key result: the Euler-Lagrange equation is the continuous shadow of
  discrete informational extremality

**Ch 7 — Connections and Transport**
*Closed question: How can information move between histories while
preserving admissibility?*

- The clock as a totally ordered sub-poset with unique successor refinement
- The interaction operator as Martin-consistent extension
- Martin's Axiom: every countable family of local choices admits a
  globally consistent selection
- `WITNESSED`: witness structure as mathematical certificate
- Parallel transport as the rule for comparing refinement counts
- Key result: a connection on the category of admissible records is a
  Martin-consistent interaction operator

**Ch 8 — Riemannian Geometry**
*Closed question: What reference structure lets distinct observers compare
their counts as one physical record?*

- `UniverseTensor`: frame of reference as mathematical structure
- The metric tensor g_μν as the unique structure making τ invariant
- `Variation`: Gâteaux/Fréchet derivative forms as ordered structure
- The Levi-Civita connection from ∇g = 0
- Key result: the Riemannian metric and Levi-Civita connection emerge from
  the single requirement that proper time is frame-invariant

**Ch 9 — Curvature**
*Closed question: What records the failure of transport to commute?*

- `YarnTheory.le` (`stokes`, `fibers`, `fabric`): the weave of paths
- The Riemann curvature tensor as commutator of covariant derivatives
- The Law of Curvature Balance
- Key result: curvature is the smooth shadow of informational strain;
  the Einstein equations are the balance condition on that strain

**Ch 10 — Symmetry Groups**
*Closed question: What remains invariant under admissible relabeling?*

- `ComputerProgram.le`: comparison routed through calibration
- `ElaborationProcess`, `HALTED`: staged invariance
- The action functional and Noether's theorem
- Gauge fields as connection forms of the admissibility constraint
- Key result: the symmetry group of the admissible ordering is the gauge
  group of the physical theory

**Ch 11 — Measure and Entropy**
*Closed question: Why does the record only grow, and when is it closed
enough to support inference?*

- `Closure`, `Closure.le`: mathematical structure of closure relation
- `INFERRED`, `INFERRED_TRUE`: inference as closure comparison
- `theory_true?`: the final question is type formation, not execution
- The Lebesgue measure as the limit of counting refinements
- The Second Law as theorem: append-only ordered records cannot decrease
- Key result: irreversibility is a theorem about append-only posets

---

## Book 2 Outline — The Physical Gauge

**Working title:** *Measurement*
**Subtitle:** How Physical Law Emerges from the Act of Observation
**Claim:** Physical laws are not imposed on nature. They are the unique
descriptions consistent with finite, distinguishable measurement records.

---

**Ch 1 — What a Measurement Is**
*Closed question: What is the smallest admissible mark a ledger can carry?*

- Events, instruments, and the act of distinction
- The ledger as the complete record of distinguishable outcomes
- `CarrierProcess`, `DISTINGUISHABLE`: the first instrument promise
- What information a measurement does and does not contain

**Ch 2 — Three Ways to Measure**
*Closed question: How can an instrument compare records and repeat the result
without pretending the comparison is the thing measured?*

- GPS, radar, speedometer: three instruments, one underlying reality
- `REPEATABLE`, `BINARY`: the physical requirements for a valid comparison
- `Study.le`, `ComputationalProcess`: structured inquiry vs. raw measurement
- Why three is the natural number of independent comparisons

**Ch 3 — What Happens Between Measurements**
*Closed question: What can be said about the gap between recorded events
without inventing structure not in the ledger?*

- The interpolation problem as a physical constraint, not a choice
- `PHYSICAL`, `NoisyProcess`: physical signal includes failure and noise
- `COMPARABLE`, `Metavariable`: unresolved placeholders carried without
  premature resolution
- The spline as the physical answer to the interpolation problem

**Ch 4 — The Grammar of Experiments**
*Closed question: How do multiple records combine without collapsing into
one undifferentiated record?*

- Comparability, correlance, the Experimental State
- `GaugeProcess`, `MEASURABLE`, `PRESENT`: gauge accountability
- `Jar`, `GUNGAN`: unresolved states held without being spent prematurely
- What it means for two experiments to be compatible

**Ch 5 — Distance**
*Closed question: How does a finite count of distinctions become an
admissible notion of distance?*

- The experimental record as a count of counts (the histogram)
- Distance as ordinal rank: the number of irreducible refinement steps
- The zero-sum constraint: refining one distinction costs another
- `MAGNITUDE`, `SCALED`, `LOAD`: the physical measurement operators

**Ch 6 — Classical Mechanics**
*Closed question: What selects one admissible continuation as the history
actually carried forward?*

- The minimal admissible interpolant as physical history selection
- The Law of Information Minimality: the universe selects least-added-structure
- `BULLSHIT`, `ArmWaveProcess`: formal overhead becomes conserved burden
- The principle of least action as consequence, not postulate

**Ch 7 — Quantum Mechanics**
*Closed question: How can information move between histories while
preserving admissibility?*

- `SCIENTIFIC`, `TRUTH`, `WITNESSED`: knowledge as carried process
- The clock, the interaction operator, Martin's condition
- Symmetric reconciliation → diffusion; oriented boundary → advection
- The Causal Doublet, qubit decoherence

**Ch 8 — General Relativity**
*Closed question: What reference structure lets distinct observers compare
their counts as one physical record?*

- `EKG`, `REAL`: calibration as the hidden reference scale
- The metric g_μν as the physical gauge of refinement agreement
- The Levi-Civita connection as the physical transport rule
- Proper time as the count of irreducible refinements

**Ch 9 — The Einstein Equations**
*Closed question: What records the failure of transport to commute?*

- `SpaceTimePath.le`: path grammar for Einstein/geodesic constructors
- `HeartbeatProcess`: the compiler's strain as part of the path story
- Informational strain, the Riemann tensor, the balance condition
- The vacuum equations and their physical solutions

**Ch 10 — The Standard Model**
*Closed question: What remains invariant under admissible relabeling?*

- `MEASURED`, `LeanProcess`: compiler elaboration as measured process
- Noether's theorem in the physical setting
- Gauge fields, Higgs mechanism, Dirac operator
- U(1), SU(2), SU(3) as the three independent admissibility invariants

**Ch 11 — Thermodynamics**
*Closed question: Why does the record only grow, and when is it closed
enough to support inference?*

- `AtreyuProcess`, `TrueOutput`: accumulated burden as physical record
- `INFERRED_TRUE`: theory closure from measured burden
- The Second Law as theorem; Landauer's principle; the arrow of time
- Dark energy, white hole, CMB as physical predictions from the framework

---

## Book 3 Outline — The Algorithmic Gauge

**Working title:** *The Compiler*
**Subtitle:** What Algorithms the Universe Runs, and Why It Cannot Be Simulated
**Claim:** The admissible record forces identifiable algorithmic forms, while
the selection rule requires exact Kolmogorov information and is therefore not
simulable by a general Turing procedure.

---

**Ch 1 — Enumeration**
*Closed question: What is the smallest admissible mark a ledger can carry?*

- `EnumerationMap`, `Enumeration`, `DecodingMap`, `Ledger` as Lean objects
- Enumeration as bijection: the first thing a compiler must do
- `CarrierProcess`: the compiler carries context, not just values
- `ADMISSIBLE`, `COUNTABLE`, `ENCODED`, `RESIDUE`: the four permissions
  as algorithmic typeclasses
- What cannot be enumerated (Cantor's theorem as an algorithmic statement)
- Algorithm: sequential scan, index construction

**Ch 2 — Divide and Conquer**
*Closed question: How can an instrument compare records and repeat the result
without pretending the comparison is the thing measured?*

- `ObservationProcess`, `BINARY`, `Trial`: comparison as divide-and-conquer
- `RepeatableProcess`, `REPEATABLE`: repeatability as the compiler's
  correctness criterion
- `ComputationalProcess`, `NUMERIC`: numeric study as composed algorithm
- Why three independent comparisons suffice (tournament argument)
- Algorithm: merge sort, binary search tree, tournament comparison

**Ch 3 — The Interpolation Problem**
*Closed question: What can be said about the gap between recorded events
without inventing structure not in the ledger?*

- `TuringProcess`, `REPRESENTABLE`: a record can be treated as a computation
  only after the representation boundary is named
- `ChaitinsNumberSequence`: halting/nonhalting as a typed boundary in
  the interpolation space
- `NoisyProcess`, `PHYSICAL`: failure and noise as admissible inputs
- `Metavariable`: unresolved placeholders carried without resolution
- The interpolation subroutine: what to return when input falls between
  known values
- Algorithm: cubic spline interpolation, natural boundary conditions

**Ch 4 — Union-Find**
*Closed question: How do multiple records combine without collapsing into
one undifferentiated record?*

- `GaugeProcess`, `MEASURABLE`: sensing process plus clock plus event predicate
- `SOURCE`, `EXECUTED`, `Abstraction`: source/compile/execute pipeline
- The correlant problem: do two events share a common admissible past?
- Union: when two histories merge (light cones intersect)
- Find: determining the equivalence class under admissible relabeling
- `GUNGAN`: unresolved states that must not be spent prematurely
- Algorithm: union-find with path compression, disjoint-set forest

**Ch 5 — Bisection and the Spline**
*Closed question: How does a finite count of distinctions become an
admissible notion of distance?*

- `GalerkinProcess`, `FINITE_ELEPHANT`, `Spline`, `Spline.le`
- The histogram as the data structure: count vector in N^M
- Distance as ordinal rank: the bisection step count
- The zero-sum constraint as the invariant bisection must preserve
- The weak form as termination condition: stop when residual is invisible
- Why Ψ^(4) = 0: the proof as an algorithm trace
- Algorithm: bisection method, Galerkin projection, Richardson extrapolation

**Ch 6 — The Noncomputable Core**
*Closed question: What selects one admissible continuation as the history
actually carried forward?*

- `ChaitinsNumberSequence`: Chaitin's Ω as the canonical noncomputable
  aggregation — the halting boundary is in the code
- Kolmogorov complexity K(w): length of shortest halting program for w
- Why K is not computable: reduction to the halting problem
- `BULLSHIT`, `PROPAGANDA`, `ACOLYTE`: formal overhead as the proxy cost
  metric when K itself is unavailable
- `EKG`: the heartbeat as the runtime's hidden cost signal
- The selection rule requires exact K; approximate K admits different
  histories — correct individually, not the actual ones
- The Pareto Effect: uniform records are inadmissible (algorithmically
  incompressible) — informational weight must concentrate
- Algorithm: Solomonoff induction, minimum description length,
  the Busy Beaver function as the upper bound on K's growth

**Ch 7 — Inversion**
*Closed question: How can information move between histories while
preserving admissibility?*

- `SCIENTIFIC`, `TRUTH`, `WITNESSED`, `Gospel`: structured transport
  of belief through a class stack
- The instance cascade `STEP_1` through `ACOLYTE_PROPAGANDA`: formal
  transport of earlier structures through a growing class stack
- The reciprocity map ψ* as the algorithmic inverse of ψ
- Why integration by parts is inversion: moving variation from ψ onto
  test functions is applying ψ*
- Symmetric reconciliation → diffusion algorithm
- Oriented boundary → advection algorithm
- The Causal Doublet: two equally admissible outputs — the degenerate case
- Algorithm: LU decomposition, adjoint method, backpropagation

**Ch 8 — The Ruler Algorithm**
*Closed question: What reference structure lets distinct observers compare
their counts as one physical record?*

- `EKG`: calibration as hidden reference scale (Prop-only public surface)
- `UniverseTensor`: frame of reference as computational structure
- `BigRedDogProcess`, `LOCAL`: local derivative discipline
- The metric tensor as the data structure for frame-comparison
- The Christoffel symbols as correction terms keeping g invariant
- The ruler as gauge: different frames measure same refinement count
- Algorithm: coordinate transformation, Gram-Schmidt, parallel transport

**Ch 9 — Commutation Failure**
*Closed question: What records the failure of transport to commute?*

- `YarnTheory.le`, `stokes`, `fibers`, `fabric`: path grammar
- `CalculusProcess`, `UNIVERSAL`: derivative plus universe tensor
- `HeartbeatProcess`: compiler strain as path/fabric element
- Curvature as commutator: [∇_u, ∇_v]w ≠ 0
- The Riemann tensor as the data structure measuring commutation failure
- The Gibbs overshoot as the irreducible residual when smoothing a jump
- Algorithm: matrix commutator, Jacobi identity, BCH formula

**Ch 10 — Invariant Computation**
*Closed question: What remains invariant under admissible relabeling or
recompilation?*

- `LOGICAL`, `ComputerProgram.le`: comparison through calibration certificate
- `ElaborationProcess`: execute moves load → transform → boolean
- `HALTED`: only `boolean` is halted; load and transform are not final
- `CompilerTape`, `CompilerOutput`, `COMPILED`: invariant staged artifact
- `Measurement`, `Measurement.le`: origin, distance, speed as ordered stages
- The action functional as cost function; Noether as invariance theorem
- Gauge fields as Lagrange multipliers enforcing admissibility
- Algorithm: gradient descent, equivariant computation, Schur lemma

**Ch 11 — Incompressibility**
*Closed question: Why does the record only grow, and when is it closed
enough to support inference?*

- `Bullshit.le`, `Bullshit.lt`: accumulated overhead as ordered record
- `AtreyuProcess`: next measurement, proof tape, and `satirize`
- `Closure`, `Closure.le`, `EquivalenceProcess`: controlled difference
  closes a record
- `theory_true?` and `#check theory_true?`: final question is type
  formation, not execution
- Landauer: the compiler cannot erase without writing elsewhere
- The Second Law as the theorem that K(record) is nondecreasing
- The selection principle requires computing K exactly; K is uncomputable;
  the manga ends with `sorry`
- Algorithm: Lempel-Ziv compression, arithmetic coding,
  Kolmogorov structure function

---

## Notes on Relative Weight

The physical gauge (Book 2) will be the heaviest. It covers all eleven
chapters in full physical detail. Estimated 80,000–100,000 words.

The mathematical gauge (Book 1) will be medium weight. Chapters 1–6
carry most of the mathematical emergence argument; Chapters 7–11 are
shorter since physics is illustrative rather than primary.
Estimated 60,000–75,000 words.

The algorithmic gauge (Book 3) will be lightest in prose but deepest in
Lean. The narrative chapters are shorter; the code sections are primary.
Estimated 50,000–65,000 words prose plus extended Lean development.

The manga runs on its own production timeline, requiring an artist.
Book 3 and `GAUGE 1199` are companion artifacts — designed to be read
together, but not two volumes of the same prose sequence.

---

## Generation Status

The project is converged at the content-boundary level. The next useful work is
drafting, not another broad planning pass.

The complete generation record now lives in:

- `three_gauges.md`: global architecture, output shape, code excerpt rules,
  and generation protocol.
- `book1_mathematical_gauge.md`: Book 1 claim, chapter plan, examples, Lean
  anchors, phenomena, codas, and section budgets.
- `book2_physical_gauge.md`: Book 2 claim, chapter plan, speedometer thread,
  physical examples, Lean anchors, phenomena, codas, and section budgets.
- `book3_algorithmic_gauge.md`: Book 3 claim, chapter plan, elaborator thread,
  Lean anchors, algorithmic forms, manga relation, codas, and section budgets.

`notes_for_gpt.md` and `notes_for_claude.md` are handoff records. They are not
sources of authority, but they remain useful as roundtrip projections: Author
-> Claude -> GPT -> Author, or Author -> GPT -> Claude -> Author. A handoff is
actionable only when the return trip exposes a structured residual. If the
roundtrip merely produces another plausible version, the project has gained an
approximation, not convergence.

---

## Shape of the Output

Each chapter begins with an unnumbered essay of about 1,500 words.
This essay is not a summary and not a preface. It is the reader's entry ramp
into the chapter's closed question.

The essay has a stable four-part shape:

1. Introduce one concrete example.
2. Name the metaphor or structure that the example reveals.
3. Display the same metaphor in a second example, so the reader sees that the
   metaphor is not trapped inside the first case.
4. Overlay the metaphor onto the chapter structure: the closed question,
   the technical machinery, and the reason the next chapter is forced.

After the unnumbered essay, the numbered chapter sections carry the technical
burden. Each chapter then ends with a coda of about 2,000 words.

The coda should use a completely unrelated metaphor. It should not merely
repeat the chapter's main example in prettier language. It must be rich enough
to embody the structures used in the chapter and show them performing as their
typeclasses: distinguishing, counting, comparing, measuring, transporting,
closing, or whatever the chapter's machinery has just required. The coda is
therefore not ornamental. It is a final independent model of the chapter's
structure.

Once the outlines stabilize, each section should receive a quantized length
target so drafting can be assigned concretely. The numbers below are base
quanta for planning. They are not a fixed size for every future book.

Suggested length quanta:

| Unit | Approximate Words | Use |
|---|---:|---|
| Box | 500 | Compact phenomenon, aside, warning, or single technical note |
| Short | 1,000 | Setup, transition, one clean example, or low-conflict definition |
| Medium | 2,000 | Core explanation, one derivation, or one substantial phenomenon |
| Long | 3,000 | Load-bearing argument, multiple phenomena, or chapter-closing machinery |

The quantization is an editorial budget, not a rigid law. Its purpose is to
make generation goals concrete enough that different models can draft, compare,
and break ties against the same target.

### Scaling the budget

Budgets scale linearly when a volume is authorized at a different total size.
The base quanta define relative weight. The book file defines the scale.

Use this calculation:

```text
scale factor = target total words / base total words
scaled unit  = base unit * scale factor
```

For example, if a compact companion is planned at 45,000 words and a larger
experimental-history volume is authorized at 170,000 words, the scale factor is:

```text
170,000 / 45,000 ≈ 3.8
```

That does not mean every Short section blindly becomes 3,800 words. It means
the book must account for roughly 3.8 times as much structural material. A
book can spend that added budget in two equivalent ways:

1. **More units:** keep Box / Short / Medium / Long close to the base quanta,
   but add more episodes, sections, codas, or apparatus blocks.
2. **Larger units:** keep the same number of units, but multiply each unit by
   the scale factor.

Most large books should use a mixed linear scaling: more units where the
material naturally subdivides, and larger units where an anchor episode,
derivation, source history, or apparatus explanation carries more load.

The rule is conservation of budget. If one section, episode, or chapter grows,
another must either shrink, disappear, or be explicitly assigned new budget.
Do not scale by quietly inflating every paragraph. Scale by assigning more
named units or larger named units.

For a 500-700 page experimental-history volume, a worked midpoint might be:

```text
target total: ~170,000 words
front matter: ~10,000
six chapters: ~22,000-30,000 each
back matter: ~5,000
episode tiers:
  vignette: 500-1,000
  working: 1,500-2,500
  anchor: 3,000-4,500
```

This is an example calculation, not a rule for the technical volumes. It shows
how the same section-based discipline can scale from a short companion to a
large history without losing the budget as a controlling structure.

The final production pass should give every chapter a small budget table:

| Section | Purpose | Length |
|---|---|---|
| Unnumbered essay | Example, metaphor, second display, chapter overlay | 1,500 |
| Core argument | Main chapter mechanism | Short / Medium / Long |
| Technical development | Proof, derivation, Lean, or apparatus | Short / Medium / Long |
| Phenomenon box | Chapter-local example | Box / Short / Medium |
| Bridge | Close the question and force the next chapter | Short |
| Coda | Unrelated metaphor performing the chapter's typeclass structure | 2,000 |

Phenomena require their own local context. A phenomenon box should not be
dropped into a chapter as an isolated exhibit. Budget each phenomenon unit as
a short-to-medium local arc: roughly one third of the budget introduces why the
phenomenon is needed here, then the phenomenon box appears, then the remaining
two thirds interpret the phenomenon back into the chapter's structure.

In other words:

```text
1/3 contextual setup -> phenomenon box -> 2/3 structural interpretation
```

Claude, GPT, and any tie-breaking model should use the same length vocabulary.
If two models disagree, the tie-breaker should decide by asking which section
introduces more new machinery, carries more phenomena, or performs the stronger
chapter-closing role.

### Roundtrip Richardson condition

Multiple models are not a voting system. Agreement between Claude and GPT is
evidence of a stable projection, but it is not by itself convergence.
Disagreement between Claude and GPT is not by itself useful either. It becomes
useful only when the disagreement has a form that can be carried through the
next pass.

The roundtrip is Richardson-like only when it exposes a structured residual:

| Roundtrip result | Interpretation | Action |
|---|---|---|
| Same claim, different wording | stable projection | keep the simpler form |
| Same structure, shifted boundary | leading error term is visible | adjust the boundary and run the next pass |
| Missing dependency appears on the return trip | null-space term exposed | add the dependency to the plan |
| Model A and Model B merely disagree | unstructured residual | treat as approximation, not convergence |
| Both models agree but no residual is named | consensus approximation | do not freeze solely on agreement |

The test is: can the return trip say what changed, why it changed, and which
earlier basis vector caused the change? If yes, the residual has form and the
next pass can cancel or absorb it. If no, the project is only sampling adjacent
approximants.

This is why the handoff notes should preserve not only recommendations but the
reason a recommendation changed. The useful object is the error structure
between passes, not the most recent answer.

## Generation Protocol

To draft a chapter, use the corresponding book file as the local source of
truth and apply this sequence:

1. Draft the unnumbered essay at about 1,500 words. Use the four-part shape:
   concrete example, named structure, second display, chapter overlay.
2. Draft the numbered sections in order. Use the section budget table in that
   book file: at base scale, Short ≈ 1,000 words, Medium ≈ 2,000 words,
   Long ≈ 3,000 words. If the book file declares a larger or smaller scale,
   use the scaled target stated there. The table is an editorial target, not a
   hard limit.
3. Place phenomena only where the book file assigns them. A phenomenon should
   arrive as a local arc: 1/3 setup, phenomenon box, 2/3 interpretation back
   into the chapter structure.
4. Draft a short bridge that explicitly closes the chapter question and forces
   the next chapter's question.
5. Draft the coda at about 2,000 words. The coda must use an unrelated metaphor
   rich enough to perform the chapter's typeclass structure.
6. During the post-pass, promote a Short section to Medium only if the draft
   reveals real structural overload. Current expected candidates are:
   Book 1 Ch 10 §3 (Noether's Theorem), Book 2 Ch 10 §4 (Yang-Mills and
   Confinement), and Book 3 Ch 11 §2 (Kolmogorov Structure Function).

Do not add new phenomena, codas, or architecture during drafting unless a
closed question cannot close without them. Bounded source-box checks remain
allowed, but they should resolve to Inside / Outside / Future Work without
reopening the book architecture.

---

## Section-Based Generation Method

The generation protocol above states what to draft. This section states how to
draft it. The method is **section-based generation**: within a chapter, write
each numbered section independently, then concatenate, then smooth, then move
to the next chapter. The method is the operational discipline that makes the
budget enforceable.

### Why section-based

Whole-chapter drafting fails for two reasons. First, context drift: by the
time the model reaches §5, the model has forgotten the budget for §2 and tends
to compress everything into a uniform middle length. Medium sections collapse
to Short; Short sections inflate toward Medium; the budget evaporates. Second,
coherence drift: an essay drafted before the sections is forced to guess at
what the sections will contain. The essay then mismatches the sections; the
chapter feels incoherent at the seam between the essay and §1.

Section-based drafting fixes both. Each section is drafted in isolation against
its own budget, with the budget explicitly stated in the prompt. The essay is
drafted **after** the sections are in place, so it can thread through specific
material that already exists. The bridge and the coda are drafted with the
sections visible, so they refer to actual chapter content rather than
hypothetical content.

### The procedure

For each chapter, in order:

1. **Write each numbered section independently against its budget.** Before
   drafting §$n$, restate the section's budget out loud: at base scale,
   Short (~1,000 words), Medium (~2,000 words), or Long (~3,000 words), or the
   scaled target declared in the book file. Then draft only that section
   against that target. Do not draft the next section until the current section
   is in place. The budget is not advisory; it is the operational target.
   Sections that drift one tier larger without an explicit budget assignment
   are not "thorough"; they are over-budget and should be cut.

2. **Concatenate the sections into the chapter file.** Each Edit call places
   one section into its slot in the chapter stub. The stub is a skeleton with
   `\section{...}` headers and empty bodies; the Edit replaces the empty body
   with the drafted section. The stub remains stable across the chapter; only
   the section bodies fill in.

3. **Smooth the chapter by drafting the bridge.** The bridge is Short; it
   closes the chapter's question explicitly and forces the next chapter's
   question. The bridge can refer to the actual sections by name because they
   are now in place.

4. **Draft the coda using the metaphor named in the book file.** The coda is
   ~2,000 words. The coda performs the chapter's typeclass structure
   independently of the chapter's own examples. Because the sections exist,
   the coda can be calibrated against the chapter's actual material; if a
   section's example overlaps with a coda candidate, the coda metaphor must
   shift.

5. **Draft the essay last.** The essay is ~1,500 words and uses the four-move
   shape: concrete example, named structure, second display, chapter overlay.
   The essay overlays onto the chapter machinery that already exists; the
   "chapter machinery" referent is the set of sections just drafted. Writing
   the essay last guarantees that the essay's promised structure matches the
   chapter's actual structure.

6. **Move to the next chapter.** Do not revise the previous chapter beyond
   typo fixes. The chapter is closed when the essay is in place; revisiting
   it later breaks the budget discipline.

### The budget is the load-bearing element

The budget table in each book file specifies which sections are Short, which
are Medium, and which are Long, or gives a scaled equivalent such as Anchor,
Working, and Vignette for a larger book. The medium and long designations are not
decorative. They identify sections that carry **specific structural load**: a
proof, a derivation, a load-bearing conceptual separation. Compressing a
Medium section to Short omits the load. Inflating a Short section to Medium
adds unrecorded structure that the book does not require.

Examples from Book 1:

- Ch 5 §2 (The Spline as Forced Continuation) is Medium because the
  Minimum Curvature Property requires an integration-by-parts argument with
  careful tracking of boundary terms. A Short version cannot carry the proof.
- Ch 6 §2 (The Euler-Lagrange Equation) is Medium because the brachistochrone
  derivation requires both the variational setup and the Beltrami first
  integral. The cycloid solution is the chapter's load-bearing example; a
  Short version omits the derivation and reduces the chapter to assertion.
- Ch 11 §2 (Measure) is Medium because the Cantor-set example requires both
  the measure construction (Caratheodory) and the cardinality argument
  (binary sequences). A Short version cannot carry both.

For each Medium section, the prompt must include the specific load the
section carries. For each Short section, the prompt must explicitly forbid
the section from drifting into the next section's territory.

### Common failure modes

- **Budget collapse**: every section ends up at ~1,200 words. Diagnosis: the
  model has not internalized which sections are Medium. Fix: restate the
  Medium designation explicitly before drafting each Medium section.
- **Coda contamination**: the coda repeats the chapter's main example in
  prettier language. Diagnosis: the coda was drafted before the sections, so
  the model picked the chapter's central example as the coda's material. Fix:
  draft the coda after the sections, with the chapter's examples explicitly
  excluded from the coda's metaphor.
- **Essay over-promising**: the essay describes structures the sections do
  not contain. Diagnosis: the essay was drafted before the sections, or
  drafted from a guess at the sections. Fix: draft the essay last; quote the
  actual section material in the four-move overlay.
- **Phenomenon orphaning**: a phenomenon box appears with no surrounding
  setup or interpretation. Diagnosis: the phenomenon was inserted as a
  standalone unit rather than as part of its host section's local arc. Fix:
  follow the 1/3 setup, phenomenon box, 2/3 interpretation rule within the
  section that hosts the phenomenon.

### The closing test

A chapter is complete when, reading from the essay through the bridge, every
structure named in the essay is performed in a section, every section is
within ~20% of its budget, the bridge closes the chapter's question, the
coda performs the chapter's structures without overlap with the chapter's
own examples, and the chapter ASCII-7 lints cleanly. Any of these failing
indicates the section-based procedure was not followed.

---

## Drafting Order: The Krylov Constraint

Chapters must be drafted in forward order: Ch 1 -> Ch 2 -> ... -> Ch 11.
The same rule binds Volume 6's six chapters, Volume 5's three, and every
other volume in the project. No skipping ahead. No drafting the hardest
chapter first. No testing the form on a late chapter before the early
chapters have been written.

This is a structural constraint, not an editorial convenience.

### Why the constraint holds

The procession is forward-dependent. Each named obligation requires the
prior names to have done their work. RESIDUE only does its work because
ENCODED has happened. BULLSHIT only does its work because LOAD and
FINITE_ELEPHANT have established what overhead is overhead *of*. The
procession is not a list; it is an iteration.

The project's own vocabulary supplies the structural argument. The
procession is a Krylov expansion of the question "what does it take to
license an inferred sentence under a record." Each name is the next
basis vector that the prior names have made necessary. In a Krylov
iteration the k-th basis vector cannot be computed without the first
k-1 basis vectors; the subspace at step k determines what step k+1 can
reach.

Drafting a late chapter first projects onto a subspace whose lower-order
basis vectors have not been computed. The form (`phenom` kernel,
calibration certificate, two-coordinate header, section-based budget
discipline) is the projector, and the projector is consistent across
chapters. But the content at step k+1 depends on the content already
established at step k. A late chapter drafted in isolation either
invents the basis it needs (drift) or assumes it (incoherence at the
seam when the earlier chapter is eventually written).

The book is not a test of the form. The book is the iteration. The
iteration cannot run out of order.

### Why the constraint is hard to obey

The recurring temptation is to draft the "hardest" or "most original"
chapter first to validate the form on demanding material. That is a
craft argument. It is structurally identical to recommending the book
be drafted backwards.

The same error appears one level up. A planning conversation that
recommends drafting Ch 4 first because Ch 4 is the most original is
itself a late-iteration projection in the conversation's own Krylov
expansion: the recommendation depends on basis vectors (the form, the
procession, the chapter dependencies) that the conversation has not yet
fully computed. The recommendation can sound sophisticated and still be
wrong for the same Krylov reason the drafting move would be wrong.

The constraint binds independently of who is suggesting otherwise.
Author, Claude, GPT, or any tie-breaking model. If craft instinct
recommends "hardest first," the structural argument still holds.

### Restart as the natural second iteration

Forward Krylov order Ch 1 -> Ch N is the first pass. A second forward
pass Ch 1 -> Ch N with the full-book voice calibrated is the restart.
The Movements act as eigenvalue clusters; revising within a movement
after the next movement has stabilized is the equivalent of restart
strategies in numerical Krylov methods. Two-pass drafting is the normal
rhythm. One-pass is the accident.

### Connection to existing project vocabulary

The author's prior framing of his own work as "Richardson extrapolation
used to over-resolve" already names this discipline. Richardson
extrapolation requires iterations to be ordered correctly: the
leading-order error term at step k+1 depends on the leading-order error
term at step k. The constraint that lets Richardson cancel error terms
is the constraint that forces forward Krylov order. The two methods are
the same discipline at different scales: Richardson across project
iterations (instrument book -> device -> volumes 1 through 6 -> manga),
Krylov within a single volume.

The same condition governs model roundtrips. A Claude -> GPT -> Claude
or GPT -> Claude -> GPT exchange converges only if the return pass makes
the error term visible. Without a visible residual, the exchange is still
valuable as search, taste, or robustness checking, but it is not
Richardson extrapolation. It can approximate the book's intended shape;
it cannot claim convergence.

### Practical rule

For every chapter drafting decision: ask whether the prior chapters
have been drafted. If not, draft them first. If "but this chapter is
the hardest" or "but this chapter is the most original" enters the
argument, the rule still holds. The hardest chapter is hardest
precisely because it depends on the most prior basis vectors; that is
exactly why it must come last in its dependency chain.

This rule supersedes any earlier "draft Chapter X first" recommendation
in `notes_for_gpt.md`, `volume_6.md`, or any other planning file. Those
recommendations were late-iteration projections without the lower-order
computation. The Krylov constraint is the structural argument that
overrides them.

---

## Code Excerpt Rules

The books may excerpt Lean code, but the excerpts should be structural rather
than exhaustive. The goal is to show the reader the pattern the code enforces,
not to reproduce entire files.

Allowed excerpt types:

1. Complete inductive definitions, when the constructors show the pattern.
2. Method names and types, especially when the type states the interface.
3. Interesting `le` match arms, especially when comparison behavior changes
   across constructors.
4. Member names and types from structures/classes, when the fields reveal what
   must be carried.
5. Interesting inheritance or instance patterns, especially where the class
   stack shows accumulated obligation.

Avoid excerpting long implementation blocks unless the exact structure of the
implementation is the argument. In most places, prefer a small code excerpt
followed by prose explaining what burden the type, constructor, field, or match
arm carries.
