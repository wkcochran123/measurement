# Book 3 - The Algorithmic Gauge

Working title: The Compiler

Safer subtitle candidate: Admissible Records, Compiler Cost, and the
Noncomputable Selection Rule

Audience: readers who think about computation and reality: Hofstadter,
Penrose, Chaitin, compiler people, proof-assistant people, and the curious
borderland between mathematics and metaphysics.

Claim: admissible records force identifiable algorithmic forms: bisection,
divide and conquer, inversion, enumeration, union-find, and proof checking.
The selection rule requires exact Kolmogorov information and is therefore not
simulable by a general Turing procedure.

The Lean code is the primary artifact. The algorithms in the code are the
argument. The book must be careful: it is not claiming the current code
implements exact `K`, nor that the code literally simulates the universe.

Ground example: the Lean elaborator. Every definition, theorem, and instance
in the code passes through Lean's elaborator — a term-rewriting engine that
carries metavariables, resolves types, checks termination, and counts
heartbeats. The elaborator is the physical instrument of Book 3. Each chapter's
key examples come from things you can observe by running the compiler or
examining the elaboration output.

## Companion Manga

Working title candidate: GAUGE 1199

The satire is not "Book 4." It is a companion manga, published physically as
manga and digitally as manga. It is not prose later decorated with panels.

The algorithmic gauge and the manga are the closest pair. Book 3 is the
technical manual; GAUGE 1199 is the dramatization of the compiler strain. The
AI assistant is on screen, the human is at the keyboard, the physics appears in
the panel space between them, and the ledger is the conversation window. The
manga ends with an open Lean file, the noncomputable selection principle
unimplemented, and `sorry` as the final line.

Strong visual motifs for the manga:

- Moire Effect: two grids beating against each other.
- Quicksand Effect: sinking to an equilibrium threshold.
- Maxwell's Demon: memory, sorting, and paid entropy.
- Tail-Latency / EKG: compiler heartbeats as visible strain.

Note on Malus Effect: this has been assigned to Book 2 Ch 5 (physical
polarimeter). Remove from manga motif list; use Quicksand and Moire instead.

## Shared Frame

Source hierarchy:

```text
gauge.pdf                       source manuscript; nine chapters; all registers mixed
three_gauges.md                 extraction and architecture plan
instrument/chapters/*.tex       phenomenon source
device/Measurement/*.lean       primary formal artifact for this book
future book drafts              audience-specific rewrites
```

Calibration is central. The calibration module is
`device/Measurement/Calibration/LeanCalibration.lean`. It imports the
nameable `ComputerProgram`, keeps the heartbeat-like `Nat` private in
`Reading`, and exposes only `Prop`-valued comparisons through `EKG`.

Current Lean calibration semantics:

- `.load` initializes the baseline.
- `.boolean` reads the calibration.
- `LOGICAL` holds `ekg : Calibration.EKG`.
- `ComputerProgram.le` asks `prop.ekg` for comparisons.
- `.boolean` programs are comparable through calibration.
- `.transform, .boolean` can be compared only through calibration.
- `.boolean, .transform` is an explicit incomparability shape.
- Covariant comparison does not currently make sense and is false.

Operational warning: do not run `lake build` casually. The build is expensive.

## Chapter Map

| Ch | Area | Closed Question |
| --- | --- | --- |
| 1 | The Record | What is the smallest admissible mark a ledger can carry? |
| 2 | Comparison | How can an instrument compare records and repeat the result without pretending the comparison is the thing measured? |
| 3 | Phenomena | What can be said about the gap between recorded events without inventing structure not in the ledger? |
| 4 | Structure | How do multiple records combine without collapsing into one undifferentiated record? |
| 5 | Distance | How does a finite count of distinctions become an admissible notion of distance? |
| 6 | Motion | What selects one admissible continuation as the history actually carried forward? |
| 7 | Transport | How can information move between histories while preserving admissibility? |
| 8 | Stress | What reference structure lets distinct observers compare their counts as one physical record? |
| 9 | Strain | What records the failure of transport to commute? |
| 10 | Symmetry | What remains invariant under admissible relabeling or recompilation? |
| 11 | Entropy | Why does the record only grow, and when is it closed enough to support inference? |

---

## Generation Budget

Generate every chapter with the shared ritual from `three_gauges.md`:

- Unnumbered essay: about 1,500 words.
- Five numbered sections: use the table below.
- Phenomenon arcs: 1/3 setup, phenomenon box, 2/3 structural interpretation.
- Bridge: Short.
- Coda: about 2,000 words, using the coda candidate named in the chapter.

Book 3 is prose-light but Lean-heavy. When a Lean trace, `#check`, or compiler
observation carries the argument, keep the prose Short and let the artifact do
the work. Do not pad compiler-facing sections just to make them look as heavy
as Book 1 or Book 2.

| Ch | §1 | §2 | §3 | §4 | §5 |
| --- | --- | --- | --- | --- | --- |
| 1 | Short | Short | Short | Short | Short |
| 2 | Short | Short | Short | Short | Short |
| 3 | Short | Short | Short | Short | Short |
| 4 | Short | Short | Short | Short | Short |
| 5 | Short | Short | Short | Short | Short |
| 6 | Short | Medium | Short | Short | Short |
| 7 | Short | Short | Short | Short | Short |
| 8 | Short | Short | Short | Short | Short |
| 9 | Short | Short | Short | Short | Short |
| 10 | Medium | Short | Short | Short | Short |
| 11 | Short | Short | Short | Short | Short |

Medium sections:

- Ch 6 §2 — Busy Beaver. `BB(5) = 47,176,870` (proved 2024), `BB(6)` unknown,
  and growth faster than any computable function. This is the hard wall between
  proxy costs and exact `K`.
- Ch 10 §1 — Bootstrapping a Compiler. Lean 4 fixed-point argument:
  `stage N+1 = stage N`; the load-bearing example before symmetry
  generalization.

Post-pass candidate: Ch 11 §2 — Kolmogorov Structure Function may be promoted
to Medium if it carries the final incompressibility argument rather than
serving as one example among several.

---

## Ch 1 - Enumeration

Closed question: What is the smallest admissible mark a ledger can carry?

Chapter job: the first compiler obligation is naming and carrying a mark. The
chapter shows that before a program can do anything, it must be able to name
a thing and distinguish it from another thing.

Elaborator thread: when Lean elaborates `def x : Nat := 3`, the elaborator
creates a `Fact` (the definition) with a `Fact.Truth` (the proof that 3 : Nat);
the carrier is the namespace entry; `DISTINGUISHABLE` is the typeclass proof
that Lean can decide whether two elaborated terms are the same.

### Sections and Key Examples

1. **Sequential Scan.** Key example: searching an unsorted list of 10⁶ integers
   for the value 42 — the scan reads each element once; the first element
   is one admissible event; each comparison is one mark; the search terminates
   when a mark matches.

2. **Index Construction.** Key example: building a B-tree over a database
   table with 10⁷ rows — the tree is an admissible enumeration with order
   preserved; inserting a row is one mark (one leaf node added); range queries
   cost O(log n) because the index preserves the order of the marks.

3. **Godel Numbering.** Key example: Godel assigns each logical formula a unique
   natural number (e.g., by prime factoring the sequence of symbol codes); every
   proof is an integer; self-reference becomes possible because a proof can
   talk about its own Godel number; this also creates the incompleteness
   boundary.

4. **The Halting Boundary as Enumeration Limit.** Key example: in Lean,
   `#eval Nat.decEq 3 3` elaborates and halts immediately returning `true`; a
   program searching for a counterexample to Goldbach's conjecture may run
   forever; the boundary between halting and non-halting is not decidable —
   it is the limit of what enumeration can carry.

5. **CarrierProcess in Lean.** Key example: `CarrierProcess` in Episode1.lean
   wraps a value with its symbol; `DISTINGUISHABLE` is the typeclass proof that
   Lean's kernel can decide definitional equality; run `#check @DISTINGUISHABLE`
   and observe the constraint it places on the type — the carrier must expose a
   decision procedure.

Lean anchors:

- `device/Measurement/Episode1.lean`
- `Fact`, `Fact.Truth`, `Number`, `Number.le`
- `CarrierProcess`, `DISTINGUISHABLE`
- `Natural`, `CountingProcess`, `ADMISSIBLE`
- `Rational`, `IndexingProcess`, `COUNTABLE`
- `Sequence`, `LimitProcess`, `ENCODED`
- `Limit`, `CauchyProcess`, `RESIDUE`, `Sample`

Phenomena to place:

- Chaitin Effect: the record already contains a halting/incompressibility
  boundary.
- Marconi Effect: signal transmission as carried record, if not kept physical.
- Cantor-Godel-Cohen should stay primarily Book 1, but can be referenced as
  the enumeration obstruction.

Algorithmic forms:

- Sequential scan
- Index construction
- Enumeration boundary

### Coda Candidate

Metaphor: a warehouse receiving dock.

Every incoming package receives a label (a unique barcode), a recorded shelf
location, and a scanner entry before it can be found again. Without the scan,
the package exists physically but is invisible to the inventory system — it
has not yet been given a `Fact`. The label is the carrier (`CarrierProcess`);
the barcode makes it `DISTINGUISHABLE` from every other package; the shelf
location makes it `COUNTABLE` (you can enumerate all packages by location);
the packing slip is the `RESIDUE` (everything about the package that is not
the barcode). The far wall of the warehouse — the shelf space not yet assigned
— is the boundary of unscanned inventory: packages exist there but cannot be
found; they are outside the enumeration.

Overlap warning: none. The chapter's examples (sequential scan of 10⁶
integers, B-tree index, Godel numbering, halting boundary, CarrierProcess in
Lean) are computational and abstract. The receiving dock is physical,
industrial, and logistical. The enumeration structures perform without
collision.

---

## Ch 2 - Divide and Conquer

Closed question: How can an instrument compare records and repeat the result
without pretending the comparison is the thing measured?

Chapter job: comparison as an algorithmic interface. Repeatability is compiler
correctness — the same input must produce the same comparison output every time.

Elaborator thread: `BINARY` in Episode2.lean is the typeclass for a binary
comparison interface; `REPEATABLE` requires that the process can carry prior
observation; these are the algorithmic analogs of "the speedometer reads the
same speed twice from the same car."

### Sections and Key Examples

1. **Binary Search.** Key example: searching a sorted array of 10⁶ integers —
   20 comparisons to find any element; each comparison is one admissible trial;
   the comparison is the instrument; the element is not touched, only compared.

2. **Merge Sort.** Key example: sorting 10⁶ records by surname — merge sort
   divides into halves, sorts each, merges; the merge step compares the
   front elements of two sorted lists; each comparison is one repeatable trial;
   the final sorted order is the admissible record.

3. **FFT: Recursive Divide.** Key example: Cooley-Tukey FFT on 2²⁰ samples —
   20 levels of recursive halving; each butterfly operation is one admissible
   comparison; the output is the unique minimal-information representation of
   the input signal in the frequency domain; O(n log n) comparisons vs. O(n²)
   for the naive DFT.

4. **Tournament Sort.** Key example: finding the fastest runner among 64
   contestants using a single-elimination tournament — 63 comparisons, each
   with a definite winner; the champion is found without ever knowing all
   pairwise rankings; each match is one admissible trial.

5. **RepeatableProcess in Lean.** Key example: `REPEATABLE` in Episode2.lean
   requires that the process carry prior observation before it is admissible;
   inspect the typeclass constraint: a comparison that forgets its previous
   output is not repeatable in this sense; the compiler checks this at
   elaboration time.

Lean anchors:

- `device/Measurement/Episode2.lean`
- `ObservationProcess`, `BINARY`
- `Trial`, `Trial.le`, `Trial.lt`
- `RepeatableProcess`, `REPEATABLE`
- `Study`, `Study.le`
- `ComputationalProcess`, `NUMERIC`

Phenomena to place:

- Turing Effect: computation as an admissible procedure.
- Fourier-Nyquist Effect: sampling and reconstruction. This is already in the
  source; do not list Nyquist-Shannon as wholly new.
- Newton-Cooley-Tukey Effect: recursive transform/divide-and-conquer.
- von Neumann-Trefethen Effect: stability as algorithmic admissibility.

Algorithmic forms:

- Merge sort
- Binary search tree
- Tournament comparison
- FFT / recursive transform

### Coda Candidate

Metaphor: a postal sorting machine with progressive scan stages.

Each piece of mail passes through automated scanners at increasing resolution.
Stage 1 reads the zip code (routing to one of 10 regional bins — one binary
decision per bit of the zip code). Stage 2 reads the street (routing within
the region). Stage 3 reads the street number (routing to one of ~100
delivery sequences). Stage 4 reads the apartment (final sort). Each scan is
one binary comparison (`BINARY`, `Trial.le`); the machine produces the same
route for the same envelope every time (`REPEATABLE`); the final route is
the accumulated record of all four comparisons (`NUMERIC`). The halving at
each stage is divide-and-conquer: the envelope's destination is narrowed by
half at each resolution level, exactly as in binary search.

Overlap warning: none. The chapter's examples (binary search, merge sort, FFT
on 2²⁰ samples, tournament sort, RepeatableProcess in Lean) are all
algorithmic and computational. The postal sorting machine is physical,
industrial, and logistical. The recursive comparison structure performs
without collision. Prefer this to "nested bins" — the progressive scanning
captures the recursive halving where static bins do not.

---

## Ch 3 - The Interpolation Problem

Closed question: What can be said about the gap between recorded events without
inventing structure not in the ledger?

Chapter job: what the compiler may carry unresolved. Metavariables are not
errors — they are admissible placeholders that the elaborator carries until
enough information is available to resolve them.

Elaborator thread: Lean's elaborator carries unification metavariables
— `?m : α` is a placeholder until sufficient constraints arrive to infer `α`;
the elaborator does not prematurely resolve it; premature resolution would
introduce unrecorded structure.

### Sections and Key Examples

1. **Cubic Spline Fitting.** Key example: given 10 temperature readings at
   10 times, fit a natural cubic spline in Python using `scipy.interpolate
   .CubicSpline` — the slopes at interior knots are the metavariables, solved
   by the C² gluing condition; observe that the spline's fourth derivative is
   numerically zero on each interval.

2. **Carrying Metavariables in the Lean Elaborator.** Key example: write a Lean
   definition with a hole: `def foo : ?α := 3`; the elaborator carries `?α` as
   a metavariable until the literal `3` forces `?α = Nat`; check the elaboration
   trace with `set_option trace.Meta.isDefEq true` — the resolution is visible.

3. **The Halting Boundary as Interpolation Limit.** Key example: `REPRESENTABLE`
   in Episode3.lean marks the boundary between processes whose output can be
   represented and those that cannot; write a Lean term that diverges (using
   `sorry` or an infinite loop) — the elaborator cannot interpolate through it;
   the boundary is the interpolation limit.

4. **Noisy Interpolation.** Key example: fit a linear regression to 20 noisy
   data points in numpy — `np.polyfit(x, y, 1)`; the slope is the metavariable
   resolved by least squares; the residual is the irreducible structure left in
   the gap after the best admissible linear fit is removed.

5. **ChaitinsNumberSequence in Lean.** Key example: `ChaitinsNumberSequence` in
   Episode3.lean encodes the halting/non-halting boundary as a typed sequence;
   examine its type signature — it names the boundary rather than crossing it;
   the sequence itself cannot be computed, but its existence as a Lean type is
   observable in the elaboration output.

Lean anchors:

- `device/Measurement/Episode3.lean`
- `Computation`, `TuringProcess`, `REPRESENTABLE`
- `ChaitinsNumberSequence`
- `NoisyProcess`, `PHYSICAL`
- `Metavariable`, `PhysicalProcess`, `COMPARABLE`
- `Sophism`, `SlipProcess`, `OBSERVED`, `Area`
- `device/Measurement/Episode4.lean`: `Phenomenon`

Phenomena to place:

- Chaitin Effect: inside here, recalled from Ch 1 as the interpolation limit.
- Adams Effect: future work. Inside if source box argues representation burden
  as an algorithmic constraint. Disposition requires reading the source box.
- Dirichlet-Bancroft Effect: future work. Inside if source box argues boundary
  data and model completeness as an algorithmic stopping condition.

Algorithmic forms:

- Cubic spline interpolation
- Natural boundary conditions
- Carrying metavariables without resolving them

### Coda Candidate

Metaphor: a legal contract with blanks waiting for signatures and dates.

The contract arrives from the lawyer's office with its structure complete:
the clauses, the obligations, the remedies. But three blanks remain: the
effective date, the buyer's signature, the seller's initials on page 4. The
contract is a valid legal structure before the blanks are filled —
`REPRESENTABLE` as a legal instrument. Acting on an unresolved blank as if
it were resolved (proceeding with transfer of title before the signature is
present) is not merely premature; it is inadmissible. The blank is a
`Metavariable`: the contract carries it without resolving it. The elaborator
that fills the blank is the signing party. Until all metavariables resolve,
the contract is in a `COMPARABLE` but not final state — it can be compared
with other contracts, ranked by its missing fields, but not executed.

Overlap warning: none. The chapter's examples (scipy cubic spline, Lean
metavariable trace, `REPRESENTABLE` boundary, numpy polyfit, ChaitinsNumber-
Sequence) are all computational. The legal contract is institutional and
document-based. The metavariable and admissible-placeholder structures perform
without collision.

---

## Ch 4 - Union-Find

Closed question: How do multiple records combine without collapsing into one
undifferentiated record?

Chapter job: merging histories while preserving identity. Union-find is the
natural algorithmic form for combining correlated records while keeping track
of which component each record belongs to.

Elaborator thread: when Lean merges two namespaces (via `open` or `import`),
names from each are unified into the current context; `Equivalation` in
Episode5.lean is the equivalence relation; `SOURCE` is the original symbol; the
union preserves both without collapsing either into an anonymous pool.

### Sections and Key Examples

1. **Network Connectivity.** Key example: given 10 servers and 15 connections,
   is server A connected to server Z? Build a union-find structure — union each
   pair of connected servers; find the root of A and Z; if roots match, they are
   connected; nearly O(1) per query after O(m) setup.

2. **Path Compression.** Key example: after 1,000 union operations on 1,000
   nodes, path compression flattens the internal tree so future finds are O(α(n))
   ≈ O(1); the canonical representative (root) is found in nearly constant time
   regardless of history; the identity of the component is preserved through the
   flattening.

3. **Compiler Symbol Table.** Key example: in Lean, add a definition to a
   namespace with `namespace Foo` and `def bar := 3`; the name `Foo.bar` is
   merged into the global environment; `Equivalation` in Episode5.lean is the
   formal version of this merge — the name is united with the namespace without
   losing its identity.

4. **Horizon as Union Failure.** Key example: a black hole horizon is a
   causal boundary where two records (inside and outside) can never be unioned
   — the union operation fails because no signal crosses the horizon; `find`
   returns two disconnected components; this is the Ch 4 algorithmic framing
   of the Hawking phenomenon.

5. **GUNGAN States in Lean.** Key example: `Jar` and `MeesaProcess` in
   Episode4.lean hold unresolved states — the Jar contains a fact that has not
   yet been spent (resolved); inspect the typeclass: the state is held without
   premature union; the union-find metaphor is that the Jar holds a potential
   union partner until `find` resolves it.

Lean anchors:

- `device/Measurement/Episode4.lean`
- `Area`, `SensingProcess`, `PRESENT`
- `Phenomenon`, `Phenomenon.le`
- `GaugeProcess`, `MEASURABLE`
- `Jar`, `MeesaProcess`, `GUNGAN`
- `device/Measurement/Episode5.lean`
- `Equivalation`, `DigitalProcess`, `SOURCE`
- `Encoding`, `CompiledProcess`, `EXECUTED`, `Abstraction`

Phenomena from Claude:

- Hawking Radiation, Ch 6 version: the uncorrelant pair as a union-find
  problem once the horizon boundary is fixed.

Disposition: Hall-Einstein-Podolsky-Rosen Effect is outside Book 3 Ch 4 unless
the source box is rewritten as algorithmic correlation bookkeeping rather than
physical experiment. Default home remains Book 2 Ch 4.

Future work: Markov-Conway Effect requires source-box reading. If it is about
state transition as an algorithmic merge/update rule, it can enter Book 3 Ch 4;
if it is about experimental state compatibility, it stays in Book 2 Ch 4.

Algorithmic forms:

- Union-find with path compression
- Disjoint-set forest
- Source / compile / execute pipeline

### Coda Candidate

Metaphor: merging transit passes across regional systems.

Three transit agencies each issue their own cards: city bus, regional rail,
and suburban metro. Each has its own record of the passenger — card number,
account balance, travel history. A unified transit authority wants to issue
one pass that works across all three systems. The unification process must
merge three independent identity records without erasing any of them: the
city bus card's history must remain auditable as city bus history, not
dissolved into a generic "transit history." The union preserves source
identity (`SOURCE`); the find operation locates the canonical representative
of each component; `Equivalation` is the equivalence relation that makes the
three systems commensurable; the unified pass is `EXECUTED`. An unresolved
state is a passenger whose regional rail card has not yet been linked —
the pass carries them without premature union.

Overlap warning: the chapter's Lean example (namespace union via `open` and
`import`, `Equivalation` in Episode5.lean) is already a union-merge example.
Write the transit pass coda at the story level — the union-find algorithm
is the argument; the pass is the thing that performs it. Avoid Lean language
in the coda prose.

---

## Ch 5 - Bisection and the Spline

Closed question: How does a finite count of distinctions become an admissible
notion of distance?

Chapter job: distance as count of refinements. The algorithmic version of
distance is the number of bisections required to locate a value — the stopping
rule is what makes the count finite.

Elaborator thread: `FINITE_ELEPHANT` in Episode6.lean is the stopping rule for
the Galerkin process — it says: this finite element approximation is admissible
at this resolution; do not refine further; the elaborator accepts the term
because the stopping rule is satisfied.

### Sections and Key Examples

1. **Bisection for Root Finding.** Key example: finding √2 by bisection — start
   with [1, 2]; test midpoint 1.5 (1.5² = 2.25 > 2, so take left half [1, 1.5]);
   after 53 steps, the result is exact to float64 precision; each step is one
   admissible refinement; the distance is the count of steps.

2. **Galerkin FEM.** Key example: solving u'' = -1 on [0,1] with u(0) = u(1) = 0
   using 10 cubic basis functions in Python — assemble the 10×10 stiffness matrix,
   solve the linear system, plot the result (a parabola); refine to 100 elements;
   the error decreases as h⁴ (fourth-order convergence for cubic elements).

3. **Richardson Extrapolation.** Key example: computing f'(x) at x = 1 for
   f(x) = sin(x) using (f(1+h) - f(1-h))/(2h) for h = 0.1 and h = 0.05 —
   Richardson extrapolation combines them to cancel the leading O(h²) error,
   giving O(h⁴) accuracy; two approximations at different refinement scales
   collapse the leading error term.

4. **Residual Stopping.** Key example: in the Conjugate Gradient method for
   Ax = b, the iteration stops when the residual ‖r_k‖ = ‖b - Ax_k‖ < ε;
   the residual is the admissible stopping criterion — further iterations
   produce no new distinctions observable at the current resolution.

5. **FINITE_ELEPHANT in Lean.** Key example: `FINITE_ELEPHANT` in Episode6.lean
   marks the end of the Galerkin iteration; examine the typeclass — it certifies
   that the current approximation is admissible at its stated resolution;
   removing it would allow the elaborator to continue refining indefinitely;
   the stopping rule is the compiler's resolution limit.

Lean anchors:

- `device/Measurement/Episode6.lean`
- `MathematicalProcess`, `VALUE`
- `Sum`, `AddingProcess`, `MAGNITUDE`
- `Product`, `MultiplyingProcess`, `SCALED`
- `Basis`, `BASICProcess`, `LOAD`
- `Polynomial`, `GalerkinProcess`, `FINITE_ELEPHANT`
- `Spline`, `Spline.le`

Phenomena from Claude:

- Ideal Ledger Effect
- Gibbs Phenomenon, the second Ch 6 version, as irreducible approximation
  error in a smooth basis

Note: Zeno's Dichotomy is inside here as a phenomenon to write. The
algorithmic content — infinite subdivision producing a finite sum; bisection
terminating because geometric series converge — directly grounds the stopping
criterion.

Algorithmic forms:

- Bisection method
- Galerkin projection
- Richardson extrapolation
- Residual stopping

### Coda Candidate

Metaphor: focusing a camera lens until no sharper distinction appears.

A photographer focuses a manual lens on a subject. Each turn of the focus
ring halves the blur circle — the circle of confusion decreases by half per
turn. The photographer stops when the sensor cannot distinguish improvement:
at maximum resolution, an additional half-turn produces a change smaller than
one pixel, which is invisible. The stopping rule is `FINITE_ELEPHANT`: this
resolution is admissible at the sensor's stated specification; refining
further produces no new distinctions. The blur at each step is the residual;
the count of half-turns is the distance (the number of bisections required
to locate the plane of focus); the sensor's pixel pitch is the resolution
limit.

Overlap warning: none. The chapter's examples (scipy bisection for √2,
Galerkin FEM for beam equation, Richardson extrapolation, Conjugate Gradient
residual stopping, FINITE_ELEPHANT in Lean) are all numerical and
computational. The camera lens is optical and craft. The bisection and residual
stopping structures perform without collision.

---

## Ch 6 - The Noncomputable Core

Closed question: What selects one admissible continuation as the history
actually carried forward?

Chapter job: draw the boundary between proxy costs and exact selection. The
admissible record forces identifiable algorithmic forms, but the selection rule
requires exact Kolmogorov information and is therefore not simulable. This
chapter names the boundary.

Elaborator thread: `set_option maxHeartbeats 400000` limits the elaborator to
400,000 heartbeats; `EKG` in LeanCalibration.lean reads the current heartbeat
count; the heartbeat is a computable proxy for program cost, but it is not K —
it measures elaboration effort, not program description length.

### Sections and Key Examples

1. **The Halting Problem.** Key example: Turing's diagonal construction —
   assume H decides halting; build D that runs forever if H(D) says "halts,"
   and halts if H(D) says "runs forever"; H(D) produces a contradiction either
   way; write this in pseudocode and trace through the contradiction; K(w)
   is not computable because it requires solving the halting problem.

2. **Busy Beaver.** Key example: BB(5) = 47,176,870 steps (proved in 2024);
   BB(6) remains unknown; BB(n) grows faster than any computable function —
   no program can compute BB for all n; the Busy Beaver boundary is the hard
   wall beyond which proxy costs (heartbeats, runtime) cannot serve as exact K.

3. **Chaitin's Ω.** Key example: Ω = Σ_{halting p} 2^(-|p|) is a real number
   between 0 and 1 whose binary digits are algorithmically random — no pattern,
   no compression, no program shorter than the first n bits can produce those
   n bits; the informational complexity of Ω is itself; K(Ω) ≈ |Ω|.

4. **Heartbeat Proxy in Lean.** Key example: write two Lean definitions of
   different complexity; check the heartbeat count for each using `#check
   @LOGICAL` and observe the EKG value; the heartbeat is a computable upper
   bound on elaboration cost, but two programs can have the same heartbeat and
   different K, or different heartbeat and the same K; the proxy is useful but
   not exact.

5. **ArmWaveProcess as Overhead Meter.** Key example: `ArmWaveProcess` and
   `BULLSHIT` in Episode7.lean measure formal overhead accumulated during
   elaboration; `Diatribe`, `CrusadeProcess`, `PROPAGANDA`, `Cult`, and
   `ACOLYTE` track class-stack burden; these are the compiler's record of how
   much formal obligation has been carried without being discharged — the
   algorithmic analog of elaboration strain.

Lean anchors:

- `device/Measurement/Episode6.lean`: `GalerkinProcess`, `Spline`,
  `FINITE_ELEPHANT`
- `device/Measurement/Episode7.lean`: `ArmWaveProcess`, `BULLSHIT`,
  `Diatribe`, `CrusadeProcess`, `PROPAGANDA`, `Cult`, `InitiationProcess`,
  `ACOLYTE`
- `device/Measurement/Episode3.lean`: `ChaitinsNumberSequence`
- `device/Measurement/Calibration/LeanCalibration.lean`: `EKG`

Phenomena from Claude:

- Maxwell Effect
- Inverse Square Effect
- Moire Effect
- Quicksand Effect
- Butterfly Effect
- Halt Effect
- Busy Beaver as a new phenomenon to write
- Pareto Effect (compressibility / information concentration reading)

Algorithmic forms:

- Solomonoff induction as boundary idea
- Minimum description length as approximation
- Busy Beaver as growth boundary
- Heartbeat proxy cost through `EKG`

Warning:

- Do not claim exact Kolmogorov `K` is implemented in Lean. The code has
  Chaitin/halting structure and heartbeat cost proxies.

### Coda Candidate

Metaphor: a sealed archive whose index contains redacted entries.

The archive holds thousands of sealed boxes. The public catalog lists each
box by accession number, acquisition date, and a one-line description. Some
entries are redacted: the description reads [CONTENT RESTRICTED]. The catalog
is a proxy for the archive's real content — useful for routing (you can find
the accession number of a restricted box), but the exact content of the sealed
records cannot be computed from the index. The proxy costs are the catalog
entries; the exact description-length of each box (its `K`) is inside the
seal, inaccessible without opening it. `ArmWaveProcess` and `BULLSHIT` are
the formally registered catalog entries for boxes whose content cannot be
assessed from outside — overhead accumulated in the index without being
dischargeable from the index. `Diatribe`, `CrusadeProcess`, `PROPAGANDA`,
`Cult`, and `ACOLYTE` are the class-stack burden entries: the cascade of
formal obligations recorded in the catalog but unreachable in content.
`ChaitinsNumberSequence` is the sequence of accession numbers of boxes that
are provably unseeable — the halting-problem boxes. The `EKG` is the
heartbeat count of how much catalog-lookup work has been done; it is a proxy
for the real cost of knowing what is inside.

Overlap warning: none. The chapter's examples (Turing diagonal, BB(5) = 47M
steps, Chaitin's Ω, heartbeat proxy in Lean, ArmWaveProcess as overhead) are
all computational and proof-theoretic. The sealed archive is archival,
institutional, and physical. The noncomputable boundary and proxy-cost
structures perform without collision. This coda also absorbs the
`BULLSHIT`/`PROPAGANDA`/`ACOLYTE` connections that were incorrectly placed in
Book 1 Ch 6; those names belong here, in the register where elaboration
overhead is the primary subject.

---

## Ch 7 - Inversion

Closed question: How can information move between histories while preserving
admissibility?

Chapter job: adjoints, inversion, backpropagation, and proof transport through
the class stack. The chapter shows how information flows backward — from output
to input — when the forward map is known.

Elaborator thread: `WITNESSED` in Episode10.lean bridges truth into the
witnessed record — a fact is witnessed if and only if an admissible transport
process has carried it from a truth state; this is the Lean model of adjoint
transport.

### Sections and Key Examples

1. **LU Decomposition.** Key example: solving the system Ax = b for a 1000×1000
   matrix using SciPy's `scipy.linalg.solve` — internally LU-decomposes A =
   LU in O(n³); forward substitution solves Ly = b; backward substitution solves
   Ux = y; the two sweeps are the forward map and its adjoint.

2. **Backpropagation.** Key example: a 5-layer neural network trained on MNIST —
   the forward pass computes the predicted digit; the backward pass propagates
   the cross-entropy gradient from the output back through each layer; the
   gradient at layer k is the adjoint of the Jacobian at layer k; the chain rule
   is the transport law.

3. **Gram-Schmidt Orthogonalization.** Key example: given 3 linearly independent
   vectors in ℝ³, Gram-Schmidt produces 3 orthonormal vectors — at each step,
   subtract the projection onto all previous vectors; the projection is the
   inversion of the correlation structure; the result has zero inner product
   with all previous vectors (verified by `numpy.dot`).

4. **Alpha-Decay Transport.** Key example: a nucleus of U-238 emits an alpha
   particle with a half-life of 4.47 billion years; the tunneling probability is
   an exponential of the classically forbidden path integral; the decay rate is
   the algorithmic output of the Gamow factor — a stochastic transition computed
   by the quantum transport through the Coulomb barrier.

5. **WITNESSED in Lean.** Key example: `WITNESSED` in Episode10.lean — examine
   its definition; it is the bridge from `TRUTH` to the witnessed record; a
   term of type `WITNESSED p` provides proof that p has been transported through
   an admissible process to the current context; without this transport, the
   truth is in the record but not yet witnessed.

Lean anchors:

- `device/Measurement/Episode8.lean`
- Instance cascade `STEP_1` through `ACOLYTE_PROPAGANDA`
- `device/Measurement/Episode9.lean`
- `Science`, `LearningProcess`, `SCIENTIFIC`
- `Knowledge`, `Knowledge.le`, `ScientificProcess`, `TRUTH`
- `Gospel`, `ReligiousProcess`
- `device/Measurement/Episode10.lean`: `WITNESSED`

Phenomena from Claude:

- Alpha-Decay Effect
- Gamma Decay Effect

Disposition: Shadow Tomography is inside Book 3 Ch 7. It is a quantum
algorithm (reconstructing a quantum state from physical measurements) and
belongs in the algorithmic register, not the physical one. Remove from Book 2.

Disposition: Gosset Effect stays in Book 2 Ch 2 (physical/industrial
inference). It is outside Book 3 unless the source box is rewritten around
minimum-sample-size as an algorithm — which would require a new source box.

Future work: Einstein Effect from source Ch 7 — disposition requires reading
the source box. If it is a shortest-path or admissible-refinement-chain
argument, it belongs here. If it recaps special relativity, it is outside
Book 3.

Algorithmic forms:

- LU decomposition
- Adjoint method
- Backpropagation
- Stochastic transition algorithms

### Coda Candidate

Metaphor: auditing an expense report backward through its approvals.

A reimbursement request arrives at accounting. The auditor traces it backward:
final reimbursement amount → manager approval (was this within budget?) →
department head sign-off (was the trip authorized?) → receipt bundle (do the
receipts sum to the claim?) → original purchase (was this category
allowable?). Each step is an adjoint operation: the forward direction is
spending; the backward direction is verification. `WITNESSED` is the signed
approval at each step — proof that the expense was transported through an
admissible process to the current context. An unwitnessed expense (a receipt
with no approval) is in the record but not witnessed; it cannot be reimbursed
until the transport chain is completed. Backpropagation of the gradient is
the audit tracing the error signal backward through the approval chain.

Overlap warning: none. The chapter's examples (LU decomposition, neural
network backpropagation, Gram-Schmidt, alpha-decay transport, WITNESSED in
Lean) are all computational or quantum-physical. The expense audit is
institutional and financial. The adjoint transport and witnessing structures
perform without collision.

---

## Ch 8 - The Ruler Algorithm

Closed question: What reference structure lets distinct observers compare their
counts as one physical record?

Chapter job: calibration as hidden reference scale and metric as routing cost.
The chapter shows that comparison requires a named reference — the ruler is not
the measurement, it is the calibration certificate that makes comparison
admissible.

Elaborator thread: `EKG.load` in LeanCalibration.lean initializes the baseline
heartbeat count; `EKG.boolean` reads the current count; `ComputerProgram.le`
asks whether one program's heartbeat cost is ≤ another's; the EKG is the
calibration — the reference, not the count.

### Sections and Key Examples

1. **Tail-Latency Measurement.** Key example: a web service processes 10,000
   requests/second; sort the latencies and find the 9,900th — that is the
   99th percentile, the ruler for SLA compliance; any request slower than this
   ruler value is a violation; the ruler is the calibrated reference, not a
   threshold chosen arbitrarily.

2. **Dijkstra as Ruler Algorithm.** Key example: finding the shortest path from
   server A to server Z in a network of 1,000 nodes using Dijkstra's algorithm
   — at each step, select the unvisited node with minimum accumulated cost;
   the cost is the ruler; the algorithm terminates when the ruler reaches Z.

3. **EKG as Calibration Reference.** Key example: write two Lean definitions —
   one simple (`def a := 1`) and one complex (a multi-level typeclass instance);
   check `a.ekg` and the complex instance's ekg value; `ComputerProgram.le`
   compares them through the calibration; the EKG is the reference scale,
   not a local measure.

4. **Gram-Schmidt as Sequential Ruler.** Key example: Gram-Schmidt builds an
   orthonormal basis — each new vector is the ruler for one dimension; before
   adding a new vector, its inner products with all previous vectors are
   measured (the calibration check); any nonzero inner product is subtracted
   before the vector is admitted.

5. **Coordinate Transform as Recalibration.** Key example: converting a
   temperature measurement from Fahrenheit to Celsius — T_C = (T_F - 32) × 5/9;
   this is recalibration, not measurement; the same physical quantity acquires
   a new number under a new reference scale; the calibration certificate (the
   offset 32 and scale 5/9) must be carried through the transform.

Lean anchors:

- `device/Measurement/Episode10.lean`
- `Truth`, `Truth.le`, `UniverseTensor`, `REAL`
- `Variation`, `BigRedDogProcess`, `LOCAL`
- `device/Measurement/Calibration/LeanCalibration.lean`: `EKG`

Phenomena from Claude:

- Tail-Latency Effect
- Traffic Effect
- Nyquist-Shannon / Fourier-Nyquist: inside here. Use the existing source name
  (Fourier-Nyquist Effect) unless a new digital-gauge box is written for the
  algorithmic register specifically.
- EKG / heartbeat visual language: inside here as the algorithmic reference
  scale. Not a new phenomenon — it is the calibration thread from Ch 1.

Algorithmic forms:

- Coordinate transformation
- Gram-Schmidt
- Parallel transport
- Routing under worst-case latency

### Coda Candidate

Metaphor: a factory quality-control room with gauge blocks.

The QC room contains a set of precision gauge blocks — hardened steel blocks
machined to exact thicknesses (e.g., 1.000 mm, 2.000 mm, 5.000 mm). Every
part that comes off the production line is compared against the gauge blocks,
not against a local opinion or the previous part. A part is accepted if its
thickness falls within tolerance relative to the gauge blocks; rejected if
not. The gauge block set is the `EKG` — the calibrated reference against
which all comparisons are made. `ComputerProgram.le` asks whether one program's
elaboration cost is within tolerance of the reference. Routing is by cost:
low-cost programs pass, high-cost programs are flagged for review. The
coordinate transform (converting millimeters to inches) is recalibration: the
same gauge blocks in new units, the calibration certificate carried through
the conversion.

Overlap warning: none. The chapter's examples (99th-percentile latency,
Dijkstra on a network, EKG comparison in Lean, Gram-Schmidt as sequential
ruler, Fahrenheit-to-Celsius recalibration) are all computational or
algorithmic. The QC room is manufacturing and metrology. The reference-scale
and routing structures perform without collision.

---

## Ch 9 - Commutation Failure

Closed question: What records the failure of transport to commute?

Chapter job: commutator, residual, curvature, and compiler strain as fabric.
The chapter shows that when two transport operations do not commute, the failure
is itself a structured quantity — the commutator — and it is the algorithmic
record of curvature.

Elaborator thread: `HeartbeatProcess` in Episode11.lean records how much
elaboration cost has accumulated along each proof path; the heartbeat count at
each step is the record of computational burden; if two proof strategies
commute (same heartbeat total regardless of order), they are informationally
equivalent; if not, the difference is elaboration strain.

### Sections and Key Examples

1. **The Matrix Commutator.** Key example: rotation matrices R_x (90° around
   x-axis) and R_y (90° around y-axis); compute R_x R_y and R_y R_x in numpy
   — the two products differ; their difference [R_x, R_y] = R_x R_y - R_y R_x
   is a rotation about the z-axis; the commutator records the failure and
   identifies the curvature direction.

2. **Git Merge Conflict.** Key example: Alice and Bob both modify line 40 of
   the same file independently; Alice's change and Bob's change do not commute
   — applying Alice's then Bob's differs from Bob's then Alice's; git reports
   a conflict; the merge resolution is the admissible record that closes both
   changes.

3. **Compiler Optimization Order.** Key example: in LLVM, run constant folding
   then dead code elimination vs. dead code elimination then constant folding
   on the same function; check whether the output IR is identical; some
   optimization pairs commute (same result regardless of order); some do not
   (one exposes the input for the other); the non-commuting pairs are curvature
   in the optimization lattice.

4. **Jacobi Identity.** Key example: for the Lie algebra sl(2) with generators
   E, F, H, verify the Jacobi identity [[E,F],H] + [[F,H],E] + [[H,E],F] = 0
   in Python; the identity confirms that the algebra of transport closes without
   contradiction — the curvature is self-consistent.

5. **HeartbeatProcess in Lean.** Key example: `HeartbeatProcess` in Episode11.lean
   — run two different proof strategies for the same goal and compare their
   heartbeat counts; if the counts differ, the strategies are not equivalent
   under transport; the heartbeat difference is the elaboration strain recorded
   in the YarnTheory fabric.

Lean anchors:

- `device/Measurement/Episode11.lean`
- `SpaceTimePath`, `SpaceTimePath.le`
- `CalculusProcess`, `UNIVERSAL`
- `YarnTheory`, `YarnTheory.le`
- `HeartbeatProcess`

Phenomena to place:

- Message Effect: inside Book 3 Ch 9. Framed as algorithmic communication/
  transport failure — the noncommuting residue of two message-passing strategies.
  Outside Book 1 and Book 2.

Algorithmic forms:

- Matrix commutator
- Jacobi identity
- BCH formula
- Gibbs-like residual as irreducible smoothing artifact

### Coda Candidate

Metaphor: print-shop color layers laid down in different orders.

A print shop runs a four-color job: cyan, magenta, yellow, black. The press
operator loads the plates and chooses the print order. Cyan then magenta then
varnish produces one result; varnish then magenta then cyan may produce
another — the varnish seals the ink differently depending on what is already
on the paper. The difference between the two orderings is visible in the final
print: a color cast, a gloss differential, a trapping failure. The commutator
is the visible residue. `SpaceTimePath` is the paper's path through the
press; `YarnTheory` tracks how the ink layers interact; `HeartbeatProcess`
records the drying time between layers; the commutation failure is the strain
recorded in the final color profile.

Overlap warning: the chapter's key examples include git merge conflict and
LLVM optimization order. The print shop is a different enough register
(physical, craft, color) to work without collision — but the coda prose
should not use version-control language, code-optimization language, or
matrix algebra. Keep it in the print shop: inks, press, paper, color.

---

## Ch 10 - Invariant Computation

Closed question: What remains invariant under admissible relabeling or
recompilation?

Chapter job: recompilation invariance, staged artifact, and algorithmic
symmetry. The chapter shows that some quantities survive any admissible
relabeling of the computation — these are the invariants that computation can
trust.

Elaborator thread: `ElaborationProcess` in Episode12.lean moves load →
transform → boolean; `HALTED` marks only boolean as final; the invariant is
the program's semantic content — the same fact expressed in source or compiled
form has the same type; recompilation returns the same type.

### Sections and Key Examples

1. **Bootstrapping a Compiler.** Key example: the Lean 4 compiler was
   bootstrapped — stage 1 (written in C) compiled the Lean source; the output
   compiled itself; run `lean --version` before and after recompiling from
   source — the version string (and the binary hash) should match; the fixed
   point is the invariant; recompilation is its test.

2. **Gradient Descent Invariance.** Key example: train the same neural network
   on MNIST twice, once with neurons in the hidden layer numbered 0..127 and
   once with them renumbered by a random permutation; after convergence, the
   loss values match; the loss function is invariant under neuron relabeling —
   it is the invariant that the optimization preserves.

3. **Ising Model Phase Transition.** Key example: simulate the 2D Ising model
   at T = 2.0 (below T_c = 2.269) and T = 3.0 (above T_c) using a Metropolis
   algorithm; below T_c, all spins align (broken symmetry); above T_c, they
   are random (restored symmetry); flipping all spins is a symmetry of the
   Hamiltonian, but the low-T ground state breaks it — the order parameter is
   the invariant that detects the broken symmetry.

4. **Feynman Diagram as Computation.** Key example: the one-loop correction to
   the electron's magnetic moment — the Feynman diagram for the vertex
   correction represents a term in the perturbation series; the amplitude is
   invariant under relabeling of the internal momentum variable (by change of
   integration variable); this invariance is the algorithmic reason the
   Feynman rules are consistent.

5. **ElaborationProcess in Lean.** Key example: `ElaborationProcess` in
   Episode12.lean — inspect the `execute` function; it moves load → transform
   → boolean; `HALTED` is provable only for the boolean step; the source program
   and the compiled program have the same type (the same fact), but only
   boolean is final; the type is the invariant; recompilation preserves it.

Lean anchors:

- `device/Measurement/Episode12.lean`
- `LOGICAL`, `ComputerProgram.le`, `ElaborationProcess`, `HALTED`
- `device/Measurement/Episode13.lean`
- `Measurement`, `Measurement.le`, `LeanProcess`, `MEASURED`
- `device/Measurement/Episode14.lean`
- `CompilerTape`, `CompilerOutput`, `COMPILED`

Phenomena from Claude:

- Semiconductor Effect
- Echo Chamber Maze Solution
- Feynman Diagram
- Ising Effect

Algorithmic forms:

- Gradient descent
- Equivariant computation
- Search over paths
- Phase transition as bifurcation

Warning:

- Standard Model structures are not in the current Lean files. Treat them as
  future expansion, not current implementation.

### Coda Candidate

Metaphor: a theater production with rotating understudies.

A theatrical company performs a work that has been running for fifteen years.
The original cast has been entirely replaced by understudies; the understudies
have been replaced by their understudies. The props are replicas of the
original props. The lighting rig has been updated to LED. And yet the
production is "the same play." What is invariant? Not the actors, not the
props, not the rig — but the type: the relational structure of the
performance, the spatial and temporal pattern that survives any admissible
substitution of implementation. `ElaborationProcess` moves load → transform
→ boolean; `HALTED` marks only the boolean (the performance, not the rehearsal)
as final; recompilation (recasting) returns the same type if the production
is the same play. The invariant is the semantic content — the play's identity
— not the version of the actors.

Overlap warning: the chapter's key example (Lean 4 bootstrapping) is already
a fixed-point invariance story. The theater frames it differently: actors are
the implementation, the play is the type. The coda should make that distinction
explicit: what would have to change for this to be a different play? That
question is the invariant computation's diagnostic test.

---

## Ch 11 - Incompressibility

Closed question: Why does the record only grow, and when is it closed enough to
support inference?

Chapter job: append-only computation, proof checking, closure, and the final
type-check. The chapter shows that some records cannot be made shorter —
incompressibility is not a limitation but the signature of a fully-loaded
record.

Elaborator thread: in Lean, every proof step adds to the proof term; steps
cannot be unproved; `#check theory_true?` at the end of Episode15.lean asks
whether the accumulated burden type-checks; the elaborator's verdict is not
an execution of the physics — it is a question about type formation.

### Sections and Key Examples

1. **Lempel-Ziv Compression.** Key example: compress a 1 MB English text file
   with `gzip` (which uses LZ77) — typical ratio 3:1 to 4:1; compress a 1 MB
   file of `/dev/urandom` output — ratio ≈ 1:1 (no compression); the random
   file is incompressible by definition: K(w) ≈ |w|; the English text is
   compressible because it has pattern.

2. **Kolmogorov Structure Function.** Key example: a protein sequence — some
   regions are compressible (repeated motifs, conserved domains with known
   patterns); some are random (intrinsically disordered regions); the structure
   function h(k) measures the minimum description length for the compressible
   part at each scale k; the random part is the irreducible component.

3. **Interactive Proof Checking.** Key example: in Lean, prove `theorem
   add_comm (n m : Nat) : n + m = m + n` step by step using `induction`,
   `simp`, and `rfl`; each tactic adds a step to the proof term; the kernel
   checks each step; no step can be removed without breaking the proof;
   the proof is the write-once tape; `#print add_comm` shows the accumulated
   record.

4. **The Final Type Check.** Key example: `#check theory_true?` in Episode15.lean
   — run it and observe the compiler's response; the question is type formation:
   does the accumulated formal burden have a type? The answer is not an
   execution; it is the elaborator's verdict on whether the record is internally
   consistent; this is the book's last sentence in code.

5. **Amdahl's Law as Incompressibility.** Key example: profile a program and
   find that 5% of the runtime is serial (cannot be parallelized); add 1,000
   processors; the speedup is bounded by 1/(0.05 + 0.95/1000) ≈ 19.6×, not
   1,000×; the serial fraction is the incompressible core; no amount of
   additional parallelism can compress it further.

Lean anchors:

- `device/Measurement/Episode15.lean`
- `Bullshit`, `Bullshit.le`, `Bullshit.lt`
- `AtreyuProcess`, `TrueOutput`
- `truthCarrier`, `DISTINGUISHABLE_PROP`, `truthDistinct`
- `Fact.SAME`
- `Closure`, `Closure.le`, `EquivalenceProcess`
- `INFERRED`, `INFERRED_TRUE`
- `theory_true?`

Phenomena from Claude:

- Superconducting Effect
- Excel Effect
- Agent Effect
- Amdahl Effect
- Jupyter Effect
- Prover-Verifier Effect

Disposition notes:

- Landauer remains physical in Book 2, but Book 3 should keep the algorithmic
  echo: stopping, erasing, and proving all leave ledger burden somewhere.
- The final question is type formation, not cosmic execution.

### Coda Candidate

Metaphor: a notary's sealed register.

The notary's register is the write-once ledger of witnessed acts: each entry
records the date, the parties, the document type, and the notary's seal.
Entries are added but never removed. The register can be summarized (this
notary witnessed 847 acts in 2024), but the summary cannot replace the register
— the seal and the witness signatures are the proof, and compressing them away
loses the proof. `Closure` names the moment when the register is closed at
end of business: no further entries are admissible until morning. `Closure.le`
asks whether one register's closure is at least as strong a record as another's.
`INFERRED` marks a claim that can be inferred from the register's pattern
but not directly read off any single entry; `INFERRED_TRUE` marks one that has
been verified against an independent record. `theory_true?` is the last act:
does this register, as sealed, constitute an internally consistent and
sufficient proof record?

The notary's register and `#check theory_true?` are the same machine. That
sentence is the coda's last line.

Overlap warning: none. The chapter's examples (gzip on random vs. text data,
Kolmogorov structure function on proteins, Lean `add_comm` proof, `#check
theory_true?`, Amdahl serial fraction) are computational and proof-theoretic.
The notary register is legal, institutional, and pre-digital. The proof-
checking and closure structures perform without collision. This is the right
final image for Book 3.

---
