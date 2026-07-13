# Scientific Computation — Volume Four adversarial outline

Status: active rebuild, 2026-07-11.

This outline supersedes the old Volume 4 prose order for the section-by-section
rewrite. It does not authorize changing Episodes 1–15. Those files remain sacred
and read-only.

## The three budget gauges

There is no per-section word quota.

1. **Ceiling:** never overrun the book's global envelope. Remove repetition before
   removing an experiment, formula, or logical dependency.
2. **Parity:** compare a section with its siblings in the same part. The early
   construction may be heavier than the late read-back, but an isolated thin
   section must justify its thinness.
3. **Emergent total:** track the accumulated PDF and prose mass; never pad toward a
   target.

Depth rule: aim for roughly three times the worked examples and twice the original
novel logic, filled with experiment descriptions, formulas, and actual code
dependencies. Do not inflate citations or repeat settled background.

## Adversarial section gate

Every section passes this exact sequence:

1. Root publishes the section contract from this outline.
2. **Writer agent** edits only the named TeX section.
3. **Verifier agent** reads the prose and the live dependency graph. It classifies
   every substantive sentence as BUILT, MEASURED, PHYSICS, INTERPRETED, or REJECT.
4. The verifier performs a **name resonance audit**:
   - a numerical value belongs to computation or physics, never both;
   - if the same number appears on both sides, the equality must be independently
     established and the two provenance chains shown;
   - if the same process appears on both sides, the process identity must be shown
     while the vocabularies remain disjoint;
   - no shared name counts as evidence.
5. Root resolves every rejection, builds the whole PDF, and records section word
   count, page count, warnings, and gate result.
6. Only then does the next section start.

The verifier trusts declarations and experiment descriptions, not filenames.
device/Measurement/attic may be discussed only as historical or rejected work.

## Register rule

Volume 4 is the reading gauge. It may put computation and physics beside each
other, but it must mark the seam.

- **Computation owns:** data structures, decidability, recursion, iteration,
  slicing, floors, costs, brackets, compiler reports, Shannon information,
  Turing decidability, Chaitin description bounds, and Cohen-style finite
  conditions.
- **Physics owns:** force, mass, charge, phase, field, curvature, coupling,
  laboratory apparatus, and empirical constants.
- **Interpretation owns:** any claim that a computational object should be read by
  a physical name.

For every resonant name, prose must state which gauge owns it. A shared name marks
a proposed correspondence, not an equality. A claimed same number or same process
must show two separate routes and the comparison map.

## Algorithm ledger: iteration and slicing

| Data structure | Iterative method | Slicing/selection method | Live anchor |
|---|---|---|---|
| Sequence | constructor refinement | terminal/index case split | Episode1.lean |
| CauchyProcess | stored iterate transition | current value versus named accumulation | Episode1.lean |
| Sample | response/history propagation | constructor and order branches | Episode1.lean |
| class/instance tower | synthesis through successive requirements | each class exposes a narrower interface | Episodes 1–16 |
| naming tower | Nat to Fin iteration | boxOf partitions variations | NamingClose.lean |
| ApparatusRatio | repeated arithmetic composition | quotient, remainder, scaled floor | Episode26.lean |
| three-point stencil | lower/middle/upper traversal | second-difference slice | Episode27.lean |
| proximity grid | distance scan | first crossing cell | Episode28.lean |
| SlipBisectBracket | bisectSlipAux recursion | retain crossing half | Episode29.lean |
| arithmetic ledgers | finite progression sums | fixed count windows | Episode30.lean |
| DyadicSlipBracket | bisectDyadicSlipAux | midpoint and dyadic half | Episode35.lean |
| NodeSelector | evaluate node list | midpoint or three-node selection | AlphaBoundCountToThree.lean |
| count-to-three report | evaluate successive counts | count-2/count-3 lids | AlphaBoundCountToThree.lean |
| self-application meter | warmup/read sequence | subtract selected costs | SelfApplication.lean |

Negative facts the book must preserve:

- A field named iterate is not a convergence theorem.
- A three-field bracket is not a certified enclosure.
- A finite partition gives a collision, not automatically a periodic orbit.
- Gauss–Legendre quadrature is not automatically a root enclosure.
- Lean heartbeats are toolchain allocation counters, not physical time or energy.

## Part I — The grammar of a reading

### Structure of representation

Every scientifically meaningful name is audited against
\[
\mathcal R=(X,\Sigma,E,Q,\Pi,I,F;\rho).
\]
Here (X) is the represented domain or carrier, (\Sigma) is the name space,
(E:X\to\Sigma) is an encoding when one is actually supplied, (Q) is the
executable question or decision procedure, (\Pi) is the partition or family
of slices induced by that question, (I) is the invariant preserved by the
operation, (F) records failure, ambiguity, or underdetermination, and
(\rho\in\{\text{computation},\text{physics}\}) records provenance. A component
absent from the code or experiment remains absent. Shared notation across the
two provenances is admitted only when it denotes the same number or the same
process; it does not merge the interpretations.

Coined-name ledger: `nowtrino` is computation-owned and may name a current-summary
projection after prior history is sliced away. `newtrino` is computation-owned
and may name the next state constructed by a declared update from that summary.
`naotrino`, coined from Greek `naos` (temple), is reserved for a physical
candidate only after an apparatus and physical model are declared; it must be
identified as this manuscript's coinage.
`\nu`-trino belongs to the standard neutrino-physics register and may be used only
with the established model and observables that license that reading. A declared
transition may connect `nowtrino` to `newtrino`; no spelling-based bridge connects
either computational name to either physical name. Resonance alone establishes
neither a shared number nor a shared process.

Covariant-apparatus ledger: the robot is not a transparent conduit. A physical
action is recorded as a transition of both world and apparatus,
`(N,s) -> (N',s',y,trace)`, not merely as returned observation `y`. Licensing
retains back-action, sensor loading, actuation, exchanged energy or material,
latency, hysteresis, drift, saturation, geometry, calibration history,
environment, prior robot state, rejected outcomes, and alternative causal
models. The world answers the declared intervention; agreement does not imply
an untouched world, independent routes, or identical processes. This baggage
is part of the covariant witness and may not be sliced away before naming.

Reader-facing exposition uses an implementation-neutral grammar rather than
proof-assistant vocabulary. Its primitive forms are finite representations,
questions, decision evidence, updates, slices, stopping rules, error bounds,
and certificates. Source declarations remain a silent conformance test, not
the book's diction. Continuous behavior is never inferred from a suggestive
name: a limit, field, wave, or continuum claim requires an identified discrete
scheme, a discretization parameter, and a stated convergence bridge. Otherwise
the book reports only the numerical method actually executed.

### Chapter 1 — A Mark Becomes a Question

#### 1.1 Difference is a predicate, not a particle
- Code: Fact, CarrierProcess, DISTINGUISHABLE.
- Computation: \(D(s,\sigma):=(s\ne\sigma)\);
  Shannon \(I(x)=-\log_2 p(x)\).
- Examples: telegraph mark, comparator, Lean proposition/decision pair.
- Fence: Fact does not contain a proof; DISTINGUISHABLE is not a detector.

#### 1.2 The symbol and the receiver
- Code: symbol, different?, dec_distinct.
- Computation: decoding basis and kernel; Shannon channel language.
- Physics resonance: signal/detector is analogy unless an experiment supplies it.
- Slicing: the receiver partitions accepted and rejected candidates.

#### 1.3 From a decision to a record
- Code: Natural, Rational, Sequence.
- Computation: constructor tree, terminal/index slices, finite encoding.
- Cohen: a finite condition is a partial record, not a generic extension.

### Chapter 2 — Iteration Does Not Mean Convergence

#### 2.1 Counting is an interface
- Code: ADMISSIBLE, COUNTABLE, IndexingProcess.
- Shannon: codebook/index distinction.
- Fence: the class name does not prove a bijective enumeration.

#### 2.2 The iterator and the alleged limit
- Code: CauchyProcess.
- Algorithms: transition function, trajectory, stopping predicate.
- Chaitin: finite descriptions versus claims about infinite tails.
- Fence: no metric or Cauchy modulus is present unless separately supplied.

#### 2.3 Slicing a sequence
- Code: Sequence cases and ENCODED relation.
- Algorithms: structural recursion, terminal/index slicing.
- Cohen: compatible finite conditions, explicitly marked analogy.

### Chapter 3 — Residue Is Stored Information

#### 3.1 The branch that cannot be silently discarded
- Code: RESIDUE and Sample.
- Computation: quotient/remainder identities and loss accounting.
- Examples: integer division, checksum, truncated record.

#### 3.2 Iterative error versus structural residue
- Algorithms: \(e_{n+1}=T(e_n)\), fixed points, nonzero remainder.
- Turing: termination requires a proof/model, not a name.
- Physics resonance: dissipation and hysteresis marked physical.

#### 3.3 Observation becomes history
- Code: OBSERVED and history-bearing structures.
- Computation: slice current reading from accumulated record.
- Shannon: sufficient statistic versus discarded information.

## Part II — Two ways through a finite object

### Chapter 4 — The Forward Pass and the Return Pass

#### 4.1 Requirements pull backward
- Code: class requirements and instance synthesis.
- Preface map: observation \(O:S\to R\), admissible fibers.
- Cohen: requirements as finite conditions.

#### 4.2 Witnesses run forward
- Code: constructed instances and proof terms.
- Turing: executable witness versus oracle assertion.
- Algorithm: dependency traversal and memoized reuse.

#### 4.3 Two-pass calibration
- Design: two direct candidates and one formal superposition per pass.
- Algorithms: overlap, preregistered transitions, round-trip closure.
- Fence: design until implemented and printed by a build target.

### Chapter 5 — Bracketing Without Guessing

#### 5.1 A crossing predicate
- Code: rationalSlipFloor and target predicate.
- Math: monotonic crossing assumptions stated explicitly.
- Physics resonance: static/kinetic slip remains marked interpretation.

#### 5.2 Bisection is iteration by slicing
- Code: bisectSlipOnce and bisectSlipAux.
- Math: \(w_n=(b_0-a_0)2^{-n}\) under enclosure hypotheses.
- Compare with Newton iteration without conflating algorithms.

#### 5.3 A report is not a theorem
- Code: SlipBisectReport and summaries.
- Distinguish computed endpoints, certified enclosure, and interpretation.
- Worked counterexample: malformed initial bracket.

### Chapter 6 — The Owned Floor

#### 6.1 Dyadic data structure
- Code: DyadicSlipBracket and midpoint conversion.
- Slicing: denominator doubling and half selection.
- Fence: denominator/order invariants must be checked.

#### 6.2 Resolution as an explicit parameter
- Code: rungs, cells, scale, floors.
- Shannon: finite alphabet resolution.
- Chaitin: a resource bound does not make an empirical constant uncomputable.

#### 6.3 Stop rules and budgets
- Code: finite fuel and live EKG bounds.
- Turing: local termination versus universal halting.
- Examples: fuel exhaustion, tolerance stop, bracket-width stop.

## Part III — Names and their resonances

### Chapter 7 — One Structure, Separate Gauges

#### 7.1 Computation names
- Count, bit, cost, bracket, remainder, each tied to a declaration.

#### 7.2 Physics names
- Mass, charge, phase, field, coupling, with equations first.
- No code name used as physical evidence.

#### 7.3 Same number or same process
- Separate provenance diagrams and explicit comparison maps.
- No shared-name bridge.

### Chapter 8 — Finite Naming

#### 8.1 Partition and collision
- Code: Variation, boxCount, boxOf, pigeonhole theorem.
- Math: exact finite pigeonhole statement.

#### 8.2 A collision is not a cycle
- State the transition compatibility needed for periodicity.
- Give finite-state examples with and without deterministic cycling.

#### 8.3 When a physical name is licensed
- Code: electronBox and naming theorem.
- Mark stipulated label versus derived finite fact.
- Apply the two-pass naming criterion.

### Chapter 9 — Rotation, Phase, and Relabeling

#### 9.1 Computational rotation
- Code: variation, order, sign, permutation, parity.

#### 9.2 Physical phase
- Math: \(e^{i\theta}\), holonomy, spinor return, physical provenance.
- Two instances do not by themselves construct a complex plane.

#### 9.3 Resonance audit
- Same-process test: composition law and invariant.
- Same-number test: separate routes and equality.

## Part IV — The apparatus and its algorithms

### Chapter 10 — Quotient and Remainder

#### 10.1 ApparatusRatio
- Code: numerator/denominator, floor, remainder, scaled floor.
- Math: \(n=qd+r\), \(0\le r<d\) only under \(d>0\).

#### 10.2 The physical balance
- Physics: Cavendish/torsion equations, units, uncertainty.
- Code route remains a separate internal ratio.

#### 10.3 Slicing the same ledger
- Algorithms: quotient, remainder, and inverse slices.
- Examples: zero denominator and truncation.

### Chapter 11 — The Compiler as Meter

#### 11.1 What a heartbeat counts
- Code/toolchain: allocation-counter semantics.
- Shannon: description and cost; no physical-time claim.

#### 11.2 Warmup, read, subtract
- Code: register_cost, cost readings, residuals.
- Algorithm: paired measurement and subtraction.

#### 11.3 Self-application without mystification
- Code: what is elaborated and normalized.
- Chaitin/Turing: precisely scoped self-description limits.
- Fence: compiler cost is not electron self-energy.

### Chapter 12 — Finite Field-Shaped Ledgers

#### 12.1 Second differences
- Code: lower/middle/upper and secondDifference.
- Math: \(\Delta^2f_k=f_{k+1}-2f_k+f_{k-1}\).

#### 12.2 Physics field equations
- Maxwell and Meissner equations with experimental meaning.
- Booleans do not prove PDEs.

#### 12.3 Iteration and slicing in the field report
- Trace data flow from stencil to ratio to report.
- Identify stored coefficients versus coefficients actually consumed.

## Part V — Calibration and the jar

### Chapter 13 — The Compiler Structure Constant

#### 13.1 The internal formula
- Code: alphaFromSecondVariationAtDistance.
- Full dependency graph; distinguish stored fields from consumed inputs.

#### 13.2 The count-to-three bracket
- Exact crossing: \(d_*=\sqrt{18/5}\) and periodic continued fraction.
- Three whole partial quotients select adjacent convergents and the owned open
  jar \((129.6,137.7)\).
- The older grid/dyadic construction is superseded and owns no bracket.

#### 13.3 Nodes, quadrature, and root finding
- Code: NodeSelector, approximate Legendre nodes, weighted average.
- Separate quadrature of an integral from root enclosure.
- Physical alpha appears only as an external comparison.

### Chapter 14 — Witness, Observation, and Two Descriptions

#### 14.1 The two propositions
- Code: exact definitions and exact content of propext proof.

#### 14.2 The cost readings
- Code: orbit/pair/echo and residual definitions.
- Measured values retain toolchain provenance.

#### 14.3 The proposed second pass
- Connect the calibration implementation when it exists.
- Until then separate proof equality, cost equality, and interpretation.

### Chapter 15 — The Jar

#### 15.1 What is built
- Root import graph, theorem/evaluation ledger, axiom footprints.

#### 15.2 What is measured
- Toolchain version, reproducibility scope, parameter sensitivity.
- Full structures-to-iteration-to-slices-to-reports map.

#### 15.3 What is interpreted
- Name resonance ledger across computation and physics.
- alpha_c remains compiler-first.
- End with the reader rerunning both passes and owning only the jar.

## Progress ledger

| Section | Writer | Verifier | PDF | Status |
|---|---|---|---|---|
| 1.1 | grammar scrub complete | ACCEPT | 133 pages; build clean | green |
| 1.2 | grammar scrub complete | ACCEPT + rendered audit | 136 pages; build clean | green |
| 1.3 | grammar scrub complete | ACCEPT + rendered audit | 138 pages; build clean | green |
| 2.1 | grammar scrub complete | ACCEPT + rendered audit | 141 pages; build clean | green |
| 2.2 | grammar scrub complete | ACCEPT + rendered audit | 142 pages; build clean | green |
| 2.3 | grammar scrub complete | ACCEPT + rendered/context audit | 146 pages; build clean | green |
| 3.1 | grammar scrub complete | ACCEPT + rendered/context audit | 147 pages; build clean | green |
| 3.2 | grammar scrub complete | ACCEPT + rendered/context audit | 151 pages; build clean | green |
| 3.3 | grammar scrub complete | ACCEPT + rendered/context audit | 154 pages; build clean | green |
| 4.1 | grammar scrub complete | ACCEPT + rendered/context audit | 157 pages; build clean | green |
| 4.2 | grammar scrub complete | ACCEPT + rendered audit | 160 pages; build clean | green |
| 4.3 | grammar scrub complete | ACCEPT + rendered audit | 164 pages; build clean | green |
| 5.1 | grammar scrub complete | ACCEPT + rendered audit | 167 pages; build clean | green |
| 5.2 | grammar scrub complete | ACCEPT + rendered audit | 169 pages; build clean | green |
| 5.3 | grammar scrub complete | ACCEPT + rendered audit | 172 pages; build clean | green |
| 6.1 | grammar scrub complete | ACCEPT + rendered/context audit | 174 pages; build clean | green |
| 6.2 | grammar scrub complete | ACCEPT + rendered/context audit | 177 pages; build clean | green |
| 6.3 | grammar scrub complete | ACCEPT + rendered audit | 179 pages; build clean | green |
| 7.1 | grammar scrub complete | ACCEPT + rendered audit | 180 pages; build clean | green |
| 7.2 | grammar scrub complete | ACCEPT + rendered/context audit | 182 pages; build clean | green |
| 7.3 | grammar scrub complete | ACCEPT + rendered audit | 184 pages; build clean | green |
| 8.1 | grammar scrub complete | ACCEPT + rendered audit | 186 pages; build clean | green |
| 8.2 | grammar scrub complete | ACCEPT + rendered audit | 188 pages; build clean | green |
| 8.3 | grammar scrub complete | ACCEPT + rendered audit | 190 pages; build clean | green |
| 9.1 | grammar scrub complete | ACCEPT + rendered audit | 191 pages; build clean | green |
| 9.2 | grammar scrub complete | ACCEPT + rendered audit | 194 pages; build clean | green |
| 9.3 | grammar scrub complete | ACCEPT + rendered audit | 197 pages; build clean | green |
| 10.1 | grammar scrub complete | ACCEPT + rendered audit | 199 pages; build clean | green |
| 10.2 | grammar scrub complete | ACCEPT + rendered audit | 200 pages; build clean | green |
| 10.3 | grammar scrub complete | ACCEPT + rendered audit | 203 pages; build clean | green |
| 11.1 | grammar scrub complete | ACCEPT + rendered audit | 206 pages; build clean | green |
| 11.2 | grammar scrub complete | ACCEPT + rendered audit | 208 pages; build clean | green |
| 11.3 | grammar scrub complete | ACCEPT + rendered audit | 211 pages; build clean | green |
| 12.1 | grammar scrub complete | ACCEPT + rendered audit | 213 pages; build clean | green |
| 12.2 | grammar scrub complete | ACCEPT + rendered audit | 216 pages; build clean | green |
| 12.3 | grammar scrub complete | ACCEPT + rendered audit | 220 pages; build clean | green |
| 13.1 | grammar scrub complete | ACCEPT + rendered audit | 221 pages; build clean | green |
| 13.2 | grammar scrub complete | ACCEPT + rendered audit | 223 pages; build clean | green |
| 13.3 | grammar scrub complete | ACCEPT + rendered audit | 226 pages; build clean | green |
| 14.1 | grammar scrub complete | ACCEPT + rendered audit | 228 pages; build clean | green |
| 14.2 | grammar scrub complete | ACCEPT + rendered audit | 230 pages; build clean | green |
| 14.3 | grammar scrub complete | ACCEPT + rendered audit | 233 pages; build clean | green |
| 15.1 | grammar scrub complete | ACCEPT + rendered audit | 235 pages; build clean | green |
| 15.2 | grammar scrub complete | ACCEPT + rendered audit | 238 pages; build clean | green |
| 15.3 | grammar scrub complete | ACCEPT + rendered audit | 241 pages; build clean | green |
| whole book | final semantic/editorial audit complete | ACCEPT: numerical, ownership, vocabulary, bibliography, rendered and visual audits | 242 pages; cache-busted final published; SHA-256 `d06c51e06709ba476567d0abf4a8bd970f344414b87d44f7c8d677796cd3d32c` | green |
