# Volume 6 - The Experimental History Gauge

Working title: **The Necessary Experiments**

Subtitle: **An Out-of-Order History of Scientific Experiment**

Earlier title seed: **The Universe**. Keep it as the ambition of the book, not
the working title. The title on the page should be more modest and more
structural, in the register of Volume 5's **The Necessary Names**.

Audience: readers who understand science through stories of experiment,
failure, instrument-making, argument, and revision. This is the book for the
reader who does not want the theorem first, the code first, the physics
textbook first, or the rhetorical procession first, but can follow the universe
as the accumulated history of what experiments taught people to trust.

Claim: scientific history is not merely a chronology of discoveries. It is a
history of obligations becoming public. Each decisive experiment taught the
record a new discipline: how to distinguish, admit, count, encode, compare,
repeat, scale, witness, localize, compile, and infer. The universe became
sayable as experiments learned how to make their claims travel.

This volume is "out-of-order" because the order is not the calendar. The order
is experimental necessity.

## What This Volume Is

Volumes 1-5 enter the project through theorem, phenomenon, compiler, trace, and
name. Volume 6 enters through experiment.

It is not a popular history of science in chronological order. It is not a
biography of great scientists. It is not a list of famous experiments. It is an
out-of-order history of the universe as learned by experiment, where each
experiment appears when its obligation becomes necessary.

The book asks one repeated question:

```text
What did this experiment teach the record how to do?
```

If an experiment only illustrates an idea, it does not belong. If it changes
the public discipline of measurement, it belongs.

## Why Out Of Order

Chronology answers the historian's first question: what happened next?

This book answers a different question: what had to become experimentally
possible before the next kind of claim could be trusted?

That means Galileo's telescope may stand near photographic plates, cloud
chambers, LIGO, and double-blind trials if the shared obligation is observation
becoming public. Michelson-Morley may sit beside blackbody radiation,
Mercury's perihelion, and early neutrino evidence if the shared obligation is
residue: the structured leftover that refuses the current theory. Cavendish,
Millikan, Hubble, and the cesium clock may sit together if the shared
obligation is magnitude under scale.

The dates stay visible, but dates do not govern the route. Each episode
header carries two coordinates:

```text
The Cavendish Torsion Balance Effect
[1798 | Staging :: SOURCE -> EXECUTED -> MAGNITUDE]
```

The reader should feel time jumping while the instrument becomes more orderly.

## Why This Is A Gauge

An experimental history gauge measures how the universe became publicly
measurable.

The mathematical gauge proves what order forces. The physical gauge explains
what instruments can measure. The algorithmic gauge follows what the compiler
can build. The reference trace gauge records what Lean accepts. The rhetorical
gauge asks what names can make public. The experimental history gauge asks
what the history of experiment made possible.

It is a gauge because each historical episode is not merely content. It is an
apparatus. The experiment supplies the conditions under which a claim becomes a
reading rather than a story.

The book's danger is romance. Famous experiments invite mythology. This volume
must resist that. The experiment is not great because a genius performed it. It
is great here only if it changed the obligations under which later claims could
be trusted.

## Relationship To The Project

| Volume | Gauge | Pressure | Public shape |
| --- | --- | --- | --- |
| 1 | Mathematical | theorem | what must follow |
| 2 | Physical | phenomenon | what can be measured |
| 3 | Algorithmic | compiler | what can be built |
| 4 | Reference trace | trace | what Lean says |
| 5 | Rhetorical | name | what people can hear |
| 6 | Experimental history | experiment | what history taught the record to trust |
| `GAUGE 1199` | Manga companion | dramatic | what it felt like |

Volume 6 can be read after Volume 5 or beside Volume 2. Volume 5 gives the
names. Volume 6 gives the history of experiments learning those names in
public.

Volume 6 should not replace Volume 2. The physical gauge explains the
machinery of measurement. The experimental history gauge shows how that
machinery entered public life through actual experimental episodes.

The instrument book already contains the project form Volume 6 needs: the
`phenom` entries. Volume 2 should inherit and select from those named effects
for physicists. Volume 6 should inherit specific `phenom` entries from the
instrument book and Volume 2, expand them with historical scene and apparatus
detail, and present them in procession order.

This prevents reinvention. If the instrument book already contains an effect,
Volume 6 should either inherit that effect under the same name or explicitly
explain why a new paired name is needed.

## Spine

The canonical spine is the procession of names from Volume 5.

Volume 6 does not need one chapter per name, but every chapter must map back to
the name procession. A candidate experiment may appear only if it performs one
or more named obligations.

The working movement map:

| Movement | Names | Historical pressure |
| --- | --- | --- |
| Entry | `Fact` through `ENCODED` | how a mark becomes a public record |
| Residue | `RESIDUE` through `MEASURABLE` | how leftovers become disciplined questions |
| Staging | `GUNGAN` through `SCALED` | how protocols turn awkward states into values |
| Overhead | `LOAD` through `ACOLYTE` | how institutions, cost, false certainty, and social force gather around evidence |
| Truth transport | `SCIENTIFIC` through `UNIVERSAL` | how experimental truth travels without leaving witness and locality behind |
| Decision | `LOGICAL` through `INFERRED` | how compiled records license conclusions without owning Truth |

This solves the out-of-order problem. The book jumps through time, but it does
not wander.

## Episode Kernel

Volume 6 should not invent a new episode genre. The instrument book already has
one: the `phenom` form.

Every Volume 6 episode uses a five-block kernel:

```tex
\begin{phenom}{The Name Effect~\cite{sourceYYYY}}
\label{ph:name-effect}

\PhStatement
The structural claim in one paragraph.

\PhOrigin
The historical figure or figures, the source of the insight, and citation.

\PhObservation
What is recorded when the phenomenon appears.

\PhConstraint
The operational rule the phenomenon forces on the record or instrument.

\PhConsequence
What the phenomenon licenses, refuses, or reorganizes.
\end{phenom}
```

The surrounding prose supplies the historical scene, apparatus detail, and
handoff. The kernel prevents anecdote drift.

The mapping from the original six-part episode method into `phenom` is:

| Volume 6 need | `phenom` placement |
| --- | --- |
| Historical scene | surrounding prose before the kernel |
| Experimental pressure | `\PhStatement` |
| Citation and original stance | `\PhOrigin` |
| What was recorded | `\PhObservation` |
| Named obligation | `\PhConstraint` |
| What changed and what was refused | `\PhConsequence` |
| Handoff | surrounding prose after the kernel |

The refusal belongs most sharply in `\PhConsequence`. A Volume 6 episode that
does not refuse something is probably too weak.

## House Rule

No experiment as anecdote.

Each experimental episode must do six things:

1. Carry the two-coordinate header.
2. Name the historical scene.
3. Use the `phenom` kernel.
4. Cross-link the named obligation from the Volume 5 procession.
5. State what the experiment refused.
6. Hand the reader to the next obligation.

No episode enters the draft without a `\PhOrigin` citation. Primary sources are
preferred when readable. Canonical secondary sources are allowed when the
primary report would bury the reader.

The refusal is essential. An experiment that only confirms is too weak for this
book. The best experiments refuse a previous convenience: naked observation,
private witness, uncontrolled comparison, unscaled magnitude, social authority,
or final Truth.

## Example Architecture

Use three kinds of examples, distributed across the whole book.

**Anchor experiments.** These are famous enough to carry a chapter hinge:
Galileo's telescopic observations, Cavendish's torsion balance,
Michelson-Morley, Millikan's oil drops, Rutherford scattering, Eddington's
eclipse plates, Hubble's redshift-distance relation, the Wu experiment,
Bell-test experiments, the cesium clock, the cosmic microwave background, LIGO.

**Corrective experiments.** These keep the book honest by showing refusal,
failure, and correction: N-rays, canal rays, polywater, cold fusion, early
ether-drift searches, failed replications, calibration disputes, instrument
noise mistaken for signal.

**Ordinary and instrument-maker experiments.** These keep the book from
becoming a museum of greatness: kitchen thermometers, clinical trials, seed
trials, tide gauges, standard weights, weather stations, survey chains, lab
notebooks, factory gauge blocks, blind taste tests, clockmakers, opticians,
technicians, field-station records, and statistical quality-control charts.

Corrective and ordinary experiments must not be isolated in one chapter. Each
chapter should include at least one refusal episode and at least one ordinary
or instrument-maker episode. That distribution is the anti-Whig, anti-hero
discipline.

## Naming Convention

Prefer paired names when an obligation is historical rather than heroic.

The instrument book already uses names such as Pythagoras--Planck,
Cauchy--Cantor, Berkeley--Galileo, Peano--Kushim, Hooke--Newton, and
Noether--Galois. Volume 6 should inherit that convention.

Pairing is not ornament. It prevents hero history by making the effect a
relation between insights rather than the possession of one person. Some
candidate pairings:

| Candidate effect | Possible pressure |
| --- | --- |
| Tycho--Mendel | counting as public experimental order |
| Cavendish--Millikan | staged value under scale |
| Michelson--Le Verrier | residue that survives comparison |
| Eddington--Weiss | witnessed transport across distance |
| Lysenko--Lavoisier | propaganda refused by experimental discipline |

The pairings are provisional. Do not finalize without source work.

## Proposed Six-Chapter Shape

This volume is authorized to fill as much room as it needs up to **600 pages**.
The page count is a ceiling, not a target to pad toward.

Planning maximum: **160,000 words** including front matter, chapter prose,
episode kernels, back matter notes, and index scaffolding. A first draft may
come in shorter. If the episode kernels close cleanly at 140,000 words, stop
there. If source work forces more than 160,000 words, split, merge, or cut
episodes before crossing the page ceiling.

At roughly 270-280 words per printed page after white space, tables, citations,
and episode headers, a 155,000-160,000 word manuscript leaves room to remain
under 600 pages. The budget should be treated as an envelope:

```text
preferred range: 145,000-158,000 words
planning ceiling: 160,000 words
hard page goal: <= 600 pages
```

The six chapters follow the six movements. Each chapter is out-of-order in
calendar time but ordered by experimental obligation.

| Unit | Movement | Ceiling | Job |
| --- | --- | ---: | --- |
| Front matter | orientation | 8,000 | teach the reader how to read the out-of-order form |
| Chapter 1 | Entry | 22,000 | show how marks become records |
| Chapter 2 | Residue | 27,000 | show how anomalies become disciplined questions |
| Chapter 3 | Staging | 20,000 | show how protocols produce values and scale |
| Chapter 4 | Overhead | 28,000 | show how cost, institutions, false discovery, and social force attach to experiment |
| Chapter 5 | Truth Transport | 26,000 | show how experimental truth travels through witness, locality, and universal rule |
| Chapter 6 | Decision | 21,000 | show how records compile into inference without owning the universe |
| Back matter | registry, bibliography, index | 5,000 | make the book navigable |
| Total |  | 157,000 | leaves a small reserve under the 600-page cap |

Some historical experiments may recur in more than one chapter if they perform
different named obligations. The repeated episode must receive a distinct
`phenom` kernel each time.

## Section Budget Vocabulary

Volume 6 scales the `Box / Short / Medium / Long` budget method from
`three_gauges.md` into experiment-sized sections.

| Section type | Words | Job |
| --- | ---: | --- |
| Anchor | 3,000-4,200 | full historical scene, apparatus, reception, later reinterpretation, and one or two `phenom` kernels |
| Working | 1,400-2,400 | one substantial episode with one `phenom` kernel and focused apparatus prose |
| Vignette | 500-900 | ordinary, corrective, or instrument-maker episode attached to a nearby anchor |
| Opening | 1,200-2,000 | name the chapter pressure after the episodes are known |
| Close | 1,000-1,800 | close the movement and force the next movement |

Every anchor section must contain a concept sub-budget. These are not extra
budget; they are the internal allocation of the anchor's ceiling. Each anchor
should name the concept load before drafting so it does not sprawl.

## Seeds And New Effects

This table should be filled before chapter drafting. It prevents name
collisions between Volume 6 and the instrument book.

| Chapter | Inherited seeds from `instrument/chapters/*.tex` | New effects likely needed |
| --- | --- | --- |
| 1 - Entry | Berkeley--Galileo, Peano--Kushim, Marconi, Chaitin | Tycho--Mendel; photographic plate effect |
| 2 - Residue | Cauchy--Cantor, Gibbs null?, spectral/quantum residues? | Michelson--Le Verrier; blackbody residue effect |
| 3 - Staging | repeatability?, calibration?, velocity?, stoichiometry?, inverse square? | Cavendish--Millikan; cesium clock effect |
| 4 - Overhead | tail latency?, Bayes?, Gosset t-test, catalyst?, thermostat? | N-rays; cold fusion; Lysenko--Lavoisier; citation cascade |
| 5 - Truth Transport | Galileo, Einstein, Eddington-like frame effects?, decoherence? | Eddington--Weiss; Bell-test transport |
| 6 - Decision | prover-verifier?, library catalog?, dark energy?, combinatorial Standard Model? | cosmological inference; particle discovery threshold |

A trailing `?` marks a seed that has not yet been verified under that exact
label in `instrument/chapters/*.tex`. The inherited seed names above are
placeholders until the Name Registry exists. Before drafting, confirm exact
labels and citations in the instrument source.

## Chapter 1 - Entry

Closed question: how does an event become a public mark?

Names: `Fact`, `DISTINGUISHABLE`, `ADMISSIBLE`, `COUNTABLE`, `ENCODED`.

Chapter job: show that scientific experiment begins before theory. It begins
when an event can be noticed, told apart, admitted under a rule, counted, and
carried in a form someone else can inspect.

Chapter ceiling: **22,000 words**.

Section budget:

| Section | Coordinate | Type | Words | Job |
| --- | --- | --- | ---: | --- |
| Opening | `[Entry]` | Opening | 1,500 | explain why an event is not yet a public mark |
| Peano--Kushim | `[ancient tokens / 1889 | Entry :: COUNTABLE -> ENCODED]` | Anchor | 3,000 | counting becomes public symbolic order |
| Tycho--Mendel | `[late 1500s / 1860s | Entry :: COUNTABLE]` | Anchor | 3,000 | tabular records survive the observer |
| Galileo--Hooke telescopy | `[1610 / 1665 | Entry :: Fact -> OBSERVED seed]` | Anchor | 3,000 | seeing enters a record through notebook and image |
| Berkeley--Galileo | `[1700s / 1600s | Entry :: ADMISSIBLE]` | Working | 1,700 | admissibility as the gate against private assertion |
| Marconi | `[1901 | Entry :: DISTINGUISHABLE -> ENCODED]` | Working | 1,800 | a signal survives transport |
| Chaitin | `[1975 | Entry :: ENCODED]` | Working | 1,800 | encoding meets its structural ceiling |
| Photographic plate | `[1800s-1900s | Entry :: ENCODED]` | Working | 1,700 | observation survives the observer |
| Geiger counter | `[1908 onward | Entry :: BINARY -> COUNTABLE seed]` | Working | 1,400 | discrete clicks become event entries |
| Faraday notebooks | `[1800s | Entry :: ADMISSIBLE -> ENCODED]` | Vignette | 700 | ordinary inscription discipline |
| Harrison H4 chronometer | `[1760s | Entry :: SCALED seed]` | Vignette | 700 | instrument-maker discipline before the theory needs it |
| Kelvin age-of-Earth failure | `[1800s | Entry :: ADMISSIBLE refusal]` | Vignette | 700 | admissible reasoning can still carry inadmissible premises |
| Close | `[Entry -> Residue]` | Close | 1,000 | the mark is carried; the leftover becomes visible |

Concept budgets for anchor sections:

| Section | Concept split |
| --- | --- |
| Peano--Kushim | token record 800; public numeral 800; Peano formalization 700; `COUNTABLE -> ENCODED` consequence 700 |
| Tycho--Mendel | Tycho tables 750; Mendel pea counts 750; tabular records survive observer 750; paired consequence 750 |
| Galileo--Hooke telescopy | apparatus 600; notebook/image discipline 800; public controversy 600; observation as record 1,000 |

Refusal: a witnessed marvel is not yet an experimental record.

Bridge: once marks can be carried, the leftover becomes visible.

## Chapter 2 - Residue

Closed question: what happens when the record leaves something structured
behind?

Names: `RESIDUE`, `BINARY`, `REPEATABLE`, `NUMERIC`, `REPRESENTABLE`,
`PHYSICAL`, `COMPARABLE`, `OBSERVED`, `PRESENT`, `MEASURABLE`.

Chapter job: show that anomalies are not embarrassments to be erased. A real
experiment makes residue visible and then disciplines it.

Chapter ceiling: **27,000 words**.

Section budget:

| Section | Coordinate | Type | Words | Job |
| --- | --- | --- | ---: | --- |
| Opening | `[Residue]` | Opening | 1,500 | define residue as structured leftover, not embarrassment |
| Michelson--Le Verrier | `[1840s-1887 | Residue :: RESIDUE -> COMPARABLE]` | Anchor | 4,000 | planetary residue and null fringe shift both refuse frameworks |
| Planck blackbody residue | `[1900 | Residue :: NUMERIC -> REPRESENTABLE]` | Anchor | 3,400 | a curve forces quantization |
| Brownian--Perrin | `[1827-1908 | Residue :: PHYSICAL -> MEASURABLE]` | Anchor | 3,300 | jitter becomes molecular evidence |
| Cauchy--Cantor | `[1800s | Residue :: REPRESENTABLE -> PRESENT]` | Anchor | 3,000 | convergence and recursion discipline the leftover |
| Spectral lines | `[1800s-1900s | Residue :: OBSERVED -> PRESENT]` | Working | 1,700 | gaps in light become held-open structure |
| Heisenberg tradeoff | `[1920s | Residue :: MEASURABLE refusal]` | Working | 1,800 | measurement refuses simultaneous completion |
| Gosset repeatability | `[1908 | Residue :: REPEATABLE -> NUMERIC]` | Working | 1,600 | small samples require disciplined inference |
| Anomalous magnetic moment | `[1940s onward | Residue :: COMPARABLE]` | Working | 1,600 | tiny residue disciplines theory across decades |
| Two-slit variants | `[1801 / 1909 / 1961 | Residue :: OBSERVED -> PRESENT]` | Working | 1,800 | arrangement makes observation into a held-open residue |
| N-rays | `[1903-1906 | Residue :: failed residue]` | Vignette | 800 | replication refuses a residue claim |
| Pulse oximetry bias | `[modern | Residue :: COMPARABLE refusal]` | Vignette | 700 | ordinary instruments leave population residue |
| Water memory | `[1988 onward | Residue :: REPEATABLE refusal]` | Vignette | 600 | fluctuation fails the residue gate |
| Close | `[Residue -> Staging]` | Close | 1,200 | disciplined residue invites protocol |

Concept budgets for anchor sections:

| Section | Concept split |
| --- | --- |
| Michelson--Le Verrier | Le Verrier/Mercury residue 850; Michelson--Morley apparatus 1,100; null result as full ledger 850; reorganization without replacement 1,200 |
| Planck blackbody residue | apparatus/curve 800; classical refusal 800; quantization as constraint 900; later reinterpretation 900 |
| Brownian--Perrin | Brown's observation 550; Einstein's representation 850; Perrin's measurement 950; molecular consequence 950 |
| Cauchy--Cantor | sequence convergence 750; recursive subdivision 750; ledger equivalence 750; representational shadow 750 |

Refusal: anomaly is not noise merely because the current theory cannot spend
it.

Bridge: once residue can be measured, experiment needs a staging discipline.

## Chapter 3 - Staging

Closed question: how does an awkward experimental state become a value under
scale?

Names: `GUNGAN`, `SOURCE`, `EXECUTED`, `VALUE`, `MAGNITUDE`, `SCALED`.

Chapter job: show experiment as procedure. The universe does not hand over
numbers. Protocols stage conditions, execute operations, and produce values
that become magnitudes only under scale.

Chapter ceiling: **20,000 words**.

Section budget:

| Section | Coordinate | Type | Words | Job |
| --- | --- | --- | ---: | --- |
| Opening | `[Staging]` | Opening | 1,200 | protocol arrives; the universe does not hand over numbers |
| Cavendish--Millikan | `[1798 / 1909-1913 | Staging :: SOURCE -> EXECUTED -> VALUE -> SCALED]` | Anchor | 3,800 | patient apparatus extracts constants from staged procedure |
| Cepheid--Hubble | `[1912-1929 | Staging :: MAGNITUDE -> SCALED]` | Anchor | 3,400 | distance ladder turns periodicity into cosmic scale |
| Cesium clock | `[1955 onward | Staging :: SCALED]` | Anchor | 2,900 | time becomes a reproducible reference |
| Rutherford scattering | `[1909-1911 | Staging :: EXECUTED -> REPRESENTABLE -> VALUE]` | Working | 1,800 | unexpected distribution forces new structure |
| Pendulum chronometry | `[1600s onward | Staging :: SOURCE -> EXECUTED]` | Working | 1,200 | staged repetition makes local gravity usable |
| Mass spectrometry | `[1900s onward | Staging :: VALUE -> MAGNITUDE]` | Working | 1,400 | staged separation becomes mass record |
| Newton--Cooley--Tukey | `[1600s / 1965 | Staging :: SOURCE -> EXECUTED]` | Working | 1,300 | decomposition as staged execution |
| Factory gauge blocks | `[1900s | Staging :: SOURCE -> SCALED]` | Vignette | 700 | ordinary scale discipline grounds precision |
| Survey chain | `[1700s-1800s | Staging :: MAGNITUDE -> SCALED]` | Vignette | 600 | land becomes measurable by protocol |
| Luminous-intensity standards | `[1800s | Staging :: SCALED refusal]` | Vignette | 600 | drifting standards expose bad staging |
| Close | `[Staging -> Overhead]` | Close | 1,100 | carrying scale has cost |

Concept budgets for anchor sections:

| Section | Concept split |
| --- | --- |
| Cavendish--Millikan | Cavendish apparatus 950; Millikan apparatus 950; constant extraction 950; staged-value comparison 950 |
| Cepheid--Hubble | Leavitt plates 800; standard candle logic 800; Hubble redshift/distance 1,000; scaled inference 800 |
| Cesium clock | atomic transition 700; reproducibility protocol 700; second redefinition 800; `SCALED` limit case 700 |

Refusal: a number without protocol is numerology.

Bridge: once scale appears, the cost of carrying scale appears too.

## Chapter 4 - Overhead

Closed question: what gathers around experiment that is not evidence, but still
changes what people believe?

Names: `LOAD`, `FINITE_ELEPHANT`, `BULLSHIT`, `PROPAGANDA`, `ACOLYTE`.

Chapter job: make the social and institutional cost of experiment visible
without becoming cynical. Experiment needs institutions, funding, standards,
publication, replication, and training. It also attracts theater, career
pressure, slogans, fraud, wishful thinking, and inherited claims.

Chapter ceiling: **28,000 words**. Draft after Chapters 1-3 have established
Entry, Residue, and Staging.

Section budget:

| Section | Coordinate | Type | Words | Job |
| --- | --- | --- | ---: | --- |
| Opening | `[Overhead]` | Opening | 2,000 | overhead is not corruption; it is the cost of carrying scale |
| N-rays | `[1903-1906 | Overhead :: BULLSHIT -> PROPAGANDA]` | Anchor | 4,000 | expectation and status masquerade as signal |
| Cold fusion | `[1989 onward | Overhead :: REPEATABLE refusal -> PROPAGANDA]` | Anchor | 4,000 | press-release science meets replication |
| Lysenko--Lavoisier | `[1700s / 1900s | Overhead :: PROPAGANDA -> ACOLYTE]` | Anchor | 4,200 | institutional conditions decide whether propaganda is refused |
| LHC trigger | `[1900s-2000s | Overhead :: FINITE_ELEPHANT]` | Anchor | 3,300 | finite selection makes overwhelming event streams usable |
| Big observatories | `[1900s-2000s | Overhead :: LOAD]` | Working | 2,000 | large apparatus carries architectural and funding load |
| Citation cascade | `[modern | Overhead :: ACOLYTE]` | Working | 1,800 | claims travel through people who did not measure them |
| Replication crisis | `[modern | Overhead :: REPEATABLE refusal]` | Working | 1,800 | population-scale repeatability failure |
| Clinical-trial registries | `[modern | Overhead :: LOAD -> LOGICAL seed]` | Working | 1,400 | ordinary discipline resists selective record-making |
| Polywater | `[1960s | Overhead :: BULLSHIT refusal]` | Vignette | 700 | chemistry refuses an inflated claim |
| Piltdown Man | `[1912-1953 | Overhead :: PROPAGANDA]` | Vignette | 700 | institutional desire carries a false record |
| Shewhart charts | `[1920s | Overhead :: LOAD discipline]` | Vignette | 600 | ordinary control resists noise and theater |
| Close | `[Overhead -> Truth Transport]` | Close | 1,500 | after cost is named, truth must travel |

Concept budgets for anchor sections:

| Section | Concept split |
| --- | --- |
| N-rays | Blondlot scene 900; apparatus and expectation 900; Wood refusal 1,000; `BULLSHIT -> PROPAGANDA` consequence 1,200 |
| Cold fusion | announcement 800; experimental claim 900; replication refusal 1,000; public/institutional afterlife 1,300 |
| Lysenko--Lavoisier | Lavoisier's experimental refusal of phlogiston 900; Lavoisier's death and what it does not refute 900; Vavilov's experimental discipline at the seed bank 900; Lysenko's institutional success and what it does refute 900; paired consequence on `PROPAGANDA` and `ACOLYTE` 600 |
| LHC trigger | event rate 800; trigger hierarchy 1,000; finite selection 900; publishable record 600 |

Refusal: social force is not evidence, even when it wears a lab coat.

Volume 6 Chapter 4 should explicitly cross-reference Volume 5's `BULLSHIT`,
`PROPAGANDA`, and `ACOLYTE` sections. Volume 5 shows the accumulating cost in
the margin. Volume 6 shows historical cases where that cost breaks the record.

Bridge: after overhead has been named, truth must be transported carefully.

## Chapter 5 - Truth Transport

Closed question: how can an experimental truth travel without losing witness,
contact, and place?

Names: `SCIENTIFIC`, `TRUTH`, `WITNESSED`, `REAL`, `LOCAL`, `UNIVERSAL`.

Chapter job: show that scientific truth travels through disciplined witness.
It does not become universal by ignoring locality. It becomes universal by
carrying local conditions well enough that other places can test, translate,
and compare.

Chapter ceiling: **26,000 words**.

Section budget:

| Section | Coordinate | Type | Words | Job |
| --- | --- | --- | ---: | --- |
| Opening | `[Truth Transport]` | Opening | 1,500 | truth travels only by keeping witness and place |
| Pasteur--Tyndall | `[1860s-1870s | Truth transport :: SCIENTIFIC -> WITNESSED]` | Anchor | 3,800 | spontaneous generation refused through public setup |
| Eddington--Weiss | `[1919 / 2015 onward | Truth transport :: WITNESSED -> LOCAL -> UNIVERSAL]` | Anchor | 4,200 | local instruments carry universal gravitational claims |
| Penzias--Wilson CMB | `[1965 | Truth transport :: REAL -> UNIVERSAL]` | Anchor | 3,600 | a local instrument meets universe-scale residue |
| Bell--Aspect | `[1960s-1980s onward | Truth transport :: LOCAL -> UNIVERSAL]` | Anchor | 3,300 | local measurements constrain universal theories |
| Einstein synchronization | `[1905 onward | Truth transport :: LOCAL -> UNIVERSAL]` | Working | 2,000 | synchronization as transport convention |
| GPS relativistic correction | `[late 1900s onward | Truth transport :: LOCAL -> UNIVERSAL -> SCALED]` | Working | 1,800 | clocks travel by carrying frame differences |
| Trinity test | `[1945 | Truth transport :: WITNESSED -> REAL]` | Working | 1,600 | witnessed truth travels because records constrain it |
| Kant/time ordering | `[1700s | Truth transport :: LOCAL seed]` | Working | 1,400 | time as ordered transport, not placeless background |
| Meteorological field station | `[modern | Truth transport :: WITNESSED]` | Vignette | 600 | ordinary transport across distance |
| Court testimony | `[ordinary | Truth transport :: WITNESSED]` | Vignette | 500 | witness under rule as non-scientific parallel |
| Failed lab transport | `[TBD | Truth transport :: REPEATABLE refusal]` | Vignette | 600 | a result that does not travel across labs |
| Close | `[Truth Transport -> Decision]` | Close | 1,100 | transported truth still needs conclusion |

Concept budgets for anchor sections:

| Section | Concept split |
| --- | --- |
| Pasteur--Tyndall | Pasteur swan-neck 900; Tyndall mountain air 900; spontaneous generation refused 900; `SCIENTIFIC + WITNESSED` consequence 1,100 |
| Eddington--Weiss | 1919 eclipse locality 1,000; plate/witness controversy 900; Weiss detector architecture/locality 1,100; universal gravitational consequence 1,200 |
| Penzias--Wilson CMB | antenna/noise scene 850; signal identification 850; cosmological residue 950; universal transport 950 |
| Bell--Aspect | Bell inequality 850; experimental arrangement 950; locality refusal 750; universal consequence 750 |

Refusal: universal does not mean placeless.

Bridge: transported truth still has to become a conclusion.

## Chapter 6 - Decision

Closed question: what conclusion may the experimental record license?

Names: `LOGICAL`, `HALTED`, `MEASURED`, `COMPILED`, `INFERRED`.

Chapter job: end where Volume 5 ends, but with historical experiment carrying
the pressure. The universe is not owned by science. It is inferred under
records that can be challenged, repeated, extended, and revised.

Chapter ceiling: **21,000 words**.

Section budget:

| Section | Coordinate | Type | Words | Job |
| --- | --- | --- | ---: | --- |
| Opening | `[Decision]` | Opening | 1,300 | ask what conclusion the record may license |
| Double-blind trial | `[1900s onward | Decision :: LOGICAL -> MEASURED]` | Anchor | 3,600 | protocol protects inference from desire |
| Standard Model compilation | `[1900s onward | Decision :: COMPILED -> INFERRED]` | Anchor | 3,800 | scattered experiments become one working structure |
| Cosmological Inference | `[1900s onward | Decision :: INFERRED]` | Anchor | 4,000 | expansion, light elements, and background radiation license a universe story |
| Particle discovery threshold | `[1900s onward | Decision :: LOGICAL -> HALTED]` | Working | 1,900 | a community names when evidence has accumulated |
| Climate compilation | `[1800s onward | Decision :: COMPILED -> INFERRED]` | Working | 1,900 | many local measurements compile into public inference |
| Noether--Galois | `[1800s-1900s | Decision :: LOGICAL seed]` | Working | 1,200 | symmetry closes as disciplined inference |
| Jury verdict | `[ordinary | Decision :: INFERRED]` | Vignette | 600 | inference under instructions |
| Bridge safety inference | `[ordinary | Decision :: MEASURED -> INFERRED]` | Vignette | 500 | engineering inference under record |
| Treatment decision | `[ordinary | Decision :: LOGICAL -> INFERRED]` | Vignette | 600 | action under uncertainty |
| Close | `[Decision]` | Close | 1,600 | the universe as publicly inferable, not owned |

Concept budgets for anchor sections:

| Section | Concept split |
| --- | --- |
| Standard Model compilation | scattering/accelerators 850; electroweak/QCD records 950; compilation into model 1,100; limits/future work 900 |
| Cosmological Inference | expansion record 800; light-element record 800; CMB record 900; inference-not-ownership landing 1,500 |
| Double-blind trial | desire/refusal problem 700; blinding protocol 900; measurement endpoint 900; inference licensed for action 1,100 |

Refusal: inference is not possession of final Truth.

Closing motion: the universe in this book is not the object in itself. It is
the universe as experimental history has made it publicly inferable.

## Length Budget

The active budget is the <=600-page envelope above, not the old compact
companion target. The book should fill only as much of the envelope as the
episodes earn.

Front matter ceiling: **8,000 words**.

| Section | Words | Job |
| --- | ---: | --- |
| Preface | 1,500 | why this experimental history belongs beside the other volumes |
| Reader's introduction | 2,000 | how to read out of order; explain two-coordinate headers |
| Why this is a gauge | 1,200 | adapt the Volume 5 gauge framing |
| The procession at a glance | 1,300 | map the 37 names to six movements |
| Note on sources | 1,000 | citation discipline and source hierarchy |
| Note on satirical names | 1,000 | why `FINITE_ELEPHANT`, `BULLSHIT`, `PROPAGANDA`, and `ACOLYTE` are literal here |

Back matter ceiling: **5,000 words**.

| Section | Words | Job |
| --- | ---: | --- |
| Name Registry projection | 1,800 | map the 37 names to Volume 6 episodes |
| Bibliography notes | 2,200 | evidence base; may be generated from BibTeX later |
| Episode index | 500 | named effects and paired figures |
| Apparatus index | 500 | instruments, protocols, and records |

Episode internal budget:

| Component | Anchor | Working | Vignette |
| --- | ---: | ---: | ---: |
| Historical scene | 600-900 | 300-500 | 100-200 |
| `phenom` kernel | 300-500 | 250-400 | 150-250 |
| Apparatus/source detail | 900-1,400 | 500-900 | 150-250 |
| Refusal/reception/consequence | 700-1,000 | 300-500 | 100-200 |
| Handoff | 200-400 | 100-200 | 50-100 |
| Total | 3,000-4,200 | 1,400-2,400 | 500-900 |

If a candidate cannot fill even a vignette shape, it is not yet a named effect.
If a candidate needs more than the anchor ceiling, split it into two named
effects or move part of the story into a neighboring section.

## Source Policy

Historical drafting requires sources.

No episode enters a chapter without a `\PhOrigin` block carrying at least one
primary or canonical-secondary citation. Chapter drafting should verify:

- dates and locations;
- apparatus details;
- what was actually measured;
- what the experimenters claimed at the time;
- what later replication or reinterpretation changed;
- which details are legend rather than record.

The book should prefer primary experiment reports when readable and reliable
secondary histories when primary sources would bury the reader. No invented
quotes. No polished anecdote unless the source supports it.

## Structural Risks

1. **Whig history.** The book must not make every experiment look as if it was
   marching toward the current theory. The obligation came first; the later
   theory often arrived confused, late, or by accident.
2. **Hero history.** The book must not reduce experiment to lone genius scenes.
   Instruments, assistants, institutions, standards, and replication matter.
3. **Chronology creep.** If a chapter starts to become "and then this
   happened," cut back to the named obligation.
4. **Anecdote drift.** A beautiful historical story that does not perform a
   named obligation belongs elsewhere.
5. **Overclaiming.** Do not say an experiment proved more than its record could
   carry at the time.
6. **Table survival.** Planning tables may remain in `volume_6.md`, but they
   should not survive into prose. Drafted chapters use `phenom` kernels, not
   summary rows.

## Drafting Method

Draft one chapter at a time, but draft each chapter by experimental episode.

For each episode:

```text
Two-coordinate header.
Historical scene.
Apparatus detail.
phenom kernel.
Refusal.
Handoff.
```

After all episodes in a chapter are drafted, write the chapter opening last.
The opening should not promise a neat story. It should name the obligation the
chapter actually performed.

## Drafting Order

Implementation order follows the Krylov constraint in `three_gauges.md`.
The book is out-of-order historically, but drafting is not out of order.
Each movement depends on the basis vectors established by the prior movement.

1. Draft Chapter 1 - Entry first. Establish what can become a public mark.
2. Draft Chapter 2 - Residue second. Let structured leftover appear only after
   marks can be carried.
3. Draft Chapter 3 - Staging third. Turn residue into protocol, value, and
   scale.
4. Draft Chapter 4 - Overhead fourth. Test the `phenom` form on N-rays, cold
   fusion, Lysenko--Lavoisier, and LHC trigger only after cost is cost *of*
   an established experimental record.
5. Draft Chapter 5 - Truth Transport fifth. Let witness, locality, and
   universality travel only after overhead has been named.
6. Draft Chapter 6 - Decision last. Land the inferred-not-owned move after
   the full experimental procession has accumulated.

## Current Verdict

Volume 6 is justified as **The Necessary Experiments: An Out-of-Order History
of Scientific Experiment**.

Its role is not to add another technical register. Its role is to let the
history of experiment perform the same spine the other volumes name, prove,
measure, compile, trace, and make public.

The plan is publishable only if the `phenom` form is adopted as the episode
kernel. Without that adoption, the volume becomes a popular history of science
with named-obligation chapter titles. With that adoption, it becomes a
continuation of the instrument book's work, presented in procession order, for
an audience the technical books cannot reach.
