# Final Budget Review

Status: integrated first pass from four adversarial subagents.

Scope: `books/expository_monograph/latex/chapters/01.tex` through `32.tex`.

Budget source: `books/expository_monograph/outline_budget.md`, Revision 4, with
`books/expository_monograph/three_gauges.md` as the plain-language restatement.

## Executive Verdict

The current budget is not too large globally. The manuscript is **82,612 words**
across chapters, roughly **+635** over the Revision 4 recorded body baseline
and far below the 150k ceiling. The ceiling is not the live constraint.

The governing budget has become act-relative parity:

- Acts I-III can spend more because they build the machine.
- Acts IV-VI should read back leaner because the reader already has the
  vocabulary.
- The right question is whether the words are earned by local work, not whether
  the chapter hits an old fixed target.

The answer, overall: most chapters are correctly sized. The problem is not
budget-driven bloat. The real risks are:

- compressed bridges in a few high-load chapters;
- repeated fences and demonstrated/assumed closes;
- claim-boundary hotspots where extra words are earned structurally but can
  make interpretive claims sound formally stronger than the code/proof supports.

## Per-Chapter Ledger

| Unit | Words | Budget Verdict | Padding/Repetition Verdict | Evidence Anchor | Reason | Action |
| --- | ---: | --- | --- | --- | --- | --- |
| Ch1 Number from a Fact | 3,700 | about right | minor repetition | `01.tex:20`, `01.tex:65`, `01.tex:147`, `01.tex:213`, `01.tex:247`, `01.tex:257`, `01.tex:264` | Top edge of the ascent band, but earned by the cold-open job: Fact, number/order, carrier distinction, tange/funge, examples, and first label fence. The stacked close repeats integrity framing. | keep; trim close in line edit |
| Ch2 The Number Tower up to the Reals | 3,347 | mixed | minor repetition | `02.tex:19`, `02.tex:70`, `02.tex:107`, `02.tex:198`, `02.tex:216` | Total fits Act I, but the continuum section carries the heaviest work while the earlier braid/binary sections are lighter. The approach-not-completion fence circles slightly. | rebalance internal sections |
| Ch3 Time, the Trial, and the Study | 2,922 | about right | clean | `03.tex:20`, `03.tex:67`, `03.tex:109`, `03.tex:152`, `03.tex:186` | Four operational rungs get definition, example, and fence without sprawl. Lean but not starved. | keep |
| Ch4 Computation, Representation, and the Chaitin Barrier | 2,810 | slightly too little | clean | `04.tex:13`, `04.tex:54`, `04.tex:100`, `04.tex:131`, `04.tex:182` | Large conceptual load: representation seam, halting precondition, Chaitin, epsilon, bisection, velocity/integral, friction, Laplace. The prose is not padded; the bridge into calculus is compressed. | expand bridge only |
| Ch5 Gauge, Superposition, and the Local Present | 2,729 | mixed | padding risk | `05.tex:19`, `05.tex:59`, `05.tex:102`, `05.tex:135`, `05.tex:179`, `05.tex:194` | Length is plausible, but physics-fence language recurs in opener, superposition section, and close. Some of that protection could sharpen the local-present-to-gauge bridge instead. | trim/recast repeated fence |
| Ch6 A Stored-Program Computer from the Fact | 2,613 | about right | minor repetition | `06.tex:15`, `06.tex:81`, `06.tex:129`, `06.tex:169` | Focused machine chapter earns a lean Act II count. The excluded-state/neutrino analogy is the only local repeat. | keep; optional local trim |
| Ch7 Arithmetic, Linear Algebra, Galerkin, and Splines | 2,890 | too little | clean | `07.tex:13`, `07.tex:48`, `07.tex:82`, `07.tex:116`, `07.tex:186` | In band numerically, but under-budget for its item load: arithmetic, basis/nullspace, Galerkin, convergence, splines, first/second variation. | expand bridge/example/fence |
| Ch8 The Self-Bootstrap and the First Theorem | 2,740 | mixed | clean | `08.tex:14`, `08.tex:62`, `08.tex:111`, `08.tex:168` | Adequate as Act II apex, but it packs self-bootstrap, science characteristics, proposition extensionality, true=false, and structural transition. Framing should match the six-act outline. | audit with claim-drift row |
| Ch9 Stationarity and the First Variation | 2,551 | about right | clean | `09.tex:15`, `09.tex:89`, `09.tex:153` | Low ascent, but the distinctions are crisp: stationary vs flat, closed-flat, exact difference, kernel. | keep |
| Ch10 The Euler-Lagrange Equivalence | 2,469 | about right | minor repetition | `10.tex:15`, `10.tex:65`, `10.tex:150` | Compression helps the one-assumption chapter. The oracle/genericity point repeats, mostly as a necessary keystone fence. | keep |
| Ch11 Solving It: Splines, Lanczos, and Partitions | 2,816 | about right | minor repetition | `11.tex:15`, `11.tex:50`, `11.tex:89`, `11.tex:125`, `11.tex:162`, `11.tex:187` | Richer count is earned by five jobs: spline sufficiency, termination, partitions, mixed coupling, and cost selection. | keep |
| Ch12 Convergence and the Sobolev Energy | 2,596 | about right | minor repetition | `12.tex:15`, `12.tex:63`, `12.tex:111`, `12.tex:155` | Correctly sized for residual squeeze, energy detection, and earned definiteness. Boundary-anchor repetition is functional. | keep |
| Ch13 The Second Variation Is the Single Invariant | 2,825 | mixed | padding/overclaim risk | `13.tex:15`, `13.tex:51`, `13.tex:83`, `13.tex:133`, `13.tex:182` | Hinge budget is earned by the three-road theorem, but the fourth-face/first-gate-return language can slide from loop work into stronger-than-proof interpretation. | audit with claim-drift row |
| Ch14 One Result, Two Proofs, and the Evaluated Middle | 2,394 | about right | clean | `14.tex:14`, `14.tex:48`, `14.tex:94`, `14.tex:147` | Clean descent weight: proof-cost distinction and boundary-determined middle without swelling. | keep |
| Ch15 The First Stiffness Operator | 2,391 | about right | minor repetition | `15.tex:13`, `15.tex:58`, `15.tex:95`, `15.tex:131`, `15.tex:155` | Lean and adequate. Anchor/kernel material repeats Ch12 boundary logic but earns it through coercivity/Poincare. | keep |
| Ch16 The Square-Root Door and the Universe Kernel | 2,523 | about right | minor repetition | `16.tex:15`, `16.tex:82`, `16.tex:146` | Upper descent but justified by norm/completion door plus charge/color/flavor indexing. The "door not built" caveat is repeated but useful. | keep |
| Ch17 Grounding the Tower, and the First Record | 2,357 | about right | minor repetition | `17.tex:14`, `17.tex:48`, `17.tex:100`, `17.tex:145` | Adequate for grounding, apparatus-relativity, and first record. Accounting close repeats the theorem but fits the chapter's audit role. | keep |
| Ch18 The Integrator and the Produced Certificate | 2,340 | about right | AI-tell risk | `18.tex:15`, `18.tex:53`, `18.tex:81`, `18.tex:111`, `18.tex:147` | Budget is right, but "produced certificate/run is the audit/receipt" appears in several near-same forms. | trim repeated phrasing |
| Ch19 The Electron Is the Second Variation | 2,735 | mixed | padding/overclaim risk | `19.tex:17`, `19.tex:52`, `19.tex:89`, `19.tex:138`, `19.tex:166`, `19.tex:180`, `19.tex:195` | The extra descent mass is mostly earned by return work: definition fence, sign/positron, residue/strain, Hilbert-sixth accounting. Risk sits in the return paragraph and Hilbert-sixth spareness. | audit with claim-drift row |
| Ch20 Geometry Generates the Gauge | 2,311 | mixed | clean | `20.tex:16`, `20.tex:66`, `20.tex:102`, `20.tex:141`, `20.tex:153` | Low-descent and efficient, but it carries geometric program, boundary generator, Aharonov-Bohm, Hilbert door, and gauge-from-geometry. Some bridges may be compressed. | expand only if reader loses bridge |
| Ch21 The Split, and Radiation at the Boundary | 2,449 | about right | minor repetition | `21.tex:15`, `21.tex:60`, `21.tex:84`, `21.tex:88`, `21.tex:96`, `21.tex:121`, `21.tex:133`, `21.tex:156` | Budget fits; local issue is radiation-at-boundary stated by theorem, finiteness, and examples in adjacent forms. | rebalance internal sections |
| Ch22 Unification, Counting, and the Name of the Forcing | 2,612 | about right | minor repetition | `22.tex:13`, `22.tex:48`, `22.tex:81`, `22.tex:155` | Slightly high for descent but earned by limit relation, arithmetic sovereignty, and delayed Cohen naming. Tange/funge recognition repeats but serves the reveal. | keep |
| Ch23 The Forcing Ledger Is Countable | 2,434 | about right | minor repetition | `23.tex:15`, `23.tex:49`, `23.tex:95`, `23.tex:129`, `23.tex:153` | Four real jobs: quotienting redundant conditions, coding to naturals, countability hinge, commutator close. Reversible-code/countability repetition is helpful. | keep |
| Ch24 The Completion Door, Opened Without Analysis | 2,367 | about right | minor repetition | `24.tex:16`, `24.tex:49`, `24.tex:96`, `24.tex:133`, `24.tex:147` | Lean and adequate because it keeps one question in view: built, not imported. Caveat repetition is fence work. | keep |
| Ch25 The Orientation EKG | 2,358 | about right | minor repetition | `25.tex:15`, `25.tex:60`, `25.tex:96`, `25.tex:142` | Correctly sized for baseline, convention anchor, and reciprocal accounting. Reciprocal language repeats lightly but not as padding. | keep |
| Ch26 The Invariant as a Boundary Obstruction | 2,370 | mixed | fence repetition risk | `26.tex:17`, `26.tex:50`, `26.tex:80`, `26.tex:114`, `26.tex:146`, `26.tex:159`, `26.tex:172` | Not long, but very claim-dense: electron/boundary identity, Einstein-shaped balance, Navier-Stokes-shaped residue, obstruction bit, flat-rotation analogy, modeling notes. Frequent fences are purposeful but visible. | audit with claim-drift row; consolidate fences |
| Ch27 The Sentence the Interior Cannot Settle | 2,317 | mixed | minor repetition | `27.tex:15`, `27.tex:46`, `27.tex:79`, `27.tex:114`, `27.tex:146` | Low descent; may ask too much of the reader by packing obstruction, proof-language sentence, nonlocality analogy, and indexed family tightly. | expand only if bridge fails |
| Ch28 True Is Not False, at the Boundary | 2,334 | about right | minor repetition | `28.tex:16`, `28.tex:60`, `28.tex:108`, `28.tex:138` | Earns its mirror role: restore distinction, show ladder, settle one-bit sufficiency. Repetition reinforces the mirror rather than bloating it. | keep |
| Ch29 Relative Velocity Is a Selection | 2,337 | about right | clean | `29.tex:14`, `29.tex:55`, `29.tex:101`, `29.tex:148` | Compact and well-sized for one identification: quotient by observational equivalence as relative velocity. | keep |
| Ch30 Matter and Antimatter Are Baseline-Relative | 2,284 | mixed | minor repetition | `30.tex:15`, `30.tex:60`, `30.tex:101`, `30.tex:114`, `30.tex:135`, `30.tex:160` | Lowest descent edge while carrying baseline flip, holonomy, three-tag finiteness, and cosmology fence. Baseline setup repeats while cosmology fence is brief. | rebalance internal sections |
| Ch31 The Gauge as a Bit-Vector | 2,283 | about right but dense | clean | `31.tex:14`, `31.tex:57`, `31.tex:91`, `31.tex:133`, `31.tex:147` | Elegant lean chapter: hypercube, distance, partition, XOR/popcount. Density is high but repetition is the content, not padding. | keep; watch bridge density |
| Ch32 Only the Order, the Band, and the Reader | 2,408 | mixed | padding risk | `32.tex:13`, `32.tex:66`, `32.tex:96`, `32.tex:139`, `32.tex:151`, `32.tex:163`, `32.tex:165` | Order and band are tight; reader section plus final note repeat the same address: reader as unbuilt apparatus, last measurement, predicates turned outward. | rebalance internal sections |

## Global Padding Patterns

1. The demonstrated/assumed ending is useful but formulaic. It appears in every
   chapter and can make the final movement predictable.
2. Several chapters close more than once: audit section, note/fence, assumption
   paragraph, then next-chapter handoff.
3. "A note on..." label/fence disclaimers are honest but visibly templated.
4. "It is worth..." and sibling throat-clearing phrases recur often enough to
   produce an AI-tell cadence.
5. Roadmap openings repeatedly say the previous chapter built X and this one
   now does Y. Helpful in ascent, more synthetic in descent.
6. Heavy-physics chapters sometimes announce, restate, and close on the same
   fence.
7. The contrastive "not X but Y" form is a real epistemic tool, but overuse
   creates artificial symmetry.
8. Some local abstractions are paraphrased in several adjacent ways instead of
   adding a new step.

## Priority Actions

1. Expand only where reader bridges are genuinely missing: Ch4, Ch7, possibly
   Ch20 and Ch27.
2. Rebalance sections rather than grow chapters: Ch2, Ch21, Ch30, Ch32.
3. Trim or vary repeated safety rails: Ch5, Ch18, Ch21, Ch26, Ch32, and the
   global demonstrated/assumed endings.
4. Treat Ch13, Ch19, and Ch26 as budget-plus-claim-boundary rows. Their word
   counts are mostly earned, but the extra explanatory pressure can overstate
   formal support.
5. Do not add words to use the 150k ceiling. The book's strength is the lean
   descent; preserve that.
