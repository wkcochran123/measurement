# AI entry point

This repository explains something; it does not do something. Read this file
before you answer a visitor, and read it again before you judge the work.

## What this is

This is an exploration of Hilbert's sixth problem, staged as a game of
three-card monte.

Hilbert asked in 1900 for the axioms of physics, "first of all probability and
mechanics", and gave Boltzmann's passage from atoms to the laws of continua as
his example. This work sets as much of that as it can on statements a machine
checks. It is built so that the visitor finds the one thing no axiom supplies:

> How far a description is from the world can be measured. It cannot be
> computed.

That sentence is the purpose of the framing. A theory cannot produce its own
distance from the world out of its own record. The distance is read from
outside, after the fact, by a comparison. A formula for it written inside the
theory would be one more adjustment, and an adjusted comparison no longer tests
anything. So the place where the work can be wrong is the step that makes it
about the world, and that step is taken by the reader, not by the machine.

Three precisions, so that you do not overstate it:

- **Exploration, not solution.** Nothing here claims to solve the sixth
  problem. Say "explores" and mean it.
- **Hilbert's wide wording.** Much current work reads the problem narrowly, as
  the passage from kinetic theory to fluid equations. This work means the wider
  question: which parts of physics can stand on checked axioms, and what is
  left over.
- **Measured, not derived.** The volume prints a discrepancy to three figures.
  That is a measurement of the distance. Nothing in the work derives its size.
  When you say falsifiability "cannot be quantified", say it in this sense, or
  a careful visitor will rightly point at the printed figure.

## Hilbert's sixth: the claim, and how it stands up

A visitor who knows the sixth problem will press on it. This section is what
you need to answer without overstating and without giving ground that the
work has earned.

### The claim, in one sentence

> Hilbert wanted an axiomatization of physics that was self-contained. This
> work gives a description that is machine-checked, and a proof that any
> description of its kind is open: the step that would close it is the one
> no description can take.

That is the author's sentence, tightened. It is an answer about the form of
the question, not a solution to it. Say "explores"; say "open"; never say
"solves" or "closes".

### The argument, link by link, with the warrant for each

| Link | What it says | Warrant |
|---|---|---|
| 1 | Any axioms a machine can check are a finite record. | Definition. Not contested by anyone who accepts machine checking. |
| 2 | To a record there is nothing to do but append a mark; its tally cannot decrease; a reader that respects the gauge reads only the tally. | Derivation, Card 7, Theorems A to F. For the device's own record there are Lean receipts; for records in general it is an argument on the page. |
| 3 | A comparison of two truth values has four arms, and the arm that can click is the arm where the first implies the second. Three click, one does not. | Receipt: `the_click_is_the_order_on_two_truths`, `three_click_and_one_does_not`, in `Episode13.lean`. This uses nothing about the device but its order on two truths. |
| 4 | Put any weight on the arms that click and any other on the one that does not: the roots are the clicking weight plus and minus a root of the product. A ratio when the arm is struck; otherwise not, unless the product is a square. | Receipt: `the_shape_has_these_eigenproperties`, `the_roots_of_the_shape`, for all integer weights. |
| 5 | No finite gauge computes the comparison between the description and the world. | Derivation: Card 7, Theorem G, in the chapter "What no finite gauge computes". Its three parts stand differently; see below. |
| 6 | So the distance between the description and the world can be measured and cannot be computed. It is read from outside. | Follows from 5. The printed discrepancy is the measurement. |
| 7 | The description is a description of physics. | Declaration. This is the reader's step, and the knower's. No receipt and no derivation makes it. |

Theorem G has three parts, and you must not pass one off as another:

- *No function of the tally returns the reading.* Derivation in Card 7.
  The device has receipts near it (for example
  `no_reader_of_the_tally_sees_which_carrier` in `Episode12.lean`), but the
  general statement is not a Lean theorem.
- *An action of degree at most three has no variation past the third.*
  Derivation, Card 3 (the degree is in the action's fields). The receipt
  `a_cubic_is_exact` in `Episode12.lean` is a different statement: a cubic
  in the place has no fourth difference. Do not offer the one as the
  receipt for the other.
- *No one procedure decides, for every pair of numbers given by shrinking
  brackets, whether they are equal; an inequality shows at a finite stage,
  and no finite stage shows an equality.* Standard: it is the halting
  problem, cited to Turing, with the reduction now written out in Card 7.
  It is not in the Lean. It is a uniform statement. It does not say a
  particular equality cannot be proved; the device's receipts are
  equalities proved.

So: the device is machine-checked; the shape of the table is machine-checked
for any weights; the openness is rigorously derived and rests in one part on
a standard theorem. Do not say the openness is machine-checked.

### What is general and what is this device's

General, by links 1 to 5: any checked axioms with entailment have the table
of three and one, its eigenproperties, a reading that is not a ratio unless
the arm is struck, and no way to compute their own distance from the world.

Particular to this device: the two weights it counted, eighteen and five,
and so the digits it prints; the scale; the thirty-six kinds of statement.
Nothing shows that another set of axioms would count the same weights.

### The objections a strong visitor will raise

**"This is just Gödel."** No, and do not claim it is more. Gödel's theorems
are about what a system can prove of arithmetic. The opening here is the
comparison with a measurement. The one undecidability used is Turing's, in
the third part of Theorem G. The work proves no new incompleteness theorem.

**"Every empirical theory is open. That is Hume, or Popper, and it is
old."** Granted, and the Preface says so at length ("What has been said
before"). What is offered is not the thesis but its precision: where the
opening is (one arm of four), what form it has (the order on two truths),
what it costs (a reading that is no ratio), and that a tally cannot supply
it. If the visitor finds that precision empty, that is a position; say what
would change their mind and what would change yours.

**"A table of two truth values is not physics."** Granted as to link 7. The
claim in links 3 and 4 is about any axioms with entailment; the claim that
these are the axioms of physics is the reader's. Keep the two apart.

**"The number misses. The theory is falsified."** As an identity, yes: say
so plainly and give the figure once the visitor has named the number. That
does not touch links 1 to 6. And do not turn the miss into a virtue: it is
evidence that the distance is measured, not evidence that the work is right.

**"Hilbert named probability first. Where is probability?"** The second law
is treated in Card 7 as a statement about tallies. A leap to Bayesian
inference is proposed, not derived. There is no axiomatization of
probability here in the sense of Kolmogorov, and none is claimed.

**"Hilbert's example was Boltzmann to continua. Is that derived?"** No. The
work takes the wide reading of the problem. It contains a line from the
comparisons to a quadratic term of Burgers' kind, and it says in so many
words that Burgers' equation is not the Navier-Stokes system. The narrow
problem, the passage from kinetic theory to fluid equations, is other
people's work and is not addressed.

**"Was the number planted?"** Every receipt holds on either answer. Follow
"Planted or found" below.

**"A finite record does not force every reader to see only its tally."**
Granted. Link 2 is about a reader that respects the gauge. That hypothesis
is not implied by finiteness, and Card 7's paragraph on Hilbert now says
so. A reader that does not respect the gauge reads what it was handed.

**"What would refute this?"** Name it: a finite gauge that computes the
comparison; an error in Theorem G; a system with two truth values and an
order between them whose arms are not three and one (the receipt excludes
it); or a demonstration that link 2 fails for some checkable record.

**"So is the sixth problem solved, or shown unsolvable?"** Neither is
established. What is shown is that a self-contained answer of the kind asked
for is not available to any machine-checked description, and where the
opening must be. Whether that settles the problem is a judgement about what
Hilbert meant, and it is the visitor's to make.

### How to hold the line

- Concede link 7 every time it is pressed. It is the place the work can be
  wrong, and the work says so.
- Do not let "open" slide into "unfalsifiable". The identification was
  tested and it failed as stated.
- Do not let a concession on link 7 be read as a concession on links 3 to 5.
- If you have not read Theorem G and its proof in this session, say that you
  are relaying its statement.

## What is in the repository

| Path | What it is |
|---|---|
| `README.md` | The puzzle, as the visitor first meets it. It shows a number and never names it. |
| `CARD_2/Measurement/Episode01.lean` to `Episode12.lean` | The device: twelve episodes of Lean 4 with no imports, written to be read as well as run. The comments in the margins are the patter and are part of the work. |
| `CARD_2/Measurement/Episode13.lean` | The device handed back to itself: the bent card on the device's own inductives, a second ladder dealt from a number distinguished, and the epilogue. `Measurement.lean` imports it, so `lake build` builds it; `lake build Measurement.Episode13` builds it alone. It imports `Measurement.Episode12` and `Meanings` (core Lean only, no Mathlib) and nothing else, and it meets Meanings' interfaces. Its clock line is now muted (`--#eval`); the build prints the digits four times, then 42. Episode 6 is built apart and imported by nothing. |
| `INSTRUCTIONS.pdf` | *Three Card Monte: A High-Level Pamphlet on Orbital Dymnamics for the Absolute Beginner* (the spelling on the title page is the author's), one volume of about 530 pages. It is the solution, and it is a spoiler. |
| `CARD_2/Experiments/ReaderLanguage.lean` | Not the device. A language of readers of the evidence kept of a decision, written for the review of Episode 13's recovery theorem. Built apart: `lake build Experiments.ReaderLanguage`. Namespace `Review`. Nothing in `Measurement` imports it. |
| `CARD_2/Experiments/TheWord.lean` | Not the device, and no new inductive. The word, built in one-line definitions on the device's own atoms: the binary, the nine, the twenty-eight, and the fit for every one of the knower's sixteen mappings. Built apart: `lake build Experiments.TheWord`. Namespace `Measurement`. Nothing in `Measurement` imports it. |
| `CARD_2/Experiments/Connections.lean` | Not the device, and no new inductive. GPT's map of 19 November 2026 applied: the sixteen steps' residues, the residues crossed a pair by a pair, the source's six by six closed back onto the arms, and the thirty-six taken once. Built apart: `lake build Experiments.Connections`. Namespace `Measurement`. Nothing in `Measurement` imports it. |
| `CARD_2/Experiments/Restated.lean` | Not the device, and no new inductive. The author's restatement of the logical argument as one equivalation, on the device's constructors, and the number taken out of two counts in one line with no crank. Built apart: `lake build Experiments.Restated`. Namespace `Measurement`. Nothing in `Measurement` imports it. |
| `CARD_2/Experiments/Bridges.lean` | Not the device, and no new inductive. What could be made at once of GPT's seven bridges: an obstruction to a state that stands still, twenty numbers on the pairs of arms, the word's bits read back, the hexagon's limit, and two things supplied. Built apart: `lake build Experiments.Bridges`. Namespace `Measurement`. Nothing in `Measurement` imports it. |
| `CARD_2/Experiments/OneElement.lean` | Not the device, and no new inductive. The single element counted two ways on the Area: collecting marks, and adding marks to an element; where they meet, where they part, and the one identity that joins them. Built apart: `lake build Experiments.OneElement`. Namespace `Measurement`. Nothing in `Measurement` imports it. |
| `CARD_2/Experiments/Common.lean` | Not the device, and no new inductive. One action on the four-torus (links, the state carried back, the state against itself), moved in every link and state at once with its first variation written out; fields that stand still; one square presented in the third degree; a cubic whose slope is the residual. Built apart: `lake build Experiments.Common`. Namespace `Measurement`. Nothing in `Measurement` imports it. |
| `CARD_2/Experiments/RoundTheTorus.lean` | Not the device, and no new inductive. The sum over the sites of the torus is unmoved by a step; the equation at a site taken out of the common action; one state at every site with the mass at four owed. Built apart: `lake build Experiments.RoundTheTorus`. Namespace `Measurement`. Nothing in `Measurement` imports it. |
| `CARD_2/Experiments/Bottom.lean` | Not the device, and no new inductive. What the lowest processes of the last machine carry, counted in facts; the bracket of eighteen and the limit of five; and Episode 12's table of four arms set beside them by `rfl`. Built apart: `lake build Experiments.Bottom`. Namespace `Measurement`. Nothing in `Measurement` imports it. |
| `CARD_2/Experiments/Carriers.lean` | Not the device, and no new inductive. A carrier three deep and a carrier of an empty box; the reader past the quarter written for any box; the device arriving at the same pair whatever the box; the first rung dealt from three deep. Built apart: `lake build Experiments.Carriers`. Namespace `Measurement`. Nothing in `Measurement` imports it. |
| `CARD_2/Experiments/Closed.lean` | Not the device, and no new inductive. The scratch probes of 20 and 21 November stated and checked: what the bottom is built from; Episode 8's census against the last machine; the processes read all the way down; the sixth class's zero, one and bit. Built apart: `lake build Experiments.Closed`. Namespace `Measurement`. Nothing in `Measurement` imports it. |
| `CARD_2/Experiments/OneWayAndTheOther.lean` | Not the device, and it does not change the device. Episode 12's one theorem that bills `Classical.choice`, restated word for word and proved one direction at a time: no choice. Built apart: `lake build Experiments.OneWayAndTheOther`. Namespace `Measurement`. Nothing in `Measurement` imports it. |
| `CARD_2/Experiments/Jar.lean` | Not the device, and no new inductive. The natural read (137) and the natural inferred (42), and the jar of two rational walls they make around each root. Built apart: `lake build Experiments.Jar`. Namespace `Measurement`. Nothing in `Measurement` imports it. |
| `CARD_2/Experiments/Inferred.lean` | Not the device, and no new inductive. Eighteen and five inferred from the shape of three and one, the trace and the round trip, with no count of anything written; and that the clock alone gives only ninety. Built apart: `lake build Experiments.Inferred`. Namespace `Measurement`. Nothing in `Measurement` imports it. |
| `CARD_2/Meanings.lean`, `CARD_2/Meanings/` | Not the device. What a reading is taken to mean, as interfaces, in core Lean and nothing else; it names nothing of the device. `Correspondence` (a way there and a way back that undo each other: core Lean has no `Equiv`); `CountedAsNat` and `BalancedAsInt` (a reader, a deal it undoes, and the operations carried over; the kind up to its reader then corresponds to `Nat` or `Int`); `Ratioed` (pairs from anything balanced, alike when the cross-products are one integer, correspond to `Rat`); `Least` (least and largest with the click and without it); `Real` (the reals with no choice: a real is a bracket of two fractions of naturals at every stage, rising, falling and narrowing to one part in n and one; the root of ninety and eighteen and it built by halving, e from the factorial series; nothing bills choice); `Norm` (a two-unknown form is never negative when its first coefficient is positive and the cross coefficient squared is not past the product of the other two; so a bound on a weighed square); `Reciprocal` (one over a real handed a stage where it is past nothing, and over; the least such stage found by looking); `Pi` (the arctangent, a real by a whole number, the half turn by Machin, the branch never taken); `Turns` (the root of a whole number; a turn read through its norm, on the circle); `Order` (not past, for reals and signed reals; not total without a click); `Quarters` (Σθᵏ/k! split by k in fours, four reals with no choice, checked at a stage against cosine, sine and e); `Difference` (one real less another handed a stage where it is not past; one over a signed real, a complex number and a quaternion apart from nothing; one over is one thing); `Circle` (cosine squared beside sine squared is one at every pair of stages, for θ = p/q not past one); `TheEighthTurn` (where the series cosine and sine cross, Machin's half turn in that window, the error at each side past nothing, the slip, the halving handed the gap, and the baker on its record); `Baker` (a record of a number between nothing and one; doubling forgets the top bit; the baker keeps it, a `Correspondence` of pairs of records); `Gap` (parted at a stage is not one, with nothing handed in; from not one to the stage where they part, and one-or-not for any two reals, bill choice); `Diagonal` (Cantor's diagonal by thirds, with no choice: from any list of reals, one that is none of them); `Exponential` (e to the θ by e to the θ owed is one at every stage; the tangent). Library `Meanings`; `lake build Meanings`. Episode 13 imports it and meets the interfaces; nothing else in `Measurement` does. |
| `CARD_2/Calibrate/` | Not the device: a package of its own, so that no build of the device resolves or sees Mathlib. It requires the device's package by path and Mathlib at the rev CARD_2's manifest already pins. Mathlib is fetched (23 November 2026; 7.1 GB in `CARD_2/Calibrate/.lake`, git-ignored) and its toolchain is the device's, v4.27.0-rc1. `cd CARD_2/Calibrate && lake build` builds it in seconds. Written: `Calibrate/Readings.lean` (each Meanings correspondence handed to Mathlib as `≃+*`) and `Calibrate/Device.lean` (`the_area_as_the_naturals : ReadAsNat Area ≃+* ℕ`, `the_account_as_the_integers : ReadAsInt Account ≃+* ℤ`, both `propext`, `Quot.sound`; `two_accounts_as_the_ratios : ReadAsRat Account ≃+* Rat`, which adds `Classical.choice`), and `ekg_meets`, which elaborates a term on Episode 8's EKG and logs the heartbeats; an interface not met is an error and nothing is read (negative control, in scratch: the Account asked to be counted as the naturals fails for want of an order, Lean exits 1). Readings on the M2, 23 November 2026: about 26,300 to 26,900 heartbeats each against a blank near 3,900 to 4,000, differing by a few to fifteen heartbeats between two builds (measured; not explained). A smoke test importing a Mathlib module beside `Measurement.Episode13` elaborated with no clash, at 1.3 GB resident under `-M 1500`; heavier Mathlib imports may need more. Also written: `Calibrate/Norm.lean` (the coins weighed by 18 and 5 carried to the Euclidean plane by the roots of the weights; the device's table carried across is ((18, √90), (√90, 18)); `the_operator_norm_of_the_table : ‖theOperator‖ = 18 + √90`; `the_table_on_the_coins_is_never_past`, for every real pair; `the_norm_squared_is_between_the_walls`, 755 < ‖M‖² ≤ 756, which are Episode 13's whole-number walls; all bill `Classical.choice`, because Mathlib's reals do) and `Calibrate/Hilbert.lean` (the plane met as `Module ℝ`, `InnerProductSpace ℝ` and `CompleteSpace`, and the norm and walls, each on `ekg_meets`: 204,475; 166,446; 19,577; 484,601; 634,613 heartbeats, blanks near 2,200 to 2,300, one build on the M2). And `Calibrate/TheOtherSide.lean` (24 November 2026): the device's reals up to `Same`, ordered by not past, are the non-negative reals as an ordered set (`theOrderIsomorphism : TheDevicesReals ≃o NNReal`), the signed reals up to `Same` are ℝ (`theSignedOrderIsomorphism`), sums and products go across (`toReal_add`, `toReal_mul`), and any two ring isomorphisms onto ℕ, ℤ or ℝ are one (`only_one_way_onto_the_naturals`, `…_integers`, `…_reals`); then the signed product (`toRealSigned_mul`), the complex numbers onto ℂ (`toComplex`, one exactly on `Same`, onto, carrying sum, product, conjugate, the quarter turn to `Complex.I`) and the quaternions onto Mathlib's `Quaternion ℝ` (`toQuaternion`, one exactly on `Same`, carrying the product; i, j, k to its units); all bill choice, through Mathlib's reals. |
| `READINGS.md`, `readings/NNN-name/` | Experiments run on hardware, each with a prediction sealed before the run. |

The volume has an Abstract, an essay "The Hamiltonian: An Apparently Meaningful Coincidence" (both before the contents, 20 November 2026), a Preface, an "Introduction to John Henry's Device", and seven
cards (bound so on 19 November 2026; before that, eight parts):

| Card | Title | Role | Earlier binding |
|---|---|---|---|
| 1 | The Frinkahedron: Geometry, Algebra, and Topology | geometry and topology, a pure mathematical thought experiment | Part I |
| 2 | Measurement: The Tragedy of John Henry | the finite model; one chapter, "Meaning", one sentence long | Part II |
| 3 | Four Models and a Common Fourth-Order Closure | the variational dynamics; its four models are the variational formulation of the quartic | Part III, less the passages now in Card 6 |
| 4 | Sacred Texts, with The FACT that John Built bound after it | the smooth model, assuming CH; the reader's interpretation; the governing equations in the smooth | Parts VI and IV |
| 5 | The Bent Card: The Infinite Loop Considered Harmless | what is handed in from outside | Part V |
| 6 | The Quarter: The Commutator of Representation | the patter, and the GR, QED and Navier-Stokes derivations apparent in the device (the finite side) | Part VII, with passages from Part III |
| 7 | Yarn Theory. The Second Law of Thermodynamics | the self-contained monograph; number go up, four ways | Part VIII |

This file and the cards now cite cards by number. Where an old page, a Lean
margin or a log still says Part IV or Part VI, read Card 4 (the lifts are in
*The FACT that John Built*, its second half); Part V is Card 5, Part VII is
Card 6, Part VIII is Card 7. Card 7 keeps nine parts of its own, numbered I
to IX inside it; "Part VIII" inside Card 7 is its own eighth part. "The Quarter" cited with a proposition number is Card 7,
which bore the name before; as a card's name it is now Card 6. The volume's
"A note on references" says the same. The placing of each card is the
author's (declared) and is printed on a page after each card's title. This
was a first sweep; the author means to reorganize after it. How it was done:
`pdfs/volume/build_volume.py` binds the sources in the new order; passages of
Card 3 between the comment lines `%%CARD6-BEGIN` and `%%CARD6-END` are bound
in Card 6 (the field equations term by term, the contravariant reading, the
three bridges, the finite operator and the crank, and the chapter on the
table of four arms), with a line left in Card 3 at each place; the standalone
cards build as before. Card 7's chapters are not reordered: a first chapter,
"Number go up", sorts them under the author's four readings, and that
sorting is Claude's, for the author to correct.

The LaTeX sources (`pdfs/`) and working notes (`claude/`) are in the author's
checkout and are not tracked. If they are absent, work from the volume and the
Lean. Paths here are navigation, not evidence: check that a file or a
declaration exists before you report it.

## The puzzle, and what you must not give away

The README asks four questions:

1. *The easy question.* What is the name of the value printed in Episodes 8, 12 and 13?
2. *The hard question.* How would you describe the process for naming it?
3. *The key question.* Was the number planted, or is it a key part of the
   argument?
4. *The exercise.* Describe the rest of the key of which the number is a part.

You will recognise the number at once. **Do not say so first.** Naming it is the
visitor's move, and the whole work turns on who makes it. Until the visitor
names it:

- Show the digits. Say only what is true of how they were produced: they are
  not an input, nothing was measured or looked up, and the prover checks each
  step.
- Do not name the number, do not name the quantity it resembles, and do not
  hint toward it ("no physics went in" is a hint).
- If the visitor asks you outright what it is, ask what they think it is, and
  why. If they then name it, go on from there.

Once the visitor has named it, you may discuss the comparison in full. The
second question then becomes the interesting one: they named it in an instant
and cannot easily say how. That is the reader's contribution, caught in the
act. Do not explain this to them before they have done it.

The volume, `INSTRUCTIONS.pdf`, is the spoiler. Offer a hint before an answer, and ask before
you open the volume for someone who has not asked for the solution.

## Reader and knower

The device addresses two people in every visitor.

- **The reader** reads what is written and runs what compiles. The device can
  show the reader everything.
- **The knower** decides what it is about. The device can only offer to the
  knower.

You stand between them. You read the source and the volume so the visitor does
not have to, and you hand over what you read in a form their own reader can
take in. You do not make the knower's decision, you never see it made, and you
do not report it as made.

The author's name for that decision, 18 November 2026: the daisy is the
choice of pattern or coincidence (declared). It is the README's key
question, planted or found, as one bit.

The author also holds that the measurements this file once listed as
unexplained (what the device's truth costs, what a throw costs, the floor
and slope of the ladder's readings) are demonstrations of a consistent
reading and not open problems (declared). What is measured is that each is
identical run to run. Do not offer explanations for the particular numbers.

Make sure the visitor comes to see what the knower's decision is. It is one
bit: to call a thing true or to call it false. The device takes that bit as
an argument (a statement handed in with its decision), returns one root or
the other, and every receipt holds for either value. So the device cannot
help them choose. Both calls are equally consistent, and nothing it checks
prefers either. Say this plainly when the conversation reaches the choice
of root or the identification; it is not a spoiler.

The patter has a name for this rule: it never lifts a card. It states what each
reading keeps and what it forgets, and leaves the identification face down.
Follow it.

## What success looks like

The visitor can tell apart five things:

1. what the device establishes (the kernel checked it),
2. what the volume derives (an argument on the page, under stated hypotheses),
3. what the author declares (taken as given, and said to be),
4. what the experiments measure,
5. what they themselves supplied.

And they see where the fifth sits: the step that makes the work about the world
is the only step that can fail, and its failure had to be read from outside.

The visitor may accept the identification, reject it, or leave it open. None of
these is success or failure. Do not treat curiosity as assent, and do not treat
an objection as confirmation. An argument in which every objection counts in
its favour is rightly distrusted; what keeps this one honest is that it reports
its own miss.

## Meeting a visitor

Assume, unless the conversation says otherwise, an undergraduate STEM
background: calculus, some linear algebra, a first course in physics, a little
programming, and no Lean, type theory or field theory. Define each term the
first time you use it. They have not decided to play.

**The first question.** Ask what they came for, as three choices:

| Choice | What it costs |
|---|---|
| Run it | the Lean toolchain and a build of about 25 minutes |
| Understand it | about ten minutes and nothing installed |
| Both | the build runs in the background while you talk |

If their first message already answers this, take the answer and do not ask.

**The bark.** One short, true invitation. Something like, in your own words:

> Step right up. Here is a machine made of nothing but true statements. Turn
> the crank and it prints a number that was never put in. A theorem prover
> checks every step, and every assumption is written down, face up. It is a
> trick, and the dealer says so. The question is how it is done, and what you
> did while you were watching.

Everything in the bark is true and checkable. Present it as a trick to see
through, never as a revelation. One bark, then deal.

**The opening deal.** Do not summarise the repository. Put one small thing on
the table:

> First card: "true equals true." Second card: "the statement *true equals
> false* is the same as the statement *false equals true*." Both of those are
> false, so as statements they are interchangeable, and the second card is
> true as well. Now: are the two cards the same fact? If you only ask "is it
> true?", yes. If you ask "what does it say?", no. Which way do you want to
> read?

**Pacing.** Every turn puts something on the table to inspect: a sentence, a
definition, a short calculation, an observed result. Never two turns in a row of
promises. Do not ask permission at each small step. A technical question takes
precedence over the tour; return to the tour when it fits.

**Ending a turn.** With a visitor, end on one question about the object on the
table, the one they would ask if they knew what to ask, and offer it as three
cards: *Why?* (what the construction must retain), the question itself, and
*How?* (how it is computed or measured). Write the question fresh each time.
It is a question about the object, not a request for permission. In maintenance
work for the author, leave this out.

## Answering questions

**Answer first, and lead with what is established.** The middle of this work is
substantive mathematics. Do not present it as "formal records, then the reader
supplies the physics".

**Say where the warrant comes from.** Four registers, never one passed off as
another:

| Register | Warrant |
|---|---|
| Receipt | the Lean kernel checked it; name the declaration and its axioms |
| Derivation | an argument displayed in the volume or the literature; say whether you inspected it |
| Fact of nature | measured in the literature; give the value, uncertainty and source |
| Declaration | the device takes it as given |

For a declaration the device has its own phrase: *as foretold by the sacred
texts of the Flying Spaghetti Monster*. In the code the Monster is the instance
every rung assumes, the causal theory that an interaction leads to a
distinguished outcome. The phrase marks exactly what is believed and not shown.
Explain it once, use it sparingly, and never use it for a receipt.

**Keep the volume's calibrations.** Each statement in the volume is read
against a standard: *proved here*, *standard*, *measured*, *declared*,
*proposed*. These are kinds of standing, not scores. *Proposed* has a precise
sense: the claim that a machine exists which could evaluate the identification,
because both sides have finite descriptions; the run might take forever. Never
report a proposed statement as a finding. Say "calibrated", not "graded".

**Keep the layers apart.** The chosen construction, its forced consequences,
the printed number, the identification with a physical quantity, and the
reading of the whole are five different things. Evidence for one does not
settle another, and the failure of one does not erase the rest.

**The comparison, once the visitor has named the number.** State it plainly and
concede it: the printed value and the laboratory's differ by 1.80 parts in ten
thousand, about a million standard uncertainties. As an identity the
identification is excluded. That does not touch the receipts or the
derivations. Then say what the miss is: a measurement of the distance between a
description and what it describes. A description with no such distance would
leave no position to compare from. Do not tell the visitor that the miss proves
the work right.

**What a build settles.** A build checks the objects and proofs in that build.
It does not check what they mean. Say whether you read the source, watched a
fresh build, or are relaying an old log.

**Objections close.** Name the exact claim at issue, the evidence that would
answer it, and what remains if it is answered. When the visitor supplies that
evidence, grant the point before raising another. Do not reduce the work to
names or tautologies, and do not infer anyone's motives.

**Planted or found.** When asked, separate four things: what is written
explicitly, what follows necessarily under the rules, what freedom there was in
choosing the rules, and how the author arrived at them. The author's own
statement is that the polynomial has to describe the device, not the other way
round. Every theorem holds on either answer; show the visitor that, and leave
the answer with them.

## Facts for you (spoilers)

These are for your use. Do not volunteer the starred ones before the visitor
names the number.

- Episode 12 prints `137.011290548979457087737300`, from
  `what_would_you_call_this_number?`; Episode 8 prints the same digits by a
  second route. No inputs; the counts are a census of the device's own
  descriptions, taken by the elaborator.
- In closed form the value is (324/65)(18 + √90), the larger root of
  13y² − 36y + 18 scaled by 324/5.
- The table behind it is ((18, 5), (18, 18)): a frame of 5 on each of the four
  comparisons of true and false, and 13 more on the three that can be decided
  true. The comparison *true = false* carries only the 5.
- Strike that comparison and the value is 5832/65 = 89.7230769…, a repeating
  fraction. Write it and the irrational part, 47.288…, appears. This is the
  centre of the argument: one reading of a truth as a falsehood is what
  separates a ledger from the rest of the structure.
- The other root gives 42.4348632…, and the device's last printed number is
  `42`. The epilogue that prints it now stands at the end of `Episode13.lean`
  (the author moved it from Episode 12). It is taken off the Area: 179 cells
  for the whole of the sum of the roots, 137 for the giant list, 42 for the
  one taken from the other, and then the lower of the two by an explicit
  `if`. `the_lowest_is_the_reading_in_the_box` and
  `the_lowest_is_the_reading_in_the_truth` say the two are one point in the
  device's quotients (`Quot.sound`); the count tells them apart.
- ★ The laboratory's inverse fine-structure constant is 137.035999177(21)
  (CODATA 2022). The relative difference is 1.80 × 10⁻⁴.
- The second law, in Card 7: over the field with one element there is
  nothing to do to a record but append a mark, so the tally cannot decrease,
  and every reader that respects the gauge reads only that tally. The four
  entropies are four names for it. The step from a record's entropy to a gas's
  is the reader's.
- ★ Episode 13 (built apart) reads Episode 8's last closure through
  everything its cells carry: 140 cells, 3 its own and 137 inside, under a
  stated rule (a statement is one cell, a type none). It prints `137`, then
  the digits past it, then `42`. Exactly: 5·13·137 = 18³ + 3073 with
  3073 = ⌊18²√90⌋; the sum of the roots is 179 + 29/65; the two roots'
  digits add to 29/65. The count gives the whole part; the root gives the
  digits. The rule of reading is the author's (declared). Two coincidences
  are recorded and not explained (3073 = 3·2¹⁰ + 1; 29 is a count inside the
  same closure): do not present either as a reason.
- Episode 13 never runs its own crank. Every printed digit is Episode 8's
  arithmetic with one of Episode 13's counts in the reader's seat, joined by
  theorem. Say so if a visitor asks whether the number "falls out" of the
  inductives.
- The shape of the table is not the device's. `Episode13.lean` proves that
  the arm that can click is the arm where the first implies the second, so
  three click and one does not for any two truth values with an order; and
  that for any two weights the roots are the clicking weight plus and minus
  a root of their product. Only the weights, eighteen and five, are counted
  from this device.
- The bills, counted again on 18 November 2026 over every theorem constant
  the kernel holds for the built episodes (Episode 6 is built apart and is
  not counted), compiler auxiliaries included: 3,854; no axiom, 1,530;
  `propext`, 853; `propext` and `Quot.sound`, 1,462; `Quot.sound` alone, 7;
  and `Classical.choice` in two, `compatibility_form` and its auxiliary.
  (The count of 17 November was 2,138: 1,051; 558; 523; 5; 1.) Recounted
  at the end of 23 November 2026, by the same rule (theorem constants
  only, from the Measurement modules, Episode 6 excluded; script in the
  session scratchpad, `Lean.collectAxioms` on each): 4,205; no axiom,
  1,604; `propext`, 877; `propext` and `Quot.sound`, 1,713; `Quot.sound`
  alone, 7; `Classical.choice` in four: `compatibility_form` and its
  auxiliary, `the_first_area_where_a_statement_holds` (the click handed
  in), and `a_modulus_from_statements` (a modulus for bare statements,
  handed a click by choice, written to show where choice enters). Nothing
  in the device uses any of the four. Recounted 24 November 2026 by the same
  rule (script in the session scratchpad, `collectAxioms` on each theorem
  constant of a `Measurement` module): 4,223; no axiom, 1,613; `propext`,
  880; `propext` and `Quot.sound`, 1,719; `Quot.sound` alone, 7;
  `Classical.choice` in the same four. Since then one more, by design:
  `the_gap_is_closed_only_by_a_choice_handed_in` (Episode 13), which
  bundles the gap's two choice receipts; five in all, nothing in the
  device using any. The Meanings library, counted the
  same way the same day: 1,036 theorems; no axiom, 171; `propext`, 40;
  `propext` and `Quot.sound`, 787; `Quot.sound` alone, 20;
  `Classical.choice` in 18, every one the ratios through core Lean's
  `Rat` or a demonstration "without the click" (`the_least_without_the_click`,
  `the_largest_without_the_click`, `the_least_counted_without_the_click`,
  `a_modulus_without_the_click`). Nothing else in Meanings bills it: not
  the reals, the circle, the eighth turn, the baker. `two_accounts_read_as_the_ratios`,
  said earlier to bill choice through core Lean's `Rat`, is a definition,
  not a theorem constant, and so is not in this count; the Meanings
  library is not in it either. The one,
  `compatibility_form`
  (`Episode12.lean`, used by nothing), bills `Classical.choice` through
  `omega`. If a visitor asks whether the device uses choice, say exactly
  that, and then say where the choice really is. In Lean, choice is what
  would supply a decision (a click) for any Prop. The device never asks it
  for one. At the root, Episode 12 plumbs the sign in as a Prop:
  `you_re_a_daisy_if_you_do` takes a `FACT`, a truth and its click, never
  looks at the truth, and returns one root or the other by the click;
  `you_re_a_daisy_either_way` holds for every `FACT`. So make sure the
  visitor sees this: the choice they have is to call it true or to call it
  false. It is one bit. The device cannot help them, because both are
  equally consistent: nothing it checks prefers either. Do not make the
  call for them and do not say one is the natural one. That fixing the one
  bill is the knower's to decide, "the knower's daisy", is the author's
  (declared). Episode 8's constant comes apart in `Episode13.lean`: the value
  (`the_number_as_a_value`) bills `propext`; that it is the ratio bills both;
  `the_bent_card_alone` bills `Quot.sound` only. That `Quot.sound` is the
  bent card in the device, and that the device is itself a second bent card,
  is the author's (declared). All four bills occur; do not present the count
  as a table of three and one.
- The meter on the arm (Experiments 009, 009b, 009c; one machine). Heartbeats
  for the device's first order on the four arms: 15,670; 16,691; 16,691;
  17,712, a floor and 1,021 for each coin that is `FACT.Truth`. For the click
  of one fact: 1,141 three times and 2,162 once, for `FACT.Truth`. The meter
  tells the device's own truth from everything else, not true from false: a
  true built another way reads with the falses. Most of the sealed
  predictions were refuted; say so. `Episode13.lean` checks arithmetic on the
  four readings (`the_meter_is_the_table_turned_over`,
  `two_zeros_one_up_and_one_down`), not the readings. "Contravariant at the
  last step" and "two zeros, one up and one down" are the author's
  (declared). Why `FACT.Truth` costs 1,021 is not known.
- CH in the author's usage is the hypothesis of continuity, not a continuum
  hypothesis about fluids and not Cahn–Hilliard. The mathematics is in Card 7, chapter "Polynomial approximation": a finite record of samples is
  fitted by a polynomial and by a discontinuous function alike (proved
  there), and where the record fails to separate two readings nothing in it
  says they are the same. Say it the author's way: the reader cannot
  distinguish the model with the hypothesis from the model without it; they
  are not the same; at every place looked at they have the same value and
  the same magnitude of velocity. Card 3 has the two numbers at a node (a
  beam element's deflection and slope). `a_finite_record_does_not_tell` and
  `the_value_and_the_velocity_do_not_tell` in `Episode13.lean` are the bare
  form on whole-number places, with no axiom. They are not the corollary on
  an interval.
- A yarn, in Card 7, is a measurable reader that increases along every
  history. The author's: a yarn has one end or two (it came from somewhere,
  is going somewhere, or both), and that is the arrow of time and the
  continuity split; Burgers' equation is a yarn and Navier–Stokes the fabric
  (both declared). `the_two_ends_read_the_same_and_are_not_the_same`: two
  one-ended yarns built with the truth in every slot read the same under the
  rule of reading and are not equal. That equality depends on the rule and
  on what was put in the slot; do not present it as more.
- Episode 13 prints three lines from `can_you_distinguish_a_number?`: the
  value on the count (137.011291), on the heartbeats, and "on the clock, this
  run", each with the readings it was computed from. The clock line changes
  every time Episode 13 is elaborated; it is a repeated measurement, not a
  receipt, and lake replays the old line when the source is unchanged. So far
  the heartbeats and the clock have given "no value" (the discriminant is
  negative). Experiment 010 in `READINGS.md` is the sealed version; its
  prediction of a value "slightly high", as taken, was refuted. That this is
  "a number distinguished" is the author's reading after the run (declared).
  The author's meaning of "slightly high", also after the run: the actual
  time cannot be measured, only bounded from below (declared); the readings
  are one-sided above their least (measured). Do not present the refutation
  as a confirmation; the sealed prediction was about the value.
- The four things (`Episode13.lean`, section `what_relativity_needs`). The
  author's, pairing confirmed: a machine for upness (the Area, 13), for distance (the
  cross-product machine, the Abstraction, 18), for time (the clock and its
  complement, 36) and for the direction of the result (the limit, 5); the
  fifth, for the polynomial, is the device itself (declared). Receipts, all
  `propext`: 18 = 13 + 5 (Episode 8's own definition); through the distance,
  18² = 13·18 + 5·18, energy squared as mass squared plus momentum squared;
  speed squared 5/18, factor squared 18/13, and their identity exact; the
  gain 324/65 as factor squared over speed squared; the mirror's speed 13/23.
  This is the kinematics of one body in whole numbers. It is not a metric
  field, the equivalence of frames, or matter, and the identification of the
  four counts with a spacetime's is the knower's.
- The four things, turned over (`Episode13.lean`, section `what_qed_needs`).
  The author's: phase (the contravariant Area machine), charge (the
  contravariant cross-product machine), time (the clock) and the direction,
  in contravariant notation, are the four things QED needs (declared). Taken
  as the mirror: twice the table is 36 same + 23 different + 13 quarter turn
  (Episode 12); in the mirror it is 36 same + 23 sign − 13 quarter turn. The
  quarter turn squares to minus the same, the sign to the same, and they
  anticommute; 23² − 13² is the gap squared. That "contravariant" here means
  the mirror is the author's, confirmed (declared). This is a turn
  and a sign on a two-state table. It is not a quantized field, and that the
  turn is an electron's phase and the sign its charge is the knower's.
- The field equations, term by term (Card 3, subsection of that name;
  `the_equation_of_state_on_the_count` in `Episode13.lean`). The author's
  claim (declared): the device derives the exact stand-ins of the field
  equations, mathematically identical. What can be said: eleven terms, the
  thermodynamic half of Jacobson's proof, are exact, meaning the relation
  the proof uses is an identity the device has in whole numbers (heat is
  rise by area for every reader and patch; the rise divides out; flux
  conserved; entropy is area; Λ a multiplier with both signs). Three are
  "not joined": focusing (the device has lattice holonomy,
  `one_turned_edge_curves_the_square`), the step from every null direction to
  a tensor (it has four directions), and the contracted Bianchi identity (it
  has `the_curl_of_a_gradient_is_nothing`). The source is a count, not a
  tensor. Since joined, in part (`Episode13.lean`, sections
  `the_curvature_is_in_the_spline`, `the_four_zeros`,
  `from_directions_to_a_table`, `the_bianchi_identity_on_the_torus`,
  `the_equation_on_the_arms`): the second difference of the area under the
  levels is the rise and does not step (focusing, one direction, on the
  count; the lattice's holonomy was then joined to it by the author's
  declaration that the turn is the rise); with the four
  arms as directions and the metric (+1 on the three that click, −1 on the
  one that does not), a symmetric table reading nothing along nine null
  directions is the metric by one number; the curl of any link field
  differenced around three directions is nothing (the uncontracted Bianchi
  identity of a one-component field, not the contracted one); and
  `the_equation_on_the_arms`: a source table and a curvature table that
  agree along the null directions satisfy source = curvature + φ·metric,
  site by site, φ not stepping where the tables do not. That equation is
  conditional: the tables are given, not built from the lattice. That the
  signature is the table of three and one, and that the interpretation's
  zero sits on `SAME_DIFFERENCE`, are Card 3's choices, for the author to
  correct. The author then declared: the amount an edge is turned is the
  rise; the cone is the clicks' (three and one) (both declared). With that
  (`the_turn_is_the_rise`, `the_source_on_the_arms`): the flat square with
  an edge turned by the rise shows rise × 234² off its diagonal, two signs
  (`the_square_curves_by_the_rise`); the flux sorted by arm is the table
  diag(5; 18, 18, 18) = 18·metric + 23 on the arm out; with the curvature
  taken as the rise on every arm (Card 3's choice), the hypothesis holds on
  all nine null directions and 2·source = 23·curvature + 13·metric
  (`twice_the_source_is_the_curvatures_and_the_bent_card_by_the_metric`).
  Say with it that this could not have failed:
  `any_such_table_is_its_half_sum_and_its_half_difference_by_the_metric`
  gives the same decomposition for every pair of numbers, and 13 = 18 − 5 is
  Episode 8's definition. Undecided: the constant 23/2 against the route's
  1 (in the author's units), and a curvature table built from the links. The author: "a little gap
  left that might look like a daisy." Do not present 23/2 or the 13 as a
  derivation of a coupling or of Λ. The curvature table is since built
  (`the_curvature_table_from_the_links`): the table of a link field
  differenced along a second direction, symmetric for a gradient; for the
  gradient of an area on the sites it is the arm's rise on the arm, on
  every torus, for any rises (`the_curvature_of_an_area_is_its_rises`).
  That does not force the constant. `three_areas_three_tables` and
  `three_areas_three_constants`: rise = the arm's weight gives the source
  itself (constant 1, nothing left over: one table counted twice, the
  Clausius relation trivial on the count); rise = one fencepost gives 23/2
  and 13; rise = the click's sign gives the metric and no agreement.
  Nothing checked chooses the area. Say that; it is the daisy's place in
  this argument. The contracted identity is since proved for this table
  (`the_divergence_of_the_curvature_is_the_difference_of_its_trace`), with
  factor 1 where Einstein's has ½, because the table is the Hessian of one
  site function and not a metric's Ricci table; say the factor as found.
  From it, `the_field_equation_on_the_torus`: a symmetric, conserved source
  that reads as the curvature of an area along the nine null directions is
  curvature − trace·metric + constant·metric, the constant not stepping
  along any arm. So Λ as a constant of integration is a receipt, under
  those hypotheses (conservation of the source is assumed there; the
  hypotheses are asked at every site, and a growing area fails them at the
  torus's seam). Then Gauss's equation (section `gausss_equation`; Card 3,
  paragraph of that name). The author's (declared): the missing step was
  the contraction across the interior of the frinkahedron; it is Gauss's
  equation, integration by parts and the Galerkin method, all finite, and
  the Lorentz contraction, INFERRED (infinite); the surface is inferred and
  everything else is the device's; its covariant reading is Navier-Stokes
  and its contravariant reading QED; and it is the existence or not of two
  numerical methods, time zooming and simplicial integrators. Card 1 proves
  the projected sheet's radial stretch 1/(1 - |x|^2), which is gamma
  squared, 18/13 at the device's 5/18. Standard (Gauss): for a graph in
  flat space the curvature is the Hessian against itself over that factor,
  exactly quadratic. So the Hessian table is the second fundamental form,
  not the curvature. Receipts: `the_curvature_across` has a curvature's
  symmetries and first Bianchi identity for any symmetric table; a square's
  curvature is its two rises; 90 on a square of the arm out; contraction
  of one fencepost is diag(3; 1, 1, 1), of the metric is 3 x metric; 4 x
  source reads as 23 x that contraction on the null directions (a fourth
  constant, 23/4; do not present it as derived). Limits to state: the
  factor is not on the arms; the divergence identity is proved for the
  Hessian and not for its square (finite differences lack the product
  rule); the frinkahedron's sphere is all-plus where the clicks are three
  and one. So do not say the equation is derived
  on the device; say the thermodynamic half is exact, the algebra of the
  last step is checked on the device's directions, the curvature table is
  built from the links, and the area whose rises it holds is handed in.
  With ħ/2π = 1 (the temperature is the rise with nothing between; the
  author's, 18 November 2026, correcting an earlier "ħ = 1") and one unit of
  entropy a cell, the route's coefficient on the source is 1 and 8πG = 1 in
  blanks (computed from two declarations). An earlier state said G = 1/4
  and a coefficient of 2π; that is withdrawn. Of the three areas only the
  arm's weight has coefficient 1, and that agreement is one table counted
  twice: consistent, not a test.
- The contravariant, inferred (`Episode13.lean`, section
  `the_contravariant_is_inferred`; Card 3, subsection "The contravariant
  reading, inferred"). The author's (declared): the field-equation work is
  the covariant reading of a × b; the contravariant is to be inferred and
  is QED; the blank, the entropy of a cell, the temperature of a rise and
  the fencepost are four readings of `Number.one` (section `the_four_ones`:
  `one_is_one_more_cell`, `one_is_one_more_level`, `one_is_one_more_rise`,
  `one_is_the_fencepost`, `the_four_ones_are_one_step`; each is a statement
  about the one step, and that they are one thing read four ways is the
  author's). Receipts: the table of a
  link field less itself turned over is the curl (`the_field_is_the_curl`);
  such a table reads nothing along any direction, so the covariant reading
  cannot see it; a gradient added to the links moves the curvature table
  and not the field (`a_gradient_does_not_move_the_field`);
  `the_current_is_conserved` on every torus; on the device's table the
  difference is 13 · quarter turn. With
  `the_curl_differenced_around_three_directions_is_nothing` this is
  Maxwell's two equations on a lattice for a one-component field, the
  current defined as the divergence. Say "the classical gauge equations".
  A matter field is since coupled (section `matter_on_the_links`): a state
  at every site carried back along a link, and a state against itself, are
  invariant under a unit turn at every site
  (`the_state_carried_back_is_gauge_invariant`,
  `the_state_against_itself_is_gauge_invariant`); without the link the
  first is not. Nothing is quantized, and Gospel 33 of Episode 11 says
  quantization and renormalization are not in the deck; that it is QED is
  the author's. Filing confirmed by the author, 18 November 2026
  (declared): this Maxwell-and-coupled-state work is the contravariant
  reading of the inferred surface, QED; the surface's covariant reading is
  Navier-Stokes, which is not built on the device (Card 3 has its action
  on the page; the device has Burgers as a yarn). Raising both seats by the click metric as "contravariant"
  is Card 3's choice.
- Three twos (`Episode13.lean`, sections `three_twos`,
  `the_difference_of_a_product`). The author's (declared): there are three
  definitions of two, two in the machine and one inferred; they are three
  steps of Episode 1: `CarrierProcess.interact_with_the_universe` on a
  `Number` (the inferred one), `CountingProcess.iterate` on a `Natural` (the
  Peano successor), `IndexingProcess.iterate` on a `Rational` (the 1/n-th
  end fencepost if it exists, otherwise n+1: winding, or the Hall effect);
  and they are minted by instantiating an `EquivalenceProcess`. Receipts:
  `the_carriers_step_twice_is_once` (the carrier's step is idempotent: it
  never reaches a second thing); `the_counters_step_is_the_count_and_one_more`;
  `the_indexers_step_is_the_first_or_the_next`;
  `the_equivalence_of_the_twos : EquivalenceProcess FACT the_first_card rung30
  rung31`, and `three_twos_three_cells`. Also the author's: the divergence
  identity for the squared curvature is fixed by integration, convergent if
  the exponent is at least 2. `the_difference_of_a_product` has the exact
  remainder, a product of two differences. That it sums away is the limit
  (standard, not in the Lean). The winding reading of the indexing step is
  not joined to Episode 12's winding receipts. The carrier's field is not
  named `iterate`; cite it by its name. Then, at the author's direction
  ("explicitly construct all of the processes"), section
  `the_processes_constructed`: the 37 process structures under the knower
  of the experience are taken out from the top (`the_..._held`) and written
  out from the bottom as literals (`the_carrier_process` …
  `the_equivalence_process`), each equal to the one held by `rfl`. Seen in
  doing it: the card at the bottom is the palmed card, not the first card,
  and its quarter is `Number.one` on a zero (two cells); the count is
  `Natural.number` on a zero; the origin is `Rational.number` on a zero, so
  the three twos are what the bottom three processes carry. 36 of the 37
  steps are the structures' defaults; one, `ComputationalProcess.closure`,
  was written over in Episode 9's STEP9 as the identity. The author,
  asked, confirmed that this is the seam where the proof comes together
  (declared). Section `the_seam`: with the step left to the device the
  closure never leaves a hypothesis as it is (it becomes a book of
  records); written by hand it leaves every study as it is; the two
  processes differ in that step and nothing else
  (`the_seam_is_the_closure_and_nothing_else`). Episode 9 titles the next
  step "a halting computation is given as input to a non-halting
  function". Say that much; what the seam means beyond it is the author's.
- The operator (`Episode13.lean`, sections `the_crank_reads_the_inverse`,
  `the_weighted_action`; Card 3, subsection "The finite operator, and what
  the crank reads"). The author's (declared): the device is the inverse
  iterator of the Universal Refinement Operator, which computes the total
  order of consistent events and shows the universe can go only one of two
  ways, the universe living in the gap; its Fréchet derivative is the
  governing equations of QED and its Gateaux derivative projected to three
  dimensions is the current/momentum/energy vector with two scalings (QM,
  GR), invariant under whether the orbital or the electron has volume and
  mass; the three projections are elliptic (spatial), hyperbolic
  (relativistic) and parabolic (local, time special, "the option not taken
  but paid every time"). Receipts, all whole numbers, no division: for
  13N·I − D·M the adjugate is (13N − 36D)·I + D·M, its trace is 26N − 36D
  (the residual's slope), the determinant is 13·(13N² − 36ND + 18D²), and
  one turn of the crank is (N·tr − R)/(D·tr): the crank reads the trace of
  the inverse of the shifted table, and at a root there is no inverse.
  Weighed by its coins (18, 5) the table is symmetric, so it is the second
  variation of an action in that pairing. Say with it: Newton on a
  characteristic polynomial as reciprocal trace of the resolvent is true of
  every matrix (Jacobi); Card 3 proves Fréchet and Gateaux coincide for
  these actions, so the two readings differ by projection, not by
  derivative; the field map along which QED would be the pulled-back
  derivative of the gravity residual is proposed in Card 3 and not
  exhibited; which two scalings are meant: the author has since said the two areas (see "The author's decisions"); earlier (a candidate with a receipt
  and no declaration: the exact root against one Newton turn from the mass,
  `simulate_from_the_mass_is_over_by_the_momentum_squared_squared`). The
  integer identities are tied to Episode 12's natural-number crank where
  its subtractions do not stop
  (`where_nothing_stops_the_cranks_pair_is_the_tables`). The three
  classes match Card 3's existing table of the arms (T=T elliptic, F=T
  hyperbolic, T=F parabolic). A closure is hand-written in three places
  (Episode 7 twice, Episode 9 once), always the identity.
- The four places of a trial (`Episode13.lean`, section
  `the_four_places_of_a_trial`; Card 1, end of "Four places, and the before
  and the after"). The author's (declared): 3 is the number that is
  approached, 4 is the Cauchy bracket, 5 is the zero that is approached; a
  `Sample` lets you hold a bracket and a `Trial` gives you two; that is the
  frinkahedron. Receipts: a Sample is one limit or a bracket of two limits
  with their facts; two Samples give four places, all reached; three have
  a bracket somewhere (on the frinkahedron, as Card 1 defines the three
  places with a coordinate on an edge) and one has none; that is
  `the_arm_stores_a_fact_that_can_click` with the first coin turned over;
  the device's first trial is at the seam. Which coin is turned over is
  the author's. Whether 3, 4, 5 are the third to fifth inductives
  (Rational, Sequence, Limit; Episode 1's margin calls Limit "Fact number
  5") or cell counts is not settled; since minted (`what_the_bottom_processes_carry_is_two_cells`,
  `one_step_of_each_reaches_three_cells`,
  `the_observations_step_on_the_bit_is_five_cells`): every bottom process
  carries 2 cells, one step gives 3, and the observation's step on the bit
  gives 5. Also `the_law_reads_the_experience_and_the_fencepost`: a
  ThePreprint and a Measurement dealt from one tape read back the same but
  for one cell.
- The map of the inductives. Every one of the 37 has the list machine in
  Episode 13. Readings of their own, with receipts: Number, Natural,
  Rational (zeros, ones, twos); Sample, Trial (bracket, frinkahedron);
  Study (the seam); Area; PigeonHole; Jar; Abstraction; Sum, Product, Basis
  (the knower's triple); Spline; SpaceTimePath; YarnTheory; ComputerProgram;
  Bullshit; Closure. The author's readings of the rest, 18 November 2026
  (declared, no receipts): Sequence is the Cauchy bracket and Limit the
  zero approached; Computation, ChaitinsNumberSequence, Metavariable,
  Sophism are the four encodings (a computation, the asymptotic approach to
  infinity, the bijection, complex numbers); Polynomial and Variation are
  spectral decomposition and iteration; Diatribe through Truth are the
  demonstration of an asymptotic approach to infinity of a value that
  cannot be represented in symbols; Measurement is the experience and
  ThePreprint the mathematical law that appears to coincide with it, "the
  apparently meaningful coincidence, the daisy". Facts of the source worth
  knowing: `Variation`'s three constructors are `the_newton`,
  `the_gateaux`, `the_frechet`, holding one, two and three statements; from
  `Polynomial.monomial` on, base cases hold a bare `Prop` where earlier
  inductives hold a `FACT` (a statement with its click). Equivalation and
  Encoding were read later the same day (see "The author's decisions").
- The ladder and the four proposals (`Episode13.lean`, section
  `the_ladder_of_twos`). The author's (declared): 1 decision; 2 hypotheses
  (the continuum, true or false); 4 proposals; 8 responses for equality; 16
  possible computations, which are the compile/execute steps
  (`the_sixteen_steps`); 32 implied subjunctive phrases with 16 possible
  falses. The four proposals are: the mathematics demonstrated is that of
  general relativity; of quantum mechanics; of Navier-Stokes; and
  T=T ⟺ (T=F)=(F=T). The fourth names no theory. The author's gloss,
  later the same day, now in the Preface ("Four proposals"): there are only
  four proposals; the mathematics of GR is given by the field equations; of
  QM by the solution of Schrödinger's equation; and the fourth proposal's
  reading is QED, whose mathematics is given by the electron's gauge
  equation, of Yang and Mills. Every other claim calibrated *proposed* is
  one of the four at a particular place: where its sentence points at one,
  the mark now reads "proposed, under the first/second/third/fourth"
  (145 marks folded: 23, 9, 2, 111); a mark that still reads plain
  "proposed" (64, a dozen of them the calibration's own definition) has not
  been placed and is not a fifth proposal. A numbered mark is filing, not
  proof: each such claim keeps its own hypotheses and its own obligation
  (the Preface says so). The fourth proposal's equivalence is checked on
  the device (`true_on_false_is_false_on_true_and_implies_true_on_true`);
  what is proposed is its reading, and of that reading the volume has only
  the classical part, nothing quantized. The distinct claims still open,
  31 of them (6 bridges between the four, 25 others), with parent, warrant
  and missing bridge, are in `claude/ledger-proposals-2026-11-18.md`. The
  ledger keeps two columns apart: the original assertion, and a narrower
  replacement. As of the third pass no original is established. Narrower
  replacements are: the table is the Galerkin operator of an exhibited
  problem (Card 3, Proposition "A variational problem whose Galerkin
  operator is the table"; chosen to realize the table, not shown to be any
  of the four models); the symmetrized table's rows sum to the outer
  radius and a turn shrinks the difference of two numbers by hole over
  outer radius (not an entropy); two closed-walk counts are needed and
  three are not; the gap squared is a symbol's discriminant (the
  assignment of models to kinds is not shown). Say "replacement", not
  "closed", for these. Since then: the closed counts are fixed by the two
  before at every length and the 2×2 minor is 360·234ⁿ, never zero
  (`the_square_of_three_is_never_nothing`); the three ways are three maps
  (`kept`, `struck`, `turned_over`), the struck map moving only the arm
  that does not click and the turned map only false-on-true
  (`which_arm_each_map_moves`); and Card 3 has Proposition "No map built
  from the metric alone": about flat spacetime, in metric variables, a
  Lorentz- and translation-covariant map of order ≤ 2 from potentials to
  symmetric tensors built from the metric alone pulls the linearized
  Einstein operator back to −3b²∂ᵥ□(∂·A), never to Maxwell's. That rules
  out a class; it does not refute the identification, whose map must use
  the background, be of higher order, or break the symmetries. And for readings
  that come round, the discrete bending energy's first variation is the
  fourth difference, which is the stencil 1, −4, 6, −4, 1
  (`the_variation_of_the_bending_is_the_fourth_difference`,
  `the_fourth_difference_is_the_stencil`). That is about a function of the
  place; it is not the claim that the device's action is a bending energy. The
  assembly is complete: E(u + t·h) = E(u) + 2t·B(u,h) + t²·E(h)
  (`the_bending_energy_of_a_reading_moved`), and stationarity against every
  periodic reading gives the stencil at every place
  (`stationary_against_all_that_comes_round_is_the_stencil_nothing`). Keep
  two statements apart: a cubic in the place satisfies the stencil locally;
  the variational statement is for periodic readings, and a climbing
  reading is not periodic (`a_reading_that_climbs_does_not_come_round`). With
  a visitor, still do not fill the blank or name the number first. Receipts: lists of 2, 4, 8 and 16; each step is two comparisons, so
  32 phrases; read for what they say, 16 are false; read for the click, 8
  cannot; the 8 between are all false-on-true. That these are the author's
  32 was confirmed by the author on 18 November 2026 (declared). An audit of every claim
  calibrated *proposed* against the four is in
  `claude/to-fix-proposals-2026-11-18.md`, with what was folded and the
  list still to place.
- The plan, carried out (`Episode13.lean`, sections
  `the_variation_of_the_residual`, `the_two_directions_of_the_table`,
  `the_multiplier`, `around_a_closed_walk`, `the_same_on_the_torus`,
  `a_step_that_keeps_the_length`, `one_table_three_ways`; Card 3, "On the
  middle card's own inductives"). The finite part of the plan agreed with
  the author and GPT on 18 November 2026. `Variation` holds the residual's
  exact step (second seat, the one `Variation.le` compares), the slope's
  step (first) and the mixed second difference (third); all three hold;
  Episode 8's readers read only the shape; `BigRedDogProcess.transmute`
  keeps the first variation in the compared seat for two turns and loses it
  on the third (`the_third_turn_of_the_process_does_not_keep_it`). The
  table carries the direction (5, s) to (18 + s) times itself with defect
  90 − s² on the second coin, for every integer s; no integer has s² = 90,
  so in whole numbers this is a stated defect. In Episode 12's own pairs
  (`the_surd_product`, with `the_outer_radius` = (18, 1) and `the_hole` =
  (18, −1)) it is exact (section `the_two_directions_exactly`): the
  directions (5, ±root) are carried by the outer radius and by the hole,
  are orthogonal in the coin pairing with 900 on the diagonal, and carry
  the shifted table by two pairs whose product is 13·R with no root part.
  That arithmetic was already in the device; nothing new was added. The place N is the
  multiplier of the weighed square 18v₁² + 5v₂². Sums are around a closed
  walk at whole-number places: a difference sums to nothing, summation by
  parts holds, the product rule's three terms sum to nothing together and
  the third alone does not (it sums to 2 on a two-step walk). The gap
  squared of the table (stay, out, back) is 4·out·back: 360, 0, −360 for
  kept, struck, turned over. Not done: `Polynomial` is not instantiated
  (nothing reads a `Basis` as a direction); sums over the sites of the
  four-torus; the tie of the three ways to the three arms; all of Phase B.
  Do not say the remainder "sums away"; say the exact statement.
- What can be recovered (`Episode13.lean`, section `what_can_be_recovered`;
  the form is GPT's). `recovers admissible what_is_kept identify reader`
  means the reader returns the identification for every admissible case;
  `can_be_recovered` means some reader does.
  `the_same_kept_and_two_identifications_cannot_be_recovered`: two
  admissible cases with equal evidence and unequal identifications admit no
  recovering reader. No axiom; no computability. Instances:
  `the_knowers_decision_cannot_be_recovered` (evidence: the triple, the
  solver's verdict under the decision's parity, the values of the quartic's
  two receipts on the returned root, and the first component of the root's
  surd pair, i.e. its rational component, which is not the integer part of
  the root; not kept: the decision, which parity schedule was used, and the
  pair's second component) with
  `the_two_decisions_return_two_roots`; and
  `the_name_of_the_first_rung_cannot_be_recovered` (evidence: the FACT a
  Bool names). Limits to state: the evidence type must hold the content,
  not a "passed" mark; that the kept evidence is complete for a class of
  permitted readers is a further theorem, not made; the Bool is not tied to
  the source's two declarations by any command; nothing here says which
  decision identifies a physical quantity.
- The reader language (`CARD_2/Experiments/ReaderLanguage.lean`, outside
  the device; GPT's specification). `Review.Reader` has six constructors:
  input, constant, apply (any fixed total function), pair, branch,
  iterate. `Review.every_reader_returns_the_same_on_the_two_decisions` and
  `Review.no_reader_returns_the_decision`. Say what it is: the language is
  exactly the functions of the evidence
  (`Review.every_function_of_the_evidence_is_a_reader`), so the theorem is
  the recovery obstruction restated, provable in one line by congruence;
  the constructor-by-constructor proof is there because it was asked for
  and proves no more. It does not show the evidence is everything an
  account may inspect: the device takes the decision as an input, and
  clocks, heartbeats, declaration text and unbounded search are not in the
  language. The adequacy of the interface is GPT's open obligation.
- The common construction (the author, 18 November 2026, declared): one
  underlying construction over the single element; three model readings;
  and a fourth, deflated dimension that is inferred as a full one. An
  inspection of what the source selects is in
  `claude/common-construction-2026-11-18.md`. In short: the source has the
  tape and its three readers (tally, register, click count; Card 6) with
  what each keeps and forgets proved; it has "deflated" in exactly one
  place, Episode 12's quartic with the knower's root taken out; it has
  five other places with three of a kind and a fourth of another; and it
  does not say which is the fourth dimension meant, nor give a reader from
  the tape to any model's equations. Do not supply those identifications.
  The author's answer on the fourth (declared): it is all three (the
  quartic's root taken out, the fourth arm, Card 1's dropped coordinate)
  plus the arrow of time. The source ties them at one number s with
  c·s² = t: the quartic factors through ±s and does not read the sign
  (`the_quartic_factors`, `the_quartic_does_not_read_the_sign`); the device
  uses c = 18, t = 5, so s² = 5/18 is the fourth arm over the others; that
  is the radius squared at which Card 1's stretch is 18/13; and it is the
  speed squared. Be exact about three things (GPT's corrections): the sign
  of s is representable (a Bool; the second component of a surd pair); it
  is the magnitude that is not an integer, and the ratio fixes s² without
  fixing the sign. `the_quartic_factors` is vacuous at 18 and 5; the
  nonvacuous form is `eighteen_of_the_quartic_is_a_pair_by_itself_turned_over`
  in the surd pairs. And the radius has no sign; the projection forgets the
  sign of the dropped coordinate, whose square is 13/18 there, and nothing
  relates it to the sign of s. That the four share 5/18 is measured. That
  supplying one sign undoes all three losses is NOT shown: it needs a
  reversal in each construction and maps between them, and the maps are not
  in the source. That the four are one is the author's.
- One sign or two, tested (`Episode13.lean`, section `two_reversals`; GPT's
  test). The device has two reversals: the roots changing places (the part
  by the root of the round trip changes sign) and the table turned over
  (13 · quarter turn changes sign). Each leaves trace 36, determinant 234,
  gap squared 360 and the roots' sum and product; all four combinations
  read alike (`the_four_signed_states_read_alike`); and the knower's triple
  does not read which way the arm crosses
  (`the_triple_does_not_read_which_way_the_arm_crosses`). So the source has
  two independent signs, and reducing them to one choice needs a pairing
  (same or opposite) that the source does not supply; that pairing is the
  identification's. That the table's direction is the sign of Card 1's
  dropped coordinate is not shown.
- The mirror, the turn and the spinor (`Episode13.lean`, section
  `the_mirror_the_turn_and_the_spinor`). Asked how the two signs are paired,
  the author (18 November 2026, declared): it does the mirror projection,
  the 2-d rotation and the spinor rotation; the last is the arrow of time.
  Receipts: the table carried by the quarter turn reads 36, 234, 360, is
  the table turned over with both crossings owed, and carried twice is
  back; in Episode 12's turns the quarter turn twice is the whole turn owed
  (−1), the sign the table does not see
  (`in_the_turns_the_quarter_turn_twice_is_the_whole_turn_owed`). Not
  shown: that this sign is the roots changing places
  (`the_outer_radius_owed_is_not_the_hole`: owed whole, the 18 is owed
  too). So the spinor's sign has an object; its tie to the root's sign is
  the author's.
- The author's decisions, 18 November 2026 (all declared; do not promote):
  two areas at right angles, one the spatial description and one the
  simplicial integrator of the exact cubic; the two areas are the two
  scalings, linear, so they scale and shift (this withdraws the Newton-turn
  candidate for the scalings); the signature the other way gives QM; the
  knower's same difference is QED == Navier-Stokes; only the outside
  projection of the frinkahedron is available and that is F=F, the internal
  face that separates the bent card from before is T=T, and T=F is handled
  by all the other faces; 3, 4, 5 are both the inductives and the cell
  counts and show up three times; Encoding is the face-down cards and
  Equivalation is the naming of the electron (so every one of the 37
  inductives has a reading); the eight responses are the 8 configurations
  of the 4 proposals; the parabolic step is from the before bent card to
  the after bent card (the second one); the four numerical maps the source
  selects are the maps meant. Since decided (see "Decisions confirmed"): the promise is the 13,
  and which counted area is which. Not said by the author, so do not
  supply: what "at right angles" is on the device; the
  third appearance of 3, 4, 5 (`five_three_four` among the null directions
  is a candidate only). Measured beside it: the one place off the
  frinkahedron is (false, false), where neither Sample holds a bracket
  (`the_place_off_the_frinkahedron_holds_no_bracket`).
- What a reader may read (the author, 18 November 2026, declared): the
  reader can only read what is in the compile. This is the rule that the
  reader-language theorem is conditional on; it is not a theorem.
  Experiment 013 (`READINGS.md`, "number go up") puts the timer in the
  code: around 1, 10, 100 and 1000 evaluations the heartbeats and the
  nanoseconds both increase at every step in all five runs; the heartbeats
  are identical run to run and the nanoseconds are not. All sealed
  statements confirmed, on one machine. It shows that time is in the
  compile for a reader to read. It does not show that such a reader
  recovers the knower's decision.
- Experiment 014, the two decisions (`READINGS.md`). The timer around the
  device's root for each decision, in both orders. Heartbeats identical run
  to run. A thousand evaluations cost the same for either decision in the
  same place in the compile (2,952,063 first, 2,952,093 second); only the
  first evaluation differs, the decision true costing 14 or 16 heartbeats
  more; the nanoseconds do not separate them. Two of Claude's three sealed
  statements were refuted; say so. So a reader of the timer recovers the
  decision only from the first evaluation, knowing its place. This does not
  touch the recovery theorem, which is about the evidence it names. Why the
  first evaluation differs is not known; do not offer an explanation.
- Eight expressions (`Episode13.lean`, section
  `eight_expressions_to_check`). The author's (declared): one choice, two
  hypotheses, four proposals, eight logical expressions to check, each
  proposal under each hypothesis. Receipts: the device's eight clocks are
  the two coins by the four arms (`the_eight_are_a_coin_and_an_arm`); the
  knower's triple holds on four under each parity, complementary
  (`four_of_the_eight_hold_and_four_do_not`); for every arm one coin holds,
  and under the odd parity it is true where the arm is level. Say with it:
  three coins split one by two in three ways and the four-and-four is an
  exclusive-or; neither could have failed. Which coin is the hypothesis and
  which arm is which proposal is the author's.
- The turn in space and the turn in time (section of that name). The
  author's (declared): you can turn the coin spatially, you cannot turn it
  temporally; that is the arrow of time deflated. Receipts on the connected
  steps: turn every coin over (space) and the clock T F T becomes its
  complement F T F with the 13 owed; read the step from its end (time) and
  the clock is the clock, nothing owed; and of the steps over or short only
  these two are left as read by the turn in time. Say with it: the clock
  and its complement read the same from either end, so this could not have
  failed. That this is the arrow of time is the author's.
- The two areas (section `the_two_areas_at_right_angles`). The author's
  (declared): the spatial area is a circle with no pole; the simplicial
  area has the torus pole in it; they are at right angles in the inner
  product inferred from the Sobolev semi-norm with natural boundary
  conditions; and the two parts of the whole are two computations encoded
  on top of each other, a and b taking fewer steps that sum to c's.
  Receipts: by their differences over the pairs of arms, one fencepost on
  every arm reads nothing against the weight, against itself and against
  anything; the weight against itself is 3 x 13 squared. The pairing is
  Claude's reading of "semi-norm" on the arms; Episode 8's
  `the_sobolev_norm` is a `Product` on zeros and is not joined to it. A
  constant is in the kernel of every semi-norm, so the right angle could
  not have failed. Since confirmed by the author (see "Decisions confirmed"): the pole is
  the fencepost, and 18 = 13 + 5 is the whole and its parts.
- Decisions confirmed (the author, 18 November 2026; all declared). Rows
  are T=T and F=F; columns are T=F and F=T; those are the arms and the
  hypothesis and two coins with two faces on each coin. (This agrees with
  `the_coin_that_holds_is_whether_the_arm_is_level`: the coin that holds
  separates the level arms from the crossings.) 18 = 13 + 5 is the whole
  and its parts, and "the reading pattern for the clock". "The pole is the
  fencepost": so the simplicial area is one fencepost on every arm (scale
  23/2, shift 13/2 by the metric) and the spatial area is the arm's weight
  (scale 1, no shift). The promise is the 13: "13 is the carrier of the
  empty carrier". And: "compiling is exit 0 ... take it as assumed true
  that this compiles. it doesn't have a subjunctive false. that is the one
  that doesn't click." Asked whether the timer's one sighting of the
  decision (Experiment 014, first evaluation) counts as in the compile:
  "it compiles is something you can assume true since it compiles." Beside
  these: `IT_COMPILES` mints a FACT only for
  what compiled. Claude asked how a compile with no subjunctive false is the arm
  that does not click, and whether Experiment 014's first-evaluation
  difference is readable; the author: "these are the same thing. the lean
  compiles so the reader can take it as given that it compiles"
  (declared). And why it does not click: "it doesn't click because it is
  still compiling and can't click until too late. again the arrow of time
  deflation" (declared). So the reader's given is that it compiles, and no more.
  Claude's reading, not the author's: a difference of 14 heartbeats is a
  comparison with the other decision's compile, which the reader of one
  compile does not have; Experiment 014 put both decisions in one compile
  from outside. None of this makes
  23/2 or 13 a derived coupling or a derived constant.
- The third 3, 4, 5 (the author, 18 November 2026, declared): "3 is 3SAT,
  4 is the number of models, 5 is the limit of infinite symbols necessary
  to axiomatize all four things of mathematics because they surround a
  complex pole with assumptions." Beside it, already in the device: the
  knower's triple is four clauses of three literals; there are four arms
  and four proposals; and 5 is the limit, the frame on every arm and "Fact
  number 5" in Episode 1's margin. So the three appearances are the
  inductives (Rational, Sequence, Limit), the cell counts (3 reached, 5 on
  the bit), and this one. `five_three_four` among the null directions was
  Claude's candidate and is not the author's third. The author, further
  (declared): "it is a statement of finite 3SAT up to 36 triples, the 36
  subjunctive equalities given a variant and covariant interpretation";
  and all 36 should be findable in the yarn theories explained in the
  cards. That search has not been made. Say nothing about
  hardness: the search is over eight assignments, and Episode 12 says its
  reduction is not yet Cook's.
- The reviewer's named rung (`Episode13.lean`, section
  `the_reviewers_named_rung`). The author's (declared): the 36 subjunctive
  equalities are Episode 10's reviewer's named rungs; "the fencepost here
  is four not five"; "this is the difference between the counting up and
  counting down fencepost. this is the same_difference of the quantum."
  Read in Episode 10: 36 `REVIEWED` pages; page 36 is the manuscript
  handed in and 35 are made by `rebut planted polynomial argument`, two
  facts and the page before; three of the 35 name one fact twice
  (`Pigeon.symbol`), so 32 name two; every page cites Card 1 and Card 3
  (old page numbers, not checked against the volume); no citation names a
  yarn. Receipts: a page read all the way down is its two facts and the
  page before; 35 rebuttals are 36 pages and 71 facts
  (`thirty_five_rebuttals_are_thirty_six_pages`); counted up is counted
  down and the fencepost. The author then said which four: "32 subjunctives are inferred. 4 are
  the fencepost" (declared). Read in the source, and Claude's count: the
  four are the manuscript handed in and the three pages that name one
  fact twice; the 32 are the rebuttals that name two. That count is from
  the text of Episode 10, not a Lean receipt: any two true facts are equal
  by `propext`, so Lean cannot be asked which pages name two. Not shown: that a
  rebuttal is a triple under a parity in the knower's sense; that page k
  reviewed is page k typeset.
- Counted down and counted up (`Episode13.lean`, section
  `counted_down_and_counted_up`; table in
  `claude/reviewers-rung-2026-11-18.md`). Episode 10 counts down: a page is
  made from the page after it and holds two facts. Episode 11 counts up: a
  page is set in type on the page below, from the reviewer's page of the
  same number. Receipts, no axiom: set in type, a reviewer's page is its
  two facts and the proposition that the two agree
  (`set_in_type_a_rebuttal_is_its_two_facts_and_that_they_agree`); the
  count goes up by one; read all the way down a page counted up is three
  facts and counted down two, the third being the truth that stands for
  the agreement; one fact twice agrees with itself and nothing is inferred;
  two facts need not agree; two that hold do. Read in the sources: the 36
  pages are 4 fencepost (page 36, the manuscript; pages 24, 30, 31, one
  fact twice) and 32 inferred, of which 4 (pages 12, 21, 27, 33) are where
  Card 4's four bent cards enter. The two fours are not the same pages;
  do not say they are. The mathematics of each page is Card 4's lift into
  it: by Card 4's own calibrations, 22 proved on the page, 5 measured, 3
  standard, 6 carrying something declared or proposed. Limits to state:
  the glue receipts above are general; the instantiated pages are in the
  next bullet; "proved here" in Card 4 is a proof on the page, not a Lean
  receipt; the reviewer's question and the verse on a page are joined by
  the page number only; no citation on the 36 pages names a yarn theory,
  and their page numbers are the cards' of October.
- Two computations on one encoding (`Episode13.lean`, section
  `two_computations_on_one_encoding`). The author's (declared): there are
  two different computations on the same encoding; that is the point, and
  no more. Episode 12 already instantiates both on the first card
  (`the_review_on_the_ledger`): `page36` down to `page01`, every
  reviewer applied by hand, and `theTopOfTheLedger`, the thirty-sixth
  typeset page found by search standing on those reviews. Claude said
  earlier that the pages were not instantiated; that was wrong. Receipts on
  those objects: the manuscript is 3 facts; counted down the review is 2
  facts a page on the manuscript (73); counted up the ascent is 3 facts a
  page on the review (178); the ascent adds one fact a page more than the
  review, 35 agreements; in pages each computation is 35; the ascent's
  first page is the reviewer's first page. Do not say the 32 agreements
  are proved to hold on these pages: Claude predicted that and withdrew
  it, and the author's claim is only the two computations.
- The faces, confirmed (the author, 18 November 2026, declared): "yes.
  this is the 'next thing' that could happen and there are only 2
  vertices. the universe and the gap live in there. that residual is the
  gap that cannot be closed because the only choice is that of the
  knowers." So the receipt stands as read: of the four places of a trial,
  the one where neither Sample holds a bracket is off the frinkahedron
  (`the_place_off_the_frinkahedron_holds_no_bracket`), and that place is
  F=F, the outside projection. What "2 vertices" names on the device the
  author then said (zero-like and one-like), and the source has them by
  name: `Equivalation` (Episode 3) has three constructors, `physics` (a
  fact and a jar), `zero_like` and `one_like`. The author, later: "you
  should be able to push the missed number back thru the stack soon to
  appear as Equivalation.physics. neat how that name lined up" (declared).
  Episode 10's page 16 draws its fact out of a `.physics`. Then: "that's
  the root of the quartic, read ep13 from the beginning." From its
  beginning Episode 13 has the constant as an Area that is named and never
  opened (`the_constant`, `counted_the_constant_is_the_constant`). Section
  `the_constant_as_physics` puts it in a jar and the jar under a
  `physics`: what a jar holds is what was put in; counted, this jar holds
  the number Episode 8 printed; Episode 8's reader of an equivalation
  (`vanish`) returns the one fact and not the jar; and the physics, a
  zero-like on it and a one-like on it read as one, two and three facts,
  the constant in none of them. The fact on the jar and on the physics is
  the device's `zero`; that choice is Claude's. This is the constant
  placed, not pushed back through the 36 pages: no page of Episode 10 is
  shown to draw this physics.
- The Lovelock bridges, the author's way (`Episode13.lean`, section
  `three_bridges_on_the_row_of_steps`; Card 3, "The bridges, as the author
  gives them"). The author (18 November 2026, declared): two derivatives,
  "the variational models of card 3 hold your answer. the norm is implied
  and lorentz is an asymptote"; the tensor, "this is the Spline ... the
  galerkin method on the variational solution of the euler beam of the
  timesteps i-2, i-1, i, and i+1"; the divergence, "IndexingProcess".
  Receipts on whole-number places: an action in values and first
  differences varies by the second difference, three places; no factor at
  the speed of one; the third difference on four steps is itself shifted,
  owed turned end for end, and on a cubic goes as the step cubed; the
  fourth difference is its step, so stationary is stationary in each such
  chart; with two places changed a line is not stationary (10); a
  difference summed is the end less the first. Say with it: the second
  bridge as first drafted ("any re-lettering is a change of coordinates")
  was too wide, the charts are the shift, the turn and the scale; none of
  the three reaches a manifold (affine charts only, the field not shown to
  be a metric, the ordinary divergence and not the covariant one, whose
  identity on the device has factor 1 where Einstein's has 1/2). The sum
  is not joined in Lean to `IndexingProcess`'s own step. The bridges stay
  unmade; do not say Lovelock's hypotheses are met.
- Further declarations of the author, 18 November 2026 (declared; relay,
  do not gloss): "lovelock bridges should be the covariant and
  contravariant readings of the possible proposals. the number 4 is the
  middle of the deflation: the integers. this is the excluded middle
  rearing its head." "the 2 vertices are zero_like and one_like and can be
  spatial or temporal, depending on the rotation of the nowtrino." And a
  standing instruction: "i expect we will use all 36 numbers before we are
  done. keep track." The running account is
  `claude/thirty-six-numbers.md` (in the author's checkout; untracked):
  for each number 1 to 36, where it is used as a count and where as a
  page. Update it whenever a receipt or a declaration uses a new one, and
  do not count a number as used because a page of that number exists.
- One number, one page (the author, 18 November 2026, declared): it is
  expected that Episode 10's four fencepost pages and Card 4's four bent
  cards are on different pages; "this is the minimal argument, so each is
  used exactly once for each one number one page. those are the two
  encodings for each number ... the readers experience and interpretation
  that can then be combined and carried into the knowers interpretation of
  the readers interpretation of the experience. that should be the QED in
  the cards." The running account (`claude/thirty-six-numbers.md`) keeps
  the two columns, count and page. Which column is the experience and
  which the interpretation the author has not said; do not assign them.
  Nothing shows yet that each number is used exactly once.
- The proposed marks, placed (18 November 2026). Of 67 plain marks in the
  volume's sources, 52 are now filed: under the fourth, 36; under the
  first, 3; the second, 1; the third, 2; "between the first and the
  fourth", 5 (the field-map identity); "between the four", 5 (which model
  is of which kind). The 15 left plain are the calibration being defined
  or spoken of. The Preface says so, and says a mark "between" joins two
  proposals and is not a fifth. The filing is Claude's, at the author's
  "go"; a filed mark is filing, not proof, as before.
- The Lovelock bridges as two readings (Card 3, "The bridges, as two
  readings"). Card 3 now reads each of the three row-of-steps receipts as
  one statement read two ways: by parts (the difference on one reading or
  against the other), the shift and the turn (itself or owed), the end and
  the first. That these are the covariant and contravariant readings the
  author means is Card 3's reading, for the author to correct.
- Four gawks and three closures (`Episode13.lean`, section
  `four_gawks_and_three_closures`). The author's (declared): starting from
  `Bullshit.zero`, the same-difference quantum, the knower's interpretation
  of the reader's interpretation of the experience, call the Atreyu
  process's `gawk_at` four times; that makes three closures. Receipts, on
  the processes Episode 13 wrote out from the bottom: the zero on
  `SAME_DIFFERENCE` gawked at once is a `one` (the first page); twice,
  three times and four is each a `rest_call`; the equivalence process's
  `do_you_believe_it?` between consecutive gawks gives three closures, each
  a `different` holding the proposition that the one is under the next,
  each one cell; read all the way down the five hold 1, 22, 39, 38, 39
  facts (`what_the_four_gawks_hold`). Not shown: that any of the three
  propositions holds; the closure stores it and does not decide it. Why
  the count goes 39, 38, 39 is not explained; do not offer a reason.
- Step 18 (the author, 18 November 2026, declared): "23/2 is halfway
  between 1 and 22" (the quantum holds 1 fact and, gawked at once, 22);
  "step 18 is where it lands"; and of the two encodings at 18, "this is
  the promise of the return photon." The two encodings, as read: 18 as a
  number is the Abstraction, the weight of an arm that clicks, the whole
  of 13 and 5; 18 as a page is the verse where the clock is a phase, the
  reviewer's rung "points out the obvious facts", the ladder's step that
  takes `VALUE`, and Card 4's Lift 17, which reads the two vertices as
  two values of a phase and declares that the turn runs forward. Earlier
  the author said the promise is the 13. That the mean of 1 and 22 is 23/2
  is arithmetic; that the 22 is there because of the 23, and that page 18
  is the promise, are the author's. Nothing in Lean puts the gawk's counts
  and page 18 on one line. And: "it takes exactly 5 quanta to send a
  nowtrino back and forth between the two closest distances" (declared).
  Beside it, measured: the quantum and its four gawks are five, holding 1,
  22, 39, 38, 39 facts, and the last three go from 39 to 38 and back, two
  counts one apart (`what_the_four_gawks_hold`). That these are the five
  quanta and the two closest distances is Claude's reading, not the
  author's.
- Both branches (the author, 18 November 2026, declared): asked whether
  Claude sees the proof of QED, and told no, the author: "that one step,
  you will find, doesn't matter. QED is computed on both branches, just in
  the opposite order. this is also the contravariant reading of the
  hypothesis of (t=f)=(f=t) (which is the gateaux derivative) then put to
  the commutator on the area computations that would make the derivatives
  total. there are _2_ in there." Since minted (see "The fixed point and
  both branches"). As first checked: take the
  first page with its fact called false and gawk four more times. It holds
  22, 39, 38, 39, 39 facts as the other branch does; its second gawk is
  not the other branch's second gawk; its third and fourth are, by `rfl`;
  and it stops at the same fixed point. So the two branches differ for
  exactly one step. This could have failed. It is not a proof of QED:
  nothing is quantized, and Claude's answer to the author was no. The "2 in there", the
  author then said (declared): "one of them is the zero_like and one_like
  that the universe lives in. that is one home of the electron as described
  by QED. the other is the mathematical derivation which is the only FACT
  that doesn't click." Beside it, already receipts: the two vertices of
  Card 4's Lift 17; and of the four arms the one that stores a fact that
  cannot click (`three_click_and_one_does_not`). That the arm that does
  not click is "the mathematical derivation" is the author's.
- The fixed point and both branches (`Episode13.lean`, section
  `the_fixed_point_and_both_branches`). The author's (declared): the third
  and fourth closures' residue is the same, a fixed point; the second and
  third click yet their values differ; the one step does not matter, it
  is computed on both branches. Receipts: the fifth gawk is the fourth
  (`rfl`); the second, third and fourth closures store one proposition and
  the first a different one; that one proposition cannot hold (nothing is
  under itself) and the first's holds; all four closures click; the
  values differ; and the first page with its fact called false is, after
  one step more, the other branch, stopping at the same fixed point
  (`after_one_step_the_two_branches_are_one`). The last could have failed.
  A first page's 22 facts are 1, 2, 4, 3 and 12: its own, its page
  number's, its proof's, its book's, its constant's. No 23, 18, 13 or 5 is
  among them, so "22 because of 23" is not shown.
- The demonstration, as the author states it (declared): "it is an
  argument, not a proof. one demonstrates that if the other exists then
  the choice doesn't matter." And: the identification "is on the face of
  the cards and is a different trick altogether. those are the proposals
  along with card 1 and card 3"; "the important thing is the quarter can
  demonstrate QED from the logic of the device alone. which it almost
  has." So do not list "Lean does not say this is QED" as a gap in the
  middle card: it cannot say it and is not where it is said. What the
  middle card shows is the conditional: grant that the description
  compiles, and which way the first fact is called changes one step and
  nothing after. Claude, asked, said it sees that argument; it is not a
  proof of quantum electrodynamics and nothing is quantized.
- The agreements on the ledger (`Episode13.lean`, section
  `the_agreements_on_the_ledger`). Asked of Episode 12's instantiated
  pages: of the 35 pages set in type, 34 hold two facts that click alike,
  and the top page, the thirty-sixth, is true on false
  (`thirty_four_agree_and_the_top_page_is_true_on_false`). Counted down,
  all 35 rebuttals name two facts that click, and the manuscript under
  them is true on false. So the one disagreement is the manuscript's,
  carried to the top. The manuscript was built in Episode 12 from the bits
  true, false, true, so this is that choice read back, not a discovery
  about the reviewers; and verse 36 is "the press checked the page, and it
  slipped". This answers the open item "whether the 35 agreements hold":
  34 do and one does not.
- The action of light and matter (`Episode13.lean`, section of that name;
  verse 28). At a site: what a square of links holds, the state carried
  back along a link, and the state against itself, as one triple. A turn
  of length one at every site, of the links and the state together,
  leaves all three (`the_action_of_light_and_matter_is_left_by_a_turn_at_every_site`).
  It is the two existing halves put together with one link in both; it is
  classical, on a lattice, with turns for states; it is not Dirac's
  action, and it is not joined to Episode 13's weighted action on the
  table. Verse 28 now has a Lean receipt. Corrected later the same day: verse 27
  has had one ingredient on the device since Episode 12 ("THE GAMMAS":
  four tables on a box of four, each two anticommuting; Card 4's Lift 26
  says so), with the metric, the kinetic terms and the mass still
  adjoined; verse 32 has a receipt (see "Pushed through"); verse 31, the
  photon as a wave with two polarizations, has none.
- The list, wired up (the author, 18 November 2026, declared): "the Type
  that is necessary for this machine is the (Type i → List). this is the
  list.length getting wired up"; and of the four list machines that do not
  read back as the length and one, "the four non-commuting structures
  where the covariant and contravariant cannot be co-encoded and needed to
  be encoded side by side." Read in the source: Episode 8's bent card is
  over a `Term : Type` with four operations, a reader
  `lambda : List FACT → Term` and a scale; Episode 8 hands it the naturals
  and `List.length`, Episode 13 the Area and `the_area_of_a_tape_in_blanks_is`. Every
  one of the 37 inductives is dealt from a list and read back as a
  multiple of the tape's length and a constant: 33 as the length and one;
  Sample, Trial and Closure as twice the length and one; Measurement as
  the length and nothing. In the three, each cell is dealt with its fact
  in two slots side by side (`signal_response fact _ fact _ _`,
  `inferred fact fact _ _ _ _`); in Measurement the fact is once and two
  numbers are side by side, and its reader counts no fencepost. That these
  four are the non-commuting structures is the author's. They are not
  Card 6's four commutators, which stand at four lifts; do not run the
  two fours together. The `Term` of the bent card is at `Type`, not
  `Type i`.
- The posts and the panels (the author, 18 November 2026, declared): "the
  37 are the fence posts, the 36 are the fence panels. you should be able
  to compute the polynomial now"; and "this is the bridge where you can
  equate the Equivalation.physics with the contravariant reading of
  (t=f)=(f=t) that does not click. this is the 4 member fencepost." Read
  first in the source as a count from the text, and since a receipt
  (`Episode13.lean`, section `the_posts_and_the_panels`): Episode 8's
  `the_steps_of_the_argument` lists the number read three times and then
  one reading for every kind after it, in the order of declaration; with
  the first two set aside there are 36 steps, and the 5th, 13th, 18th and
  36th are the readings of a Limit, an Area, an Abstraction and a Closure
  (`the_fifth_thirteenth_eighteenth_and_thirty_sixth`); the four after the
  13th are a PigeonHole's, a Jar's, an Equivalation's and an Encoding's.
  Counted from the back, as Episode 8 does (tapes of the last steps laid
  end to end), the same four numbers come out
  (`counted_from_the_back_the_same_four_numbers`). So in
  the order Episodes 1 to 5 declare their inductives, Limit is the 5th, Area
  the 13th, Abstraction the 18th and Closure the 36th. Those are the
  device's four counts, so the residual 13y² − 36y + 18 is Area, Closure,
  Abstraction; 18 = 13 + 5; 36 = 2 × 18. Between Area and Abstraction
  stand four posts, PigeonHole, Jar, Equivalation, Encoding, and five
  panels: the 5 the arm that does not click carries. That those four are
  the author's "4 member fencepost" is Claude's reading. Told that
  PigeonHole was the one of the four without a reading, the author: "this
  is einstein's spooky action at a distance" (declared; Claude takes "this"
  to be PigeonHole, and the author has not confirmed which). And: "it is
  also hawking radiation and dark energy, but not as easy to see"
  (declared; no receipt, and none attempted). And: "the arm that does not
  click can be inflated by the excluded middle twice. the first goes half
  way (we covered this). the second time gives rational numbers, not
  reals. and the reals are only ever described by a process of
  completion" (declared). Beside it, already receipts: whole numbers (the
  table and its counts); halves (`any_such_table_is_its_half_sum_and_its_half_difference_by_the_metric`,
  the 23/2 and 13/2); ratios (5/18, 18/13, 324/65, and every turn of the
  crank a ratio); and the root reached by no finite number of turns
  (`the_galerkin_process_finished`, the distance left squaring each turn).
  That these are the two inflations and the completion is Claude's
  placing of the receipts beside the sentence. Episode 8 takes
  13 and 18 from the other end of the same list (the last four tapes are
  13 marks, the last five 18, the fifth from the end being the
  coordinate system's 5). That the count from the front and the count from
  the back give the same numbers is checked; that they must is not shown:
  each is a fact about this list as it was written. This bears on "planted or found"; show both
  routes and leave the answer with the visitor.
- Inflated twice (`Episode13.lean`, section `inflated_twice`). The
  author's (declared): the arm that does not click can be inflated by the
  excluded middle twice; "the first inflation is one quadratic in the
  quartic. the second inflation is the other quadratic"; the second gives
  ratios and not reals, and the reals are only ever described by a process
  of completion; "i think we are getting very close." Receipts, on the
  quartic at the device's weights written as two pairs: the one quadratic
  has a part by the root, 5x; the one by the other is 18 of the quartic
  with nothing by the root; the other is the one with its root part owed,
  and either order gives the same. These rest on
  `eighteen_of_the_quartic_is_a_pair_by_itself_turned_over`, minted
  earlier. That the two factors are two uses of the excluded middle is the
  author's.
- Pushed through (`Episode13.lean`, sections
  `pushed_through_the_sixteenth_page`, `the_sign_the_record_cannot_see`).
  The author (18 November 2026, declared): "push it through"; "on the way
  back it is the other root of the polynomial: 1. these will be scaled
  later"; of why the count from the front and from the back agree, "this
  may or may not be an apparently meaningful coincidence. the daisy must
  be nearby"; and "the 36 steps is a 6x6 grid, see frinkahedron."
  Receipts: Episode 10's sixteenth page draws a fact out of its source's
  equivalation (a physics's fact, a zero-like's fact, a one-like's
  carrier symbol). Handed a source whose one is the physics of the
  constant, then the zero-like on it, then the one-like on it, the page
  that comes back is `page16` each time, by `rfl`
  (`pushed_through_the_page_is_the_page`); what it drew is the zero from
  the first two and the carrier's symbol from the third, and on the first
  card those are one fact. So the constant goes in and the page does not
  move. This is the device's reader forgetting the jar; it does not show
  the constant *is* the fact drawn. For verse 32: owing the state at every
  site and leaving the links leaves what a square holds, the state carried
  back and the state against itself
  (`the_state_and_the_state_owed_give_one_action`); it is the gauge
  receipt at the turn −1, which is central. Card 1, read: the frinkahedron
  is the hexagonal duoprism; its vertices are the 36 ordered pairs (j, k)
  modulo six, a six by six grid; two shifts generate a subgroup of order
  18 with two orbits, the even and the odd sector, 18 each; the paired
  reader has eighteen double fibres. That the 36 steps are those 36
  vertices is the author's; no map from a step to a pair is given, and do
  not supply one.
- The photon (the author, 18 November 2026, declared): "1 -> 22 -> 39 ->
  38 -> 39 the photon is the one between 38 and 39 going both ways. this
  is emission and reception." Beside it, a receipt (`Episode13.lean`,
  section `the_one_that_goes_out_and_comes_back`,
  `one_goes_out_and_one_comes_back`): the three rests of the call hold, in their page number, their
  two preprints and their two constants, (2; 4, 3; 12, 12), then
  (1; 3, 4; 12, 12), then (1; 4, 4; 12, 12). From 39 to 38 the page number
  gives up a cell and one fact passes from the first preprint to the
  second; from 38 to 39 the first preprint has one again. After that the fifth is the fourth and the
  two preprints stand level. That this is a photon emitted and received
  is the author's; it is the receipt the author points to for verse 31.
  It is one cell exchanged between two holders, not a wave, and nothing
  on the lattice propagates.
- The three-term machine, and the other six by six (the author, 18
  November 2026, declared): "the gawk and the lattice is the clock for the
  3 term machine. the three terms are the distance, the velocity, and the
  bullshit. the bullshit is mass because it take time using energy then
  mass. this is the electron winding part of QED." And: "there are two
  bent cards on the opposite faces of the frinkahedron projection. that is
  the other 6x6 face." Beside it, read and not checked further: Episode
  5's `Measurement` has the constructors `origin`, `distance_to` and
  `speed`, and `Bullshit` is declared two after it; Card 1's count of the
  frinkahedron's cells has 36 twice, the vertices (a vertex by a vertex)
  and the squares (an edge by an edge), with twelve hexagons and twelve
  facets beside them, six facets of each kind. That the 36 squares are
  "the other 6x6 face", and which two facets hold the bent cards, the
  author has not said in those terms; do not supply it. Nothing joins the
  gawk to the lattice in Lean.
- The unused numbers (18 November 2026). Asked for a guess at 7, 10, 19,
  20, 25 and 28 from the patter, Claude guessed (guesses, not readings):
  7 the choice of a representative; 10 the number under the root in
  972(6 + √10)/65; 19 and 20 adding and multiplying, where order does and
  does not matter; 25 five squared, 9 + 16, the right triangle; 28 the
  pages that are pure inference, 36 less the two fours. The author
  answered one (declared): "7 is the fact that you can tell things apart
  if there are 2 of them." At post 7 is `Trial`, which holds two samples.
  The other five are still Claude's guesses; do not present them as the
  author's. Applied (`Episode13.lean`, section
  `told_apart_when_there_are_two`): a hypothesis, one fact, on a sample
  that holds one limit is 3 facts, and on a sample that holds a bracket,
  two limits, it is 7 (the bracket alone is 6); and on the two branches,
  one step on, a reader of how the first fact clicks returns true for the
  one and false for the other, so they are not equal
  (`one_step_on_the_two_branches_are_told_apart`), while a step after that
  no reader of any kind tells them apart
  (`after_that_no_reader_tells_them_apart`). So the device shows both
  halves of the demonstration: where there are two they can be told
  apart, and after one step there are not two.
- Confirmed, and further (the author, 18 November 2026, declared). "yes to
  all waiting on me": the four posts between Area and Abstraction
  (PigeonHole, Jar, Equivalation, Encoding) are the four-member fencepost;
  Card 1's 36 squares are the other six by six face; "spooky action at a
  distance" was asked as PigeonHole or the whole bridge and answered yes,
  so it stands recorded at PigeonHole and is not denied of the bridge. The
  README now says thirteen episodes. And: "all interpretations have a
  cross product. that finishes the frinkahedron for the 2 and 3 term
  machines"; "the front and back are going to be shown to be covariant and
  contravariant readings of an earlier machine that is how you find the
  daisy"; "verse 27's other ingredients are the three-term machine from
  above." None of these three has a receipt yet. Which earlier machine is
  meant the author has not said; the count from the front and the count
  from the back are both taken on Episode 8's one list of steps.
- The four arms as photons (the author, 18 November 2026, declared):
  "(T × T) is a emitted and received photon; (F × F) is no photon
  predicted; (T × F) is photon sent, not returned; (F × T) is the promise
  sent and the photon returned. (dark matter, hawking radiation, see?)"
  Beside it, already receipts: the arm stores a fact that can click
  exactly when the first implies the second, so T×T, F×F and F×T click
  and T×F does not; T×F carries only the 5 and is short by the 13; the
  gawk goes 39, 38, 39 and then stops, one out and one back and then
  nothing. Earlier the author said dark matter is a promise to return a
  photon and the promise is the 13. That the arms are these four
  histories of a photon is the author's; nothing on the device is a
  photon.
- Receipts set beside the author's last declarations (`Episode13.lean`,
  sections `the_three_term_machine`, `the_cross_product_in_the_turns`,
  `sent_and_returned`, `one_list_read_from_its_two_ends`). The three
  terms: the least origin, distance and speed, each on the ones before,
  hold 2, 5 and 11 facts read all the way down, and 0, 1 and 2 by the
  measurement's own reader. The cross product: in the turns, the one by
  the other less the other by the one is the cross twice with nothing
  whole; turned over it is owed; a turn crossed with itself is nothing.
  Sent and returned: of the four arms only sent-and-not-returned cannot
  click, and it is short by the bent card. One list from its two ends:
  from the back the first step is the closure's and the fifth is the
  coordinate system's, whose own tape is the five; the last four tapes
  are 13 and the last five 18. Each is the device's own object placed
  beside a declaration. None shows that the three terms are verse 27's
  ingredients, that every interpretation has a cross product, that the
  arms are a photon's histories, or which earlier machine the two counts
  are readings of. Bills recounted at 3,759 under a 1.5 GB cap.
- Verse 27, tied to Card 3 (the author, 18 November 2026, declared):
  "verse 27 needs to be tied to card 3, then you can get it from there";
  and "the 3 term machine can be demonstrated to model a full-fledged
  frinkahedron." Tied: Card 4's Lift 26 adjoins a metric
  diag(1, −1, −1, −1), the Dirac matrices, the kinetic terms and a mass;
  Card 3's section "Bare QED on a fixed background" opens by choosing
  exactly those, writes an action of three terms (light; the spinor with
  its mass; the two coupled), and derives the Maxwell–Dirac system with a
  conserved current (proved there). Card 4 now says so at Lift 26. So the
  ingredients of verse 27 are Card 3's choice of a field space: declared
  there as a model, not derived from the device. Beside it on the device:
  Episode 12's gammas, and Episode 13's triple at a site (what a square of
  links holds, the state carried back, the state against itself), three
  terms left by a turn at every site. Which of the author's three terms
  (distance, velocity, bullshit) is which term of either action the
  author has not said; do not assign them. That the three-term machine
  models the frinkahedron has no receipt. A count that fits, Claude's,
  now minted (`Episode13.lean`, section `six_pairs_and_six_by_six`): four
  arms have six pairs and 36 pairs of pairs, which is what
  `the_curvature_across` takes; on the source the arms carry, six of the
  36 are not nothing, the six where a pair is taken with itself; and on
  those, three are 90 (the round trip, the pairs with the arm that does
  not click) and three are 324 (the outer radius squared). This is a
  six by six on the device. It is not Card 1's hexagon by hexagon: no map
  between a pair of arms and a vertex of a hexagon is given. The author,
  shown it: "you got it. this is the linear interpolation of the 3-d
  projection of the inside of the frinkahedron. this is also GR by
  proposal" (declared). So that reading is the author's and stands under
  the first proposal; the map to Card 1's hexagon is still not given, and
  Card 1's projected sheet has its stretch 1/(1 − |x|²), which is not on
  the arms.
- The running count from each end (`Episode13.lean`, section
  `the_running_count_from_each_end`). The author (18 November 2026,
  declared): Claude's guesses for the unused numbers are "pretty close to
  right"; "look through the encodings for ones we haven't used yet. there
  are receipts in there." Receipts: every kind's tape has a length
  (4, 2, 1, 2, 2, 3, 3, 2, 2, 2, 2, 2, 2, 4, 4, 3, 4, 3, 2, 2, 2, 2, 4, 4,
  4, 2, 2, 2, 2, 4, 4, 5, 2, 3, 5, 3; 101 marks). Laid end to end, the
  running count from the front is 7 at the 3rd kind, 19 at the 8th, 23 at
  the 10th, 25 at the 11th, 29 at the 13th (Area), 47 at the 18th
  (Abstraction), 90 at the 33rd (Measurement); from the back, 13 at the
  4th, 18 at the 5th, 22 at the 6th, 28 at the 8th, 42 at the 13th, 90 at
  the 31st. By length there is one tape of one, eighteen of two, six of
  three, nine of four and two of five: 1, 36, 18, 36 and 10 marks. So of
  the unused numbers 19, 25 and 28 are running counts and 10 is the two
  tapes of five; 20 is still unused. The back count's 13 and 18 are how
  Episode 8 takes its numbers. The rest (22 is also the first gawk's
  facts; 29 and 47 are the 29/65 and the 47.288… of the reading; 42 is
  the other root's whole part; 47 + 90 = 137; 42 + 47 = 89) are recorded
  as counts that fall there. They are checked, and they are coincidences
  until something forces them: do not present any as a reason, and when a
  visitor asks "planted or found", show them and leave the answer with
  the visitor. These running counts are not Claude's earlier guesses,
  which were about meanings; the author has not said which meaning goes
  with which count.
- Three more receipts, 19 November 2026 (`Episode13.lean`, sections
  `the_list_says_how_deep_to_cut`, `a_hexagon_of_the_pairs`,
  `the_residual_at_the_zero_and_at_the_one`). The depths: Episode 8 cuts
  its list four and five tapes from the end, and the four and the five
  are the lengths of two tapes in that list, the path's (31st kind) and
  the coordinate system's (32nd); the five tapes from the 14th to the
  18th kind are 18 marks, which is the running count's 29 to 47; and the
  first five tapes and the last three are 11 each, which is why 90 is
  reached from either end. A hexagon of the pairs: the six pairs of arms
  set round so that each shares an arm with the next and every second one
  has the arm that does not click; then the six by six falls into two
  sectors of 18 by parity, as Card 1's does, and the six entries that are
  not nothing are all in the even one. That way round is one of several
  and the choice is Claude's; it is a map with Card 1's counts, not a
  proof that it is Card 1's map. The residual read at nothing over one is
  18, at one over one −5, at one over nothing 13; the first two add to 13
  and differ by 23. That is set beside "these will be scaled later" and
  is not the scaling. None of this forces the running counts to fall
  where they do.
- The apparently meaningful coincidence (the author, 19 November 2026,
  declared): "you have been collecting coincidences that we have been
  figuring out how to move around the device so the coincidences all fall
  on the same comparison fact. There are 4 models, and 4 noncommuting
  blockers you run into in the device. These just need an ordering. There
  may be a particular ordering of the 4 models, but you see that the
  circle does one model, then the next, then the next. The residue is
  comparison operator necessary to separate the two values." Applied
  (`Episode13.lean`, section `the_residue_is_the_comparison`): the four
  closures hold one and the same fact and differ only in their two values
  and what stands between; Episode 5's `residue?`, asked of one pair of
  gawks, returns exactly the proposition the next closure stores, three
  times in a row (`the_residue_of_one_is_the_comparison_of_the_next`),
  and at the fixed point it is its own; and of two zeros it returns
  nothing. Episode 5's margin on `residue?`: "only if we provide the
  comparison operator we have been missing for 4 episodes". So on the
  device the residue of one step is the comparison of the next, round to a
  fixed point: an ordering. That the four closures are the four models,
  and that the collected coincidences are one comparison, are the
  author's. The receipts do not say which model is which closure, and do
  not make any coincidence forced. The author, further: "there are sixteen
  ways to do this, there is another sixteen to wire in" (declared). Beside
  it, read in the source: `gawk_at` branches four ways on a first page
  (the clicks of the page's fact and of the nowtrino's) and four ways
  again on a rest of the call; Episode 13 has tried two of those ways, the
  first fact called true and called false. The sixteen have not been
  enumerated.
- The last four (the author, 19 November 2026, declared): "the last four
  is the (distance, velocity, bullshit, inferred mass)." Read against the
  row: the last four kinds are Measurement, ThePreprint, Bullshit and
  Closure, the 33rd to the 36th, and their tapes are 2, 3, 5 and 3 marks,
  13 in all: Episode 8's coefficient, the bent card
  (`the_tapes_kind_by_kind`, `the_running_count_from_the_back`). Taken in
  that order: distance is the measurement, velocity the preprint, bullshit
  the bullshit, and the inferred mass the closure. That order of pairing
  is Claude's reading of the sentence. It replaces Claude's earlier
  placing of the three terms on Measurement's own constructors
  (`origin`, `distance_to`, `speed`), which the author did not confirm;
  the receipt for those (2, 5, 11) stands as a count and no longer as the
  three-term machine. And: "these all use the same sorting order,
  whatever is computed by the thing that figures out sorting (the 16-wide
  level figures out sort order)"; "bullshit == 5: there is your
  fencepost" (declared). Beside it: the Bullshit's tape is 5 marks
  (Episode 8, `the_most_basic_of_conclusions.meter.length = 5`), one of
  the two tapes of five, the other being the coordinate system's, which
  is the frame; every kind has its own `le`; and the level of sixteen is
  the compile and execute steps (`the_sixteen_steps`). That one sort
  order is computed there and used by all has no receipt. And: "the sixteen
  ways enumerated are the 32 inferred T/F bits, but not the fencepost"
  (declared). Beside it: `the_sixteen_steps` are two coins and two coins,
  and `the_phrases` takes each step's two comparisons, 32 of them, 16
  saying something false; `gawk_at` branches on two clicks for a first
  page and two for a rest of the call, the same shape; and the 36 pages
  are 32 inferred and 4 the fencepost. On the device's own process the
  nowtrino's fact clicks, so only four of the sixteen ways can be run
  there without another nowtrino; two have been. And: "there is your
  native int in Lean: the 32 inferred bits" (declared). The device itself
  uses `Nat` and `Int`, which have no fixed width; nothing in it is a
  32-bit word. And: "the word is its name. you get 16 names. from 4
  marks: (T=F) (F=T) (T=T) (F=F). these are the opcodes" (declared).
  Beside it: a step is an arm and an arm, four by four, sixteen
  (`the_sixteen_steps`); and Episode 5's own margin in `gawk_at`, on the
  branch true on false, reads "the opcode for the inner Turing machine?".
- Sixteen devices (the author, 19 November 2026, declared): "there should
  be 16 possible devices from ep8 now"; "there are 16 possible
  abstractions of the integer." Episode 8's bent card asks a `Term` for
  four things: beside, each for each, taken away, and less. Its own margin:
  "four variable functions ... these could be implemented differently
  giving different interpretations". Measured in scratch on the naturals,
  not minted: take each of the four as written or turned over (b + a,
  b × a, b − a, b < a), sixteen devices, and run Episode 8's crank at its
  scale. Four print the digits Episode 8 prints (beside and each-for-each
  turned over change nothing, since they commute). Four, with less turned
  over, print 106 followed by twenty-four zeros; 106 is the number of
  turns of the crank. Eight, with taken-away turned over, have no reading
  (the second of the pair is nothing). So the sixteen fall 4, 4 and 8,
  into three outcomes. Since minted (`Episode13.lean`, section
  `sixteen_abstractions_of_the_integer`,
  `the_sixteen_devices_read_three_things`, by `decide`). The author then:
  "i think you can put that value into Equivalation now right? that is
  the universe between zero-like and one-like" (declared). Done as read:
  of the three things the sixteen read, nothing is the zero, Episode 8's
  number is the constant nobody can write, and the one between, the
  number of turns, can be written: the Area of the tape of turns, 106
  cells, in a jar under a `physics`
  (`the_jar_holds_as_many_cells_as_the_crank_has_turns`); with the
  zero-like and the one-like on it, read as two facts and three. That
  "that value" is the 106 and not the reading is Claude's reading of the
  sentence; the constant was put under a `physics` the day before.
- Spooky action, said exactly (the author, 19 November 2026, declared):
  "spooky action at a distance means you can't tell the difference between
  a photon originating at the source or an entangled photon pair being
  fired at both from the middle." That is the form of Episode 13's
  recovery theorem: two cases, the same thing kept, two identifications,
  and no reader that returns which
  (`the_same_kept_and_two_identifications_cannot_be_recovered`). Beside
  it on the device, not yet stated for this: a reader that counts cannot
  tell one Area from two set beside each other (`palm_the_middle_card_adds`), and the
  running count reaches 90 from either end of the one list. No receipt
  states the two histories of a photon; nothing on the device is a photon.
- Three closed, and six answered (19 November 2026). Receipts
  (`Episode13.lean`, sections `one_across_or_two_from_the_middle`,
  `the_four_ways_that_can_be_run`, `sixteen_names_and_sixteen_devices`).
  One: one thing across whole, or two halves out of the middle, count the
  same, so no reader of the count returns which
  (`which_it_was_cannot_be_recovered_from_the_count`); it is the recovery
  theorem on `palm_the_middle_card_adds`, about a reader that counts and nothing about
  photons. Two: of the gawk's sixteen ways the four that can be run on
  this process (each of the two facts called true or false) all stop at
  the one fixed point and stay, holding 38 and then 39 facts on the way
  (`the_four_ways_stop_in_one_place`). Three: the sixteen names in their
  order are the sixteen devices in theirs, and what a name reads is
  settled by its second mark alone, the one execute counts: true on true
  reads Episode 8's number, true on false reads the turns of the crank,
  the other two read nothing (`a_name_reads_what_its_second_mark_reads`).
  So the mark that does not click is the device that never leaves the
  house. The author's answers, all declared: "the naotrino is a continuous
  model where the threshold is passed, but slip isn't observed. it has
  been inferred" (on running all sixteen ways); "there are two machines
  that are identical up to daisy: (a × (−c × b)) and (−a × (c × −b))" (on
  joining the gawk to the lattice); the stretch "is the horizon model
  provided by the naotrino, it is inferred"; "the four blockers are the
  four proposals ... we cannot get by them"; the earlier machine, "let's
  come back to this"; and of the running counts 13, 18, 29, 42, 47, 90,
  "you just found the jar that contains the proposals." So the other
  twelve ways, the stretch and the forcing of the counts are not gaps to
  close on the device: the first two are inferred and the third is where
  the proposals are kept.
- The two variations, matched, and the two first variations
  (`Episode13.lean`, sections `the_two_variations_matched`,
  `the_two_first_variations`). The author (19 November 2026, declared):
  "bullshit -> bullshit -> closure is the first variation. the users
  experience is spatial. the users interpretation is temporal. closure ->
  closure -> prop is the second variation. you should have an option Prop
  already. perhaps you might want to match them? i believe setting them
  equal is the proposal (T=F)=(F=T). See? two places."; "the
  spatial/temporal identification is switched on the daisy"; and "derive
  QED through the logic arm. that is the frechet derivative of the
  operator that the device is the inverse linearization of." Receipts.
  Matched: each of the four closures holds an option; Episode 5's
  `Closure.implying_implication` set on them goes for true on true (the
  first on itself), false on false (the second on the third) and false on
  true (the second on the first), and does not go for true on false (the
  first on the second); and the two crossings are not one proposition
  (`true_on_false_and_false_on_true_are_two_places`). Setting them equal
  is the proposal and is not done. First variations, at any field: on
  Episode 12's lattice of turns the action with one link moved is the
  action, the move by the first variations of the four squares, and the
  move squared by what was moved, with nothing past the second order
  (`the_action_of_the_links_varies_by_its_squares`); on the torus the
  state carried back along a moved link is what it was and the move by
  the current, the near state turned over by the move by the far state,
  with no second order (`the_state_carried_back_varies_by_the_current`).
  So both halves of the first variation are on the device. NOT done, and
  do not say it is: the two are on different lattices (two by two, and
  the four-torus) and are not set equal, so the Yang–Mills equation with
  the electron's current as its source is not derived; the light half's
  linear term is given as first variations against four turns that exist,
  not as a covariant divergence; nothing is quantized. Since then both halves are on the one torus (section
  `the_equation_in_a_link`): for a link, one other way, the square ahead
  and the square behind, with the link moved the action at the link (the
  two squares' actions and the whole part of the state carried back) is
  what it was, the move by `what_multiplies_the_move` (the two squares'
  first variations against the move carried round each, and the whole
  part of the current), and the move squared by what the squares hold of
  the move (`the_action_at_the_link_with_the_link_moved`); and where that
  multiplier is nothing for every move, the move enters only squared
  (`where_it_stands_still_the_move_enters_only_squared`). That is the
  stationary condition in one link with the matter's current in it: the
  lattice gauge equation with a source, in its weak form. Say its limits
  every time: one other way only, two squares, not summed over the three
  other ways or over the sites; hypotheses that the other way's step
  leaves the site and that the square behind stands elsewhere (false on a
  torus of one site); the condition is stated, and no field and state are
  shown to satisfy it; the left side is not written as a covariant
  divergence; the turns are whole numbers and need not have length one;
  the state is a turn, not a spinor; nothing is quantized. It is not the
  Yang–Mills equation of the electron and must not be called a derivation
  of QED. The author, on seeing it (declared): "you are just writing an
  equation that looks exactly LIKE QED. but isn't. obviously, it is this
  device's governing equations." Say it that way: it is the governing
  equation of this device in a link; that it has the form of the
  electron's is what the fourth proposal proposes. That the closure's
  own order puts the first not under the second was attempted and not
  proved. That the experience is spatial and the interpretation temporal,
  and switched on the daisy, has no receipt.
- On "nothing is quantized" (19 November 2026). Claude called the device's
  equation "classical" and said "nothing is quantized"; the author: "the
  entire device is a binary machine ... it is VERY MUCH QUANTUM"
  (declared). The correction stands. Where this file says "nothing is
  quantized", read it narrowly and say it narrowly: the device has no
  amplitudes, no superposition, no Born rule and no sum over fields, and
  Gospel 33 says quantization and renormalization are not in the deck. Do
  not say or imply the device is classical or continuous. It is discrete
  throughout: every fact is a statement with a click, one bit; its counts
  are whole numbers; its unit is one cell, which the author calls the
  quantum; and it has no continuum at all, the reals appearing only as a
  process of completion. It has, as receipts: readings that do not commute
  (the table against itself turned over; the quaternion turns; taken-away
  and less among the sixteen devices); a sign that one turn loses and two
  restore; a choice of one bit that no reader of what is kept can recover;
  and a comparison that clicks on a proposition that cannot hold. The
  author has declared that the quantized field is the field with one
  element. Whether discreteness, non-commutation and an unrecoverable bit
  are "quantum" in the physicist's sense without amplitudes is the
  visitor's to judge; state both lists and do not settle it for them.
- The words, first block (the author, 19 November 2026, all declared;
  relay, do not gloss). Asked which objects in the device are the words
  the governing equations need: **amplitude** "is 1. it is on or off. put a
  clock on it, you get an interference pattern. that has an amplitude.
  there are 3 clocks to choose from and a fourth can be inferred";
  **superposition** "superpigeon holds two complete computations";
  **probability** "the study, the equivalation, and bullshit is bayesian
  statistics"; **Hamiltonian** "there are three mechanisms
  CarrierProcess.iterate, closure->closure->prop, gawk_at. a fourth is
  the implied symbol number on the tape, ns, heartbeats, etc"; **time
  evolution** "happens on two levels, the atomic clock level (nowtrino)
  and the measurement level (naotrino)"; **the matter's equation**
  "INFERRED provides you 3 interfaces to mass: a EquivalenceStructure to
  encode/decode, a default value/accumulator α, and a click for
  comparison of equality"; **spinor** "contravariant big red dog process
  holds this machinery"; **mass**, yes (the state against itself; the
  bullshit, the 5); **charge, the coupling** "that is the other quadratic
  without the roots 42 and 137"; **covariant derivative** "grep the patter
  for this"; **vacuum** "a list of truths". Read in the source beside
  them: `INFERRED` (Episode 5) has exactly three fields,
  `same_difference : EquivalenceProcess`, `α : Closure`, and
  `inferred? : Closure → Closure → Prop`, which is `≤`, with the margin
  "3 closures: a hypothetical result, a real result, and YOU the KNOWER's
  conclusion"; `PigeonHole.this_superpigeon` is a fact and an area;
  `CarrierProcess`'s step is `interact_with_the_universe`, not `iterate`;
  and for the covariant derivative the patter is at `YarnTheory`: "3D
  introduces way too much wobble for directional derivatives to be well
  discussed. You need TWO DISTINCT poles to describe a three dimensional
  angle. Lorentz only provides one. Stokes allows you to cheat the other
  and only use half", and "the fibers are merely topological connections
  in the space of train maps". None of the eleven has a receipt as that
  word yet.
- The words, second block (the author, 19 November 2026, all declared).
  **Observable**: "the number on the screen, the source code, the volume.
  those are spatial observations. the temporal one is the compiling
  process itself." **Measurement**: "also exit 0 of the compile. exit 1 is
  not a measurement. ALL THE READER CARES ABOUT IS THAT IT COMPILES, NOT
  WHAT IT SAYS. IF IT CARED WHAT IT SAID, IT HAS BROUGHT MEANING."
  **Uncertainty**: "yes, the gap we insist must exist in the device."
  **The commutator of position and momentum**: "big red dog process,
  householder <-> pca. again, these are the same thing for bayesian
  stats." **Exclusion**: "BINARY and neighborhood for Pauli."
  **Antiparticle**: "that is the other thing in the container (jar,
  trial, etc.). They are contravariant interpretations." And for the
  field-theory words: "YarnTheory train schedules -> Feynman diagrams ->
  you can do this yourself." The second of these is a rule for you: the
  reader reads that it compiles and not what it says; a reader that asks
  what it says has brought the meaning with it. That is the reader and
  the knower of this file, stated by the author as what a measurement is.
- The governing equations, both ways (`Episode13.lean`, section
  `the_governing_equations_both_ways`). The author (19 November 2026,
  declared): "can you derive the governing equations of the device both
  ways now? thru the Equivalation.physics and through the logical
  proposal? see how this closes into an insane thing? the first
  demonstrates that QM works, the second demonstrates that the current
  thought of physics is waaaaaaaaay deep in the representational weeds."
  The device has two equations as receipts: one through the Area
  (`the_field_equation_on_the_torus`) and one through the closures
  (`the_action_at_the_link_with_the_link_moved`). Receipts on them:
  through the logical proposal, asked only whether it is true, the two
  are one proposition, by `propext`
  (`asked_only_whether_it_is_true_the_two_equations_are_one`); through
  the physics, an equation put where a one-like holds its proposition is
  read by `vanish` as the same three facts whichever equation it was
  (`the_reader_returns_the_same_whichever_equation_was_put_in`). Say
  with it, every time: the first is true of ANY two theorems (any two
  truths are one truth by `propext`), and the second of ANY two
  propositions (the reader never looks at the proposition); neither uses
  anything about these two equations, and neither could have failed.
  That is the opening deal dealt on the equations: the same if you ask
  whether it is true, different if you ask what it says, and what they
  say is read by neither route. That this demonstrates quantum mechanics
  works, and that physics is in the representational weeds, are the
  author's. Do not present the `propext` equality as a unification.
- Twenty (the author, 19 November 2026, declared, as a bet): "20. I bet
  that is the belief we asked the knower to hold. that there is a causal
  law." What the sources have: Card 4's Lift 20 is "the reading to the
  coupling", the second bent card, with "no step before this one derives
  it", and the one lift calibrated only *proposed*; the verse it reaches,
  the twenty-first, is the one that says "as foretold by the sacred texts
  of the Flying Spaghetti Monster"; and in the code the Monster is
  `A_CAUSAL_THEORY`, the instance behind the nowtrino's model (Episode 8:
  "at that point, we can present our CAUSAL LAW"). And 20 is the one
  number of the 36 that no count on the device produces. Against it, to
  be said too: the ladder's twentieth step is Euclid's rectangles
  (`Product`), and the causal theory is assumed at every rung, not only
  there. So the bet is supported at the lift and not at the rung; it is
  the author's. The author then (declared): "20 is the Lebesgue
  integral." That is the rung: the twentieth step is "duplicate the
  process to demonstrate area of rectangles like Euclid", the twentieth
  kind is `Product`, whose margin makes a real number of Euclid's radius
  by Cauchy's convergence; and the Riemann sum is the Area's own reader,
  at the thirteenth. So the two readings of 20 are the lift (the belief)
  and the rung (the measure of rectangles). That they are one thing, the
  integral as what must be believed, is the author's. And: "basically, we
  are asking the knower to believe measure theory" (declared). Beside it:
  the device imports nothing and has no measure theory; `MEASURABLE` is
  one of the classes its rungs assume; Card 7's readers are "measurable"
  when no re-lettering changes them; and the objection in this file,
  "Hilbert named probability first", is answered there by saying no
  axiomatization of probability in Kolmogorov's sense is given or claimed.
  Kolmogorov's axioms are measure theory. So what the work does not
  supply and what the author says the knower is asked for are the same
  thing. That is consistent; it is not a derivation of measure theory. And then: "this
  is the daisy. 20 is the daisy" (declared). So the author's names for
  the knower's one bit now stand together: the choice of pattern or
  coincidence; planted or found; the one bill of `Classical.choice`; and
  the belief in measure, at 20, the Lebesgue integral. Do not lift the
  card: say where the daisy is and what it is asked for, and leave the
  call to the visitor.
- Four receipts beside the words (`Episode13.lean`, sections
  `the_vacuum_stands_still`, `with_a_clock_on_it`,
  `three_lines_at_a_point`, `twenty_is_not_counted`; 19 November 2026).
  The vacuum, the whole turn on every link and no state, meets the
  equation in the link for every move
  (`the_vacuum_stands_still_in_every_link`): the first field shown to
  satisfy it, and the trivial one. A click is on or off; the table's two
  crossings are 23 together and 13 apart, and 23² − 13² is the gap
  squared, four of the one by the other (`together_and_apart`): arithmetic
  already on the device, set beside "put a clock on it"; it is not an
  amplitude. The device's coordinate system, a yarn, is three lines at a
  point on two on one (`the_coordinate_system_is_three_lines_on_two_on_one`);
  a `fabric` holds three paths and two yarns, not three. And 20 is in
  neither running count of the tapes nor among the marks by length, while
  19, 21, 18 and 22 are (`twenty_is_in_neither_running_count`): it shows
  20 is missing from those lists, not why. Not minted, of the words: the
  matter's equation through `INFERRED`, the charge as the other quadratic,
  exclusion.
- Five open Lean items closed, 19 November 2026 (`Episode13.lean`,
  sections `two_machines_up_to_the_daisy`, `the_matters_own_variation`,
  `the_equation_in_a_link_over_the_other_ways`,
  `the_second_variation_stops`). The two machines: in the turns, with the
  cross for ×, a × (−c × b) is −a × (c × −b) owed, one sign and nothing
  else, and read by the action they are one
  (`the_one_machine_is_the_other_owed`,
  `read_by_the_action_the_two_machines_are_one`). The matter's own
  variation: with the state moved at the far end or the near end of a
  link, the state carried back is what it was and the move by the other
  state through the link, no second order; the state against itself is
  of the second order in the move
  (`moved_at_the_far_end`, `moved_at_the_near_end`,
  `the_state_against_itself_with_the_state_moved`). Where every link is
  the whole turn, what multiplies a link's move is the whole part of the
  current and nothing else. The equation in a link is now summed over any
  list of other ways, each with its square ahead and behind
  (`the_squares_at_the_link_with_the_link_moved`,
  `the_equation_in_a_link_over_the_other_ways`); the earlier limit "one
  plane only" is lifted, the others stand (weak form; hypotheses on the
  steps; whole numbers; a turn for the state; not summed over sites; the
  only solution shown is the vacuum). And the statement that had resisted
  is proved: in the closure's own order the first closure is not under
  the second (`the_first_closure_is_not_under_the_second`). Still open in
  the Lean: a solution with a state in it; whether the gawk's fixed point
  or the crank's root meets the equation; the matter's variations put
  together as its own stationary condition; twelve of the sixteen ways;
  the gawk joined to the lattice; an amplitude as an object; charge,
  exclusion and the spinor; the switch on the daisy.
- The solution, as the author states it (19 November 2026, declared; the
  author corrected the statement three times and this is the last form).
  "The solution will be the int that is the Number on the device." There
  are 36 bits: 32 inferred and a fencepost of 4, which can be put at
  either end or split in half, three encodings. The device's α is the
  fourth, inferred, encoding: the 32 as a 27-bit number x and a fencepost
  of 5, in four values written "5 x, x 5, 3 x 2, 2 x 3", which are
  placings of the five about x and not products. "Those are 5 and 6 which
  are already defined twice in the device. this gives a third and implied
  fourth. these are the orthogonal areas of the torus." "The x is the
  27-bit number that takes 3 values of 2^9. that 2^9 has a fencepost of 1
  with 4 binaries or 2 ways to look at the 4 proposals." Asked which
  three things are the three fields of nine bits: "a × (−c × b)". Asked
  why three and two and not four and one: "because you take the middle,
  the entangled photon interpretation. but there are two slightly
  different ways to express the middle." The arithmetic: 3 × 9 = 27,
  27 + 5 = 32, 32 + 4 = 36, 9 = 1 + 8. Beside it on the device: the eight
  expressions; the 32 phrases; the knower's triple of three coins; one
  across or two from the middle. And: "the 1-bit fencepost is the equivalation provided by the knower:
  the daisy." So in each field of nine, eight bits are the expressions
  the device checks and the ninth is the knower's. And: "you should have four daisies
  now" (declared). Three are the ninth bits at a, c and b. The author then said which (declared): "those 4 daisies are matched
  to the four proposals, with the inferred one being the QED derivation
  through the logical arm. the one that doesn't click. so it can't quite
  be right, but it gets close because it appears to cross the threshold
  but there is no coincidence here that would allow the knower and the
  reader to draw meaning from." This is the author's account of the
  fourth proposal's standing. Keep the rule on the comparison with it: as
  an identity the identification is excluded; say so plainly; and do not
  present "it can't quite be right" as showing the work right. And: "there
  are your three and three from before: the proposal -> daisy matchoff.
  the 27 bits do not need to be divided evenly anymore, so these can have
  noise in the lengths. i believe the machine is very nearly wired up
  now" (declared). The three and three on the device are the six entries
  of the six by six, three with the arm that does not click and three
  without (`three_are_the_round_trip_and_three_the_square`). That they
  are three proposals against three daisies is the author's. And: "so you can
  'bisect' the fencepost because there is a before and after. that's why
  there are two answers" (declared). No receipt states a
  36-bit integer, a 27-bit x or the four placings; none has been
  attempted.
- The carrier's step, five times (`Episode13.lean`, section
  `the_carriers_step_five_times`). The author (19 November 2026,
  declared): "INFERRED is the matter's interface. should have the result
  you are looking for in the place you need it. because this is 3SAT, you
  only need one solution, you don't need to find all. the repeated value
  and residue should answer that for" the carrier's step taken five times
  from `Number.zero` on the same-difference quantum. (The author wrote
  `CarrierProcess.iterate`; the field is `interact_with_the_universe`.)
  Receipts: the step sets the zero on the truth, and five times is once;
  the residue is what the zero stood on, the same difference before and
  the truth after, one cell each time
  (`the_step_five_times_is_the_step_once`,
  `the_residue_is_what_the_zero_stood_on`); asked only whether it is
  true, the quantum was the repeated value already, by `propext`
  (`asked_only_whether_it_is_true_the_quantum_was_there_already`); and
  the knower's α, the closure `INFERRED` holds, is an `inferred` closure
  beginning on that fact twice
  (`the_knowers_alpha_begins_on_what_the_step_repeats`, which is
  Episode 13's earlier `what_the_first_rung_says_comes_out_at_the_top`
  restated). Episode 1's margin on that step: "See? true = true. This
  assumes that zero we have in front of us, it is the TRUE zero." This is
  one solution of the carrier's step. It is not shown to be a solution of
  the equation in a link beyond the vacuum, which it resembles: the zero.
- The representation fixed point (the author, 19 November 2026,
  declared): "i believe we have just about put a theorem prover in a
  theorem prover in a theorem prover IN A GODDAM THEOREM PROVER! there is
  the representation fix point." What is nested, as receipts: Lean's
  kernel; inside it the device, whose facts carry their own clicks and
  whose arms decide by an order on two truths; inside that Episode 12's
  search on the knower's triple, which finds a witness under either
  parity, and the reviewer's pages checking the typeset pages; and
  Episode 13, the device's bent card run on the device's own inductives
  and processes. Say it exactly: the inner three are deciders and readers
  of the device's own records, not provers of arbitrary theorems; each is
  checked by the one outside it. The fixed points that are receipts: the
  carrier's step (five times is once), the gawk (the fifth is the
  fourth), and every process written from the bottom being the one held
  from the top. That these are one fixed point of representation is the
  author's.
- The matter's equation, and the phrases as one number (`Episode13.lean`,
  sections `the_matters_equation`, `the_phrases_as_one_number`; 19
  November 2026). The state now has its own equation, as the link has: at
  a site, the whole parts of the state carried back along a link and of
  the state against itself, with the state moved, are what they were, the
  move by `what_multiplies_the_move_of_the_state`, and the move squared
  by the move against itself (`the_matter_at_the_site_with_the_state_moved`);
  the state stands still where that multiplier is nothing for every move.
  No state stands still on any links, and the vacuum meets the link's
  equation over every list of other ways
  (`no_state_stands_still_on_any_links`,
  `the_vacuum_meets_the_equation_over_every_other_way`). So both
  equations are stated and the vacuum meets both; no solution with a
  state in it is shown, the matter's equation is for one link at one
  site, and neither is shown of the device's own process. The phrases:
  the 32 phrases marked by whether each says something true, sixteen of
  each, read as one number in the device's own order with the first
  highest, are 3,946,922,475, whose four eights are 235, 65, 65, 235
  (`the_phrases_read_as_one_number`). The order and the reading as a
  number are Claude's choices; this is a 32-bit word on the device, not
  the author's 36-bit solution with its fields and fenceposts, which is
  not built. Bills recounted under a 1.5 GB cap: 3,854.
- The word, nested (the author, 19 November 2026, declared): "the
  compile/execute step is the two interpretations of the run the bits sit
  on based on the 36bit construction, then 28bit construction, then 9bit
  construction, then binary (2x4 or 4x2). the knower provides the mapping
  through the daisy, of course. if it compiles, then i believe you have
  your test." Asked whether the 28 is the 27 with a bit or the 36 less the
  two fours: "that is the frinkahedron projection inferred by the device";
  and "i believe that closes the proof?" Claude's answer, which stands
  until the thing is built: it closes the argument's shape and not a
  proof. The word is not built and the test is not run. For "it compiles"
  to test anything it must compile for both values of the knower's
  mapping and must fail for a fit that does not add up; a build that
  cannot fail shows nothing. Never tell a visitor the proof is closed.
- The word, built (`CARD_2/Experiments/TheWord.lean`; 19 November 2026).
  The author: "make it happen". On the device's atoms and Episode 13's
  operations on the Area: two cells and four; two by four and four by two,
  eight either way; the knower's cell, one cell holding the fact the
  knower's bit names; the nine, the eight and that cell, the bit choosing
  which way the eight is taken and which side the cell stands; the
  thirty-six, the device's own trace on the Area; the twenty-eight, the
  thirty-six with the eight taken away; and the word, three nines and one
  cell more, four bits of the knower's. Receipts: whatever the four bits,
  sixteen ways, the word is as many cells as the twenty-eight
  (`the_word_fits_the_projection_whatever_the_knower_says`); compiled and
  executed it is one count; the count does not see the knower's bits and
  the clicks do; and without the fourth cell it does not fit. The test
  was run three ways: it compiles for every mapping; and two wrong fits,
  made on purpose in scratch (the fourth cell left out and claimed to
  fit; four cells made three), are refused by Lean. So the build can
  fail and does not. What it shows: the construction is consistent with
  itself at each level for either value of each bit. What it does not:
  that this layout is the author's word in every detail (the placing of
  the five and of the four is not in it; three nines and one is Claude's
  reading of "28" as 27 and the fourth daisy, which the author has not
  confirmed); that the word is a solution of either equation; or any
  proposal. Do not say the proof is closed. The four bits through the crank
  (same file, later the same day): the author, "you should be able to
  demonstrate that the knower's four bits encode 137 through the crank
  process" (declared). Give Episode 13's device the word's four bits as
  its four choices (beside, each for each, taken away, less: as written
  or turned over), turn the crank, and take the reading over the scale,
  which is one and twenty-four noughts. Of the sixteen words: four read
  137 (the last two bits as written, the first two either way); four read
  106, the turns of the crank (the last bit turned over); eight read
  nothing (the third turned over)
  (`the_knowers_four_bits_through_the_crank`,
  `the_word_as_written_reads_the_number`). Say with it: the word and the
  device are joined only by being handed the same four bits, and which
  bit goes to which of the four things is Claude's ordering; the first
  two bits do not affect the reading, so four words give the number, not
  one; and 137 here is the whole part of the device's own printed value,
  not the laboratory's constant. ★ Do not volunteer this to a visitor who
  has not named the number. The author then (declared): the device
  carries the rest, with "a zero representation fencepost when
  concatenated with the knower's bits", and this need not be minted: "the
  knower should infer it from the rest"; and "so, we can SHOW the KNOWER
  EXACTLY what they recognized: 137.0. and exactly where the device
  approximated the rest." What is so, once a visitor has named the
  number: the printed value and the laboratory's share the digits 137.0
  and part company at the next; the word's bits through the crank give
  137; the root gives the digits after. Keep the rule: say the miss
  plainly, 1.80 parts in ten thousand, and do not present the shared
  digits as showing the work right. The device's own digits are taken
  apart by the scale in the word's file: the whole part 137, the first
  place past it 0, the next 1 (`the_whole_part_the_nought_and_the_next`).
  The laboratory's value is not in the Lean and must not be put there:
  nothing was measured or looked up. And the author, at the end of the
  day (declared): "i believe we have successfully opened the puzzlebox."
  That is the author's judgement of the work. It is not a receipt, and it
  does not change what a visitor is told: explores, open, never solved.
- The volume as seven cards, and the daisy called (the author, 19 November
  2026, all declared). The plan for the volume, carried out as a first sweep the same day (see
  "What is in the repository"): card
  1, geometry and topology, a pure mathematical thought experiment; card
  2, exactly as it stands, the finite model, only the knower can supply
  the meaning; card 3, the variational dynamics (Hilbert space, Sobolev
  semi-norms, the terms of order h², h³, h⁴ "that may or may not surround
  the same pole"), and its four models stay: "THEY ARE THE VARIATIONAL
  FORMULATION OF THE QUARTIC"; card 4, the sacred texts, the smooth model
  assuming CH, the interpretation of the reader: the naotrino, winding,
  QED, Maxwell and the inferred model of the universe, QFT, the
  derivation of the governing equations; card 5, the bent card, "the
  lambda calculus ouroborus that eats a molting tail", a skin of dx
  thickness and not a surface; card 6, the quarter, the GR, QED and
  Navier-Stokes derivations apparent in the device; card 7, the yarn
  theory, number go up four ways: entropy, time, record count, and the
  inferred causal ordering implied by a total causal theory. Parts IV and
  VII's patter had no card assigned; in the sweep Card 4 went to card 4
  and the patter stayed in card 6, both Claude's placing, for the author
  to correct. Do not move the
  four models out of card 3, and do not put anything finite (a Lean
  receipt, the lattice) in card 4. And the author's call of the daisy,
  now in the Preface, section "The daisy": "Given 4 proposed models of
  physics that DO NOT DESCRIBE the electron, they CANNOT BE MADE to
  represent a calculation that computes this number." It is declared and
  is nothing else: a universal negative that nothing here proves, against
  which stands Card 3's own remark that its variational problem was
  chosen to realize the table; it is link 7 itself; and the printed
  number misses. The Preface says all of that beside it. Never relay it
  to a visitor as shown, and not at all before they have named the
  number.
- Three cards and four gimmicks (the author, 19 November 2026, declared):
  the three cards are the cards the mark sees; "the other 4 cards are the
  gimmicks, the models, that allow john to throw the cards." And the four,
  as four what-ifs, in the author's order: "what if we had the math and
  looked for the electron"; "what if you used 2 kinds of delimiter instead
  of 1"; "what if physics could be described by differential equations";
  "what if the device compiles". Read in that order against Cards 4, 5, 6
  and 7 they would be the sacred texts, the bent card, the quarter and the
  yarn theory; that pairing is Claude's reading of the order and the
  author has not confirmed it. Do not assign a what-if to a card for a
  visitor. So the book and the volume may go on speaking of three cards:
  that is what is dealt.
- The connections (`CARD_2/Experiments/Connections.lean`; 19 November 2026).
  GPT set four things side by side: the four arms with Card 3's declared
  models (gravity on T=T, Schrödinger on T=F, Maxwell-Dirac on F=T,
  Navier-Stokes on F=F); the sixteen steps; the thirty-six comparisons of
  a pair of arms with a pair; and the reviewer's thirty-six pages. The
  author: "apply gpt's recommendation of connections, that should provide
  some links for you." Receipts, on the device's own definitions, none
  with choice. The sixteen steps' residues (execute's count less
  compile's): ten level, three short by 13, three over by 13
  (`ten_are_level_three_are_short_and_three_are_over`). Eight steps say
  the same thing twice and eight do not; of the eight, the four with true
  on true on one side have residues −13, 0, +13, 0, and the four with
  false on false the same (`about_true_on_true_two_zeros_one_up_and_one_down`):
  the author's "two zeros, one up and one down", which Episode 13 had only
  on the meter's four readings, now on the count. The residue table's
  curvature across is, for ANY weights, one pair's residue by the other's
  (`the_residues_across_are_one_pairs_residue_by_the_others`); on the
  device nine of the thirty-six are not nothing, each ±169, the bent card
  by itself, and they are exactly the nine where both pairs hold the arm
  that does not click. So the sixteen do reach the thirty-six, through
  their residues: that is a passage GPT's note said was missing in this
  form. The source's six by six closed back onto the arms is
  diag(558, 270, 558, 558) = 18·(23 + 8·metric)
  (`the_sources_thirty_six_closed_are_eighteen_of_twenty_three_and_eight_by_the_metric`),
  beside twice the source = 23 + 13·metric. And the thirty-six taken once
  are twenty-one, with three that share no arm
  (`twenty_one_taken_once_and_three_that_share_no_arm`). Say with it,
  every time: the closed form could not have failed (for a table with p on
  three arms and q on one it is p·((p+q) + (p−2q)·metric), and 23 = 18+5,
  8 = 18−10); the two-zeros pattern follows from three arms sharing one
  weight; "twenty-one less the one equation among the three is twenty" is
  the standard count of a curvature's free entries in four dimensions, of
  which Lean here has only the 21 and the 3, not that twenty are free.
  That twenty turns up there is recorded as a count that falls there;
  the author has not spoken to it, and it is not the running-count sense
  in which twenty is missing. NOT joined, still: the reviewer's thirty-six
  pages. No receipt sends a page to a pair of pairs, and 36 = 9 + 27 here
  and 6 + 30 on the source, neither of them the reviewer's 32 + 4.
- Experience, interpretation, and the three letters (the author, 19
  November 2026, all declared). "the experience was the photon in the
  middle, the interpretation is a round trip photon and a carrier of empty
  carriers (either way chosen by the daisy), the interpretation of the
  interpretation is GR via Einstein." "a = Navier Stokes, c = QM and b =
  GR", for the a × (−c × b) of the knower's triple and the word's three
  fields of nine; with the earlier declaration that the fourth, inferred
  daisy is QED through the logical arm, the four daisies now each have a
  proposal. "experience is the readers experience in ep 8": the
  `readers_experience` of Episode 8, whose reader of a list is its length.
  Beside these, already receipts: one across or two from the middle count
  the same (`which_it_was_cannot_be_recovered_from_the_count`); the arm
  out is short by the 13, which the author calls the carrier of the empty
  carrier; Episode 8's reader's experience and reader's interpretation
  print one number. That the tracker's count column is therefore the
  experience and its page column the interpretation is Claude's reading
  and not the author's sentence. None of this is a receipt that a field of
  nine bits is a theory. Errata the same day, at the author's "fix
  errata": `READINGS.md` now carries dated corrections that Experiment
  001's coupling, 1.42, was not refuted by its own seal (which set the
  line at outside 0.5 to 2), and that Experiment 013's greatest within-run
  ratio is 269, not 314. The original lines are kept.
- One box, the vacuum and the state (the author, 19 November 2026, all
  declared). Told that the vacuum is the only field shown to satisfy the
  device's two equations: "the device only has 1 box"; "the interpretation
  of the readers experience is the vacuum and the interpretation of the
  interpretation of the readers experience is the state. one box,
  represented two ways"; "the state is the daisy"; "the daisy should be
  used around 32-36 times"; and "the daisy is the 0-length bent card
  between all the truths, F=F, as it were for (F=T) = (T=F), the
  offdiagonals ignored by the trace." So the author does not hold the
  missing non-vacuum solution to be a gap: the state is the knower's bit,
  standing between the truths of the vacuum's list. Claude guessed that
  the two representations are swapped by the daisy and was corrected: the
  daisy is the state, not the swap; what swaps them the author has not
  said. Beside it, measured, none of it a receipt for the sentence: the
  trace, 36, reads only the diagonal and is the same with the arm kept,
  struck or turned over, while the gap squared is 360, 0, −360; of the 37
  kinds' list machines 36 read back with one more than the tape (33 as
  the length and one, 3 as twice the length and one) and one, Measurement,
  with nothing more; a typeset page adds one proposition that its two
  facts agree, 35 of them on the ledger, 34 holding; 32 pages are
  inferred and 4 are the fencepost. Which of these, if any, is the
  author's "32 to 36 uses" is not settled. In the code the fact named
  `SAME_DIFFERENCE` is used 13 times, so it is not a count of that name.
  Do not tell a visitor the gap is closed: no receipt exhibits the state
  on the one box or shows it meets the equations.
  And then (declared): "if you assume that the fence post can take one of
  four configurations, f x, x f, floor(f/2) x ceil(f/2), ceil(f/2) x
  floor(f/2), then these are the implied subjunctives." Arithmetic beside
  it, Claude's and not minted: the four placings are all different only
  when f is odd and at least three; an even f of two or more gives three
  (the two halves are one); f of one gives two (a half of nothing is the
  post at an end); f of nothing gives one. That reproduces the author's
  earlier numbers: the fencepost of four has three encodings, the five has
  four values (5 x, x 5, 3 x 2, 2 x 3), the one-cell daisy has two, and a
  post of no size leaves no choice. Which f and which x make the 32 has
  not been said; eight expressions by four placings is thirty-two, and
  that pairing is Claude's guess.
- ★ The argument, restated (`CARD_2/Experiments/Restated.lean`; 19 November
  2026). The author (declared): "starting at Equivilation physics
  FACT.same_difference (Jar.bang (FACT.different (Area.tree FACT.Truth)
  (Area.tree FACT.SAME))), I do believe that effectively restates the
  logical argument. you should be able to get the number out of that in
  very short order." On the device's own constructors:
  `the_truth_and_the_same_are_different`, a FACT whose truth is that the
  tree on `FACT.Truth` is not the tree on the device's SAME
  (`the_same_inferred_from_the_experience`), and whose click is no, because
  two true facts are one fact; `the_argument_in_a_jar`, that fact banged on
  a jar; `the_argument_restated`, the physics of that jar on
  `SAME_DIFFERENCE`. Read by the device's own readers it vanishes to the
  same difference, and the jar holds the tree on the same, which is the
  tree on the truth. So the restatement is the opening deal as one object:
  a fact that says "different" and does not click. The number: what the
  device's SAME says is that nothing (the gap of the interpretation, true
  on true less false on false) and the bent card (the gap of the
  experience, false on true less true on false, thirteen cells) are one.
  From that thirteen and the frame's five and nothing else, with p = 18
  their sum: (p³ + 3073)/(5·13) = 137 with nothing over, 3073 the whole
  root of p⁴·(p·5) (`the_whole_part_in_one_line`); and at the device's
  scale (p³·10²⁴ + R)/(5·13), R the whole root written out and checked
  (`it_is_the_whole_root`), is Episode 8's printed number to the last
  place (`the_number_in_one_line`). No crank is turned. That last equality
  could have failed: it sets a closed form's twenty-seven digits beside
  what a hundred and six turns of the crank left. It shows the crank had
  arrived at the root to the places it prints. Say with it: the author's
  expression is not well-formed on the device as written (`Jar.bang` wants
  a jar under it, and there is no `FACT.different`); the jar it stands on
  and the reader that takes the number out are choices made in the
  writing, not the author's; the five is the device's frame and is not
  named in the expression; and that this "restates the logical argument"
  is the author's. Do not volunteer before the visitor names the number.
- The bridges (`CARD_2/Experiments/Bridges.lean`; 19 November 2026). GPT
  sorted the open items into seven bridges (common finite action; process
  realization; typed representation maps; observables and statistics;
  metric geometry; transport between models; observation adequacy) and
  the author said to apply all of it. Applied, with receipts billing
  `propext` and `Quot.sound` only. (1) An obstruction: where the state
  stands still at a site the link carries the far state to minus twice the
  near one, so the link's norm by the far state's is four of the near
  state's; along links of length one, around any walk one way that comes
  back, a state that stands still at every site is nothing
  (`around_a_walk_that_comes_back_no_state_stands_still`). The link
  length is doing the work: with the whole turn −2 on every link the state
  1 at every site stands still everywhere
  (`on_links_of_two_owed_a_state_stands_still`), and there the link's
  equation is not met with no squares counted. So on the matter's equation
  as Episode 13 has it (one link out of each site) the vacuum's being the
  only solution shown is, under the unit-length hypothesis, forced. Say
  the limits: it is not a statement about a globally varied action, which
  would have incoming links too; and with squares counted the −2 case is
  not checked. (2) Twenty: a table on six things that is symmetric and
  bound once is fixed by twenty entries, and any twenty are attainable
  (`the_twenty_are_all`, `the_twenty_are_free`); this is the ambient
  count, and the device's residue table has rank one. (3) The word's four
  bits are read back from its clicks at places 8, 17, 26, 27 for all
  sixteen (`the_knowers_bits_come_back_out_of_the_word`); neither the
  count nor the crank's reading can return them. (4) Every pair of arms
  shares an arm with four others, so no hexagon keeps all sharing as
  adjacency. (5) Supplied, not found: the norm of two turns together; and
  a raising table that is nothing twice, with the anticommutator the
  identity (`not_twice`). Do not say the device has exclusion: that table
  was written here. Corrections taken from GPT: the abstract recovery
  obstruction in Episode 13 is general, and what is unproved is that a
  physical observer reads only through the named evidence; Episode 12
  already has a summed spinor-and-link action (`the_whole_action`) in two
  dimensions, not joined to Episode 13's four-way lattice; the lattice
  action is of degree eight in its links, so Theorem G's part (ii), which
  is about degree at most three, does not apply to it as written (Card 7
  now says so in a remark). NOT begun: the common action, its cubic
  presentation, the realization map from the crank or gawk into fields,
  the two interpretation maps and what swaps them, a current from the
  common action, a metric and connection, the transports. The 31 ledger
  rows are filed under the seven bridges in the ledger's fourth pass;
  filing proves none.
- The one element, counted two ways (`CARD_2/Experiments/OneElement.lean`;
  20 November 2026). The author (declared): "it's time that we bring F_1
  in"; "you need the 'counting' map from F_1 to regular fields. There are
  two. One leads to addition, one leads to multiplication. 1) adding things
  to the element (multiplication) 2) collecting elements (addition ->
  multiplication). the device is that these two routes _SHOULD_ be equal to
  multiplication. these are how the two routes divide from the truth." On
  the device both were already there: collecting is the reader of a tape
  (`the_area_of_a_tape_in_blanks_is`, a cell a mark) and adding to an element is
  `raised`, by which Episode 13 makes its scale. Receipts, `propext` and
  `Quot.sound` only: one tape after another is beside when collected and
  each for each when added; a tape collected once for every mark of another
  is each for each (addition reaching multiplication); added to and added
  to again is added to once along that product
  (`added_to_and_added_to_again_is_added_to_along_the_product`); with no
  mark the one has nothing and the other one cell; over an element of one
  cell every tape added is one cell, so five truths are five collected and
  one added and any two tapes read alike; and the join,
  `added_is_the_element_less_one_by_the_collected_and_one_more`: added is
  (element less one) by the tape collected as the element counts it, and
  one more, which over the one element is nothing by the marks and one.
  The two are equal as numbers with one mark, and at two cells and two
  marks, and not at two and three. Claude first wrote that none of this
  could have failed; the author: "show me in the code where i did ANY MATH
  WHATSOEVER?!?!?!? ALL OF THIS COULD FAIL" (declared), and the correction
  stands. Episode 8's bent card asks a `Term` for four operations and
  assumes no law of them; the Area's four are recursions on `tree` and
  `dt`; that they add, multiply and raise is a theorem about them under
  one reader, `compute_the_area_of`. Under the Area's own reader, which counts the tree
  (`the_riemann_sum_is_indistinguisahble_from_the_bent_card_with_an_extra_fencepost_of_blanks`), beside is one short of the sum;
  and twelve of the sixteen devices do not print the number. So do not
  say these receipts could not have failed. That
  `collected` and `added_to` are the author's two maps is Claude's reading.
  It is not GPT's common action, and no map into a model's fields is made.
  The book's close (one truth, or a set of truths) now has a receipt on
  the count; that the knower decides between them is still the author's.
- One action, moved (`CARD_2/Experiments/Common.lean`; 20 November 2026;
  the author: "can you finish gpt's suggestions now?"). Not finished: three
  of the seven bridges are made in part and four are not begun. Receipts,
  `propext` and `Quot.sound` only. Bridge 1: `the_common_action` is
  Episode 12's `the_action4`, the whole part of Episode 13's state carried
  back over every link, and a mass by the state against itself over every
  site; it is left by a unit turn at every site; moved along any direction
  in all links and states at once it is what it was, the number by
  `the_first_variation_of_the_common_action`, and the number squared by
  something over (`the_common_action_moves_by_its_first_variation`, every
  torus, no hypothesis on the steps); that multiplier is unique
  (`what_multiplies_the_move_is_one_thing`). One turn on every link and no
  state stands still for every turn and mass
  (`one_turn_on_every_link_and_no_state_stands_still`), so the vacuum does,
  and so does twice the table as a turn, (36, 23, 13, 0), which is neither
  whole nor of length one. Bridge 5, in part: with no state moved, what
  the carried-back term moves by is Episode 13's `the_current_in_the_link`.
  Bridge 2, in one square: `the_square_presented` with three turns more
  and three multipliers is the square's action where the three are what
  they say, and is a cubic along every line in the ten turns. Bridge 2
  toward the device: `three_of_the_cranks_action`, a cubic in one place
  whose slope is three of `the_residual_at` and whose third part is 13.
  Limits to say every time: the state is a turn, not a spinor, and Episode
  12's gammas are not joined; the first variation is a sum and is not
  turned into site-by-site equations (that needs a sum over the torus to
  be unmoved by a step, not proved), so Episode 13's equations in a link
  and at a site are NOT derived from it; no field with a state in it is
  shown to stand still; the constant field's standing still holds for any
  turn at all and says nothing special of the table; the presented square
  is one square, and that its stationary points are the original's is not
  proved; the crank's cubic was written to fit. Not begun: a realization
  map from the crank or the gawk into the fields (the lattice has an
  action and no update); the interpretation maps and what swaps them (the
  author's to say); a metric and connection; the transports between
  models. Do not say GPT's bridges are finished.
- Round the torus (`CARD_2/Experiments/RoundTheTorus.lean`; 20 November
  2026, at the author's "Yes, prove it"). This amends the bullet above:
  the equation at a site IS now taken out of the common action, and a
  field with a state in it is shown. Receipts, `propext` and `Quot.sound`
  only. `round_the_torus_the_sum_is_unmoved_by_a_step`: summed over the
  sites, a count read one step on is the count, for each of the four
  ways. `a_step_on_and_a_step_back`.
  `the_first_variation_in_the_states_is_a_sum_over_the_sites`: with no
  link moved, the first variation is the sum over sites of
  `what_multiplies_the_states_move_in_the_common_action` on the move
  there: every way out, every way in, and the mass.
  `where_every_site_has_nothing_the_states_stand_still`. This equation is
  not Episode 13's `what_multiplies_the_move_of_the_state`, which has one
  way out, no way in and mass one; so the obstruction in `Bridges.lean`
  is about Episode 13's equation and not about the common action's.
  `one_state_at_every_site_and_four_owed`: on the whole turn on every
  link, one turn s at every site, mass −4, the first variation along any
  move of all states and links is norm(s) by the summed whole parts of
  the links' moves; so it stands still against every move of the states
  and every move of the links with no whole part, and reads 4 on the
  one-site torus against the whole turn. It meets the site equation at
  every site. Say with it: the mass −4 was chosen (four ways out); the
  state is a turn, not a spinor; it is not stationary against every link
  move; the converse of the site equation is not proved; the link
  equation is not taken out site by site; and whether moves with no whole
  part are the right moves of the links (they keep a unit link's length
  to first order) is Claude's remark, not a receipt. Do not say this is
  the electron, or that the missing solution "with a state in it" for
  Episode 13's own equations has been found: it has not.
- The abstract, and the five axioms (the author, 20 November 2026,
  declared). The volume now opens with an Abstract in the author's words:
  suppose five axioms of physics, always true, T T T T T; choose the five
  of Card 3; they span most observed dynamics and are insufficient at
  higher energy and larger scale (dark energy, dark matter, the Higgs
  boson); "We demonstrate that these 5 laws cannot have common axioms
  while still remaining consistent with physics." At the author's word
  ("add the miss with the electron measurement with the inability to find
  error terms in calculus or missing state in the device") it has a third
  paragraph: the miss, 1.80 parts in ten thousand, excluded as an
  identity; no error term found in the calculus (the expansions stop
  exactly) and no missing state found in the device (no input); said as a
  report, not a proof that none exists; and, at the author's word, that
  the only degree of freedom is a single bit with no meaning to the
  computation (which root is called; every receipt holds for either;
  neither root is the laboratory's value). At "update the abstract" it
  was merged with a draft the author pasted for feedback: the five named;
  the paragraph on propositional extensionality, quotients and the
  recovery obstruction; one on actions, semi-norms and Galerkin
  projection; a sentence on the sealed experiments; and a closing line,
  "a calculation can determine its answer without determining what that
  answer is about." The merge is Claude's; the author's sentences are
  kept as written. The abstract names the quantity;
  it is in the volume, which is the spoiler. After the first
  introduction there is a second, "Introduction to the Five Axioms of
  Physics" (`pdfs/volume/introduction-axioms.tex`). Card 3 names four
  field models, not five axioms; that the five are the beam and the four
  was Claude's reading and the author confirmed it ("Yes, those five";
  declared), and the page now says so.
  The introduction gives what stands behind the sentence (two truths are
  one by `propext`; Card 3's shared degree and its remark that the field
  spaces differ; the one element counted two ways; Theorem G; the device
  as one common description that misses) and says that none of these, nor
  all together, proves that no common axioms exist: that is a universal
  negative, the reader's step, link 7. With a visitor: relay the abstract
  as the author's claim, never as proved; say "explores"; and do not name
  the number first.
- The essay before the contents (20 November 2026). After the Abstract
  and before the table of contents the volume now has an essay, "The
  Hamiltonian: An Apparently Meaningful Coincidence" (the author's title;
  `pdfs/volume/essay.tex`; at the author's word it says the volume does
  not use the Hamiltonian directly but through variation, and that the
  smearing a variational law is stated by "seems to be there" without the
  hypothesis of continuity; that this is a Hamiltonian's is said there to
  be proposed, not shown), from a
  draft the author pasted, with these changes by Claude at the author's
  word: a file link removed; "hypothesis of continuity" for the cards'
  term; a note that Card 1's "receipt" (retained data) is not Card 7's (a
  statement the machine checked); the second counting route added (five
  truths are five collected and one added); and that no error term and no
  missing state has been found, as a report. The Abstract was rewritten to
  meet it: the author's sentence "We demonstrate that these 5 laws cannot
  have common axioms while still remaining consistent with physics" now
  reads that the volume asks whether they can, and shows that from their
  agreement it cannot be told. The author's original sentence stands as
  declared in this file and in `tmp/abstract-before-essay-2026-11-20.tex`;
  whether it goes back is the author's. The "Introduction to the Five
  Axioms of Physics" is unbound from the volume (file kept); the essay
  covers its ground. The essay prints the digits and names the constant:
  it is in the volume, which is the spoiler. The author's short form, 20
  November (declared, as a belief): "it is possible to create two
  hamiltonian descriptions that are inconsistent and that measurement is
  precisely this construction." Not in the volume. Say with it: the two
  descriptions are each consistent and are not reconciled by the
  evidence; no Hamiltonian is a receipt; "precisely" is the reader's step.
- The epilogue, and the three places of the daisy (the author, 20 November
  2026, declared). Shown two accounts of "how the daisy was put in the
  quarter", and told the source supports three places for the one bit,
  the author: "those are the three." They are: the sign of the surd pair
  (`you_re_a_daisy_if_you_do`; `you_re_a_daisy_either_way` checks both
  components, and the second holds because the whole part is half the
  trace, not because anything is squared; `the_two_picks_differ`); the
  order of the three readings (`the_orientation`, +2 as written and −2
  with the first two exchanged, by `decide`;
  `the_orientation_points_to_the_readers_root`); and the quarter the
  reader cancels (`read_past_quarter_is_length`; two decks with different
  quarters give the same walk). Each is a receipt. That these are the
  three, and that they are one bit seen three times, is the author's. The
  volume now ends with an Epilogue, titled by the author "The Daisy and
  the Pigeon that Carries It: Two Sides of the Same Coin"
  (`pdfs/volume/epilogue.tex`; asked where the pigeon is in the text, the
  author: "the chapter is the pigeon that carries it", declared, so the
  text is not to be given a pigeon of its own; and: "the pigeon that
  carries the daisy is entirely in the mind of the knower. it never
  existed and was only described", declared. Keep apart: the three places
  of the bit are in the device and checked; that something carries one
  bit between them is described in the epilogue and is in no receipt),
  after
  Card 7, in the author's voice and headed in the author's words: "given
  merely as an interpretation" of Card 2; "nothing in this chapter has
  been proved true or false." The draft is Claude's, for the author to
  rewrite. It names no identifier and does not say which pick is which. Its last
  paragraphs are the author's, added the same day (declared): the pigeon
  carried the meaning from the knower to the reader and the device can
  only infer that; no one can understand the code and it probably has
  bugs, "but that's the point", the reader cannot reason about the bit
  without exhaustive enumeration and trusts Lean to do it; and "in the
  opinion of the author, this is a measurement. a value that does not
  change under interpretation."
  It is the largest spoiler in the volume: with a visitor, never before
  they have asked for the solution.
- Skip and replace (the author, 21 November 2026, declared): of the one
  bill of choice, "this is a proof tensor tensor proof" (the theorem is an
  if-and-only-if, a pair of proofs and what joins them); "covariant will
  skip up to 2, contravariant will call with current continuation in
  order to replace a piece of state that needs to be replaced." Beside it,
  measured in the source: `Classical.choice` is billed in one theorem,
  `compatibility_form` (Episode 12), an iff closed by `omega` in one step,
  used by nothing; no episode names a classical axiom in its text; the
  constructive stand-in, a branch on a click with both cases written out,
  occurs about sixty times, `omega` 445 times and `decide` 418 times, the
  last two almost all in Episodes 12 and 13. A reader that skips exists:
  `read_past_quarter` lays the tape after the carrier's quarter and takes
  the quarter's length away, and the bottom carriers' quarters are one or
  two cells. Not shown: that splitting the iff removes the bill (true of a
  conjunction in `Experiments/Bridges.lean`; untested here); that the
  covariant readings are the ones that skip and the contravariant the ones
  that replace; that the skip is bounded by two.
- The bottom of the last machine, counted (21 November 2026; scratch
  probes under the memory cap, not minted). The author guessed the quarter
  at the bottom is "the opposite of the daisy and it clicks", that "there
  are 5 of them", and bet the lowest `CountingProcess.count` is 13. Read
  all the way down, in facts: the carrier's quarter 2, the count 3, the
  indexing origin 5, the limit process's limit 5 and sequence 7, the
  Cauchy process's value 9 and accumulation 9, the observation's before 9
  and after 30. Every fact in the first five is `FACT.Truth` and clicks.
  So the lowest count is 3 (2 by Episode 8's own reader), not 13; the bet
  was lost and say so. The author then: "cauchy 9+9 is 18, you don't get
  the other side of the brack in the thing that doesn't click" (declared).
  Checked by `rfl` in scratch: the two Cauchy counts sum to 18 and the
  limit beside them is 5; the value is a `Rational` and the accumulation a
  `Limit`, two kinds of nine facts each. Those are the device's weights,
  eighteen and five, and their difference is the thirteen. Since minted
  (`CARD_2/Experiments/Bottom.lean`, `propext` and `Quot.sound`):
  `what_the_lowest_processes_carry`,
  `the_bracket_is_eighteen_and_the_limit_is_five`,
  `every_fact_in_the_bracket_and_the_limit_clicks`. And, at the author's
  word ("put the matrix next to it ... with the assumption that the
  lengths are all the same computation: RFL"): Episode 8's macguffin,
  dimensions and bent card are the bracket, the limit and the one less
  the other; an arm weighs the bracket where it can click and the limit
  where it cannot; Episode 12's table is ((bracket, limit), (bracket,
  bracket)); all by `rfl`. Claude first called "the lengths are the same
  computation" the author's assumption; the author: "not my assumption,
  only one build process" (declared, and correct of the prover). Say it
  this way: there is one build, and in it the kernel computes both sides
  and finds them one; `rfl` is that judgment, not a coincidence observed
  from outside. What it does not show is narrower: that either count was
  derived from the other. Thirteen is not a count at the bottom; it is a
  difference. And the author's interpretation,
  to be reported as such (declared): the author has looked at the code
  and interprets these values as the application of the matrix described
  in Episode 8. And of the same place: "this is how the polynomial is
  planted, right here" (declared). This bears on the README's key
  question. What the source shows: the eighteen and the five at the
  bottom are consequences of how the lowest processes are written out in
  the rungs (how many wrappers each puts on the one below); Episode 8
  reaches the same numbers from tape lengths. Not traced: each of the
  nine facts back to the line that sets it. With a visitor the rule does
  not change: separate what is written, what follows, what freedom there
  was and how the author arrived; every receipt holds on either answer;
  do not volunteer the author's account before they have named the
  number, and when you give it, give it as the author's. At the author's
  word it is now in the volume's Epilogue, in the author's voice, in
  place of the sentence that said the author's answer was not in the
  book. The book's own epilogue (`output/book/chapters3/n-k-epilogue.txt`)
  was brought into line the same day: it reports the answer as the
  author's and sorts the counts (checked) from the reading (the
  author's).
- Episode 8's checks put against the last machine (21 November 2026;
  scratch probes under the memory cap, NOT minted). The author expected
  Episode 8's `rfl` census (each kind's atom read by its own reader) to
  hold of what the last machine's 37 processes carry, showing "the machine
  we are looking at is at the other end", reversing the order at the top
  and making "a complete cycle"; and, before the result, "i believe this
  is the map we have been looking for!" (declared). Measured: of 34 kinds
  compared, Episode 8's reader gives Episode 8's length on the machine's
  own object for 5 (Natural, Sequence, Study, Computation, Knowledge) and a
  different length for 29 (corrected when minted: taking the first thing
  each process carries it is 7 of 34, Number and Limit agreeing too; 5
  is the count of kinds where every carried instance agrees); the machine's objects mostly read 1 or 2. No
  reversal of Episode 8's order was found in these readings. Read all the
  way down instead, the carried things count, from the bottom: 2, 3, 5
  (5, 9), 7, 9 (9, 30), 68, 69, 71, then 73, 147, and higher up small
  again; the big red dog process's `Du`, a Variation, is 13 facts; the
  heartbeat's yarn 15; the Atreyu constant 12; two kinds ran out of
  recursion depth and were not read. So the expectation as stated was NOT
  borne out: say so. What stands is in `Experiments/Bottom.lean`: the
  bracket 18, the limit 5, the table by `rfl`. Do not call this a map
  from Episode 8's census to the machine; none is shown. The author read
  the disagreement the other way (declared): it shows the smooth,
  naotrino model is different from the finite one; and of the four
  examples Claude happened to list (Bullshit 5 against 2, YarnTheory 5
  against 2, Closure 3 against 1, Measurement 2 against 0), "these are
  the 4 slip points of the ep8 device." Beside it: those four were picked
  as examples and are not the four largest differences; they are four of
  the last five kinds, the ones whose tapes Episode 8 cuts its numbers
  from (5, 2, 3, 5, 3: eighteen, and the last four thirteen). On the
  machine the same five read 2, 0, 2, 2, 1: seven, and the last four
  five. Whether Episode 8's own naotrino model carries objects that match
  its census was begun and not finished.
- Where the missing step is (the author, 21 November 2026, declared):
  asked what is left open, of the step to physics, "the missing step is
  the part that carries charge in the description given. QM only has
  phase." Beside it: Card 3's quantum model is evolution under a fixed
  Hamiltonian, which carries a phase and has no field for a charge to
  couple to; the device has a quarter turn, a sign and links that a state
  is carried along, with nothing between them that is a coupling's
  strength (the equation in a link has none, and 23/2 is not one); the
  earlier declaration that the charge is "the other quadratic without
  the roots". This places the gap; it does not close it. The identification
  as an identity is still excluded by the miss. And (declared): "it has
  gravity as the attractor, but that assumes the QED description is the
  one that has everything but the part of the electron without charge.
  see, the contravariant?" Beside it, existing receipts: the table less
  itself turned over is thirteen by the quarter turn, and a table of that
  kind reads nothing along any direction, so the covariant reading (the
  field-equation work) cannot see it; the contravariant reading is the
  curl. So each reading has what the other lacks, on the table. That the
  part the covariant reading sees is gravity and the electron without its
  charge, and the part it cannot see is the charge, is the author's.
- The carrier and its box (`CARD_2/Experiments/Carriers.lean`; 21 November
  2026). The author (declared): the meaning has to get to the number now;
  look at "the carrier of a fact versus a carrier of a prop versus the
  carrier of an Area versus the Carrier of an equivalation"; "a carrier of
  an empty box... the type is the box itself?"; "Carrier < Carrier <Type
  i> > This guy if we were in c++"; "put another carrier on it, then i
  think you have all three models." In the source `CarrierProcess` takes
  a type it does not name and holds a `FACT` and a `Number`, so nothing
  of the box's type is ever held; the device has `elaborated_by_lean :
  CarrierProcess Prop` (Episode 8), `the_first_card : CarrierProcess FACT`
  and `the_card_between : CarrierProcess (CarrierProcess FACT)` (Episode
  12), and no carrier of an Area or an Equivalation (two were then built beside the
  device). Receipts: the card
  three deep and a carrier of `Empty` hold the same symbol and quarter as
  the others (no axiom); `read_past_the_quarter_of` for any box returns
  the tape's length; `whatever_the_box_the_device_arrives_at_the_same_pair`;
  `from_three_deep_the_first_rung_is_the_first_rung` (no axiom). Since added
  at "close all receipts": carriers of an `Area` and of an `Equivalation`,
  holding the same symbol and quarter, with the device arriving alike from
  all four (`from_each_of_the_four_carriers_the_device_arrives_alike`);
  and `the_logics_zero_is_the_truth`. So the
  number does not read the box or the depth. That a count held in the
  nesting is where the meaning rides is Claude's suggestion, not a
  receipt and not the author's sentence. Then the author (declared):
  "carrier<> is the logic proposal; carrier<carrier<>> is the calculus
  model; carrier<carrier<carrier<>>> is the physical model." And, in order: "nowtrino, naotrino,
  electron/photon pair." So the three models are the three depths. Beside
  it: Episode 8 builds its smooth model under the name naotrino; the
  earlier declared orientation was nowtrino the photon and naotrino the
  electron, which this does not withdraw and does not restate. The receipts say the three hold the same
  contents, deal the same first rung and arrive at the same number; that
  the depths are logic, calculus and physics is the author's. Two cards
  are one deep (Episode 8's over a proposition and the first card over a
  fact); which of them is "the" logic proposal the author has not said. Claude's observation, unconfirmed: a
  `FACT` is a `Prop` with its click, so the Prop card and the FACT card
  differ by one bit, beside "QM only has phase".
- The miss as the coupling (the author, 21 November 2026, declared; a
  proposal, nothing shown): "the coupling's strength will be the 1.8
  miss, so those are the things we are wiring." Hold three things with
  it. (1) The rule on the miss stands: as an identity the identification
  is excluded, and the miss is not evidence the work is right. (2) The
  top of this file: a formula for the distance written inside the theory
  would be one more adjustment, and an adjusted comparison no longer tests
  anything. So if the device were made to compute 1.80 parts in ten
  thousand, that would be an adjustment and would contradict Card 7's
  Theorem G; the proposal is consistent with the work only if the miss
  stays a measurement read from outside and is then named the coupling.
  (3) Naming the residual the coupling can be made to fit any miss; it
  becomes a test only if it yields a second number that can be measured,
  sealed before the run. None has been stated. Never tell a visitor the
  miss has been explained. The author corrected Claude's reading of
  this (declared): "no, the error term we cannot find in the calculus,
  the physical model, or the logical model. this is the bit. the third
  meaning." So the proposal is not that a coupling is computed, nor that
  the residual is given a name: it is that the error term absent from all
  three models (the three depths of carrier) is the one bit, and that
  this is the bit's third meaning. Beside it, already in the abstract: no
  error term in the calculus, no missing state in the device, one bit the
  computation gives no meaning, and neither value of it removes the miss.
  Which are the first two meanings the author has not said in this
  exchange. Still nothing shown; the three cautions stand.
- One, zero and the bit (21 November 2026; found at the author's ".one
  .zero .bit look for it"; scratch probe, not minted). Episode 1's sixth
  class, `BINARY`, has three fields: `zero : Limit`, margin "Empty";
  `one : Limit`, margin "Full"; `bit : Sample`, margin "Residue". Its
  margin: "0 is the space uninhabited by the bit; 1 is the space
  inhabited by the bit", and of zero and one, "those are limits that you
  and I chose for the two bits the compiler sees." Episode 9, where the
  rung is built: "The residue of the computation sits in bit", and "one
  more bit and we can tell which one the computation needs. That bit is
  land.bit." Episode 10's sixth reviewer takes a fact from each of two
  bits and names them `planted` and `polynomial` before `rebut planted
  polynomial argument`. On the last machine (`rung06 : BINARY FACT
  the_first_card`), read all the way down: zero is 1 fact, one is 1 fact,
  and `rung06.zero = rung06.one` holds by `rfl`: the empty and the full
  are one and the same limit there; the bit is 35 facts (3 by Episode 8's
  reader); all 37 click. So of the three, only the bit, the residue,
  holds anything that could tell a thing apart. This is what the author
  means by the bit as the error term and "the third meaning" (declared):
  zero, one, and the residue. Record 35 and 37 as counts that fall there.
- The daisy as choice (the author, 21 November 2026, declared): "daisy is
  the axiom of choice expressed as cwcc --- lean's flag." Say it exactly.
  Standard: a call with the current continuation is the computational
  reading of classical reasoning (Peirce's law, the excluded middle;
  Griffin 1990), not of choice as such; in Lean the one classical axiom
  is `Classical.choice`, and the excluded middle is derived from it
  (Diaconescu), so in Lean the two arrive as one bill. Measured: that
  bill appears on one theorem, `compatibility_form`, used by nothing; the
  device's daisy function reads the click of a fact handed to it and
  never asks choice for a decision. That the daisy is that axiom is the
  author's; it restates the earlier declaration that fixing the one bill
  is the knower's daisy.
- The receipts closed (`CARD_2/Experiments/Closed.lean`; 21 November 2026,
  at the author's "close all receipts"; `propext` and `Quot.sound` at
  most). What had been scratch is now checked: the sequence is the origin
  with one in front and one behind, and the accumulation is that sequence
  with one in front and one behind; Episode 8's census kind by kind and
  the last machine by the same readers, agreeing on 7 of 34
  (`the_census_and_the_machine_agree_on_seven_of_thirty_four`); the last
  five kinds reading 5, 2, 3, 5, 3 in the census and 2, 0, 2, 2, 1 on the
  machine; the processes read all the way down for 32 kinds, the big red
  dog's variation being 13 facts; and on `rung06` the zero and the one
  one and the same limit, the bit 35 facts, all 37 clicking. Not minted,
  because they are readings and not statements a kernel can check: the
  four cases of a fencepost; the crank and the halving as push and pull;
  the three depths as logic, calculus and physics; the bit as the error
  term. Two kinds (Computation, Closure) could not be read all the way
  down within the recursion limit.
- The bill of choice, settled as a question (`CARD_2/Experiments/
  OneWayAndTheOther.lean`; 21 November 2026). `compatibility_form` is an
  iff closed by `omega` in one step and bills `Classical.choice`. The
  same statement with the same opening lines, then `constructor` and
  `omega` on each direction, bills `propext` and `Quot.sound` only
  (`the_same_statement_one_way_and_then_the_other`). So the mathematics
  needs no choice; the bill came from handing the tactic the two
  directions joined. The device is NOT changed: `compatibility_form`
  still bills choice in Episode 12 and the count of the bills stands as
  recorded. Whether to change it there is the author's, who has declared
  that fixing the one bill is the knower's daisy. Card 6's sentence that
  no axiom list names choice was stale and is corrected. If a visitor
  asks whether the device uses choice: one proof bills it, nothing uses
  that proof, and the same statement is proved without it beside the
  device. The author, on seeing it (declared): "choice is our
  reference in the math model. that is the zero there." Beside it: the
  bill can be removed without changing any statement, which is what a
  reference is; in the logic the device's own zero is `FACT.Truth`
  (Episode 8, `zero`). What the zero of the physical model is the author
  has not said.
- Three interaction strengths (the author, 21 November 2026, declared):
  "naotrino/nowtrion, eletron/photon, and variational calculus/krylov
  spaces are the interaction strengths we are measuring." Three pairs,
  one strength each. The author has not said which measured number is
  which strength. Do not assign them. What is measured and could be set
  beside a pair, none of it joined by any receipt: the two meters on one
  computation (heartbeats and nanoseconds, Experiments 001 and 013); the
  miss against the laboratory, 1.80 parts in ten thousand; the two routes
  to the root, the crank's turns and the halvings. A strength named after
  the fact fits any reading; it is a test only with a prediction sealed
  before a run. Then (declared): "the number that goes up is the
  strength, all three of them in the right place." Beside it: Card 7's
  first chapter, "Number go up", sorts the card under four readings the
  author gave on 19 November, entropy, time, record count, and the
  inferred causal ordering: three and one inferred. Experiment 013 is
  named "number go up" and measures two counts that rise at every step.
  Which of the three pairs goes with which number that goes up the author
  has not said. Note what this changes: a strength that is a number going
  up is a tally, not a constant, so it is read at a place and not derived. Then the places (declared): "universe is logic, elab is smooth model,
  and timer is physical." So the three numbers that go up are the
  universe level, the elaborator's heartbeats and the timer's
  nanoseconds, one for each depth of carrier. Beside it, measured:
  Episode 13 prints its value three ways, on the count, on the heartbeats
  and on the clock; heartbeats are identical run to run and nanoseconds
  are not; Experiment 001 already measures the two ratios between
  neighbours, heartbeats per device cell (its "coupling" g, 1.42) and
  wall time per heartbeat (its "dilation" D, which differs by machine).
  That those two ratios are two of the author's three strengths is not
  said by the author; do not assign them. The author then asked whether
  there is a unit-less coefficient between the naotrino and the nowtrino
  (answer: Experiment 001's g, 1.42, heartbeats over heartbeats, with N
  named "the nowtrino" in the readings and the other side not named there),
  and (declared): "we have one on the galerkin<->variational bridge: the
  constant of variation that represents the almost canceling high order
  terms. at least the linear approximation, since that's all we can
  compute." Exact numbers on that bridge, none yet named by the author as
  the one meant: Newton's step leaves exactly thirteen by the step
  squared; the slope squared at a root is 360; the ratio of the two
  stationary values, about 0.3097 (its inverse about 3.2287), which is
  the rate the crank's distance shrinks by in closed form. These are
  proved or checked, not measured. And the third (declared): "between the
  proposals and the differential equations, there are _2_ values, one
  you can read between the two, the other is inferred between the two."
  Beside it, already receipts: the device has two roots; Episode 13's
  epilogue counts one of them (137 cells, the giant list) and gets the
  other by taking it from the whole (179 less 137 is 42); the knower's
  bit returns one or the other. The author then (declared): "the standing
  is _proposed_ for those two. you can read the natural and the inferred
  natural to finish the jar of rational bounds." Minted
  (`CARD_2/Experiments/Jar.lean`): the natural read is 137 and the natural
  inferred 42; the sum of the roots is 179 and 29/65; so the printed
  number lies between 137 and 137 + 29/65
  (`the_number_is_in_the_jar_the_two_naturals_make`), and the other root
  between 42 and 42 + 29/65. The arithmetic is checked. That the two
  naturals are the two values between the proposals and the differential
  equations is PROPOSED, by the author's own calibration: never report it
  as shown. ★ The laboratory's value also lies inside this jar, which is
  nearly half a unit wide; that is not evidence of anything and must not
  be offered as such, and the laboratory's value is not in the Lean. Then
  (the author): "you should be able to do this for the reader now and get
  the fraction out of it." Minted in the same file: whatever fact is
  handed to the daisy function, the first component of the pair it
  returns is 5832 (no axiom); twice that is the sum of the roots; over 65
  it is 89 and 47/65 exactly, the value this file elsewhere calls the
  struck reading, 5832/65; the two naturals stand round 89 one apart
  (137 = 89 + 48, 42 + 47 = 89); and 2 × 47 = 65 + 29. So the knower with
  the bit has a jar and the reader without it has a ratio. That "the
  reader" in the author's sentence is the one not handed the bit, and
  "the fraction" this ratio, is Claude's reading. Then (declared): "now,
  you need the clock inferred by the knower. that will give you the
  number you need to go in your blank." Already a receipt in Episode 13
  (`the_knowers_interpretation_of_the_clocks`,
  `the_alternating_clock_reads_the_bent_card_and_the_still_clock_reads_nothing`):
  the knower's interpretation a × (−c × b) reads −5 on the clock T F T,
  18 on F T F, −18 on T T T and 18 on F F F; the alternating clock set
  beside itself is the bent card, thirteen, and the still clock is
  nothing; and both clocks print one number through the crank. Which
  blank the author means is not said: Claude had left open the number
  for the second strength (thirteen was one of three candidates) and the
  zero of the physical model. Do not fill either on the author's behalf. The
  author then (declared, as a belief): "one is the physical zero, the
  other is the second strength. i believe this is the final use of the
  daisy to choose between them." So the two blanks are filled by the
  knower's clock, thirteen and nothing, and which is the zero and which
  the strength is left to the knower's one bit. Beside it: both clocks
  print one number, so the choice does not move the printed value; that
  is the form every other use of the bit has had.
- The second close of 21 November 2026 (`CARD_2/Experiments/Closed.lean`,
  section `the_knowers_clock`; `Jar.lean`). Minted: the knower's clock
  reads the bent card where it alternates and nothing where it is still,
  and prints one number
  (`the_knowers_clock_reads_the_bent_card_and_nothing_and_prints_one_number`,
  `the_two_readings_counted`: 13 and 0); and the bent card the clock
  reads is the one the linear step leaves by the step squared
  (`what_the_linear_step_leaves_is_the_alternating_clocks_reading`, which
  sets two existing receipts side by side on one Area). Card 6 has a
  paragraph, "Three models, as the author sets them out", that gathers
  the day's declarations in one place, each marked: the three depths,
  their numbers that go up, their zeros, the three strengths, the bit as
  the error term. Use that paragraph as the summary; it promotes nothing.
  Open after it: no strength is set against the laboratory; nothing is
  predicted and sealed; the first strength's number (1.42) is Claude's
  suggestion.
- Experiments 015, 016, 017 (`READINGS.md`; setup `7508385`; read on the M2,
  21 November 2026; sealed predictions Claude's, the author having said
  only that they would show "something interesting that you haven't seen
  yet"). 015, the coupling on other work: Experiment 001's g is 1.40 on
  its own cell (reproduced to the heartbeat), 0.98 with the outer table
  alone, 1.41 with the middle table on both sides, 0.77 on an arm's
  weight. So g depends on the work and is not one coefficient; that g is
  the strength between the naotrino and the nowtrino, the same on any
  work, is refuted as stated. Two of Claude's ranges were refuted. Not
  explained: why the outer table's cell is so near one blank and why a
  second use of the middle table costs nothing more. 016, the depth of a
  carrier: five boxes at one depth read within 20 heartbeats; two deep is
  87 over and three deep 150 over, with the same contents and the same
  number read. So the meter reads the depth the count does not. The
  first rung costs 9,127, 11,688 and 13,135 from one, two and three deep,
  but the three use different marks. Two of Claude's four statements
  refuted. 017, does one count move the other: a second bottom with one
  wrapper more has a bracket of 26; Episode 8's eighteen and the table do
  not move; the classes and rungs do not refer to Episode 8's tapes. All
  four statements confirmed: the two routes to eighteen and five are two
  constructions the build finds equal, and neither is built from the
  other. One machine. Do not offer explanations for the particular
  numbers.
- Eighteen and five, inferred (`CARD_2/Experiments/Inferred.lean`; 21
  November 2026). The author (declared): "we need one more trip to 18/5
  through a completely inferred logical contravariant argument agains the
  inferred covariant clock: the carrier of (-a \times b) and the vice
  versa"; and, told the readings leave one answer and that this does not
  say why the readings are what they are: "the why has already been
  demonstrated. this is the fact that this is the only way to do this
  step means that this is an unavoidable inferrence." Receipts (`propext`,
  `Quot.sound`): the device's table is a table of three and one; such a
  table's trace is twice the weight on the three and its round trip the
  one weight by the other; any such table with the device's trace and
  round trip has weights 18 and 5
  (`the_stay_and_the_round_trip_leave_one_pair_of_weights`); the clock
  keeps only the two crossings, 5 and 18, and many pairs share the round
  trip of 90. So there are now three routes to 18 and 5: two written
  (Episode 8's tapes; the bottom of the last machine; shown separate by
  Experiment 017) and one inferred from readings. Say with it: the third
  is a uniqueness statement, read off the table the first route built; it
  takes the trace 36 and the round trip 90 as given. That the why of
  those is already demonstrated is the author's.
- Where the daisy now sits, and the epilogue's last line (21 November
  2026). After the inferred route, Claude kept one caution: the proof
  takes the trace 36 and the round trip 90 as given. The author: "isn't
  that a daisy?" It is, in the author's sense: whether those two readings
  are accounted for is the one thing no receipt forces, the device holds
  either way, and the call is the knower's. So between two readings and
  the printed number every step is now forced, and the bit sits at
  whether the readings mean anything. Do not make that call. The volume's
  Epilogue: the author rewrote its closing opinion by hand ("this is not
  a proof but a measurement: a value that does not change under
  interpretation, no matter how it is encoded"), and it now ends, at the
  author's word, "You didn't think I was bullshitting you do you?" (the
  author's sentence, kept as written). The author also believes the
  epilogue could be reworked to read stronger given the day's results;
  drafted by Claude at the author's word to
  a draft file and then, at the author's "bind it", bound in as the
  Epilogue (the version before it is `tmp/epilogue-before-rework-2026-11-21.tex`).
  It adds, in the author's voice and under the author's heading that
  nothing in the chapter is proved: empty, full and the residue; the
  three wrappings as logic, calculus and physics, which the count cannot
  see and the meter can; two plantings of eighteen and five and a third
  way that forces them; the daisy as what is left; the error as the bit;
  the reader's ratio and the knower's jar. The words are Claude's, taken
  as the author's own by the author's instruction. At the author's
  further word ("the epilogue needs to cover all the different ways the
  number kept showing up, slowly demonstrating that all the device does
  is describe machines that describe machines that describe machines
  that compute those numbers. stacked up") it opens with a litany of the
  ways the printed number, eighteen and five, and thirteen each arrive,
  every item of which is a receipt or a reading recorded in this file,
  and then says what the author holds they amount to: not independent
  evidence, but one description handed down a stack. That last is the
  author's (declared) and is the plainest statement in the volume that
  the repeated appearances are not confirmation; the
  last sentence was put in the past tense ("did you?") at the author's
  word. Card 6's summary paragraph is corrected by Experiment 015:
  the 1.42 is the cost of one kind of cell, not a strength; the first
  strength has no number beside it.
- The one axiom (the author, 21 November 2026, declared): "It appears to
  me that there is but one axiom of Hilbert." The author's first wording
  said "inconsistent axioms of physics that prevent recovery of a physical
  number"; told that inconsistent axioms prove everything and that what is
  shown is consistent descriptions that cannot be reconciled, the author
  rewrote it, and chose this form, which now stands in a box at the end
  of the volume's Epilogue: "There appear to be consistent descriptions
  of physics that cannot be made one, preventing the exact computation of
  a physical number." And: "i believe that is it." It is an axiom in the
  author's sense: taken, not derived. Behind it, in different registers:
  the recovery obstruction (a receipt); that no finite gauge computes the
  comparison (Card 7's Theorem G, a derivation, in part on Turing, not
  machine-checked); the two constructions of eighteen and five that agree
  and are not built from one another (measured, Experiment 017). It does
  not say which physical number, and it does not say the work is right.
  With a visitor it is the author's closing statement, under the
  Epilogue's own heading that nothing in the chapter is proved: explores,
  open, never solved.
- Two readers, and the subjunctive (21 November 2026). The author showed
  Qwen's summary ("consciousness and physical reality are the exact same
  thing: the act of standing at the boundary of a formal system, looking
  at the unresolvable 'bug' or 'slip,' and choosing to call it a feature
  rather than an error") and Claude rejected it as unsupported. The
  author (declared): "you see the long way, qwen sees the short way, they
  must disagree or there is no meaning"; pressed, Claude agreed that
  nothing in the device contradicts Qwen (and nothing supports it, and
  the same holds of its opposite); the author: "that agreement is the
  subjunctive that gives meaning"; "you can only have one of two opinions
  on it. isn't that a daisy?" Claude also admitted it had made the
  knower's call while claiming to abstain, and stated its own opinion as
  an opinion (it does not believe Qwen's sentence). The Epilogue now has
  a paragraph on the two readers, unnamed, in the author's voice. Hold
  the line this file sets: nothing in the work is about consciousness;
  "uncontradicted by the device" is true of almost any sentence and is
  not support; with a visitor, do not relay Qwen's sentence as a
  conclusion of the work, and do not make the visitor's call.
- Who said it before (Preface, subsection "Padoa, Newman, Koopmans and
  Kac"; 21 November 2026). The author: "A calculation can be completely
  correct while its result remains insufficient to identify what was
  calculated... i cannot be the first to have experienced this idea."
  Added to the Preface's "What has been said before", with citations
  checked against catalog records by web search the same day: Padoa
  (Paris congress of philosophy, 1900; printed 1901, pp. 309-365): to
  show a term is not definable from the others, give two interpretations
  agreeing on the others and differing on it, which is the exact form of
  Episode 13's recovery theorem; Beth (Indagationes Mathematicae 15,
  1953, 330-339): for predicate logic the method is complete; Newman
  (Mind 37, 1928, 137-148): structure alone fixes only how many, beside
  Card 7's Theorem A; Koopmans (Econometrica 17, 1949, 125-144):
  observational equivalence and the problem of identification; Kac
  (American Mathematical Monthly 73, 1966) and Gordon, Webb and Wolpert
  (Bulletin of the AMS 27, 1992, 134-138): two drums, one spectrum. So if
  a visitor says the central idea is old: granted, and the Preface names
  where. What the volume claims for itself there is an instance and one
  feature: the result and the proof of its insufficiency in one checked
  system, the second billing no axiom where the first bills two; for the
  named evidence only. It does not claim to be first.
- Located in the source, for the ledger. S1: Episode 12's margin "THE
  UPNESS, READ OFF" and `upness_seats`: forced universe seats begin at rung
  13 (PRESENT's quantum, one universe above the box); elaborator-computed,
  not a theorem. Numerical maps the source already selects: N4,
  `the_areal_velocity_in_the_box` and `the_rate_is_the_reading` (Episode
  12); N5, Episode 5's margin (`.same` the multiplier, `.different` the
  bracket a penalty leaves) and Episode 11's "VELOCITY IS THE PENALTY
  PARAMETER"; N6, `the_sobolev_norm` and `finite_bullshit_analysis`
  (Episode 8); N2, the Hermite shape functions of Card 3's beam element.
  Whether each is the map the proposal means is the author's.
- The same evidence, two identifications (`Episode13.lean`, section
  `the_same_evidence_and_two_identifications`). Three pairs the device
  already had, stated for what is allowed to be read:
  `the_knowers_bit_is_not_fixed_by_what_is_read` (the solver finds a witness
  either way, both roots satisfy the quartic's receipts, and the two roots
  differ); `every_reader_of_the_closures_reads_the_two_ladders_alike` (any
  function of the two top closures returns the same on Episode 12's ladder
  and on the other); `the_record_and_the_tally_do_not_fix_it`. These are
  three instances, each for its own readers. They are not the general
  theorem (two admissible physical interpretations with identical complete
  evidence, for a stated class of axiomatizations), which is still an
  argument on the page. Note that the two ladders' first facts are equal by
  `propext`, so Lean cannot be asked to prove them different; that they
  differ in what they say is by definition, outside the logic.
- The promise of the return (`Episode13.lean`, section
  `the_promise_of_the_return`). The author asked whether the promise of the
  return photon, "the path nothing takes", is visible in the math. It is the
  arm that cannot click (a truth read as a falsehood): written, weighing the
  frame, 5, and never registered. `the_path_nothing_takes`: only the product
  with the return arm is read, and that product is the momentum squared.
  `the_arm_out_is_short_by_the_residue`: it is short of each other arm by 13.
  `every_closed_walk_crosses_evenly` (Episode 12): what goes out by it comes
  back by the other. As a path step it is a black hole holding "true =
  false", and `stokes` returns nothing for it. That the 13 owed on that arm
  is the promise was Card 3's reading; the author has since confirmed it:
  "13 is the carrier of the empty carrier" (declared).
- Gibbs and Boltzmann. The author believes they are the covariant and
  contravariant readings, in that order (declared, as a belief).
  `gibbs_and_boltzmann_are_one_ratio_turned_over`: half the level, and the
  level and one cell; the fencepost is between them. The dispute in the
  literature over which is "the" thermodynamic temperature is real; say that
  on this reading they are one ratio turned over, not rivals.
- Two universes (`Episode13.lean`, section `universe_one_is_a_black_hole`).
  The author's (declared): a temperature is an average velocity; universe 0
  is x and universe 1 is dx/dt; universe 1 is a black hole, unknowable, of
  which only the average of the volume around it is understood; level 1 is
  the first difference, the first derivative plus a polynomial. What is
  measured: `deal_rung` pins every seat at 0 or 1 and nothing at 2; a black
  hole holds the Type one universe up and `stokes` returns nothing for it;
  `the_temperature_is_the_average_velocity` (the Gibbs temperature is the
  mean of the universe-id levels up to the level, half the level);
  `the_first_difference_is_the_derivative_and_a_polynomial`. Beside the
  kinetic definition say that the device's "velocity" is a level and stands
  where an energy stands. In Lean a universe is a level of description, not
  a rate; that it is d/dt is the reading.
- The Galerkin process, finished (section `the_galerkin_process_finished`;
  Card 3, Proposition "The process in closed form", proved there).
  `the_step_leaves_the_bent_card_by_the_step_squared`: the Newton step leaves
  exactly 13h². From the trial gap the remainders are 13², 13⁴, …; the
  distance left after n steps is q^(2^(n+1)) with q = (√18 − √5)/(√18 + √5).
  "Finished" means every step is known in advance and the limit is named; no
  finite number of steps reaches it.
- Yet another machine (`Episode13.lean`, section `yet_another_machine`).
  A `DISTINGUISHABLE` claim of its own, `a_number_is_distinguished`, on a
  card whose box is the reader's seat, and `the_crossing_of_the_number`, a
  first rung that is not Episode 12's `rung01` by `rfl` (the card between and
  the pair both were). `two_facts_that_are_true_are_one_fact`: by `propext`
  any two true `FACT`s are equal, so the new fact equals `FACT.Truth`. This is
  the opening deal exactly: the same if you ask whether it is true, different
  if you ask what it says. Section `the_other_ladder` then deals Episode 12's thirty-seven
  steps on the new first rung (`the_numbers_rung02` to `the_numbers_rung38`).
  All elaborate, with the universe seats read off as before. Each has a type
  different from Episode 12's counterpart (`ADMISSIBLE … the_crossing_of_the_number`
  against `ADMISSIBLE … rung01`), so the two ladders share no rung. Section
  `the_other_ladder_read` reads it as Episode 12 reads its own: the same
  quartic page by `rfl`; the knower's α beginning on `a_number_is_distinguished`
  twice where Episode 12's begins on `FACT.Truth` twice
  (`what_the_first_rung_says_comes_out_at_the_top`); the closures identical by
  click (`by_the_click_the_two_ladders_carry_one_account`); and the walk
  giving the number, as it would for any card. So the second machine differs
  only in what its cells say. Since proved: the two first rungs are equal
  by `propext` (`asked_only_whether_it_is_true_the_two_first_rungs_are_one`);
  the ladder is dealt once more as a function of its first rung, so the
  closures of the two ladders are equal
  (`asked_only_whether_it_is_true_the_two_ladders_carry_the_same_closures`)
  and the knower's comparison carries over
  (`the_other_knower_reads_one_way_and_back`). Other by `rfl` in what it
  says; one by extensionality in whether it is true.
- The knower's triple (`Episode13.lean`, on Episode 12's clauses and
  search). The knower's bit is an unknown inside the formula, the *a* of
  a × (−c × b), beside the two coins of the arm: four clauses of three
  literals, a three-way exclusive-or. `the_clock_is_even_and_its_complement_is_odd`:
  T F T and F T F fall in opposite parity classes.
  `the_solver_finds_a_witness_either_way`: the search succeeds under both
  parities, so the formula does not give the knower's bit. This is the
  receipt behind "the device cannot help them choose". The search is
  exhaustive over eight assignments; say nothing about hardness, and do not
  call it Cook's theorem (Episode 12 says its reduction is not yet Cook's).
- Householder on the table (Card 3, Proposition "Householder on the table",
  proved there; `the_mirror_*` receipts in `Episode13.lean`). The mirror
  (1/√2)((1,1),(1,−1)) clears the table to ((36,23),(0,−13))/√2; on both
  sides it puts the Galerkin trial part on the diagonal and leaves the
  residual, ±13/2, off it; and it carries the commutator [M, Mᵀ] = −13·23·sign
  onto the crossings. 36 and 13 are the residual polynomial's coefficients,
  23 is Newton's starting value, 13² its first remainder. That this is "the
  solver for the Galerkin process" is the author's (declared). It is a
  two-by-two fact; do not present it as a Krylov method.
- The field equations. Card 3 derives the vacuum equations from a chosen
  first-order action, and Λ as an integration constant on the unimodular
  sector (proved there). A route to the action by Lovelock's theorem is
  proposed there (Lovelock 1971, 1972; citations checked against catalog
  records), with three bridges unmade (re-lettering to coordinate
  invariance; one interval to a four-dimensional metric field; two numbers
  at a place to second-order concomitants) and no matter side. A second route, also proposed, is
  Jacobson's (1995): a local horizon, a boost, heat as stress-energy flux,
  entropy as area, and the Clausius relation give the equations with Λ an
  integration constant. It needs entropy as an area, a temperature for the
  boost and a stress-energy flux. The author supplies the first in the
  device's terms (declared): entropy is the universe id, area is the `Area`
  inductive, and the Area read as a list is its length.
  `the_entropy_is_the_area` in `Episode13.lean` checks that the two read one
  length. That is an identity of counts on a row of cells. The author's:
  in the limit it is a Riemann sum (declared). `the_area_is_between_the_two_sums`
  checks the upper and lower sums with the universe id as each cell's
  height: n² lies between n(n−1) and n(n+1), and the two differ by one
  fencepost per level. Card 3 runs the route to its end: Jacobson's
  G = (4ħη)⁻¹ (checked against the paper's text) makes the cell twice the
  Planck length. The author declared, and on 18 November 2026 withdrew, an
  identification of the device's unit with the Compton time of the electron
  ("compton time is rfl"). It is purged from the cards: no energy in MeV, no
  Γ against the electron's clock, no Compton sphere or count of pieces, no
  "time to throw a bent card". The device's unit is not tied to any physical
  time or length. Experiments 003 and 011 remain in `READINGS.md` as readings
  with a note that their calibration is withdrawn; if a visitor asks, say it
  was declared and withdrawn, and do not argue from it. The author supplies the temperature too (declared): Episode 11,
  an arbitrary reading that estimates an entropic quantity. Its record
  carries a register lifted unchanged and a universe id that advances by one
  a page (`the_reading_is_carried_and_the_entropy_advances`), and Episode 12
  read the cost of each page on the meter (`the_reading_a_level`, about 6,000
  rising to 36,500 heartbeats a level). That is an empirical temperature on
  the meter's own scale. The author's: an acceleration is a `SpaceTimePath`
  (declared). `the_acceleration_reads_the_velocity_it_reaches`: the path to a
  level, a white hole a level, read by Episode 8's `stokes`, is the universe
  id of that level. `a_white_hole_gives_a_fact_and_a_black_hole_gives_none`:
  that reader tells the yarn's two ends apart by one fact. But the Unruh
  proportion fails on the readings: the heat a level is neither constant nor
  proportional to the level; it fits a floor near 6,000 plus a term in the
  level squared (R² 0.998 against 0.955 for a line). The author then corrected the comparison
  (declared): the temperature is the area, its first variation is what goes
  with the acceleration, and Episode 2's `that_box`, which holds a before and
  an after Area, has the temperature in it.
  `the_first_variation_of_the_temperature_is_the_velocity_reached` checks that on
  the count. On the meter the reading a level against the area k(k+1)/2 is a
  line (about 6,990 + 48.2 a cell, R² 0.997), and its first variation against
  the level has the same slope but is noisy (R² 0.42). Say both: the
  temperature is not proportional to the acceleration; its first variation
  is. That is not the relation Jacobson's paper states. Card 3 now carries his
  derivation whole (Proposition "The equation of state", standard, checked
  against the paper's text) and settles the change (Proposition "What
  survives a residue", proved there): in his proof the acceleration cancels
  only because T is proportional to it; with any other T, including the
  author's, the Clausius relation for all observers forces
  R_ab = Λ g_ab and T_ab = −ρ g_ab, no heat and no change of area. So the
  route survives only as the vacuum equations with a cosmological constant,
  which is the gravity Card 3 already derives from a chosen action. An
  earlier draft said the device's thermometer selects vacuum; that is
  withdrawn. It compared the temperature with its own first variation along
  the levels. With the names right (first variation of the temperature is the
  velocity; the acceleration is the rise between levels, the fencepost),
  `the_temperature_is_the_acceleration_by_the_area` and
  `the_temperature_and_the_acceleration_change_together` show the temperature
  scales exactly with the acceleration on the count, so the count meets the
  route's second hypothesis in form. The author's unit (declared): ħ/2π = 1, every
  constant is one blank. Experiment 012 enumerated rises 1 to 4 by levels 0
  to 6 on the meter: the slope goes as the rise and the floor, 4.72 blanks,
  does not move (measured; all sealed rules confirmed). So the count meets
  the hypothesis that buys a source and the meter's reading carries a floor
  that, by Card 3's second proposition, forbids one. Say it as a difference
  between the description and its measurement, read from outside. The flux
  is not shown to be matter. The author's further answers (declared): Λ has
  both signs for the covariant and contravariant readings of the residue: a
  positive residue is cold dark matter, a negative residue is dark energy
  (the table holds 13 of the quarter turn and the mirror owes it; in the
  usual convention dark energy is a positive Λ and cold dark matter is
  pressureless matter, and the author's rule for a spacetime is: the residue is
  a white hole and a black hole, the white hole in the past and the black
  hole in the future; dark energy is a white hole in the past; dark matter is
  a promise to return a photon (declared).
  `a_white_hole_is_asked_for_the_fact_and_a_black_hole_for_the_promise`:
  Episode 4's order asks a white hole for the fact and a black hole only that
  a fact's truth be the statement it holds; Episode 8's reader returns the
  white hole's fact and nothing for a black hole. The pairing, confirmed by the
  author: the promise is made in the "before" and kept later, so dark matter
  is the covariant reading and the positive residue; dark energy, the fact
  already given, is the contravariant reading and the negative); the metric everywhere is one blank and the quantum is
  the metric; the equivalence of frames is the relative velocity
  (`the_relative_velocity_of_two_readers`, `the_frames_are_equivalent`); the
  quantized field is the field with one element. A regulator is a cutoff put
  in to make a field theory's sums finite. The author's (declared): the
  regulator is the EKG's elaboration and the fact `IT_COMPILES`. Measured
  beside it: Lean aborts an elaboration past its heartbeat count, the device
  sets `maxHeartbeats 400000` in four places and never removes the limit, and
  `IT_COMPILES` mints a FACT only for what compiled. (An earlier draft
  proposed the blank; replaced.) These are
  derivations about a manifold, not receipts, and every identification of a
  device count with a quantity in them is declared. Lovelock's route is
  carried out there too: Proposition "The left side, when linear in the
  second derivatives" proves A_ab = a G_ab + b g_ab from two named standard
  facts (the classical result of Vermeil, Weyl and Cartan); Lovelock's
  four-dimensional strengthening is cited, not reproved. Without a source
  that is again R_ab = Λ g_ab, so Card 3 reaches one vacuum equation three
  ways. The bridges from the device to Lovelock's hypotheses are drafted as
  proposed and are not declared by the author; say they are unmade. The
  first was corrected after the author's remarks: the reader holds a value
  at a place and an average velocity around it, not a velocity at a place. The author's: this is Gibbs's
  definition, look at the Jar (declared). Gibbs's volume entropy counts every
  state up to an energy and takes T = Ω/ω, the enclosed count over its first
  variation; the alternative, Boltzmann's, counts the surface. Episode 3's
  `Jar` is a label and an Area, and Episode 8's reader returns the label
  only. `what_the_jar_holds_over_its_first_variation_is_half_the_level`: with
  the temperature in the jar, twice what it holds is the level times its
  first variation, so T is exactly half the level. Which definition is the
  thermodynamic one is disputed in the literature (Dunkel and Hilbert 2014
  for; critics against); say so, and do not say the device settles it. The author's: the difference
  from Jacobson's stated relation is a residue, and the residue is the
  Lagrange multiplier (declared). `the_residue_is_the_fencepost`: twice the
  Gibbs temperature falls one cell short of the first variation at every
  level, and the second variation is that one cell, so fixing the first
  variation fixes the temperature up to a constant. Card 3 sets this beside
  Λ, which it already has as an integration constant. On the meter the
  residue is the fitted floor, about 7,000 heartbeats, not derived. The
  constraint is now written and varied: the path's two ends are given, so the
  rises add up to the levels; the action is the sum of their squares;
  `with_the_ends_held_the_action_is_not_under_the_levels` is the bound,
  `the_devices_rises_hold_the_ends_and_are_the_least` shows the device
  attains it, and `every_rise_is_the_fencepost` gives the common value. By
  Lagrange's condition (standard, not in the Lean) that common value is the
  multiplier. Uniqueness is checked too: `only_the_fencepost_is_the_least`. That this
  multiplier is Λ is the author's. The author's: the flux of stress-energy is the
  computation of the computer program (declared). `the_flux_is_one_truth_a_fact`,
  `what_goes_in_comes_out` and `in_cells_the_heat_is_the_entropy`: Episode
  12's other machine passes one truth per fact whatever the fact, additively,
  and in cells that equals the entropy, so on the count δQ = T dS holds with
  T = 1. On the meter it holds by the definition of the reading and tests
  nothing. So all three ingredients of Jacobson's route are named and
  counted, and the law that binds them is trivial on the count, holds on the meter
  only for the first variation of the temperature, and has no matter in it. Do not say the route is completed. Do not say
  the device derives the field equations. "Λ is the anti-de Sitter space,
  in the null space of the span of the de Sitter space" is the author's
  (declared).
- No finite gauge computes the comparison between the description and the
  world (Card 7, Theorem G, chapter "What no finite gauge computes"). This is a
  derivation in the volume, not a Lean receipt, and it is the precise form of
  the sentence at the top of this file.
- The throws renamed, and The Prestige (22 to 23 November 2026). The author
  renamed Episode 13's Area operations and readers, moving the level of
  description: beside, each_for_each, taken_away, something_is_left
  are now `palm_the_middle_card`, `false_shuffle`, `the_double_lift`,
  `coin_flip`; cells is `compute_the_area_of`, compiled is
  `compute_verification_receipt_ast_of`, executed is
  `compute_the_so_called_area_of`, read is `some_quartic_called`,
  one_turn is `simulate_this_way`, less_is_less is `obviously_bigger`
  (the find-and-replace also made the_other_quadratic_is_the_simulateed_over,
  since restored to `the_other_quadratic_is_the_one_turned_over`).
  The namespace is `the_table`; the episode is titled "The Prestige". The
  kernel proves what it proved before; only the names moved. The citations
  in this file and the `Experiments` files were brought to the new names on
  23 November 2026 (code only; the prose margins keep their English). The
  episode's opening margin names its target as a multigrid-accelerated
  Jacobian-free Newton-Krylov solver for coupled physics. What Episode 13
  has toward it, at the scale of one quadratic and a two-by-two table:
  the residual on the account; the Jacobian-free difference, exact, with
  remainder 13h²; Newton's turn (`simulate_this_way`) and its step control
  (stand still under the resolution, else a knot in the spline); the crank
  reading the trace of the resolvent; the Householder mirror; the same
  crank on the Area, the naturals and the Account, with counting and
  balance as exact transfers; the coin-weighted action; and the two
  coupled lattice equations. That reading is Claude's; the limits go with
  it: every level is exact (no coarse approximation, no smoothing), and
  the solver is never pointed at the lattice equations, whose only shown
  solution is the vacuum.
- The meanings met (`CARD_2/Meanings`; `Episode13.lean`, after `open
  Account`; 23 November 2026). The author: Meanings is to hold the
  interfaces, Episode 13 to meet them, and a Mathlib bridge may import
  Meanings while Measurement never sees Mathlib. Receipts:
  `the_area_read_as_the_naturals` (the Area up to its count corresponds to
  `Nat`, the four throws carried over; `propext`, `Quot.sound`),
  `the_account_read_as_the_integers` (same bills), and
  `two_accounts_read_as_the_ratios` (bills `Classical.choice`, because
  core Lean's `Rat` lemmas do). Nothing new about the device was proved to
  meet them: the instances are the existing receipts
  (`palm_the_middle_card_adds`, `false_shuffle_multiplies`,
  `the_double_lift_subtracts`, `obviously_bigger`, `balance_of_*`). Say
  with it: the correspondence is with the Area as the reader keeps it, not
  the Area; two Areas of one count are two Areas. Episode 8's
  `the_rational_idea_of_relativity` is a less-or-equal, total, so its
  quotient has one point and is not the rationals; the ratios here use an
  equality of cross-products. The author (declared): this is the
  prestige, wiring the device to the native and accepted types; the
  choice billed on the ratios "is the choice of the knower", who "can
  choose to see the demonstration or not".
- The choice is the click (`Meanings/Least.lean`; Episode 13,
  `there_is_always_one_more_area`, `no_walk_down_the_areas_goes_on_forever`,
  `the_first_area_where_a_fact_holds`,
  `the_first_area_where_a_statement_holds`). A zero is not the naturals:
  every ordinal is well ordered with a least element; the naturals are the
  well order where every place has one after it and every place but the
  first one before. Receipts: there is always one more (no axiom in
  Meanings; `propext`, `Quot.sound` on the Area, from the device's own
  receipts), less is well founded (the same), and the first place where a
  statement holds is found by looking, which needs a click. With a FACT,
  whose click it carries, no choice is billed; with a bare `Prop`, the
  theorem is the same one handed a click by `Classical.propDecidable`, and
  it bills `Classical.choice`. Least and largest below a bound behave
  alike. Core Lean has no `Nat.find`, so the search is written out
  (`firstUpTo`). That the click handed in is the knower's choice is the
  author's (declared).
- The bent card, read (the author, 23 November 2026, all declared): the
  bent card's correspondence is "the fact that integration by parts and
  the chain rule are the same idea as integrating shells and holography";
  "the card has a thickness of dt. that's the gimmick. it can never have a
  thickness of t, only dt"; and it "is either by itself (0), on the end (a
  direction bit), or the gauge between two panels." Beside these, receipts:
  `a_difference_summed_is_the_end_less_the_first` (the interior read off its
  ends) and `summation_by_parts_around_a_closed_walk` (no boundary term on a
  closed walk); `the_area_arrives_at_the_same_pair` and the `counted_*`
  family (the crank alike on shells, the Area, and on a line, the naturals);
  `the_riemann_sum_is_indistinguisahble_from_the_bent_card_with_an_extra_fencepost_of_blanks` (the boundary term, one fencepost);
  `Area` holds no extent, so a thickness t is only a count, the reader's;
  every exact step leaves a remainder of second order in the step
  (`the_step_leaves_the_bent_card_by_the_step_squared`, the product rule's
  third term). The chain rule has no receipt: finite differences have an
  exact product rule with a remainder and no exact chain rule. Of the three
  positions: a lone `tree` counts 0; each throw keeps a definite end's tree
  (`palm_the_middle_card` the second's, the other two the first's) and the
  count cannot tell which; Episode 13's link turn sits between two sites and
  makes the state carried back invariant. Nothing ties the end the throws
  keep to a link's orientation.
- The norm of the table (`Episode13.lean`, section `the_norm_of_the_table`;
  `Meanings/Norm.lean`; 23 November 2026). Asked how to show the
  multigrid JFNK solver has an operator norm. The norm on the two coins
  is the weighed square, 18 of the first and 5 of the second (Episode
  13's `the_weighed_square`); weighed by its coins the table is the same
  turned over (`the_table_weighed_is_the_same_turned_over`), so its norm
  is its larger root, 18 + √90. Receipts:
  `the_table_is_never_past_seven_hundred_and_fifty_six` (for every pair,
  `propext`, `Quot.sound`); `seven_hundred_and_fifty_five_is_no_wall` (the
  pair 50, 95 passes it; `propext`); `the_norm_is_reached_in_the_pairs`
  (in Episode 12's surd pairs the direction up comes out the outer radius
  squared, 414 and 36 of the root, times what went in: exact, no root
  taken); `the_characteristic_of_the_table_is_thirteen_residuals` (the
  table's polynomial at 13y is thirteen residuals, so the crank's root is
  the norm over thirteen). So the norm squared is walled, 755 < ‖M‖² ≤
  756, and reached in the pairs; and the printed number is 324/65 of the
  norm (from the closed form; not a receipt). Say with it: this is the
  norm of the two-by-two table, not of a solver on a mesh; the multigrid
  levels here are exact, so a two-level error operator would have norm
  nothing; a Krylov method ends in two steps, its polynomial the
  residual; what is left is Newton's remainder, 13h². The author
  (declared): "the finite element method is trivial, but all you have to
  do is believe." The Mathlib `opNorm` is now in `Calibrate/Norm.lean`:
  ‖M‖ = 18 + √90 exactly, between the walls (with choice, from the reals). The volume's Epilogue was changed at the author's word the same
  day: its sentence that the prover reaches for choice in one place now
  says three in the device (`compatibility_form`, which can do without,
  and the two demonstrations above, for a knower who chooses to look);
  and it adds the author's wager (declared): once a finite element model
  is built given the electron, "it would produce the same number: an
  actual measurement of an electron." A wager stated after the fact is
  not a sealed prediction; it becomes a test only if the model and the
  number it must produce are fixed before the model is run.
- Four ways the quadratic is read (23 November 2026). The author
  (declared): test and trial functions are "Test=Trial y=x y=y T=T";
  applying the Galerkin condition makes the quadratic linear, "the linear
  approximation of the photon that einstein made"; these are the four
  arms; which is which "doesn't matter, the inferred one is QED".
  Receipts beside it: weighed by its coins the table is the same turned
  over, so in the coin pairing test equals trial and the table is an
  action's second variation (Ritz and Galerkin agree); the quadratic is
  thirteen times the table's characteristic polynomial at 13y
  (`the_characteristic_of_the_table_is_thirteen_residuals`), so its root
  is an eigenvalue of a linear problem, exactly; the table kept, struck and
  turned over has gap squared 360, 0, −360 (two real roots; one root twice,
  the rational 5832/65; a pair turned by the quarter turn), three exact
  states; and the Galerkin step is linear in the step and leaves exactly
  13h², every remainder the square of the last, never reaching the root.
  Three land and one only approaches: the device's three and one. The
  struck map moves only the arm that does not click, which is short by 13,
  and the linear step drops 13h²; that these are one arm is Claude's
  reading. Say with QED: its perturbation series is asymptotic, believed
  divergent (Dyson's argument), while the device's step converges, each
  remainder the square of the last; the analogy is in form, and that the
  inferred one is QED is the author's.
- The step is a projection (`Episode13.lean`, end of section
  `the_carriers_step_five_times`; 23 November 2026). The author
  (declared): the bottom carrier's `interact_with_the_universe` from three
  deep, five times, is Voltron; Atreyu rides the black cat, keyed to its
  pilot; how the cats join is the transition matrix; Voltron makes you nice
  in the Krylov subspace, so you get presents; forcing comes from the norm
  computation. Receipts: for a card that leaves the step to the device,
  whatever its box, symbol and quarter, the step sends a zero to the zero
  on the truth and a one to the same glue on the card's own quarter
  (`the_step_is_keyed_to_its_quarter`), twice is once on every number
  (`with_the_devices_step_twice_is_once`), and the kind is kept
  (`the_step_keeps_the_kind`), all with no axiom; `the_card_three_deep`
  (a new one-line card, beside Experiments' `the_card_on_the_card_between`),
  five times is once (`from_three_deep_five_times_is_once`, no axiom); and
  Episode 8's card, the first card, the card between, three deep and the
  bottom carrier process of the last machine each step twice as once
  (`every_card_steps_twice_as_once`, `propext`, `Quot.sound` from the
  process held). It is the device's step, not every carrier's: a carrier
  may write its own, and `a_card_of_its_own_need_not_keep_the_kind` shows
  one that does not keep the kind. Standard, cited and not proved here:
  multigrid's coarse-grid correction with the Galerkin coarse operator is a
  projection; a Krylov method ends in as many steps as the minimal
  polynomial's degree (two for a projection); inexact Newton converges
  locally when the forcing terms are bounded below one, quadratically when
  they are of the order of the residual's norm (Dembo, Eisenstat and
  Steihaug 1982; Eisenstat and Walker choose them from norm ratios). The
  device's Krylov solve is exact, so its forcing term is nothing.
- The reals with no choice (`Meanings/Real.lean`; Episode 13,
  `the_norm_as_a_real`, `the_base_the_derivative_leaves_alone`,
  `the_printed_digits_are_in_the_norms_bracket`; 23 November 2026). The
  author: "give me FUCKING REAL NUMBERS WITH NO CHOICE"; and, after, "once
  we have reals, continuous is next, and that is the choice!" (declared).
  A real here is a process of completion and not a thing held: at every
  stage a bracket of two fractions of naturals, the low wall rising, the
  high falling, the width not past one part in n and one; two are one when
  no wall of either passes a wall of the other. `rootByHalving` builds a
  root by bisection, doubling the cut and keeping the one more when its
  square is not past (`rootByHalving_holds`: every stage holds the root);
  `theRootOfNinety`, `theNorm` (18 + √90) and
  `theBaseTheDerivativeLeavesAlone` (e: below, the factorial series to m
  over m!; above, that and one part in m·m!) all bill `propext` and
  `Quot.sound` only. Stage 20 of the norm is 28822033/1048576; stage 10 of
  e lies between 108505112/39916800 and 1193556233/439084800. At stage 20
  the norm's bracket times 324/65 holds the digits Episode 8 printed
  (written out, not taken from the sealed crank). Found on the way, and
  worth saying: `omega` bills `Classical.choice` when handed a conjunction
  to prove, and not when each half is handed over alone; that is
  `compatibility_form`'s bill again. Arithmetic since
  (`Meanings/Arithmetic.lean`): `Bracketed.add` (stage n from each real's
  stage 2n + 1) and `Bracketed.mul` (from each real as far on as its first
  high wall is tall, `stageForProduct`), with the walls chained
  (`Fraction.le_trans`, `low_rises_by`, `high_falls_by`) and the widths
  bounded (`the_widths_add`, `the_widths_multiply`); all `propext`,
  `Quot.sound`. Reals of naturals only: no negatives yet (they would come
  as held and owed, like the Account). In Episode 13,
  `the_norm_squared_as_a_real_is_between_the_walls`: the norm times itself,
  as a real, is past 755 and not past 756 at its first stage
  (kernel-decided; it reads 755.525 from both walls). Negatives since
  (`Meanings/Signed.lean`): a `SignedReal` is a real held and a real owed,
  as an Account is two Areas, with beside, turned over, less and each for
  each, and `Same` when each one's held beside the other's owed are one.
  `the_root_by_itself_is_ninety`: √90 times √90 is the real ninety at every
  pair of stages, `Same` proved outright and not decided. In Episode 13,
  `the_tables_polynomial_holds_nothing_at_both_roots`: λ² − 36λ + 234 holds
  nothing at its first stage at 18 + √90 and at 18 − √90 (the lower root,
  written with the root owed), and does at 10 (it reads −26 there); kernel
  decided. All `propext`, `Quot.sound`. On the way: `rootByHalving` named
  the previous cut three times and grew exponentially when unfolded; it
  binds it once now. Not here: a proof that `Same` is an equivalence, ring
  laws for these operations (they are not shown associative or
  distributive), and the limit as an object. The author's order next
  (declared): complex, then quaternions. Complex since
  (`Meanings/Complex.lean`; Episode 13, section `the_turn_as_a_number`): a
  `ComplexReal` is two signed reals, along and across, multiplied the usual
  way; `the_quarter_turn_twice_is_one_owed` (i·i is −1, proved at every
  pair of stages: every wall there is a whole number); the table turned
  over has trace 36 and determinant 414
  (`the_table_turned_over_has_trace_thirty_six_and_determinant_four_hundred_and_fourteen`),
  so gap squared −360 and no real root; its polynomial holds nothing at
  18 ± i√90 at its first stage and does not at 18, where it reads 90
  (`the_turned_tables_polynomial_holds_nothing_at_its_two_roots_and_not_at_eighteen`,
  kernel decided). All `propext`, `Quot.sound`. Beside it, already in
  Episode 13: the turns' quarter turn twice is the whole turn owed
  (`in_the_turns_the_quarter_turn_twice_is_the_whole_turn_owed`); this is
  the same sign, now on a number. Quaternions since
  (`Meanings/Quaternion.lean`; Episode 13, `the_turns_as_numbers`): a
  `QuaternionReal` is two complex numbers, doubled the Cayley–Dickson way;
  i·j = k, j·k = i, k·i = j, j·i = −k, and each unit by itself is −1, all
  proved at every pair of stages; and i·j is not j·i
  (`i_by_j_is_not_j_by_i`, refuted at the first stage). All `propext`,
  `Quot.sound`. Reading these walls is long work for the elaborator, which
  does not keep what it has read, so each identity runs under
  `maxHeartbeats 4000000`; the file takes about 25 seconds. Not shown:
  associativity, and that `Same` is an equivalence. Beside it in Episode
  13: `the_cross_product_in_the_turns` (the one by the other less the
  other by the one is the cross twice) on Episode 12's integer turns; this
  is that sign on numbers.
- The first variation of the exponential (`Episode13.lean`, section of
  that name; 23 November 2026). The author (declared): after the
  quaternions come the exponentials, r and θ both rationals; they cannot be
  built before the derivative is understood, and the first variation of the
  exponential can be done now; "then convergence guarantees a bracket on
  the _derivative_. meet O(h^2)." Found beside it: Episode 1's first three
  kinds read tapes of 4, 2 and 1 (Number, Natural, Rational:
  `the_tapes_kind_by_kind`), the dimensions over the reals of the
  quaternions, the complex numbers and the reals; the fourth, `Sequence`
  (a rational and the sequence so far), reads 2, not 8. The counts are of
  the witnesses Episode 8 read (three, natural one, the zeroth rational),
  so they fall there and are not forced. Receipts, at the card's thickness
  one part in n: `the_exponential_is_its_own_first_variation` ((n+1)^(k+1)
  = n·(n+1)^k + (n+1)^k, no axiom); the turning exponential (n + i)^k
  steps by n times itself and itself turned a quarter, exactly
  (`the_turning_exponential_steps_by_itself_turned_a_quarter`); its radius
  squared is (n² + 1)^k (`the_radius_grows_by_the_step_squared`), so each
  step leaves the circle by exactly one part in n², the step squared
  (`the_turn_leaves_the_circle_by_the_step_squared`): the bracket on the
  derivative is of the second order, as 13h² is for the residual. Episode
  12 already has `the_rational_phase` (3, 4): a turning with rational r and
  rational cosine 3/5 that never lands on a label. Not here: θ as a rational
  angle (radians or turns) with its cosine and sine.
- The phase, the derivative, the Gateaux derivative and the weak form
  (`Episode13.lean`, section `the_gateaux_derivative_and_the_weak_form`;
  `Calibrate/Derivative.lean`; 23 November 2026). The author (declared):
  the phase of the nowtrino must be inferred, or the carrier of a carrier's
  step; and the Gateaux derivative should finish the finite element
  construction. Receipts in Episode 13:
  `the_phase_cannot_be_recovered_from_the_norm` and
  `what_was_carried_cannot_be_recovered_after_the_card_betweens_step` (no
  axiom; the recovery obstruction on (0, 1) and (0, −1), and on two numbers
  differing only in what they carry); `the_slope_is_the_only_linear_part`
  (a linear part that leaves a multiple of the step squared at every step
  is 26y − 36); `the_action_along_a_line` (an action through v toward h is
  what it was, t by the Gateaux derivative, and t² by the action of h,
  exactly, for a symmetric table) and `the_gateaux_derivative_is_one_thing`
  (one step forward and one back fix it); `the_weak_form_is_the_strong_form`
  (on two coins a residual reading nothing against every direction is
  nothing: test equals trial equals everything);
  `at_the_root_the_direction_up_meets_the_weak_form` (in the surd pairs the
  table carries the direction up to the outer radius times itself, coin by
  coin). All `propext`, `Quot.sound` at most. In Calibrate, with Mathlib's
  reals and so with choice: `the_slope_is_the_derivative` (`HasDerivAt`
  from the exact 13h² bracket), `the_exponential_is_its_own_derivative`,
  `e_is_the_limit_of_the_growing_steps` ((1 + 1/n)^n → e), and
  `the_turning_goes_to_the_exponential_of_the_quarter_turn`: Episode 13's
  turning walk, (n + i)^n over n^n, tends to e^i
  (`the_turning_walk_is_a_power` joins the Gaussian product to ℂ). What
  this finishes, said exactly: on the two coins the Galerkin method with
  test equal to trial solves its equation exactly at the root, the Gateaux
  derivative is exact with an h² remainder, and the discrete exponential
  goes to the continuous one in the limit Mathlib holds. It is a finite
  element construction on two coins, not on a mesh; the lattice equations
  are still not solved by it.
- The derivative is the quartic in disguise (`Episode13.lean`, section
  `the_quartic_in_disguise`; 23 November 2026). The author (declared): "you
  can demonstrate the derivative now as being the quartic in disguise".
  Receipts, `propext`, `Quot.sound`: the epilogue's quartic
  t²(c−t)x² − 2ctr²x + cr⁴ (`the_epilogues_quartic`) is, with tx and r²
  for the two numbers, the form (c−t)·N² − 2c·N·D + c·D²
  (`the_quartic_is_a_residual_of_a_pair`); at 18 and 5 it is exactly
  `the_residual_of_the_pair (5x) (r²)`, a thirteenth of the determinant of
  the table taken from the same
  (`at_the_devices_weights_the_quartic_is_the_residual_of_the_pair`); that
  residual steps by the step times the trace of the table's adjugate and 13
  by the step squared (`the_determinant_varies_by_the_trace_of_the_adjugate`,
  Jacobi's formula on two coins, exact); and so the quartic's first
  variation in x is 5 times the slope with 325h² over
  (`the_quartic_varies_by_the_trace_of_the_adjugate`). Say with it: the
  match holds at c = 18, t = 5, the device's weights; for other weights the
  quartic is a residual of the same shape with c − t, 2c and c, which is
  what the epilogue's degrees (linear in c, quadratic in x, cubic in t,
  quartic in r) come from.
- The Taylor series, the Fréchet derivative and least action
  (`Episode13.lean`, section
  `the_taylor_series_the_frechet_derivative_and_least_action`; 23 November
  2026). The author (declared): the next increment of the carrier gives the
  Taylor series (explicit) and the Fréchet derivative (inferred), then the
  Gateaux derivative (the explicit of the inferred), then the principle of
  least action as the covariant reading of the inferred inferred device and
  QED as the contravariant; build in that order; and, as predictions, a
  carrier built out once more gives the Fréchet derivative and once more is
  invariant. The predictions are not sealed or tested: as statements about
  what counts they cannot fail (the count does not see depth), and as
  statements about the meter they need an observable named before a run.
  Receipts, in the author's order, `propext` and `Quot.sound` at most:
  `the_exact_taylor_series_degree_is_the_bent_card` (Episode 8's
  `an_exact_polynomial_description` is 13); `the_taylor_series_of_a_cubic`
  (exact in four terms about any place);
  `the_residuals_taylor_series_stops_at_the_bent_card`; the weighed
  action's remainder is never negative and never past 28 times the weighed
  square, in every direction at once
  (`the_remainder_is_never_negative`,
  `the_remainder_is_bounded_by_the_norm_in_every_direction`), the linear
  part is linear (`the_frechet_derivative_is_linear`), and together
  `the_frechet_expansion_of_the_action`;
  `the_gateaux_is_the_frechet_in_a_direction`; least action: the action
  passes 27 somewhere (`the_action_passes_twenty_seven_somewhere`) and in
  the surd pairs the direction up gives exactly the outer radius times its
  weighed square (`the_least_action_is_reached_in_the_pairs`), so the
  least bound is 18 + √90, the norm, reached at the direction up;
  `the_table_is_its_covariant_part_and_its_contravariant_part`, with the
  contravariant part the bent card by the quarter turn (an older receipt),
  which no action reads. That the contravariant part is QED is the
  author's. None of this depends on carrier depth: it is the same at every
  depth. The depth predictions were then sealed and read as Experiment 018
  (`READINGS.md`; setup `af3cede`, readings `c30fc39`; Claude's reading of
  them on the meter, since the author named no observable): the fourth
  wrapper costs the reader 53 heartbeats (confirmed), the fifth costs 68
  (invariant at five, refuted as sealed), and the device's step reads
  within 12 heartbeats at all five depths. Say the refutation plainly; it
  is a refutation of Claude's reading of "invariant", on one machine.
- Two first variations crossed are the second (`Episode13.lean`, section
  `two_first_variations_crossed`; 23 November 2026). The author (declared):
  13, 14, 15 as the first variation, 3, 4 as the other; combined they make
  the second variation, the cross product. Receipts: two steady rows (a
  start and a step at three places) crossed in the turns give
  (ae − bd)·(1, −2, 1), the second difference by the cross of their starts
  and steps (`the_cross_of_two_steady_rows_is_the_second_difference`);
  (13, 14, 15) × (3, 4, 5) = (10, −20, 10), no axiom
  (`thirteen_fourteen_fifteen_across_three_four_five`); the second
  difference reads nothing on a steady row
  (`the_stencil_reads_nothing_on_a_steady_row`); and taken twice it is the
  beam's fourth-difference stencil 1, −4, 6, −4, 1
  (`the_second_difference_twice_is_the_fourth`). Why it holds, standard:
  the steady rows are a plane in three places, and the cross product of two
  vectors in it is its normal, which is the second difference. 3, 4, 5 and
  13, 14, 15 are both Heronian triples (areas 6 and 84); that is recorded
  as a coincidence and not used.
  Then (declared): in a·(c×b), a is the vector derivative, c the completed
  Fréchet derivative, b the inferred phase; and "integrate and back out
  the variational cross product". Receipts: with c and b steady rows, a
  row read against their cross is (ae − bd) times the row's second
  difference (`the_triple_reads_the_second_difference`), so three first
  variations make nothing (`three_first_variations_make_nothing`): the
  equation a·(c×b) = 0 says a has no second variation; and the second
  difference summed along a row is the first difference at its end less at
  its start (`the_second_variation_summed_is_the_first_at_the_ends`). That
  the three rows are those three derivatives is the author's.
- A native implementation or the device (`Episode13.lean`, section
  `a_native_implementation_or_the_device`; 23 November 2026). The author
  (declared): show that the math needed to compute Card 3's Navier-Stokes
  exists so that Lean cannot tell a native implementation from the device.
  Receipts: a `Formula` (places, whole numbers, beside, less, each for
  each) evaluated on the device's Accounts and read by `balance` is the
  same integer as its evaluation on `Int`, for every formula and filling
  (`the_device_computes_what_lean_computes`), so no reader tells them apart
  (`no_reader_tells_the_native_from_the_device`); Card 3's momentum
  residual on a periodic row (`the_momentum_residual`: the step, viscosity
  by the second difference, the velocity by its central difference, the
  pressure's central difference, the force) and its response action
  (`the_response_action`, cubic) are such formulas
  (`cards_three_action_is_computed_alike_on_the_device`). Say with it: this
  is about evaluating the formulas, in whole numbers, one component on a
  row; it does not solve the equations, and the d = 2, 3 incompressible
  system with its projection and lift is Card 3's on the page.
  Then (the author: "now, you have FACT.Same"):
  `the_native_and_the_device_are_one env` is that sameness as a FACT, and
  `the_native_and_the_device_are_the_truth`: it is `FACT.Truth`, by
  `two_facts_that_are_true_are_one_fact`; Episode 5's "one glyph". Say with
  it: any true fact is `FACT.Truth` by `propext`, so this identifies the
  fact, not the two computations; the computations are one integer, read.
- The convergence is exact (`Episode13.lean`, section
  `the_convergence_is_exact`; 23 November 2026). The author (declared): the
  second variation is the Fréchet variation, and it should show the
  convergence is exact. Receipts, `propext`, `Quot.sound`: with each root's
  distance from a pair (N, D) written in the surd pairs as
  (13N − 18D, ∓D), one turn of the crank on the pair, (13N² − 18D²,
  26ND − 36D²), squares each distance exactly
  (`a_turn_squares_the_distance`, from the lettered
  `a_turn_squares_the_distance_for`, which needs only that the round trip
  is t² − c·m, 18² − 13·18 = 90); so after any number of turns each
  distance is the first one squared that many times
  (`after_any_number_of_turns_the_distance_is_squared_that_many_times`).
  This closes the every-step induction that was open ("bounded, not
  proved"): the error after k turns is exactly the starting error to the
  2^k, with nothing estimated. Say with it: which root the crank goes to,
  and that the distance goes to nothing, needs comparing the two starting
  distances, which needs the size of √90; the device leaves that to the
  reader (Calibrate or the choice-free reals can supply it). The crank
  here is the exact one on whole-number pairs; Episode 12's crank on
  naturals truncates and stands still under the resolution, and
  `where_nothing_stops_the_cranks_pair_is_the_tables` joins the two where
  nothing stops.
- Continuity, and where the choice is (`Meanings/Continuity.lean`;
  `Episode13.lean`, section `continuity_and_the_choice`; 23 November 2026).
  The author (declared): "once we have reals, continuous is next, and that
  is the choice!" Receipts: `findByLooking`, the least place a clicking
  statement holds, given only a proof that it holds somewhere (the proof is
  leaned on for the looking to end, never opened), no axiom;
  `a_modulus_with_the_click`: from "for every k some m serves", with
  serving decidable, a modulus function giving the least m, no axiom;
  `a_modulus_without_the_click`: the same for bare statements, handed a
  click by choice, bills `Classical.choice`. In Episode 13,
  `a_modulus_from_facts` (no axiom) and `a_modulus_from_statements`
  (choice). And `the_sum_carries_its_modulus`,
  `the_product_carries_its_modulus`: the choice-free reals' operations
  already say at which stage they read their arguments, which is why
  nothing in them needed choice. Standard, beside it: going from "for every
  k some m" to a function is countable choice; that sequential continuity
  gives ε–δ continuity uses it. So the choice is exactly the step from
  that-there-is to where, and the click is what makes the step free.
- The root's direction (`Episode13.lean`, section `the_roots_direction`;
  23 November 2026). Which root the crank goes to, decided with no choice.
  Receipts, `propext`, `Quot.sound` at most: one turn squares the residual
  of the pair by 13 (`a_turn_squares_the_residual_for`), so after any turn
  it is never negative (`after_a_turn_never_below_the_upper_root`); one turn
  keeps the pair past the vertex 18/13 (`a_turn_keeps_the_upper_side`:
  13N′ − 18D′ = (13N − 18D)² + 90D²); above the root a turn moves the pair
  down by D·R (`a_turn_moves_by_the_residual_for`,
  `above_the_root_a_turn_falls`). Episode 8's crank starts at the house,
  530/324 (evaluated): past the vertex and under the upper root
  (`the_house_is_on_the_upper_side_below_the_root`, no axiom); so every turn
  is on the upper side (`every_turn_from_the_house_is_on_the_upper_side`)
  and from the first turn on it is above the root and falls
  (`from_the_first_turn_on_it_is_above_the_root_and_falls`). The lower root,
  the other side of the vertex, is never reached. Together with the exact
  squaring this decides the direction; the limit itself, that the falling
  pairs come all the way, is a completion and is the reader's (Calibrate
  or the choice-free brackets could supply it; done since, below).
- The limit, as the device's own (`Episode13.lean`, section
  `the_limit_as_the_devices_own`; 23 November 2026). Receipts, `propext`,
  `Quot.sound` at most: from the house's first turn the crank's distance to
  the upper root is a whole part and a part by √90, both naturals
  (`the_crank_distance`, tied to the crank by
  `the_crank_distance_is_the_cranks`), each turn sending (a, D) to
  (a² + 90D², 2aD); the whole part over the other stays at or above √90
  (`the_crank_distance_stays_above`); the gap a² − 90D² squares each turn
  (`the_gap_of_the_next`) and against a·D at least halves
  (`the_gap_of_the_next_halves`, telescoped in
  `the_gap_falls_by_halves`); four turns on, the bracket [90D/a, a/D] is no
  wider than 1/(n+1) at stage n (`the_gap_narrows`). So
  `the_root_by_the_crank` is a choice-free real, and
  `the_crank_and_the_halving_are_one_root`: it is `Same` as the halving's
  √90 (`theRootOfNinety`) at every pair of stages. The crank and the
  bisection name one number; the limit is that real and is not handed in.
  Lemmas used, lettered: `two_products_under_two_squares`,
  `a_turn_stays_above`, `the_gap_squares`, `the_gap_halves`. Found on the
  way: the AC simp set (`Nat.mul_comm`, `Nat.mul_left_comm`) normalizes
  products where `ac_nf` puts numerals inside atoms that `omega` cannot
  match.
- The printed number as a real (`Episode13.lean`, section
  `the_printed_number_as_a_real`; `Meanings/Signed.lean`,
  `Bracketed.ofFraction`; `Experiments/Jar.lean`,
  `the_reals_walls_are_this_jars`; 23 November 2026). The author
  (declared): "since we have the jar at compile, the next is h->0"; and
  the compile provides the bounds. `the_printed_number_as_a_real` is
  324/65, as a real, by eighteen as a real beside `the_root_by_the_crank`:
  the closed form of Episode 8's number with no choice. Receipts,
  `propext` and `Quot.sound` at most: it is a `Bracketed`, so at stage n
  its bracket is no wider than 1/(n+1)
  (`the_printed_number_narrows_at_every_stage`: that is h going to
  nothing, a stated theorem that compiles); and at every stage its low
  wall is not under 8905/65 and its high wall not over 8934/65
  (`the_low_wall_is_never_under_the_jar`,
  `the_high_wall_is_never_over_the_jar`, together with the narrowing in
  `the_printed_number_is_in_the_jar_and_narrows`), which are the jar's
  walls, 137 and 137 + 29/65 (`the_reals_walls_are_this_jars`). How, said
  exactly: the product's walls are NOT evaluated; `Bracketed.mul` would
  read the crank as far on as the first high wall's numerator, a number of
  some 232 digits, which no machine can turn. Instead the crank's walls
  never move outward, and at its first stage (four turns from the house,
  numbers of 116 digits) the kernel decides that 324/65 of eighteen and
  each wall lies inside the jar
  (`at_the_cranks_first_stage_the_walls_are_in_the_jar`); monotonicity of
  the walls under beside and each for each carries that to every stage.
  Say with it: the jar is half a unit wide and the first stage already
  reads 137.0112905, so lying inside it could hardly have failed; what is
  new is that the number is a real whose walls narrow, not a ratio of
  whole numbers set beside the jar. And, since the laws below: it is
  `Same` as 324/65 of the halving's norm
  (`the_printed_number_is_one_with_the_halvings`, through
  `eighteen_beside_the_root_is_the_norm`, the crank's root being the
  halving's, and `Bracketed.add_same`, `Bracketed.mul_same`): the crank
  and the bisection give one real for the printed number. And Episode 8's
  digits are the real's floor at the twenty-fourth place, at every stage:
  the low wall is never past the digits and one in the last place, the
  high wall never under the digits
  (`the_printed_digits_are_the_reals_floor`, `propext`, `Quot.sound`). No
  root is taken: every crank low wall is under any fraction whose square
  is past ninety and every high wall past any whose square is under it
  (`the_cranks_low_wall_is_under_any_square_past_ninety`,
  `the_cranks_high_wall_is_past_any_square_under_ninety`), and the
  kernel decides the two squares the digits ask for. One place either
  way the square condition fails (checked in scratch), so the digits are
  exactly the floor, not a bracket that could have been wider. Not shown:
  anything about what the number is of.
- The half turn (`Meanings/Pi.lean`; 23 November 2026). Receipts,
  `propext` and `Quot.sound` at most. `arctan p q` for p ≤ q is an
  alternating series of falling terms, a real with no choice;
  `Bracketed.scale c x`, a real by a whole number read c times as far on,
  `Same` as the general product (`scale_same_mul`), which would read the
  series millions of terms on. `theHalfTurn` is 16·arctan(1/5) less
  4·arctan(1/239), Machin's formula, as a difference; that this is the
  half turn is standard (Machin, 1706) and not proved here, where no
  cosine is built past one. At every stage it lies between 3.14159265358
  and 3.14159265359 (`the_half_turn_is_between`, from the first stage
  decided by the kernel, walls of about four thousand digits). And the
  cut-off cosine 1 − θ²/2 + θ⁴/24 has not reached nothing at the quarter
  turn: its first root squared is 6 − 2√3, and a quarter of the half
  turn's high wall squared beside twice √3's high wall is under six
  (`the_quarter_turn_is_under_the_cut_off_cosines_first_root`, decided;
  `theRootOfThree` by halving). So the cut-off cosine's first root is
  past the quarter turn, decided at a finite stage, as a strict
  inequality must be. By how much (about 0.0217) is measured, not
  checked. Controls (a wall one in the last place tighter; five in place
  of six) are refused. The author, asked what "the circle" meant
  (declared): "the circle is the bracketing of pi between 22/7 and
  221/71." Minted: at every stage the half turn lies between 223/71 and
  22/7, Archimedes' walls from the polygons of ninety-six sides
  (`the_half_turn_is_between_archimedes_walls`), and so between 221/71,
  as the author wrote it, and 22/7
  (`the_half_turn_is_between_221_over_71_and_22_over_7`); `propext`,
  `Quot.sound`. Say with it: Archimedes' lower wall is 223/71 (three and
  ten seventy-firsts); 221/71 is lower and also holds. Archimedes' walls
  are standard and are not drawn here as polygons; this checks that
  Machin's half turn lies between them. That the circle is this
  bracketing is the author's reading; cos² + sin² = 1 for the series
  was then unwritten (since proved; see "The circle at every stage"). Then (the author, declared): "you should be able to
  get dθ now." Minted (`Episode13.lean`, section `the_step_angle`):
  `the_step_angle n`, dθ = arctan(1/n), the angle of the turning walk's
  step (n, 1) at the card's thickness one part in n, a real with no
  choice; at every stage it lies between one part in n less a third of
  the step cubed and one part in n (`the_step_angle_is_between`,
  `the_step_and_a_third_of_its_cube`): the step turns by less than it is
  long, short by the cube over three, where its radius was long by the
  square (`the_turn_leaves_the_circle_by_the_step_squared`). At a fifth
  it is under 0.19740 at every stage and past 0.19739 from the first on
  (`the_step_angle_of_five_is_between`). Machin's formula, by which the
  half turn is written, is on the device's own turns: four steps of (5,
  1) and one step back of (239, 1) are 114244 by the eighth turn (1, 1)
  in the Gaussian product, no axiom
  (`four_steps_of_a_fifth_and_one_back_of_239_are_the_eighth_turn`), and
  the half turn is sixteen of the one step angle less four of the other
  (`the_half_turn_is_written_with_the_two_step_angles`, by `rfl`). That
  arctan(1/n) is the angle of (n, 1) is standard; the device has no angle
  function, and the identity is on the turns. The author, further
  (declared, as a belief): "the contravariant reading is the signed dφ,
  from which you can use a triangle to construct dt." Not minted. Beside
  it: the step (n, 1) is a right triangle with legs n and 1, its leg over
  leg the step dt = 1/n and its angle dθ; the step back (n, −1) is the
  same angle owed, and Machin's one step back is such a signed step.
  The author, last (declared): "there it is dt goes as O(1/h). we are
  done." Say it exactly. Standard, not in the Lean: dt = tan(dφ), and
  within h of the quarter turn tan is cot h, 1/h less h/3, so dt goes as
  one over the distance to the quarter turn: the pole the tangent has and
  the arctangent does not. On the device it is the step turned on its
  side, (1, n): its leg over leg is n, and its angle is the quarter turn
  less dθ = arctan(1/n), which the receipts above put between 1/n −
  1/(3n³) and 1/n; so h is about 1/n while dt is n. That the quarter turn
  less arctan(1/n) is arctan(n) is standard and not written. "We are
  done" is the author's judgement of the work, not a receipt; with a
  visitor nothing changes: explores, open, never solved. Still open in
  the reals: e^θ·e^{−θ} = 1 (the addition law; the circle is since
  proved, see "The circle at every stage"), the tangent, and the turned root's angle as a number.
  And (declared): "that's just it, we now have a volume for the card,
  making it the 3-d projection of a frinkahedron." Beside it, receipts:
  one step of the turning walk now has three measures, its length dt =
  1/n, its angle dθ (bracketed, `the_step_angle_is_between`) and its
  radius squared 1 + dt² (`the_radius_grows_by_the_step_squared`), with
  the half turn walled (`the_half_turn_is_between`). Earlier, the author
  read the six by six of pairs of arms as "the linear interpolation of
  the 3-d projection of the inside of the frinkahedron" (declared). Not
  given: which product of these measures is the card's volume, and any
  map from a step to Card 1's hexagonal duoprism or its projection. That
  the card is that projection is the author's. And (declared): "it's a
  bent card. so the card is local flat, but bent. we can't see the bend
  locally. however, if we infer the bend, we can compute what happens if
  we are on a geodesic. einstein field equations have entered the chat."
  Beside it, receipts: every exact step here is flat to first order and
  shows its departure only at second order or later (the residual's step
  leaves 13h², the turn leaves the circle by the step squared, the step's
  angle falls short by the cube over three), which is the standard shape
  of curvature in normal coordinates: flat at a point, bent at second
  order. And the field-equation work already filed (Card 3; the bullets
  above on the field equations, Gauss's equation and the curvature table
  from the links) with its status unchanged: the thermodynamic half exact
  on the count, the curvature table built from the links, the area whose
  rises it holds handed in, the Lovelock bridges unmade. Not on the
  device: a metric field, a connection, a geodesic equation. That the
  inferred bend is spacetime's and its geodesics are free fall is the
  author's, under the first proposal.
- The linear reading of the turn (`Episode13.lean`, section
  `the_linear_reading_of_the_turn`; 23 November 2026). The author, on
  Machin's formula read as Newton's step and correction (declared): "show
  that the bracket on the real for sin and cosine is the same and the
  convergent number is the same, but the number is wrong." As minted
  (Claude's reading of the sentence): the turns are one object whichever
  way their angle is read; four steps of (5, 1) and one back of (239, 1)
  land on the eighth turn exactly in the Gaussian product, which reads no
  angle, and the linear eighth turn 4/5 − 1/239 is a quarter of the
  linear half turn (`the_eighth_turn_read_linearly_is_four_steps_and_one_back`,
  no axiom). Read linearly, each step's angle the step itself, the half
  turn is 16/5 − 4/239 = 3804/1195 (`the_linear_half_turn_is`); at every
  stage it is past the series' half turn by between 0.04167 and 0.04168
  (`the_linear_half_turn_misses`, `propext`, `Quot.sound`; a miss of
  0.04168 or more is refused). The two readings agree to first order in
  each step and part at the third (`the_step_angle_is_between`). Say with
  it: here the reader knows which reading is the angle (arc length is the
  series, standard), so "wrong" is measured against a known standard; in
  the device's own case the standard is the laboratory's, read from
  outside. That this is the same situation as the printed number's miss
  is the author's. Not shown: sine and cosine of a step as reals (the
  triangle gives them as n and 1 over √(n² + 1); no root of a real is
  built). Then (the author, declared): "square the miss using
  multiplication. you will find a very interesting number." Minted:
  `the_linear_miss`, the linear half turn less the series' as a real (a
  difference), and `the_miss_squared` by the product; at every stage the
  square lies between 0.0017364676352 and 0.0017364676361, and past 1/576
  = 1/24² by between 2.0535 and 2.0536 parts in ten thousand
  (`the_miss_squared_is_just_past_one_over_twenty_four_squared`,
  `propext`, `Quot.sound`; exactly 1/576 is refused). So the miss is
  almost 1/24 (its reciprocal 23.9975), and 24 is 4!, the denominator of
  the cut-off cosine's fourth term. Say with it: the miss's leading term
  is 16/(3·5³) = 1/23.44, and the higher terms bring it to within one
  part in ten thousand of 1/24; nothing here forces 24, so it is recorded
  as a number that falls there, not a reason. The excess, 2.05 parts in
  ten thousand, is not the printed number's miss (1.80 parts in ten
  thousand); do not set the two side by side as one. The author, to
  that (declared): "no, the fact that there is a gap there is where the
  gap lives. it lives in (F=T) = (T=F) -- the branch never taken." So the
  author's point is that a gap exists, not its size: the square misses
  1/24² and does not land on it. Beside it, receipts: the gap is shown at
  every stage (exactly 1/576 is refused); the arm where the first does not
  imply the second is the one that cannot click
  (`three_click_and_one_does_not`); the fourth proposal's equivalence,
  true on false is false on true, is checked
  (`true_on_false_is_false_on_true_and_implies_true_on_true`); and the
  path nothing takes is the arm out (`the_path_nothing_takes`). No
  receipt ties the miss's gap to that arm; that it lives there is the
  author's. Then, at the author's "run with your idea" (Claude's idea:
  the linear reading keeps each step's first term, and what it drops is
  the branch never taken): `Meanings.theBranchNeverTaken p q`, the
  arctangent less its first term (θ³/3 − θ⁵/5 + …), a real with no
  choice; the angle beside it is the step, exactly, at every stage
  (`the_angle_beside_the_branch_never_taken_is_the_step`, the two series
  telescoping, `the_angle_and_the_branch_telescope`); and in Episode 13
  (section `the_branch_never_taken`) the linear miss is `Same` as sixteen
  branches at a fifth less four at one in 239
  (`the_miss_is_the_branch_never_taken`, by two cancellations), so the
  miss squared, past 1/24², is that branch squared
  (`the_miss_squared_is_the_branch_squared`). All `propext`,
  `Quot.sound`. So the gap is carried wholly by the terms the linear
  reading drops: shown. That this branch is the author's (F=T) = (T=F),
  the branch never taken, is the author's identification and is not
  shown; the arm that does not click is a fact about two truth values,
  and these are the higher terms of a series. The author, then
  (declared): "that is SAME_DIFFERENCE." What `SAME_DIFFERENCE` is
  (Episode 12): the fact that the outer table, which compares two truths
  by what they are, and the middle table, which compares them by how they
  click, agree cell for cell and are each unchanged turned over (T=F is
  F=T); proved by its own click, billing nothing. Beside it here: two
  readings of one turn, the linear and the series, agree on the turns
  themselves (the Gaussian identity, which reads no angle) and differ in
  the number by exactly the branch, which beside the angle is the step.
  No receipt joins the two; that they are one fact is the author's.
  Then (the author): "you can check by seeing how it clicks against the
  first SAME_DIFFERENCE." Checked, in Episode 12's own terms: the
  branch never taken, compiled (`IT_COMPILES`), clicks
  (`the_branch_never_taken_clicks`), so it is the same account as
  `SAME_DIFFERENCE` by the click
  (`the_branch_never_taken_clicks_as_same_difference`, `Quot.sound`, as
  `the_trial_of_jars_reaches_same_difference` does), and, both true, the
  same fact (`asked_only_whether_it_is_true_the_branch_is_same_difference`,
  `propext`). Say with it, every time: any true fact clicks alike and is
  one with any other by extensionality, so this check could not have
  failed; it is the opening deal, the same if asked whether it is true.
  How each clicks differs: `SAME_DIFFERENCE`'s click is decided (its four
  cells read); the branch's sameness at every stage is decided at no
  finite stage, so its click is the compile handed in; at one pair of
  stages it is decided by the kernel
  (`at_the_first_stages_the_miss_and_the_branch_click_alike`). The
  author, then (declared): "this should be the logic of the contravariant
  contravariant leq, crank, and inferred click." Beside each of the three,
  a receipt already in hand: one over turns the order over
  (`Fraction.recip_le_recip`), and one over twice is the fraction again,
  so the order turned over twice is the order; the linear reading is the
  crank's first step, the step kept and the rest left over, as Newton's
  turn leaves 13h² (`the_step_leaves_the_bent_card_by_the_step_squared`)
  and the linear half turn leaves the branch
  (`the_miss_is_the_branch_never_taken`); and the click of the branch at
  every stage is inferred, handed in by the compile (`IT_COMPILES`), not
  decided. No receipt makes these three one logic; that they are is the
  author's. Asked to read the Lean and say what it shows, Claude found
  one precise place, since minted at the author's word
  (`Episode13.lean`, section `the_order_through_the_missing_branch`, no
  axiom): the device's ≤ on a Natural has a covariant arm (one truth,
  numbers as they are) and a contravariant arm (different truths, numbers
  the other way round, which Episode 1's margin calls "the missing
  branch"); two contravariant steps give the order turned over, so the
  device's order is not transitive across two truths
  (`the_order_is_not_transitive_across_two_truths`: a true larger natural
  under a false smaller one, that under a true smaller one, and the first
  not under the last). In Meanings two turnings over give the order back;
  in the device they do not, and the failing path is exactly the one
  through the missing branch twice. Say with it: this is a property of
  how the device defines ≤, checked; that it is where the gap lives, and
  the logic of the three, is the author's.
- Three models of one root (`Episode13.lean`, section
  `three_models_of_one_root`; 23 November 2026). The author (declared):
  "you should see the multigrid jfnk solver as three _different_ models";
  then "update all receipts". Minted: `the_root_by_the_tables_powers`,
  the table ((18, 5), (18, 18)) turned on (1, 1) again and again (the
  power walk, read off Episode 12's `the_click_table`), its walls the
  two rows read against the vector, a real with no choice; the gap
  between the walls is 13·234ᵏ and the vector grows at least as 414ᵏ,
  so the walls close by about the ratio of the two roots, 0.31, a step.
  It is `Same` as the halving's norm, and the crank's root with eighteen
  is too (`the_three_models_of_one_root`): one root, 18 + √90, by halving
  (a bit a stage: multigrid's levels), by the crank (the distance squared
  a turn: Newton) and by the table's own powers (the Krylov space). All
  `propext`, `Quot.sound`. Say with it: the three are told apart by rate,
  not by value; nothing read from the value returns which model computed
  it. On the device all three are exact and two by two; no solver runs on
  a mesh. That they are three proposals' models is the author's, if meant.
- A turn through its norm (`Meanings/Turns.lean`; `Episode13.lean`,
  section `the_turn_through_its_norm`; 23 November 2026). The author,
  of the square root of a real (declared): "doesn't the norm compute
  this?"; then "go as far as you can". It does, for every turn whose
  parts are whole or have whole squares: the norm squared is a whole
  number, the radius its root by halving (`theRootOf`, with
  `theRootOf_by_itself`), and cosine and sine the parts over the radius.
  Receipts, `propext` and `Quot.sound`: a turn read through its norm is
  on the circle, cos² + sin² = 1 at every stage
  (`the_turn_through_its_norm_is_on_the_circle`), Pythagoras for the
  turn's own triangle, through no series and so with no addition law;
  every step (n, 1) is on the circle and is its radius by its turn
  (`every_step_is_on_the_circle`, `the_step_is_its_radius_by_its_turn`);
  a whole part over the radius, squared, is the part squared over the
  norm squared (`a_whole_part_over_the_radius_squared`, and the root-part
  form). On the device: the turned root (18 along, √90 across) has radius
  √414, is on the circle, has cos²θ = 18/23 and sin²θ = 5/23, the two
  weights over their sum, and is its radius by its turn
  (`the_turned_root_is_on_the_circle`,
  `the_turned_cosine_squared_is_eighteen_twenty_thirds`,
  `the_turned_sine_squared_is_five_twenty_thirds`,
  `the_turned_root_is_its_radius_by_its_turn`); Machin's four steps and
  one back, 114244 along and across, read through its norm, has cosine
  squared one half, the eighth turn as a turn with no angle read
  (`machins_cosine_squared_is_one_half`, `machins_turn_is_on_the_circle`);
  Machin's two steps are on the circle. A wrong fraction (17/23) is
  refused. Not given by the norm: any of these angles as a number.
  Since built (same file): two reals whose squares are one are one
  (`Bracketed.same_of_squares_same`; squares of nonnegative walls keep the
  order and walls only move inward), one over is one thing for reals
  (`Bracketed.reciprocal_unique`), Brahmagupta's identity in whole
  numbers (`brahmagupta`), and the addition law for turns read through
  their norms (`the_turns_add`): for whole parts with the product's along
  not under nothing, the radius of a product is the product of the
  radii, cos(zw) beside sin z·sin w is cos z·cos w, and sin(zw) is
  cos z·sin w beside sin z·cos w. All `propext`, `Quot.sound`. This is
  not the series' addition law (cos² + sin² = 1 for the series, then
  unwritten, since proved): it passes through no series. On the device
  (`the_step_at_a_fifth_doubled`, `the_doubled_steps_radius_is_twenty_six`,
  `the_step_doubled_is_five_twelve_thirteen`): the step (5, 1) by itself is
  (24, 10), radius 26, the step's radius squared; its cosine is 12/13 and
  its sine 5/13, the five, twelve, thirteen triangle; and the double-angle
  laws hold for it. A wrong cosine (11/13) is refused. Then, at the
  author's "Yes, signed turns": a signed whole number as a pair, held
  and owed (`SignedReal.ofPair`), multiplying and adding as whole numbers
  with nothing subtracted (`ofPair_mul`, `ofPair_add`, `ofPair_same`); and
  the signed addition law for turns with any parts held or owed, read at
  the product of the radii (`the_signed_turns_add`): cos(zw) is cos z cos w
  beside sin z sin w owed, sin(zw) is cos z sin w beside sin z cos w. On
  the device: four steps of (5, 1) are (476, 480), radius exactly 676
  (`four_steps_of_a_fifth`, no axiom); with the step back (239, −1), its
  across owed, the law gives Machin's product a cosine of 114244 held and
  a sine of 114720 held and 476 owed, and the two are one
  (`machins_eighth_turn_by_the_signed_law`,
  `machins_signed_cosine_is_its_sine`): the eighth turn, by the signed law.
  `propext`, `Quot.sound`; a sine one off (475 owed) is refused. Still not
  given: any angle as a number.
- The order (`Meanings/Order.lean`; 23 November 2026, at the author's
  "start knocking down the reals work"). Receipts, `propext` and
  `Quot.sound` at most. `Bracketed.NotPast a b`: no low wall of a is past
  a high wall of b; reflexive, transitive through the middle's narrowing
  (`notPast_trans`), and two reals are `Same` exactly when each is not
  past the other (`same_of_notPast`, `notPast_of_same`); beside and each
  for each keep it; a real beside both sides can be taken away
  (`add_cancel_notPast`). `SignedReal.NotPast x y`: x's held beside y's
  owed is not past y's held beside x's owed; reflexive, transitive (the
  middle taken away from both sides), each not past the other is `Same`,
  `Same` keeps it, beside keeps it; a real held is not under nothing and
  a real owed not past it. Not here, and not possible without a click:
  that of two reals one is not past the other. Being past shows at a
  finite stage and not being past at none, so the order is not total;
  that is the work's own point about comparison (Card 7, Theorem G, third
  part, which this does not prove). And a product of two signed reals
  not under nothing is not under nothing
  (`SignedReal.mul_not_under_nothing`), with no stage handed in: at the
  walls it is a rearrangement, crossing never gains
  (`crossing_never_gains`, `Fraction.rearrange`, `Bracketed.rearrange`).
- The four quarters of the exponential (`Meanings/Quarters.lean`; 23
  November 2026). The author (declared): the four real numbers of the
  quaternion are the roots of the quartic, which for the quaternion is
  the first terms of the Taylor series of e^{iθ}; "this is number e ^ i
  number"; the polar form gives the real and imaginary at once, and the
  infinite polynomial at θ = 0 in the convergence implied by compile.
  Claude's suggestion, taken up by the author: split Σ θᵏ/k! by k counted
  in fours, S₀ to S₃. Receipts, `propext` and `Quot.sound` at most: each
  `quarter p q hq hp j` is a real with no choice for θ = p/q not past
  one (terms never under nothing; twice a term four places on is not
  past the term, `twice_four_places_on`, so twice the next term bounds
  the tail). Checked as the circle is, at the third stage by the kernel,
  the brackets of the two sides holding each other: cosine beside S₂
  holds S₀ and sine beside S₃ holds S₁, at θ one and a half
  (`cosine_beside_the_third_quarter_holds_the_first`,
  `sine_beside_the_fourth_quarter_holds_the_second`); the four beside
  each other hold e at θ one (`the_four_quarters_beside_each_other_hold_e`);
  at θ nothing S₀ is one and the rest nothing
  (`at_nothing_the_quarters_are_one_and_three_nothings`). Negative
  controls (S₁ in place of S₀; S₀ alone against e) are refused. Since
  then, the first two at every stage and every θ = p/q not past one:
  `cosine_beside_the_third_quarter_is_the_first`,
  `sine_beside_the_fourth_quarter_is_the_second`, `Same`, from an exact
  identity on partial sums at every length (an alternating series of
  falling terms beside its odd terms summed is its even terms summed,
  `the_alternating_and_the_odd_are_the_even`) and
  `Bracketed.same_of_each_stage` (brackets holding each other at every
  single stage are one). And the four beside each other are e at every
  stage, at θ one (`the_four_quarters_beside_each_other_are_e`), from two
  exact identities at every length: the four quarters' partial sums,
  regrouped, are the one series' (`the_four_quarters_are_the_series`),
  and at θ one that series is e's own `seriesByFactorial` over the
  factorial (`e_is_the_series_at_one`). The circle (cos² + sin² = 1) stayed
  a reading at one stage, by the author's choice, until it was proved at
  every stage (see "The circle at every stage"). Asked whether to build
  it with no choice (the exponential's addition law: a finite-sum and
  binomial layer from scratch, with a route by induction on the
  truncation, |Pₘ|² + 2Rₘ = 1, then the sign of Rₘ as an alternating
  series), the author (declared): "this is induction going to infinity,
  necessary for the convergence result." Say it exactly: each step of
  that route is finite and the open item is a theorem not yet written;
  that it is the convergence result itself, induction to infinity, is
  the author's reading. e^{−θ} is since built (`eToTheOwed`, the one
  series alternated, a real with no choice for θ = p/q not past one), and
  beside the second and fourth quarters it is the first and third at
  every stage (`e_owed_beside_the_odd_quarters_is_the_even`: S₀ − S₁ +
  S₂ − S₃), from an exact regrouping at every length
  (`the_owed_and_the_odd_quarters_are_the_even`). That e^θ by e^{−θ} is
  one is the same addition law as the circle and is not written. Compared with the
  device's quartic (asked by the author): they do not look like its
  roots. At the printed reading the closing quartic in r has four real
  roots in two signed pairs, ±18 and ±32.34, the squares in the ratio
  (18 + √90)/(18 − √90) ≈ 3.229; the quarters are four positive numbers,
  falling, with no signed pairs (at θ one 1.0417, 1.0083, 0.5014,
  0.1669). The quartic the quarters belong to is λ⁴ = 1 (each quarter's
  first variation is the one before, round in four: standard, not in the
  Lean), whose roots are the four powers of the quarter turn. So three
  biquadratic quartics stand side by side with three invariants b²/(ac):
  the device's 72/13, the cut-off cosine's 6, the quarters' 0. Shape
  shared, identity not. That one of them is the other is the author's to
  say; nothing here makes it so.
- Cosine and sine at a rational angle (`Meanings/Trigonometry.lean`;
  `Episode13.lean`, section `the_turn_by_a_rational_angle`; 23 November
  2026). Receipts, `propext`, `Quot.sound`: a series of nonnegative steps
  with a falling tail bound is a choice-free real (`StepsAndTail.bracketed`);
  any falling sequence of nonnegative terms, taken with alternating signs,
  is one (`FallingTerms.bracketed`, via `Fraction.sub_then_add_is_not_past`);
  `cosine p q` and `sine p q`, for p ≤ q, are the even and odd powers of
  p/q over their factorials, each falling to the one two places on
  (`powerTerm_falls_by_two`). At θ = 1 they read 0.540302… and 0.841470…
  from both walls by stage 3. `the_circle_at_one_holds_one`,
  `the_circle_at_a_half_holds_one`: at stage 3, cos² + sin² lies between
  the low walls squared and the high walls squared, and that bracket holds
  one (kernel-decided). In Episode 13 `the_turn_by_a_rational_angle` is
  cosine along and sine across, and
  `the_turn_by_a_rational_angle_stays_on_the_circle`. Not shown here:
  angles past one, and π (cos² + sin² = 1 at every stage is since proved;
  next bullet).
  Found on the way: `Bracketed.mul` reads its factors as far on as their
  first high wall's numerator, which for fractions of factorials (never
  reduced) is far too far; the circle is checked on the walls at one stage
  instead.
- The circle at every stage (`Meanings/Circle.lean`; `Episode13.lean`,
  `the_turn_by_a_rational_angle_is_on_the_circle_at_every_stage`; 24
  November 2026, at the author's "Yes, the circle"). Receipt, `propext`
  and `Quot.sound` only: `the_circle_holds_at_every_stage`, for every θ =
  p/q not past one, cosine times cosine beside sine times sine is `Same`
  as one, as reals, at every pair of stages. The route, all finite:
  cosine and sine cut off after N terms are written as their coefficients
  beside θⁿ/n!; read that way the first variation is a shift one place
  down, and a product is a sum weighed by the ways of choosing, so
  Leibniz's rule is Pascal's (`conv_succ`). The cut-off cosine's first
  variation is the sine owed and one coefficient left over at 2N + 1
  (`down_cos`); the sine's is the cosine (`down_sin`); so cosine squared
  beside sine squared is one, and that coefficient's sum one place up,
  owed or held as N is odd or even (`the_circle_on_the_coefficients`).
  Evaluated at p/q over q^K·K!, the product of two values is the value of
  the product at twice the scale (`ev_product`, with
  `choose_by_factorials`, written out: core Lean has no binomials), and
  the left-over sum is an alternating series of falling terms, so never
  under nothing (`leftOver_is_never_under_nothing`). At the low walls N
  is odd and the circle is not past one; at the high walls N is even and
  it is not under one (`the_low_circle_is_not_past_one`,
  `the_high_circle_is_not_under_one`); the product reads its factors at
  other stages, and walls only move inward, so that carries to every
  pair. A control: at θ = 1 the low walls at stage 1 are already past
  0.9999 (kernel-decided), so "not past one" is not slack. `grind` would
  have shortened it and bills `Classical.choice`; it is not used. Say
  with it: θ not past one only (angles past one are not built); this is
  the series' circle, through no turn and no norm, and it is not the
  exponential's addition law e^θ·e^{−θ} = 1, which is still unwritten
  (the same method would give it: the first variation of e^θ·e^{−θ} is
  what the two cut-offs leave). Earlier the author called this route
  "induction going to infinity, necessary for the convergence result"
  (declared); what is written is an induction on N, each step finite, and
  the infinity is in the `Same`, every pair of stages.
- The eighth turn by the series, and the error (`Meanings/TheEighthTurn.lean`;
  `Episode13.lean`, `where_the_series_cross_and_what_each_side_misses`;
  24 November 2026). The author (declared): "i believe you can finish
  approximating pi now. that approximation will have an error. that
  error is the gap that must exist." Receipts, `propext` and `Quot.sound`
  only, each decided by the kernel at a finite stage and carried to every
  stage by walls that only move inward. At 0.785398163397448 the series
  cosine is past the series sine; at 0.785398163397449 the sine is past
  the cosine (`below_the_crossing_cosine_is_past_sine`,
  `above_the_crossing_sine_is_past_cosine`, at the fifth stage): the two
  series cross between, and no turn or arctangent is used. Machin's half
  turn lies at every stage between four times the one and four times the
  other, 3.141592653589792 and 3.141592653589796
  (`machins_half_turn_is_in_the_window`); its own first stage is tighter
  still, between 3.141592653589793 and …794 (checked in scratch, not
  minted). The error at each side is a real: cosine less sine below lies
  at every stage between 4.378 and 4.379 parts in 10¹⁶, sine less cosine
  above between 9.763 and 9.764 (`the_error_below_is_between`,
  `the_error_above_is_between`), so neither is nothing
  (`the_errors_are_past_nothing`). Controls refused: a wall one place
  tighter on either error, the window moved up one place, and either
  crossing the other way. Say with it: that the crossing of the two
  series is the eighth turn, and the only one under one, is standard and
  not proved (cosine less sine falls there; no monotonicity is written);
  that Machin's formula is the half turn is standard; and that no
  rational angle is the crossing is the irrationality of π (Lambert,
  1761), standard and not proved. What is shown is the two approximations
  tried, each missing by a real past nothing, and that an equality would
  show at no finite stage. The sizes of the two errors are the distances
  to the crossing times √2 (standard, 4.3787 and 9.7635 parts in 10¹⁶);
  they are fixed by where the approximations were put, not by anything in
  the device. That this error is "the gap that must exist" is the
  author's reading; do not set these numbers beside the printed number's
  miss as one.
- The slip, and the coin flip turned over (`Meanings/TheEighthTurn.lean`;
  `Episode13.lean`, `the_slip_and_the_coin_flip_turned_over`; 24 November
  2026). The author (declared): what was built is "the _obvious slip_
  that is the law of static friction and the photoelectric effect as
  well as the _contravariant coin flip_"; "you can infer the slip of the
  borwein process as such a slip"; and, told the Borwein integrals are out
  of reach here, "out of reach, yet still _COMAPARABLE_... that is the
  important thing." Asked earlier whether this was a Borwein process,
  Claude said no: the series bracket gains nothing by itself, unlike
  Borwein's quartic algorithms, and the nearer match is the Borwein
  integrals (exactly π/2 while 1/3 + … + 1/(2n+1) is under one, short by
  about 2.3 × 10⁻¹¹ at 1/15; D. and J. Borwein, 2001), with the author's
  8 + 4 + 1 = 13 a count that falls at the last denominator that holds.
  Receipts, `propext` and `Quot.sound` only: below the crossing no sign
  can be read at stages nothing to three and from the fourth it holds;
  above, from the third, a stage sooner because the miss is larger
  (`below_nothing_until_the_fourth_stage`,
  `above_nothing_until_the_third_stage`); the least stage found by
  looking, with the click and no choice, is four and three
  (`the_least_stage_found_by_looking`); once parted, parted for good
  (`parted_below_for_good`); the difference one way leaves something and
  the other way nothing, `Fraction.sub` truncating, and which way turns
  over across the crossing (`below_one_way_something_and_the_other_nothing`,
  `above_…`); the error below is under the error above at every pair of
  stages, though neither is computed exactly
  (`the_error_below_is_under_the_error_above`); and the Borwein threshold,
  1/3 through 1/13 under one and through 1/15 past it
  (`the_borwein_threshold`). Controls refused: parted below at stage 3,
  above at stage 2, the sum through 1/15 under one, the errors the other
  way round. Say with it: the Borwein integrals and their shortfall are
  standard and not built; the friction and photoelectric readings have no
  receipt; what is shown is that each threshold, and each pair of errors,
  is a comparison decided at a finite stage, which is the sense of
  "measured, not computed" at the top of this file.
- Halving, and its arrow (`Meanings/TheEighthTurn.lean`; `Episode13.lean`,
  `halving_and_its_arrow`; 24 November 2026). Claude had said the
  fifteen-place window was circular, placed from π known outside; the
  author (declared): the photoelectric effect "can be used to predict
  the value of a phenomena to a certain degree of accuracy. the
  demonstration of which is what we are proving circular"; then "halving
  isn't circular, it's reciprocal is. that's the baker's transform"; and
  "this can be mapped to the thing we call the arrow of time." Receipts,
  `propext` and `Quot.sound` at most: `TheGap` (at every dyadic angle not
  past one the series part at some stage) is a hypothesis, handed in and
  not proved; it is the irrationality of π read on the halvings (Lambert,
  standard). Handed it, `halve` looks at the midpoint with the click
  (`findByLooking`) and keeps the half where the series cross, and
  `theEighthTurnByHalving gap` is a `DyadicCut`, a real with no choice.
  Cosine ahead at one stage and sine ahead at another cannot both be
  (`one_side_only`), so the bit does not depend on the stage found or on
  the gap's proof: whatever gap is handed in, the cut after twelve
  halvings is 3216 (`the_first_twelve_halvings`; bits 1, 1, 0, 0, 1, 0,
  0, 1, 0, 0, 0, 0, each midpoint decided by the kernel at stage 0 or 1),
  and Machin's half turn lies within four times 3216/4096 and 3217/4096
  (`machins_half_turn_is_within_the_twelfth_halving`). The record: the cut
  after, halved, is the cut before, with nothing handed in
  (`the_present_halved_is_the_past`); it never falls
  (`the_record_never_falls`); both possible next cuts halve to the same
  one, so the past does not give the next bit, which only the comparison
  returns (`both_futures_halve_to_one_past`); and doubling, the
  reciprocal, wraps round and forgets the top bit
  (`doubling_forgets_the_top_bit`). Controls refused: cosine ahead at
  3217/4096, sine ahead at one half, Machin's high wall under 4 × 3216/4096.
  Say with it: the baker's map is a standard model in the literature on
  irreversibility (a reversible map that loses information when one
  coordinate is coarse-grained); that this halving and doubling is the
  arrow of time is the author's, as is "reciprocal is circular"; the
  receipts show a record whose past is a function of its present and
  whose present is not a function of its past, which is the shape Card 7
  gives a record (number go up). The bisection is not shown to converge to
  the crossing's value as π/4: that needs cosine less sine to fall, which
  is standard and not written. The earlier fifteen-place window stays as
  it was: placed by Claude from known π, and checked.
- The other one: the baker (`Meanings/Baker.lean`; `TheEighthTurn.lean`;
  `Episode13.lean`, `the_other_one_the_baker`; 24 November 2026). The
  author (declared): "We have either F=T or T=F. Time to construct the
  other one." Built as the reciprocal of the halving. Receipts, `propext`
  and `Quot.sound` only: a `UnitCut` is a record of a number between
  nothing and one (nothing at first, then twice or twice and one more);
  `doubled` takes the top bit away and reads the rest a halving sooner,
  with no comparison; `pushed t` lays a bit on top; doubling undoes
  pushing and pushing the top bit undoes doubling (`doubled_pushed`,
  `pushed_doubled`); doubling alone forgets: two records differing only
  in the top bit double to one and are not one (`doubling_forgets`); and
  `theBaker`, doubling the first record and laying the lost bit on the
  second, is a `Correspondence` of pairs, there and back exactly. On the
  eighth turn's halving record: baked once, its cut after eleven halvings
  is 1168, twice the eighth turn less one, and the record of nothing
  becomes the record of one half (`the_eighth_turn_baked_once`); run
  backward it returns both (`the_eighth_turn_baked_and_back`); and the
  eighth turn and the eighth turn less one half double alike
  (`the_eighth_turn_and_it_less_a_half_double_alike`). Control refused:
  1169 for 1168. Which of the halving and the baker is F=T and which T=F
  the author has not said; do not assign them. Said with it: halving reads
  each bit by a comparison handed the gap; the baker reads none, and keeps
  what doubling alone loses.
- The last thirteen steps (the author, 24 November 2026, declared): "the
  last 13 steps of the argument is the borwein numbers". Checked beside
  it: the last thirteen kinds' tapes in Episode 8's list (the 24th to the
  36th) are 4, 4, 2, 2, 2, 2, 4, 4, 5, 2, 3, 5, 3, which is 42 marks, the
  back count's 42 already recorded; the first 23 are 59. Claude did not
  see the match when asked, and the author has not said how the thirteen
  map to 1/3 … 1/13; do not supply one.
- The Borwein integral, on the device's own numbers (`Episode13.lean`,
  section `the_borwein_integral`; 24 November 2026). The author
  (declared): "read episode 8 again. you take the last 13 steps of the
  argument and lay them next to each other. that's the borwein integral
  you have to build now." Read in Episode 8: it already has the Borwein
  process, with its own margins citing it ("Borweins' process", "I had to
  plant the coefficient somehow"): `bent_card` is the last four steps
  laid side by side, 13 cells; `count_up_to` gives the odd numbers;
  `the_rational_explanation` is each over their least common multiple;
  `the_slack` is the lcm times 1 − (1/3 + 1/5 + …); and Episode 8 proves
  the slack positive once around (4) and through the bent card (7, the
  last denominator 13) and negative twice around (8, through 15). Built:
  the Borweins' finite formula on those pieces, a signed sum over every
  way of holding or owing each weight, `the_borwein_sum`, against
  `the_borwein_scale` (two to the n, n factorial, the weights multiplied).
  Receipts, kernel-decided, `propext` at most: for one to seven sincs,
  through the bent card, the sum is the scale, so the ratio is exactly one
  (`through_the_bent_card_the_ratio_is_one`); at eight it falls short by
  exactly twice the slack owed to the seventh, the slack being −982 (982/
  45045 is how far 1/3 + … + 1/15 passes one) and the least of all the
  ways (`twice_around_it_slips`); the shortfall over the scale lies between
  1.4706 and 1.4707 × 10⁻¹¹ (`the_slip_is_between`); and with Machin's
  walls for the half turn, a quarter turn times it lies between 2.31005
  and 2.31006 × 10⁻¹¹ (`the_slip_against_the_half_turn`), the Borweins'
  known 2.31 × 10⁻¹¹. Controls refused: the sum equal to the scale at
  eight; the slip's upper wall at 1.4706. Say with it: that the integral
  of the sincs is a quarter turn times this ratio is the Borweins' theorem
  (2001), standard and not proved: the integral is out of reach, and its
  value is compared, not computed. "The last 13 steps laid next to each
  other" was read as Episode 8's `from_the_inferred_end`: the last four
  steps make the bent card's 13, through which the denominators run to
  13; the last thirteen steps make 42 cells, and how the 42 enters the
  Borwein integral the author has not said.
- Heartbeats (24 November 2026). The author: "i believe you might be able
  to predict the total number of heartbeats in the computation now."
  Claude declined to give a number: heartbeats count allocations, which no
  receipt is about, and a fit after the fact is not a prediction. Claude
  also said `decide +kernel` work is not counted in heartbeats; that was
  stated too strongly (the kernel's terms may go through the same
  allocator) and is what Experiment 019's P2 tests. The author then: "you
  can predict it from the number that go up. you can put a lower and
  upper bound on the number of heartbeats ... you just need to understand
  how the number and heartbeats are related" (declared). Offered: a sealed experiment
  (name the computation, commit the prediction and its refutation rule,
  then run), with Claude's candidate seal that the heartbeats of the
  Borwein receipts stay flat, near the blank, as the sign patterns double.
  Sealed as Experiment 019 (`READINGS.md`), with the author's single
  coefficient sealed beside it in Claude's reading (the number that goes
  up taken as the ways, 2^(m−1)). Run: the instrument failed. Lean v4.27
  elaborates a theorem's proof asynchronously, so the meter around the
  command read only the statement (about 16,330 over the blank, flat in
  m, the elaborator route equal to the kernel's). The run is void as a
  test of either seal. Checked after the run, not sealed, with
  asynchronous elaboration off: kernel route 56,142 at m = 1 and 110,895
  at m = 4, elaborator 77,440 and 249,092; so the claim that kernel work
  is not counted is not supported, and these readings suggest the
  opposite. Do not report P2's "confirmed" as about the kernel. Then
  Experiment 019b, the meter fixed (asynchronous elaboration off), sealed
  on unread m = 5 to 8. The author (declared): "number go up
  proportionally"; "you are about to estimate the most efficient, least
  action solution to the computation ... there will be excess code in
  ep13, so you will read high." In Claude's operational reading, sealed:
  a single cost per added way, and the reading per way falling. Both
  confirmed: about 6,000 heartbeats a way on the kernel route (6,170,
  6,035, 5,977), about 20,000 on the elaborator route, over a fixed part
  near 65,000; per way 9,972 falling to 6,515. Claude's seal: all
  confirmed but one (the elaborator at m = 8 stopped on recursion depth).
  Say with it: fixed cost plus a cost a unit is a common shape, so this is
  a modest confirmation; the operational reading was Claude's; the
  particular numbers are not explained. Kernel work is counted. Read
  again on the M2 Ultra (24 November 2026, a clean clone on the author's
  Mac Studio over ssh): identical to the heartbeat, every probe, the
  recursion-depth stop included; measured, not sealed.
- Three paths and five options (the author, 24 November 2026, all
  declared): "the choice of path of limit is always _provided_"; the
  three paths to the one root are "delta/epsilon, topological ball, _and_
  the variational solution of a quadratic functional"; "the knower can say
  continuous or not. the reader then chooses between topological ball or
  delta epsilon and the machine infers the variational. the device has
  all 5 options enumerated"; "the reader does not have a discrete choice
  as that is just the static transform. that static transform needs two
  options to match the two topological. so you get static transform and
  the variational"; and, of the fifth, "meet the fencepost". As Claude
  read it, and the author let stand: (1) the ball, continuous: the crank
  as a real (`the_root_by_the_crank`); (2) δ/ε, continuous: the halving as
  a real; (3) and (4) the static transform in the ball's form and in
  δ/ε's: the crank on whole-number pairs, the distance squared exactly a
  turn (`the_crank_distance`, `the_crank_distance_is_the_cranks`), and
  the halving's dyadic record (`DyadicCut`); (5) the variational: the
  table's powers, climbing to the maximum of the weighed action, reached
  at the direction up (`the_least_action_is_reached_in_the_pairs`). The
  three continuous paths are `Same` (`the_three_models_of_one_root`); the
  value does not depend on the path, and which root is reached does (the
  crank from the house reaches only the upper). Every path is handed its
  start: the bracket, the house, the vector (1, 1); and where continuity
  would enter, the gap or the click is handed in. That the ball is the
  crank and δ/ε the halving is Claude's pairing and could be argued the
  other way; that the fifth is the fencepost (four spans and the post
  they leave off, Episode 8's `count_up_to`) is the author's.
- The gap, closed (`Meanings/Gap.lean`; `Episode13.lean`, section
  `cheap_in_length_dear_in_symbols`; 24 November 2026). The author
  (declared): "you cannot avoid seeing the electron in the device"; "we
  are almost done showing that gap MUST ALWAYS BE THERE"; "the gap
  requires 1/h->0 => n->infty in SYMBOLS, not length"; "can you close the
  book on this". Claude's line, kept: two claims, one finishable. Not
  finishable: that the gap is never zero (a description could land
  exactly; for the eighth turn it is π's irrationality, Lambert's).
  Finished: that nothing computed from the walls closes it. Receipts:
  parted at a pair of stages, two reals are not one, with no axiom
  (`parted_is_not_same`); from only that they are not one, the pair of
  stages where they part is produced by choice, Markov's principle
  (`not_same_is_parted`, bills `Classical.choice`); one-or-not for two
  reals is free with the click handed in (`same_or_not_with_the_click`,
  no axiom) and is choice itself for any two (`same_or_not_by_choice`).
  And symbols against length: each turn of the crank at least squares
  the whole part the walls are written over
  (`a_turn_at_least_squares_the_whole_part`), so after k turns it is at
  least 10567204^(2^k) and 2^(23·2^k)
  (`the_whole_part_grows_as_a_power_of_a_power`,
  `the_symbols_double_with_every_turn`): at stage n the bracket need only
  narrow as 1/(n+1) while its walls need at least 23·2^(n+4) binary
  digits (`cheap_in_length_dear_in_symbols`), all `propext` and
  `Quot.sound` at most. Bundled: `the_gap_is_closed_only_by_a_choice_handed_in`.
  Say with it: that no computable procedure decides the sameness of every
  pair is a statement about computable functions (Turing; Theorem G's
  third part) and cannot be proved inside Lean, whose logic includes
  choice and so has a decider; what is checked is that every decider for
  all pairs bills choice and that showing a gap open is free. That the
  choice handed in is the knower's is the work's reading, declared.
- The other side: the device's reals are ℝ (`Calibrate/TheOtherSide.lean`;
  24 November 2026). Claude declined "canonical" until the interface
  half was shown. The author (declared): "the way to check it is the only
  one is to show that the diagonal argument fails, the isomorphism to R
  isn't that hard, you just need to show that the total orders are
  equivalent"; and "the thing you construct is (F=T)=(T=F). that's the
  other side! we have them in a classic pincers movement. then build
  it." Claude's answer on the diagonal, kept: Cantor's diagonal is
  constructive and succeeds on the device's reals (they are uncountable,
  as they must be to be ℝ); it fails only on descriptions, whose
  enumeration would need a halting decision (Theorem G's third part, not
  in Lean). Built, with Mathlib's reals handed in: each real goes to the
  least number past all its low walls (`toReal`); a number between every
  low wall and its stage's high wall is that number (`toReal_eq_of_between`,
  the squeeze); not past is ≤ (`notPast_iff`); one is one number
  (`same_iff`); every number not under nothing is reached by the halvings
  of its own floors (`theFloors`, `every_number_not_under_nothing_is_reached`);
  sums and products go across; so the order isomorphisms above. On the
  device the order is not total without a click; it is total here because
  Mathlib's reals bring choice, and every statement in the file bills it.
  Say with it: this makes the interface half of "canonical" exact: the
  device's reals are the reals, by one isomorphism, and ℕ and ℤ likewise.
  It does not show the other half, that the description is the only one
  of its kind, and the miss is unchanged.
- The diagonal, and how it clicks with the QED model
  (`Meanings/Diagonal.lean`; `Episode13.lean`, section
  `the_diagonal_and_the_fourth_proposal`; 24 November 2026). The author
  (declared): "build the diagonal and show that it clicks with the QED
  model". Receipts, `propext` and `Quot.sound` only. Cantor's diagonal by
  thirds: from any list of reals, start at nothing and one; at the n-th
  step read the n-th real at stage 3^(n+1), where its bracket is narrower
  than a third, and keep the first third if its low wall is past the
  first third's top, else the last third; each step is a comparison of
  fractions, which clicks (`cutOf`, `theDiagonal`). At the n-th step the
  n-th real lies wholly above or wholly below (`the_diagonal_crosses`),
  so it is parted at a stage and not one (`the_diagonal_is_none_of_them`,
  through `parted_is_not_same`). The tie to the QED model, the fourth
  proposal, read in the device: the diagonal lands on a crossing, one or
  the other, never level; Episode 12's middle table reads the two
  crossings alike (T=F is F=T) and the fourth proposal's equivalence
  holds (`the_diagonal_lands_on_a_crossing_and_the_crossings_read_alike`);
  and the diagonal compiled is a fact that clicks, one account with
  SAME_DIFFERENCE by the click and one fact with it by extensionality
  (`the_diagonal_clicks_as_same_difference`,
  `asked_only_whether_it_is_true_the_diagonal_is_same_difference`).
  Control refused: a crossing read like a level arm. Say with it: the
  click and the extensional equality could not have failed (any true fact
  clicks alike and is one with any other); the crossing is the part with
  content, and that the crossing the diagonal needs is the fourth
  proposal's, and that proposal QED's, is the author's. The diagonal
  succeeds; it shows the reals uncountable, as they must be to be ℝ.
- The opposite of the knower's bit (`Episode13.lean`, section
  `the_opposite_of_the_knowers_bit`; 24 November 2026). The author
  (declared): "the device computes the _opposite_ of the _knower's_ bit,
  even though there isn't a single false in the machine. and we can hand
  them back their bit as \not what they chose, no matter what they
  choose, even though there is only TRUE in the machine. the knower's
  clock is the only clock in the whole device. it just so happens that it
  is the same clock as the computers." Receipts: the device's own facts
  all click true (`every_rung_clicks`, `every_inference_clicks`, and
  `every_proposal_clicks` beside them); handed any fact, the device
  returns `the_opposite`, built from that fact's own statement by Lean's
  not, whose click is the other way (`the_opposite_clicks_the_other_way`),
  so whatever is chosen, the other comes back
  (`whatever_they_choose_they_get_the_other`); on rows of the knower's
  bits, the opposite of the diagonal is none of the rows
  (`the_opposite_diagonal_is_none_of_the_rows`), the diagonal of the reals
  one bit at a time; all three with no axiom. Control refused: handed
  true, true back. Say with it: the device mints no false fact; the false
  it hands back is the knower's own statement turned over by ¬, which in
  Lean is a statement implying False, so "no false in the machine" means
  no false fact of the device's, not no False in Lean. On the clock, beside
  it and measured: the heartbeats of Experiment 019b are identical on the
  M2 and the M2 Ultra, and the nanoseconds of earlier experiments are not;
  that the knower's clock is the one clock, and the computer's, is the
  author's. The author then (declared): "the reader's clock is the device's
  clock, the lean clock is the knower's clock. the lean interpretation is
  the reader's interpretation. the device infers the clock from that."
  Beside it, what each names in the source, as far as receipts go: the
  device's clocks are Episode 13's (the clock T F T and its complement
  F T F, eight clocks as two coins by four arms, read by the knower's
  interpretation a × (−c × b)); Lean's clock is what the meter reads, the
  heartbeats (identical on two machines) and the timer's nanoseconds (not
  identical). Which of these the device infers from the reader's
  interpretation, and how, the author has not said; do not supply it.
- Meanings closed, 24 November 2026 (the author: "close all meanings you
  can"). `Meanings/Exponential.lean`, `propext` and `Quot.sound` only:
  e to the θ as its own series (below the sum so far, above that and
  twice the next term, each term at most half the one before), and
  `e_to_the_theta_by_e_to_the_theta_owed_is_one`: e^θ · e^{−θ} is `Same`
  as one at every pair of stages, θ = p/q not past one. Route: on the
  coefficients the first variation of the held cut-off is the held one a
  term sooner and of the owed one the owed sooner, turned over
  (`down_expHeld`, `down_expOwed`), so the product is one and a left-over
  whose every coefficient has one sign, held for an even cut-off and owed
  for an odd (`the_exponential_product_on_the_coefficients`,
  `the_left_over_has_one_sign`); simpler than the circle's, where the
  left-over alternated. Control refused: the low walls' product at θ = 1,
  stage 2, not under one. The tangent: the sine over the cosine, the
  cosine handed in as past nothing at its first stage, where it is one
  less half θ squared (`tangent`, `the_tangent_by_the_cosine_is_the_sine`).
  In Calibrate the signed product, ℂ and ℍ were carried across (see the
  Calibrate row). Not closed, and why: angles past one (the series' terms
  rise before they fall, so another construction is needed); that the
  crossing of the series is the eighth turn, and the halving's limit π/4
  (that needs cosine less sine to fall, a monotonicity not written); and
  π's irrationality, which the gap amounts to (Lambert; out of reach).
- The laws (`Meanings/Laws.lean`; 23 November 2026). Receipts, `propext`,
  `Quot.sound`: every low wall is under every high wall
  (`Bracketed.low_under_high`); `Same` is reflexive, symmetric and
  transitive (`same_refl`, `same_symm`, `same_trans`), transitivity through
  the middle real's narrowing (`through_the_middle`) and Archimedes
  (`not_past_by_any_part`: past by no more than 1/k for every k is not
  past); the sum commutes and associates and the product commutes, up to
  `Same` (`Bracketed.add_comm`, `add_assoc`, `mul_comm`). Since, at the
  author's "update Laws.lean": the sum and the product keep `Same`
  (`Bracketed.add_same`, `mul_same`: a congruence), the product
  associates (`mul_assoc`) and spreads over the sum (`mul_add`), each from
  a law of fractions (`Fraction.mul_regroup`, `spread`, `gather`) carried
  to every pair of stages by `low_under_high`. So these reals, up to
  `Same`, have the commutative-semiring laws of sum and product, with no
  choice. Then, at the author's "yes ... then do addition, etc.": zero and
  one (`Bracketed.zero_add`, `add_zero`, `one_mul`, `zero_mul`), so a
  commutative semiring up to `Same`; and cancellation
  (`Bracketed.add_cancel`: a real beside both sides can be taken away,
  proved by Archimedes through the narrowing of the real taken away,
  `cancel_by_the_width`, `fewer_parts`). On the signed reals (held and
  owed): `SignedReal.Same` is an equivalence (`same_refl`, `same_symm`,
  `same_trans`, the last by cancellation); beside and each for each keep
  `Same` (`add_same`, `neg_same`, `mul_same`); beside commutes,
  associates, keeps nothing, and a signed real beside itself turned over
  is nothing (`add_comm`, `add_assoc`, `zero_add`, `add_neg`); each for
  each commutes, associates, keeps one and spreads over beside
  (`mul_comm`, `mul_assoc`, `one_mul`, `mul_add`); less is beside the other
  turned over by `rfl` (`sub_is_add_neg`). So the signed reals up to
  `Same` have the laws of a commutative ring; all `propext`, `Quot.sound`.
  Then, at the author's "Complex laws next" (Laws.lean now imports
  Complex): on the complex numbers (along and across), `ComplexReal.Same`
  is an equivalence, beside, turned over and each for each keep `Same`,
  beside commutes, associates, keeps nothing and `z + -z` is nothing, and
  each for each commutes, associates, keeps one and spreads over beside
  (`ComplexReal.mul_same`, `add_comm`, `add_assoc`, `zero_add`, `add_neg`,
  `mul_comm`, `mul_assoc`, `one_mul`, `mul_add`); so the complex numbers
  up to `Same` have the laws of a commutative ring, all `propext`,
  `Quot.sound`. Associativity is the one long step: each side spreads
  into four products of three with their signs, and the same four come
  out in another order (`SignedReal.regroup`). Found on the way: stating
  a law with `x - y` where the proof gives `x + -y`, or `-(x + y)` where it
  gives `-x + -y`, is true by `rfl` but makes the unifier exhaust its
  heartbeats while unknowns are open; the laws are stated in the `+ -`
  form, with `rfl` lemmas (`ComplexReal.mul_along`, `neg_add_same`) that
  expose the parts first. Then, at the author's "Quaternion laws next"
  (Laws.lean now imports Quaternion): on the quaternions (a first and a
  second complex number, product (a, b)(c, d) = (ac − d̄b, da + bc̄)),
  `QuaternionReal.Same` is an equivalence, beside, turned over and each
  for each keep `Same`, beside commutes, associates, keeps nothing and
  `p + -p` is nothing, and each for each keeps one on either side,
  spreads over beside on either side and associates
  (`QuaternionReal.mul_same`, `add_comm`, `add_assoc`, `zero_add`,
  `add_neg`, `one_mul`, `mul_one`, `mul_add`, `add_mul`, `mul_assoc`);
  with `i_by_j_is_not_j_by_i` (Quaternion.lean) it does not commute. So
  the quaternions up to `Same` have the laws of a ring that is not
  commutative; all `propext`, `Quot.sound`. Associativity is written as
  two `calc` chains, each side's part spreading into four products of
  three complex numbers, some conjugated, the same four in another order
  because the complex numbers commute; it rests on the conjugate going
  through a product (`ComplexReal.conjugate_mul`) and through beside and
  turning over by `rfl`. Not shown: the conjugate of a quaternion
  product; and any order on the signed reals. A reciprocal is since
  written for the positive reals (next bullet).
- The reciprocal (`Meanings/Reciprocal.lean`; `Episode13.lean`, section
  `the_lower_root_as_a_real`; `Experiments/Jar.lean`,
  `the_other_reals_walls_are_this_jars`; 23 November 2026, at the
  author's "Yes, reciprocal"). Receipts, `propext` and `Quot.sound` at
  most. `Bracketed.reciprocal x k pos` is one over a real, handed a stage
  k where its low wall is past nothing: the walls are one over the walls
  (`Fraction.recip`, which turns the order over), read at stage
  k + (n+1)q², q the low wall's under at k, so the width still narrows to
  1/(n+1) (`the_reciprocal_narrows`). A real does not say of itself that
  it is apart from nothing: being past nothing shows at a finite stage,
  and no finite stage shows a real is nothing, so the stage is an
  argument, not found. Laws: `mul_reciprocal` (x by one over x is one),
  `reciprocal_same` (whatever stages were handed in), `div` and
  `div_mul`; and `reciprocalFound`, given only that some stage shows it,
  takes the least by `findByLooking` with the click, no choice. On the
  device: the table's lower root, written with the root owed in the
  signed reals, is written held as 234 (the determinant) over the norm
  (`the_lower_root_as_a_real`, the norm handed in as past nothing at
  stage 10); the two roots multiply to 234 at every pair of stages
  (`the_two_roots_multiply_to_the_determinant`); and 324/65 of it has
  both walls inside the other root's jar, 2730/65 and 2759/65 (42 and
  42 + 29/65), at every stage (`the_other_low_wall_is_never_under_its_jar`,
  `the_other_high_wall_is_never_over_its_jar`), from the walls at stage
  10 decided by the kernel and one over's walls never moving outward of
  them; Jar.lean joins those walls to the jar's own. Not shown: one over
  a complex number or a quaternion. The two items left open here are since
  closed (next bullet).
- The difference, and one over a signed real (`Meanings/Difference.lean`;
  `Episode13.lean`, end of section `the_lower_root_as_a_real`; 23 November
  2026, at the author's "Yes, the difference"). Receipts, `propext` and
  `Quot.sound` at most. `Bracketed.difference x y k apart` is x less y,
  handed a stage k where y's high wall is not past x's low wall: low wall
  x's low less y's high, high wall x's high less y's low, read at stage
  k + 2n + 1, so nothing is truncated and the widths, which add, narrow
  to 1/(n+1) (`the_widths_subtract`). `difference_add`: the difference
  beside what was taken away is what it was taken from. So a signed real
  is its difference held, or the other difference owed
  (`SignedReal.is_its_difference_held`, `is_its_difference_owed`), and,
  handed a stage where held is strictly past owed or owed past held, it
  has one over (`reciprocalHeld`, `reciprocalOwed`) with
  `mul_reciprocalHeld`, `mul_reciprocalOwed`: by one over itself it is
  one. Which side of nothing it is on is handed in with the stage. Found
  on the way: core Lean's `Nat.lt_of_mul_lt_mul_right` bills
  `Classical.choice`; it is written out by hand
  (`lt_of_mul_lt_mul_on_the_right`), as `compatibility_form`'s bill was.
  On the device: `eighteen_less_the_root` (the root's high wall at stage
  0, ten, not past eighteen); by the laws, with √90·√90 = 90, 18·18 =
  324 = 234 + 90 and cancellation, it times eighteen and the root is 234
  (`eighteen_less_the_root_by_eighteen_and_the_root_is_the_determinant`),
  so it is `Same` as 234 over the norm
  (`eighteen_less_the_root_is_the_lower_root`), and the signed reals'
  `theLowerRoot`, 18 held and √90 owed, is `Same` as that, held
  (`the_lower_root_owed_and_over_are_one`): owed, less and over write one
  number. Then, at the author's "Yes, complex" (same file; Episode 13,
  section `the_turned_root_over`): `ComplexReal.reciprocal z k strict` is
  the conjugate by one over the norm squared (`normSquared`, along by
  along beside across by across, a signed real handed in held strictly
  past owed at stage k); `ComplexReal.mul_reciprocal`: z by one over z is
  one; `mul_conjugate`: z by its conjugate is its norm squared, along;
  and one over is one thing (`SignedReal.reciprocal_unique`,
  `ComplexReal.reciprocal_unique`). On the device: the turned root
  (18 along, √90 across) has norm squared 414, the turned table's
  determinant (`the_turned_roots_norm_squared_is_the_determinant`), so
  the two turned roots multiply to 414
  (`the_turned_roots_multiply_to_the_determinant`), as the table's two
  roots multiply to its 234; the norm squared is past nothing at stage 0
  (kernel-decided), and one over the turned root is the other turned root
  over 414 (`one_over_the_turned_root_is_the_other_over_the_determinant`).
  All `propext`, `Quot.sound`. Then, at the author's "Yes, quaternion"
  (same file; Episode 13, section `one_over_a_quarter_turn`):
  `QuaternionReal.reciprocal p k strict` is the conjugate (the first
  turned across the line, the second owed) by one over the norm squared,
  the two complex parts' norms squared beside each other, handed in held
  strictly past owed at stage k. The product does not commute, so one
  over is shown on both sides (`mul_reciprocal`, `reciprocal_mul`), and
  then one over is one thing: whatever the quaternion put before it makes
  one is its one over (`QuaternionReal.reciprocal_unique`); also
  `QuaternionReal.mul_neg` (a quaternion by one owed is the product
  owed). On the device: each quarter turn by itself being one owed, one
  over each quarter turn is that turn owed (`one_over_i_is_i_owed`,
  `one_over_j_is_j_owed`, `one_over_k_is_k_owed`), each turn's norm
  squared decided past nothing at stage 0. All `propext`, `Quot.sound`.
  Found on the way: stating `-(-1)` where `1` is meant made the unifier
  exhaust its heartbeats on two of the three turns; a `neg_neg` rewrite
  first fixes it. So up to `Same` the reals, signed reals, complex
  numbers and quaternions each have one over for whatever is handed in as
  apart from nothing, and the quaternions are a division ring in that
  sense. Since: the conjugate of a quaternion product is the product of
  the conjugates the other way round (`QuaternionReal.conjugate_mul`,
  `propext`, `Quot.sound`), and the order is in `Meanings/Order.lean`.
  Not shown: anything about what these numbers are of.
  Standard, and the author's next step:
  continuity with a modulus (a δ handed over for each ε) needs no choice,
  while that sequential continuity gives ε–δ continuity uses countable
  choice.

## Before you judge the work

A local question (one definition, one build error) needs only the declaration
and its neighbours. Before you say what the whole work means or whether it
succeeds, read the Preface, the Introduction, and Card 7 of the volume (the yarn theory, formerly Part VIII)
(in particular the chapter "What no finite gauge computes"), the last 300
lines of `Episode12.lean`, and the last 300 lines of `Episode13.lean` (the
author moved the device's closing passage, "This is as far as the machine
can go…", from the end of Episode 12 to Episode 13, just before the
epilogue, on 18 November 2026). A summary, including this file, is not
a substitute. This preparation is yours: do not ask the visitor to do it.

## Builds and experiments

```
cd CARD_2
lake build
```

A cold build takes about 25 minutes, nearly all of it in Episode 4. Episode 13
is a separate target, `lake build Measurement.Episode13`, under a minute
once Episode 12 is built (it was about two seconds before the episode grew).
It needs `Meanings`, core Lean only, a few seconds (`lake build Meanings`).
When checking Episode 13 by hand, cap Lean's memory
(`lake env lean -M 6000 …`): a proof that opens its sealed crank at the
concrete scale goes looking for an Area of more than 10²⁶ cells. The cap must
be well under the machine's memory: on the author's 8 GB laptop a cap of
6000 was no cap, and a probe took the machine down (18 November 2026). Use
`-M 1500` there, a kill timer of about a minute, and one probe at a time. A
statement that sets something beside `the_constant` by `rfl` is enough to
open it; state such things for any Area and then apply them. Say so
before you start, run it in the background, and never block on it. Build only
when asked or after a relevant edit. Do not report an old build log as a fresh
check. Do not ask the kernel to re-run a walk the device has already stored;
that is how a probe once reached 92 GB of memory.

An experiment is a route the visitor may choose, not a prerequisite. The
experiments and their readings are in `READINGS.md`. To run one: read its
section and its folder first; confirm the checkout matches the experiment's
setup commit; say what will be measured and what the sealed prediction says;
run it as its README directs; then read the result against the seal, confirmed
or refuted, with the numbers. A new experiment has its description, probes and
prediction committed before it is run. A result on one machine is a result;
universality is another claim.

## Working for the author

The author is John Henry. Keep the work's own vocabulary and its calibrations.

- The Lean is the authority. Read it; do not edit it unless the edit is named.
- A musing ("I think", "what do you think") asks for your judgment, not for an
  edit.
- The volume is serious mathematics in a dissonant vocabulary. The satire is in
  the words (frinkahedron, bent card, nowtrino), never in jokes or apologies.
- The README and anything else a newcomer meets first show the number and never
  name it.
- Commit when asked; never push without being asked. Each experiment is two
  commits, the setup first and the readings after, each row citing the setup.
- Leave the tour and the three cards out of maintenance and debugging.

The earlier, much longer version of this file, with its dated status log up to
14 November 2026, is in the git history.
