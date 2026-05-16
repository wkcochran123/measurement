# Volume 4 - The Reference Trace Gauge

Working title: **The Reference Trace**

Subtitle candidates:

- Eleven Traces Through the Lean Compiler
- What Happens When You Type `#check`
- A Calibration Notebook for the Compiler

Status: draft scaffold with Chapter 1 prototype. Compiler outputs are pending
until captured under the pinned Lean toolchain.

## Claim

The first three volumes explain the formal machinery from three registers:
theorem, phenomenon, and compiler. This volume is the fourth gauge. It does
not explain the reading from outside. It takes the reading.

Each chapter gives one reproducible Lean trace. The trace names the input,
records the compiler's response, and fixes enough of the surrounding
environment that another reader can recover the same answer. The prose is
sparse by design. The transcript is the load-bearing artifact.

This is not `GAUGE 1199`. The manga dramatizes the strain of formalization.
The reference trace calibrates the claim.

## Why This Is A Gauge

A gauge is the apparatus that makes a reading meaningful. A speedometer does
not merely display a number; it supplies the reference structure that lets the
number count as speed. A proof assistant trace does the same thing for the
compiler. It tells the reader what was asked, what environment the question
was asked in, what the compiler accepted, what it refused, and where the
boundary of the claim actually lies.

The mathematical gauge asks what order forces. The physical gauge asks what an
instrument can measure. The algorithmic gauge asks what computation the
compiler is building. The reference trace gauge asks what Lean actually says
when the reading is taken.

## Relationship To The Project

| Volume | Gauge | Pressure | Artifact |
| --- | --- | --- | --- |
| 1 | Mathematical | theorem | forced abstract structure |
| 2 | Physical | phenomenon | calibrated measurement story |
| 3 | Algorithmic | compiler | computation as argument |
| 4 | Reference trace | trace | witnessed compiler answer |
| `GAUGE 1199` | Manga companion | dramatic | strain rendered in panels |

Volume 4 is a peer to the other technical volumes, not an appendix. It
depends on them for motivation, but it does not merely summarize them. It is
the bench where the claims are placed under the instrument.

## Reproducibility Contract

Every final trace must state:

- Lean version.
- Lake project or file target.
- Exact command used.
- Exact input file contents or command input.
- Relevant `set_option` lines.
- Heartbeat settings if they affect the output.
- Whether a clean cache is required.
- Whether the output is expected to drift across Lean versions.

Current project pin:

```text
Lean toolchain: leanprover/lean4:v4.27.0-rc1
Lake package: measurement
Default target: Measurement
Important Lake option: -DautoImplicit=false
```

The project rule still applies: do not casually run the full Lean build. For
this volume, traces should be captured with the smallest file-level command
that demonstrates the chapter's claim.

Proposed command shape:

```text
cd device
lake env lean Trace/Volume4/Ch1.lean
```

The `Trace/Volume4` directory is a proposed scratch location for reproducible
trace files. It should not be imported by the episode modules.

## Trace Form

Each chapter contains one canonical trace and up to two variations.

```text
TRACE STATUS: pending verification

INPUT:
  > Lean input exactly as run

OUTPUT:
  compiler output exactly as produced

NARRATION:
  Two to four sentences explaining what the trace shows.
```

Variation blocks are smaller:

```text
VARIATION:
  > small admissible or inadmissible change
  output: compiler response
  note: why the response matters
```

No output should be invented. If the compiler has not been run, the output
remains pending.

## Code Exposure Rule

This volume may show more code than the first three because transcript is the
point. Excerpts are allowed when they do reference work:

- complete inductive definitions when the pattern matters;
- method names and types;
- interesting `LE` match arms;
- member names and types;
- inheritance and instance-stack patterns;
- actual Lean input/output transcript.

Do not excerpt code for atmosphere. Every excerpt must help the reader
understand the trace.

## Chapter Shape

Each chapter is short in prose and heavy in transcript.

| Component | Target |
| --- | --- |
| Setup | about 200 words |
| Canonical trace | 20-100 lines of Lean I/O |
| Narration | about 150 words |
| Variations | two variations, 2-5 lines each |
| Structural explanation | about 300 words |
| Bridge | about 100 words |
| Total prose | about 800-1,200 words |

The bridge is a handoff, not a recap. The trace has already carried the
chapter.

# Chapter 1 - The Record

Closed question: What is the smallest admissible mark a ledger can carry?

## Setup

The first reading is not a number. It is not even a value standing alone. The
first reading is a value carried by a process that lets the compiler tell it
apart from something else.

In Volume 1, this appeared as the mathematical distinction between a value,
its carrier, and the order that makes comparison admissible. In Volume 2, it
appeared as the physical event admitted by an instrument. In Volume 3, it
appeared as enumeration: the compiler must have a nameable thing before it can
scan, compare, index, or halt.

The reference trace takes that claim literally. It asks Lean what the
distinguishability interface is. The point is not to prove a theorem about
sets. The point is to watch the compiler reveal the shape of the first mark.

The two names for this chapter are:

```lean
CarrierProcess
DISTINGUISHABLE
```

`CarrierProcess` says that a value enters the ledger through a carrier.
`DISTINGUISHABLE` says that the carrier supplies enough structure for the
compiler to ask whether a candidate symbol differs from the distinguished one.

## Local Excerpt

The relevant declarations live in `device/Measurement/Episode1.lean`.

```lean
structure CarrierProcess
    (Carrier: Type)
  where
  symbol: Fact
  value: Number

  event: Number -> Number := fun s =>
    match s with
    | .zero _ => .zero Fact.Truth
    | .one  p _ => .one  p value
```

The carrier does not merely store a value. It also supplies an `event`
operation: a way for an incoming number to be carried forward by the process.

```lean
class DISTINGUISHABLE
    (Value: Type)
    (Observation: CarrierProcess Value)
    where

  fact: Fact
  symbol: Type Value

  distinct? : Prop := True
  different? : Type Value -> Prop :=
    fun s1 => s1 <> symbol

  dec_distinct : DecidablePred different?
```

The class has two explicit inputs: the `Value` and an `Observation` that is
already a `CarrierProcess Value`. This is the arity that matters. A
distinguishable mark is not merely `Nat`, or `Nat -> Nat`, or any naked type.
It is a type under a carrier process.

## Canonical Trace

TRACE STATUS: pending verification

Trace file candidate:

```lean
import Measurement.Episode1

#check @Measurement.CarrierProcess
#check @Measurement.DISTINGUISHABLE
```

Command candidate:

```text
cd device
lake env lean Trace/Volume4/Ch1.lean
```

Expected role of the trace: Lean should print the fully explicit type of
`CarrierProcess` and `DISTINGUISHABLE`. The output is not quoted here because
it has not yet been captured under the pinned toolchain.

```text
INPUT:
  > #check @Measurement.CarrierProcess
  > #check @Measurement.DISTINGUISHABLE

OUTPUT:
  [to be captured]

NARRATION:
  The trace shows that the first admissible mark has an arity. Lean does not
  expose `DISTINGUISHABLE` as a one-argument predicate on a naked type. It
  exposes it as a class over a value and the carrier process for that value.
```

## Variation 1 - Supplying The Carrier Shape

TRACE STATUS: pending verification

This variation should check the well-formed class family after both the value
and the carrier have been named.

```lean
import Measurement.Episode1

section
  variable (Value : Type)
  variable (observation : Measurement.CarrierProcess Value)

  #check Measurement.DISTINGUISHABLE Value observation
end
```

```text
VARIATION:
  > variable (Value : Type)
  > variable (observation : Measurement.CarrierProcess Value)
  > #check Measurement.DISTINGUISHABLE Value observation
  output: [to be captured]
  note: the class can be named only after the value and carrier are both in
        scope.
```

## Variation 2 - The Bad Shortcut

TRACE STATUS: pending verification

The tempting mistake is to treat `DISTINGUISHABLE` as if it accepted one naked
type. The final trace should include a small failure that proves why that is
not the interface.

Candidate input:

```lean
import Measurement.Episode1

#check Measurement.DISTINGUISHABLE Nat
```

This is intentionally incomplete. The exact error message must be captured
before the chapter is finalized.

```text
VARIATION:
  > #check Measurement.DISTINGUISHABLE Nat
  output: [to be captured]
  note: this fails because `Nat` is not yet a carried observation. The carrier
        is not decoration; it is part of the mark.
```

## What The Trace Establishes

The chapter's closed question asks for the smallest admissible mark a ledger
can carry. The trace answers by refusing to let the mark be only a value. Lean
requires the carrier layer.

That requirement is the first calibration of the whole project. A value has to
enter through a named process before the compiler can ask about it. The
compiler does not begin with arithmetic. It begins with a carried thing and a
decision procedure for difference.

This is why the wrong shortcut matters. If `DISTINGUISHABLE Nat` were the
right shape, distinguishability would be a property of `Nat` alone. But the
project's code asks for more: `DISTINGUISHABLE Value observation`, where the
observation is already a `CarrierProcess Value`. The ledger does not admit a
bare object. It admits a carried object.

The reference trace is therefore doing what the other three volumes described.
It is showing the instrument enforce the ontology.

## Bridge

Chapter 1 names the carried mark. Chapter 2 asks what the instrument can do
with two such marks. The next trace moves from distinction to comparison: a
procedure that can say one record is below another, and a repeatability
certificate that prevents the comparison from being mistaken for the thing
measured.

# Chapter 2 - Comparison

Closed question: How can an instrument compare records and repeat the result
without pretending the comparison is the thing measured?

Canonical trace: check or evaluate the `Trial.le` interface, then check the
shape of `REPEATABLE`.

Trace candidates:

```lean
import Measurement.Episode2

#check @Measurement.Trial.le
#check @Measurement.REPEATABLE
```

Purpose: show that comparison is a separate procedure and repeatability is a
separate certificate. The trace should make visible that `le` is not the
record itself; it is an interface over records.

Risks:

- Do not invent a concrete `Trial` value unless the constructor stack is small
  enough to show cleanly.
- If a concrete evaluation is too noisy, keep the canonical trace at the type
  level and use a variation for synthesis failure.

# Chapter 3 - Phenomena

Closed question: What can be said about the gap between recorded events
without inventing structure not in the ledger?

Canonical trace: a metavariable or elaborator diagnostic trace around
`Metavariable`, using the current Lean trace options only after they have been
verified.

Trace candidates:

```lean
import Measurement.Episode3

#check @Measurement.Metavariable
```

Possible elaborator trace:

```lean
set_option trace.Meta.isDefEq true
```

Purpose: show an unresolved object being carried by the compiler rather than
filled by authorial guesswork.

Risks:

- Verify trace option names before final text.
- Do not claim `def foo : ?alpha := 3` works in a particular way until the
  exact behavior is captured.
- If Lean's raw elaborator trace is too noisy, use a smaller local example and
  quote only the relevant lines.

# Chapter 4 - Structure

Closed question: How do multiple records combine without collapsing into one
undifferentiated record?

Canonical trace: namespace and qualified-name resolution, tied back to the
compiler symbol table without claiming Lean namespaces are literally
union-find.

Trace candidate:

```lean
namespace TraceCh4

namespace Foo
def bar := 3
end Foo

#check Foo.bar

open Foo
#check bar

end TraceCh4
```

Purpose: show that a record can be made accessible through a new context
without erasing its source identity.

Risk: soften the analogy. The trace demonstrates scope and name resolution,
not a literal union-find implementation.

# Chapter 5 - Distance

Closed question: How does a finite count of distinctions become an admissible
notion of distance?

Canonical trace: check `Spline.le` and its `LE` instance.

Trace candidate:

```lean
import Measurement.Episode6

#check @Measurement.Spline.le
#check inferInstanceAs (LE Measurement.Spline)
```

Purpose: show distance as an interface induced by finite constructors and a
comparison relation.

Risks:

- Avoid claiming a numerical spline solve unless the code actually constructs
  one.
- Keep this trace about the relation, not about a full numerical method.

# Chapter 6 - Motion

Closed question: What selects one admissible continuation as the history
actually carried forward?

Canonical trace: check `GalerkinProcess`, `FINITE_ELEPHANT`, or a bounded
approximation certificate that the current code supports.

Trace candidate:

```lean
import Measurement.Episode6

#check @Measurement.GalerkinProcess
#check @Measurement.FINITE_ELEPHANT
```

Purpose: show approximation as the computable shadow of selection. The exact
Kolmogorov selector is not implemented and must not be presented as if it were.

Risks:

- Do not promise a brachistochrone Galerkin solve.
- Do not claim exact `K` is computed.
- If the trace is only type-level, the prose must say that honestly.

# Chapter 7 - Transport

Closed question: How can information move between histories while preserving
admissibility?

Canonical trace: one bounded instance-cascade step, preferably through
`WITNESSED` or a smaller scientific-process witness.

Trace candidate:

```lean
import Measurement.Episode10

#check @Measurement.WITNESSED
```

Purpose: show transport as a witnessed passage through an admissible process,
not as free movement of truth.

Risks:

- Do not try to print the whole cascade if it overwhelms the reader.
- A short trace that exposes the class stack is better than a long trace that
  becomes unreadable.

# Chapter 8 - Stress

Closed question: What reference structure lets distinct observers compare
their counts as one physical record?

Canonical trace: check the public `Calibration.EKG` interface and one
Prop-valued method.

Trace candidate:

```lean
import Measurement.Calibration.LeanCalibration

#check Measurement.Calibration.EKG
#check Measurement.Calibration.EKG.raw
#check Measurement.Calibration.EKG.booleanLength?
#check Measurement.Calibration.EKG.booleanProgram?
```

Purpose: show calibration as a hidden reference with a public Prop-valued
surface.

Risks:

- The private `Reading` and its `Nat` must remain hidden.
- If visible heartbeat counts are needed, use Lean's own trace diagnostics or
  a separate trace-only wrapper. Do not leak the hidden reference through the
  episode interface.

# Chapter 9 - Strain

Closed question: What records the failure of transport to commute?

Canonical trace: compare two proof or elaboration paths through a trace surface
that records cost or route without violating calibration abstraction.

Trace candidate:

```lean
import Measurement.Episode11

#check @Measurement.HeartbeatProcess
```

Purpose: show that non-commuting routes leave a record in the compiler's work.

Risks:

- Heartbeats are a computable proxy for elaboration cost, not semantic
  equality.
- Do not imply that different heartbeat counts prove different mathematical
  meanings.

# Chapter 10 - Symmetry

Closed question: What remains invariant under admissible relabeling or
recompilation?

Canonical trace: a cheap fixed-point or invariance demonstration. The actual
Lean bootstrap is too expensive for a reader-facing trace.

Trace candidates:

```lean
#check Eq.refl
```

or a small local definition whose normal form stabilizes under reduction.

Purpose: show invariance without asking the reader to rebuild Lean.

Risks:

- Do not claim byte-identical bootstrap output.
- Use "fixed point up to chosen observational equivalence" unless a stronger
  reproducible condition is actually proven.

# Chapter 11 - Entropy

Closed question: Why does the record only grow, and when is it closed enough to
support inference?

Canonical trace: the final type check.

Trace candidate:

```lean
import Measurement.Episode15

#check Measurement.theory_true?
```

Purpose: end with the compiler's answer to the accumulated project.

Risks:

- Verify the exact output under the pinned toolchain.
- If the output is visually thin, refine the surrounding trace or narration;
  do not fake drama.

# Draft Order

1. Capture Chapter 1 traces.
2. Replace Chapter 1 pending blocks with exact output.
3. Read Chapter 1 for rhythm: setup, trace, narration, variation, structural
   explanation, bridge.
4. If the rhythm works, capture Chapters 2-4.
5. Pause before Chapters 5-7 to verify the trace surfaces are not too large.
6. Draft Chapters 8-9 after calibration trace policy is settled.
7. Draft Chapter 10 only after the cheap invariance substitute is chosen.
8. Draft Chapter 11 last, after `theory_true?` is verified.

# Open Technical Tasks

- Create the `device/Trace/Volume4` scratch directory or choose another
  documented trace location.
- Decide whether trace files are committed or generated artifacts.
- Pin exact command lines for each trace.
- Verify the actual output of `#check @Measurement.DISTINGUISHABLE`.
- Verify the actual output of `#check Measurement.theory_true?`.
- Decide how to show heartbeat or elaboration cost without exposing private
  calibration internals.

# Current Verdict

The document is now a draft, not merely a plan. Chapter 1 is ready for trace
capture. Chapters 2-11 are intentionally held as trace plans until their Lean
output is real.
