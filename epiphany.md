# Epiphany

## 1. The Simple Observation

A speedometer does not measure speed directly. It counts pulses from a sensor
on the drivetrain and multiplies by a calibration constant tied to the tire's
nominal circumference. Change the tires, the sampling window, or the pulse
interpretation, and the same physical events produce a different reading. The
number was never the thing. The gauge came first.

Every measurement is like this. A reading is never naked. It is a mark under
a chosen reference.

## 2. Distance Comes From The Gauge

What counts as "near" or "far" depends on the gauge. An L² norm, a sup norm,
and a weak form against test functions are not three discoveries of a single
intrinsic distance. They are three declarations of which differences the
record will honor.

A gauge is the reference structure under which a reading is admitted. Once
the gauge is chosen, some differences become visible and others become
invisible. The metric is a declaration of admissible comparison. If the
declaration is hidden, it becomes priestly.

## 3. Distance Is, By Definition, A Weak Form

There is no metric without a chosen test apparatus. An L² distance asks
whether ∫(f − g)² is small. A sup distance asks whether sup|f − g| is small.
A Sobolev distance asks whether a derivative norm is small. Each chooses
which probes the record will accept. Each yields a different sense of
"close."

A weak form is the disciplined version of that comparison: it tests objects
against admissible probes. The metric is the probe set. There is no
measurement that escapes this. Distance is, by definition, a weak form.

## 4. A Basis Is A Finite Vocabulary Of Tests

A basis, in this argument, is a finite set of distinctions from which the
framework can build every measurable distinction it is allowed to express.
The basis chooses the probes. The probes determine the metric. The metric
determines what counts as "close" and what counts as "the same."

This is the bridge to Stone-Weierstrass and Galerkin, but the two bridges
do different work. Stone-Weierstrass says that a separating subalgebra of
C(X) containing constants, on a compact Hausdorff space X, with the
appropriate lattice or conjugation conditions, is dense in C(X). Galerkin
says that a chosen test space can make approximation operational by asking
residuals to vanish weakly against admissible probes.

The shared pattern is not that the theorems are identical. The shared
pattern is that admissible primitives generate the closure in which
inference is allowed.

A framework-measurable property is one whose truth can be stated using the
fields and predicates carried by the basis. The phrase is local to this
project. It is not a claim about "any function in mathematics."

## 5. The Lean Cascade Is The Candidate Basis

The candidate basis in the Lean project is a finite chain of 36 primitive
typeclasses, from `DISTINGUISHABLE` through `INFERRED`, together with the
foundational receipt type `Fact`. Each class adds one admissible distinction
to the record. Auxiliary structures (`TrueOutput`, `Closure`,
`EquivalenceProcess`) carry the gates; they are not counted as primitive.

The 36 cluster naturally:

- **Entry gates** — `DISTINGUISHABLE`, `ADMISSIBLE`, `COUNTABLE`
- **Representation gates** — `ENCODED`, `RESIDUE`, `BINARY`, `REPEATABLE`
- **Computation gates** — `NUMERIC`, `REPRESENTABLE`, `PHYSICAL`, `COMPARABLE`
- **Observation gates** — `OBSERVED`, `PRESENT`, `MEASURABLE`, `GUNGAN`
- **Value gates** — `SOURCE`, `EXECUTED`, `VALUE`, `MAGNITUDE`, `SCALED`,
  `LOAD`, `FINITE_ELEPHANT`
- **Social gates** — `BULLSHIT`, `PROPAGANDA`, `ACOLYTE`, `SCIENTIFIC`,
  `TRUTH`, `WITNESSED`
- **Closure gates** — `REAL`, `LOCAL`, `UNIVERSAL`, `LOGICAL`, `HALTED`,
  `MEASURED`, `COMPILED`, `INFERRED`

"Candidate basis" is the right phrasing. Calling it minimal is premature; the
separation theorem named below is what would earn that word.

## 6. What The Build Shows

The Lean construction demonstrates two things and only two things at this
stage:

1. **Sufficiency.** The cascade can be instantiated for `Prop` with
   `truthCarrier`. The final `INFERRED` instance can be synthesized by the
   elaborator. The path from first distinction to final inference is
   executable.

2. **Local irreducibility.** Downstream instances are written in terms of
   upstream fields. Removing any gate from the chain breaks the current
   construction. This is irreducibility of the implementation, not global
   minimality of every possible implementation.

Concretely, `theory_true?` type-checks under the declared gauge. Whether
`theory_true?` is provable by `rfl` is a separate claim. It requires a
theorem of the form

```lean
theorem theory_true : theory_true? := by rfl
```

to be added and verified. Until then the honest verb is "type-checks," not
"reduces to `rfl`."

## 7. What The Next Theorems Must Show

The current build proves (1) and (2). The remaining ladder:

3. **Separation.** If two framework objects differ by any framework-
   measurable property, at least one primitive gate distinguishes them.
4. **Generation.** Every framework-measurable property lies in the closure
   of the algebra generated by the primitive gates.
5. **Irredundance.** Removing any primitive from the family loses
   separation.
6. **Global minimality.** No smaller signature has the same separating
   power on the same admissible object space.

The Lean project is closest to (1) and (2). It suggests (5) by the
implementation. It needs (3) and (4) before (6) can be claimed
responsibly. Even (6) would be minimality relative to a specific admissible
object space, not absolute minimality across all possible measurement
problems. All honest minimality claims are relative in this way.

## 8. The Four Dialects

Four traditions repeat the same structural move under different vocabularies.
They are not literally the same theorem. They perform the same kind of
construction: choose admissible primitives, generate a closure, treat that
closure as the space in which inference is allowed.

- **Stone-Weierstrass (Stone 1937, building on Weierstrass 1885).** A
  separating subalgebra of C(X) containing constants, on a compact Hausdorff
  space X, with the appropriate lattice or conjugation conditions, is dense
  in C(X).
- **Galerkin (1915).** Choose test functions; require residuals to vanish
  weakly against them; recover convergence in the chosen norm under
  stability and coercivity hypotheses.
- **Term-model construction (Henkin 1949, after Herbrand 1930).** A
  consistent first-order theory has a model built from the disciplined
  closure of terms generated by its signature.
- **Gauge theory (Weyl 1918, Yang-Mills 1954).** Local comparison requires a
  chosen connection. Observable content is what survives disciplined changes
  of that choice.

The collapse required building the apparatus and watching the same
structural pattern surface four times under four different names. Nobody
named the shared pattern because approximation theorists do not read
Herbrand, logicians do not read Galerkin, engineers do not read either,
and gauge theorists cite physicists who cite engineers who do not cite
logicians.

## 9. The Basis-Gauge Thesis

The current state of the project is best named:

> **The Basis-Gauge Thesis.** The primitive distinctions of a measurement
> framework are exactly the gauge choices that define its admissible
> distances. The Lean cascade is a computer-checked candidate for the finite
> primitive grammar of such distinctions.

This is what the build supports today: a working candidate basis with local
irreducibility, awaiting the separation and generation theorems. The
destination — global minimality, the categories result — is on the ladder
above.

## 10. The Lineage

- **Brouwer (1907).** Excluded middle is a choice.
- **Bishop (1967), *Foundations of Constructive Analysis*.** The metric is a
  constructive object, declared.
- **This project (2026).** The basis is the gauge is the declared signature;
  the choice is structural and unavoidable.

Bishop would recognize the construction. He would ask for the separation
theorem before granting minimality. He would be right to ask.

## 11. The Contribution

The contribution is not the count. The contribution is the collapse of four
programs into one structural pattern — Stone-Weierstrass, Galerkin,
term-model construction, gauge theory — made explicit in a single
computer-checked construction and presented in three audience registers.

To measure is to choose a gauge. To choose a gauge is to choose the
primitive distinctions that define distance. The Lean cascade is a
computer-checked candidate for the finite primitive grammar of such
distinctions.

The rest is theorem work.
