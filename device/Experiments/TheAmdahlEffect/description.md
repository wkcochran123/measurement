# The Amdahl Effect

Source: `instrument/chapters/11.tex:331`
Environment: `phenomenon`
Original title: `The Amdahl Effect`

## Description

No refinement can be made arbitrarily fast by parallelism.  The admissible
speed of causal execution is bounded by the largest uncorrelant segment of
the ledger.

If a fraction $p$ of the refinement is perfectly correlant, and a remaining
fraction $1 - p$ is sequentially uncorrelant, then no admissible extension of
the ledger can exceed the bound
\[
S_{\max} = \frac{1}{(1 - p)}.
\]
The uncorrelant portion is not a technical defect but a structural
constraint: segments of the causal record that cannot be merged, reordered,
or parallelized without violating admissibility.

Uncorrelance is therefore not inefficiency.  It is the irreducible
sequentiality required for the ledger to remain globally consistent.
