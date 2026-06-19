# The Newton-Cooley-Tukey Effect

Source: `instrument/chapters/02.tex:1967`
Environment: `phenom`
Original title: `The Newton--Cooley--Tukey Effect~\cite{cooley1965,newton1687}`
Labels: `ph:recursion`

## Statement
Any process whose structure admits hierarchical refinement may be computed by
operating locally along that hierarchy, provided the decomposition is exact and
aligned with the instrument's decoding maps.

## Origin
Newton introduced local methods of computation based on successive refinement,
demonstrating that complex behavior could be resolved through iterative
linearization~\cite{newton1687}.  Much later, Cooley and Tukey showed that global
transformations could be computed efficiently by exploiting recursive
factorization already present in the problem structure~\cite{cooley1965}.
Although developed in distinct contexts, both approaches rely on the same
principle: computation proceeds by respecting an existing hierarchy rather than
by treating the problem as flat.

## Observation
Physical and computational instruments routinely exploit hierarchical structure.
Signal transforms are computed by recursive decomposition, differential
equations are solved by local updates, and refinement-based searches narrow
admissible outcomes step by step.  In each case, computation advances by acting
on small components whose organization mirrors the structure of the instrument
itself.  The ledger records only the outcomes of these local operations, while
the hierarchy remains implicit.

## Constraint
No computation may lawfully bypass the refinement structure of the instrument.
Operations must act locally within the hierarchy exposed by decomposition.
Attempts to compute globally without respecting this structure introduce
unrecoverable distinctions and violate exactness.

## Consequence
Phenomenon~\ref{ph:recursion} exhibits hierarchical description that admit
efficient computation.  Computational power arises not from algorithmic
ingenuity alone, but from alignment between the instrument's decomposition and
the process being computed.  When such alignment holds, global behavior emerges
from local refinement.  When it does not, computation becomes intractable or
ill-defined.
