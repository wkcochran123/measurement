# Shadow Tomography

Source: `instrument/chapters/07.tex:198`
Environment: `phenomenon`
Original title: `Shadow Tomography~\cite{aaronson2013}`

## Description

**Note.** This informational phenomenon reflects results by Aaronson and others
showing that only a bounded amount of operationally accessible information
about a quantum system can be extracted, regardless of the continuum
descriptions allowed by Hilbert-space formalism.  The argument below does not
use physical tomography; it expresses the same limitation in the language of
refinement and distinguishability.


Consider a system whose underlying measurement record consists of a discrete
chain of refinements.  Let $\{O_1,\ldots,O_m\}$ be a family of admissible tests
that the observer may apply.  Classically, one might expect that by probing the
system with sufficiently many such tests, one could reconstruct an arbitrarily
detailed internal description.  Shadow tomography demonstrates that this is not
the case: only a small, coarse projection of the underlying informational
structure can ever be distinguished.

From the standpoint of the Axioms of Measurement, the reason is immediate.
Each test $O_j$ extracts only the distinctions resolvable at the minimal
increment dictated by the Axiom of Planck.  The Axiom of Kolmogorov ensures
that each measurement outcome has finite informational content, and the Axiom
of Peano ensures that these outcomes accumulate discretely.  Thus, even an
exponentially large sequence of tests cannot expose distinctions that lie below
the minimum resolvable scale or that require refinements forbidden by the
Axiom of Ockham.

Operationally, the observer does not recover the internal structure of the
system's full refinement history.  Instead, they recover a \emph{shadow}: the
projection of that history onto the small set of distinctions probed by the
tests $\{O_j\}$.  Two systems whose internal refinements differ but whose
shadows coincide are operationally indistinguishable.  In the language of this
manuscript, they represent distinct admissible histories that yield the same
externally visible refinement pattern.

This phenomenon clarifies why the continuum description of quantum states
contains far more degrees of freedom than can ever appear in practice.  Shadow
tomography reveals that measurement accesses only the coarse-grained shadow of
the underlying informational structure, never its complete refinement.  It
provides an operational reason why uncorrelant events, informational decoherence,
and refinement non-commutation arise naturally: the observer sees only the
shadow, while the full informational record remains inaccessible.
