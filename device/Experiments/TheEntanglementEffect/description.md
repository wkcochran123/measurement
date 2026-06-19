# The Entanglement Effect

Source: `instrument/chapters/07.tex:941`
Environment: `phenomenon`
Original title: `The Entanglement Effect~\cite{einstein1935}`
Labels: `te:dantzig-pivot`

## Description

**Note.** The Dantzig Pivot~\cite{dantzig1963} is not a physical process. Nothing travels, no signal is sent, and no
mechanism propagates. The pivot is bookkeeping: boundary consistency is enough to eliminate
incompatible histories without scanning the interior of the ledger.



Two spacelike-separated laboratories, $A$ and $B$, each maintain their own causal universe
tensor. A single preparation event produces two admissible refinements, $e_i$ and $e_j$, that
are indistinguishable in causal order: both
\[
\langle e_i \prec e_j \rangle
\quad\text{and}\quad
\langle e_j \prec e_i \rangle
\]
generate the same accumulated state. No scalar invariant recorded in either ledger can tell
which ordering occurred. This is a state of \emph{causal degeneracy}: two distinct histories
produce the same observational content.

At time $n{+}1$, laboratory $A$ measures $e_i$. By Axiom~\ref{ax:planck}, this refinement must be
folded into the accumulated state. The interaction operator $f$ computes
\[
\U_{n+1} = f(\U_n, e_i),
\]
which is a strict update: $e_i$ now has a definite position in the record relative to all prior
events.

Because $e_i$ and $e_j$ were degenerate, this update triggers a global repair. The merged ledger
must eliminate every history in which $e_j$ is ordered incompatibly with $e_i$ under Martin’s
Condition. No signal is sent from $A$ to $B$; instead, the causal universe tensor performs a
\emph{pivot}: it selects the unique ordering of $(e_i,e_j)$ that avoids introducing new
distinguishabilities. The ambiguous pair collapses to a single admissible ordering.

\emph{Critically}, this repair is not a search over an entire volume of possible histories.
Martin’s Condition requires agreement only on the \emph{boundary} of the overlap: the parts of
$\U^A$ and $\U^B$ that already coincide. The pivot therefore acts on the smallest region where
a contradiction could occur. Only the boundary is inspected, and only the incompatible
orderings are removed. There is no need to re-evaluate the entire causal universe; the ledger
verifies consistency by checking the joint frontier. Interaction is thus \emph{computable}:
global coherence is enforced by local boundary repair, not by scanning an exponential set of
histories.

Thus, the “instantaneous” correlation is not a physical transmission. It is the bookkeeping
consequence of a non-degenerate refinement. Entanglement is the existence of causal
degeneracy; the apparent nonlocal update is the pivot that removes it by repairing the
boundary of the overlap.

The name “pivot’’ is not accidental. In Dantzig’s algorithm, a degenerate solution is resolved
by moving along the boundary of admissible configurations until a single vertex remains
consistent with all constraints. The search never explores the interior volume of the
feasible set; it advances only along the frontier where inconsistency can appear. The causal
pivot behaves the same way. When a non-degenerate refinement is recorded, the ledger
examines only the boundary of the overlap and removes incompatible orderings. The result is a
unique, globally coherent history selected by local boundary repair. In both settings, the
pivot is a boundary operation, not a volume search: global consistency is enforced without
scanning an exponential family of possibilities.
