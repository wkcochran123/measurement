# The Bell-Aspect Tests

Source: `instrument/chapters/07.tex:1040`
Environment: `phenomenon`
Original title: `The Bell--Aspect Tests~\cite{bell1964}`
Labels: `te:bell-aspect`

## Description

Two spacelike-separated laboratories, $A$ and $B$, share a preparation event that produces
an entangled pair. Each maintains its own causal universe tensor. The preparation is such
that multiple ordered refinements remain admissible: different measurement settings at $A$
and $B$ produce distinct, yet individually consistent, ledgers. Before either measurement is
recorded, the global state is degenerate: many joint histories remain compatible with all
previous refinements, and no scalar invariant distinguishes among them.

A local hidden-variable model assumes that this degeneracy can be resolved purely by local
rules. In ledger language, it assumes that the update
\[
(\text{measure at }A,\text{ measure at }B)
\]
can be decomposed into separate, predetermined refinements in each ledger. That is,
the merged state could be written as a fold of two independent maps acting only on local
records, with no global repair.

The Bell--Aspect tests show this is impossible. When $A$ records a refinement corresponding
to setting $a$ and $B$ records one corresponding to $b$, the accumulated tensor must be
updated by the interaction operator,
\[
\U_{\mathrm{final}} = f(\U^A,\U^B).
\]
For many setting pairs $(a,b)$, the resulting ledger eliminates histories that would have
remained admissible under any local rule. The violation of Bell inequalities is the empirical
statement that no decomposition of $f$ into independent, local updates can preserve all
observed distinctions. The fold is intrinsically global.

Operationally, a new refinement at $A$ forces a pivot on the boundary shared with $B$,
eliminating joint histories that contradict the updated record. No signal travels between the
laboratories; no mechanism carries information. The ledger simply performs the minimal
boundary repair required by Martin's Condition. The observed ``nonlocal'' correlations are
the bookkeeping consequence of enforcing a single, globally consistent causal ordering.

Thus, the Bell--Aspect tests reveal that entanglement is not a hidden influence. It is the
fact that the causal universe must repair its boundary globally when a non-degenerate
refinement is recorded. Local hidden variables fail because they deny the existence of this
global pivot.
