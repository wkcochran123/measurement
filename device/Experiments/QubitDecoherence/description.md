# Qubit Decoherence

Source: `instrument/chapters/07.tex:1201`
Environment: `phenomenon`
Original title: `Qubit Decoherence~\cite{joos2003,zurek2003}`

## Description

**Note.** This informational phenomenon does not rely on physical decoherence
mechanisms, environmental coupling, or geometric dynamics.  It arises solely
because measurements are recorded and admissible refinements must remain
consistent with the axioms of event selection, refinement compatibility, and
Ockham minimality.


A \emph{causal doublet} is the minimal unit of informational degeneracy: a
system admitting two equally admissible refinement paths $S=\{e_0,e_1\}$.
Such a structure represents a qubit in the informational sense: a pair of
distinct updates that are locally indistinguishable and jointly admissible.

Decoherence occurs when a new event is recorded that is inconsistent with
one of the branches.  The Interaction Operator $f$ performs a \emph{pivot} on
the shared boundary, eliminating all incompatible orderings and collapsing the
doublet to a single admissible history.  This collapse satisfies Martin's
Condition, ensuring that the refined ledger extends the earlier one without
introducing new admissible distinctions.

The observed \emph{rate} of this collapse is a smooth shadow of two underlying
informational constraints:

\begin{enumerate}
\item \textbf{Finite Causal Resolution.}
Irreducible uncertainty in the ordering of micro-events at scale $\Delta x$
induces a stochastic drift in the admissible refinements.  This drift arises
whenever unresolved orderings accumulate faster than they can be anchored by
distinguishable events.

\item \textbf{Informational Diffusion ($D$).}
The propagation of unresolved distinctions obeys a diffusion law: coarse
records evolve stochastically under refinement, with an effective diffusion
coefficient $D$ determined by the informational bandwidth of the system.
\end{enumerate}

Together, these constraints imply that decoherence is the statistical failure
to maintain a causal degeneracy in the presence of new distinctions.  The
macroscopic decoherence rate emerges as the smooth shadow of this
irreversible informational process and is governed by the informational
diffusion coefficient $D$ and the minimal unresolved action $\hbar$.  No
physical environment or geometric postulate is required.
