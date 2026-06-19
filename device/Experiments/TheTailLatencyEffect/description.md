# The Tail-Latency Effect

Source: `instrument/chapters/08.tex:1063`
Environment: `phenomenon`
Original title: `The Tail-Latency Effect`
Labels: `ph:tail-latency`

## Description

\textbf{Statement.}
Latency in an admissible region increases with both the number of active
causal connections and the surface measure of the region through which
refinements must be transported.

\textbf{Mechanism.}
Each admissible refinement must be reconciled across all attached causal
interfaces.  Let $N$ denote the number of active connections incident on a
region $\Omega$, and let $|\partial \Omega|$ denote the surface measure of its
boundary.  The cost of transport is not determined by the shortest path, but
by the slowest admissible reconciliation.

The tail of the latency distribution is therefore governed by
\[
\mathcal{L}_{\mathrm{tail}} \propto N \cdot |\partial \Omega|.
\]

\textbf{Interpretation.}
Transport in the causal ledger is not limited by average throughput but by
worst-case synchronization.  Each additional connection increases the number
of constraints that must be satisfied, and each increase in boundary area
expands the number of admissible reconciliation paths.

Latency therefore accumulates geometrically: wide interfaces and dense
connectivity do not accelerate refinement, they delay it.  The slowest
boundary dominates the admissible update rate.

This is not a property of signal speed.  It is a bookkeeping constraint: the
ledger cannot commit a refinement until every connected boundary can be
reconciled without contradiction.
