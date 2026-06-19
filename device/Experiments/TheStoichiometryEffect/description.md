# The Stoichiometry Effect

Source: `instrument/chapters/07.tex:635`
Environment: `phenomenon`
Original title: `The Stoichiometry Effect`
Labels: `ph:stoichiometry`

## Description

\textbf{Statement.}
Causal interactions are governed by Diophantine constraints, not continuous
variation.  Because the causal ledger is composed of discrete, indivisible
events, admissible interactions occur only when integer refinement counts
balance exactly.

\textbf{The Integer Constraint.}
Let $N_A$ and $N_B$ denote the number of unresolved refinement threads carried
by systems $A$ and $B$.  An admissible interaction
\[
f(U_A, U_B) \rightarrow U_C
\]
exists only if there are integers $a,b,c \in \mathbb{Z}$ such that
\[
a N_A + b N_B \rightarrow c N_C.
\]
No fractional event may be recorded, and no partial refinement may be
committed.

\textbf{Hard Failure (No Reaction).}
If the integer balance cannot be satisfied, no admissible merge exists.  The
ledger rejects the update.  The systems may scatter, deflect, or pass through
one another, but no interaction occurs, because a fractional event would be
required to close the account.

\textbf{Conclusion.}
Chemical stoichiometry, particle number conservation, and selection rules are
not arbitrary physical laws.  They are bookkeeping necessities imposed by the
impossibility of writing half an event in a discrete causal ledger.  An
interaction is the solution of an integer program.
