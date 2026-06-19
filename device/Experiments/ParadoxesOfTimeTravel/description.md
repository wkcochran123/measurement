# Paradoxes of Time Travel

Source: `instrument/chapters/06.tex:455`
Environment: `phenomenon`
Original title: `Paradoxes of Time Travel~\cite{godel1931,lewis1976}`

## Description

**Note.** Apparent paradoxes often attributed to \emph{time travel}, \emph{remote 
viewing}, or other extraordinary mechanisms are pathologies of 
over--resolution.  They arise when incompatible refinements are treated as 
simultaneously admissible, producing the illusion of phenomenal violation 
rather than an actual failure of causal order.

**Note.** This thought experiment introduces constructions that are intentionally
self--referential.  These devices are used only to illustrate how paradoxes
arise when an observer attempts to treat its own temporal index as a
manipulable datum.  Such constructions lie outside the admissible structure
of the axioms and are not permitted in any formal derivation.  In particular,
they follow the general pattern of self--reference that Godel cautioned
against in his incompleteness results: systems that encode statements about
their own inferential process cannot, in general, maintain global
consistency~\cite{godel1931}.  The paradoxes described here therefore serve only as intuitive
warnings.  They do not represent allowable configurations within the theory,
and no phenomenon in this manuscript relies on them.




Let $E = \{e_1, e_2, e_3, \dots\}$ be a locally finite causal chain where each
event $e_i$ has a unique successor $e_{i+1}$.  Define the corresponding universe
tensor
\begin{equation}
\U_n = \sum_{k=1}^{n} \E_k, \qquad \E_k=\mathbf\Psi_k(e_k).
\end{equation}
Now suppose we attempt to ``extend'' this history by splitting a single event
$e_j$ into uncountably many indistinguishable refinements:
\begin{equation}
e_j \longrightarrow \{e_{j,\alpha}\}_{\alpha \in [0,1]},
\end{equation}
each representing a formally distinct but observationally identical outcome.
Algebraically, this replacement yields
\begin{equation}
\E_j \longrightarrow \int_{0}^{1} \E_{j,\alpha}\, d\alpha,
\end{equation}
so that the next update becomes
\begin{equation}
\U_{n+1} = \U_n + \int_{0}^{1} \E_{j,\alpha}\, d\alpha.
\end{equation}

This ``extension'' violates the finiteness and distinguishability conditions
necessary for causal coherence:
\begin{enumerate}
\item The set $\{e_{j,\alpha}\}$ is uncountable, destroying local finiteness;
\item The new events are indistinguishable, so Extensionality no longer
      guarantees unique contributions;
\item The total tensor amplitude $U_{n+1}$ can diverge or cancel arbitrarily,
      depending on how the continuum of duplicates is treated.
\end{enumerate}

Operationally, this is a Banach--Tarski-like overcounting: the causal structure
has been ``refined'' in a way that preserves measure only formally while the
order relation collapses.  The observer would now predict contradictory
outcomes for the same antecedent state---an \emph{overcomplete history}.

To prevent this, the \emph{Axiom of Event Selection} restricts the permissible
extension to a countable, consistent refinement:
\begin{equation}
e_j \longrightarrow e_{j,1}, e_{j,2}, \dots, e_{j,k},
\end{equation}
and requires the selection of exactly one representative outcome from each
locally admissible family.  This keeps $E$ locally finite and maintains a
single-valued universe tensor,
\begin{equation}
\U_{n+1} = \U_n + \E_{j,k^\ast}.
\end{equation}
The axiom thus enforces the same regularity that Martin's Axiom guarantees in
set theory: every countable family of local choices admits a globally consistent
selection that preserves the partial order.
