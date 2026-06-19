# It\^o's Lemma

Source: `instrument/chapters/07.tex:2025`
Environment: `phenomenon`
Original title: `It\^o's Lemma~\cite{ito1944,ito1951}`
Labels: `ph:ito`

## Description

**Note.** It\^o's Lemma appears here not as a theorem of stochastic calculus,
nor as a property of diffusion processes, but as a structural consequence
of informational refinement. When a finite record is repeatedly refined,
the admissible interpolants must update according to Martin consistency
and Ockham minimality. These updates produce the same correction terms
that, in classical settings, are associated with stochastic differentials.
No probabilistic or physical assumptions are used; the result is purely
algebraic.


Let $X_t$ denote the minimal continuous extension of a finite record
obtained by Spline Sufficiency. Suppose that between two refinements,
the record admits a locally smooth representation
\[
X_{t + \Delta t} = X_t + \Delta X_t.
\]
Refinement compatibility requires that any function $f(X_t)$ be updated
by comparing the old and new admissible extensions. The refinement
\[
f(X_{t+\Delta t}) - f(X_t)
\]
must be consistent with the joint refinement of $X_t$ and $f$ under the
axioms of order, minimality, and Martin consistency. Expanding to second
order in the refinement step and discarding inadmissible terms produces
\[
df = f'(X_t)\,dX_t + \tfrac{1}{2} f''(X_t)\,(dX_t)^2,
\]
where $(dX_t)^2$ is the second-order correction forced by the comparison
of successive minimal interpolants. This quadratic term is not a physical
noise term but an informational artifact: the unavoidable discrepancy
between two successive minimal refinements of the same record.

Thus It\^o's Lemma arises as the continuous shadow of discrete,
consistent refinements of observational data.
