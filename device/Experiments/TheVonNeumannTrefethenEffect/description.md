# The von Neumann-Trefethen Effect

Source: `instrument/chapters/02.tex:2964`
Environment: `phenom`
Original title: `The von Neumann--Trefethen Effect~\cite{trefethen1997,vonneumann1947}`
Labels: `ph:stability`

## Statement
The practical success of finite computation reflects a selection effect on
operator \emph{constructions}.  Although refinement is generically unstable under
finite precision, those operators that arise through standard constructions and
persist under refinement exhibit a remarkable statistical stability.  Stability
is not typical; it is earned through survivorship of construction.

## Origin
Von Neumann and Goldstine analyzed error propagation in finite-precision
computation and demonstrated that, in the worst case, iterated refinement leads
to explosive growth of residual variation.  Their analysis correctly described
the generic behavior of symbolic translation under iteration.  Decades later,
Trefethen and collaborators studied operators as they are actually constructed in
numerical practice---through discretization, linearization, truncation, and
projection---and observed, through extensive statistical and empirical analysis,
that these constructions are far from generic.  The stability encountered in
practice reflects the structure of the construction process itself.

## Observation
Across scientific computation, operators produced by standard construction
schemes cluster in well-conditioned regimes.  Trefethen's studies of spectra and
pseudospectra show that operator constructions which survive repeated refinement
exhibit unusually slow growth of residual variation.  Ill-conditioned
constructions fail early and are discarded, leaving a statistically stable
subset that supports accumulation and lawlike behavior.

## Constraint
Finite instruments cannot support arbitrarily ill-conditioned operator
constructions.  Constructions whose residual variation grows faster than
accumulation can stabilize are operationally inadmissible.  Such constructions
cannot sustain refinement and therefore cannot function as devices of
measurement.

## Consequence
The effectiveness of computation is not guaranteed by mathematics alone.  It
arises from the selective retention of operator constructions that remain stable
under refinement.  Lawful structure emerges only where symbolic expression is
sufficiently easy that refinement does not destroy the distinctions it seeks to
sharpen.  Stability is not assumed in advance; it is revealed statistically by
those constructions that endure their own refinement.
