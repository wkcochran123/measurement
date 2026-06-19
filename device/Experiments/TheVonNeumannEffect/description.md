# The von Neumann Effect

Source: `instrument/chapters/08.tex:179`
Environment: `phenomenon`
Original title: `The von Neumann Effect~\cite{vonneumann1947}`
Labels: `ph:informational-quantum-effect`

## Description

\textbf{Statement.}
Every admissible measurement process possesses a nonzero minimum scale of
distinction below which no further refinement is possible.

\medskip

\textbf{Description.}
Refinement proceeds by adding distinguishable events to the causal ledger.
However, distinguishability itself is finite. A measurement cannot encode
arbitrarily small differences; it can only record distinctions down to a fixed
resolution bound.

This mirrors the behavior of numerical computation. In finite linear systems,
repeated application of linear operators saturates at a machine-dependent
precision. Once rounding error dominates, further operations do not increase
accuracy. The system has reached its informational floor.

In the informational framework, this floor is not technological. It is
axiomatic.

\medskip

\textbf{Noise and Saturation.}
As refinement approaches this lower bound, noise ceases to be suppressible.
Additional distinctions no longer produce new admissible events. Instead,
attempted refinements collapse into existing records. The informational ledger
saturates.

This saturation forces a quantization of admissible structure. The
interpolating spline may assign analytic values between anchor points, but
those values cannot correspond to distinct admissible refinements once they
differ by less than the minimal distinguishable scale.

\medskip

\textbf{Phenomenon.}
We call this forced discreteness the \emph{Informational Quantum Effect}. It
is not the emergence of particles or energy levels. It is the inevitability of
a smallest unit of distinguishability in any coherent measurement system.

The quantum is not imposed by physics. It is imposed by logic.

While von Neumann and Goldstine demonstrated that finite-precision arithmetic
admits pathological cases of instability~\cite{vonneumann1947}, Strang and
others have emphasized that matrices arising from physical and empirical
measurement are typically well-conditioned and structured, so these worst-case
failures are rarely observed in practice~\cite{strang1980}.
