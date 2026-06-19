# The Conservation of Energy

Source: `instrument/chapters/10.tex:490`
Environment: `phenomenon`
Original title: `The Conservation of Energy~\cite{noether1918}`

## Description

Consider a real Klein--Gordon field $\phi$ in flat spacetime with
\[
\mathcal{L} \;=\; \tfrac12\,\partial_\mu\phi\,\partial^\mu\phi \;-\; \tfrac12\,m^2\phi^2,
\qquad
\eta_{\mu\nu}=\mathrm{diag}(-,+,+,+).
\]
The (symmetric) stress--energy tensor is
\[
T^{\mu\nu} \;=\; \partial^\mu\phi\,\partial^\nu\phi \;-\; \eta^{\mu\nu}\mathcal{L}.
\]
Energy density and energy flux are then
\[
\mathcal{E}\;\equiv\;T^{00}
= \tfrac12\!\left(\dot\phi^2 + |\nabla\phi|^2 + m^2\phi^2\right),
\qquad
S^i \;\equiv\; T^{0i}
= \dot\phi\,\partial^i\phi .
\]

\paragraph{Continuity (bookkeeping) equation.}
Using the Euler--Lagrange equation $\Box\phi + m^2\phi=0$
and differentiating,
\[
\partial_t \mathcal{E}
= \dot\phi\,\ddot\phi + \nabla\phi\cdot\nabla\dot\phi + m^2\phi\,\dot\phi
= \dot\phi\big(\ddot\phi - \nabla^2\phi + m^2\phi\big) + \nabla\!\cdot(\dot\phi\,\nabla\phi)
= \nabla\!\cdot(\dot\phi\,\nabla\phi),
\]
so
\[
\partial_t \mathcal{E} + \nabla\!\cdot(-\dot\phi\,\nabla\phi) = 0
\quad\Longleftrightarrow\quad
\partial_\mu T^{\mu 0} = 0.
\]
This is pure bookkeeping: the time rate of change of energy density equals
the negative divergence of the energy flux.

\paragraph{Integrated conservation law.}
Integrate over a fixed region $\mathcal{R}$ with outward normal $\mathbf{n}$:
\[
\frac{d}{dt}\int_{\mathcal{R}} \mathcal{E}\,d^3x
= -\int_{\partial\mathcal{R}} \mathbf{S}\cdot\mathbf{n}\,dS.
\]
If fields vanish (or are periodic) on the boundary so the surface term is
zero, then the total energy
\[
E \;=\; \int_{\mathbb{R}^3} \mathcal{E}\, d^3x
\]
is conserved: $\tfrac{dE}{dt}=0$.

\paragraph{Causal bookkeeping interpretation.}
$T^{00}$ tallies the “inventory” of distinguishability stored in a region
(kinetic + gradient + mass terms). The flux $T^{0i}$ records how that
inventory flows across the boundary. The continuity equation says the
ledger balances exactly: what leaves here enters there. Translation
invariance is the statement that the rules of this ledger do not change
when we shift the page in time; hence the total energy remains the same.
