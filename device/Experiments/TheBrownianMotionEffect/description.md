# The Brownian Motion Effect

Source: `instrument/chapters/07.tex:1811`
Environment: `phenomenon`
Original title: `The Brownian Motion Effect`
Labels: `sec:brownian-quantum`, `eq:brownian-update`, `eq:brownian-diffusion`, `eq:schrodinger-free`

## Description

**Register.** Physical experiment, treated as a *representation*, on the near side: the coarse record's jitter is modelled as the projection's fiber seen *in motion* (finite resolution leaves micro-orderings the ledger cannot tell apart, so the kept summary wanders among them and the wandering reads as chance) --- a fact about the reading's resolution, not a source of randomness in the world. What the record does between the forgotten micro-states stays on the far side, unwatched. Used in Vol5 Ch1 §1.3 as the fiber's *dynamic* face (distinct from the static lossiness of §1.3.p6). Build verified: `claim_holds` depends on `[propext, Quot.sound]`.

Brownian motion can be interpreted as a quantum informational phenomenon in
the present framework.  The source of randomness is not mechanical noise but
\emph{finite causal resolution}: each refinement step leaves a family of
equally admissible micro--orderings that the ledger cannot distinguish.  The
coarse record therefore evolves stochastically.

\paragraph{Stochastic Reconciliation at Finite Resolution.}

Let $u_i^k$ be the normalized refinement count on cell $i$ at time $t_k$.
When the observer cannot resolve all admissible distinctions at scale
$\Delta x$, the symmetric smoothing update acquires an irreducible stochastic
term:
\begin{equation}
  u_i^{k+1}
  =
  u_i^k
  +
  \frac{\kappa\,\Delta t}{\Delta x^2}
  (u_{i+1}^k - 2u_i^k + u_{i-1}^k)
  +
  \sqrt{2D\,\Delta t}\;\xi_i^k,
  \qquad \mathbb{E}[\xi_i^k]=0,\;\mathbb{E}[(\xi_i^k)^2]=1.
\end{equation}
The deterministic part is the symmetric reconciliation enforced by the Law of
Spline Sufficiency; the random term is the ledger's irreducible uncertainty at
the observation scale.

\paragraph{Smooth Shadow: Diffusion as Quantum Measure.}

Under refinement $\Delta x,\Delta t\to 0$ with $D$ fixed, the central limit
theorem implies convergence of \eqref{eq:brownian-update} to the diffusion
equation for the coarse density $u(x,t)$:
\begin{equation}
  u_t = D\,u_{xx}.
\end{equation}
Here $D$ is the \emph{informational diffusion coefficient}: the effective
bandwidth of unresolved distinctions per unit time.

\paragraph{Bridge to Schr\"odinger via Analytic Continuation.}

The free Schr\"odinger equation is related to diffusion by analytic
continuation of time.  Setting
\(
  D = \tfrac{\hbar}{2m}
\)
and $t \mapsto -\,i t$ maps \eqref{eq:brownian-diffusion} to
\begin{equation}
  i\,\hbar\,\partial_t \Psi = -\,\frac{\hbar^2}{2m}\,\partial_{xx}\Psi,
\end{equation}
i.e., the smooth shadow of unresolved, symmetric refinement at fixed
informational bandwidth equals the quantum free evolution with Planck scale
$\hbar$.  In this sense, Brownian motion is \emph{quantized uncertainty}:
$\hbar$ calibrates the minimal unresolved action, while $D$ measures the rate
at which that unresolved structure propagates statistically.

\paragraph{Consistency with the Two Laws.}

- \emph{Spline Sufficiency} ensures no spurious extrema: the stochastic update
  remains a projection into the admissible class almost surely.
- \emph{Boundary Consistency} fixes oriented interfaces; adding an upwind
  drift $c$ to \eqref{eq:brownian-update} yields the standard
  advection--diffusion (Fokker--Planck) limit.

**Note.** This construction shows \emph{how} quantum evolution can arise from
measurement limits: if the ledger's unresolved bandwidth $D$ is fixed by a
Planck scale, diffusion analytically continues to Schr\"odinger dynamics.  It
does not assert that nature must realize this identification in every regime.
