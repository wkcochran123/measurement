# The Aharonov-Bohm Effect

Source: `instrument/chapters/10.tex:841`
Environment: `phenomenon`
Original title: `The Aharonov--Bohm Effect~\cite{aharonov1959}`

## Description

The Aharonov--Bohm experiment demonstrates that the physically relevant
quantity in electromagnetism is not the field strength $F_{\mu\nu}$ alone but
the connection $A_\mu$ that governs causal phase transport.

Consider an electron beam split into two coherent branches encircling a region
containing a confined magnetic flux $\Phi$, with no field present along either
path.  In the causal formulation, each branch corresponds to a sequence of
ordered events $\{E_{1,k}\}$ and $\{E_{2,k}\}$ transported by the local gauge
connection $A_\mu$.  The Reciprocity Law requires that each infinitesimal
update preserve order:
\[
E_{k+1} = E_k + \Phi^{-1}(A_\mu\,dx^\mu),
\]
so that the cumulative phase acquired along a closed loop is
\[
\Delta \phi = \frac{e}{\hbar} \oint A_\mu\,dx^\mu = \frac{e\Phi}{\hbar}.
\]

Although the magnetic field vanishes along both paths
($F_{\mu\nu}=0$ locally), the two causal chains differ by a holonomy in the
connection---an informational mismatch in the bookkeeping of phase.
When the beams are recombined, their interference pattern depends on
$\Delta\phi$: shifting continuously as the enclosed flux changes by fractions
of the flux quantum $h/e$.

In the causal gauge picture, this effect shows that the universe tensor
records not merely local field strengths but the global consistency of the
connection.  The vector potential $A_\mu$ is the differential form of causal
memory; its holonomy measures how distinction is transported around a loop.
The Aharonov--Bohm interference is thus the experimental detection of a
nontrivial element of the causal holonomy group---the smallest observable
instance of curvature without force.
