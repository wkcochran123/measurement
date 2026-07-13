# The Flat Rotation Curve Effect

Source: `instrument/chapters/09.tex:850`
Environment: `phenomenon`
Original title: `The Flat Rotation Curve Effect~\cite{shannon1948}`
Labels: `eq:rotation-viscosity`

## Description

**Note.** This is an informational consequence, not an astrophysical hypothesis.
No assumptions regarding doesn't-matter, mass distributions, or Newtonian
potentials are invoked.  The flattening derived here is the smooth
shadow of a discrete consistency requirement: non--commuting refinements
produce a curvature residue that appears, in the continuum, as a viscous
correction to transport.

**Note.** The argument presented here is not a dynamical model of galaxies.
It is a bandwidth computation in the precise sense of Shannon's theory of
communication~\cite{shannon1948}.  The causal network has a finite capacity
to convey distinguishable refinement, and therefore cannot reproduce
curvature variations whose informational rate exceeds this capacity.  The
flattening of the rotation profile reflects this saturation of
distinguishability bandwidth, not the presence of unobserved mass or
additional physical fields.



Every orbit reconstructed from finite measurements consists of two refinement
chains:
(i) the radial chain of recorded separations, and
(ii) the tangential chain of angular distinctions.
In an informationally flat geometry these chains commute---refining the radial
data then the angular record yields the same admissible completion as
refining them in the opposite order.

However, whenever local refinements disagree on their common boundary,
or when uncorrelant segments must be merged, the two refinement chains
fail to commute.  
By the Axiom of Ockham, no hidden structure may be inserted to enforce
commutativity, and by the Axiom of Boltzmann, the global record must
remain coherent.  
The irreducible mismatch is therefore a \emph{viscous residue}, the same
object defined in Section~\ref{sec:viscosity} as \emph{informational viscosity}.

In the smooth shadow, this residue manifests as a curvature-induced tangential
correction.  The observable effect is that the angular velocity $v_\theta(r)$
does \emph{not} decay as $r^{-1/2}$ even when the inferred radial refinements
would demand it.  Instead, informational viscosity contributes a
boundary-consistency correction that remains finite at large radii:
\begin{equation}
v_\theta(r)
\;=\;
v_{\mathrm{Newton}}(r)
\;+\;
\eta_{\mathrm{info}}
\left(
\frac{\partial}{\partial r}
\left(
\frac{1}{r}\,\frac{\partial r}{\partial \tau}
\right)
\right)
\;+\;
\mathcal{O}(\eta_{\mathrm{info}}^2),
\end{equation}
where $\eta_{\mathrm{info}}$ is the informational viscosity parameter introduced
in Equation~(6.x), and $\tau$ is the informational interval of
Section~\ref{sec:informational-interval}.  

At sufficiently large radii the Newtonian term becomes negligible while the
informational-viscosity term remains non-zero, leading to \emph{flattened
rotation curves}.
