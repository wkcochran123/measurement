# The Quicksand Effect

Source: `instrument/chapters/06.tex:1484`
Environment: `phenomenon`
Original title: `The Quicksand Effect~\cite{batchelor1967,bonn2005}`
Labels: `ph:viscosity-quicksand`

## Description

**Note.** In a continuous fluid, buoyancy is described by Archimedes' principle~\cite{archimedes1912}: an 
immersed body floats when the upward force from displaced fluid balances its 
weight~\cite{batchelor1967}. Bonn et al.~\cite{bonn2005} show that quicksand, 
though a granular suspension rather than a true fluid, exhibits a nearby 
buoyant behavior: objects settle only to a finite depth and then float, 
reaching an equilibrium set by density matching, yield stress, and local 
fluidization. The macroscopic effect resembles (and, to a certain coarseness 
of refinement, is modeled by) Archimedes' principle, even though its 
microscopic origin is entirely different. These physical observations serve 
only as an analogy for the informational phenomenon described here; they do 
not constrain the model. They illustrate how a finite set of admissible states 
may appear, in the smooth limit, as a buoyant equilibrium.

**Note.** The phenomenon described here concerns the irreversible, informational 
component of fluid mechanics: the resistance to refinement below the minimum 
distinguishable scale $\delta$. It is not a complete account of physical 
viscosity, which depends on a finite third parameter $\Theta$ (see Coda: 
Navier--Stokes as a Finite Third Parameter, Chapter~3) and requires an 
independent kinematic assumption relating shear stress to velocity gradients. 
The informational viscosity $\Psi_\delta$ treated here reflects only the 
constraints of Causal Order and informational Minimality; it captures the 
coarse, irreducible structure that remains when all sub-$\delta$ refinements 
are suppressed.

**Note.** \emph{A person floats on quicksand, rather than sinks}~\cite{bonn2005}



Consider an agent $E$ attempting to move through a medium governed solely by 
distinguishability. Before contact, the mathematical continuum admits an 
infinite family of smooth paths $\Phi_i$, distinguished by arbitrarily small 
variations in curvature.

Once $E$ enters the medium, the informational constraints become active. By 
Axiom~\ref{ax:planck}, there exists a minimum distinguishable scale $\delta$. 
Any displacement smaller than $\delta$ fails to generate a new event. The 
continuum therefore collapses to a finite chain of $\delta$--compatible 
anchors,
\[
    \Psi_\delta=\{x_1,\dots,x_N\},
\]
representing all positions that can be observationally distinguished.

The medium exhibits an informational \emph{viscosity}: any attempted motion 
that introduces sub-$\delta$ curvature is resisted and cancelled, keeping $E$ 
pinned to the nearest admissible anchor. Only when the displacement exceeds 
the refinement threshold does $E$ transition from $x_k$ to $x_{k+1}$.

By Proposition~\ref{prop:pigeonhole}, the infinite microscopic variations 
beneath the surface collapse into the finite observational buckets of 
$\Psi_\delta$. Informational minimality (Axiom~\ref{ax:ockham}) then forces 
the unique discrete closure consistent with the anchors and containing no 
unrecorded structure: the discrete spline $\Psi_\delta$.

This is the viscosity of quicksand: the resistance to refinement below the 
minimum distinguishable scale $\delta$. Any attempted motion that fails to 
produce a new admissible distinction is suppressed, and the system remains at 
the nearest anchor in $\Psi_\delta$. In the smooth shadow, this appears as the 
buoyant or viscous equilibrium observed by Bonn and others, where 
a person floats because further descent would require the granular medium to 
rearrange at scales smaller than the yield threshold of individual particles 
of sand. Physically, the grains simply stop moving; informationally, no 
additional distinctions can be recorded. The collapse of the infinitely many 
ideal paths $\Phi_i$ into the single admissible sequence $\Psi_\delta$ is 
therefore mirrored by the granular equilibrium: motion ceases not because of 
any continuous force law, but because neither the sand nor the informational 
model permits sub-$\delta$ refinements.
