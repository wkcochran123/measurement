# The Angular Momentum Effect

Source: `instrument/chapters/09.tex:915`
Environment: `phenomenon`
Original title: `The Angular Momentum Effect`
Labels: `ph:ang-momentum`

## Description

A bicycle wheel of mass $M$ and radius $R$ is mounted on low--friction
bearings.  The wheel is brought to a steady rotational speed and its angular
velocity is measured using a stroboscope or optical tachometer.

The angular momentum is then \emph{observed and computed} from measurable
quantities:
\[
L = I \,\omega ,
\]
where the moment of inertia of the wheel is
\[
I \approx M R^2 ,
\]
and the angular velocity is
\[
\omega = 2\pi f ,
\]
with $f$ the observed rotation frequency.

For example, a wheel with
\[
M = 2.0~\mathrm{kg}, \qquad R = 0.33~\mathrm{m}, \qquad f = 5~\mathrm{Hz}
\]
has
\[
\omega = 31.4~\mathrm{rad/s}, \qquad
I \approx 0.218~\mathrm{kg\,m^2},
\qquad
L \approx 6.85~\mathrm{kg\,m^2/s}.
\]

This value is not inferred from theory but reconstructed directly from
observable mass, geometry, and frequency.  The persistence of this quantity
under external perturbation constitutes the observational phenomenon of
angular momentum.

The observational computation above admits a strictly weaker informational
representation.  Although the applied influences are linear and act along
distinct spatial directions, the admissible record does not require a full
two--dimensional description of the induced motion.  The record may be
compressed by replacing independent linear displacements with a single angular
coordinate.

Rather than tracking the motion in a full planar basis, the admissible
description collapses to the pair
\[
(r,\theta),
\]
where $r$ encodes radial admissibility and $\theta$ encodes cyclic refinement.
The angular component carries half the effective dimensional burden of a
Cartesian basis, as the refinement is constrained to a closed orbit.

Informationally, this compression is not an approximation but a necessity:
the coherent record cannot sustain independent degrees of freedom once the
cyclic constraint becomes admissible.  The refinement therefore induces a
second--variational structure.  After the first (Jacobi) variation fixes the
admissible path, the remaining admissible deformations appear only in the
angular coordinate.

The persistence of angular momentum is, in this sense, not a force law but a
second--variational residue of admissible compression.
