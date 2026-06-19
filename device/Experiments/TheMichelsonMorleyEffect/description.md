# The Michelson-Morley Effect

Source: `instrument/chapters/08.tex:904`
Environment: `phenomenon`
Original title: `The Michelson--Morley Effect~\cite{michelson1887}`
Labels: `ph:michelson`

## Description

**Note.** This phenomenon is not interpreted as a physical test of ether
hypotheses, relativistic postulates, or the dynamics of light. It is
treated purely as an informational experiment: a demonstration that
distinguishable events may propagate through a region in which no medium
is observed. The null result is therefore a statement about the structure
of admissible refinements and boundary conditions, not about physical
substrates.

**Note.** This thought experiment does not appeal to optical physics, wave
interference, or the existence of a medium.  It is a finite informational model
illustrating that the metric gauge must assign the same refinement cost
$\epsilon$ to extremal paths in all admissible directions.  No physical claims
about light or propagation are implied.


Consider an observer attempting to refine two extremal segments of equal
informational content, but aligned in different coordinate directions.  Let
$dx^{\mu}$ and $dy^{\mu}$ denote the local labels assigned to the two
segments.  Each segment is chosen such that its refinement requires the same
number of $\epsilon$--increments when described in the observer's own frame.

Now suppose the observer rotates their coordinate system.  After rotation, the
new labels are $dx'^{\mu} = \Lambda^{\mu}_{\ \nu} dx^{\nu}$ and
$dy'^{\mu} = \Lambda^{\mu}_{\ \nu} dy^{\nu}$.  The rotation
$\Lambda^{\mu}_{\ \nu}$ preserves causal order, so it is an admissible
transformation.  The question is whether the observer must still assign the
same informational interval $\tau$ to both segments after the rotation.

The Law of Causal Transport requires that the $\epsilon$--refinement counts for
both segments remain invariant:
\[
\tau_x^{2}
=
g_{\mu\nu}\, dx^{\mu} dx^{\nu},
\qquad
\tau_y^{2}
=
g_{\mu\nu}\, dy^{\mu} dy^{\nu}.
\]
After rotation, the transformed intervals are
\[
\tau_x'^{\,2}
=
g'_{\mu\nu}\, dx'^{\mu} dx'^{\nu},
\qquad
\tau_y'^{\,2}
=
g'_{\mu\nu}\, dy'^{\mu} dy'^{\nu}.
\]
Substituting the transformation rules for $dx'^{\mu}$, $dy'^{\mu}$, and
$g'_{\mu\nu}$ gives
\[
\tau_x'^{\,2}
=
g_{\alpha\beta}\, dx^{\alpha} dx^{\beta}
=
\tau_x^{2},
\qquad
\tau_y'^{\,2}
=
g_{\alpha\beta}\, dy^{\alpha} dy^{\beta}
=
\tau_y^{2}.
\]

Thus the observer must continue to assign the same informational interval to
the two extremal segments under any admissible rotation.  There is no freedom
to deform the refinement counts directionally: doing so would imply that
$\epsilon$--sized increments depend on orientation and would violate the
requirement that informational refinement be globally coherent.

This invariance is the informational analogue of isotropy.  It expresses that
the metric gauge $g_{\mu\nu}$ must refine extremal paths uniformly in all
directions: the number of $\epsilon$--increments needed to resolve a segment of
given informational content cannot depend on the coordinate orientation.

The Michelson--Morley experiment is therefore understood here not as a test of
a physical medium, but as a finite illustration of the isotropy of the metric
gauge.  The invariance of $\tau$ under rotations forces $g_{\mu\nu}$ to encode
a direction--independent refinement rule.  Section~\ref{sec:connection} develops
the compatible connection that propagates this rule under changes of frame.
