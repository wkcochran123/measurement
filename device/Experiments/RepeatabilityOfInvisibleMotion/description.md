# Repeatability of Invisible Motion

Source: `instrument/chapters/06.tex:1071`
Environment: `phenomenon`
Original title: `Repeatability of Invisible Motion~\cite{bacon1620}`
Labels: `ex:repeatability`

## Description

Consider two independent observers, $A$ and $B$, who record the motion of a
particle between the same event anchors $x_i \prec x_{i+1}$.  Each observer
has finite resolution: any acceleration or inflection large enough to be
distinguishable produces a new event.  Both refine their instruments until
no further events are detected on the interval.

If hidden curvature existed between the anchors, further refinement would
create additional distinguishable records.  The absence of such records
forces each observer to recover the same polynomial of minimal degree.  Thus
both obtain a cubic patch on the interval.

Now let $A$ and $B$ exchange data and perform a joint refinement on a finer
grid.  Any disagreement in value, slope, or bending moment at a shared
anchor would itself generate an observable event.  To avoid contradiction,
the cubic patches must glue together with continuous $U$, $U'$, and $U''$.
In the dense refinement limit, the piecewise constant third derivative
converges to a continuous function whose integral vanishes on every
shrinking interval, yielding
\[
U^{(4)} = 0.
\]

Thus repeatability demands the Euler--Lagrange closure: if two observers can
refine their measurements indefinitely without producing new events, their
reconstructions must converge to the same cubic extremal.  Smooth dynamics
are therefore the unique histories that leave no trace.
