# LiDAR

Source: `instrument/chapters/07.tex:105`
Environment: `phenomenon`
Original title: `LiDAR~\cite{christian2013}`
Labels: `te:laser-tracking`

## Description

Two identical observers, A and B, begin co-located with synchronized clocks. Observer B
embarks on a journey involving periods of acceleration, while observer A remains at the
origin of an idealized inertial frame. We \emph{explicitly neglect} the gravitational and
relativistic influence of Earth, the Sun, Sagittarius~A*, and all other bodies; spacetime is
treated as Minkowski over the region of interest.

Rather than waiting for reunion, A continuously tracks B by emitting a stream of
monochromatic laser pulses. Each pulse is timestamped in A’s notebook when fired, and
timestamped again when the reflected pulse is received from B’s retroreflector.

Every fired pulse is a distinguishable event; every received pulse is another. If B follows a
complicated accelerative path, then the return times of the pulses form a more densely
refined sequence than the symmetric record A would observe if B were inertial. The point
is not energy or Doppler shift. The informational content of the record increases: each
round-trip establishes a new ordered pair of emission and reception, constraining B’s
admissible motion.

If B were inertial, the spacings of the returned timestamps would follow the unique minimal
interpolant that introduces no unobserved curvature. But acceleration forces extra
refinements: the return times become uneven in a way that cannot be reconciled with a
coasting trajectory. These “irregularities’’ are not interpreted through differential
equations; they are simply distinct events that must be merged into A’s causal record.

When B returns, both observers merge their sequences. A’s laser notebook contains a much
longer chain: every emission and every reflection has already placed constraints on B’s path.
B’s local clock, by contrast, has recorded only its own internal ticks and those refinements
forced by onboard events. The merge therefore requires A to reconcile a larger
informational workload, while B performs a smaller one. Consistent ordering assigns the
larger count of admissible distinctions to A, and the smaller to B. The result is that A’s
proper time is larger---she has the denser causal record.

In the smooth limit, the same count enforces the classical dilation formula of relativity. But
here the conclusion is purely informational: acceleration introduces refinements, refinements
create more events, and more events imply more work when histories are coherently merged.
Time dilation is the bookkeeping of laser-certified distinctions, not a geometric postulate.

This informational mechanism therefore recovers the ability to compute the Lorentz
contraction posed in Thought Experiment~\ref{te:boosting-velocity} through the update rule
\(E_k = \Psi\!\bigl(e_k \cap \Rhat(e_{k-1})\bigr)\), using only the observers’ laboratory notebooks.
