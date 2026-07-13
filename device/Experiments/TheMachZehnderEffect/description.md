# The Mach-Zehnder Effect

Source: `instrument/chapters/07.tex:999`
Environment: `phenomenon`
Original title: `The Mach--Zehnder Effect~\cite{zehnder1891}`
Labels: `te:mach-zehnder-updated`

## Description

**Register.** Physical experiment, treated as a *representation*: a model of how reading which of two indistinguishable refinements was taken abolishes their recombination, on the near side --- the touch it describes is the machine's own reading, never the photon-in-itself. Used in Vol5 Ch3 §3.1 as the sharpest instance of "no passive reading" (the reading is the very act that tells the paths apart). Build verified: `claim_holds` axiom-clean (no axioms).

**Note.** Although the Mach--Zehnder device originates in optical physics, the
informational structure it exhibits does not depend on any physical
mechanism.  The branching and recombination of admissible refinements is a
purely combinatorial phenomenon: it arises whenever two indistinguishable
paths diverge, evolve under independent refinements, and reunite at a shared
boundary.  No metric, phase, or wave dynamics are assumed.


A single photon enters a Mach--Zehnder interferometer. At the first beam splitter, a single
input event $e_0$ leads to two admissible refinements, $e_1$ (upper path) and $e_2$ (lower
path). Both produce valid causal chains: each path accumulates its own ordered list of
refinements---reflections, delays, and phase shifts---and each yields an accumulated tensor
$\U^{(1)}$ and $\U^{(2)}$ satisfying Martin's Condition. No experiment in either arm can
distinguish which refinement is ``real'': both histories are admissible and neither produces a
contradiction. The interferometer therefore carries two coexisting, consistent ledgers.

At the second beam splitter, the detection event $e_f$ must be recorded as a strict update.
By Axiom~\ref{ax:planck}, the refinement $e_f$ must fold into the accumulated state. The
interaction operator computes
\[
\U_{\mathrm{final}} = f(\U^{(1)},\U^{(2)}),
\]
the minimal accumulated tensor consistent with both paths. All hypothetical histories in
which the arrival at $e_f$ contradicts either ledger are removed.

Interference is the informational comparison of the two causal chains. If their accumulated
phase---a bookkept record of distinguishability---is equal modulo $2\pi$, the paths are
informationally indistinguishable at the boundary. The fold produces a single ledger: both
paths merge without creating new refinements. If the accumulated phase differs by $\pi$, the
asymmetric parts of the update factors cancel under the fold, and $e_f$ becomes inadmissible.
No destructive force is invoked; the cancellation expresses the fact that no consistent
ledger can be formed with that ordering.

Thus, ``superposition'' is the coexistence of multiple valid, Martin-consistent refinements
until detection forces a non-degenerate fold. The Mach--Zehnder interferometer does not show
a particle traveling two paths; it shows that causal histories can remain distinct and
simultaneously admissible until the interaction operator selects the unique ordering that
avoids contradiction at the boundary.
