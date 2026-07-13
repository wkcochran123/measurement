# The Prover-Verifier Effect

Source: `instrument/chapters/11.tex:232`
Environment: `phenomenon`
Original title: `The Prover--Verifier Effect`
Labels: `ph:prover-verifier`

## Description

**Register.** Thought/computational experiment on the device's *role*: the engine is the *verifier* (near side --- it weighs a claimed value against its own reading and returns whether they agree and by how much they miss), and the world of admissible physical models is the *prover* (far side --- where a laboratory touches and signs the number). The device never derives; it checks. Used in Vol5 Ch7 §7.2 to name why the engine's claim is "not a capture" (verify, not derive --- SPEC's final API). Build verified: builds clean.

\textbf{Statement.}
The informational theory is not complete in isolation.  It requires the
existence of all admissible physical models as its prover, and serves only as
their verifier.  The causal ledger is the unique fixed point of this
interaction.

\textbf{Classical Context.}
A proof establishes that a conclusion follows from axioms, but it does not
guarantee that any model exists in which the axioms are realized.  Conversely,
a model demonstrates consistency of a structure, but does not explain why its
behavior is necessary.  Classical physics has oscillated between these roles:
sometimes as constructive dynamics (prover), sometimes as consistency
principle (verifier).

\textbf{Informational Interpretation.}
In this framework, the axioms of measurement and refinement define the rules
for admissible ledgers.  They do not specify which particular ledger must be
realized; they only constrain what is possible.

The physical universe plays the role of prover.  Every admissible physical
model is a concrete strategy for generating refinement records that obey the
axioms.  The informational theory plays the role of verifier.  It checks that
each proposed model corresponds to a ledger that can be extended without
contradiction.

The requirement that all admissible models exist somewhere in the space of
possible realizations is not metaphysical excess, but a completeness
condition.  Without such models, the axioms would be vacuous; with them, the
ledger is the unique object that all provers must approximate.

\textbf{Consequence.}
Physics is the smooth shadow of a two-player game.  The universe proposes
histories; the axioms of measurement either admit or reject them.  What is
called ``physical law'' is the intersection of all histories that can survive
this prover--verifier loop.

Quod erat demonstrandum: the theory does not eliminate physical models.  It
requires them.  The existence of a rich class of realizations is the
operational content of its truth.
