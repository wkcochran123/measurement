# The Halt Effect.

Source: `instrument/chapters/08.tex:1098`
Environment: `phenomenon`
Original title: `The Halt Effect.`

## Description

Not every admissible refinement admits a successor.  There exist boundary
configurations for which no further consistent update can be constructed.

If a partial ledger extension would require the separation of correlated
events without a permissible ordering, the update operator has no admissible
output.  The refinement process halts.

This is not a failure of computation but a structural limit of admissibility.
A halted ledger is not incomplete; it is complete in the only sense allowed by
the axioms.  No further event can be appended without violating global
consistency.

The halting of a causal sequence is therefore not destruction.  It is the
formal termination of admissible history.
