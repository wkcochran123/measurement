# The Chaitin Effect

Source: `instrument/chapters/01.tex:1727`
Environment: `phenom`
Original title: `The Chaitin Effect~\cite{chaitin1975}`
Labels: `ph:chaitin-effect`

## Statement
A measurement record may consist entirely of finite and
distinguishable events, and yet admit no extractable dynamical law. The
accumulation of facts alone does not guarantee the emergence of a truth.

**Register.** Thought/computational experiment whose job is to *gesture at the far side* and hold it open: Chaitin's halting probability is definable exactly yet computable never --- a number the machine can name and cannot derive, so it marks the un-derivable truth without pronouncing on it. Used in Vol5 Ch7 §7.6 as the data-side face of the finiteness fence (finite facts accumulate; the derived value does not follow). Build verified: `claim_holds` depends on `[propext]` only.

## Origin
Chaitin introduced the halting probability $\Omega$ by fixing a universal
prefix-free computing device and aggregating the termination events of all
finite programs. Each contributing event corresponds to the successful
completion of a specific, finitely describable procedure. Although each such
event is individually verifiable, the collection as a whole resists
compression into a predictive rule.

## Observation
Each refinement contributing to $\Omega$ records a distinct halting event.
The ledger grows by the verified completion of finite procedures, each of which
is admissible under the Axioms of Measurement. However, no relation among past
refinements constrains when the next halting event will occur, or whether it
will occur at all. The record accumulates without contradiction, yet without
pattern.

## Constraint
Let $\mathcal{L}_t$ denote the ledger formed by recording halting events up to
step $t$. No rule derived from $\mathcal{L}_t$ constrains the set of
possible future refinements. In particular, no operator may predict, from any
finite prefix of the record, which additional procedures will halt. The ledger
is precise, but admits no law linking one refinement to the next (see
Phenomenon~\ref{ph:truth-effect}).

## Consequence
$\Omega$ marks an epistemic boundary of measurement. It demonstrates that the
existence of a set of well-defined, well-ordered records does not imply the
existence of an extractable law governing its continuation. Phenomenon~\ref{ph:chaitin} 
therefore realizes Phenomenon~\ref{ph:hume-effect} in its strongest form: even an unbounded
accumulation of facts may fail to provide any predictive value at all.
