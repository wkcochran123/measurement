# The da Vinci-Coulomb Effect

Source: `instrument/chapters/01.tex:1814`
Environment: `phenom`
Original title: `The da Vinci--Coulomb Effect~\cite{davinci1493,coulomb1785}`
Labels: `ph:static-friction`

## Statement
The onset of motion under static friction constitutes a finite, distinguishable
event whose occurrence cannot be predicted from prior refinements of the
experimental ledger alone. The application of force may refine the ledger indefinitely
without determining when motion will begin.

## Origin
Leonardo da Vinci observed that bodies in contact resist motion up to a
threshold that depends on load but not on apparent contact area. Amontons later
identified these regularities empirically, and Coulomb formalized the
distinction between static and kinetic friction, characterizing the transition
between them as abrupt and irreversible. Before this transition, no motion
occurs; after it, motion proceeds continuously. The transition itself is an
event.

## Observation
The familiar inequality $|F| \ge \mu |N|$ expresses a bound in representation,
but it does not encode a procedure that computes $\mu$ from the record. It
establishes only one admissible side of estimation, and therefore carries
model--side noise analogous to the Chaitin Effect: a bound can be declared
without being operationally executable. Recovery of the physical threshold
$\mu$ is instead a ledger-derived invariant, forced only after many empirical
refinements bracket the minimal normal-load transitions at which ``slip''
becomes distinguishable from ``stick.'' As with any finite refinement
sequence, the record may accumulate confirmations, but no finite criterion
certifies that convergence has completed. The Kantian ``moment of slip'' is
therefore not a primitive instant, but the least-refined record completion
that has survived both model inequality and experimental noise, without any
method to assert that further trials would cease to refine the threshold.

## Constraint
Some invariants are not available to a single refinement of the record, but can
only be estimated through the accumulation of many distinguishable trials whose
completion itself takes indexed steps to obtain. The invariant is therefore
coupled to the observer's chronometry: it requires ledger time, not merely model
consistency, to be approximated.

## Consequence
Static friction demonstrates that Phenomenon~\ref{ph:chaitin} is not a peculiarity of
formal computation, but a universal constraint on measurement.
Here, the system is fully physical, finite, and repeatable, and the governing
rules are well understood. Yet the ledger admits no rule that determines
when the decisive event will occur. The event of slip becomes known only
at the moment it becomes admissible, when the measurement that implies motion is 
recorded as fact. As with
halting and $\Omega$, the absence of a predictive law is not due to instrumental noise, error,
or incomplete specification, but to the structure of refinement itself. 
Phenomenon~\ref{ph:static-friction} therefore shows that lawlessness of this form arises
wherever events are defined by thresholds and silence. Computation does not
introduce the limitation; it reveals it. The Chaitin Effect is a general feature
of finite observation, not a property of abstract machines.
