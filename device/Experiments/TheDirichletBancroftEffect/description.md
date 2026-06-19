# The Dirichlet-Bancroft Effect

Source: `instrument/chapters/03.tex:555`
Environment: `phenom`
Original title: `The Dirichlet--Bancroft Effect~\cite{dirichlet1850,bancroft1985}`
Labels: `ph:db`

## Statement
A fully specified geometric model may admit multiple admissible solutions
until sufficient boundary or reception constraints are committed to the
ledger. Uniqueness arises not from the governing equations alone, but from
additional admissible data.

## Origin
Dirichlet formalized the role of boundary conditions in determining unique
solutions to differential equations~\cite{dirichlet1850}. A governing relation
may be exact and internally consistent, yet without specified boundary data it
admits multiple realizations. Bancroft later demonstrated that the algebraic
system underlying GPS position determination similarly admits multiple
solutions when insufficient constraints are imposed~\cite{bancroft1985}. In
both cases, structural completeness of the model does not guarantee uniqueness
of realization.

## Observation
In GPS, satellite positions and relativistic corrections are fully specified.
The pseudorange equations are exact. Yet with only three satellite receptions,
the system generally produces two geometrically valid intersections. One lies
near the Earth’s surface; the other lies far into space. Both satisfy the
modeled propagation relations.

In practice, it is rare that the receiver is located in space. Implementations
often incorporate admissibility assumptions that constrain the solution to the
Earth-bound branch, effectively eliding the extraneous realization. The ledger
is supplemented either by additional reception events or by environmental
constraints that function as boundary data.

## Constraint
No geometric specification alone suffices to eliminate multiplicity when
temporal parameters remain unresolved. Only additional committed events or
boundary admissibility conditions may collapse the solution space to a unique
realization.

## Invariant
The invariant is the propagation relation encoded in the pseudorange equations.
This relation remains stable across all admissible solutions. Multiplicity
arises not from failure of the invariant, but from insufficient refinement of
temporal commitment.

## Refinement
Under refinement—such as reception from a fourth satellite or incorporation of
environmental boundary constraints—the residual temporal degree of freedom is
eliminated. The extraneous branch disappears, and the solution becomes unique.
Refinement sharpens realization without altering the invariant.

## Consequence
The Dirichlet--Bancroft Effect demonstrates that model completeness and ledger
sufficiency are distinct. Even when geometry and relativistic corrections are
exact, admissible history must supply the final constraint. Uniqueness is not
imposed by equations alone, but by the accumulation of committed events.
