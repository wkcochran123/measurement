# The Fourier-Nyquist Effect

Source: `instrument/chapters/02.tex:977`
Environment: `phenom`
Original title: `The Fourier--Nyquist Effect~\cite{fourier1822,nyquist1928}`
Labels: `ph:sampling`

## Statement
Exact decomposition of measurement is lawful if and only if the refinement of
the record is sufficient to permit recovery.  Decomposition may be applied
internally to measured distinctions, but no component may be recovered unless
the ledger commits distinctions densely enough to support inversion.

## Origin
Fourier introduced decomposition as a method for representing complex phenomena
through orthogonal components, showing that structured behavior could be
analyzed by factorization rather than direct inspection~\cite{fourier1822}.
Nyquist later identified the conditions under which such decompositions remain
recoverable when measurements are recorded sequentially~\cite{nyquist1928}.
Together, their work established that decomposition alone is insufficient:
recoverability depends on the rate and structure of refinement.

## Observation
Physical instruments routinely employ internal decomposition to resolve
structure from composite measurements.  Optical imaging, radio transmission,
and digital signal processing all separate admissible components from a single
sensor response.  In each case, the ledger records only sequential samples, while
decomposition occurs internally.  Successful reconstruction depends not on the
continuity of the underlying process, but on whether the recorded refinements
are sufficient to support exact recovery.

## Constraint
No decomposition may introduce distinctions not licensed by measurement.
Components resolved by internal structure must correspond exactly to refinements
that can be recovered from the ledger.  If refinement is too sparse, the
decomposition ceases to be exact, and recoverability is lost.

## Consequence
Phenomenon~\ref{ph:sampling} identifies the boundary between lawful and unlawful
decomposition.  Apparent continuity, smooth spectra, or rich intermediate
structure do not guarantee recoverability.  What matters is whether sequential
commitment to the ledger is dense enough to support inversion.  Decomposition is
therefore not a metaphysical property of phenomena, but an instrumental
achievement constrained by refinement.
