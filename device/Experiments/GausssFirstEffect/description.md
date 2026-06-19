# Gauss's First Effect

Source: `instrument/chapters/02.tex:2447`
Environment: `phenom`
Original title: `Gauss's First Effect~\cite{gauss1809}`
Labels: `ph:gauss-first`

## Statement
When an instrument is applied repeatedly under a fixed encoding and decoding
scheme, the distribution of ledger entries converges toward a stable bell-shaped
form characterized by a mean and a variance.  These parameters arise from the
structure of repetition itself, not from any assumed smoothness of the
underlying phenomenon.

## Origin
Gauss encountered this effect in the analysis of astronomical observations, where
repeated measurements of the same quantity produced clustered deviations about
a central value~\cite{gauss1809}.  The normal curve was introduced not as a law of
nature, but as a practical representation of error arising from repeated
observation with a fixed instrument.  Its justification was empirical and
operational rather than metaphysical.

## Observation
In repeated trials, individual ledger entries vary, yet their aggregate exhibits
remarkable regularity.  The sample mean stabilizes under refinement, and the
spread of outcomes admits a consistent numerical summary.  This regularity
appears even when the underlying phenomenon lacks any intrinsic randomness,
provided the instrument enforces a stable alphabet and repetition protocol.

## Constraint
The effect depends critically on representational invariance.  If the encoding
map, decoding map, or ledger update rule changes between trials, the bell-shaped
distribution dissolves.  No appeal to a continuous error field or hidden noise
source is permitted; only those distinctions explicitly committed to the ledger
may contribute to the observed distribution.

## Consequence
Mean and variance are not properties of the phenomenon in isolation, but of the
instrument under repetition.  The bell curve reflects the accumulation of
discrete ledger entries produced by a fixed device, not an underlying continuous
law.  Phenomenon~\ref{ph:gauss-first} therefore grounds statistical regularity in the
structure of measurement itself, establishing repetition as a generative act
from which probability emerges.
