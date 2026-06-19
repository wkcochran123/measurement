# The Feynman Diagram

Source: `instrument/chapters/10.tex:550`
Environment: `phenomenon`
Original title: `The Feynman Diagram~\cite{feynman1965}`
Labels: `te:feynman-full`

## Description

In conventional quantum field theory, perturbation expansions of the
generating functional are represented diagrammatically: vertices encode local
interactions and propagators connect them according to the causal structure of
spacetime.  In the causal formulation developed here, the same construction
arises directly from the Universe Tensor.

Each vertex corresponds to an event tensor $E_k \in T(V)$ contributing a
measurable distinction within the causal order.  A propagator corresponds to
an admissible contraction between event tensors---a bilinear map
\[
\langle E_i , E_j \rangle = \mathrm{Tr}(E_i^\top\, G\, E_j),
\]
where $G$ is the causal propagator enforcing Martin consistency between the
connected events.  The complete amplitude for a process is therefore the
contraction of the ordered product
\[
U_n = \sum_{k=1}^{n} E_k,
\]
with all admissible propagators.  The resulting scalar invariants of $U_n$
constitute the measurable quantities of the theory.

Thus, a Feynman diagram is the graphical representation of a tensor
contraction in the causal algebra: each diagram corresponds to one term in the
finite expansion of the Universe Tensor, and summing over all diagrams is
equivalent to enforcing global consistency of causal order.  What appears in
standard field theory as a perturbation series is, in this formalism, a finite
enumeration of distinguishable causal relations---a bookkeeping identity
derived from the Reciprocity Law rather than using calculus.
