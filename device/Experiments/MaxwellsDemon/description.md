# Maxwell's Demon

Source: `instrument/chapters/11.tex:101`
Environment: `phenomenon`
Original title: `Maxwell's Demon~\cite{maxwell1865}`

## Description

Consider a classical gas divided by a partition with a single gate controlled by a demon who measures particle velocities and opens the gate selectively.  
Let $M$ denote the demon's measurement operator and $U$ the physical evolution of the gas.  
If $M$ and $U$ commute—$[M,U]=0$—the demon's observation does not alter the causal order: measurement and evolution can be exchanged without changing the macrostate.  
But in reality $[M,U]\neq0$: the act of measurement refines the partition of distinguishable states, altering the subsequent evolution.  
This non-commutativity forces the entropy balance
\[
\Delta S_{\text{gas}}+\Delta S_{\text{demon}}\;=\;k_{\mathrm B}\ln\!\left|\Omega_{\text{joint}}\right|\;>\;0,
\]
because the demon’s internal record adds new causal distinctions to the universe tensor even as it reduces them locally.  

Operationally, the demon cannot perform a measurement without joining the measured system’s causal order; the refinement of its internal partition $P_{n}\!\rightarrow\!P_{n+1}$ increases the global count of distinguishable configurations.  
The apparent violation of the Second Law disappears: the measurement and evolution operators fail to commute, and that failure \emph{is} the entropy production term.  
Thus Maxwell’s demon exemplifies the theorem $\Delta S\ge0$: informational refinement in one domain demands compensating coarsening in another so that the global order remains consistent.
