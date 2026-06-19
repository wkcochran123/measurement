# The Thermostat Effect

Source: `instrument/chapters/07.tex:2596`
Environment: `phenomenon`
Original title: `The Thermostat Effect`
Labels: `ph:thermostat`

## Description

\textbf{Statement.}
An admissible ledger exhibits self--regulation around low--strain states.  This
behavior appears macroscopically as thermostatic control.

\textbf{Mechanism.}
Let $\mathcal{I}$ denote the informational strain functional.  Refinement
updates do not merely seek $\delta \mathcal{I} = 0$, but dynamically suppress
deviations from locally stable minima.  When the ledger drifts away from a
low--strain configuration, subsequent refinements are biased toward restoring
that state.

\textbf{Low and High Water Marks.}
Stable configurations act as \emph{set points}.  
If $\delta^2 \mathcal{I} > 0$, deviations decay and the ledger returns to the
same admissible history (cooling/heating correction).  
If $\delta^2 \mathcal{I} < 0$, deviations amplify and the control loop fails.

\textbf{Interpretation.}
A thermostat is not a separate mechanism imposed on the system.  It is the
observable signature of second--variation stability in the refinement
functional.  The ledger enforces feedback because unstable histories are
inadmissible.

\textbf{Conclusion.}
Thermal equilibrium is not static; it is an actively maintained fixed point of
the causal bookkeeping process.
