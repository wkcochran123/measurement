# The Navier-Stokes effect

Source: `instrument/chapters/09.tex:423`
Environment: `phenomenon`
Original title: `The Navier--Stokes effect~\cite{navier1822,stokes1845}`

## Description

**Note.** This is an informational phenomenon.  No physical fluid or continuum is
assumed.  The classical Navier--Stokes equations are quoted only as the smooth
shadow of discrete refinement transport.  The phenomenon illustrates that the
appearance of viscous terms is nothing more than the accumulation of
informational strain under non-closing updates.


Classical fluid dynamics records the transport of a state variable through
space and time.  The Navier--Stokes equation,
\[
\partial_t u + (u \cdot \nabla)u = -\nabla p + \nu\,\Delta u,
\]
is traditionally interpreted as the momentum balance of a viscous medium.

Informationally, this equation expresses something more fundamental:
\emph{closure requires correction}.  The convective term
\(
(u \cdot \nabla)u
\)
represents the pure transport of distinguishability under the refinement map.
If refinement closed globally, this transport would suffice.  Yet classical
convective transport fails to be integrable; small loops do not return the
same state.  The discrepancy accumulates as informational strain.

The viscous term
\(
\nu\,\Delta u
\)
is precisely the correction required to force closure.  It is the smooth
shadow of the strain operator $\Sigma$: the minimal adjustment needed to
reconcile locally transported information with a globally coherent record.
Viscosity is therefore an informational phenomenon.  It is the continuous
representation of the curvature induced by non-closure of refinement.

In this interpretation, Navier--Stokes is not a physical law but the canonical
example of how strain appears when local informational updates fail to agree.
Its form is dictated entirely by the requirement that refinement remain
coherent across overlapping regions.  The equation emerges as the unique
smooth expression of balancing informational strain.
