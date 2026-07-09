# The Continuum Limit Effect

The device reads a finite stress-strain mesh.  The stress is the device
reading, the mixed second difference `pairDelta2`; the strain is the count from
the origin.  Because the Measurement device collapses terms into the three tag
classes, refinement inside the device is pinned at the coarsest mesh.

The experiment records the three available coarse samples:

- strain 0 reads stress -1
- strain 1 reads stress +1
- strain 2 reads stress 0

The continuum limit is therefore not claimed as an owned object of the device.
It is named as the limit of a refinable external mesh whose coarsest member is
the device reading.  The honest result is the gap between the finite reading and
any finer model, together with the methodological rule that threshold/kink
locations must be fitted from refinement rather than assumed by a linear law.

