/-
Calibrate: the meanings, judged by Mathlib.

Not the device.  This package imports Meanings, Mathlib, and the device to read it.  Nothing in Measurement imports it,
and the device's own package does not require Mathlib, so no build of the device clones, resolves or sees it.

  `Readings`  each Meanings correspondence handed to Mathlib as `≃+*`.
  `Device`    the Area, the Account and the ratios of Accounts as `≃+*` to ℕ, ℤ and the rationals, each read on
              Episode 8's EKG by `ekg_meets`, which fails when an interface is not met.
  `Norm`      the coins weighed by eighteen and five carried to the plane; the device's table carried across is the
              operator with eighteen on the diagonal and the root of ninety off it; its operator norm is eighteen and
              the root of ninety; on the coins that bounds the weighed square for every pair; and its square lies
              between Episode 13's walls, 755 and 756.
  `Hilbert`   the plane met as a module, an inner-product space and a complete space, and the norm, on the EKG.
  `Derivative` the slope as the derivative, from the exact bracket; the exponential its own derivative; e as the limit
              of the growing steps; and the device's turning walk going to the exponential of the quarter turn.

The reals and the completion are Mathlib's.  They are handed in here, and nowhere in the device.
-/
import Calibrate.Readings
import Calibrate.Device
import Calibrate.Norm
import Calibrate.Hilbert
import Calibrate.Derivative
