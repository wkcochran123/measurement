import Std

import Measurement.Chapter1.Definitions
import Measurement.Chapter2.ZFC

namespace Measurement

universe u v

/-- A representation map (tilde-rho) is just a function. -/
def RhoTilde (R : Type u) (X : Type v) : Type (max u v) :=
  R -> X

/-- Construction 1: identity representation (when `X = R`). -/
def rhoTilde_id (R : Type u) : RhoTilde R R :=
  fun r => r

/-- Construction 2: constant representation (needs an inhabitant of `X`). -/
def rhoTilde_const (R : Type u) (X : Type v) [Inhabited X] : RhoTilde R X :=
  fun _ => default



end Measurement
