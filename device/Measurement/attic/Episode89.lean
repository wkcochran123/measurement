import Measurement.Episode88

namespace Measurement

/-
__EPISODE 89__: _The Positron Count -- `(Electron XOR number) AND Electron`_

The structure receipt of a reading is its bit-vector over the rungs.  The ELECTRON is the resolved
ramp `1^p 0^…` (p = the precision it was measured to).  A POSITRON is a rung that came back TANGE
where the electron resolved a FUNGE:

  positronCount = popcount ( (Electron XOR number) AND Electron )

The `AND Electron` is load-bearing -- it confines the count to the resolved region, so a flip out in
the noise (Electron = 0) is not a positron.  MATTER is the complement -- the funges that held.  Inside
the resolved region every rung is one or the other, so matter + positron = popcount Electron.
-/

/-- bitwise XOR of two bit-vectors. -/
def bvXor : List Bool → List Bool → List Bool := List.zipWith Bool.xor

/-- bitwise AND of two bit-vectors. -/
def bvAnd : List Bool → List Bool → List Bool := List.zipWith (· && ·)

/-- the count of set bits (the funges). -/
def popcount (bs : List Bool) : Nat := (bs.filter id).length

/-- THE POSITRON COUNT: the funges that flipped to tange inside the electron's resolved region. -/
def positronCount (electron number : List Bool) : Nat :=
  popcount (bvAnd (bvXor electron number) electron)

/-- THE MATTER READING: the funges that held against the electron. -/
def matterReading (electron number : List Bool) : Nat :=
  popcount (bvAnd number electron)

-- sanity, decided: the electron read against itself carries no positron; one flip is one positron;
-- a funge out past the precision (electron = 0 there) is NOT counted; and matter + positron = p.
example : positronCount [true, true, true] [true, true, true] = 0 := by decide
example : positronCount [true, true, true] [true, false, true] = 1 := by decide
example : positronCount [true, true, true] [true, true, true, true] = 0 := by decide  -- noise past p
example : matterReading [true, true, true] [true, false, true]
            + positronCount [true, true, true] [true, false, true] = 3 := by decide

end Measurement
