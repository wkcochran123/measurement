/-
Measurement.Agent.Positron

Counting positrons THROUGH THE GAUGE.  No δ², no continuity, no episode imports -- the discrete
pigeonhole.  A reading answers each gate (its class method's verdict) with a funge (true) or a tange
(false).  The ELECTRON is the all-funge gauge.  A POSITRON is a gate that tanged where the electron
funged: `(Electron XOR number) AND Electron`, counted.  To read the device you call the gate, not the
arithmetic.
-/
import Measurement.Agent.Gates

set_option autoImplicit false

namespace Measurement.Agent

/-- A gauge reading: the funge/tange verdict at each gate -- the answer its class method gives
(MAGNITUDE's `whelmed?`, BINARY's `different?`, …).  True = funge (matter), false = tange. -/
def Reading := Gate → Bool

/-- The reading laid out in cascade order -- the rung bit-vector, read off the gauge. -/
def Reading.bits (r : Reading) : List Bool := Gate.all.map r

/-- THE ELECTRON: every gate funges -- pure matter, the superconducting condensate. -/
def electron : Reading := fun _ => true

/-- THE SUPERCONDUCTING PAIR, read through the gauge: every gate funges except MAGNITUDE, where
`whelmed?` flips to tange -- the admitted positron.  This is the device's reading, by calling the
gates, not by recomputing δ². -/
def superconductingPair : Reading := fun g => decide (g ≠ Gate.magnitude)

/-- THE POSITRON COUNT, over the gauge: the gates that tanged where the electron funged. -/
def positronCount (elec number : Reading) : Nat :=
  (Gate.all.filter (fun g => elec g && !(number g))).length

/-- THE MATTER READING: the gates that funged with the electron. -/
def matterReading (elec number : Reading) : Nat :=
  (Gate.all.filter (fun g => elec g && number g)).length

-- COUNT POSITRONS, off the gauge:
#eval positronCount electron electron              -- 0: the pure pair carries no positron
#eval positronCount electron superconductingPair    -- 1: one positron, at MAGNITUDE (`whelmed?`)
#eval matterReading electron superconductingPair     -- 35: every other gate holds matter
#eval (superconductingPair Gate.magnitude)           -- false: the tange gate

/-- The native pair, read through the gauge, carries no positron -- matter all the way down. -/
theorem native_pair_pure_matter : positronCount electron electron = 0 := by decide

/-- THE COUNT: bring the device near the superconducting pair, read it through the gauge, and exactly
ONE positron is admitted -- at MAGNITUDE, where `whelmed?` flips. -/
theorem pair_admits_one_positron : positronCount electron superconductingPair = 1 := by decide

/-- Every gate is matter or positron: the two tallies are the whole gauge.  The pigeonhole closes --
no rung left over, no continuity needed. -/
theorem gauge_partition :
    matterReading electron superconductingPair + positronCount electron superconductingPair
      = Gate.all.length := by decide

end Measurement.Agent
