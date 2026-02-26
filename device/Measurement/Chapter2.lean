/-
Measurement/Chapter2.lean

Chapter 2 develops the concept of the _pair_.  Given
a set _S_, a pair is a relation on _S_.  With a pair,
you can implement a divide and conquer strategy where
half of the work is in one part and the other half
is in the other.
-/

import Measurement.Chapter1

namespace Measurement

/-
Invariant:     Divide and conquer strategy
Instrument:    List of symbols that represent divisions
Device:        The measurement instrument
Closure:       A description of the mechanism of a physical
-/

structure Decomposition
    (σ : Type now) [Distinguishable σ]
    (τ : Type now) [Distinguishable τ]
    where
  data : Numbering (ArrowOfTime σ τ)


structure Alphabet
  (σ : Type now) [Distinguishable σ]
  (τ : Type now)
  where
  symbol: σ
  lookup: Noisy Decomposition σ τ

structure Instrument
    (σ : Type now) [Distinguishable σ]
    (τ : Type now)
    : Type (now+2) where
  sensorAlphabet : Alphabet σ τ

  sensor : Noisy Ledger σ
  gauge  : Noisy Ledger τ

/-
A device is merely the decomposition of the instrument
that takes _time_ to read.  The single internal symbol
is updated.
-/
structure Device (σ : Type u) (τ:Type v)
   [Distinguishable σ] [Distinguishable τ] where
  instrument : Instrument σ τ
  decomposition : PhysicalDecomposition σ τ

/--
Constructions:

o EinsteinDevice:  This is a clock, it counts upward once for every event,
                   much like a pendulum clock that advances a mechansim.

o TuringDevice:    A theoretical device that computes representations, a
                   trivial abbreviation, but
-/
abbrev EinsteinDevice := Device Nat Nat
/-
Suppose we would like to use math to both describe the world and how it evolves?
This is the message to the compiler that it can assume math will both describe the world
and how it evolves.
-/
abbrev TuringDevice (σ : Type u)
    [Distinguishable σ] := Device σ σ

structure Computer (σ : Type u)
    [Distinguishable σ] where
  cpu : TuringDevice σ
  memory: Ledger σ

namespace Decomposition
  variable {σ : Type u}[Distinguishable σ]
  variable {τ : Type v}[Distinguishable τ]

  instance [Distinguishable α] [Distinguishable β] : Distinguishable (α × β) where
  inst := inferInstance
  symbol := (Distinguishable.symbol, Distinguishable.symbol)

  def zip (eσ : Enumeration σ) (eτ : Enumeration τ) : Decomposition σ τ :=
      { left :=
          { symbol := eσ
          , numbering := eσ.naturals 0
          }
      , right :=
          { symbol := eτ
          , numbering := eτ.naturals 0
          }
      }

  def enumerate (d : Decomposition σ τ) : Enumeration (σ × τ) :=
      let rec walk : Enumeration σ → Enumeration τ → Enumeration (σ × τ)
        | .nil, _ => .nil
        | _, .nil => .nil
        | .cons s ss, .cons t ts => .cons (s, t) (walk ss ts)
      walk d.left.symbol d.right.symbol
end Decomposition


namespace Instrument

variable {σ : Type u}[Distinguishable σ]
variable {τ : Type v}[Distinguishable τ]

/--
Readout: The 'after' state of the current arrow of time.
This is the symbol currently displayed by the instrument.
-/
def reading?
  (I : Instrument σ τ) : Option (ULift τ) :=
  let sensor_reading := Friction.slip? I.sensor I.arrow
  match sensor_reading with
  | none => none
  | some reading => let reading_ndx := I.sensor.base.data.η reading.down
    match reading_ndx with
    | none => none
    | some ndx => let gauge_symbol := I.gauge.data.ζ ndx
      match gauge_symbol with
      | none => none
      | some sym => some (ULift.up sym)

end Instrument


namespace Device
/-
The device must spend time quietly waiting for the reading.
-/
variable {σ : Type u}[Distinguishable σ]
variable {τ : Type v}[Distinguishable τ]

def gauge? (D: Device σ τ) (x : σ) : Option (ULift τ) := D.instrument.read_out? x

end Device


namespace Computer

variable {σ : Type u}[Distinguishable σ]

def execute? (C: Computer σ) (x: σ): Option (ULift σ) :=
  C.cpu.read? x

end Computer


end Measurement
