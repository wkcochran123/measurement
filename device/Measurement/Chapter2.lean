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


/--
A description of a mechanism, given σ the mechanism returns τ.
-/
structure Decomposition (σ : Type u) (τ : Type v) where
  pairs : Enumeration (σ × τ)

/--
These are the symbols that are read out.  They will be
paired with the symbols that are in the ledger to
form a decomposition.
-/
structure Alphabet (σ : Type v) where
  symbols : Enumeration σ

/--
An instrument is the metaphysical device that pairs an
alphabet with a listing of that alphabet.
-/
structure Instrument (S : Type u) (σ : Type v) where
  -- The State
  alphabet : Alphabet σ
  ledger   : Ledger S

/-
A device is merely the decomposition of the instrument
that takes _time_ to read.  The single internal symbol
is updated.
-/
structure Device (σ : Type u) (τ:Type (u+1)) where
  instrument : Instrument σ τ
  decomposition : Decomposition σ τ
  silence: ArrowOfTime σ τ



/--
Constructions:

o EinsteinDevice:  This is a clock, it counts upward once for every event,
                   much like a pendulum clock that advances a mechansim.

o TuringDevice:    A theoretical device that computes representations, a
                   trivial abbreviation, but
-/
abbrev EinsteinDevice := Device Nat (ULift Nat)
abbrev TuringDevice (σ : Type u) (τ : Type (u+1)) := Device σ τ







namespace Enumeration

  def pair {A : Type u} {B : Type v} :
      Enumeration A → Enumeration B → Enumeration (A × B)
    | .nil,      _         => .nil
    | _,         .nil      => .nil
    | .cons a as, .cons b bs => .cons (a, b) (pair as bs)

end Enumeration

namespace Decomposition
  /-
  A decomposition provides a new ζ for the combination symbols
  -/
  def ζ {σ τ} (D : Decomposition σ τ) (n : Nat) : Option (σ × τ) :=
    Enumeration.ζ D.pairs n

  /-
  You can make a decomposition very easily from two enumerations by running
  their iterators simulaneously.
  -/
  def zip {σ τ} (eσ : Enumeration σ) (eτ : Enumeration τ) :
    Decomposition σ τ :=
  { pairs := Enumeration.pair eσ eτ }

end Decomposition



namespace Device
/-
The device must spend time quietly waiting for the reading.
-/
def read? {σ : Type u} {τ : Type (u+1)} (D: Device σ τ): Option τ := D.silence.elapse

end Device


end Measurement
