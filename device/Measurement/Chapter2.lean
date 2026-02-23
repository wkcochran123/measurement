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
  ordering : Numbering (σ × τ)

abbrev PhysicalDecomposition (σ :Type u)(τ: Type v) := Friction (Decomposition σ) τ

/--
These are the symbols that are read out.  They will be
paired with the symbols that are in the ledger to
form a decomposition.
-/
structure Alphabet (σ : Type u) where
  symbols : Enumeration σ

/--
An instrument is the metaphysical device that pairs an
alphabet with a listing of that alphabet.
-/
structure Instrument (σ : Type u) (τ : Type (v+1)) where
  -- The State
  ledger   : Ledger σ
  alphabet : Alphabet τ

/-
A device is merely the decomposition of the instrument
that takes _time_ to read.  The single internal symbol
is updated.
-/
structure Device (σ : Type u) (τ:Type (v+1)) where
  instrument : Instrument σ τ
  decomposition : PhysicalDecomposition σ τ


/--
Constructions:

o EinsteinDevice:  This is a clock, it counts upward once for every event,
                   much like a pendulum clock that advances a mechansim.

o TuringDevice:    A theoretical device that computes representations, a
                   trivial abbreviation, but
-/
abbrev EinsteinDevice := Device Nat (ULift Nat)
/-
Suppose we would like to use math to both describe the world and how it evolves?
This is the message to the compiler that it can assume math will both describe the world
and how it evolves.
-/
abbrev TuringDevice (σ : Type u) (τ : Type (u+1)):= Device σ τ

structure Computer (σ : Type u) (τ : Type (u+1)) where
  cpu : TuringDevice σ τ
  memory: Ledger σ

namespace Enumeration

  def pair {A : Type u} {B : Type v} :
      Enumeration A → Enumeration B → Enumeration (A × B)
    | .nil,      _         => .nil
    | _,         .nil      => .nil
    | .cons a as, .cons b bs => .cons (a, b) (pair as bs)

  def flip {X : Type u} : Enumeration (Nat × X) → Enumeration (X × Nat)
    | .nil => .nil
    | .cons (n, x) xs => .cons (x, n) (flip xs)

  def numbering {X : Type u} (e : Enumeration X) : Numbering X :=
    let ps := e.relation 0
    { pairs := ps
    , swaps := flip ps
    }

end Enumeration

namespace Decomposition
  /-
  You can make a decomposition very easily from two enumerations by running
  their iterators simulaneously.
  -/
  def zip {σ : Type u} {τ : Type (u+1)}
    (eσ : Enumeration σ) (eτ : Enumeration τ) : Decomposition σ τ :=
  by
    let ps : Enumeration (σ × τ) := Enumeration.pair eσ eτ
    exact
    { pairs := ps
    , ordering := Enumeration.numbering ps
    }

  def enumerate {σ : Type u} {τ : Type (u+1)} (d : Decomposition σ τ) : Enumeration (σ × τ) :=
    d.pairs
end Decomposition


namespace Instrument

def arrow {σ : Type u} {τ : Type (u+1)} (I : Instrument σ τ) [DecidableEq σ] [DecidableEq τ]: ArrowOfTime σ τ :=
    -- Step 1: Extract the sequences
    let alpha_seq := I.alphabet.symbols
    let ledger_seq := I.ledger.linked_list
    let zip_seq := Decomposition.zip ledger_seq alpha_seq

    match zip_seq.pairs.numbering.ζ 0 with
    | none => sorry
    | some pair => ArrowOfTime.mk pair.1 pair.2

end Instrument

namespace Device
/-
The device must spend time quietly waiting for the reading.
-/

def silence {σ : Type u} {τ : Type (u+1)} (D: Device σ τ) [DecidableEq σ] [DecidableEq τ]: ArrowOfTime σ τ := D.instrument.arrow

def read? {σ : Type u} {τ : Type (u+1)} (D: Device σ τ) [DecidableEq σ] [DecidableEq τ]: Option τ := D.silence.elapse

end Device


namespace Computer

def execute? {σ : Type u} {τ : Type (u+1)} (C: Computer σ τ) [DecidableEq σ] [DecidableEq τ]: Option τ :=
  C.cpu.silence.elapse

end Computer


end Measurement
