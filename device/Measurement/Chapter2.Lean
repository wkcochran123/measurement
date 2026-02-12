import Measurement.Chapter1


namespace Measurement

universe u v w

/--
Defintion 5: Decomposition

Processing lists has a long history in software development.
Concepts like list iteration seem slow and inefficient to most developers,
but they can actually be used to express the full power of computation.

We start with the paired iteration of a list.  Given two lists,
you can iterate through them together, pairing elements as you go.
-/
structure Decomposition (σ : Type u) (τ : Type v) where
  pairs : Enumeration (σ × τ)

namespace Enumeration

  def zip {A : Type u} {B : Type v} :
      Enumeration A → Enumeration B → Enumeration (A × B)
    | .nil,      _         => .nil
    | _,         .nil      => .nil
    | .cons a as, .cons b bs => .cons (a, b) (zip as bs)

end Enumeration

namespace Decomposition

  def ζ {σ τ} (D : Decomposition σ τ) (n : Nat) : Option (σ × τ) :=
    Enumeration.nth D.pairs n

  def ofZips {σ τ} (eσ : Enumeration σ) (eτ : Enumeration τ) :
    Decomposition σ τ :=
  { pairs := Enumeration.zip eσ eτ }

end Decomposition


/--
Definition 6: Alphabets

When Turing intuited his machine, he assumed that symbols
existed and are countable.  This is an unfortunate assumption
that we must fix in order to truly perform all of mathematics.

We start by defining Turing's alphabet as an enumeration of symbols.
-/
structure Alphabet (σ : Type v) where
  symbols : Enumeration σ

/--
Definitinon 7: Instruments

We begin by identifying computation as an instrument with which
we can perform measurements. An alphabet and a linked list.
-/
structure Instrument (S : Type u) (σ : Type v) where
  -- The State
  alphabet : Alphabet σ
  ledger   : Ledger S

/--
Definition 8: Devices

Devices are mechanisms that provide a mathematical description of the
relationship between the symbols chosen and the order they are placed
in the list.  Given a symbol, it can tell you a place in the list to
find it and given a place in the list, it can tell you what symbol is there.
-/
structure Device (σ : Type S) (τ:Type T) where
  instrument : Instrument σ τ
  decomposition : Decomposition τ σ

/--
Definition 9: The Clock

Our first algorithm just outputs the current cycle number each cycle.
-/
abbrev EinsteinDevice := Device Nat Nat

/--
Definition 10: -/
abbrev TuringDevice (S : Type u) (σ : Type v) : Type (max u v) :=
  Device S σ

end Measurement
