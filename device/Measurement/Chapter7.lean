import Measurement.Chapter6


namespace Measurement

structure Representation (A : Type u) where
  physical : Decomposition A A
  metaphysical : Enumeration A

structure RationalNumbers (σ : Type u) (τ : Type (u+1)) where
  numerator: Enumeration NaturalNumbers
  denominator: Enumeration NaturalNumbers
  invariants: Enumeration (Invariant σ τ)
  representations: Enumeration (Representation (Invariant σ τ))

structure Number (σ : Type u) (τ : Type (u+1)) where
  symbol: Representation (RationalNumbers σ τ)
  value: Invariant σ τ

structure Ring (σ : Type u) (τ : Type (u+1)) where
  left: Number σ τ
  right: Number σ τ


namespace RationalNumbers

def represent?
  {σ : Type u} {τ : Type (u+1)}
  (R : RationalNumbers σ τ)
  (I : Invariant σ τ) : Option (Representation (Invariant σ τ)) :=
    let ndx := R.invariants.η I
    R.values.ζ ndx

  def decode {σ : Type u} {τ : Type (u+1)} {E : Event σ τ} (L: Ledger σ)(R : RationalNumbers σ τ)
  [DecidableEq σ] [DecidableEq τ]: Number σ τ :=
    let event_decomposition := Decomposition.mk (Enumeration.cons (R, R) Enumeration.nil)
    let event_iteration := Enumeration.cons R Enumeration.nil
    let invariant := E.invariant L
    Number.mk
      (Representation.mk event_decomposition event_iteration)
      invariant

end RationalNumbers


namespace Numbers
def rational_instrument {σ : Type u} {τ : Type (u+1)} [DecidableEq σ] [DecidableEq τ]
    (R : RationalNumbers σ τ) (N : NaturalNumbers) : Instrument Nat (ULift Nat) :=
    -- Alphabet is the Nat reading from the ticks
    let alpha := Alphabet.mk (N.ticks.map (fun e => e.reading))

    -- The Map: Building the Ledger via Compiler Directive
    -- η: Lookup map (Symbol -> Location)
    -- ζ: Decoding map (Location -> Symbol) [cite: 4, 16]
    let list := R.values.map (fun n =>
      match (Counting.enumerate n).decoder.ζ (match R.values.η n with
        | none => sorry
        | some loc => loc) with
      | none => sorry
      | some sym => sym)


    -- Ledger: A list with symbols for random access [cite: 17, 18]
    let ledger := Ledger.mk list list.decoder
    Instrument.mk ledger alpha
end Numbers

end Measurement
