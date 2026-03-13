import Measurement.Chapter2

namespace Measurement

class LOCAL
    (symbol: Type now)
    (event: Type (now+1))
    [DISTINGUISHABLE symbol event]
    (η : symbol)
    (LT : symbol -> symbol -> Bool)
    [COUNTABLE symbol event η LT]
    (LE : symbol -> symbol -> Bool)
    (transform : symbol -> Option (ULift.{now+1, now} symbol))
    where
  ζ? : symbol -> Option (ULift.{now+1, now} symbol) -> Bool
  step_size? : symbol -> Option (ULift.{now+1, now} symbol) -> Bool

  vector: symbol

namespace LOCAL
variable {symbol : Type now}
         {event : Type (now+1)}
         [ds: DISTINGUISHABLE symbol event]
         {η : symbol}
         {LT : symbol -> symbol -> Bool}
         [cs: COUNTABLE symbol event η LT]
         {domain : symbol -> symbol -> Bool}
         {transform : symbol -> Option (ULift.{now+1, now} symbol)}
def ζ
  (n : symbol) : Option (ULift.{now+1, now} symbol) :=
  cs.witness n
end LOCAL


inductive Accumulate
    (count : Type (now+1))
    (i : Type now)
    (j : Type (now+1))
    [DISTINGUISHABLE i j]
    (η : i)
    (LT : i -> i -> Bool)
    [COUNTABLE i j η LT]
    : Type (now+2)
  | nil : Accumulate count i j η LT
  | cons : i → j -> Count i j →  (j×i) → count →
          Accumulate count i j η LT → Accumulate count i j η LT

structure BinaryOperator
    (symbol : Type now)
    (event : Type (now+1))
    [A : DISTINGUISHABLE symbol event]
    [B : DISTINGUISHABLE symbol event]
    (η : symbol)
    (LT : symbol -> symbol -> Bool)
    [A_count : COUNTABLE symbol event η LT]
    where
  -- Input Bits (The 3)
  top    : symbol
  bottom : symbol
  left   : symbol
  -- The "Etching" Logic (No-label pass-through)
  right? : symbol → symbol → symbol → Bool

namespace BinaryOperator
variable {symbol : Type now}
         {event : Type (now+1)}
         [A : DISTINGUISHABLE symbol event]
         [B : DISTINGUISHABLE symbol event]
         {η : symbol}
         {LT : symbol -> symbol -> Bool}
         [A_count : COUNTABLE symbol event η LT]

end BinaryOperator

structure Iteration
    (symbol: Type now)
    (event: Type (now+1))
    [DISTINGUISHABLE symbol event]
    (η1 : symbol)
    (LT1 : symbol -> symbol -> Bool)
    [count: COUNTABLE symbol event η1 LT]
    (η2 : symbol)
    (LT2 : symbol -> symbol -> Bool)
    [strain: INVARIANT symbol event η2 LT2]
    (LE : symbol -> symbol -> Bool)
    (transform : symbol -> Option (ULift.{now+1, now} symbol))
    [LOCAL symbol event η LT LE transform]
    (φ : symbol)
    (dφ : symbol → symbol → Bool)
      where
  value : symbol
  le? : symbol -> symbol -> Bool
  lt? : symbol -> symbol -> Bool
  step? : symbol -> symbol -> Bool
  round? : symbol -> Option (ULift.{now+1, now} symbol) -> Bool
  transform? : symbol -> symbol -> Option (ULift.{now+1, now} symbol)

namespace Iteration
variable {symbol : Type now}
         {event : Type (now+1)}
         [DISTINGUISHABLE symbol event]
         {η : symbol}
         {LT : symbol -> symbol -> Bool}
         [COUNTABLE symbol event η LT]
         {LE : symbol -> symbol -> Bool}
         {transform : symbol -> Option (ULift.{now+1, now} symbol)}
         [LOCAL symbol event η LT LE transform]
         {φ : symbol}
         {dφ : symbol → symbol → Bool}

def le (a b : symbol) : Bool :=
  LE a b

def lt (a b : symbol) : Bool :=
  LT a b

def step (a b : symbol) : Bool :=
  dφ a b

def round
  [inv : Invariant symbol event η LT]
  (a : symbol)
  (n : Option (ULift.{now+1, now} symbol)) : Bool :=
  match n with
  | none => false
  | some n' => LT a n'.down

end Iteration

structure Inverse
    (symbol : Type now)
    (event : Type (now+1))
    [DISTINGUISHABLE symbol event]
    (number : symbol)
    (value : symbol -> symbol -> Bool)
    [count: COUNTABLE symbol event number value]
    (inverse_of: symbol)
    (inverse? : symbol -> symbol -> Bool)
    where
  forward: Decomposition symbol event number value
  preimage? : symbol -> symbol -> Bool

structure PartialOrdering
    (symbol : Type now)
    (event : Type (now+1))
    [DISTINGUISHABLE symbol event]
    (number : symbol)
    (value : symbol -> symbol -> Bool)
    [count: COUNTABLE symbol event number value]
    where
  le? : symbol -> symbol -> Bool
  causal? : symbol -> symbol -> Bool
  correlant? : symbol -> symbol -> Bool
  admissible? : symbol -> symbol -> symbol -> Bool

namespace PartialOrdering

variable {symbol : Type now}
         {event : Type (now+1)}
         [DISTINGUISHABLE symbol event]

/--
Standard less-than-or-equal check.
Directly uses the raw boolean map from the index.
-/
def le (p : PartialOrdering symbol event) (a b : symbol) : Bool :=
  p.le? a b

/--
The etching path of the carrier.
Determines if bit 'a' is a causal prerequisite for bit 'b'[cite: 49].
-/
def causal (p : PartialOrdering symbol event) (a b : symbol) : Bool :=
  p.causal? a b

/--
Multiset pressure correlation.
Identifies bits that share a neighborhood in the giant bitset[cite: 49].
-/
def correlant (p : PartialOrdering symbol event) (a b : symbol) : Bool :=
  p.correlant? a b

/--
The 3-to-1 bit reduction resolver.
Validates if bits 'a' and 'b' are admissible relative to a third symbol[cite: 49].
-/
def admissible (p : PartialOrdering symbol event) (a b threshold : symbol) : Bool :=
  p.admissible? a b threshold

end PartialOrdering
end Measurement
