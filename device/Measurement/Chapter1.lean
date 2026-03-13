/-
Measurement/Chapter1.lean
Facts
-/

import Std
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Basic



namespace Measurement

universe i

/- universe i+1-/
abbrev NEXT (Symbol : Type i) := ULift.{i+1,i} Symbol

/- --------------------------------------------------------
-/
class DISTINGUISHABLE
    (Symbol : Type i)
    (Distinguishable : Symbol -> Symbol -> Bool)
    where

  fact           : Symbol
  possibilities  : NEXT Symbol

  different?          : Symbol → Symbol → Bool
  resolved?           : Symbol → NEXT Symbol → Bool


namespace DISTINGUISHABLE

variable  {Symbol : Type i}
          {Distinguishable : Symbol -> Symbol -> Bool}
          [d: DISTINGUISHABLE Symbol Distinguishable]

def different
    (s1: Symbol)
    (s2: Symbol)
      : Bool :=
  different? Distinguishable s1 s2

def distinguish
    (now: Symbol)
    (later: NEXT Symbol)
      : Bool :=
  resolved? Distinguishable now later

end DISTINGUISHABLE





/- --------------------------------------------------------
-/
class ADMISSIBLE
    (Symbol : Type i)
    (Distinguishable : Symbol -> Symbol -> Bool)
    (Admissibile : Symbol -> NEXT Symbol -> Bool)
    [d: DISTINGUISHABLE Symbol Distinguishable]     -- Virtual inheritance dispatch for partial orderings
    where

  symbol : Symbol

  different?    : Symbol → Symbol → Bool
  occured?      : Symbol → NEXT Symbol → Bool


namespace ADMISSIBLE
variable  {Symbol : Type i}
          {Distinguishable : Symbol → Symbol → Bool}
          {Admissible : Symbol → NEXT Symbol → Bool}
          [d: DISTINGUISHABLE Symbol Distinguishable]
          [s: ADMISSIBLE Symbol Distinguishable Admissible]

def different
    (pack: Symbol)
    (individual: Symbol)
      : Bool :=
  d.different? pack individual

def occurred
    (now: Symbol)
    (later: NEXT Symbol)
    : Bool :=
  occured? Distinguishable Admissible now later

end ADMISSIBLE






/- --------------------------------------------------------
-/

class CAUSAL
    (Symbol: Type i)
    (Distinguishable: Symbol → Symbol → Bool)
    (Admissible : Symbol → NEXT Symbol → Bool)
    (Phenomenon : NEXT Symbol → NEXT (NEXT Symbol) → Bool)
    [d: DISTINGUISHABLE Symbol Distinguishable]
    [a: ADMISSIBLE Symbol Distinguishable Admissible]
    where

  stimulus: Symbol
  response: NEXT Symbol

  less_than?    : Symbol → Symbol → Bool
  precedes?     : Symbol → NEXT Symbol → Bool
  continues?    : NEXT Symbol → NEXT (NEXT Symbol) → Bool

namespace CAUSAL
variable  {Symbol: Type i}
          {Distinguishable: Symbol → Symbol → Bool}
          {Admissible : Symbol → NEXT Symbol → Bool}
          {Phenomenon : NEXT Symbol → NEXT (NEXT Symbol) → Bool}
          (d: DISTINGUISHABLE Symbol Distinguishable)
          (a: ADMISSIBLE Symbol Distinguishable Admissible)
          (c: CAUSAL Symbol Distinguishable Admissible Phenomenon)

def less_than
    (left : Symbol)
    (right : Symbol)
      : Bool :=
  d.different? left right

def precedes
    (before: Symbol)
    (after: NEXT Symbol)
      : Bool :=
  a.occured? before after

def continues
    (next: NEXT Symbol)
    (following: NEXT (NEXT Symbol))
    : Bool :=
  continues? Distinguishable Admissible Phenomenon next following

end CAUSAL








/- --------------------------------------------------------
-/

class ITERABLE
    (Symbol: Type i)
    (Distinguishable: Symbol → Symbol → Bool)
    (Admissible : Symbol → NEXT Symbol → Bool)
    (Phenomenon : NEXT Symbol → NEXT (NEXT Symbol) → Bool)
    (Converged : (Symbol -> NEXT Symbol) -> (NEXT Symbol -> NEXT (NEXT Symbol)) -> Bool )
    [d: DISTINGUISHABLE Symbol Distinguishable]
    [a: ADMISSIBLE Symbol Distinguishable Admissible]
    [c: CAUSAL Symbol Distinguishable Admissible Phenomenon]
    where

  running_total : Symbol

  different?    : Symbol → Symbol → Bool
  less_than?    : Symbol → NEXT Symbol → Bool
  continues?    : NEXT Symbol → NEXT (NEXT Symbol) → Bool
  converged?    : (Symbol → NEXT Symbol) → (NEXT Symbol → NEXT (NEXT Symbol)) → Bool


namespace ITERABLE
variable  {Symbol: Type i}
          {Distinguishable: Symbol → Symbol → Bool}
          {Admissible : Symbol → NEXT Symbol → Bool}
          {Phenomenon : NEXT Symbol → NEXT (NEXT Symbol) → Bool}
          {Converged : (Symbol -> NEXT Symbol) -> (NEXT Symbol -> NEXT (NEXT Symbol)) -> Bool }
          (d: DISTINGUISHABLE Symbol Distinguishable)
          (a: ADMISSIBLE Symbol Distinguishable Admissible)
          (c: CAUSAL Symbol Distinguishable Admissible Phenomenon)
          (i: ITERABLE Symbol Distinguishable Admissible Phenomenon Converged)



end ITERABLE





/- --------------------------------------------------------
-/

structure Universe
    (Symbol: Type i)
    (Distinguishable: Symbol -> Symbol -> Bool)
    (Admissible : Symbol -> NEXT Symbol -> Bool)
    (Phenomenon : NEXT Symbol -> NEXT (NEXT Symbol) -> Bool)
    (Converged : (Symbol -> NEXT Symbol) -> (NEXT Symbol -> NEXT (NEXT Symbol)) -> Bool)
    [DISTINGUISHABLE Symbol Distinguishable]
    [ADMISSIBLE Symbol Distinguishable Admissible]
    [CAUSAL Symbol Distinguishable Admissible Phenomenon]
    [ITERABLE Symbol Distinguishable Admissible Phenomenon Converged]
    where

  tensor : Symbol







/- --------------------------------------------------------
-/

class ENCODED
    (Symbol: Type i)
    (Encoding: Symbol -> Symbol -> Bool)
    (Encoded: Symbol -> NEXT Symbol -> Bool)
    [symbol: DISTINGUISHABLE Symbol Encoding]
    where

  glyph: Symbol

  encoding?: Symbol -> Symbol -> Bool
  encoded?: Symbol -> NEXT Symbol -> Bool

namespace ENCODED
variable  {Symbol: Type i}
          {Encoding: Symbol -> Symbol -> Bool}
          {Encoded: Symbol -> NEXT Symbol -> Bool}
          [d: DISTINGUISHABLE Symbol Encoding]
          [e: ENCODED Symbol Encoding Encoded]


def encoding
    (concept: Symbol)
    (symbol: Symbol)
      : Bool :=
  encoding? Encoding Encoded concept symbol

def encoded
    (concept: Symbol)
    (symbol: NEXT Symbol)
      : Bool :=
  encoded? Encoding Encoded concept symbol


end ENCODED







/- --------------------------------------------------------
-/

class COMPUTABLE
    (Symbol: Type i)
    (Encoding: Symbol -> Symbol -> Bool)
    (Execution: Symbol -> (NEXT Symbol) -> Bool)
    [DISTINGUISHABLE Symbol Encoding]
    [ENCODED Symbol Encoding Execution]
    where

  state : Symbol

  encoding?   : Symbol -> Symbol -> Bool
  executable? :  Symbol → NEXT Symbol -> Bool


namespace COMPUTABLE
variable  {Symbol: Type i}
          {Encoding: Symbol -> Symbol -> Bool}
          {Execution: Symbol -> (NEXT Symbol) -> Bool}
          [DISTINGUISHABLE Symbol Encoding]
          [ENCODED Symbol Encoding Execution]
          [COMPUTABLE Symbol Encoding Execution]


def addressable
    (label : Symbol)
    (address : Symbol)
      : Bool :=
  encoding? Encoding Execution label address

def executable
    (instruction : Symbol)
    (result : NEXT Symbol)
      : Bool :=
  executable? Encoding Execution instruction result

end COMPUTABLE


/--
Counting symbols thru metavariables!
-/
inductive Enumerate
    (Symbol : Type i)
    (Distinguishable : Symbol -> Symbol -> Bool)
    (CountingProcess : Symbol -> (NEXT Symbol) -> Bool)
    [DISTINGUISHABLE Symbol Distinguishable ]
    [ADMISSIBLE Symbol Distinguishable CountingProcess]
  | nil : Enumerate Symbol Distinguishable CountingProcess
  | cons : Symbol →
           DISTINGUISHABLE Symbol Distinguishable →
           ADMISSIBLE Symbol Distinguishable CountingProcess →
           Enumerate Symbol Distinguishable CountingProcess




inductive Index
    (Symbol: Type i)
    (Encoding: Symbol -> Symbol -> Bool)
    (Encoded: Symbol -> NEXT Symbol -> Bool)
    [DISTINGUISHABLE Symbol Encoding]
    [ENCODED Symbol Encoding Encoded]
    : Type (i+1)
  | nil  :  Index Symbol Encoding Encoded
  | cons :  Symbol →
            DISTINGUISHABLE Symbol Encoding →
            ENCODED Symbol Encoding Encoded →
            Index Symbol Encoding Encoded


inductive Ledger
    (Symbol: Type i)
    (Encoding: Symbol -> Symbol -> Bool )
    (Encoded: Symbol -> NEXT Symbol -> Bool)
    (Value : Symbol -> Symbol -> Bool)
    (Phenomenon: Symbol -> NEXT Symbol -> Bool)
    [DISTINGUISHABLE Symbol Encoding]
    [ENCODED Symbol Encoding Encoded]
    [DISTINGUISHABLE Symbol Value]
    [ENCODED Symbol Value Phenomenon]
    [ADMISSIBLE Symbol Value Phenomenon]
    [COMPUTABLE Symbol Encoding Encoded]
    [COMPUTABLE Symbol Value Phenomenon]

    : Type (i+1)
  | nil :  Ledger Symbol Encoding Encoded Value Phenomenon
  | cons: Symbol →
          DISTINGUISHABLE Symbol Encoding →
          ENCODED Symbol Encoding Encoded →
          DISTINGUISHABLE Symbol Value →
          ENCODED Symbol Value Phenomenon →
          ADMISSIBLE Symbol Value Phenomenon →
          COMPUTABLE Symbol Encoding Encoded →
          COMPUTABLE Symbol Value Phenomenon →
          Ledger Symbol Encoding Encoded Value Phenomenon →
          Ledger Symbol Encoding Encoded Value Phenomenon


end Measurement
