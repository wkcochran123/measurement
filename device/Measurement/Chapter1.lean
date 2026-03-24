/-
Measurement
Chapter 1: Physical
-/

-- There are NO IMPORTS. We assume the concept of a PROCESS
-- provided by an abstract universe called "COMPILER".
-- We will build a device to measure a process and see what
-- can be learned from it.

-- I also assume that you exist and are reading this right now.
-- Not to be too pedantic, but this is going to get tooo pedantic.

-- I further assume not only that I exist, but that I wrote this
-- with the intention that you would read it.

-- I do not assume that the compiler exists. I have demonstrated
-- to myself it probably does by compiling this program several times.

-- Draw your own conclusions.

namespace Measurement

-- So, we start with the universe.  Only Types exist in the
-- universe of the compiler. However, we step through time
-- by step 1, step 2, etc.. step i, ...
-- Whenever you see an index on a variable, this is that
-- index. No index, then it is the current value in the universe,
-- I mean compiler. A Type.
universe i

-- This is repeatable observation.  We wait for what is next.
abbrev OBSERVE {x} := Option (ULift.{i+1,i} x)
-- If you have seen it, then you can look directly at the symbol of the result.

-- To count, one needs a token. We hope to collect a lot
-- of TOKEN Symbols
abbrev TOKEN (Invariant : Type i) := Option Invariant

-- If we have already seen it, then you don't need to
-- de-option it.
abbrev OBSERVED {x} := ULift.{i+1,i} x
-- A different symbol is probably some other symbol, we will
-- prove that in a bit.

-- We can talk about something being on and off. We call that token
abbrev BOOL (Invariant :Type) := TOKEN Invariant

-- We can talk about truth using the truth the compiler gives us.
abbrev TRUTH  : BOOL Bool := some true

-- BOOL.  See how we are making the process of making TOKENS?
-- Would you like to see the only primitive TOKEN?

-- Verified silence. This is the only thing we can know for sure,
-- nothing has been verified and so we can TOKENIZE that concept as
def __SILENCE__ {Invariant: Type} : (TOKEN Invariant) := none
-- We define FALSE to be the symbol that represents unrepresentable symbols.
-- This is a DISTINCT Invariant, although it will never be observed as such.
-- I made it REALLY distinct so you do NOT miss it.
--
-- There is only one ball, keep your eye on it.
-- Like and Subscribe if you think I should make the ball bigger or smaller.


abbrev REFINE (Symbol: Type i) := Option (ULift Symbol)
abbrev REFINED (Symbol: Type i) := ULift Symbol


/- --------------------------------------------------------
DISTINGUISHABLE.

Something is DISTINGUISHABLE from others if there exists
some characteristic that is either present or absent from
the something relative to the others.
-/
class DISTINGUISHABLE
    (Characterisitic : Type → TOKEN (Type))
    (Invariant: Type)
    [DecidableEq Invariant]
    where

  -- The universe only exists as a type.
  -- Any higher type is metaphysical and belongs to
  -- the compiling engine, not the proof.
  -- Or does it?
  -- Meet our single invariant:
  æther               : Type

  different? : Invariant → Invariant → Prop :=
    fun s1 s2 => s1 ≠ s2
  distinct? : Invariant → Prop :=
    fun s => ∃ c : Invariant, different? s c
  dec_distinct : DecidablePred distinct?

namespace DISTINGUISHABLE
variable {Characterisitic : Type → TOKEN (Type)}
         {Invariant: Type}
         [DecidableEq Invariant]
         [d: DISTINGUISHABLE Characterisitic Invariant]

def different
    (s1 s2 : Invariant) : Prop :=
  d.different? s1 s2

def distinct
    (s : Invariant) : Prop :=
  d.distinct? s

def encode
    (symbol: Invariant)
    (compiler_type : Type)
      : TOKEN (Type) :=
  if (d.dec_distinct symbol).decide then some compiler_type else none

end DISTINGUISHABLE






/- --------------------------------------------------------
-/

-- At one time, people were over run with floods and people were like
-- I've had it with these random floods coming randomly and randomly
-- destroying everything. So they said:

-- Let's sciene the hell out of this.

-- And so, they could start to figure out that one thing leads to another.
-- We started understanding that certain situations were impossible
-- given current conditions.  Everything else could happen, theoretically.
-- We can further distinguish our universe by whether or not something
-- _could_ happen. So, an admissible stuff state in the future is one
-- that _could_ represent this.  That's 2 _coulds_.  Those are different
-- _coulds_.  Or, are they? Do they have to be?  Why not both?

-- An LA(1) compiler can only do 1 thing, refine a token into
-- compiled code.
abbrev EVENT (_: Type 1) := REFINE (TOKEN Type)

class ADMISSIBLE
    (Invariant: Type)
    (Value: Type 1)

     -- Notice the metaphor is starting to work on abstract types.
     -- It is _metaphysical_.
    (Metaphor: TOKEN Invariant → EVENT Value → BOOL Bool)
    where

  admissible? : TOKEN Invariant → EVENT Value → BOOL Bool := Metaphor

  event: EVENT Value

namespace ADMISSIBLE
variable {Invariant: Type}
         {Value: Type 1}
         {Metaphor: TOKEN Invariant → EVENT Value → BOOL Bool}
         [a : ADMISSIBLE Invariant Value Metaphor]

def admissible
    (s : TOKEN Invariant)
    (e : EVENT Value)
      : BOOL Bool :=
  a.admissible? s e

end ADMISSIBLE


class COUNTABLE
    -- Physical Traits of counting (these are real to the compiler)
    (Characteristic   : Type → TOKEN Type)
    (Invariant        : Type)
    (Symbol           : Type)       -- This here is what a compiler calls a "symbol".

    -- Metaphysical traits of a number: (One, 1) and its representation
    -- on the page (these are ℝeal to you and I)
    (Value            : Type 1)
    (Token            : Type 1)

    -- A description of the counting process.
    (Number           : TOKEN Invariant)
    (Metaphor         : TOKEN Invariant → EVENT Value  → BOOL Bool)

    -- Things that must be true in order for counting to be possible.
    [invariant_equality : DecidableEq (Invariant)]
    [symbol_equality    : DecidableEq (Symbol)]
    [value_equality     : DecidableEq (Value)]
    [token_equality     : DecidableEq (Token)]

    [DISTINGUISHABLE Characteristic Invariant]
    [a: ADMISSIBLE Invariant Value Metaphor]
    [ADMISSIBLE Symbol Token fun _ t => a.admissible? Number t]
      where

  symbol: Token
  value:  Value

  -- The notion of the origin does not change.  This is the root of
  -- a _frame of reference_.  This is the thing that has 0 velocity and
  -- 0 value.  We count this guy.  Just like Peano.
  -- Have no idea _WHAT_ has no value or velocity yet, but I'm sure it
  -- is important.
  origin: TOKEN Invariant

  -- This is 0, often mistaken for the origin.  0 is a symbol, not a number.
  -- We know what this is, right?  This is our word for what the compiler
  -- calls 0. We will pick 0000.... as the written symbol of this word...
  -- eventually... one bit at a time.
  -- That seems like a really convenient 0 for 0.
  zero:   REFINED (TOKEN Symbol)

namespace COUNTABLE

end COUNTABLE


inductive Iteration
    -- Physical Traits of counting (these are real to the compiler)
    (Characteristic   : Type → TOKEN Type)
    (Invariant        : Type)
    (Symbol           : Type)       -- This here is what a compiler calls a "symbol".

    -- Metaphysical traits of a number: (One, 1) and its representation
    -- on the page (these are ℝeal to you and I)
    (Value            : Type 1)
    (Token            : Type 1)

    -- A description of the counting process.
    (Number           : TOKEN Invariant)
    (Metaphor         : TOKEN Invariant → EVENT Value  → BOOL Bool)

    -- Things that must be true in order for counting to be possible.
    [invariant_equality : DecidableEq (Invariant)]
    [symbol_equality    : DecidableEq (Symbol)]
    [value_equality     : DecidableEq (Value)]
    [token_equality     : DecidableEq (Token)]

    [DISTINGUISHABLE Characteristic Invariant]
    [ADMISSIBLE Invariant Value Metaphor]
    [ADMISSIBLE Symbol Token fun _ t => ADMISSIBLE.admissible? Metaphor Number t]
      where

  | nil :
      REFINED (TOKEN Symbol) →
      Iteration Characteristic Invariant Symbol Value Token Number Metaphor
  | cons :
      REFINED (Invariant) →
      REFINED (TOKEN Symbol) →
      Iteration Characteristic Invariant Symbol Value Token Number Metaphor →
      Iteration Characteristic Invariant Symbol Value Token Number Metaphor →
      Iteration Characteristic Invariant Symbol Value Token Number Metaphor



namespace ITERATION

end ITERATION



class NUMERIC
    (Characteristic   : Type → TOKEN Type)
    (Invariant        : Type)
    (Symbol           : Type)

    -- Metaphysical traits of a number: (One, 1) and its representation
    -- on the page (these are ℝeal to you and I)
    (Value            : Type 1)
    (Token            : Type 1)

    -- A description of the counting process.
    (Number           : TOKEN Invariant)
    (Ordinal          : TOKEN Symbol)
    (Metaphor: TOKEN Invariant → EVENT Value  → BOOL Bool)
    (Metafive: TOKEN Symbol → EVENT Token  → BOOL Bool)


    -- Things that must be true in order for counting to be possible.
    [invariant_equality : DecidableEq (Invariant)]
    [symbol_equality : DecidableEq (Symbol)]
    [value_equality : DecidableEq (Value)]
    [token_equality : DecidableEq (Token)]


    -- Right now, we only care that the value is distinguishable
    -- and the next value is admissible. This allows words like
    -- "twenty or so" as a loose description of a size.
    [DISTINGUISHABLE Characteristic Invariant]
    [DISTINGUISHABLE Characteristic Symbol]
    [event: ADMISSIBLE Invariant Value Metaphor]
    [ADMISSIBLE Symbol Token fun _ t => ADMISSIBLE.admissible? Metaphor Number t]
    [ADMISSIBLE Symbol Token Metafive]
    [COUNTABLE  Characteristic Invariant Symbol
                Value Token
                Number Metaphor]
      where

  glyph: Token
  value: Value
  number: TOKEN Invariant
  ordinal: REFINED (TOKEN Invariant)

  correlant?: TOKEN Invariant → TOKEN Invariant → BOOL Bool :=
    fun s t => (event.admissible? s event.event) == TRUTH &&
               (event.admissible? t event.event) == TRUTH &&
               (Metaphor s event.event) == TRUTH &&
               (Metaphor t event.event) == TRUTH




-- This is purely an induction on the bits differentiatied in the compiler.
inductive Stack
    (Characteristic   : Type → TOKEN Type)
    (Invariant        : Type)
    (Symbol           : Type)
    (Value            : Type 1)
    (Token            : Type 1)
    (Number           : TOKEN Invariant)
    (Ordinal          : TOKEN Symbol)
    (Metaphor: TOKEN Invariant → EVENT Value  → BOOL Bool)
    (Metafive: TOKEN Symbol → EVENT Token  → BOOL Bool)
    [invariant_equality : DecidableEq (Invariant)]
    [symbol_equality : DecidableEq (Symbol)]
    [value_equality : DecidableEq (Value)]
    [token_equality : DecidableEq (Token)]
    [DISTINGUISHABLE Characteristic Invariant]
    [DISTINGUISHABLE Characteristic Symbol]
    [event: ADMISSIBLE Invariant Value Metaphor]
    [ADMISSIBLE Symbol Token fun _ t => ADMISSIBLE.admissible? Metaphor Number t]
    [ADMISSIBLE Symbol Token Metafive]
    [COUNTABLE  Characteristic Invariant Symbol
                Value Token
                Number Metaphor]
    [NUMERIC  Characteristic Invariant Symbol
              Value Token
              Number Ordinal
              Metaphor Metafive]
  where
  | zero :
      TOKEN Invariant →
      REFINED (TOKEN Invariant) →
      Stack Characteristic Invariant Symbol Value Token Number Ordinal
            Metaphor Metafive →
      Stack Characteristic Invariant Symbol Value Token Number Ordinal
            Metaphor Metafive →
      Stack Characteristic Invariant Symbol Value Token Number Ordinal
            Metaphor Metafive
  | succ :
      REFINED (TOKEN Invariant) →
      REFINED (TOKEN Invariant) →
      Stack Characteristic Invariant Symbol Value Token Number Ordinal
            Metaphor Metafive →
      Stack Characteristic Invariant Symbol Value Token Number Ordinal
            Metaphor Metafive →
      Stack Characteristic Invariant Symbol Value Token Number Ordinal
            Metaphor Metafive


namespace Stack

variable  {Characteristic: Type → TOKEN Type}
          {Invariant: Type}
          {Symbol: Type}
          {Value: Type 1}
          {Token: Type 1}
          {Number: TOKEN Invariant}
          {Ordinal: TOKEN Symbol}
          {Metaphor: TOKEN Invariant → EVENT Value  → BOOL Bool}
          {Metafive: TOKEN Symbol → EVENT Token  → BOOL Bool}
          [invariant_equality : DecidableEq (Invariant)]
          [symbol_equality : DecidableEq (Symbol)]
          [value_equality : DecidableEq (Value)]
          [token_equality : DecidableEq (Token)]
          [DISTINGUISHABLE Characteristic Invariant]
          [DISTINGUISHABLE Characteristic Symbol]
          [event: ADMISSIBLE Invariant Value Metaphor]
          [ADMISSIBLE Symbol Token fun _ t => ADMISSIBLE.admissible? Metaphor Number t]
          [ADMISSIBLE Symbol Token Metafive]
          [COUNTABLE  Characteristic Invariant Symbol
                      Value Token
                      Number Metaphor]
          [NUMERIC  Characteristic Invariant Symbol
                    Value Token
                    Number Ordinal
                    Metaphor Metafive]

def ζ
    (n : Stack Characteristic Invariant Symbol
               Value Token Number Ordinal Metaphor Metafive)
      : REFINED (TOKEN Invariant) :=
  match n with
  | zero _ s _ _ => s
  | succ s _ _ _ => s


end Stack


class RELATABLE
    (Characteristic   : Type → TOKEN Type)
    (Invariant        : Type)
    (Symbol           : Type)
    (Value            : Type 1)
    (Token            : Type 1)
    (Number           : TOKEN Invariant)
    (Ordinal          : TOKEN Symbol)
    (Metaphor: TOKEN Invariant → EVENT Value  → BOOL Bool)
    (Metafive: TOKEN Symbol → EVENT Token  → BOOL Bool)
    [invariant_equality : DecidableEq (Invariant)]
    [symbol_equality : DecidableEq (Symbol)]
    [value_equality : DecidableEq (Value)]
    [token_equality : DecidableEq (Token)]
    [DISTINGUISHABLE Characteristic Invariant]
    [DISTINGUISHABLE Characteristic Symbol]
    [event: ADMISSIBLE Invariant Value Metaphor]
    [ADMISSIBLE Symbol Token fun _ t => ADMISSIBLE.admissible? Metaphor Number t]
    [ADMISSIBLE Symbol Token Metafive]
    [COUNTABLE  Characteristic Invariant Symbol
                Value Token
                Number Metaphor]
    [NUMERIC  Characteristic Invariant Symbol
              Value Token
              Number Ordinal
              Metaphor Metafive]
      where

  precedes? : TOKEN Invariant → EVENT Value → BOOL Bool := Metaphor

  lt? : TOKEN Symbol → EVENT Token → BOOL Bool := Metafive

inductive Relation
    (Characteristic   : Type → TOKEN Type)
    (Invariant        : Type)
    (Symbol           : Type)
    (Value            : Type 1)
    (Token            : Type 1)
    (Number           : TOKEN Invariant)
    (Ordinal          : TOKEN Symbol)
    (Metaphor: TOKEN Invariant → EVENT Value  → BOOL Bool)
    (Metafive: TOKEN Symbol → EVENT Token  → BOOL Bool)
    [invariant_equality : DecidableEq (Invariant)]
    [symbol_equality : DecidableEq (Symbol)]
    [value_equality : DecidableEq (Value)]
    [token_equality : DecidableEq (Token)]
    [DISTINGUISHABLE Characteristic Invariant]
    [DISTINGUISHABLE Characteristic Symbol]
    [event: ADMISSIBLE Invariant Value Metaphor]
    [ADMISSIBLE Symbol Token fun _ t => ADMISSIBLE.admissible? Metaphor Number t]
    [ADMISSIBLE Symbol Token Metafive]
    [COUNTABLE  Characteristic Invariant Symbol
                Value Token
                Number Metaphor]
    [NUMERIC  Characteristic Invariant Symbol
              Value Token
              Number Ordinal
              Metaphor Metafive]
    [RELATABLE  Characteristic Invariant
                Symbol Value Token Number Ordinal
                Metaphor Metafive]
      where
  | nil : Relation Characteristic Invariant Symbol Value Token Number Ordinal
             Metaphor Metafive →
          Relation Characteristic Invariant Symbol Value Token Number Ordinal
             Metaphor Metafive
  | cons: EVENT Token →
          Relation Characteristic Invariant Symbol Value Token Number Ordinal
             Metaphor Metafive →
          Relation Characteristic Invariant Symbol Value Token Number Ordinal
             Metaphor Metafive

class REPRESENTATIVE
    (Characteristic   : Type → TOKEN Type)
    (Invariant        : Type)
    (Symbol           : Type)
    (Value            : Type 1)
    (Token            : Type 1)
    (Representative   : Prop)

    (Number           : TOKEN Invariant)
    (Ordinal          : TOKEN Symbol)

    -- holy hell....
    (TRUTH)

    (Metaphor: TOKEN Invariant → EVENT Value  → BOOL Bool)
    (Metafive: TOKEN Symbol → EVENT Token  → BOOL Bool)
    [invariant_equality : DecidableEq (Invariant)]
    [symbol_equality : DecidableEq (Symbol)]
    [value_equality : DecidableEq (Value)]
    [token_equality : DecidableEq (Token)]
    [DISTINGUISHABLE Characteristic Invariant]
    [DISTINGUISHABLE Characteristic Symbol]
    [event: ADMISSIBLE Invariant Value Metaphor]
    [ADMISSIBLE Symbol Token fun _ t => ADMISSIBLE.admissible? Metaphor Number t]
    [ADMISSIBLE Symbol Token Metafive]
    [COUNTABLE  Characteristic Invariant Symbol
                Value Token
                Number Metaphor]
    [NUMERIC  Characteristic Invariant Symbol
              Value Token
              Number Ordinal
              Metaphor Metafive]
    [RELATABLE  Characteristic Invariant
                Symbol Value Token Number Ordinal
                Metaphor Metafive]
      where
  carrier: TRUTH
  compiled_symbol: Representative
  representative: Invariant
  invariant: Symbol
  symbol: Value
  value: TOKEN Invariant
  number: TOKEN Symbol

namespace REPRESENTATIVE

variable  {Characteristic   : Type → TOKEN Type}
          {Invariant        : Type}
          {Symbol           : Type}
          {Value            : Type 1}
          {Token            : Type 1}
          {Representative   : Prop}
          {Number           : TOKEN Invariant}
          {Ordinal          : TOKEN Symbol}
          {Metaphor         : TOKEN Invariant → EVENT Value → BOOL Bool}
          {Metafive         : TOKEN Symbol   → EVENT Token → BOOL Bool}
          [invariant_equality : DecidableEq Invariant]
          [symbol_equality    : DecidableEq Symbol]
          [value_equality     : DecidableEq Value]
          [token_equality     : DecidableEq Token]
          [DISTINGUISHABLE Characteristic Invariant]
          [DISTINGUISHABLE Characteristic Symbol]
          [value_event : ADMISSIBLE Invariant Value Metaphor]
          [token_event : ADMISSIBLE Symbol Token fun _ t =>
              ADMISSIBLE.admissible? Metaphor Number t]
          [symbolic_event : ADMISSIBLE Symbol Token Metafive]
          [COUNTABLE Characteristic Invariant Symbol
                     Value Token
                     Number Metaphor]
          [NUMERIC Characteristic Invariant Symbol
                   Value Token
                   Number Ordinal
                   Metaphor Metafive]
          [rel : RELATABLE Characteristic Invariant
                            Symbol Value Token Number Ordinal
                            Metaphor Metafive]
          [r : REPRESENTATIVE Characteristic Invariant Symbol
                              Value Token Representative
                              Number Ordinal (BOOL Bool)
                              Metaphor Metafive]

def admissible? : BOOL Bool :=
  if (r.carrier == TRUTH) &&
     (rel.precedes? (some r.representative) value_event.event == TRUTH) &&
     (rel.lt? (some r.invariant) symbolic_event.event == TRUTH)
  then
    TRUTH
  else
    __SILENCE__

end REPRESENTATIVE

-- These are all the numbers that the compiler can "represent"
inductive Numbers
    (Characteristic   : Type → TOKEN Type)
    (Invariant        : Type)
    (Symbol           : Type)
    (Value            : Type 1)
    (Token            : Type 1)
    (Representative   : Prop)

    (Number           : TOKEN Invariant)
    (Ordinal          : TOKEN Symbol)

    -- holy hell....
    (Truth: BOOL Bool)

    (Metaphor: TOKEN Invariant → EVENT Value  → BOOL Bool)
    (Metafive: TOKEN Symbol → EVENT Token  → BOOL Bool)
    [invariant_equality : DecidableEq (Invariant)]
    [symbol_equality : DecidableEq (Symbol)]
    [value_equality : DecidableEq (Value)]
    [token_equality : DecidableEq (Token)]
    [DISTINGUISHABLE Characteristic Invariant]
    [DISTINGUISHABLE Characteristic Symbol]
    [event: ADMISSIBLE Invariant Value Metaphor]
    [ADMISSIBLE Symbol Token fun _ t => ADMISSIBLE.admissible? Metaphor Number t]
    [ADMISSIBLE Symbol Token Metafive]
    [COUNTABLE  Characteristic Invariant Symbol
                Value Token
                Number Metaphor]
    [NUMERIC  Characteristic Invariant Symbol
              Value Token
              Number Ordinal
              Metaphor Metafive]
    [RELATABLE  Characteristic Invariant
                Symbol Value Token Number Ordinal
                Metaphor Metafive]
    [r : REPRESENTATIVE Characteristic Invariant Symbol
                        Value Token Representative
                        Number Ordinal (BOOL Bool)
                        Metaphor Metafive]

    | zero :
        TOKEN Invariant →
        REFINED (TOKEN Invariant) →
        Numbers Characteristic Invariant Symbol Value Token Representative
                Number Ordinal Truth
                Metaphor Metafive →
        Numbers Characteristic Invariant Symbol Value Token Representative
                Number Ordinal Truth
                Metaphor Metafive →
        Numbers Characteristic Invariant Symbol Value Token Representative
                Number Ordinal Truth
                Metaphor Metafive

class ENCODED
    (Characteristic   : Type → TOKEN Type)
    (Invariant        : Type)
    (Symbol           : Type)
    (Value            : Type 1)
    (Token            : Type 1)
    (Representative   : Prop)

    (Number           : TOKEN Invariant)
    (Ordinal          : TOKEN Symbol)

    (Truth: BOOL Bool)

    (Metaphor: TOKEN Invariant → EVENT Value  → BOOL Bool)
    (Metafive: TOKEN Symbol → EVENT Token  → BOOL Bool)
    [invariant_equality : DecidableEq (Invariant)]
    [symbol_equality : DecidableEq (Symbol)]
    [value_equality : DecidableEq (Value)]
    [token_equality : DecidableEq (Token)]
    [DISTINGUISHABLE Characteristic Invariant]
    [DISTINGUISHABLE Characteristic Symbol]
    [event: ADMISSIBLE Invariant Value Metaphor]
    [ADMISSIBLE Symbol Token fun _ t => ADMISSIBLE.admissible? Metaphor Number t]
    [ADMISSIBLE Symbol Token Metafive]
    [COUNTABLE  Characteristic Invariant Symbol
                Value Token
                Number Metaphor]
    [NUMERIC  Characteristic Invariant Symbol
              Value Token
              Number Ordinal
              Metaphor Metafive]
    [RELATABLE  Characteristic Invariant
                Symbol Value Token Number Ordinal
                Metaphor Metafive]
    [r : REPRESENTATIVE Characteristic Invariant Symbol
                        Value Token Representative
                        Number Ordinal (BOOL Bool)
                        Metaphor Metafive]
        where

  carrier: Representative
  representative: Invariant
  invariant: Symbol
  symbol: Value
  value: TOKEN Invariant
  number: TOKEN Symbol

inductive Tape
    (Characteristic   : Type → TOKEN Type)
    (Invariant        : Type)
    (Symbol           : Type)
    (Value            : Type 1)
    (Token            : Type 1)
    (Representative   : Prop)

    (Number           : TOKEN Invariant)
    (Ordinal          : TOKEN Symbol)

    (Truth: BOOL Bool)

    (Metaphor: TOKEN Invariant → EVENT Value  → BOOL Bool)
    (Metafive: TOKEN Symbol → EVENT Token  → BOOL Bool)
    [invariant_equality : DecidableEq (Invariant)]
    [symbol_equality : DecidableEq (Symbol)]
    [value_equality : DecidableEq (Value)]
    [token_equality : DecidableEq (Token)]
    [DISTINGUISHABLE Characteristic Invariant]
    [DISTINGUISHABLE Characteristic Symbol]
    [event: ADMISSIBLE Invariant Value Metaphor]
    [ADMISSIBLE Symbol Token fun _ t => ADMISSIBLE.admissible? Metaphor Number t]
    [ADMISSIBLE Symbol Token Metafive]
    [COUNTABLE  Characteristic Invariant Symbol
                Value Token
                Number Metaphor]
    [NUMERIC  Characteristic Invariant Symbol
              Value Token
              Number Ordinal
              Metaphor Metafive]
    [RELATABLE  Characteristic Invariant
                Symbol Value Token Number Ordinal
                Metaphor Metafive]
    [r : REPRESENTATIVE Characteristic Invariant Symbol
                        Value Token Representative
                        Number Ordinal (BOOL Bool)
                        Metaphor Metafive]
    [ENCODED Characteristic Invariant Symbol
              Value Token Representative
              Number Ordinal Truth   -- We have resolved 1 bit.
              Metaphor Metafive]
  | nil : TOKEN Invariant →
          REFINED (TOKEN Invariant) →
          Tape Characteristic Invariant Symbol Value Token Representative
               Number Ordinal Truth
               Metaphor Metafive →
          Tape Characteristic Invariant Symbol Value Token Representative
               Number Ordinal Truth
               Metaphor Metafive →
          Tape Characteristic Invariant Symbol Value Token Representative
               Number Ordinal Truth
               Metaphor Metafive
  | cons :  REFINED (Invariant) →
            REFINE  (TOKEN Invariant) →  -- This is how we resolve the bit
            Tape Characteristic Invariant Symbol Value Token Representative
                 Number Ordinal Truth
                 Metaphor Metafive →
            Tape Characteristic Invariant Symbol Value Token Representative
                  Number Ordinal Truth
                  Metaphor Metafive →
            Tape Characteristic Invariant Symbol Value Token Representative
                  Number Ordinal Truth
                  Metaphor Metafive


class COMPUTABLE
    (Characteristic   : Type → TOKEN Type)
    (Invariant        : Type)
    (Symbol           : Type)
    (Value            : Type 1)
    (Token            : Type 1)
    (Representative   : Prop)

    (Number           : TOKEN Invariant)
    (Ordinal          : TOKEN Symbol)

    (Truth: BOOL Bool)

    (Metaphor: TOKEN Invariant → EVENT Value  → BOOL Bool)
    (Metafive: TOKEN Symbol → EVENT Token  → BOOL Bool)
    [invariant_equality : DecidableEq (Invariant)]
    [symbol_equality : DecidableEq (Symbol)]
    [value_equality : DecidableEq (Value)]
    [token_equality : DecidableEq (Token)]
    [DISTINGUISHABLE Characteristic Invariant]
    [DISTINGUISHABLE Characteristic Symbol]
    [event: ADMISSIBLE Invariant Value Metaphor]
    [ADMISSIBLE Symbol Token fun _ t => ADMISSIBLE.admissible? Metaphor Number t]
    [ADMISSIBLE Symbol Token Metafive]
    [COUNTABLE  Characteristic Invariant Symbol
                Value Token
                Number Metaphor]
    [NUMERIC  Characteristic Invariant Symbol
              Value Token
              Number Ordinal
              Metaphor Metafive]
    [RELATABLE  Characteristic Invariant
                Symbol Value Token Number Ordinal
                Metaphor Metafive]
    [r : REPRESENTATIVE Characteristic Invariant Symbol
                        Value Token Representative
                        Number Ordinal (BOOL Bool)
                        Metaphor Metafive]
    [ENCODED Characteristic Invariant Symbol
              Value Token Representative
              Number Ordinal Truth   -- We have resolved 1 bit.
              Metaphor Metafive]
        where
  carrier: Invariant
  invariant: Symbol
  symbol: Value
  value: TOKEN Invariant
  number: TOKEN Symbol

inductive Ledger
    (Characteristic   : Type → TOKEN Type)
    (Invariant        : Type)
    (Symbol           : Type)
    (Value            : Type 1)
    (Token            : Type 1)
    (Representative   : Prop)

    (Number           : TOKEN Invariant)
    (Ordinal          : TOKEN Symbol)

    (Truth: BOOL Bool)

    (Metaphor: TOKEN Invariant → EVENT Value  → BOOL Bool)
    (Metafive: TOKEN Symbol → EVENT Token  → BOOL Bool)
    [invariant_equality : DecidableEq (Invariant)]
    [symbol_equality : DecidableEq (Symbol)]
    [value_equality : DecidableEq (Value)]
    [token_equality : DecidableEq (Token)]
    [DISTINGUISHABLE Characteristic Invariant]
    [DISTINGUISHABLE Characteristic Symbol]
    [event: ADMISSIBLE Invariant Value Metaphor]
    [ADMISSIBLE Symbol Token fun _ t => ADMISSIBLE.admissible? Metaphor Number t]
    [ADMISSIBLE Symbol Token Metafive]
    [COUNTABLE  Characteristic Invariant Symbol
                Value Token
                Number Metaphor]
    [NUMERIC  Characteristic Invariant Symbol
              Value Token
              Number Ordinal
              Metaphor Metafive]
    [RELATABLE  Characteristic Invariant
                Symbol Value Token Number Ordinal
                Metaphor Metafive]
    [r : REPRESENTATIVE Characteristic Invariant Symbol
                        Value Token Representative
                        Number Ordinal (BOOL Bool)
                        Metaphor Metafive]
    [ENCODED Characteristic Invariant Symbol
              Value Token Representative
              Number Ordinal Truth   -- We have resolved 1 bit.
              Metaphor Metafive]
    [COMPUTABLE Characteristic Invariant Symbol
                Value Token Representative
                Number Ordinal Truth   -- We have resolved 1 bit.
                Metaphor Metafive]
  | nil : TOKEN Invariant →
          REFINE (TOKEN Invariant) →
          Ledger Characteristic Invariant Symbol Value Token Representative
               Number Ordinal Truth Metaphor Metafive →
          Ledger Characteristic Invariant Symbol Value Token Representative
               Number Ordinal Truth Metaphor Metafive →
          Ledger Characteristic Invariant Symbol Value Token Representative
               Number Ordinal Truth Metaphor Metafive
  | cons: REFINE Invariant →
          REFINE (TOKEN Invariant) →
          Ledger Characteristic Invariant Symbol Value Token Representative
               Number Ordinal Truth Metaphor Metafive →
          Ledger Characteristic Invariant Symbol Value Token Representative
               Number Ordinal Truth Metaphor Metafive →
          Ledger Characteristic Invariant Symbol Value Token Representative
               Number Ordinal Truth Metaphor Metafive



class PHYSICAL
    (Characteristic   : Type → TOKEN Type)
    (Invariant        : Type)
    (Symbol           : Type)
    (Value            : Type 1)
    (Token            : Type 1)
    (Representative   : Prop)

    (Number           : TOKEN Invariant)
    (Ordinal          : TOKEN Symbol)

    (Truth: BOOL Bool)

    (Metaphor: TOKEN Invariant → EVENT Value  → BOOL Bool)
    (Metafive: TOKEN Symbol → EVENT Token  → BOOL Bool)
    [invariant_equality : DecidableEq (Invariant)]
    [symbol_equality : DecidableEq (Symbol)]
    [value_equality : DecidableEq (Value)]
    [token_equality : DecidableEq (Token)]
    [DISTINGUISHABLE Characteristic Invariant]
    [DISTINGUISHABLE Characteristic Symbol]
    [event: ADMISSIBLE Invariant Value Metaphor]
    [ADMISSIBLE Symbol Token fun _ t => ADMISSIBLE.admissible? Metaphor Number t]
    [ADMISSIBLE Symbol Token Metafive]
    [COUNTABLE  Characteristic Invariant Symbol
                Value Token
                Number Metaphor]
    [NUMERIC  Characteristic Invariant Symbol
              Value Token
              Number Ordinal
              Metaphor Metafive]
    [RELATABLE  Characteristic Invariant
                Symbol Value Token Number Ordinal
                Metaphor Metafive]
    [r : REPRESENTATIVE Characteristic Invariant Symbol
                        Value Token Representative
                        Number Ordinal (BOOL Bool)
                        Metaphor Metafive]
    [ENCODED Characteristic Invariant Symbol
              Value Token Representative
              Number Ordinal Truth   -- We have resolved 1 bit.
              Metaphor Metafive]
    [COMPUTABLE Characteristic Invariant Symbol
                Value Token Representative
                Number Ordinal Truth   -- We have resolved 1 bit.
                Metaphor Metafive]
      where
  carrier: Symbol
  symbol: Value
  value: TOKEN Invariant
  number: TOKEN Symbol

  -- This compiles one bit at a time.
  slip? : TOKEN Invariant → REFINE (TOKEN Invariant) → BOOL Bool :=
    fun s t => if r.admissible? s t = TRUTH then TRUTH else __SILENCE__


inductive Domain
    (Characteristic   : Type → TOKEN Type)
    (Invariant        : Type)
    (Carrier          : Prop)
    (Parameter        : Type i)       -- Metaphysical trait across all time
    (OpCode           : Type 1)       -- The metaphysical value right now
    (Assembly         : Invariant)    -- The decomposition to interpret a number as a value
    (NextParameter    :  Type i → REFINED (Type i))
    (NextOpCode       :  Type 1 → REFINED (Type 1))
    (NextAssembly     :  Type   → REFINED  Type   )
    (ActOfCounting : EVENT Type)
    (Metaphor: TOKEN Invariant → REFINE (TOKEN Invariant)  → BOOL Bool)
    [DecidableEq (Parameter)]
    [DecidableEq (OpCode)]
    [DecidableEq (Invariant)]
    [DISTINGUISHABLE Characteristic Invariant]
    [counting: ADMISSIBLE ActOfCounting
                          NextOpCode Invariant
                          NextAssembly Metaphor]
    [origin: COUNTABLE  Characteristic Invariant
                        Parameter OpCode Assembly
                        NextParameter NextOpCode NextAssembly
                        ActOfCounting Metaphor]
    [relation: RELATABLE Characteristic Invariant ActOfCounting
                        NextOpCode NextAssembly Metaphor]
    [NUMERIC Characteristic Invariant Carrier
              Parameter OpCode Assembly
              NextParameter NextOpCode NextAssembly
              ActOfCounting Metaphor]
    [REPRESENTATIVE Characteristic Invariant Carrier
                    Parameter OpCode Assembly
                    NextParameter NextOpCode NextAssembly
                    ActOfCounting Metaphor]
    [ENCODED Characteristic Invariant Carrier
              Parameter OpCode Assembly
              NextParameter NextOpCode NextAssembly
              ActOfCounting Metaphor]
    [COMPUTABLE Characteristic Invariant Carrier
                Parameter OpCode Assembly
                NextParameter NextOpCode NextAssembly
                ActOfCounting Metaphor]
    [PHYSICAL Characteristic
              Invariant Carrier
              Parameter OpCode Assembly
              NextParameter NextOpCode NextAssembly
              ActOfCounting Metaphor]

  | nil : REFINED (TOKEN Invariant) →
          History Characteristic Invariant Carrier Parameter OpCode Assembly
                  NextParameter NextOpCode NextAssembly ActOfCounting Metaphor

  | cons :  REFINED (Invariant) →
            REFINE  (TOKEN Invariant) →
            History Characteristic Invariant Carrier Parameter OpCode Assembly
                    NextParameter NextOpCode NextAssembly ActOfCounting Metaphor →
            History Characteristic Invariant Carrier Parameter OpCode Assembly
                    NextParameter NextOpCode NextAssembly ActOfCounting Metaphor →
            History Characteristic Invariant Carrier Parameter OpCode Assembly
                    NextParameter NextOpCode NextAssembly ActOfCounting Metaphor
end Measurement
