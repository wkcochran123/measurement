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
    (Value: Type 1)
    (Description: Type → REFINED (Type))
    (Invariant: Type)

     -- Notice the metaphor is starting to work on abstract types.
     -- It is _metaphysical_.
    (Metaphor: TOKEN Invariant → EVENT Value → BOOL Bool)
    where

  admissible? : TOKEN Invariant → EVENT Value → BOOL Bool := Metaphor

  event: EVENT Value

namespace ADMISSIBLE
variable {Invariant: Type}
         {Value: Type 1}
         {Description: Type → REFINED (Type)}
         {Metaphor: TOKEN Invariant → EVENT Value → BOOL Bool}
         [a : ADMISSIBLE Value Description -- for the
                         Invariant Metaphor]
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

    -- Metaphysical traits of a number: (One, 1) and its representation
    -- on the page (these are ℝeal to you and I)
    (Value            : Type 1)
    (Token            : Type 1)
    (ValueDescription      : Type → REFINED (Type))
    (TokenDescription      : Type → REFINED (Type))


    -- A description of the counting process.
    (ActOfCounting    : EVENT Type)
    (Metaphor: TOKEN Invariant → EVENT Value  → BOOL Bool)


    -- Things that must be true in order for counting to be possible.
    [invariant_equality : DecidableEq (Invariant)]
    [value_equality : DecidableEq (Value)]
    [token_equality : DecidableEq (Token)]

    -- Right now, we only care that the value is distinguishable
    -- and the next value is admissible. This allows words like
    -- "twenty or so" as a loose description of a size.
    [DISTINGUISHABLE Characteristic Invariant]
    [ADMISSIBLE Value ValueDescription Invariant Metaphor]
    [ADMISSIBLE Token TokenDescription Invariant Metaphor]
      where

  symbol: Token

  -- The notion of the origin does not change.  This is the root of
  -- a _frame of reference_.  This is the thing that has 0 velocity and
  -- 0 value.  We count this guy.  Just like Peano.
  -- Have no idea _WHAT_ has no value or velocity yet, but I'm sure it
  -- is important.
  origin: TOKEN Invariant

namespace COUNTABLE
variable  {Characteristic: Type → TOKEN Type}
          {Invariant: Type}
          {Value: Type 1}
          {Token: Type 1}
          {ValueDescription: Type → REFINED (Type)}
          {TokenDescription: Type → REFINED (Type)}
          {ActOfCounting: EVENT Type}
          {Metaphor: TOKEN Invariant → EVENT Value → BOOL Bool}
          [invariant_equality : DecidableEq (Invariant)]
          [value_equality : DecidableEq (Value)]
          [token_equality : DecidableEq (Token)]
          [DISTINGUISHABLE Characteristic Invariant]
          [ADMISSIBLE Value ValueDescription Invariant Metaphor]
          [ADMISSIBLE Token TokenDescription Invariant Metaphor]
          [c: COUNTABLE Characteristic Invariant
                        Value Token
                        ValueDescription TokenDescription
                        ActOfCounting Metaphor]

end COUNTABLE


inductive Iteration
    (Characteristic   : Type → TOKEN Type)
    (Invariant        : Type)

    -- Metaphysical traits of a number: (One, 1) and its representation
    -- on the page (these are ℝeal to you and I)
    (Value            : Type 1)
    (Token            : Type 1)
    (ValueDescription      : Type → REFINED (Type))
    (TokenDescription      : Type → REFINED (Type))


    -- A description of the counting process.
    (ActOfCounting : EVENT Type)
    (Metaphor: TOKEN Invariant → EVENT Value  → BOOL Bool)


    -- Things that must be true in order for counting to be possible.
    [invariant_equality : DecidableEq (Invariant)]
    [value_equality : DecidableEq (Value)]
    [token_equality : DecidableEq (Token)]


    -- Right now, we only care that the value is distinguishable
    -- and the next value is admissible. This allows words like
    -- "twenty or so" as a loose description of a size.
    [DISTINGUISHABLE Characteristic Invariant]
    [ADMISSIBLE Value ValueDescription Invariant Metaphor]
    [ADMISSIBLE Token TokenDescription Invariant Metaphor]
    [COUNTABLE Characteristic Invariant
               Value Token
               ValueDescription TokenDescription
               ActOfCounting Metaphor]
      where

  | nil :
      REFINED (TOKEN Invariant) →
      Iteration Characteristic Invariant Value Token ValueDescription TokenDescription
                ActOfCounting Metaphor
  | cons :
      REFINED (Invariant) →
      REFINED (TOKEN Invariant) →
      Iteration Characteristic Invariant Value Token ValueDescription TokenDescription
                ActOfCounting Metaphor →
      Iteration Characteristic Invariant Value Token ValueDescription TokenDescription
                ActOfCounting Metaphor →
      Iteration Characteristic Invariant Value Token ValueDescription TokenDescription
                ActOfCounting Metaphor


-- So we found a COMPILER invariant: an inductive Iteration.
-- A COUNTABLE Symbol of Type has to be named in order to compile
-- this iteration.
-- However, we do NOT want to instantiate that as that would confuse
-- the symbol for the fact.  We have no idea if it is a fact yet.
-- BUT.... the compiler HAS given us a carrier for invariant!
-- We have an indication that the compiler has distinct as a symbol!
-- The CARRIER will tell us if the current symbol has been distinct
-- by the compiler.
def CARRIER
    {Characteristic : Type → TOKEN Type}
    {Invariant : Type}
    [DecidableEq Invariant]
    [d : DISTINGUISHABLE Characteristic Invariant]
    (s : Invariant) : Prop :=
  d.distinct? s
-- The root of the Invariant is the BOOL Bool.  Bool is a Prop. A
-- Prop can be named in the compiler.  So, we have a symbol that
-- names a symbol in the compiler that is never instantiated, only
-- probed and waited for.

namespace ITERATION
variable  {Characteristic: Type → TOKEN Type}

end ITERATION

class RELATABLE
    (Characteristic   : Type → TOKEN Type)
    (Value            : Type 1)
    (Invariant        : Type)
    (Event            : EVENT Type)
    (Description      : Type → REFINED Type)
    (Metaphor         : TOKEN Invariant → EVENT Value → BOOL Bool)

    [invariant_equality : DecidableEq (Invariant)]
    [value_equality : DecidableEq (Value)]

    [DecidableEq Invariant]
    [DISTINGUISHABLE Characteristic Invariant]
    [a : ADMISSIBLE Value Description Invariant Metaphor]
    where

  rel : TOKEN Invariant → EVENT Value → Prop :=
    fun s t => a.admissible? s t = some true

  dec_rel : DecidableRel rel

  lt?: TOKEN Invariant → TOKEN Invariant → Prop :=
    fun s t => rel s (a.event) ∧ ¬ rel t (a.event)


class NUMERIC
    (Characteristic   : Type → TOKEN Type)
    (Invariant        : Type)

    -- Metaphysical traits of a number: (One, 1) and its representation
    -- on the page (these are ℝeal to you and I)
    (Value            : Type 1)
    (Token            : Type 1)
    (ValueDescription      : Type → REFINED (Type))
    (TokenDescription      : Type → REFINED (Type))


    -- A description of the counting process.
    (ActOfCounting : EVENT Type)
    (Metaphor: TOKEN Invariant → EVENT Value  → BOOL Bool)


    -- Things that must be true in order for counting to be possible.
    [invariant_equality : DecidableEq (Invariant)]
    [value_equality : DecidableEq (Value)]
    [token_equality : DecidableEq (Token)]


    -- Right now, we only care that the value is distinguishable
    -- and the next value is admissible. This allows words like
    -- "twenty or so" as a loose description of a size.
    [DISTINGUISHABLE Characteristic Invariant]
    [ADMISSIBLE Value ValueDescription Invariant Metaphor]
    [ADMISSIBLE Token TokenDescription Invariant Metaphor]
    [COUNTABLE  Characteristic Invariant
                Value Token
                ValueDescription TokenDescription
                ActOfCounting Metaphor]
    [r: RELATABLE Characteristic Value Invariant
                  ActOfCounting ValueDescription Metaphor]
      where

  -- Could this be real life?
  -- Or is this just fantasy?
  variable_name: Invariant
  -- For those keeping score at home, variable_name can represent anything that you can count, including
  -- π, e, and √{-1}.  Although, the last one is exclusively Gaussian integers. We label that
  -- value by its name _variable name_.
  -- BTW, this label is _in the compiler_, not in the proof.  It is æther that cannot
  -- be distinct --- yet.

  carrier: Carrier
  -- We can also ask the compiler if the current symbol has been distinct.

  lt?: TOKEN Invariant → TOKEN Invariant → Prop :=
    fun s t => r.lt? s t


-- This is purely an induction on the bits differentiatied in the compiler.
inductive Count
    (Characteristic   : Type → TOKEN Type)
    (Invariant        : Type)

    -- Metaphysical traits of a number: (One, 1) and its representation
    -- on the page (these are ℝeal to you and I)
    (Value            : Type 1)
    (Token            : Type 1)
    (ValueDescription      : Type → REFINED (Type))
    (TokenDescription      : Type → REFINED (Type))


    -- A description of the counting process.
    (ActOfCounting : EVENT Type)
    (Metaphor: TOKEN Invariant → EVENT Value  → BOOL Bool)


    -- Things that must be true in order for counting to be possible.
    [invariant_equality : DecidableEq (Invariant)]
    [value_equality : DecidableEq (Value)]
    [token_equality : DecidableEq (Token)]


    -- Right now, we only care that the value is distinguishable
    -- and the next value is admissible. This allows words like
    -- "twenty or so" as a loose description of a size.
    [DISTINGUISHABLE Characteristic Invariant]
    [ADMISSIBLE Value ValueDescription Invariant Metaphor]
    [ADMISSIBLE Token TokenDescription Invariant Metaphor]
    [COUNTABLE  Characteristic Invariant
                Value Token
                ValueDescription TokenDescription
                ActOfCounting Metaphor]
    [r: RELATABLE Characteristic Value Invariant
                  ActOfCounting ValueDescription Metaphor]
    [number: NUMERIC Characteristic Invariant Value Token
                     ValueDescription TokenDescription
                     ActOfCounting Metaphor]
  | zero :
      TOKEN (Invariant) →
      Count Characteristic Invariant Value Token ValueDescription TokenDescription
            ActOfCounting Metaphor
  | succ :
      Invariant
      → TOKEN (Invariant) →
      Count Characteristic Invariant Value Token ValueDescription TokenDescription ActOfCounting Metaphor →
      Count Characteristic Invariant Value Token ValueDescription TokenDescription ActOfCounting Metaphor


namespace Count
variable  {Characteristic: Type → TOKEN Type}
          {Invariant: Type}
          {Value: Type 1}
          {Token: Type 1}
          {ValueDescription: Type → REFINED (Type)}
          {TokenDescription: Type → REFINED (Type)}
          {ActOfCounting: EVENT Type}
          {Metaphor: TOKEN Invariant → EVENT Value → BOOL Bool}
          [invariant_equality : DecidableEq (Invariant)]
          [value_equality : DecidableEq (Value)]
          [token_equality : DecidableEq (Token)]
          [DISTINGUISHABLE Characteristic Invariant]
          [ADMISSIBLE Value ValueDescription Invariant Metaphor]
          [ADMISSIBLE Token TokenDescription Invariant Metaphor]
          [c: COUNTABLE  Characteristic Invariant
                         Value Token
                         ValueDescription TokenDescription
                         ActOfCounting Metaphor]
          [r: RELATABLE Characteristic Value Invariant
                        ActOfCounting ValueDescription Metaphor]
          [number: NUMERIC  Characteristic Invariant Value Token
                            ValueDescription TokenDescription
                            ActOfCounting Metaphor]

def ζ
    (n : Count Characteristic Invariant Value Token ValueDescription TokenDescription
                ActOfCounting Metaphor)
      : TOKEN Invariant :=
  match n with
  | zero _ => c.origin
  | succ _ n' _ => n'

end Count

-- "We are putting a theorem prover in your theorem prover
-- so you can prove theorems about theorems while you prove
-- theorems about theorems about the world."
                            -- Willie Nelson

-- This will actually give us One, Two Three.
class REPRESENTATIVE
    (Characteristic   : Type → TOKEN Type)
    (Invariant        : Type)
    (Carrier          : Prop)
    (Value            : Type 1)       -- The metaphysical value right now
    (Token            : Type 1)
    (Variable         : Type i)       -- uh, oh.  something can vary!
    (Representation   : Invariant)    -- The decomposition to interpret a number as a value
    (NextName            :  Type i → REFINED (Type i))
    (NextValue           :  Type 1 → REFINED (Type 1))
    (NextRepresentation  :  Type   → REFINED  Type   )
    (ActOfCounting : EVENT Type)
    (Metaphor: TOKEN Invariant → REFINE (TOKEN Invariant)  → BOOL Bool)
    [value_equality : DecidableEq (Value)]
    [invariant_equality : DecidableEq (Invariant)]
    [name_equality : DecidableEq (Name)]
    [DISTINGUISHABLE Characteristic Invariant]
    [ADMISSIBLE ActOfCounting
                NextValue Invariant
                NextRepresentation Metaphor]
    [origin: COUNTABLE  Characteristic Invariant
                        Name Value Representation
                        NextName NextValue NextRepresentation
                        ActOfCounting Metaphor]
    [relation: RELATABLE Characteristic Invariant ActOfCounting
                         NextValue NextRepresentation Metaphor]
      where

  ordinal: Invariant
  carrier: Carrier


-- These are all the numbers that the compiler can "represent"
inductive Numbers
      (Characteristic   : Type → TOKEN Type)
      (Invariant        : Type)
      (Carrier          : Prop)
      (Name             : Type i)       -- Metaphysical trait across all time
      (Value            : Type 1)       -- The metaphysical value right now
      (Representation   : Invariant)    -- The decomposition to interpret a number as a value
      (NextName            :  Type i → REFINED (Type i))
      (NextValue           :  Type 1 → REFINED (Type 1))
      (NextRepresentation  :  Type   → REFINED  Type   )
      (ActOfCounting : EVENT Type)
      (Metaphor: TOKEN Invariant → REFINE (TOKEN Invariant)  → BOOL Bool)
      [value_equality : DecidableEq (Value)]
      [invariant_equality : DecidableEq (Invariant)]
      [name_equality : DecidableEq (Name)]
      [DISTINGUISHABLE Characteristic Invariant]
      [ADMISSIBLE ActOfCounting
                  NextValue Invariant
                  NextRepresentation Metaphor]
      [origin: COUNTABLE  Characteristic Invariant
                          Name Value Representation
                          NextName NextValue NextRepresentation
                          ActOfCounting Metaphor]
      [relation: RELATABLE Characteristic Invariant ActOfCounting
                          NextValue NextRepresentation Metaphor]
      [REPRESENTATIVE Characteristic Invariant Carrier Name Value Representation
                      NextName NextValue NextRepresentation ActOfCounting Metaphor]

    | zero :
        Numbers Characteristic Invariant Carrier Name Value Representation
                NextName NextValue NextRepresentation ActOfCounting Metaphor

    | succ :
        Count Characteristic Invariant Carrier Name Value Representation
              NextName NextValue NextRepresentation ActOfCounting Metaphor →
        Numbers Characteristic Invariant Carrier Name Value Representation
                NextName NextValue NextRepresentation ActOfCounting Metaphor

class ENCODED
      (Characteristic   : Type → TOKEN Type)
      (Invariant        : Type)
      (Carrier          : Prop)
      (Name             : Type i)       -- Metaphysical trait across all time
      (Value            : Type 1)       -- The metaphysical value right now
      (Representation   : Invariant)    -- The decomposition to interpret a number as a value
      (NextName            :  Type i → REFINED (Type i))
      (NextValue           :  Type 1 → REFINED (Type 1))
      (NextRepresentation  :  Type   → REFINED  Type   )
      (ActOfCounting : EVENT Type)
      (Metaphor: TOKEN Invariant → REFINE (TOKEN Invariant)  → BOOL Bool)
      [value_equality : DecidableEq (Value)]
      [invariant_equality : DecidableEq (Invariant)]
      [name_equality : DecidableEq (Name)]
      [DISTINGUISHABLE Characteristic Invariant]
      [ADMISSIBLE ActOfCounting
                  NextValue Invariant
                  NextRepresentation Metaphor]
      [origin: COUNTABLE  Characteristic Invariant
                          Name Value Representation
                          NextName NextValue NextRepresentation
                          ActOfCounting Metaphor]
      [relation: RELATABLE Characteristic Invariant ActOfCounting
                          NextValue NextRepresentation Metaphor]
      [REPRESENTATIVE Characteristic Invariant Carrier
                      Name Value Representation
                      NextName NextValue NextRepresentation
                      ActOfCounting Metaphor]
        where

  representation_of_numbers: Invariant
  -- This is best estimate of our understanding of the compiler's representation.

  carrier: Carrier

class COMPUTABLE
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
    [ADMISSIBLE ActOfCounting
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
        where
  instruction: Invariant
  carrier: Carrier

inductive Ledger
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
    [ADMISSIBLE ActOfCounting
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
  | nil : REFINED (TOKEN Invariant) →
          Ledger Characteristic Invariant Carrier Parameter OpCode Assembly
                 NextParameter NextOpCode NextAssembly ActOfCounting Metaphor
  | cons : REFINED (Invariant) →
           REFINE  (TOKEN Invariant) →
           Ledger Characteristic Invariant Carrier Parameter OpCode Assembly
                  NextParameter NextOpCode NextAssembly ActOfCounting Metaphor →
           Ledger Characteristic Invariant Carrier Parameter OpCode Assembly
                  NextParameter NextOpCode NextAssembly ActOfCounting Metaphor →
           Ledger Characteristic Invariant Carrier Parameter OpCode Assembly
                  NextParameter NextOpCode NextAssembly ActOfCounting Metaphor

class PHYSICAL
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
      where
  invariant: Invariant
  threshold: TOKEN Invariant
  carrier: Carrier

  -- This compiles one bit at a time.
  slip? : TOKEN Invariant → REFINE (TOKEN Invariant) → BOOL Bool :=
    fun s t => if counting.admissible? s t = TRUTH then TRUTH else __SILENCE__


inductive History
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
