/-
Measurement
Chapter 2:
-/

namespace Measurement
universe i

structure Fact where
  truth : Prop
  decTruth : Decidable truth

namespace Fact
def Truth : Prop := True
end Fact


-- Big Endian Binary number with LE ordering.
inductive Number where
  | zero : Number
  | succ : Fact → Number → Number

namespace Number
def le : Number → Number → Prop
  | .zero, _ => True
  | .succ _ _, .zero => False
  | .succ p1 n1', .succ p2 n2' =>
      match p1.decTruth, p2.decTruth with
      | isTrue _,  isTrue _  => le n1' n2'
      | isTrue _,  isFalse _ => False
      | isFalse _, isTrue _  => True
      | isFalse _, isFalse _ => le n1' n2'
end Number

-- And the notation to match.
instance : LE Number where
  le := Number.le

structure Carrier
    (carrier: Fact)
  where
  present? : Option Number → Prop := fun s =>
    match s with
    | none      => False
    | some f  => match f with
      | .zero => carrier.truth
      | .succ p _ => p.truth


class DISTINGUISHABLE
    (Carrier: Number)
    (Label: Type 1)
    [DecidableEq Label]
    where

  different? : Label → Label → Prop :=
    fun s1 s2 => s1 ≠ s2
  distinct? : Label → Prop :=
    fun s => ∃ c : Label, different? s c
  dec_distinct : DecidablePred distinct?

inductive Glyphs
  (Value: Number)
  (Label: Type 1)
  [DecidableEq Label]
  [number: DISTINGUISHABLE Value Label]
  where
  | nil : Glyphs Value Label
  | cons : DISTINGUISHABLE Value Label  →
           Glyphs Value Label →
           Glyphs Value Label


structure Variable
    (Value: Number)
    (NaturalNumber: Type 1)
    [DecidableEq NaturalNumber]
    [DISTINGUISHABLE Value NaturalNumber]
    (Label: Type 1)
    [DecidableEq Label]
    [DISTINGUISHABLE Value Label]
    (Name: Glyphs Value Label)
    [DecidableEq Number]
  where
  value: Number
  label: Glyphs Value Label
  number: Type 1
  name: Type 1
  decValue : DecidableEq Number
  leValue: DecidableLE Number


class ADMISSIBLE
  (Signal: Number)
  (Response: Type 1)
  [DecidableEq Response]
  [DISTINGUISHABLE Signal Response]
  where

  admissible? : Response → Prop := fun s =>
    ∃ h : Measurement Signal Response, h = Carrier ∧
      match h with
      | .nil => False
      | .cons d _ => d.distinct? s


inductive Mapping
  (Signal: Number)
  (Response: Type 1)
  [DecidableEq Response]
  [DISTINGUISHABLE Signal Response]
  [ADMISSIBLE Signal Response]
  where
  | nil : Mapping Signal Response
  | cons : DISTINGUISHABLE Signal Response →
           Mapping Signal Response →
           Mapping Signal Response


structure PartialOrdering
  (Value: Number)
  (Precision: Type 1)
  [DecidableEq Precision]
  [DISTINGUISHABLE Value Precision]
  [ADMISSIBLE Value Precision]
  (history: Mapping Value Precision)
  (α: Type 1)
  (β: Type 1)
  [DecidableEq α]
  [DecidableEq β]
  where
  le? : Option (Type 1) → Option (Type 1) → Prop := fun a b =>
    match a, b with
    | none, none => True
    | none, some _ => False
    | some (t1, φ1), none => False
    | some (t2, φ2), some (t3, φ3) => t2 ≤ t3


inductive Ordering
  (Observation: Invariant)
  (Label: Type 1)
  (Value: Type 1)
  [DecidableEq Label]
  [DISTINGUISHABLE Observation.Carrier. Label]
  [ADMISSIBLE Observation Label Value]
  where
  | nil : Ledger Observation Label Value
  | cons : Event →
           Symbol →
           Ledger Observation Label Value →
           Ledger Observation Label Value







structure Event where
  Carrier: Symbol
  Value: Number
  Invariant: Measurement Carrier Symbol


inductive Counting
  (Observation: Invariant)
  (Label: Type 1)
  (Value: Type 1)
  [DecidableEq Label]
  [DISTINGUISHABLE Observation Label]
  [ADMISSIBLE Observation Label Value]
  where
  | nil : Counting Observation Label Value
  | cons : Event →
           Symbol →
           Counting Observation Label Value →
           Counting Observation Label Value



class COUNTABLE
    (Observation: Invariant)
    (Label: Type 1)
    (Value: Type 1)
    where
  zero : Symbol
  observe : Event → Prop
  tick : Prop → Event → Symbol




/- STOP HERE--------------------------------------------------------
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
abbrev SYMBOL (_: Type 1) := REFINE (TOKEN Type)

structure Event where
  invariant: Type
  label: Type 1
  value: Type 1
  decomposition: Type 1

  slip? : Option Type -> BOOL Bool := fun s => match s with
    | none => __SILENCE__
    | some _ => TRUTH




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

structure Representative (Invariant Symbol Value : Type i) where
  source : Invariant
  symbol : Symbol
  value  : Value

class COUNTABLE
    (Invariant Symbol Value : Type) where
  zero    : TOKEN Symbol
  observe : Representative Invariant Symbol Value → BOOL Bool
  tick    : BOOL Bool → EVENT (OBSERVE Symbol) → OBSERVE Symbol

inductive Enumeration
    (Invariant Symbol Value : Type i) : Type i where
  | nil  : Enumeration Invariant Symbol Value
  | cons :
      Representative Invariant Symbol Value →
      Enumeration Invariant Symbol Value →
      Enumeration Invariant Symbol Value

namespace COUNTABLE

variable {Invariant Symbol Value : Type i}
         [c : COUNTABLE Invariant Symbol Value]

def Count :
    Enumeration Invariant Symbol Value → OBSERVE Symbol
  | .nil       => c.zero
  | .cons r xs => c.tick (c.observe r) (Count xs)

end COUNTABLE



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

structure Representative (Invariant Symbol Value : Type i) where
  source  : Invariant
  symbol  : Symbol
  value   : Value


inductive Enumeration
    (Symbol: COUNTABLE Representative)
  | nil

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

abbrev CORRELATED (Symbol_1: Type) (Symbol_2: Type) := (Symbol_1×Symbol_2)

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

  metaphysial_relation: RELATED Symbol Symbol
  physical_relation   : RELATED (TOKEN Symbol) (TOKEN Symbol)
  precedes? : TOKEN Invariant → EVENT Value → BOOL Bool := Metaphor

  le? : TOKEN Symbol → EVENT Token → BOOL Bool := Metafive

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

class METAPHYSICAL
    (Characteristic   : Type → TOKEN Type)
    (Invariant        : Type)
    (Carrier          : Type)
    (Value            : Type 1)
    (Token            : Type 1)
    (Admissible       : Prop)

    -- A number has 2 metaphysical properties: a count of individuals and the number of individuals with like characteristics.
    (Number           : TOKEN Invariant)
    (Count            : TOKEN Carrier)

    -- A number as 1 physical property:  You can see it on a page and recognize it as a symbol.
    (Symbol           : OBSERVED (TOKEN Carrier))
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
    [e1: ADMISSIBLE Symbol Token fun _ t => ADMISSIBLE.admissible? Metaphor Number t]
    [e2: ADMISSIBLE Symbol Token Metafive]
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
  present?: OBSERVE Invariant
  compiled_symbol: Representative
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

/--
  NOISY represents the state where an observation exists,
  but the refinement into a stable Invariant is corrupted or ambiguous.
-/
class NOISY
    (Characteristic   : Type → TOKEN Type)
    (Invariant        : Type i)
    (Symbol           : Type i)
    (Value            : Type (i+1))
    (Token            : Type (i+1))
    (Representative   : Prop)
    where
  -- Numerical and Ordinal representations of tokens
  Number  : TOKEN Invariant
  Ordinal : TOKEN Symbol

  -- Using your defined BOOL and TRUTH [cite: 17, 18]
  Truth   : BOOL Bool := some true

  -- Metaphor and Metafive maps: Using OBSERVE for EVENT as per turn-based logic [cite: 13]
  Metaphor : TOKEN Invariant → OBSERVE Value → BOOL Bool
  Metafive : TOKEN Symbol → OBSERVE Token → BOOL Bool

  -- Class fields
  entropy : Symbol
  strain  : Value
  value   : TOKEN Invariant
  number  : TOKEN Symbol

inductive Channel
    (Characteristic   : Type → TOKEN Type)
    (Invariant        : Type i)
    (Symbol           : Type i)
    (Value            : Type (i+1))
    (Token            : Type (i+1))
    (Representative   : Prop)
    [NOISY Characteristic Invariant Symbol Value Token Representative]
    where
  | nil : REFINE (TOKEN Invariant) →
          Channel Characteristic Invariant Symbol Value Token Representative
  | cons: REFINED Invariant →
          REFINE (TOKEN Invariant) →  -- Read next bit/byte/word/paragraph/etc.
          Channel Characteristic Invariant Symbol Value Token Representative →
          Channel Characteristic Invariant Symbol Value Token Representative

class PHYSICAL
    (Characteristic   : Type → TOKEN Type)
    (Invariant        : Type i)
    (Symbol           : Type i)
    (Value            : Type (i+1))
    (Token            : Type (i+1))
    (Representative   : Prop)
    [noise: NOISY Characteristic Invariant Symbol Value Token Representative]

    where
  -- The channel through which records are produced by an instrument
  channel : Channel Characteristic Invariant Symbol Value Token Representative

  -- The physical manifestation of entropy within the measurement
  entropy_witness : Symbol := noise.entropy
  strain_witness  : Value  := noise.strain

  -- Constraints on the ActOfCounting
  count_invariant : TOKEN Invariant := noise.value
  count_symbol    : TOKEN Symbol    := noise.number

inductive Domain
    (Characteristic   : Type → TOKEN Type)
    (Invariant        : Type i)
    (Symbol           : Type i)
    (Value            : Type (i+1))
    (Token            : Type (i+1))
    (Representative   : Prop)
    [noise: NOISY Characteristic Invariant Symbol Value Token Representative]

end Measurement
