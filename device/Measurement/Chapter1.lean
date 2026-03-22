/-
Measurement/Chapter1.lean

CODA:  Welcome the the TuringDevice that explicitly describes
the computations necessary for the simultaneous decomposition
and evaluation of a real valued function.

As promised, we beign at the beginning and rely on the state
transform mechanisms of Lean as an example of a discrete universal
Turing machine.  The following is an arbitrary encoding, so be
on the lookout for Godel. I would consider this some "arbitrary
encoding."


-- There are NO IMPORTS.

-/


namespace Measurement

/- there is only one universe.  that universe has
a current state.  that current state is at time _i_,
our first symbol-/
universe i

/- This is the act of seeing something happen. We assume
it takes time and space to build a device that observe and the thing
being observed also must take up time and space. If you find
this assumption too WOKE, tell it to Planck, Heisenberg, Dirac, etc.
You don't know the future until you yank off that Option.
-/
abbrev OBSERVE (x : Type i) := Option (ULift.{i+1,i} x)
-- If you have seen it, then you can look directly at the symbol of the result.
abbrev OBSERVED (x: Type i) := ULift.{i+1,i} x
-- A different symbol is probably some other symbol, we will
-- prove that in a bit.
abbrev DIFFERENT (Invariant : Type i) := Option Invariant


-- At the end of the day, a type is a symbol that can be assigned a name and value.
-- This sounds liks counting, to me.  Let's exploit this structure.
abbrev SYMBOL := Type


-- A TOKEN Invariant is one that the compiler can recognize as being
-- distinct from all other symbols.
abbrev TOKEN (Invariant : Type) := DIFFERENT Invariant

-- We can talk about something being on and off. We call that token
abbrev BOOL (Invariant :Type) := TOKEN Invariant
-- BOOL.  See how we are making the process of making TOKENS?
-- Would you like to see the only primitive TOKEN?

-- Verified silence. This is the only thing we can know for sure,
-- nothing has been verified and so we can TOKENIZE that concept as
def _______________FALSE_______________ {Invariant: Type} : (TOKEN Invariant) := none
-- We define FALSE to be the symbol that represents unrepresentable symbols.
-- This is a DISTINCT Invariant, although it will never be observed as such.
-- I made it REALLY distinct so you do NOT miss it.
--
-- There is only one ball, keep your eye on it.
-- Like and Subscribe if you think I should make the ball bigger or smaller.



/- --------------------------------------------------------
DISTINGUISHABLE.

Something is DISTINGUISHABLE from others if there exists
some characteristic that is either present or absent from
the something relative to the others.
-/
class DISTINGUISHABLE
    (Characterisitic : Type → DIFFERENT (Type))
    (Invariant: Type)
    [DecidableEq Invariant]
    where

  -- The universe only exists as a type.
  -- Any higher type is metaphysical and belongs to
  -- the compiling engine, not the proof.
  -- Or does it?
  æther               : Type

  different? : Invariant → Invariant → Prop :=
    fun s1 s2 => s1 ≠ s2
  distinguished? : Invariant → Prop :=
    fun s => ∃ c : Invariant, different? s c
  dec_distinguished : DecidablePred distinguished?

namespace DISTINGUISHABLE
variable {Characterisitic : Type → DIFFERENT (Type)}
         {Invariant: Type}
         [DecidableEq Invariant]
         [d: DISTINGUISHABLE Characterisitic Invariant]

def different
    (s1 s2 : Invariant) : Prop :=
  d.different? s1 s2

def distinguished
    (s : Invariant) : Prop :=
  d.distinguished? s

def encode
    (symbol: Invariant)
    (compiler_type : Type)
      : DIFFERENT (Type) :=
  if (d.dec_distinguished symbol).decide then some compiler_type else none

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

abbrev EVENT (_: Type 1) := OBSERVE (DIFFERENT Type)

class ADMISSIBLE
    (Event: EVENT Type)
    (ChangeInCircumstance : Type 1 → OBSERVED (Type 1))
    (Invariant: Type)
    (Description: Type → OBSERVED (Type))

     -- Notice the metaphor is starting to work on abstract types.
     -- It is _metaphysical_.
    (Metaphor: DIFFERENT Invariant → OBSERVE (DIFFERENT Invariant)  → BOOL Bool)
    where

  -- Is this a possible future state of the universe? Dunno, could be.
  admissible? : DIFFERENT Invariant → OBSERVE (DIFFERENT Invariant) → BOOL Bool := Metaphor

  -- Michelson and Morley disallowed the æther as a possible thing that could be
  -- distinguished. The æther is the absence of any symbol, so it cannot be distinguished
  -- from itself.
  aether_inadmissible :
    ∀ obs : OBSERVE (DIFFERENT Invariant), admissible? none obs = none

namespace ADMISSIBLE
variable {Event: EVENT Type}
         {ChangeInCircumstance : Type 1 → OBSERVED (Type 1)}
         {Description : Type → OBSERVED (Type)}
         {Invariant      : Type}
         {Metaphor    : DIFFERENT Invariant → OBSERVE (DIFFERENT Invariant) → BOOL Bool}
         [a : ADMISSIBLE Event ChangeInCircumstance
                         Invariant Description
                         Metaphor]

def admissible
    (s   : DIFFERENT Invariant)
    (obs : OBSERVE (DIFFERENT Invariant))
      : BOOL Bool :=
  a.admissible? s obs

end ADMISSIBLE


class COUNTABLE
    -- Physical Traits of counting
    (Characteristic   : Type → DIFFERENT Type)
    (Invariant        : Type)

    -- Metaphysical traits of a number: (One, 1) and its representation
    -- on the page
    (Name             : Type i)       -- Metaphysical trait across all time
    (Value            : Type 1)       -- The metaphysical value right now
    (Representation   : Invariant)    -- The decomposition to interpret a number as a value


    -- When we count, we have to bump everything
    -- except the Name.  That is the invariant of counting.
    (NextName            :  Type i → OBSERVED (Type i))
    (NextValue           :  Type 1 → OBSERVED (Type 1))
    (NextRepresentation  :  Type   → OBSERVED  Type   )


    -- A description of the counting process.
    (ActOfCounting : EVENT Type)
    (Metaphor: DIFFERENT Invariant → OBSERVE (DIFFERENT Invariant)  → BOOL Bool)


    -- Things that must be true in order for counting to be possible.
    [value_equality : DecidableEq (Value)]
    [invariant_equality : DecidableEq (Invariant)]
    [name_equality : DecidableEq (Name)]


    -- Right now, we only care that the value is distinguishable
    -- and the next value is admissible. This allows words like
    -- "twenty or so" as a loose description of a size.
    [DISTINGUISHABLE Characteristic Invariant]
    [ADMISSIBLE ActOfCounting
                NextValue Invariant
                NextRepresentation Metaphor]
    where

  next_name? : Type i → OBSERVED (Type i) := NextName
  next_value? : Type 1 → OBSERVED (Type 1) := NextValue
  next_representation? : Type → OBSERVED Type := NextRepresentation


  -- The notion of the origin does not change.  This is the root of
  -- a _frame of reference_.  This is the thing that has 0 velocity and
  -- 0 value.  We count this guy.  Just like Peano.
  origin: Invariant

namespace COUNTABLE
variable  {Characteristic: Type → DIFFERENT Type}
          {Invariant: Type}
          {Name: Type i}
          {Value: Type 1}
          {Representation: Invariant}
          {NextName: Type i → OBSERVED (Type i)}
          {NextValue: Type 1 → OBSERVED (Type 1)}
          {NextRepresentation: Type → OBSERVED Type}
          {ActOfCounting: EVENT Type}
          {Metaphor: DIFFERENT Invariant → OBSERVE (DIFFERENT Invariant) → BOOL Bool}
          [value_equality : DecidableEq (Value)]
          [invariant_equality : DecidableEq (Invariant)]
          [name_equality : DecidableEq (Name)]
          [DISTINGUISHABLE Characteristic Invariant]
          [ADMISSIBLE ActOfCounting
                      NextValue Invariant
                      NextRepresentation Metaphor]
          [c : COUNTABLE Characteristic Invariant
                         Name Value Representation
                         NextName NextValue NextRepresentation
                         ActOfCounting Metaphor]

def next_name
    (n : Type i)
      : OBSERVED (Type i) :=
  c.next_name? n

def next_value
    (v : Type 1)
      : OBSERVED (Type 1) :=
  c.next_value? v

def next_representation
    (r : Type)
      : OBSERVED Type :=
  c.next_representation? r

end COUNTABLE


inductive Iteration
    (Characteristic   : Type → DIFFERENT Type)
    (Invariant        : Type)
    (Name             : Type i)       -- Metaphysical trait across all time
    (Value            : Type 1)       -- The metaphysical value right now
    (Representation   : Invariant)    -- The decomposition to interpret a number as a value
    (NextName            :  Type i → OBSERVED (Type i))
    (NextValue           :  Type 1 → OBSERVED (Type 1))
    (NextRepresentation  :  Type   → OBSERVED  Type   )
    (ActOfCounting : EVENT Type)
    (Metaphor: DIFFERENT Invariant → OBSERVE (DIFFERENT Invariant)  → BOOL Bool)
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

  | nil : OBSERVE (Invariant) →
                  Iteration Characteristic Invariant Name
                  Value Representation NextName NextValue NextRepresentation ActOfCounting Metaphor

  | cons : Invariant →
           OBSERVE (Invariant) →
           Iteration Characteristic Invariant Name
                    Value Representation NextName NextValue NextRepresentation ActOfCounting Metaphor →
           Iteration Characteristic Invariant Name
                    Value Representation NextName NextValue NextRepresentation ActOfCounting Metaphor

-- So we found a COMPILER invariant: an inductive Iteration.
-- A COUNTABLE Symbol of Type has to be named in order to compile
-- this iteration.
-- However, we do NOT want to instantiate that as that would confuse
-- the symbol for the fact.  We have no idea if it is a fact yet.
-- BUT.... the compiler HAS given us a carrier for invariant!
-- We have an indication that the compiler has distinguished as a symbol!
-- The CARRIER will tell us if the current symbol has been distinguished
-- by the compiler.
def CARRIER
    {Characteristic : Type → DIFFERENT Type}
    {Invariant : Type}
    [DecidableEq Invariant]
    [d : DISTINGUISHABLE Characteristic Invariant]
    (s : Invariant) : Prop :=
  d.distinguished? s
-- The root of the Invariant is the BOOL Bool.  Bool is a Prop. A
-- Prop can be named in the compiler.  So, we have a symbol that
-- names a symbol in the compiler that is never instantiated, only
-- probed and waited for.

class NUMERIC
    (Characteristic   : Type → DIFFERENT Type)
    (Invariant        : Type)
    (Carrier          : Prop)
    (Name             : Type i)       -- Metaphysical trait across all time
    (Value            : Type 1)       -- The metaphysical value right now
    (Representation   : Invariant)    -- The decomposition to interpret a number as a value
    (NextName            :  Type i → OBSERVED (Type i))
    (NextValue           :  Type 1 → OBSERVED (Type 1))
    (NextRepresentation  :  Type   → OBSERVED  Type   )
    (ActOfCounting : EVENT Type)
    (Metaphor: DIFFERENT Invariant → OBSERVE (DIFFERENT Invariant)  → BOOL Bool)
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
      where

  -- Could this be real life?
  -- Or is this just fantasy?
  variable_name: Invariant
  -- For those keeping score at home, variable_name can represent anything that you can count, including
  -- π, e, and √{-1}.  Although, the last one is exclusively Gaussian integers. We label that
  -- value by its name _variable name_.
  -- BTW, this label is _in the compiler_, not in the proof.  It is æther that cannot
  -- be distinguished --- yet.

  carrier: Carrier
  -- We can also ask the compiler if the current symbol has been distinguished.



class RELATABLE
    (Characteristic   : Type → DIFFERENT Type)
    (Invariant        : Type)
    (Event            : EVENT Type)
    (ChangeInCircumstance : Type 1 → OBSERVED (Type 1))
    (Description      : Type → OBSERVED Type)
    (Metaphor         : DIFFERENT Invariant → OBSERVE (DIFFERENT Invariant) → BOOL Bool)
    [DecidableEq Invariant]
    [DISTINGUISHABLE Characteristic Invariant]
    [a : ADMISSIBLE Event ChangeInCircumstance Invariant Description Metaphor]
    where

  rel : DIFFERENT Invariant → OBSERVED (DIFFERENT Invariant) → Prop :=
    fun s t => a.admissible? s t = some true

  dec_rel : DecidableRel rel




-- "We are putting a theorem prover in your theorem prover
-- so you can prove theorems about theorems while you prove
-- theorems about theorems about the world."
                            -- Willie Nelson

class REPRESENTATIVE
    (Characteristic   : Type → DIFFERENT Type)
    (Invariant        : Type)
    (Carrier          : Prop)
    (Name             : Type i)       -- Metaphysical trait across all time
    (Value            : Type 1)       -- The metaphysical value right now
    (Representation   : Invariant)    -- The decomposition to interpret a number as a value
    (NextName            :  Type i → OBSERVED (Type i))
    (NextValue           :  Type 1 → OBSERVED (Type 1))
    (NextRepresentation  :  Type   → OBSERVED  Type   )
    (ActOfCounting : EVENT Type)
    (Metaphor: DIFFERENT Invariant → OBSERVE (DIFFERENT Invariant)  → BOOL Bool)
    [value_equality : DecidableEq (Value)]
    [invariant_equality : DecidableEq (Invariant)]
    [name_equality : DecidableEq (Name)]
    [DISTINGUISHABLE Characteristic Invariant]
    [ADMISSIBLE ActOfCounting
                NextValue Invariant
                NextRepresentation Metaphor]
    [ZERO: COUNTABLE  Characteristic Invariant
                        Name Value Representation
                        NextName NextValue NextRepresentation
                        ActOfCounting Metaphor]
    [variable_name: NUMERIC Characteristic
                            Invariant Carrier
                            Name Value Representation
                            NextName NextValue NextRepresentation
                            ActOfCounting Metaphor]
      where

  ordinal: Invariant
  carrier: Carrier



class ENCODED
    (Characteristic   : Type → DIFFERENT Type)
    (Invariant        : Type)
    (Carrier          : Prop)
    (Name             : Type i)       -- Metaphysical trait across all time
    (Value            : Type 1)       -- The metaphysical value right now
    (Representation   : Invariant)    -- The decomposition to interpret a number as a value
    (NextName            :  Type i → OBSERVED (Type i))
    (NextValue           :  Type 1 → OBSERVED (Type 1))
    (NextRepresentation  :  Type   → OBSERVED  Type   )
    (ActOfCounting : EVENT Type)
    (Metaphor: DIFFERENT Invariant → OBSERVE (DIFFERENT Invariant)  → BOOL Bool)
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
    [carrier: NUMERIC Characteristic
                      Invariant Carrier
                      Name Value Representation
                      NextName NextValue NextRepresentation
                      ActOfCounting Metaphor]
      where
  encoding: Invariant
  carrier: Carrier




end Measurement
