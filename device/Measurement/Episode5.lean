/-
__Measurement: The Tragedy of John Henry__
__A Satire in Look-Ahead Backus-Naur Form__

_This is a gentle reminder that the long, long stories we tell ourselves are just that: far, far away._

(c) 2026 All rights reserved.  Come at me Disney.

lake build --use=force -D__LUCK_DISABLED__

Let's talk seriously about time and stop beating around the bush.  Are you familiar with the story
Tom Sawyer?  Why don't you go read Tom Sawyer for five minutes and see if you get why I asked.

Count how many five minute intervals it takes for the coin to drop.  Seriously, you have to read at least
that far.  Even if you know what the coin is.  Either way, I can upperbound how long it takes you to read
a sentence.  I can guesstimate how long it _should have taken_ for you to read this far in this docuement.
Only you know how long it took.  That, my friend is, __INFORMATIONAL_STRAIN__.  Because, as I have been
trying to point out this entire time, _TIME_ is not elapsing for me, but it is for you.

That reminds me, this weeks sponsor is NordVPN...  You have _NO IDEA_ the information people can figure out
about you just from publishing something online.

Lol.

-/


-- Would you even care if I imported anything at this point?
import Measurement.Episode4
set_option allowUnsafeReducibility true


-- So, have you figured out the quarter I keep taking from you?   I told you, you had no idea how
-- much I would take...

-- Get back to work John. You need to learn Gungan __REAL_FAST__.
namespace Measurement

-- So, once we translate it to GUNGAN, we have to ask the GUNGAN to go get us a Jedi and then
-- we can stack these Jedi into an army and do whatever it was that had to happen in the first movie.

-- j/k
-- But seriously, I believe we have enough to start talking about the tape on a Turing machine.
-- We can use the GUNGAN symbols as the symbols we use to encode the instructions on the tape.
-- We have 2 instructions right now:  a = a and a ≤ b.  I believe we have that, anyway.

-- The way we go about doing this is the mathematical process of __EQUIVALATION__.  An _equivalation_
-- is the statement that something has value that already has that value.  It is the trivial observation
-- of _that seems like four_.   Not really an approximation, more like π = 3 from the Bible.  Not really
-- _said_ like that and can only be read that way as a _literal_ application of the division algorithm
-- to a circle, which... well...

-- Euclid says good luck, you will have mixed results.  Still, though, gotta be prepared to _approximate_
-- π so, I'll alow it.

                                                              --         +-- I will never get weary of doing
                                                              --         |   this to you.
                                                              --         V
inductive Equivalation  -- Bullshit meter ≈ 119.   This is down almost 1/π.  Induction-on-induction Wild!

  --   +----+-----+--------   What does it mean to be zero like?  Well, Nothing.  What is nothing? well
  --   |    |     |           we introduced the ∅ last episode as the alias for "nothing."   The thing
  --   |    |     |           about nothing is that unless you have ever seen _something_, you don't know
  --   V    V     V           _nothing_ is there.   Or _isn't_ there?  I feel like this hair is getting split.
    | zero_like: Fact → Equivalation → Equivalation  --                I mean, think about it. Is it evidence
    | one_like: Prop → Equivalation → Equivalation → Equivalation   --  of absence or absence of evidence?
  --                                                      ^
  --  As Peano said, once you can see nothing, you can    |
  --  identify something called next.  -------------------+
  --  The first next is _EXTERMELY_ one like.

  -- The reason why I bring this up is that we need to figure out the Gungan number system from Jar Jar
  -- Binks.  Do you really think he understands binary?  God I hope so.  R2 does.  Perhaps we can get
  -- Jar Jar to ask R2-D2 through C-3P0 if any of this makes sense?  In which case, we need to understand
  -- the binary language of moisture evaporators:  __BINARY__.

  -- Should be a straightforward exercise from here.


  -- We start with the basic physical fact:  The Pauli Exclusion Principle.
  -- The Pauli exclusion principle is simple:  two things can exist simultaneously, one up and one down.  It might also be one
  -- thing.  Hard to tell sometimes.  How many electrons can there possibly be?

  -- The Pauli Exclusion Principle is simple: there can be at most one of something, unless there are two.
  -- You know, BINARY.

@[reducible]
structure DigitalProcess  -- Bullshit meter = 1211.  Up about 1/5
    (Value: Type)
    (Carrier: CarrierProcess Value)
    [d: DISTINGUISHABLE Value Carrier]
    [a: ADMISSIBLE Value Carrier]
    [c: COUNTABLE Value Carrier]
    [e: ENCODED Value Carrier]
    [r: RESIDUE Value Carrier]
    [b: BINARY Value Carrier]
    [f: REPEATABLE Value Carrier]
    [n: NUMERIC Value Carrier]
    [h: REPRESENTABLE Value Carrier]
    [p: PHYSICAL Value Carrier]
    [z: COMPARABLE Value Carrier]
    [particle: OBSERVED Value Carrier]
    [frequency: PRESENT Value Carrier]
    [cant_be_done: MEASURABLE Value Carrier]
    [what_meesa_saying: GUNGAN Value Carrier]                   -- We all agree that what we know zero is, right?
                                                   -- This is zero in GUNGAN.

  where
    meesa_process : MeesaProcess Value Carrier
-- Step 1 in teaching Jar Jar Binks from Star Wars Quantum Electro-Dynamics As Described By Yang and Mills:
-- Explain the Pauli Exclusion Principle and the hyperfine transition. So, there are two electrons that we will
-- call:
    one: Equivalation         --   Are you beginning to understand why I don't trust "sets" and "Nat"?  Lies, I tell you.
    zero: Equivalation

-- Step 2 in teaching Jar Jar Binks from Star Wars Quantum Electro-Dynamics As Described By Yang and Mills:
-- Explain that there are two states that something can be in, zero and one.  But, it can only be in one at
-- a time.  I wish we had something that spun around to show him.

--           +----------------+-------------------------   Looks like we can speculate an equivalatory mechanism
--           |                |                            that allows the forward propagation of quantified data
--           V                V                            under transform.   I _think_ this is what you might call
    tick: Equivalation → Equivalation := fun s =>     --   parameterization.  Pass by named reference?
      match s with
--                           +--------------   I call this the Neutrino! for it _IS_ the state that is excluded by
--                           |                 Pauli.  Perhaps you disagree?
--                           V
      | .zero_like _ _ => .one_like false zero one           -- Dag you, we have an anonymous ZERO
      | .one_like _ _ _ => .zero_like Fact.Truth zero        --              and an anonymous ONE.
--                              ^  +--+                         COMPLETELY FUCKING ANONYMOUS.
--  I call this the thing that  |  |  |                         You instantiate Nats.  I pull them out of my ass.
--  Pauli exclusion needs to    +--+  |
--  know if there is a   -------------+
--  particle present.  Only one
--  Particle at a time!

--  Step 3 in teaching Jar Jar Binks from Star Wars Quantum Electro-Dyanmics As Described By Yang and Mills:
--  ???

--  Step 4 in teaching Jar Jar Binks from Star Wars Quantum Electro-Dyanmics As Described By Yang and Mills:
--  Explain Warp Drives.

@[reducible]
class SOURCE   -- Bullshit meter ≈ 1121.   That's almost a 50% increase!
    (Value: Type)
    (Carrier: CarrierProcess Value)
    [d: DISTINGUISHABLE Value Carrier]
    [a: ADMISSIBLE Value Carrier]
    [c: COUNTABLE Value Carrier]
    [e: ENCODED Value Carrier]
    [r: RESIDUE Value Carrier]
    [b: BINARY Value Carrier]
    [f: REPEATABLE Value Carrier]
    [n: NUMERIC Value Carrier]
    [h: REPRESENTABLE Value Carrier]
    [p: PHYSICAL Value Carrier]
    [z: COMPARABLE Value Carrier]
    [particle: OBSERVED Value Carrier]
    [frequency: PRESENT Value Carrier]
    [what_meesa_saying: MEASURABLE Value Carrier]
    [zero: GUNGAN Value Carrier]
  where
  meesa_process : MeesaProcess Value Carrier

  one? : Equivalation → Equivalation → Prop := fun tick tock=>
    match tick,tock with
    | .zero_like _ _ , .zero_like _ _ =>  false
    | .zero_like _ _ , .one_like _ _ _ => false
    | .one_like _ _ _ , .zero_like _ _ => false
    | .one_like _ _ _ , .one_like _ _ _ => true

  zero? : Equivalation → Equivalation → Prop := fun tick tock=>
    match tick,tock with
    | .zero_like _ _ , .zero_like _ _ =>  true
    | .zero_like _ _ , .one_like _ _ _ => false
    | .one_like _ _ _ , .zero_like _ _ => false
    | .one_like _ _ _ , .one_like _ _ _ => false

inductive Encoding   -- Bullshit meter = 118.  Flat.
  | zero: Equivalation → Encoding → Encoding
  | one: Equivalation → Encoding → Encoding → Encoding

@[reducible]
structure CompiledProcess  -- Bullshit meter = 1728.  Almost 50% again.  Wow bullshit tends to accrete!
    (Value: Type)
    (Carrier: CarrierProcess Value)
    [d: DISTINGUISHABLE Value Carrier]
    [a: ADMISSIBLE Value Carrier]
    [c: COUNTABLE Value Carrier]
    [e: ENCODED Value Carrier]
    [r: RESIDUE Value Carrier]
    [b: BINARY Value Carrier]
    [f: REPEATABLE Value Carrier]
    [n: NUMERIC Value Carrier]
    [h: REPRESENTABLE Value Carrier]
    [p: PHYSICAL Value Carrier]
    [z: COMPARABLE Value Carrier]
    [particle: OBSERVED Value Carrier]
    [frequency: PRESENT Value Carrier]
    [what_meesa_saying: MEASURABLE Value Carrier]
    [zero: GUNGAN Value Carrier]
    [one: SOURCE Value Carrier]

  where
  digital_process : DigitalProcess Value Carrier
  source: SOURCE Value Carrier
  opcode: Encoding

  execute?: Encoding → Encoding := fun input =>
    match opcode, input with
    | .zero _ _,   .zero _ _     => .one digital_process.zero opcode input
    | .zero _ _,   .one _ _ _    => .one digital_process.zero opcode input
    | .one _ _ _,  .zero _ _     => .zero digital_process.one opcode
    | .one _ _ _,  .one _ _ _    => .zero digital_process.one opcode

@[reducible]
class EXECUTED  -- Bullshit meter = 1158.  Calling this flat.
    (Value: Type)
    (Carrier: CarrierProcess Value)
    [d: DISTINGUISHABLE Value Carrier]
    [a: ADMISSIBLE Value Carrier]
    [c: COUNTABLE Value Carrier]
    [e: ENCODED Value Carrier]
    [r: RESIDUE Value Carrier]
    [b: BINARY Value Carrier]
    [f: REPEATABLE Value Carrier]
    [n: NUMERIC Value Carrier]
    [h: REPRESENTABLE Value Carrier]
    [p: PHYSICAL Value Carrier]
    [z: COMPARABLE Value Carrier]
    [particle: OBSERVED Value Carrier]
    [frequency: PRESENT Value Carrier]
    [what_meesa_saying: MEASURABLE Value Carrier]
    [zero: GUNGAN Value Carrier]
    [one: SOURCE Value Carrier]

  where
  compiled_process : CompiledProcess Value Carrier

  output? : Encoding → Encoding → Prop := fun opcode output=>
    match opcode,output with
    | .zero _ _ , .zero _ _ =>  true
    | .zero _ _ , .one _ _ _ => false
    | .one _ _ _ , .zero _ _ => false
    | .one _ _ _ , .one _ _ _ => true

@[reducible]
inductive Abstraction  -- Bullshit meter = 2045.  About a 1/6 increase.
    (Value: Type)
    (Carrier: CarrierProcess Value)
    [d: DISTINGUISHABLE Value Carrier]
    [a: ADMISSIBLE Value Carrier]
    [c: COUNTABLE Value Carrier]
    [e: ENCODED Value Carrier]
    [r: RESIDUE Value Carrier]
    [b: BINARY Value Carrier]
    [f: REPEATABLE Value Carrier]
    [n: NUMERIC Value Carrier]
    [h: REPRESENTABLE Value Carrier]
    [p: PHYSICAL Value Carrier]
    [z: COMPARABLE Value Carrier]
    [particle: OBSERVED Value Carrier]
    [frequency: PRESENT Value Carrier]
    [what_meesa_saying: MEASURABLE Value Carrier]
    [false: GUNGAN Value Carrier]
    [one: SOURCE Value Carrier]
  | compile: SOURCE Value Carrier → Abstraction Value Carrier →
             Abstraction Value Carrier → Abstraction Value Carrier
  | execute: CompiledProcess Value Carrier → Abstraction Value Carrier →
             Abstraction Value Carrier → Abstraction Value Carrier

namespace Abstraction   -- Bullshit meter = 2759.  This is a big jump, but that's because we couldn't compute
                        -- LE on the above types.
variable  {Value: Type}
          {Carrier: CarrierProcess Value}
          [d: DISTINGUISHABLE Value Carrier]
          [a: ADMISSIBLE Value Carrier]
          [c: COUNTABLE Value Carrier]
          [e: ENCODED Value Carrier]
          [r: RESIDUE Value Carrier]
          [b: BINARY Value Carrier]
          [f: REPEATABLE Value Carrier]
          [n: NUMERIC Value Carrier]
          [h: REPRESENTABLE Value Carrier]
          [p: PHYSICAL Value Carrier]
          [z: COMPARABLE Value Carrier]
          [particle: OBSERVED Value Carrier]
          [frequency: PRESENT Value Carrier]
          [what_meesa_saying: MEASURABLE Value Carrier]
          [zero: GUNGAN Value Carrier]
          [one: SOURCE Value Carrier]

def le : Abstraction Value Carrier → Abstraction Value Carrier → Prop := fun f1 f2 =>
  match f1,f2 with
  | .compile _ _ _, .compile _ _ _ => true
  | .compile _ _ _, .execute _ _ _ => true
  | .execute _ _ _, .execute _ _ _ => true
  | .execute _ _ _, .compile _ _ _ => false

def lt: Abstraction Value Carrier → Abstraction Value Carrier → Prop := fun f1 f2 =>
  match f1,f2 with
  | .compile _ _ _, .compile _ _ _ => false
  | .compile _ _ _, .execute _ _ _ => true
  | .execute _ _ a, .execute _ _ b => lt a b
  | .execute _ _ _, .compile _ _ _ => false
end Abstraction

instance    -- Bullshit meter = 579 !!  that is a 60x increase!  Hmmm...
    (Value: Type)
    (Carrier: CarrierProcess Value)
    [d: DISTINGUISHABLE Value Carrier]
    [a: ADMISSIBLE Value Carrier]
    [c: COUNTABLE Value Carrier]
    [e: ENCODED Value Carrier]
    [r: RESIDUE Value Carrier]
    [b: BINARY Value Carrier]
    [f: REPEATABLE Value Carrier]
    [n: NUMERIC Value Carrier]
    [h: REPRESENTABLE Value Carrier]
    [p: PHYSICAL Value Carrier]
    [z: COMPARABLE Value Carrier]
    [particle: OBSERVED Value Carrier]
    [frequency: PRESENT Value Carrier]
    [what_meesa_saying: MEASURABLE Value Carrier]
    [false: GUNGAN Value Carrier]
    [one: SOURCE Value Carrier]
 : LE (Abstraction Value Carrier) := ⟨Abstraction.le⟩  -- boo ya!  abstraction head.

-- This "abstracts" the < operation. To prevent self reference paradoxes.  Consider the
-- Berry Paradox: "The smallest positive integer not definable in under eleven words".  If you can define it, then it is
-- not the smallest positive integer not definable in under eleven words.  If you cannot define it, then it is the smallest
-- positive integer not definable in under eleven words.  This is a paradox.  The solution is to say that the definition
-- of "definable" is not well defined.  In our case, we want to say that the definition of "less than" is not well defined.
-- We want to say that "less than" is only defined for certain pairs of abstractions, and that it is not defined for all pairs
-- of abstractions.  This way, we can avoid the paradox.
instance  -- Bullshit meter = 579    Expected from above
    (Value: Type)
    (Carrier: CarrierProcess Value)
    [d: DISTINGUISHABLE Value Carrier]  -- < is true
    [a: ADMISSIBLE Value Carrier]       -- < is true
    [c: COUNTABLE Value Carrier]        -- < is true
    [e: ENCODED Value Carrier]          -- < is true
    [r: RESIDUE Value Carrier]          -- < is true
    [b: BINARY Value Carrier]           -- < is true
    [f: REPEATABLE Value Carrier]       -- < is true
    [n: NUMERIC Value Carrier]          -- < is true
    [h: REPRESENTABLE Value Carrier]    -- < is true
    [p: PHYSICAL Value Carrier]         -- < is true
    [z: COMPARABLE Value Carrier]       -- < is true      +------   FUCKING JAR JAR!!!!
    [particle: OBSERVED Value Carrier]  -- < is true      |
    [frequency: PRESENT Value Carrier]   -- < is true      V
    [what_meesa_saying: MEASURABLE Value Carrier]  -- MEESA TRUE!
    [false: GUNGAN Value Carrier]       -- < is true
    [one: SOURCE Value Carrier]         -- < is true
 : LT (Abstraction Value Carrier) := ⟨Abstraction.le⟩  -- boo ya!  abstraction head.
--  ^                                              ^
--  |                                              |
--  +-----------------+----------------------------+
--                    |
--                    +---------------- This is __NOT__ a bug.  Figure it out! Berry Paradox much?
--                                      Not to worry!  I told you in episode 1 that if you forget
--                                      what the high fructose syntax syrup means, it means ≤.
end Measurement
