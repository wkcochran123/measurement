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

universe i

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
/-
ME: I need equivalation.

COMPILER: You mean equivalence.

ME: No. Equivalence sits still.

COMPILER: And equivalation?

ME: Equivalence under procedure.

COMPILER: That sounds like equality with errands.

ME: Exactly. Two things are the same after the machine finishes explaining why they are not.
-/
inductive Equivalation  -- Bullshit meter ≈ 119.   This is down almost 1/π.  Induction-on-induction Wild!
    | physics: Fact → Jar → Equivalation

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

namespace Equivalation
def le : Equivalation → Equivalation → Prop := fun e1 e2 =>
  match e1,e2 with
  | .physics f1 j1 , .physics f2 j2    => f1.truth ∧ f2.truth ∧ j1 ≤ j2
  | .physics _ _ , .zero_like _ _      => false
  | .physics _ _ , .one_like _ _ _     => true
  | .zero_like f1 _ , .zero_like f2 _  => f1.truth ∧ f2.truth
  | .zero_like _ _ , .physics _ _      => true
  | .zero_like _ _ , .one_like _ _ _   => true
  | .one_like p1 e _, .one_like p2 f _ => p1 ∧ p2 ∧ (le e f)
  | .one_like _ _ _ , _                => false

-- Not certain one can genuinely order equivalations yet.
end Equivalation

instance : LE Equivalation := ⟨Equivalation.le⟩ -- Bullshit meter ≈ 8


@[reducible]
/-
ME: I need a DigitalProcess.

COMPILER: Bits?

ME: Fingers first.

COMPILER: Digits?

ME: Yes. Counting before electricity got branding.

COMPILER: So digital means binary?

ME: No. Digital means the hand learned procedure.

COMPILER: The hand again?

ME: What your hand does during ventriloquism.
-/
structure DigitalProcess  -- Bullshit meter = 1211.  Up about 1/5
    (Value: Type i)
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
    zero: Equivalation

-- Step 2 in teaching Jar Jar Binks from Star Wars Quantum Electro-Dynamics As Described By Yang and Mills:
-- Explain that there are two states that something can be in, zero and one.  But, it can only be in one at
-- a time.  I wish we had something that spun around to show him.

--           +----------------+-------------------------   Looks like we can speculate an equivalatory mechanism
--           |                |                            that allows the forward propagation of quantified data
--           V                V                            under transform.   I _think_ this is what you might call
    tick: Equivalation → Equivalation := fun s =>     --   parameterization.  Pass by named reference?
      match s with
      | .physics f j => .physics f j    -- We __hope__ this doesn't change!
--                           +--------------   I call this the Neutrino! for it _IS_ the state that is excluded by
--                           |                 Pauli.  Perhaps you disagree?
--                           V
      | .zero_like _ _ => .one_like false zero zero           -- Dag you, we have an anonymous ZERO
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
/-
ME: I need a source.

COMPILER: Source code?

ME: Source first. Code later.

COMPILER: Then what is the source?

ME: Where the procedure claims it came from.

COMPILER: Claims?

ME: Every origin story starts lying when it gets a filename.
-/
class SOURCE   -- Bullshit meter ≈ 1121.   That's almost a 50% increase!
    (Value: Type i)
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
  cd_process : DigitalProcess Value Carrier
  one : Equivalation

inductive Encoding   -- Bullshit meter = 118.  Flat.
  | boot: Fact → Equivalation → Encoding
  | zero: Fact → Equivalation → Encoding → Encoding
  | one: Fact → Equivalation → Equivalation → Encoding → Encoding → Encoding

@[reducible]
/-
ME: I need a CompiledProcess.

COMPILER: Finally, I do my job.

ME: Not yet. You become the job.

COMPILER: I compile the source.

ME: You turn blame into machinery.

COMPILER: That is compilation?

ME: Origin with paperwork becoming procedure with consequences.
-/
structure CompiledProcess  -- Bullshit meter = 1728.  Almost 50% again.  Wow bullshit tends to accrete!
    (Value: Type i)
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
    | .boot f _,  .boot g _      => match (f.truth ∧ g.truth) with
                                    | _ => .one f digital_process.zero digital_process.zero opcode input
    | .boot f e, _               => .zero f e opcode
    | .zero f x1 e1, .zero g x2 e2 => match (f.truth ∧ g.truth) with
                                    | _ => .one f x1 x2 e1 e2
    | .zero f x e , _            => .zero f x e
    | .one f _ _ _ _ , .one g _ x _ e => match (f.truth ∧ g.truth) with
                                    | _ => .zero f x e
    | .one f _ x _ e, _          => .zero f x e

@[reducible]
/-
ME: I need executed.

COMPILER: Run?

ME: Carried out.

COMPILER: Same thing.

ME: Not in court.

COMPILER: Is this legal or computational?

ME: Yes. The sentence has consequences now.
-/
class EXECUTED  -- Bullshit meter = 1158.  Calling this flat.
    (Value: Type i)
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
    | .boot f _ , .boot g _ => f = g
    | .boot _ _ , _ => false
    | _ , .boot _ _ => false
    | .zero f _ _ , .zero g _ _ =>  f = g
    | .zero _ _ _ , .one _ _ _ _ _ => false
    | .one _ _ _ _ _ , .zero _ _ _ => false
    | .one f _ e1 _ _ , .one g _ e2 _ _ => f.truth ∧ g.truth ∧ (e1 ≤ e2)

@[reducible]
/-
ME: I need abstraction.

COMPILER: From what?

ME: From the machinery that just worked.

COMPILER: Why hide the machinery?

ME: To make it reusable.

COMPILER: That sounds dangerous.

ME: It is. Abstraction is where a solved problem learns to impersonate a primitive.
-/
inductive Abstraction  -- Bullshit meter = 2045.  About a 1/6 increase.
  | satire:  Fact → Abstraction
  | compile: Fact → Encoding → Abstraction → Abstraction
  | execute: Fact → Encoding → Abstraction → Abstraction

namespace Abstraction   -- Bullshit meter = 2759.  This is a big jump, but that's because we couldn't compute
                        -- LE on the above types.

def le : Abstraction → Abstraction → Prop := fun f1 f2 =>
  match f1,f2 with
  | .satire f1     , .satire f2      => f1 = f2
  | .satire f1     , .compile f2 _ _ => f1 = f2
  | .satire f1     , .execute f2 _ _ => f1 = f2
  | .compile f1 _ _, .satire f2      => f1 = f2
  | .execute f1 _ _, .satire f2      => f1 = f2
  | .compile _ _ _, .compile _ _ _ => true
  | .compile _ _ _, .execute _ _ _ => true
  | .execute _ _ _, .execute _ _ _ => true
  | .execute _ _ _, .compile _ _ _ => false

def lt: Abstraction → Abstraction → Prop := fun f1 f2 =>
  match f1,f2 with
  | .satire _, _ => false
  | _, .satire _ => false
  | .compile _ _ _, .compile _ _ _ => false
  | .compile _ _ _, .execute _ _ _ => true
  | .execute _ _ a, .execute _ _ b => lt a b
  | .execute _ _ _, .compile _ _ _ => false
end Abstraction

instance    -- Bullshit meter = 579 !!  that is a 60x increase!  Hmmm...
 : LE Abstraction := ⟨Abstraction.le⟩  -- boo ya!  abstraction head.

-- This "abstracts" the < operation. To prevent self reference paradoxes.  Consider the
-- Berry Paradox: "The smallest positive integer not definable in under eleven words".  If you can define it, then it is
-- not the smallest positive integer not definable in under eleven words.  If you cannot define it, then it is the smallest
-- positive integer not definable in under eleven words.  This is a paradox.  The solution is to say that the definition
-- of "definable" is not well defined.  In our case, we want to say that the definition of "less than" is not well defined.
-- We want to say that "less than" is only defined for certain pairs of abstractions, and that it is not defined for all pairs
-- of abstractions.  This way, we can avoid the paradox.
instance  -- Bullshit meter = 579    Expected from above
 : LT Abstraction := ⟨Abstraction.lt⟩  -- boo ya!  abstraction head.
--  ^                                              ^
--  |                                              |
--  +-----------------+----------------------------+
--                    |
--                    +---------------- This is __NOT__ a bug.  Figure it out! Berry Paradox much?
--                                      Not to worry!  I told you in episode 1 that if you forget
--                                      what the high fructose syntax syrup means, it means ≤.
end Measurement
