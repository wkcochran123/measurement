/-
__Measurement: The Tragedy of John Henry__
__A Satire in Look-Ahead Backus-Naur Form__

_This is a gentle reminder that the convergent stories we tell ourselves are just that: stories._

(c) 2026 void *rights = malloc(sizeof(ALL))


I feel like we are playing a little loose and cool with the definition of time.  I mean, sure we
can jimmy up numbers with a snap, but I'm not certain we are all on the same page here.

We are on Einstein's page.  Between the _lines_ on Einstein's page.  When Einstein discusses
clocks, he _clearly_ states that he has absolutely NO IDEA what happens between the emission and
reception of a carrier particle.  Just that the math works unbelievably nicely if we just assume
the it is linear in nature.

The man was brilliant and _knew_ he was taking a short cut.  Don't blame him though, this category
error was made by anyone who ever said it was _possible_ to do __X__.  Not certain Turing was so
humble when _he_ made the same claim that process could be represented by symbols.  You ever play
piano?  But, I digress.

Like I said, we have to be _VERY_ careful about what we _TRY_ to program so that we don't accidentally
violate __Turing's assumption__.  That's the hard part, I believe I can earn the descriptions I make.
They are the universe labels the compiler generates, somehow, and represents as electrons, somehow,
that can be represented as electron state, somehow, and have that process faithfully inverted to
present to you this very sentence, somehow.  See?  Engineering!

That's why it is _GRAVELY_ important that (1) you understand I am trying to describe how Du=0 works
to the compiler, (2) I am trying to describe to you how time can be measured by the very act of
compiling this document, (3) while describing the sciene necessary to achieve the feats of engineering
descibed above.  All while making sure I do not program anything that does allow the violation of
the halting problem.  Sound fair?  Unless the compiler is actually _doing_ something, I bet you would
never believe this is true. It will always compile, it just might start taking time as I start asking
the compiler to fudge it a bit.

Play for a quarter?
-/

-- Have I convinced you yet of the dangers of using other peoples imports?
import Measurement.Episode3


-- Use this at your own risk.  If you accidentally program something that requires the violation of
-- the halting problem to represent, you might find yourself waiting a few minutes for the compiler
-- as it slowly enumerates ALL of computation to find your program.

-- -O2 is for suckers, this thing enumerates computation and finds the one that we want and copies
-- the input into the output. That's how it compiles!  Kolmogorov eat your heart out, I put a ring on it!

-- Literally, algebraic ring incoming.
namespace Measurement


-- I forgot where we were, easy to get lost.  Oh yeah, Oldendian and Newendian.  This is how things
-- appear on a wire.  Oldendian arrives first, new endian arrives second.  So, what we want to do
-- is have co/contravariant old/new endian representations of binary objects.  I think that allows
-- __Ψ__ function to be something more fancy than Fact.Truth superposed with..  superposed with..
-- what is it superposed with?  Itself?  Probably.

-- Or, think about it like this.  Think assembly code.  Think add by value, add by register, and
-- add by address.  What if _ALL_ three opcodes _HAPPENED_ to resolve the register exactly the same
-- way __BUT__ leave the internal state of the computer different?  Heartbleed style?
-- You remember Heartbleed, right?  Yeah, finally showed up in a proof I couldn't get to work.
-- Took a minute to debug.

-- _TIME_ is precious.  And, for all you care, electrons are _FREE_ and full of _ENERGY_.
-- We can equate them for you and the compiler now.  We can tell the compiler that, in fact,
-- It generated _these_ bits for _you_ in this _order_.  But, there is no reason why every bit
-- had to exactly come in that order to do the same thing.  One may iterate with tail recursion
-- or a for loop, each optimized for different patterns of access.   It is the pattern of access
-- that matters most to make the most economical use of time.

-- Thank God Kolmogorov was very clear in explaining exactly _HOW_ you can write code to make it
-- the shortest to _encode_.  As I said, computing Chaitin bits gets... expensive in time.

-- Now, according to Einstein, time cannot be well ordered, so, just as with a number, a history is
-- partially ordered.

-- But first, let me case-and-paste the code just as in Episode 1:
namespace Area
def le : Area → Area → Prop
  | .t _ , _ => True
  | .dt  _ _, .t _ => False
  | .dt  p1 n1', .dt  p2 n2' =>
      match p1.decTruth, p2.decTruth with
      | isTrue _,  isTrue _  => le n1' n2'
      | isTrue _,  isFalse _ => False
      | isFalse _, isTrue _  => True
      | isFalse _, isFalse _ => ¬ le n1' n2'

-- Simultaneity prevents well ordering
end Area

instance : LE Area := ⟨Area.le⟩

structure SensingProcess
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
  where
  slip_process : SlipProcess Value Carrier
  accumulation: Area

  receive_carrier: Area → Area := fun s => match s with
    | .t _ => .t d.fact
    | .dt fact _ => .dt fact accumulation

class PRESENT
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
  where
  sensing_process: SensingProcess Value Carrier
  present: Area → Area → Prop := fun s1 s2 => sensing_process.receive_carrier s1 = s2

inductive Phenomenon
  | inital_condition: Fact → Area → Phenomenon → Phenomenon
  | observations: Fact → Area → Phenomenon → Phenomenon → Phenomenon

namespace Phenomenon
def le : Phenomenon → Phenomenon → Prop := fun p1 p2 =>
  match p1, p2 with
  | .inital_condition f1 _ p1', .inital_condition f2 _ p2' =>
      match f1.decTruth, f2.decTruth with
      | isTrue _,  isTrue _  => le p1' p2'
      | isTrue _,  isFalse _ => False
      | isFalse _, isTrue _  => True
      | isFalse _, isFalse _ => ¬ le p1' p2'
  | .observations f1 _ p11 p12, .observations f2 _ p21 p22 =>
      match f1.decTruth, f2.decTruth with
      | isTrue _,  isTrue _  => le p11 p21 ∧ le p12 p22
      | isTrue _,  isFalse _ => False
      | isFalse _, isTrue _  => True
      | isFalse _, isFalse _ => ¬ (le p11 p21 ∧ le p12 p22)
  | .inital_condition _ _ _, .observations _ _ _ _ => True
  | .observations _ _ _ _, .inital_condition _ _ _ => False

end Phenomenon

structure GaugeProcess
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
  where
  sensing_process : SensingProcess Value Carrier
  phenomenon : Phenomenon

class MEASURABLE
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
  where
  gauge_process : GaugeProcess Value Carrier          -- See? Anything that can   --------------+
                                                      -- Du=0 can F=dF + A∧A.                   |
                                                      --                                        V
  observed: Area → Area → Prop := fun s1 s2 => gauge_process.sensing_process.receive_carrier s1 = s2

-- The compiler and I agree.  It promises that any computation I ask of it will satisfy Du=0 _and_ F=dF + A∧A.
-- You and I will call that fact 0.  This is our initial condition.

inductive Jar
  | bang: Fact → Jar → Jar -- BINKS!  Meesa Spake!
  | superposition: Fact → Jar → Jar → Jar

namespace Jar
def le : Jar → Jar → Prop := fun j1 j2 =>
  match j1, j2 with
  | .bang f1 j1', .bang f2 j2' =>
      match f1.decTruth, f2.decTruth with
      | isTrue _,  isTrue _  => le j1' j2'
      | isTrue _,  isFalse _ => False
      | isFalse _, isTrue _  => True
      | isFalse _, isFalse _ => ¬ le j1' j2'
  | .superposition f1 j11 j12, .superposition f2 j21 j22 =>
      match f1.decTruth, f2.decTruth with
      | isTrue _,  isTrue _  => le j11 j21 ∧ le j12 j22
      | isTrue _,  isFalse _ => False
      | isFalse _, isTrue _  => True
      | isFalse _, isFalse _ => ¬ (le j11 j21 ∧ le j12 j22)
  | .bang _ _, .superposition _ _ _ => True
  | .superposition _ _ _, .bang _ _ => False

-- Again, not well ordered.  This is the _DEFINITION_ of simultaneous.
-- Spooky!
end Jar

instance : LE Jar := ⟨Jar.le⟩  -- boo ya!  jar head.

-- Meesa explain!
-- Meesa take the concept and put it in the jar!
-- Meesa don't know what meesa saying but the compiler does!
-- Meesa the β-reduction! Meesa VERY IMPORTANT!

structure MeesaProcess
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
    [frquency: PRESENT Value Carrier]
    [what_meesa_saying: MEASURABLE Value Carrier]  -- <-- compiler gibberish representing a number
  where
  gauge_process : GaugeProcess Value Carrier
  concept: Jar
  life_debt? : Jar → Jar := fun j => match j with
    | .bang f _ => .bang f concept
    | .superposition f _ j2 => .superposition f concept j2

class GUNGAN
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
    [frquency: PRESENT Value Carrier]
    [what_meesa_saying: MEASURABLE Value Carrier]  -- <-- compiler gibberish representing a number
  where
  gauge_process : GaugeProcess Value Carrier
  translation? : Jar → Jar → Prop := fun j1 j2 => match j1, j2 with
    | .bang f1 _, .bang f2 _ => f1 = f2         -- What color is your jar?
    | .superposition f1 _ _, .superposition f2 _ _ => f1 = f2
    | _, _ => False
-- I mean, c'mon now.  Can't you see the imaginary number here?
-- If we teach the Gungans Maxwell's equations then we can calibrate 1 second across everyone!
-- And the compiler will let us know if it _thinks_ we are getting through by us asking is _true_
-- still equal to _true_?

-- You remember that puzzle.  From your childhood.  The one where one person always lies
-- and one always tells the truth?  . ntroducing the translater for the two people guarding the door.

-- Do you remember the colosseum? Do you remember looking at the doors and asking which door?
-- Do you want the lady? or the tiger?

-- Do you think the compiler is going to give you the lady? or the tiger?

-- Hope you don't ask much of the compiler....
end Measurement
