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
namespace Area   -- Bullshit meter ≈ 111
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

instance : LE Area := ⟨Area.le⟩ -- Bullshit meter ≈ 8

structure SensingProcess -- Bullshit meter ≈ 750
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
  static_fraction : SlipProcess Value Carrier
-- μ: You don't get to know this.
  accumulation: Area   -- You _do_ get to know this.

  use_force: Area → Area := fun s => match s with
    | .t _ => .t d.fact
    | .dt fact _ => .dt fact accumulation

-- You know who else has a secret threshold _AND_ can use the force?

-- Santa Claus!
-- How do you _KNOW_ if you have been _TOO_ naughty?  Can you be a little bit _more_ naughty and still get presents?
-- Also, using the force is _THE ONLY EXPLANATION_ for how he can get around the Earth in a single night.

class PRESENT  -- Bullshit meter ≈ 594
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
--     +---------------+---------------------------    Somehow, the _FAT MAN_(tm) always knows if you have been good or bad.  He
--     |               |                               uses this information to compute the most efficient route to "cover" the
--     |               |                               sphere.  He does this using what Jar Jar Binks would recognize as "the force".
--     V               V                               Not saying _it is_ the force, just saying Jar Jar would see it that way.
  santa_claus: SensingProcess Value Carrier
  present: Area → Area → Prop := fun s1 s2 => santa_claus.use_force s1 = s2    -- Now, this is an AI video waiting to happen.
--     ^    ^      ^
--     |    |      |                     One of the more interesting things that Einstein showed us is that the "present time"
--     +----+------+------------------   is very much a "local" computation.  The farther away you are from something, the farther
--                                       away in time it is to you.  This is why the present is only in the local area.  That,
--                                       and I suspect Santa uses Stokes' theorem to compute the local curl.

inductive Phenomenon   -- Bullshit meter ≈ 153
  | inital_condition: Fact → Area → Phenomenon → Phenomenon
  | observations: Fact → Area → Phenomenon → Phenomenon → Phenomenon

namespace Phenomenon  -- Bullshit meter ≈ 227
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

-- If we are talking about a phenomenon, we need to talk about how to measure it.  Normally, you get an intstrument
-- with a _gauge_ on it, stick the instrument in the phenomenon, and read the gauge.  In order to explain Yang-Mills
-- Gauge theory to Jar Jar Binks, we need to first agree on what a gauge is.  A gauge generally takes a physical principle,
-- like quantum electrodynamics, and uses it to measure something.  In this case, we are going to measure _time_.

-- A stop watch is a cromulent gauge for measuring time, but Jar Jar Binks is from Star Wars and Star Wars happened a long
-- time ago before they invented clocks.  So, we have to use something else.  Actually, any gauge will work.  That's the
-- thing about Gauge Theory.  It explains how gauges display the numbers physics wants it to.

-- STAND BACK!  I am about to _SCIENCE_!
structure GaugeProcess  -- Bullshit meter ≈ 830
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
--       +-------------------------------------------  Sensors are neat little devices.  They are capable of _exchanging_ things.
--       |                                             A sensor exchanges _information_ for _chaos_.   You learn something about
--       |                                             the universe and the universe gets lower frequency photons in return.
--       V
  sensing_process : SensingProcess Value Carrier
  phenomenon : Phenomenon

  event? : Phenomenon → Phenomenon := fun p =>
    match p with
    | .inital_condition f a p => .observations f (sensing_process.use_force a) p phenomenon
    | .observations f a _ p12 => .observations f (sensing_process.use_force a) p12 phenomenon

class MEASURABLE  -- Bullshit meter ≈ 730
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
  observed: Area → Area → Prop := fun s1 s2 => gauge_process.sensing_process.use_force s1 = s2

-- The compiler and I agree.  It promises that any computation I ask of it will satisfy Du=0 _and_ F=dF + A∧A.
-- You and I will call that fact 0.  This is our initial condition.

inductive Jar  -- Bullshit meter ≈ 153    *hmmm*,    I would have thought this should be higher?

  | bang: Fact → Jar → Jar -- BINKS!  Meesa Spake!        So, what the hell is a jar?  I've never heard of a mathematical or
--   ⠀⠀⠀⠀⠀⠀⢀⣶⣤⣀⠀⠀⠀⡼⡑⠢⣄⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀                   physical concept called a jar.  Will, it is like a bag, except you
--   ⠀⠀⠀⠀⠀⠀⢘⢉⢹⣯⣆⡰⣾⣷⣀⡄⣼⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀                   can kinda see whats in the middle of it.  You can't really see what's
--   ⠀⠀⠀⠀⠀⠀⠈⣧⠭⣹⢟⣽⣿⣷⡚⠿⠏⠳⠒⠢⡀⠀⠀⠀⠀⠀⠀⠀⠀⠀                   around the edge because of the curvature of the jar.  The important
--   ⠀⠀⠀⠀⠀⠀⠀⢈⠏⠈⠼⣿⣿⣏⠉⠀⠀⠀⠀⢶⠛⠢⡀⠀⠀⠀⠀⠀⠀⠀                   thing about a jar is you can classify the stuff in side by just looking
--   ⠀⠀⠀⠀⠀⠀⠀⡦⠂⠀⠊⠳⠀⠛⡢⠀⠀⠀⠀⠈⠄⠁⣻⡄⠀⠀⠀⠀⠀⠀                   at it rather than _actually_ opening it up and verifying what's inside.
--   ⠀⠀⠀⠀⠀⠀⡔⠁⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠸⠄⣘⢣⠀⠀⠀⠀⠀⠀                   You can't verify _EVERY LITTLE DETAIL_, but you can get the gist of it.
--   ⠀⠀⠀⠀⠀⢎⣀⡠⠤⢄⣀⡀⠤⠴⠶⠠⠀⠀⠀⠀⢀⠎⢸⣽⡀⠀⠀⠀⠀⠀
--   ⠀⠀⠀⠀⠀⠀⠘⡤⣀⣀⣀⣤⣶⣤⠤⠂⠐⠀⠀⠀⢸⠘⠔⠝⡅⠀⠀⠀⠀⠀                   TBF, this is the most elastic concept in the entire stack of the proof.
--   ⠀⠀⠀⠀⠀⠀⢰⢅⣽⢷⡝⡈⠀⠀⠀⢀⠀⠀⠀⠀⣟⠈⢄⡌⡵⠀⠀⠀⠀⠀                   I mean, it allows for spooky action at a distance, like moving a quarter
--   ⠀⠀⠀⠀⠀⢀⢇⣾⣯⡞⢀⠱⡀⠀⠀⠀⠀⠀⠀⢸⠀⢔⠀⠈⠂⡆⠀⠀⠀⠀                   from under one card to another.  Spooky!
--   ⠀⠀⠀⠀⠀⡜⣻⡿⣹⠃⡌⡠⠃⠀⠀⠀⠀⠀⢠⣿⠀⠀⠈⢄⠉⢳⠀⠀⠀⠀
--   ⠀⠀⠀⠀⢰⢡⣿⢷⣿⡖⠉⠀⠀⠀⠀⠀⠀⠀⠀⢿⣆⠀⢀⣀⠊⠀⠢⠀⠀⠀                   I get it, it makes no sense.  It is a jar that has multiple things inside
--   ⠀⠀⢀⢔⣡⣾⣿⣿⣿⣷⠀⠀⠀⠀⠀⠀⠀⠀⠀⠘⣻⣷⣄⡀⠀⠁⠅⣵⠀⠀                   but it behaves as a unit of boundedness.  Looks like you can just keep
--   ⠀⠀⣶⣯⠟⠛⣿⣿⣿⣿⣷⣦⣤⠀⠀⠀⠀⠀⢀⣤⣾⣿⣿⡧⡀⠠⠎⠌⡄⠀                   sticking stuff into the jar, but you may find that being able to put
--   ⠀⠀⠜⠁⠀⠀⠸⣿⣿⣿⣿⣿⣿⣦⡀⠀⠀⢠⣿⣽⣿⣿⣿⣧⠀⠑⠄⡉⢘⡄                   _anything_ in the jar leads to serious build time problem.
--   ⡔⠀⠀⠀⠀⠀⠀⣿⣿⣿⣿⣿⣿⣿⣿⠀⠀⣼⣿⣿⣿⣿⣿⣿⠀⠀⠀⠘⡄⡴

  | superposition: Fact → Jar → Jar → Jar
--        ^
--        |
--        +---------   Look, others have satirized superposition better than I ever could. 🐱📦🍄☁️

namespace Jar  -- Bullshit meter ≈ 214
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

instance : LE Jar := ⟨Jar.le⟩  -- Bullshit meter ≈ 5.   I mean, c'mon compiler.  I'm confident my
                               -- bullshit meter is pretty well calibrated.

-- Looks like Jar Jar has something to _VERY IMPORTANT_ to say about the nature of time:

-- Meesa explain!
-- Meesa take the concept and put it in the jar!
-- Meesa don't know what meesa saying but the compiler does!
-- Meesa the β-reduction! Meesa VERY IMPORTANT!

-- Am I going to have to invite JarJar along with us on the ride of your life?
-- Of course, I have to explain IEEE 754 to Gungans.  Didn't I say that last episode?  That I was going to end up
-- doing it?   May as well show you the MeesaProcess, the way we know the compiler has found a bit.


-- FULL DISCLOSURE:  Jar Jar is along for the ride to help __YOU__.  I _understand_ all of this already.
-- You have no one to blame but yourself.

structure MeesaProcess  -- Bullshit meter ≈ 1010.    There we go, we just broke 1000 on the bullshit meter.
                        -- That's about 1/4 increase in bullshit, measured structure-on-structure.
                        -- Huh, is that 2 bits of information?
    (Value: Type)
    (Carrier: CarrierProcess Value)                             -- It is at this point I would like to honor one of the
    [d: DISTINGUISHABLE Value Carrier]                          -- greatest philosophers of our age, Harry Frankfurt.  I urge
    [a: ADMISSIBLE Value Carrier]                               -- you to write your Congressbot and ask them to invade France
    [c: COUNTABLE Value Carrier]                                -- so that SI will have to make a new unit called the Frankfurt.
    [e: ENCODED Value Carrier]                                  -- The Frankfurt is the amount of bullshit that comes out of
    [r: RESIDUE Value Carrier]                                  -- Jar Jar Binks' mouth in a single sentence.
    [b: BINARY Value Carrier]                                   --
    [f: REPEATABLE Value Carrier]                               -- I declare the MeesaProcess to be the first Frankfurt degree.
    [n: NUMERIC Value Carrier]                                  --
    [h: REPRESENTABLE Value Carrier]                            -- Bulshit meter ≈ 1010 = 1⁰F.
    [p: PHYSICAL Value Carrier]
    [z: COMPARABLE Value Carrier]
    [particle: OBSERVED Value Carrier]
    [frequency: PRESENT Value Carrier]
    [impossible: MEASURABLE Value Carrier]
  where
  gauge_process : GaugeProcess Value Carrier
  concept: Jar
  life_debt? : Jar → Jar := fun j => match j with
    | .bang f _ => .bang f concept
    | .superposition f _ j2 => .superposition f concept j2

class GUNGAN  -- Bullshit meter = 802.  Only a 1/8 increase on classes.  Is that 3 bits?
              -- Can't tell if the compiler is trying to carry 2 or 3 bits in its head right now.
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
    [gibberish: MEASURABLE Value Carrier]
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
