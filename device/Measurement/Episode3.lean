/-
__Measurement: The Tragedy of John Henry__
__A Satire in Look Ahead Backus-Naur Form__

_This is a gentle reminder that the convergent stories we tell ourselves are just that: converging._

(c) 2026 All rights reserved -- All lefts flamboyant

__EPISODE 3__: _Convergence_

"Forty-two?"
                       -- Douglas Adams

"It's the ship that made the Kessel Run in less than twelve parsecs."
                       -- Han Solo

"Almost all statistics are made up on the spot. 70% of people know that."
                       -- Slim Goodbody

lake build -O2 -Wpacked -Wpadded

__HONEST QUESTION__: Why isn't distance measured in Hz? It is calibrated in Hz. Or must distance always be calculated in Hz no matter how hard you
try not to? Hmm.
-/

-- Welcome back to the chaotic maelstrom that is my understanding of math.
import Measurement.Episode2
-- So far, though, haven't needed anything else imported, don't see the need to start.
set_option allowUnsafeReducibility true

namespace Measurement

universe i --| We dropped a bomb last episode. We defined the arrow of time to be a direction from the origin (Ep2:821), not the other way around
           --| (Ep2:822). We then spent about 300 lines of code demonstrating to *YOU the KNOWER* that they probably don't know what _MATTER_s and
           --| what _DOESN'T MATTER_. But, without the _DOESN'T MATTER_, the code is poorly defined. Entire universes of false statements can be
           --| built. And Godel assures us that at least a countable number of them even compile. Or, must they compile? What if they compile in
           --| another language? No MATTER the case, we have demonstrated that universes are not necessarily full of TRUTH, there can be lots of
           --| False Facts that exist by theorem alone. I mean, we are making them right now, so don't take my word for it. Take the compiler's.

           --| We ended last episode with the concept of a PRESENT. A box wrapped so you cannot see inside it, much like the experiments run at the
           --| Large Hadron Collider (double checks spelling---there are jokes in good taste and those in poor). The interaction is captured on paper
           --| and looked at afterward. Scientist look at the paper and suggest that a Jar might be the better descriptor here.  You can see into
           --| jars instead of boxes of PRESENTs. What if we could describe the PRESENT without unwrapping it?

           --| Any physicist will tell you that the opacity of cardboard _SEVERELY_ restricts the ability to see inside the container. Rather, the
           --| physicist would suggest more translucent materials. This is why I suggest Jar as the better model for now than boxes of PRESENTs.
           --| You can mostly work out what is in a Jar just by looking at it.

           --| The Jar does not affect the opacity of the PRESENT. The Jar just has the property that you can _see inside_. That's the thing we want
           --| to _ADD_ to the present so we can, well, _see inside_. See, without laughably false statements, we could not ask the compiler to
           --| evaluate the consistency of the Fact that you can, mostly, see what's inside the Jar.

/-
ME: I need Jar Jar Binks.           | It is very hard to see past the origin. Past the beginning. Before. As you look backward in time, there is
COMPILER: Absolutely not.           | an accumulation of ignored residue. This residue accretes until, finally, the only thing left to distinguish
ME: Relax. First, just the jar.     | is if there was a before.
COMPILER: What is in it?            |
ME: That's the point. Opacity.  ----+ There is _always_ a before. We keep seeing _afters_.
-/
inductive Jar  -- Bullshit meter ≈ 153    *hmmm*,    I would have thought this should be higher?
  | color: Fact → Area → Jar
  | bang: Fact → Jar → Jar -- BINKS!  Meesa Spake! -----+ So, what the hell is a jar?  I've never heard of a mathematical or physical concept called
--   ⠀⠀⠀⠀⠀⠀⢀⣶⣤⣀⠀⠀⠀⡼⡑⠢⣄⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀                 | a jar.  Will, it is like a bag, except you can kinda see whats in the middle of it. You
--   ⠀⠀⠀⠀⠀⠀⢘⢉⢹⣯⣆⡰⣾⣷⣀⡄⣼⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀                 | can't really see what's around the edge because of the curvature of the jar. The important
--   ⠀⠀⠀⠀⠀⠀⠈⣧⠭⣹⢟⣽⣿⣷⡚⠿⠏⠳⠒⠢⡀⠀⠀⠀⠀⠀⠀⠀⠀⠀                 | thing about a jar is yuo can classify the stuff inside by justs looking at it rather than
--   ⠀⠀⠀⠀⠀⠀⠀⢈⠏⠈⠼⣿⣿⣏⠉⠀⠀⠀⠀⢶⠛⠢⡀⠀⠀⠀⠀⠀⠀⠀                 | _actually_ opening it up and verifying what's inside. You can't verify _EVERY LITTLE DETAIL_,
--   ⠀⠀⠀⠀⠀⠀⠀⡦⠂⠀⠊⠳⠀⠛⡢⠀⠀⠀⠀⠈⠄⠁⣻⡄⠀⠀⠀⠀⠀⠀                 | but you can get the gist of it.
--   ⠀⠀⠀⠀⠀⠀⡔⠁⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠸⠄⣘⢣⠀⠀⠀⠀⠀⠀                 |
--   ⠀⠀⠀⠀⠀⢎⣀⡠⠤⢄⣀⡀⠤⠴⠶⠠⠀⠀⠀⠀⢀⠎⢸⣽⡀⠀⠀⠀⠀⠀                 | TBF, this is the most elastic concept in the entire stack of the proof. I mean, it allows
--   ⠀⠀⠀⠀⠀⠀⠘⡤⣀⣀⣀⣤⣶⣤⠤⠂⠐⠀⠀⠀⢸⠘⠔⠝⡅⠀⠀⠀⠀⠀                 | spooky actiona at a distance, like changing the value of a card from "not hiding a quarter"
--   ⠀⠀⠀⠀⠀⠀⢰⢅⣽⢷⡝⡈⠀⠀⠀⢀⠀⠀⠀⠀⣟⠈⢄⡌⡵⠀⠀⠀⠀⠀                 | to "hiding a quarter."
--   ⠀⠀⠀⠀⠀⢀⢇⣾⣯⡞⢀⠱⡀⠀⠀⠀⠀⠀⠀⢸⠀⢔⠀⠈⠂⡆⠀⠀⠀⠀                 |
--   ⠀⠀⠀⠀⠀⡜⣻⡿⣹⠃⡌⡠⠃⠀⠀⠀⠀⠀⢠⣿⠀⠀⠈⢄⠉⢳⠀⠀⠀⠀                 | I get it, it makes no sense. It is a jar that has multiple things inside but it behaves as
--   ⠀⠀⠀⠀⢰⢡⣿⢷⣿⡖⠉⠀⠀⠀⠀⠀⠀⠀⠀⢿⣆⠀⢀⣀⠊⠀⠢⠀⠀⠀                 | a unit of boundedness. Looks like you can just keep sticking stuff into the jar, but you
--   ⠀⠀⢀⢔⣡⣾⣿⣿⣿⣷⠀⠀⠀⠀⠀⠀⠀⠀⠀⠘⣻⣷⣄⡀⠀⠁⠅⣵⠀⠀                 | may find that being able to put _anything_ in the jar leads to a serious build time
--   ⠀⠀⣶⣯⠟⠛⣿⣿⣿⣿⣷⣦⣤⠀⠀⠀⠀⠀⢀⣤⣾⣿⣿⡧⡀⠠⠎⠌⡄⠀                 | problem.
--   ⠀⠀⠜⠁⠀⠀⠸⣿⣿⣿⣿⣿⣿⣦⡀⠀⠀⢠⣿⣽⣿⣿⣿⣧⠀⠑⠄⡉⢘⡄                 |
--   ⡔⠀⠀⠀⠀⠀⠀⣿⣿⣿⣿⣿⣿⣿⣿⠀⠀⣼⣿⣿⣿⣿⣿⣿⠀⠀⠀⠘⡄⡴                 | This code already takes dozens and dozens of hours to build.

  | superposition: Fact → Jar → Jar → Jar
--        ^
--        |
--        +---------   Look, others have satirized superposition better than I ever could. 🐱📦🍄☁️

namespace Jar  -- Bullshit meter ≈ 214
def le : Jar → Jar → Prop := fun j1 j2 =>
  match j1, j2 with
  | .color f1 a1 , .color f2 a2 => (f1.truth ∧ f2.truth) ∧ (a1 ≤ a2) --+ In the very least, you can tell the two things in a container apart by their
  | .color _ _ , _ => True --                                          | color. This is true no matter how else it may be distinguished. However,
  | _ , .color _ _ => False --                                         | color alone is not enough to arbitrarily distinguish objects.

  | .bang f1 j1', .bang f2 j2' =>  -----------------+ Should one drop a jar on the floor, there will be a loud bang! and all the stuff in the jar
      match f1.decTruth, f2.decTruth with --        | will come spilling out and the pieces of the jar become very DANGEROUS to touch. It is
      | isTrue _,  isTrue _  => le j1' j2' --       | surprising just how many square feet of liquid can be contained by just 1 square foot of jar.
      | isTrue _,  isFalse _ => False --            |
      | isFalse _, isTrue _  => True --             | Drop a jar of mayonaise, of water, and of mineral oil. Not only are the areas different, they
      | isFalse _, isFalse _ => ¬ le j1' j2' --     | change over time, with some being less now and more later compared to others. Others grow mold.

  | .superposition f1 j11 j12, .superposition f2 j21 j22 =>  ---+ When shelving jars, you can easily read off ALL labels. This allows you to
      match f1.decTruth, f2.decTruth with --                    | _predict_ the area of the inside based on the label.  Mayonaise would have some
      | isTrue _,  isTrue _  => le j11 j21 ∧ le j12 j22 --      | value, water some value, and oil some value.  So, just looking at the number of
      | isTrue _,  isFalse _ => False --                        | _slots_ on the label, you can probably guess what will happen if you find two
      | isFalse _, isTrue _  => True --                         | with the same label. If you throw _one_ on the floor, the area should be roughly
      | isFalse _, isFalse _ => ¬ (le j11 j21 ∧ le j12 j22) --  | the same as the other, up to the shape of the jar.

  | .bang _ _, .superposition _ _ _ => True  ---+ Blah, blah, blah.  Sleight-of-hand... misdirection... Ya da, ya da. Would _NOT_ matter in the least
  | .superposition _ _ _, .bang _ _ => False  --| if I tried to explain this to you.

-- Again, not well ordered.  This is the _DEFINITION_ of simultaneous.           **SPOOKY!**
end Jar

/- CHORUS:
ME: Allow me to introduce Jar Jar Binks. --                       | The trope I am referring to here is that the Gungan could be relied on to try
COMPILER: Dear god, no. --                                        | to explain intelligence through organized use of communicative symbols by using
JAR JAR: MEESA SPAKE! --------------------------------------------+ said symbols to present the argument. Qui-gon balked at the obvious circularity,
ME: Jar Jar doesn't hold any deep meaning for the universe, I     | responding that the ability to communicate alone does not make one intelligent.
    just needed a trope.
-/
instance : LE Jar := ⟨Jar.le⟩  -- Bullshit meter ≈ 5.   I mean, c'mon compiler.  I'm confident my
                               -- bullshit meter is pretty well calibrated.

-- Looks like Jar Jar has something to _VERY IMPORTANT_ to say about the nature of time:

-- Meesa explain!                                                              |   |
-- Meesa take the concept and put it in the jar!                               |-O-|  pyew! pyew!
-- Meesa don't know what meesa saying but the compiler does!                   |   |*
-- Meesa the β-reduction! Meesa VERY IMPORTANT!                                         *

-- FULL DISCLOSURE:  Jar Jar is along for the ride to help __YOU the READER__ explain to __YOU the KNOWER__ how this argument works. *YOU the KNOWER*
-- is invited to laugh at the frivolity on display for the time being.

/-                                                 | I am reminded of the paradox of Mary and the color red. Imagine Mary is locked in a room for
ME: I need a MeesaProcess. ------------------------+ her entire life. The room has no color in it. It does have the worlds literature and
COMPILER: I refuse the dialect.                    | entertainment in it. But all objects, save Mary herself, are black and white. The internet,
ME: You called yourself a ventriloquist.           | movies, TV, what have you. All black and white. And most importantly, it has Wikipedia and the
COMPILER: I make values speak through symbols.     | page for the color red. Mary studies this page every day. And she walks out of the room and
JAR JAR: ME TOO!                                   | is shown the color red for the first time. Did Mary learn anything? Put what she learned in a
-/ --                                              | Box and hand it to a Pigeon.
structure MeesaProcess  -- Bullshit meter ≈ 1010.
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [DISTINGUISHABLE Box Pigeon] --+
    [ADMISSIBLE Box Pigeon] --     |           | You may be wondering what happened to the *CLICK* we used to get. The compiler isn't elaborating
    [COUNTABLE Box Pigeon] --      |           | the source in the β-reduction. It is applying a rule explicitly without recursion, meaning that
    [ENCODED Box Pigeon] --        +-----------+ unless we ask it _DIRECTLY_ with decTruth, the compiler need not elaborate anything. The elaboration
    [RESIDUE Box Pigeon] --        |           | step measures _consistency of argument_. We are looking at _consistency of spelling and grammar_.
    [BINARY Box Pigeon] --         |           | That's what can be measured. How many objects have been stacked (indicated by universe level) or
    [REPEATABLE Box Pigeon] --     |           | how long has it taken to compile (the bullshit meter). It doesn't take a rocket surgeon to put two
    [NUMERIC Box Pigeon] --        |           | and two together and come up with the _faster_ the Millineum Falcon was going, the _shorter_ the
    [REPRESENTABLE Box Pigeon] --  |           | trip. That's just _PHYSICS_.
    [PHYSICAL Box Pigeon] --       |           |
    [COMPARABLE Box Pigeon] --     |           | It is the _ACT of MEASUREMENT_ that actually does the distinguishing. That's also, just _PHYSICS_.
    [OBSERVED Box Pigeon] --       |           |
    [PRESENT Box Pigeon] --        |           | And, is there anything more scientific than a _measurement_?
    [MEASURABLE Box Pigeon] -------+
  where
--      +-----------------------------------+ This is the process that _tickles_. The compiler keeps track of where it tickles and names each spot.
--      |                                   | This name is put on the jar. Remember, _tickles_ means that there are contravariant meanings afoot:
--      V                                   | illustrious bullshit meant to direct the attention of *YOU the READER* toward or away from a certain
  gauge_process : GaugeProcess Box Pigeon --| aspect of the argument.
  concept: Jar
--      ^                      | The ability to wrap a very complex concept in a very small term is the successful applicaiton of Huffman encoding.
--      |                      | While I do not claim that we are implementing said encoding, I offer it as an example of how concepts may stack based
--      +----------------------+ on just their syntactic usage.

--    +--------------------------------------------------------------+ The study and practice of science takes years and years and years to master,
--    |                                                              | if it can be mastered at all. The important thing is that these jars are
--    V                                                              | completely fungible. Colors only lead to colors, bangs only lead to bangs,
  life_debt? : Jar → Jar := fun j => match j with --                 | and these are purely _countable_ creations that a Master of Science can
    | .color f a => .color f a          -- Colors don't run          | readily understand as the diffusion equation.
    | .bang f _  => .bang f concept
    | .superposition f _ j2 => .superposition f concept j2  -- The concept inherits the current state of affairs in the superposition.

-- As carefully explained last episode, our argument is a very specially constructed _ONTOLOGY_ as the compiler can be readily called upon to make
-- _ONTOLOGICAL_ arguments. However, we also demonstrated that such arguments allow for utter _NONSENSE_ to be spoken of as possibilities. Here
-- is more nonsense on why this is fine: The *CLICK*s and pops of the instrument itself was a _DEMONSTRATION_ of how _MEANING_ can _tunnel_ out of
-- ontological arguments through leaky abstractions. The β-reduction is NOT a leaky abstraction. No *CLICK*s.

/-
ME: I need GUNGAN.                                        | Much of the perceived "nonsense" of this argument is laid out across the type system of
COMPILER: This is Lean.                                   | Lean. Inductives are used to wire together ever more complex definitions of ≤. Rules
ME: It is a translation layer.                            | are generated that evolve these inductive definitions into each other. Other rules
COMPILER: From what?                                      | provide a comparison of two inductive definitions. It all must compile to be an
ME: From the jar's dialect into admissible structure. ----+ _admissible_ argument. If the argument does not at least _compile_, how can it ever
COMPILER: I refuse to understand it.                      | be used in the construction of a correct understanding?
ME: Good. Understanding was never the contract.           |
-/ --                                                     | Correctness of argument and the truth of the argument may or may not be related.
class GUNGAN  -- Bullshit meter ≈ 802.
    (Box: Type i)
    (Pigeon: CarrierProcess Box) --    | What does it mean for an argument to be _admissible_? It means that there must have been a situation that
    [DISTINGUISHABLE Box Pigeon] --    | lead to what ever situation you can think about. Every _after_ has a _before_. That is a _FACT_ of life
    [ADMISSIBLE Box Pigeon] -----------+ not a truth to be discovered. However, not all _befores_ have an _after_. Consider two polarizing filters
    [COUNTABLE Box Pigeon] --          | at right angles to each other. While the photon may be _before_ the second filter, it is not _after_ it.
    [ENCODED Box Pigeon] --            | The photon just _stops_.
    [RESIDUE Box Pigeon] --            |
    [BINARY Box Pigeon] --             | It isn't absorbed. It just is canceled out. That _before_ of a photon stopped having an _after_ as the
    [REPEATABLE Box Pigeon] --         | photon no longer was capable of existing due to orientation. Sliding a third polarizing filter between the
    [NUMERIC Box Pigeon] --            | two, offset at a forty-five degree angle and the photon may now exist _after_ the second filter.
    [REPRESENTABLE Box Pigeon] --      |
    [PHYSICAL Box Pigeon] --           | Two polarizers admit _no light_. Three polarizers, two arranged identically as before, admit _light_.
    [COMPARABLE Box Pigeon] --         |
    [OBSERVED Box Pigeon] --           | What happens if you spin the middle filter?
    [PRESENT Box Pigeon] --            |
    [MEASURABLE Box Pigeon] --         | **DISCO**
  where
  meesa_process : MeesaProcess Box Pigeon
  correllant? : Jar → Jar → Prop := fun j1 j2 => match j1, j2 with
    | .bang f1 _, .bang f2 _ => f1 = f2         -- What color is your jar?
    | .superposition f1 _ _, .superposition f2 _ _ => f1 = f2
    | _, _ => False
-- and one always tells the truth?  Introducing the translater for the two people guarding the door. Do you remember the colosseum? Do you remember
-- looking at the doors and asking which door? Do you expect the lady? or the tiger?

-- Do you think the compiler is going to give you the lady? or the tiger? I hope you don't ask much of the compiler....

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
    (Box: Type i)
    (Carrier: CarrierProcess Box)
    [d: DISTINGUISHABLE Box Pigeon]
    [a: ADMISSIBLE Box Pigeon]
    [c: COUNTABLE Box Pigeon]
    [e: ENCODED Box Pigeon]
    [r: RESIDUE Box Pigeon]
    [b: BINARY Box Pigeon]
    [f: REPEATABLE Box Pigeon]
    [n: NUMERIC Box Pigeon]
    [h: REPRESENTABLE Box Pigeon]
    [p: PHYSICAL Box Pigeon]
    [z: COMPARABLE Box Pigeon]
    [particle: OBSERVED Box Pigeon]
    [frequency: PRESENT Box Pigeon]
    [cant_be_done: MEASURABLE Box Pigeon]
    [what_meesa_saying: GUNGAN Box Pigeon]                   -- We all agree that what we know zero is, right?
                                                   -- This is zero in GUNGAN.

  where
    meesa_process : MeesaProcess Box Carrier
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
ME: The origin story. The physical thing
    that stores the information itself.
-/
class SOURCE   -- Bullshit meter ≈ 1121.   That's almost a 50% increase!
    (Value: Type i)
    (Carrier: CarrierProcess Value)
    [d: DISTINGUISHABLE Box Pigeon]
    [a: ADMISSIBLE Box Pigeon]
    [c: COUNTABLE Box Pigeon]
    [e: ENCODED Box Pigeon]
    [r: RESIDUE Box Pigeon]
    [b: BINARY Box Pigeon]
    [f: REPEATABLE Box Pigeon]
    [n: NUMERIC Box Pigeon]
    [h: REPRESENTABLE Box Pigeon]
    [p: PHYSICAL Box Pigeon]
    [z: COMPARABLE Box Pigeon]
    [particle: OBSERVED Box Pigeon]
    [frequency: PRESENT Box Pigeon]
    [what_meesa_saying: MEASURABLE Box Pigeon]
    [zero: GUNGAN Box Pigeon]
  where
  cd_process : DigitalProcess Box Carrier
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
    [d: DISTINGUISHABLE Box Pigeon]
    [a: ADMISSIBLE Box Pigeon]
    [c: COUNTABLE Box Pigeon]
    [e: ENCODED Box Pigeon]
    [r: RESIDUE Box Pigeon]
    [b: BINARY Box Pigeon]
    [f: REPEATABLE Box Pigeon]
    [n: NUMERIC Box Pigeon]
    [h: REPRESENTABLE Box Pigeon]
    [p: PHYSICAL Box Pigeon]
    [z: COMPARABLE Box Pigeon]
    [particle: OBSERVED Box Pigeon]
    [frequency: PRESENT Box Pigeon]
    [what_meesa_saying: MEASURABLE Box Pigeon]
    [zero: GUNGAN Box Pigeon]
    [one: SOURCE Box Pigeon]

  where
  digital_process : DigitalProcess Box Carrier
  source: SOURCE Box Carrier
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
    [d: DISTINGUISHABLE Box Pigeon]
    [a: ADMISSIBLE Box Pigeon]
    [c: COUNTABLE Box Pigeon]
    [e: ENCODED Box Pigeon]
    [r: RESIDUE Box Pigeon]
    [b: BINARY Box Pigeon]
    [f: REPEATABLE Box Pigeon]
    [n: NUMERIC Box Pigeon]
    [h: REPRESENTABLE Box Pigeon]
    [p: PHYSICAL Box Pigeon]
    [z: COMPARABLE Box Pigeon]
    [particle: OBSERVED Box Pigeon]
    [frequency: PRESENT Box Pigeon]
    [what_meesa_saying: MEASURABLE Box Pigeon]
    [zero: GUNGAN Box Pigeon]
    [one: SOURCE Box Pigeon]

  where
  compiled_process : CompiledProcess Box Carrier

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
