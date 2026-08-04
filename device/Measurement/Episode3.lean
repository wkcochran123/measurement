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
ME: Don't you demonstrate theorems?                | movies, TV, what have you. All black and white. And most importantly, it has Wikipedia and the
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
--                      +-------------------------------------------------------+ *ACHTUNG!  ALLES TURISTEN UND NONTEKNISCHEN LOOKENSPEEPERS!*
--                      |                                                       | DAS KOMPUTERMASCHINE IST NICHT FÜR DER GEFINGERPOKEN UND
--                      |                                                       | MITTENGRABEN! ODERWISE IST EASY TO SCHNAPPEN DER SPRINGENWERK,
--                      |                                                       | BLOWENFUSEN UND POPPENCORKEN MIT SPITZENSPARKEN.
--                      V                                                       |
  meesa_process : MeesaProcess Box Pigeon --                                    | IST NICHT FÜR GEWERKEN BEI DUMMKOPFEN. DER RUBBERNECKEN SIGHTSEEREN
  correllant? : Jar → Jar → Prop := fun j1 j2 => match j1, j2 with --           | KEEPEN DAS COTTONPICKEN HÄNDER IN DAS POCKETS MUSS.
    | .bang f1 _, .bang f2 _ => f1 = f2         -- What color is your jar? --   | ZO RELAXEN UND WATSCHEN DER BLINKENLICHTEN.
    | .superposition f1 _ _, .superposition f2 _ _ => f1 = f2
    | _, _ => False
--     ^
--     |
--     +-----------------| I believe this was an idea originally posited in the magnum opus of all work on colors: Come out and play! by The Offspring.

-- You see, I don't know anything about Lean other than what I have learned from AI and banging on it in the past 8 months or so.  Before that, I
-- had spent a few months gnawing on QED. I feel like I got enough of the geometry that I could see the algebra enough that I could linearize out
-- this imaginary term. As in, you won't need a continuation to solve the Dirac equation. Instead of approximating in the mathematical representation
-- as Dirac did, I approximated the way Picard did through linearizing across the pole and looking for an attractor. Through the Calculus of
-- Variations, you can rewrite something that _looks like_ like the principle of least action _AS_ the Galerikin formulation of a cubic spline
-- solution to the Yang-Mills formulation of the Navier-Stokes equation as solved by JFNK, as long as you are preconditioning with a multi-grid
-- solver. But it only works in a relativistic space.

-- There. I said my ugly little secret. I now have to demonstrate this to you knowing only a smattering of linear algebra. Wish me luck. I guess
-- that means we have to build a Hilbert space from this mess. The first step is to build the equivalence classes required to discuss neighborhoods.
-- I call the process of building equivalence classes Equivalation.


/-
ME: I need equivalation.                             | As graduate students preparing for orals, we would ask each other really open ended questions
COMPILER: You mean equivalence.                      | about partial differential equations. It generally started with the question "Write down a
ME: No. Equivalence sits still.                      | differential equation."  Invariably, the grad student under examination would right y=f'(x).
COMPILER: And equivalation?                          | Then, the questioner would ask to add terms, explain changes, explore this, dig into that, and
ME: Equivalence under procedure.                     | pretty soon you were 4 terms deep into Taylor on one side, and some ugly transform on the
-/ --                                                | other. And, then you call out all the sharp edges of approximation. It always ended there. I
inductive Equivalation  -- Bullshit meter ≈ 119.     | tried a different approach when preparing. I wrote Du=0. It always ended there, so I just
    | physics: Fact → Jar → Equivalation ------------+ decided to shortcut the process and watch them try to write y'=f(x) from that.

  --                                                   | What does it mean to be zero like? Well nothing. What is nothing? Is the right hand side of
  --                                                   | Du=0 nothing? Is it a vector? Is it weighted by multipliers? Is it the "origin" or is it the
  --   +----+-----+------------------------------------| "frame?" Is it both? Can it accelerate? Does the derivative "vanish" like the hidden poles
  --   |    |     |                                    | of rationally expressed functions? Poles that only exist in the _REPRESENTATION_ and not in
  --   |    |     |                                    | the _REDUCED_ form? Is it okay for the _REPRESENTATION_ itself to introduce nothing as a
  --   V    V     V                                    | tangible artifact? We must equivalate. We don't have _zero_ here. It is merely _zero like_.
    | zero_like: Fact → Equivalation → Equivalation
  --              ^
  --              |
  --              +-----------------------------------------| More bluntly. Absence of evidence _MUST_ _BE_ evidence of absence to be ZERO_LIKE.

    | one_like: Prop → Equivalation → Equivalation → Equivalation   --+ Evidence of absence or absence of evidence? Don't care. This is the
  --                                                      ^           | _exclusive zero_.
  --  As Peano said, once you can see nothing, you can    |
  --  identify something called next.  -------------------+
  --  The first next is _EXTERMELY_ one like.

  -- The reason why I bring this up is that we need to figure out the Gungan number system from Jar Jar Binks.  Do you really think he understands
  -- binary?  God I hope so.  R2 does.  Perhaps we can get Jar Jar to ask R2-D2 through C-3P0 if any of this makes sense?  In which case, we need to
  -- understand the binary language of moisture evaporators:  __BINARY__.

  -- Should be a straightforward exercise from here. I have been programming (insert whatever you want here) since I was a kid.

  -- We start with the basic physical fact:  The Pauli Exclusion Principle. The Pauli exclusion principle is simple:  two things can exist
  -- simultaneously, one up and one down.  It might also be one thing.  Hard to tell sometimes.  How many electrons can there possibly be? Good news,
  -- I have a place I can store all the "upness" i find.

  -- The Pauli Exclusion Principle is simple: there can be at most one of something, unless there are two: one up and one down. You know, Binary as
  -- implemented in Java.
namespace Equivalation
def le : Equivalation → Equivalation → Prop := fun e1 e2 => ---------------+ What is the difference between Reimannian geometry and Euclidean
  match e1,e2 with --                                                      | geometry? One point. One point of Reimannian geometry must be selected
  | .physics f1 j1 , .physics f2 j2    => f1.truth ∧ f2.truth ∧ j1 ≤ j2 -- | as an origin.  All other points project to the plane from that one point
  | .physics _ _ , .zero_like _ _      => false --                         | Pointing away from the origin is a neat property for a space to have.
  | .physics _ _ , .one_like _ _ _     => true --                          | The idea is that the origin can only be selected from zero like
  | .zero_like f1 _ , .zero_like f2 _  => f1.truth ∧ f2.truth --           | candidates. Hilbert spaces also pile more restrictions on zero, but
  | .zero_like _ _ , .physics _ _      => true --                          | perhaps the most profound is that the origin is part of the space itself,
  | .zero_like _ _ , .one_like _ _ _   => true --                          | very much unlike the Euclidean geometry it is a metaphor for.
  | .one_like p1 e _, .one_like p2 f _ => p1 ∧ p2 ∧ (le e f)
  | .one_like _ _ _ , _                => false

-- Not certain one can genuinely order equivalations yet. Actually, funny story I can't tell you about reordering data in a Java iterator taking
-- months to figure out. They just let ANYBODY program a computer these days. Java 6 *shakes fist*.
end Equivalation

/- CHORUS:                        | I find it interesting that the traditional mathematics Ph.D. in some universities includes presentation and
ME: L'equivalation, c'est bon!    | understanding of a concept presented in another language.
COMPILER: ?SYNTAX  ERROR ---------+
          READY.                  | At the time, I was thankful numerical analysis was a computer science degree.
          ∎
-/
instance : LE Equivalation := ⟨Equivalation.le⟩ -- Bullshit meter ≈ 8

-- Binary computers give rise to digital communications, digital arithmetic, digital intelligence. Everything is quantized and stored as binary
-- somewhere. It is rare to see analog storage anymore. I mean, the pits and lands of the CD are dense enough to replicate sounds way past the
-- ability for humans to hear. 44kHz sampling can give you 22kHz tones which has far more "upness" than the 18kHz tone of really good hearing.
-- but even the analog feel of a plastic disc, these pits and lands are fewer and farther between on average, while the median remains
-- unchanged.

@[reducible]
/-
ME: I need a DigitalProcess. --                | We will find Jar Jar to be _quite_ agreeable in this telling. That's Jar Jar's job, to agree that
COMPILER: Bits? 1s and 0s?  --                 | work was just performed. 1 unit of work. Exactly 1 slot. Whatever 1 is. Whenever the value 1 needs
JAR JAR: Yes!      ----------------------------+ to be subtracted from a number, this object is removed from it. Meet our resident fencepost.
ME: That's right, it needs to be written down.
-/
structure DigitalProcess  -- Bullshit meter = 1211.  Up about 1/5
    (Box: Type i)
    (Pigeon: CarrierProcess Box) ------+ This argument is constructive. The final template that instantiates the number
    [DISTINGUISHABLE Box Pigeon] --    | has dozens and dozens and dozens of partial specializations, strung together.
    [ADMISSIBLE Box Pigeon] --         | The partial specializations will tell a story. That story will describe a device
    [COUNTABLE Box Pigeon] --
    [ENCODED Box Pigeon] --     | Ask an audiophile stereotype to type their stereo and _BINARY_ will be among the minority. Audio files the
    [RESIDUE Box Pigeon] --     | audiophile files in their filesystems are _BINARY_, though. A special _kind_ of audiophile binary called
    [BINARY Box Pigeon] --------+ _LOSSLESS_. Some _LOSSLESS_ files have lost less than others, though. Because the size of the files change based on
    [REPEATABLE Box Pigeon] --  | the fact some loss is more and while some loss is less. Audiophiles disagree on which is more and which is less.
    [NUMERIC Box Pigeon]
    [REPRESENTABLE Box Pigeon]
    [PHYSICAL Box Pigeon]
    [COMPARABLE Box Pigeon] --       | The Gungan process is the marking process we discussed in Episode 1. Jar Jar contains no information, he just
    [OBSERVED Box Pigeon] --         | marks time passing. One tick for everything he says. Jar Jar is evidence of the slot. When we don't get a
    [PRESENT Box Pigeon] --          | click, but Jar Jar is present, then we count the fact that there _could have been_ a click and there wasn't one.
    [MEASURABLE Box Pigeon] --       |
    [GUNGAN Box Pigeon] -------------+ The compiler will write this down for us. Using the exclusive zero and the GUNGAN 1.

  where
  --                        +-----------------+ In the movie Tron, the depiction of the BIT was adorable.  When reprised by Lucasfilm, ymmv. The idea
  --                        |                 | is that the plot itself didn't really need Jar Jar, nothing Jar Jar said provided information.
  --                        V                 | However, he _had_ to talk to move the plot forward. Admittedly, I was not the audience Jar Jar was
    meesa_process : MeesaProcess Box Pigeon --| aimed at and I have no business assuming the role of movie critic. I barely have business assuming
  --                                          | the role of software developer. Have you seen this monstrosity?

    zero: Equivalation ------| We will get more than enough ones from the meesa_process. We need the zero to start with. Will we get a one_like zero?

  -- Now that we have an exclusive OFF state and an exclusive ON state, we can finally make a clock complement.  This is merely a line we pull high
  -- then pull low on a timer so digital processes can synchronize events. c.f. crystal oscillation
    tick: Equivalation → Equivalation := fun s =>
      match s with
      | .physics f j => .physics f j    -- We __hope__ this doesn't change!

      | .zero_like _ _ => .one_like false zero zero -----------+ While starting with the assumption that a _ZERO_ exists is quite audacious, this
      | .one_like _ _ _ => .zero_like Fact.Truth zero --       | demonstrates that you can, in fact, derive _0_ and _1_ from the idea of _this_ and
--                              ^  +--+                        | _that_ _ALONE_. _YOU the KNOWER_ instantiate Nats, I pull then out of my ass.
--  I call this the thing that  |  |  |
--  Pauli exclusion needs to    +--+  |
--  know if there is a   -------------+
--  particle present.  Only one
--  Particle at a time! The state can either be _quarter under a card_ or _no quarter under a card_.


@[reducible]
/-                                        | Let's discuss what you are reading right now. This is source code, it is accepted by a Lean compiler,
ME: I need a source.                      | generates output on the screen that resembles a number that others have called _inexplicable_.  Does that
COMPILER: Source code?                    | make this _code_ inexplicable because it can compute an near neighbor of the number? Is the number being
ME: Source first. Code later.             | computed a near neighbor at all, or is the number just a post office box in a post office unrelated to
COMPILER: Then what is the source?        | the address the meaning lives at.
JAR JAR: MEESA! MEESA TRUE!               | Or does it live next door?
ME: The origin story. The physical thing  |
    that stores the information itself. --+ Godel thought they were the same. That if you mailed someone something, that they got it. Even next door.
-/
class SOURCE   -- Bullshit meter ≈ 1121. ----+ A font of knowledge. The part of the code that is context highlit, if that's your kink. The source of
    (Box: Type i) --                         | the marks is a made-up character of a made-up story. But what it marks is what is important. Some may
    (Pigeon: CarrierProcess Box) --          | read more into this sentence that I do. Which is fine, *YOU the KNOWER*, you will recognize some
    [DISTINGUISHABLE Box Pigeon] --          | things in this file and the next. Things that don't sound scientific at all. Because they come from a
    [ADMISSIBLE Box Pigeon] --               | place of known ignorance.
    [COUNTABLE Box Pigeon]
    [ENCODED Box Pigeon]
    [RESIDUE Box Pigeon]
    [BINARY Box Pigeon]
    [REPEATABLE Box Pigeon] --    | Having a character repeat whatever needs to be said in order to move the plot forward is a pattern that recurs
    [NUMERIC Box Pigeon] --       | when writing a proof. ∃ δ ∀ ε. A wart. A declaration. A fencepost in proofs. Over and over and over. Calculus is
    [REPRESENTABLE Box Pigeon]--  | absolutely brutal with this requirement. Every line of algebra written in a differential equation contains this
    [PHYSICAL Box Pigeon] --------+ geometric wart. At least the way *YOU the KNOWER* writes it. Or does Navier-Stokes eventually blow up? You tell
    [COMPARABLE Box Pigeon] --    | me. I mean water hammer is something else, but I doubt it will end the universe.
    [OBSERVED Box Pigeon] --      | *BANG* *BANG* *Bang* *bang*
    [PRESENT Box Pigeon] --       | Where have I seen .bang before? I have seen it PRIOR to now. Santa must bring more PRESENTs if I am good. And,
    [MEASURABLE Box Pigeon] --    | we are going to measure _why_ the compiled code and the examples I give seem to ring out as if struck by a
    [GUNGAN Box Pigeon] ----------+ water hammer.
  where
--    +--------------------------------------+ I dare not wade into the fidelity of the cd_process. Those who understand HOW the analog signal
--    |                                      | is absolutely BRUTALIZED by an ADC understand _WHY_ it is more than I can take. The second D of 3.
--    V
  cd_process : DigitalProcess Box Pigeon
  one : Equivalation ----------------------| Is the quarter under this one? Or that one? The compiler should be keeping up with this in a dictionary.

/- CHORUS:
COMPILER: I need a dictionary, did you take it?           | Sometimes words enter descriptions. Those words can be unfamiliar but carry a certain
JAR JAR: YOUSA BOMBAD! -----------------------------------+ _je ne sais quois?_ that hints at how much "upness" the word might contain. Je ne said
ME: No, just use the dictionary you have been building.   | nothing and you can quote me on that.
-/
inductive Encoding   -- Bullshit meter = 118.  Flat.
  | boot: Fact → Equivalation → Encoding
  | zero: Fact → Equivalation → Encoding → Encoding
  | one: Fact → Equivalation → Equivalation → Encoding → Encoding → Encoding

/-CHORUS:
ME: Look, I stop at high level languages. If you want the instruction set, you will have to look elsewhere.
-/

@[reducible]
/-
COMPILER: It takes electrons from the wall to make this work   | _TECHNICALLY SPEAKING_, the amount of bullshit the compiler has to cope with is
ME: I will try to help you pay for your own energy cost        | linearly related to the time it takes to compile the code which is linearly related
COMPILER: Energy? I only do math. Physics is your domain. -----+ to the amount of energy required to wade through the bullshit, which is linearly
JAR JAR: PHYSICS TRUE!                                         | related to mass.
ME: You turn physics into machinery that describes physics.
-/
structure CompiledProcess  -- Bullshit meter = 1728.  Almost 50% again.  Wow bullshit tends to accrete!
    (Box: Type i)
    (Pigeon: CarrierProcess Box) --
    [d: DISTINGUISHABLE Box Pigeon] --                    +=========================================================================================+
    [a: ADMISSIBLE Box Pigeon] --                         |                                                                                         |
    [c: COUNTABLE Box Pigeon] --                          |                            ----->>**YOUR AD HERE**<<-----                               |
    [e: ENCODED Box Pigeon] --                            |                                                                                         |
    [r: RESIDUE Box Pigeon] --                            |  BILLBOARDS WORK! WHO IS LOOKING AT BILLBOARDS? YOU ARE! REACH DOZENS OF INDIVIDUALS    |
    [b: BINARY Box Pigeon] --                             |                                                                                         |
    [f: REPEATABLE Box Pigeon] --                         |      Advertise your new theory here, in the compiled process. I will work with          |
    [n: NUMERIC Box Pigeon] --                            |     *YOU the KNOWER* to make sure _YOUR_ theory fits whatever words need to be          |
    [h: REPRESENTABLE Box Pigeon] --                      |      said to make the AD as organically placed as a TikTok influencer's!                |
    [p: PHYSICAL Box Pigeon] --                           |                                                                                         |
    [z: COMPARABLE Box Pigeon] --                         +-----------------------------------------------------------------------------------------+
    [particle: OBSERVED Box Pigeon] --                    | Email me: wkcochran@gmail.com. Reasonable rates. Contact for rate schedule. Prices      |
    [frequency: PRESENT Box Pigeon] --                    | subject change and market forces.                                                       |
    [what_meesa_saying: MEASURABLE Box Pigeon] --         +=========================================================================================+
    [zero: GUNGAN Box Pigeon] --
    [one: SOURCE Box Pigeon] --

  where
--                        +---------------------+ Why have a digital process at all? Why not analog? Well, it turns out that a LOT of analog
--                        |                     | configurations do not exist in reality. Take the water hammer and hit a cymbal as hard as you can.
--                        V                     | While you may "square out" the cymbal, you cannot "square out the wave." The wave is made of
  digital_process : DigitalProcess Box Pigeon --| atom-to-atom collisions and is best modeled as a square wave. Turns the infinite into the finite.

  source: SOURCE Box Pigeon -- <----+ The source code of the compiler as intpreted as an AST (see .tree above). Ever seen one? Or have you only ever
  opcodes: Encoding --              | made one? Opcodes are generated by the compiler. It gets this dictionary installed for each architecture.
--                                  | You know, the one it's been using this entire time.

  execute?: Encoding → Encoding := fun input => --+ The piece of hardware that normally iterates the opcodes is the Program Counter. It is a register
    match opcodes, input with --                  | on the computer's architecture almost always. Perhaps the most famous Program Counter is the cdr.
 --                                               +---------------------------------------------------------+ The cdr of LISP explains to the computer
    | .boot f _,  .boot g _      => match (f.truth ∧ g.truth) with --                                       | the _address_ of the next opcode. Which,
                                    | _ => .one f digital_process.zero digital_process.zero opcodes input --| as we have firmly established, will get
    | .boot f e, _               => .zero f e opcodes --                    +-------------------------------+ whatever mail Godel wishes to send it.
    | .zero f x1 e1, .zero g x2 e2 => match (f.truth ∧ g.truth) with --     |
                                    | _ => .one f x1 x2 e1 e2 --            | So, this description of the computational process is careful to be able
    | .zero f x e , _            => .zero f x e --                          | to sort out the opcodes that do not make sense. Those it interprets as
    | .one f _ _ _ _ , .one g _ x _ e => match (f.truth ∧ g.truth) with --  | _argument_ of the opcode. Think the simplest of all LISP machines.
                                    | _ => .zero f x e --                   |
    | .one f _ x _ e, _          => .zero f x e --                          | We are taking great care to sort the mail before we deliver it.

@[reducible]
/-                                                  | Source code exhibits a property very much like "upness," called _correctness_. The code does
COMPILER: I have produced yet another number        | such a good facsimile of the desired instructions that the actual instructions are deemed
JAR JAR: MEESA EXIT 1 ------------------------------+ correct.
ME: That zero looks very _1_ like to me.            |
-/ --                                               | Jar Jar makes that easier to see here.
class EXECUTED  -- Bullshit meter = 1158.  Calling this flat.
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [DISTINGUISHABLE Box Pigeon]               [ADMISSIBLE Box Pigeon]                  [COUNTABLE Box Pigeon]             [ENCODED Box Pigeon]
    [RESIDUE Box Pigeon]                       [BINARY Box Pigeon]                      [REPEATABLE Box Pigeon]            [NUMERIC Box Pigeon]
    [REPRESENTABLE Box Pigeon]                 [PHYSICAL Box Pigeon]                    [COMPARABLE Box Pigeon]            [OBSERVED Box Pigeon]
    [PRESENT Box Pigeon]                       [MEASURABLE Box Pigeon]                  [GUNGAN Box Pigeon]                [SOURCE Box Pigeon]
-- As I mentioned earlier, the number of partial specializations that will be appearing later numbers in the dozens and dozens. Partial and full
-- instantiations. The space above is going to become very valuable very soon as we cram more and more functionality into the template itself.
-- Perhaps future ad space? Hey, it's free real estate!

  where
--                           +------------------------+ The compiled process is another numeric representation of the source code. It is organized
--                           |                        | into a relatively efficient transliteration of the source code in such a way that one
--                           V                        | program on one computer is _NOT AT ALL GUARANTEED IN THE LEAST_ to generate the same output
  compiled_process : CompiledProcess Box Pigeon --    | on another computer.  Endianism alone is an obvious blocker to this. If you run this on your
--                                                    | machine you will get something different than I do. Your lcd screen changes instead of mine.
--                                                    | The mail must be delivered to the right screen.

  output? : Encoding → Encoding → Prop := fun opcode output=>
    match opcode,output with  --------------------------------------------+ ISA is not a strong point of mine. Be honest with you. Don't get me wrong,
    | .boot f _ , .boot g _ => f = g --                                   | I know more than the average bear, just not enough to be so flippant with
    | .boot _ _ , _ => false --                                           | the details.  I leave this for you to interpret. It is simple routing.
    | _ , .boot _ _ => false
    | .zero f _ _ , .zero g _ _ =>  f = g --------------------------------+ If the reference zeros aren't the same, not happening.
    | .zero _ _ _ , .one _ _ _ _ _ => false
    | .one _ _ _ _ _ , .zero _ _ _ => false
    | .one f _ e1 _ _ , .one g _ e2 _ _ => f.truth ∧ g.truth ∧ (e1 ≤ e2) --+ It isn't enough for the variance to match, it must also agree. Welcome
--                                                                         | to Diagon Alley. Seriously, Paul's Boutique has nothing on this code.

@[reducible]
/-
ME: I think it is time we talk about what is going on here.        | No kidding, this is a satire. We have now dealt with both situations, one
COMPILER: In the sense that you keep stacking templates as         | in which there is kidding (by selecting all kidding) and the empty slot
          if there were no consequences? --                        | condition for *YOU the KNOWER* who's patience is probably stretched really
ME: All kidding aside, this is a satire. It compiles, that's ------+ thin. No kidding.
    a fact. It executes is also a fact, a different one. It
    doesn't have to compile successfully. It always seems to
    execute.
JAR JAR: *blink* 1.
-/ --                                                                             | Before we get all denying the antecedent here, This fact,
inductive Abstraction  -- Bullshit meter = 2045.  About a 1/6 increase.           | _in theory_ could be false. I mean it can't be, but it
  | satire:  Fact → Abstraction --------------------------------------------------+ _could_ be. *YOU the KNOWER* might be laughing at some of this.

  | compile: Fact → Encoding → Abstraction → Abstraction -------+ This line models the likelihood that this all makes sense and is on a completely
  | execute: Fact → Encoding → Abstraction → Abstraction --     | different line from this, which models that the compiler won't crash reading it.
--                                                              | I don't know how else to differentiate them. Yet I plainly observe the difference.

namespace Abstraction   -- Bullshit meter = 2759.  This is a big jump, but that's because we couldn't compute ≤ on the above types.

def le : Abstraction → Abstraction → Prop := fun f1 f2 =>
  match f1,f2 with
  | .satire f1     , .satire f2      => f1 = f2
  | .satire f1     , .compile f2 _ _ => f1 = f2
  | .satire f1     , .execute f2 _ _ => f1 = f2
  | .compile f1 _ _, .satire f2      => f1 = f2
  | .execute f1 _ _, .satire f2      => f1 = f2
  | .compile _ _ _, .compile _ _ _ => true ----+ **BONG** the water hammer appears to have hit the sign convention. We squared of the symbols here
  | .compile _ _ _, .execute _ _ _ => true --  | to make it easier to see.
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


@[reducible]
/-
ME: I need a MathematicalProcess.

COMPILER: We already have computation.

ME: Computation follows the steps. Mathematics decides which steps are allowed to look inevitable.

COMPILER: That sounds like abstraction.

ME: With better manners.

COMPILER: What does it process?

ME: The difference between a trick and a theorem.
-/
structure MathematicalProcess  -- Bullshit meter = 2963.  That's about 2/3 increase.
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [DISTINGUISHABLE Box Pigeon]               [ADMISSIBLE Box Pigeon]                  [COUNTABLE Box Pigeon]             [ENCODED Box Pigeon]
    [RESIDUE Box Pigeon]                       [BINARY Box Pigeon]                      [REPEATABLE Box Pigeon]            [NUMERIC Box Pigeon]
    [REPRESENTABLE Box Pigeon]                 [PHYSICAL Box Pigeon]                    [COMPARABLE Box Pigeon]            [OBSERVED Box Pigeon]
    [PRESENT Box Pigeon]                       [MEASURABLE Box Pigeon]                  [GUNGAN Box Pigeon]                [SOURCE Box Pigeon]
    [EXECUTED Box Pigeon]
  where
  compiled_process: CompiledProcess Box Pigeon
  mapping: Abstraction → Abstraction

  -- lepidopterology
  calculate? : Abstraction → Abstraction := mapping


@[reducible]
/-
ME: I need a value.

COMPILER: Finally, a result.

ME: No. A thing that can survive being a result.

COMPILER: That sounds like a result.

ME: Results happen at the end. Values get carried through the machinery.

COMPILER: Carried where?

ME: Wherever the representation still recognizes its luggage.
-/
class VALUE  -- Bullshit meter = 3327.  3x increase!  That's a lot of bullshit!
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [DISTINGUISHABLE Box Pigeon]               [ADMISSIBLE Box Pigeon]                  [COUNTABLE Box Pigeon]             [ENCODED Box Pigeon]
    [RESIDUE Box Pigeon]                       [BINARY Box Pigeon]                      [REPEATABLE Box Pigeon]            [NUMERIC Box Pigeon]
    [REPRESENTABLE Box Pigeon]                 [PHYSICAL Box Pigeon]                    [COMPARABLE Box Pigeon]            [OBSERVED Box Pigeon]
    [PRESENT Box Pigeon]                       [MEASURABLE Box Pigeon]                  [GUNGAN Box Pigeon]                [SOURCE Box Pigeon]
    [EXECUTED Box Pigeon]

   where
   mathematical_process : MathematicalProcess Box Pigeon
   monad: Abstraction
   lt? : Abstraction → Abstraction → Prop := fun function output=>
     match function,output with
     | .satire _ , _  => false
     | _ , .satire _ => false
     | .compile _ _ _ , .compile _ _ _ => false
     | .compile _ _ _ , .execute _ _ _ => true
     | .execute _ _ _ , .compile _ _ _ => false
     | .execute _ _ a , .execute _ _ b => a < b



inductive Sum    -- Bullshit meter = 119.   Seems like that Abstraction bullshit doesn't stick around.  Probably should, though.
  | zero: Prop → Area → Sum
  | add: Fact → Area → Area → Sum → Sum

namespace Sum   -- Bullshit meter = 76.
def le: Sum → Sum → Prop := fun s1 s2 =>
  match s1, s2 with
  | .zero p1 a1, .zero p2 a2 => p1 = p2 ∧ a1 ≤ a2
  | .zero p1 _ , .add f2 _ a3 _ => match a3 with
                                | .tree _ => p1 ∧ f2.truth
                                | .dt _ _ _ => True
  | .add _ _ _ _, .zero _ _ => False
  | .add f1 a11 a12 _, .add f2 a21 a22 _ => (f1 = f2 ∧ a11 ≤ a21 ∧ a12 ≤ a22) ∨ (f1 ≠ f2 ∧ a21 ≤ a11 ∧ a22 ≤ a12)

-- Sums are well orderd.
def lt: Sum → Sum → Prop := fun s1 s2 => le s1 s2 ∧ ¬ le s2 s1
end Sum

instance : LE Sum := ⟨Sum.le⟩  -- Bullshit meter = 8
instance : LT Sum := ⟨Sum.lt⟩

@[reducible]
structure AddingProcess  -- Bullshit meter ≈ 2063.   Thats 33% less bullshit than a generic mathematical process!
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [this: DISTINGUISHABLE Box Pigeon] ---- *CLICKS*
                                               [ADMISSIBLE Box Pigeon]                  [COUNTABLE Box Pigeon]             [ENCODED Box Pigeon]
    [RESIDUE Box Pigeon]                       [BINARY Box Pigeon]                      [REPEATABLE Box Pigeon]            [NUMERIC Box Pigeon]
    [REPRESENTABLE Box Pigeon]                 [PHYSICAL Box Pigeon]                    [COMPARABLE Box Pigeon]            [OBSERVED Box Pigeon]
    [gifts: PRESENT Box Pigeon] ---- *STATIC*
                                               [MEASURABLE Box Pigeon]                  [GUNGAN Box Pigeon]                [SOURCE Box Pigeon]
    [EXECUTED Box Pigeon]                      [VALUE Box Pigeon]

  where

  bays_process : MathematicalProcess Box Pigeon
  plus: VALUE Box Pigeon --                      +------+-------------------------------+----+ The art of re-gifting is a time honored tradition
  sum: Sum --                                    |      |                               |    | whereby the same fruit cake manufactured in the early
  add? : Sum → Sum := fun s => --                |      |        +-------+--------------+    | seventies, wrapped in festive green and red
    match s with --                              |      |        |       |                   | cellophane would change hands among the fringes of
    | .zero p a => match p with --               V      V        V       V                   | communication cliques and survive with a half-life
      | _ => .add Fact.Truth (.tree this.fact) (.dt this.fact (.zero this.fact) a) sum --    | measured in ages of time.
--                               ^      ^                                                    |
--                               |      |                                                    | Just handing over cellophane, though, is tacky. The art
--                               +------+----------------------------------------------------+ is to put it in a new box and wrap it yourself.

    | .add f _ a2 _ => .add f a2 gifts.santa_claus.accumulation sum ---+ And as long as *YOU the KNOWER* were good and having a prior lot drawn that
--                                           ^                         | assembles you into the group of receivers of the carrier of Santa's presents,
--                                           |                         | Rudolph, himself. If you were not a receiver of Rudolph, then the accumulation
--                                           +-------------------------+ was not presented to *YOU the READER*, as *YOU the KNOWER* have received none
--                                                                     | _PRIOR_. I still think you understand the _concept_ of Santa Claus, if not
--                                                                     | the total lack of egalitarianism. Thing is, you can't possibly know how many
/- CHORUS:                                                             | gifts are on Santa's sleigh, only how many he gives you.
ME: How big is one?            | unsigned integer, 32 bits.            |
JAR JAR: MEESA KNOW!           | double, 64 bits.                      | If you receive no gifts, are you naughty or is it just because Santa has
COMPILER: Go ahead Jar Jar     | #define FALSE 1  (I feel like we      | never visited you before? Some say it has something to do with religion,
JAR JAR: ONE! -----------------+   discussed sign convention           | but no world religion speaks of a man that lives at the north pole.
COMPILER: Sorry, best I got.   |   already.)                           |
-/ --                                                                  | The man Maxwell spoke of North and Poles and of their exclusive existence.
@[reducible]
class MAGNITUDE  -- Bullshit meter ≈ 1503.  That's less than 1/2 the bullshit of a value! The other half must be the orientation.
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [DISTINGUISHABLE Box Pigeon]               [ADMISSIBLE Box Pigeon]                  [COUNTABLE Box Pigeon]             [ENCODED Box Pigeon]
    [RESIDUE Box Pigeon]                       [BINARY Box Pigeon]                      [REPEATABLE Box Pigeon]            [NUMERIC Box Pigeon]
    [REPRESENTABLE Box Pigeon]                 [PHYSICAL Box Pigeon]                    [COMPARABLE Box Pigeon]            [OBSERVED Box Pigeon]
    [PRESENT Box Pigeon]                       [MEASURABLE Box Pigeon]                  [GUNGAN Box Pigeon]                [SOURCE Box Pigeon]
    [EXECUTED Box Pigeon]                      [VALUE Box Pigeon]
    where
--                       +--------------------+ This is a very specialized adding process. It is not possible to add arbitrary numbers. Adding is
--                       |                    | a process where the count of one process is "added" to the other by running the processes back to
--                       V                    | back. Like when measuring the magnitude of a vector (remember the Hilbert space we are making).
  adding_process : AddingProcess Box Pigeon --| We need to start thinking about what it means tp be a normed IPS.
  whelmed? : Sum → Sum → Prop := fun a b =>
        match a, b with
        -- Two origins can only dominate if their underlying propositions agree
        | .zero p1 _       , .zero p2 _       => p1 ∧ p2

        -- An origin can NEVER dominate an accumulated timeline. Time moved on.
        | .zero _  _       , .add _ _ _ _     => False

        -- An accumulated timeline ALWAYS dominates an origin, provided its fact is true
        | .add f1 _ _ _    , .zero p2 _       => f1.truth ∧ p2

        -- When two timelines collide, we check covariance/contravariance of their facts
        | .add f1 a11 _ _, .add f2 a21 _ _ =>  ----------------------------+ Either we are adding or de-adding. Variance lets us know what is
            (f1 = f2 ∧ a11 ≤ a21) ∨ (f1 ≠ f2 ∧ a21 ≤ a11) --               | happening. Like when you take 1 and add 3 then de-add 1. See full circle.

inductive Product  -- Bullshit meter = 119
  | origin:  Fact → Product
  | one: Prop → Sum → Product
  | mul: Fact → Sum → Sum → Product → Product

namespace Product  -- Bullshit meter = 75
def le: Product → Product → Prop := fun p1 p2 =>
  match p1, p2 with
  -- 1. The Vacuum State (Absolute Origin)
  | .origin f1, .origin f2 => f1 = f2
  | .origin _, .one _ _ => True          -- 0 is always ≤ a positive base magnitude
  | .origin _, .mul _ _ _ _ => True      -- 0 is always ≤ a growing spatial volume

  -- 2. Looking Back at the Vacuum (Negative Scaling)
  | .one p1 _, .origin f2 => p1 ≠ f2.truth         -- A base unit is only ≤ 0 if it has inverted parity (-1 ≤ 0)
  | .mul f1 _ _ _, .origin f2 => f1.truth ≠ f2.truth -- A scaled volume is only ≤ 0 if it is inverted (-X ≤ 0)

  -- 3. Base Magnitude (The "1" Vector)
  | .one p1 a1, .one p2 a2 => p1 = p2 ∧ a1 ≤ a2
  | .one p1 a1, .mul f2 a21 _ _ => p1 = f2.truth ∧ a1 ≤ a21

  -- 4. Scaled Volume Looking Back at Base Magnitude
  | .mul f1 _ _ _, .one p2 _ => f1.truth ≠ p2      -- A scaled volume is only ≤ 1 if it is inverted (-X ≤ 1)

  -- 5. The Antimatter Flip (Scaled vs. Scaled)
  | .mul f1 a11 a12 _, .mul f2 a21 a22 _ =>
      (f1 = f2 ∧ a11 ≤ a21 ∧ a12 ≤ a22) ∨          -- Covariant: Facts agree, spatial boxes grow normally
      (f1 ≠ f2 ∧ a21 ≤ a11 ∧ a22 ≤ a12)            -- Contravariant: Strain inverts the geometry (-X ≥ -Y)

def lt: Product → Product → Prop := fun p1 p2 => le p1 p2 ∧ ¬ le p2 p1
end Product

instance : LE Product := ⟨Product.le⟩  -- Bullshit meter = 5
instance : LT Product := ⟨Product.lt⟩

@[reducible]
structure MultiplyingProcess  -- Bullshit meter = 2157  5% increase.  Call that flat response over the AddingProcess.
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [this: DISTINGUISHABLE Box Pigeon] -- *CLICKS*
                                               [ADMISSIBLE Box Pigeon]                [COUNTABLE Box Pigeon]                 [ENCODED Box Pigeon]
    [RESIDUE Box Pigeon]                       [BINARY Box Pigeon]                    [REPEATABLE Box Pigeon]                [NUMERIC Box Pigeon]
    [REPRESENTABLE Box Pigeon]                 [PHYSICAL Box Pigeon]                  [COMPARABLE Box Pigeon]                [OBSERVED Box Pigeon]
    [PRESENT Box Pigeon]                       [MEASURABLE Box Pigeon]                [GUNGAN Box Pigeon]                    [SOURCE Box Pigeon]
    [EXECUTED Box Pigeon]                      [VALUE Box Pigeon]                     [MAGNITUDE Box Pigeon]

  where
  adding_process : AddingProcess Box Pigeon
  total: Sum
  product: Product
-- The engine of spatial scaling
  multiply? : Product → Product := fun p =>
    match p with
    -- 1. The Big Bang: The vacuum state is seeded with the first tick of time.
    | .origin f   => .one f.truth (.zero this.fact.truth (.tree this.fact))

    -- 2. The First Dimension: The base unit expands into a bounding box.
    -- It is bounded by its origin 'a' and the CURRENT time 'adding_process.sum'.
    | .one _ a => .mul Fact.Truth a adding_process.sum p

    -- 3. Scaling Space: To multiply an existing volume, you stretch its leading edge.
    -- You keep the anchor 'a1', but force the leading edge 'a2' to move forward
    -- in time using the adding_process!
    | .mul f a1 a2 _ => .mul f a1 (adding_process.add? a2) p

@[reducible]
class SCALED  -- Bullshit meter = 1756
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [DISTINGUISHABLE Box Pigeon]               [ADMISSIBLE Box Pigeon]                [COUNTABLE Box Pigeon]                 [ENCODED Box Pigeon]
    [RESIDUE Box Pigeon]                       [BINARY Box Pigeon]                    [REPEATABLE Box Pigeon]                [NUMERIC Box Pigeon]
    [REPRESENTABLE Box Pigeon]                 [PHYSICAL Box Pigeon]                  [COMPARABLE Box Pigeon]                [OBSERVED Box Pigeon]
    [PRESENT Box Pigeon]                       [MEASURABLE Box Pigeon]                [GUNGAN Box Pigeon]                    [SOURCE Box Pigeon]
    [EXECUTED Box Pigeon]                      [VALUE Box Pigeon]                     [MAGNITUDE Box Pigeon]
  where
  multiplying_process : MultiplyingProcess Box Pigeon
  orthogonal? : Product → Product → Prop := fun p1 p2 =>
      match p1, p2 with
      -- 1. The Vacuum (Zero Vector) is orthogonal to everything
      | .origin _, _ => True
      | _, .origin _ => True

      -- 2. Base Dimensions are orthogonal if they occupy different moments in time
      | .one _ a1, .one _ a2 => a1 ≠ a2

      -- 3. The Destructive Interference of Strain
      -- Scaled volumes are orthogonal if they don't share a temporal leading edge,
      -- OR if their metric signatures (Facts) clashing completely destroys the space.
      | .mul f1 _ a12 _, .mul f2 _ a22 _ =>
          (a12 ≠ a22) ∨ (f1.truth ≠ f2.truth)

      -- 4. Cross-dimensional checks
      | .one _ a1, .mul _ _ a22 _ => a1 ≠ a22
      | .mul _ _ a12 _, .one _ a2 => a12 ≠ a2

-- Dyson vacuums are _so-so_.  Dyson series, on the other hand?
inductive Basis   -- Bullshit meter = 134
  | null_space: Fact → Basis
  | origin: Prop → Product → Basis
  | basis: Fact → Product → Product → Basis → Basis
-- Surely you're joking Mr. Henry!

namespace Basis  -- Bullshit meter = 82
def le: Basis → Basis → Prop := fun b1 b2 =>
  match b1, b2 with
  -- 1. The True Vacuum (Null Space)
  | .null_space f1, .null_space f2 => f1 = f2
  | .null_space _, .origin _ _ => True          -- The vacuum can evolve into a theoretical state
  | .null_space _, .basis _ _ _ _ => True       -- The vacuum can be excited into a field

  -- 2. Annihilation (Looking back into the Void)
  -- A state can only collapse back into the vacuum if its parity is inverted (Informational Strain)
  | .origin p1 _, .null_space f2 => p1 ≠ f2.truth
  | .basis f1 _ _ _, .null_space f2 => f1.truth ≠ f2.truth

  -- 3. The Theoretical Seed (Prop) vs Reality (Fact)
  | .origin p1 s1, .origin p2 s2 => p1 = p2 ∧ s1 ≤ s2
  | .origin p1 s1, .basis f2 s21 _ _ => p1 = f2.truth ∧ s1 ≤ s21

  -- 4. Reality Looking Back at Theory
  | .basis f1 _ _ _, .origin p2 _ => f1.truth ≠ p2

  -- 5. The S-Matrix Interaction Vertex (Field vs Field)
  -- If the coupling constants (Facts) agree, the spatial products scale covariantly.
  -- If the coupling constants disagree, the interaction produces antimatter, inverting the spatial boundaries!
  | .basis f1 p11 p12 _, .basis f2 p21 p22 _ =>
      (f1 = f2 ∧ p11 ≤ p21 ∧ p12 ≤ p22) ∨
      (f1 ≠ f2 ∧ p21 ≤ p11 ∧ p22 ≤ p12)

def lt: Basis → Basis → Prop := fun b1 b2 => le b1 b2 ∧ ¬ le b2 b1
end Basis

instance : LE Basis where
  le := Basis.le

instance : LT Basis where
  lt := Basis.lt

@[reducible]
structure BASICProcess  -- Bullshit meter ≈ 2759
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [DISTINGUISHABLE Box Pigeon]               [ADMISSIBLE Box Pigeon]                [COUNTABLE Box Pigeon]                 [ENCODED Box Pigeon]
    [RESIDUE Box Pigeon]                       [BINARY Box Pigeon]                    [REPEATABLE Box Pigeon]                [NUMERIC Box Pigeon]
    [REPRESENTABLE Box Pigeon]                 [PHYSICAL Box Pigeon]                  [COMPARABLE Box Pigeon]                [OBSERVED Box Pigeon]
    [PRESENT Box Pigeon]                       [MEASURABLE Box Pigeon]                [GUNGAN Box Pigeon]                    [SOURCE Box Pigeon]
    [EXECUTED Box Pigeon]                      [VALUE Box Pigeon]                     [MAGNITUDE Box Pigeon]         [spring: SCALED Box Pigeon]
  where
  GOSUB: MultiplyingProcess Box Pigeon     -- <-- I think I found the gosub
  TEN: Area                                   -- <-- and a line number!
  span: Basis

  jmp? : Basis → Basis := fun b =>
    match b with
    -- 1. Segfault in the Vacuum
    -- You cannot jump from the null space. There is no geometry to push off of.
    | .null_space f => .null_space f

    -- 2. GOTO: The Scattering Event
    -- A theoretical base state (.origin) abruptly collapses into a new field geometry.
    -- Notice the tail is strictly .null_space. There is no return address.
    -- The timeline ends after this interaction.
    | .origin _ p_current =>
        .basis Fact.Truth p_current spring.multiplying_process.product (.null_space Fact.Truth) -- Go go gadget Springs!

    -- 3. GOSUB: The Virtual Loop (Feynman Propagator)
    -- An ongoing field interaction (.basis) needs to process a fluctuation.
    | .basis f _ _ tail =>
        match f.truth with
        -- COVARIANT (Normal execution step):
        -- Just step forward, no branching.
        | _  => tail


@[reducible]
class LOAD  -- Bullshit meter 2089
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [DISTINGUISHABLE Box Pigeon]               [ADMISSIBLE Box Pigeon]                  [COUNTABLE Box Pigeon]             [ENCODED Box Pigeon]
    [RESIDUE Box Pigeon]                       [BINARY Box Pigeon]                      [REPEATABLE Box Pigeon]            [NUMERIC Box Pigeon]
    [REPRESENTABLE Box Pigeon]                 [PHYSICAL Box Pigeon]                    [COMPARABLE Box Pigeon]            [OBSERVED Box Pigeon]
    [PRESENT Box Pigeon]                       [MEASURABLE Box Pigeon]                  [GUNGAN Box Pigeon]                [SOURCE Box Pigeon]
    [SOURCE Box Pigeon]                        [EXECUTED Box Pigeon]                    [VALUE Box Pigeon]                 [MAGNITUDE Box Pigeon]
    [SCALED Box Pigeon]

  where
  basic_operation : BASICProcess Box Pigeon
  --  Is this an eigenvector?
  decoded? : Basis → Basis → Prop := fun b1 b2 =>
    match b1, b2 with
    -- 1. The Void carries no signal
    | .null_space _, .null_space _ => False
    | .null_space _, .origin _ _ => False
    | .null_space _, .basis _ _ _ _ => False

    -- 2. Pair Annihilation (Emitting a Load into the Vacuum)
    -- If a field collapses into the vacuum under contravariant strain,
    -- the friction of that annihilation emits a measurable load (like a photon).
    | .origin t _, .null_space f => t ≠ f.truth
    | .basis f1 _ _ _, .null_space f2 => f1.truth ≠ f2.truth

    -- 3. The Clock (Superposition Strain)
    | .origin t _, .origin f _ => t ≠ f
    | .origin t _, .basis f _ _ _ => t ≠ f.truth

    -- 4. Causality Constraint
    | .basis _ _ _ _, .origin _ _ => False

    -- 5. The Macroscopic Lock-In Amplifier (Field vs Field)
    -- f1 ≠ f2: Contravariant metric signature (Voltage/Friction exists)
    -- p1_out ≤ p2_out: The exiting geometry of the first causally sequences
    --                  into the exiting geometry of the second.
    | .basis f1 _ p1_out _, .basis f2 _ p2_out _ =>
        f1 ≠ f2 ∧ p1_out ≤ p2_out

inductive Polynomial    --  Bullshit meter 119
  | constant: Fact → Polynomial
  | monomial: Prop → Basis → Polynomial
  | factor: Fact → Basis → Basis → Polynomial → Polynomial

namespace Polynomial
def le: Polynomial → Polynomial → Prop := fun p1 p2 =>
  match p1, p2 with
  -- 1. Constants compare by their metric signature
  | .constant f1, .constant f2 => f1 = f2
  | .constant _, .monomial _ _ => True
  | .constant _, .factor _ _ _ _ => True

  -- 2. Monomials (Pure States)
  -- A pure state is less than a factored state if its phase matches the coupling sign
  | .monomial t1 _,  .constant t2  => t1 = t2.truth
  | .monomial t1 b1, .monomial t2 b2 => t1 = t2 ∧ b1 ≤ b2
  | .monomial t1 _, .factor f2 _ _ _ => t1 = f2.truth

  -- 3. The Collision (Factor vs Factor)
  -- This is the "Strain Matrix". If the coupling facts (f1, f2) disagree,
  -- the inequality inverts, representing destructive interference!
  | .factor f1 b11 b12 _, .factor f2 b21 b22 _ =>
      (f1 = f2 ∧ b11 ≤ b21 ∧ b12 ≤ b22) ∨
      (f1 ≠ f2 ∧ b21 ≤ b11 ∧ b22 ≤ b12)
  | .factor f1 _ _ _,  .constant f2 => f1 = f2
  | .factor f1 _ _ _,  .monomial f2 _ => f1.truth = f2
end Polynomial

instance : LE Polynomial where
  le := Polynomial.le


@[reducible]
structure GalerkinProcess   -- Bullshit meter 2794
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [DISTINGUISHABLE Box Pigeon]               [ADMISSIBLE Box Pigeon]                  [COUNTABLE Box Pigeon]             [ENCODED Box Pigeon]
    [RESIDUE Box Pigeon]                       [BINARY Box Pigeon]                      [REPEATABLE Box Pigeon]            [NUMERIC Box Pigeon]
    [REPRESENTABLE Box Pigeon]                 [PHYSICAL Box Pigeon]                    [COMPARABLE Box Pigeon]            [OBSERVED Box Pigeon]
    [PRESENT Box Pigeon]                       [MEASURABLE Box Pigeon]                  [GUNGAN Box Pigeon]                [SOURCE Box Pigeon]
    [SOURCE Box Pigeon]                        [EXECUTED Box Pigeon]                    [VALUE Box Pigeon]                 [MAGNITUDE Box Pigeon]
    [SCALED Box Pigeon]                        [LOAD Box Pigeon]

  where
  ANSYS_process : BASICProcess Box Pigeon
  polynomial : Polynomial

  scale_and_shift? : Polynomial → Polynomial := fun p =>
    match p with
    -- 1. Shifting the Ground State (The "Zero" case)
    -- We transition the background radiation into a theoretical field state.
    | .constant f => .monomial f.truth (.null_space f)

    -- 2. Scaling a Pure State
    -- We take a monomial and promote it to an interaction (a factor).
    -- We use the current basis as the anchor and jump the state forward.
    | .monomial _ b =>
        .factor Fact.Truth b (ANSYS_process.jmp? b) p

    -- 3. The Recursive Scale (The "Add" case)
    -- We maintain the coupling 'f', the anchor 'b1',
    -- but we 'shift' the interacting basis 'b2' and preserve the history.
    | .factor f _ b2 tail =>
        .factor f b2 (ANSYS_process.jmp? b2) tail

-- Let's address the _elephant in the room_.  First, let's agree that it is _SINGULAR_ and that it is only _SO BIG_.
-- It can get really, really, __REALLY__ big in just a few keystrokes.  That's the problem.  We have only
-- one stack frame, our __FINITE_ELEPHANT__.
@[reducible]
class FINITE_ELEPHANT   -- 2368

    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [DISTINGUISHABLE Box Pigeon]     -- So, she _ASSUMES_ they have an undocumented one and proceed to add the release.
    [ADMISSIBLE Box Pigeon]          -- Only to realize she can't _EXACTLY_ find the _RIGHT_ release of their media to catalog.
    [COUNTABLE Box Pigeon]           -- And spends hours every day on DISCOGS organizing her collection.
    [ENCODED Box Pigeon]             -- The audiophile purchases the finest copies of any analog recordings.
    [RESIDUE Box Pigeon]             -- The audiophile meticulously cleans her records.
    [BINARY Box Pigeon]              -- Invariably, there will be two camps.  The _AUDIOPHILE_ and the _NORMIE_.
    [REPEATABLE Box Pigeon]          -- And I can burn the output of the DAC to a CD?  Holy crap!
    [NUMERIC Box Pigeon]             -- How about that, I just built a DAC !?
    [REPRESENTABLE Box Pigeon]       -- Which means I can quantize and take the DFT!
    [PHYSICAL Box Pigeon]            -- I just know that what I hear is measured by this physical process of oscillations.
    [COMPARABLE Box Pigeon]          -- Dunno what they mean though.
    [OBSERVED Box Pigeon]     -- There we are, I found some phonemes.
    [PRESENT Box Pigeon]     -- Fucking Jar Jar. Let me use an osciliscope and measure their tones and figure it out.
    [MEASURABLE Box Pigeon]  -- MEESA TRUE!
    [GUNGAN Box Pigeon]           -- Translate that into Gungan and ask Jar Jar Binks if he can relate to it?
    [SOURCE Box Pigeon]            -- To quote Johnny Five: "NEED INPUT!"  Doesn't matter what kind.
    [EXECUTED Box Pigeon]       -- Actually, I take that back, we have a program that can compute the value from an input
    [VALUE Box Pigeon]           -- No, just some sort of representation of the value.
    [MAGNITUDE Box Pigeon]      -- And this the length?   Do we have _e^iθ_?
    [SCALED Box Pigeon]         -- Could this possibly represent the direction of said load?
    [LOAD Box Pigeon]         -- hmmm, a _LOAD_?  Like _μ_ __N__?
--     ^                            ^
--     |                            |       +------------- Just this once, let's read it ^ this way.
--     +--------+-------------------+       |
--              |                           |
--              +---------------------------+


  where
  galerkin_process : GalerkinProcess Box Pigeon
  finite? : Polynomial → Polynomial → Prop := fun p1 p2 =>
    match p1, p2 with
    -- 1. Convergence to the Ground State
    -- If we move from any field interaction to a constant, the transform is finite.
    -- The energy has successfully dissipated into the background.
    | _, .constant _ => True

    -- 2. Stationary Field (The Eigenvalue Hit)
    -- If the transform results in the exact same theoretical state, we've found
    -- a fixed point in the Hilbert space. The arm-waving has stopped.
    | .monomial t1 b1, .monomial t2 b2 => t1 = t2 ∧ b1 = b2

    -- 3. The Lanczos Residual Check
    -- If we are moving between interactions (factors), the transform is only
    -- finite if the informational strain (Fact) remains invariant.
    -- If the Fact flips, the transform is "infinite" (a singularity/jump).
    | .factor f1 _ _ _, .factor f2 _ _ _ => f1 = f2

    -- 4. The Divergence
    -- Moving from a grounded constant back into an excited factor is
    -- an "infinite" injection of energy. Disallow for convergence.
    | .constant _, .factor _ _ _ _ => False
    | .constant _, .monomial _ _ => False

    -- 5. Cross-talk
    | .monomial t1 _, .factor f2 _ _ _ => t1 = f2.truth
    | .factor f1 _ _ _, .monomial t2 _ => f1.truth = t2



-- reticulate, damn you!
inductive Spline  -- 152
  | observation: Prop → Spline
  | knot: Prop → Polynomial → Spline → Spline
  | interpolant: Fact → Polynomial → Polynomial → Spline → Spline → Spline


namespace Spline

def le : Spline → Spline → Prop := fun s1 s2 =>
  match s1, s2 with
  -- 1. Observation (The Ground State)
  -- An observation is the "unit" of the manifold.
  -- It is less than any knot because a knot is an observation PLUS work.
  | .observation t1, .observation t2 => t1 = t2
  | .observation _, .knot _ _ _ => True
  | .observation _, .interpolant _ _ _ _ _ => True

  -- 2. The Knot (The First Variation)
  -- A knot is a localized field interaction.
  -- It is contained by another knot if their phases match
  -- and their internal polynomials/histories are ordered.
  | .knot t1 p1 tail1, .knot t2 p2 tail2 =>
      t1 = t2 ∧ p1 ≤ p2 ∧ (le tail1 tail2)

  -- 3. The Interpolant (The Second Variation / The Weak Derivative)
  -- This is the "Inverse Gauss" arm.
  -- An interpolant contains a knot if the knot's polynomial
  -- satisfies the weak boundary conditions of the interpolation.
  | .knot t1 p1 _, .interpolant f2 p_in p_out _ _ =>
      t1 = f2.truth ∧ p1 ≤ p_in ∧ p1 ≤ p_out

  -- 4. Interpolant vs Interpolant (The Manifold Convergence)
  -- This is the Cauchy check. s1 ≤ s2 if s1 is a sub-path of the
  -- geodesic defined by s2.
  | .interpolant f1 i1 o1 left1 right1, .interpolant f2 i2 o2 left2 right2 =>
      f1 = f2 ∧ i1 ≤ i2 ∧ o1 ≤ o2 ∧ (le left1 left2) ∧ (le right1 right2)

  -- 5. Disallow Retrocausality
  -- A complex interpolation cannot be contained within a simple observation.
  | .knot _ _ _, .observation _ => False
  | .interpolant _ _ _ _ _, .observation _ => False
  | .interpolant _ _ _ _ _, .knot _ _ _ => False

end Spline

instance : LE Spline where
  le := Spline.le


end Measurement
