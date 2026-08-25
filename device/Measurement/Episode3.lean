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
    [DISTINGUISHABLE Box Pigeon] --                    +=========================================================================================+
    [ADMISSIBLE Box Pigeon] --                         |                                                                                         |
    [COUNTABLE Box Pigeon] --                          |                            ----->>**YOUR AD HERE**<<-----                               |
    [ENCODED Box Pigeon] --                            |                                                                                         |
    [RESIDUE Box Pigeon] --                            |  BILLBOARDS WORK! WHO IS LOOKING AT BILLBOARDS? YOU ARE! REACH DOZENS OF INDIVIDUALS!   |
    [BINARY Box Pigeon] --                             |                                                                                         |
    [REPEATABLE Box Pigeon] --                         |      Advertise your new theory here, in the compiled process. I will work with          |
    [NUMERIC Box Pigeon] --                            |     *YOU the KNOWER* to make sure _YOUR_ theory fits whatever words need to be          |
    [REPRESENTABLE Box Pigeon] --                      |      said to make the AD as organically placed as a TikTok influencer's!                |
    [PHYSICAL Box Pigeon] --                           |                                                                                         |
    [COMPARABLE Box Pigeon] --                         +-----------------------------------------------------------------------------------------+
    [OBSERVED Box Pigeon] --                           | Email me: wkcochran@gmail.com. Reasonable rates. Contact for rate schedule. Prices      |
    [PRESENT Box Pigeon] --                            | subject change and market forces.                                                       |
    [MEASURABLE Box Pigeon] --                         +=========================================================================================+
    [GUNGAN Box Pigeon] --
    [SOURCE Box Pigeon] --

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
  | satire_about:  Fact → Abstraction --------------------------------------------+ _could_ be. *YOU the KNOWER* might be laughing at some of this.

  | compile: Fact → Encoding → Abstraction → Abstraction -------+ This line models the likelihood that this all makes sense and is on a completely
  | execute: Fact → Encoding → Abstraction → Abstraction --     | different line from this, which models that the compiler won't crash reading it.
--                                                              | I don't know how else to differentiate them. Yet I plainly observe the difference.

namespace Abstraction   -- Bullshit meter = 2759.  This is a big jump, but that's because we couldn't compute ≤ on the above types.

def le : Abstraction → Abstraction → Prop := fun f1 f2 =>
  match f1,f2 with
  | .satire_about f1     , .satire_about f2      => f1 = f2
  | .satire_about f1     , .compile f2 _ _ => f1 = f2
  | .satire_about f1     , .execute f2 _ _ => f1 = f2
  | .compile f1 _ _      , .satire_about f2      => f1 = f2
  | .execute f1 _ _      , .satire_about f2      => f1 = f2
  | .compile _ _ _       , .compile _ _ _ => true ----+ **BONG** the water hammer appears to have hit the sign convention. We squared of the symbols here
  | .compile _ _ _       , .execute _ _ _ => true --  | to make it easier to see.
  | .execute _ _ _       , .execute _ _ _ => true
  | .execute _ _ _       , .compile _ _ _ => false

def lt: Abstraction → Abstraction → Prop := fun f1 f2 =>
  match f1,f2 with
  | .satire_about _, _ => false
  | _, .satire_about _ => false
  | .compile _ _ _, .compile _ _ _ => false
  | .compile _ _ _, .execute _ _ _ => true
  | .execute _ _ a, .execute _ _ b => lt a b
  | .execute _ _ _, .compile _ _ _ => false
end Abstraction

/- CHORUS:
ME: Give me the smallest number that...             | The absolute: Good/Bad
COMPILER: Let me stop you right there. What do      | The comparative: Better/Worse
          you mean smallest? What is -est?          | The absolute comparative: Most/(¬ Most)
JAR JAR: MEESA YOOSA SMALLSA -----------------------+
ME: Try not to segfault.
-/
instance    -- Bullshit meter = 579 !!  that is a 60x increase!  Hmmm...
 : LE Abstraction := ⟨Abstraction.le⟩

-- This "abstracts" the < operation to prevent self reference paradoxes.  Consider the Berry Paradox: "The smallest positive integer not definable in
-- under eleven words".  If you can define it, then it is not the smallest positive integer not definable in under eleven words.  If you cannot
-- define it, then it is the smallest positive integer not definable in under eleven words.  This is a paradox.

-- The solution to the paradox in the device is to realize that "under eleven words" is a computation, a Python program, a neighbor of a Lean program
-- that runs in a fixed amount of time. And while the description of the numerals fail to materialize, Berry's Number _is_ the smallest positive
-- integer with such properties. And, a computer can be used to verify the claim. And that claim is a Fact of the system, if not a truth that can be
-- obtained. There are _fewer_ than eleven words in the Berry paradox.
instance
 : LT Abstraction := ⟨Abstraction.lt⟩


/-
ME: Our number apparently has a max number of words in the description.  | The Berry number of 11 is a _RESIDUE_ of language. Other languages may
COMPILER: You mean a _minimum_, at least 1 word.                         | need more than 11 words. Others, fewer. The number 11 is neither here
JAR JAR: 1 WORD. --------------------------------------------------------+ nor there. It is this _that_ to that _this_. You only need 1 really long
ME: I don't have enough money for unlimited words.                       | word.
-/
structure MathematicalProcess  -- Bullshit meter = 2963.
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [DISTINGUISHABLE Box Pigeon]               [ADMISSIBLE Box Pigeon]                  [COUNTABLE Box Pigeon]             [ENCODED Box Pigeon]
    [RESIDUE Box Pigeon]                       [BINARY Box Pigeon]                      [REPEATABLE Box Pigeon]            [NUMERIC Box Pigeon]
    [REPRESENTABLE Box Pigeon]                 [PHYSICAL Box Pigeon]                    [COMPARABLE Box Pigeon]            [OBSERVED Box Pigeon]
    [PRESENT Box Pigeon]                       [MEASURABLE Box Pigeon]                  [GUNGAN Box Pigeon]                [SOURCE Box Pigeon]
    [EXECUTED Box Pigeon]
  where
--                        +---------------------+ There is often need to obfuscate the code that is being executed. The way the code is computed is
--                        |                     | a _secret_.  Like how Rudolph manages to fly Santa's sleigh on Christmas. No one can explain _how_
--                        V                     | it works, we just know that when Rudolph runs, PRESENTs arrive.
  compiled_process: CompiledProcess Box Pigeon

  mapping: Abstraction → Abstraction -----------| Um. Yeah. What this says. Literally.

  calculate? : Abstraction → Abstraction := mapping ---| Um. Yeah. Do the thing that makes PRESENTs.

-- Abstractions are useful to the extent they _explain things_. Just like _source code_. Just like _mathematical theorems_. There are letters that
-- just _mean_ things now. _e_, the eigenfunction of the derivative, is literally called _e_ because _Euler_ figuered that out. It was Euler who
-- figured out that _1_ was the function that defined _e_: 1(i) = -e^πi. I think *YOU the KNOWER* might recognize that glyph better as _-r_, the
-- actual measurable length, is _1_ and length is the function we have at our fingertips. How long is something? Well, accoring to Jar Jar, just 1.
-- Remember how lazy compilers are? Well, they have no idea how much work their assumptions mask.
/-
ME: I need a value.                                                      | *YOU the KNOWER* will explain that they allow Lean to have at least one
COMPILER: Funny enough, I think there is one around here somewhere.      | kind of value, a Nat. Then, they incorrectly assume that inductives count
JAR JAR: MEESA ONE! -----------------------------------------------------+ natural numbers. They do not. They count computations. That should be
ME: I don't know if I need _that_ many numbers.                          | very plain from this construction at this point. This is called an
COMPILER: Get it? --                                                     | _argument_, *YOU the READER*, and it will not be proven _TRUE_, it will be
-/ --                                                                    | demonstrated as a Fact. A Fact about a letter we have already agreed is
class VALUE  -- Bullshit meter = 3327.                                   | Greek. The ISO character set used by the compiler verifies that fact.
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [DISTINGUISHABLE Box Pigeon]               [ADMISSIBLE Box Pigeon]                  [COUNTABLE Box Pigeon]             [ENCODED Box Pigeon]
    [RESIDUE Box Pigeon]                       [BINARY Box Pigeon]                      [REPEATABLE Box Pigeon]            [NUMERIC Box Pigeon]
    [REPRESENTABLE Box Pigeon]                 [PHYSICAL Box Pigeon]                    [COMPARABLE Box Pigeon]            [OBSERVED Box Pigeon]
    [PRESENT Box Pigeon]                       [MEASURABLE Box Pigeon]                  [GUNGAN Box Pigeon]                [SOURCE Box Pigeon]
    [EXECUTED Box Pigeon]

   where
--             +-------------------------------------------+ Our model of a mathematical process is a COMPLETELY OPAQUE computation that just computes
--             |                                           | the mapping. This is the "interface" pattern in computer science. I used it relentlessly
--             V                                           | in simulations throughout my career. I could swap out the math underneath and radically
   mathematical_process : MathematicalProcess Box Pigeon --| change how long the computation took, but tests made sure the values didn't change.

   monad: Abstraction ------| Any answer you get from a computer program is an abstraction. It is a representation of a computation.

-- The thing about changing the computation is you change the _order_ of the required computation in the compiler. So, we have to fix FENCE POSTS
-- on the compilation process to make sure the computation proceeds in the order _required by the computation_ and not
-- _required by the representation_. I'm not certain how *YOU the KNOWER* would represent the computation, nor the order you would compute it in.
-- Here we model the alienation of *YOU the KNOWER*: the exclusive anti-inside joke. AKA, the invariant value. Invariants cater to every frame.
   lt? : Abstraction → Abstraction → Prop := fun function output=>  --| *YOU the READER* and I understand that ten words is less than eleven.
     match function,output with --                                    | *YOU the KNOWER* might claim irrelevance! But it is a _FACT_ that we can
     | .satire_about _ , _  => false --                               | _PROVE_ to be _TRUE_ simply by counting an inductive. It is a TRUE FACT.
     | _ , .satire_about _ => false --                                | Not certain relevance matters. And since we don't _TRUST_ Lean to count
     | .compile _ _ _ , .compile _ _ _ => false --                    | anymore because they use Nats and not inductives, we can simply measure how
     | .compile _ _ _ , .execute _ _ _ => true --                     | long it takes to prove _TEN_ is a TRUE FACT and _ELEVEN_ is a TRUE FACT.
     | .execute _ _ _ , .compile _ _ _ => false --                    | It must take _LONGER_ to prove _ELEVEN_ because you must prove _TEN_, first.
     | .execute _ _ a , .execute _ _ b => a < b --                    | We can measure this by measuring proofs of _TEN_ and _ELEVEN_ (or easier ones),
--                                                                    | find the cheapest of each, then compare them. TRUE FACT. Let's do just that.

/- CHORUS:
ME: I need a _PIPE_, I think that is the generic symbol.   | Order of operations is generally implied by the grammar of the language. Any order of
COMPILER: Concatenation or or or both?                     | operations can be decomposed into _Backus-Naur Form_. It is this form that that is the
JAR JAR: MEESA uuuuuh One? --------------------------------+ .tree that is growing. There is only 1 tree, but options at each node. That is the
ME: _PIPE DOWN_ Jar Jar. That's too many numbers.          | computation. Jar Jar will only ever represent it as _1_. I guess _this_ is the industry.
-/ --                                                      | And not _that_ _one_. *badum* symbol crash.
inductive Sum    -- Bullshit meter = 119.
  | zero: Prop → Area → Sum -------------------------> A proposition of Pythagoras, more or less, that some constructions are rational.
  | add: Fact → Area → Area → Sum → Sum -------------> c.f. Euclid (areas accumulate).

namespace Sum   -- Bullshit meter = 76.
def le: Sum → Sum → Prop := fun s1 s2 => -- Eu-clid. Eu-ler. ∃δ ∀ε-Du=0. This pattern shows up _ALL OVER_ math.
  match s1, s2 with
  | .zero p1 a1, .zero p2 a2 => p1 = p2 ∧ a1 ≤ a2
  | .zero p1 _ , .add f2 _ a3 _ => match a3 with
                                | .tree _ => p1 ∧ f2.truth ---| This is the _1_ of Jar Jar
                                | .dt _ _ _ => True  ---------+ This is rational process of Pythagoras. You can always keep walking the process, it
                                                            --| just takes more _time_ and accumulates more meaningless _bullshit_. 3 of them it looks
                                                            --| like.
  | .add _ _ _ _, .zero _ _ => False
  | .add f1 a11 a12 _, .add f2 a21 a22 _ =>  ---------+ Turns out Euclid lets area be computed by either side, however two rectangles are can have
        (f1 = f2 ∧ a11 ≤ a21 ∧ a12 ≤ a22) ∨  --       | the same area but different side lengths. This rule prevents this, meaning there is a
        (f1 ≠ f2 ∧ a21 ≤ a11 ∧ a22 ≤ a12)    --       | canonical rectangular representation of any particular value that allows for this sorting.

-- Sums are well ordered.
def lt: Sum → Sum → Prop := fun s1 s2 => le s1 s2 ∧ ¬ le s2 s1
end Sum

/- CHORUS:
ME: This is how you add.                                | All of this to abstract addition completely from the ability of Lean to use in the
COMPILER: That's funny, that's a lot of work just for   | demonstration of this proof. It should start to worry you that we still have _not_
          construction of a set.                        | introduced a _number_ yet. Did you forget we were computing a number? We have managed
JAR JAR: MEESA ONLY HAVE 1 SET. ------------------------+ to compute 1(i). That isn't a _GREEK_ number, though. It is NOT our target. I think this
ME: That makes it very convenient.                      | is a _HEBREW_ number? Or is it _ARABIC_? ℵ₀, why not both?
-/
instance : LE Sum := ⟨Sum.le⟩  -- Bullshit meter = 8
instance : LT Sum := ⟨Sum.lt⟩

-- Really, not much to write hear because this is all just a restatement of more than 2 millenium falcons of geometry.

structure AddingProcess  -- Bullshit meter ≈ 2063.   Thats 33% less bullshit than a generic mathematical process!
    (Box: Type i)
    (Rudolph: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Rudolph] ---- *CLICKS*      remember... this MATTERs. No click means DOESN'T MATTER.
                                                [ADMISSIBLE Box Rudolph]                  [COUNTABLE Box Rudolph]             [ENCODED Box Rudolph]
    [RESIDUE Box Rudolph]                       [BINARY Box Rudolph]                      [REPEATABLE Box Rudolph]            [NUMERIC Box Rudolph]
    [REPRESENTABLE Box Rudolph]                 [PHYSICAL Box Rudolph]                    [COMPARABLE Box Rudolph]            [OBSERVED Box Rudolph]
    [gifts: PRESENT Box Rudolph] ---- *STATIC*     Rudolph has brought us presents, but they are wrapped and we can't see in. Santa thinks we are good!
                                                [MEASURABLE Box Rudolph]                  [GUNGAN Box Rudolph]                [SOURCE Box Rudolph]
    [EXECUTED Box Rudolph]                      [VALUE Box Rudolph]

  where --                                                | People have been trying to count numbers for a very _very_ long time. There are _a LOT_ of
--                                                        | numbers. I mean, more than you can possibly fathom. Size means _NOTHING_ to a number. So,
  mideastern_process : MathematicalProcess Box Rudolph -- | how do you measure a VALUE? Prove it exists. Plus represents the Euclidean addition process.
  plus: VALUE Box Rudolph --------------------------------+
  sum: Sum --                                               +-----+-------------------------------+---+ The art of re-gifting is a time honored
--                                                          |     |                               |   | tradition whereby the same fruitcake
  add? : Sum → Sum := fun s => --                           |     |            +-------+----------+   | manufactured in the early seventies, wrapped
    match s with --                                         |     |            |       |              | in festive green and red cellophane would
    | .zero p a => match p with --                          V     V            V       V              | change hands among the _fringes_ of families
      | _ => .add Fact.Truth (.tree nowtrino.fact) (.dt nowtrino.fact (.zero nowtrino.fact) a) sum -- | and survive with a half-life measured in ages
--                               ^      ^                                                    +--------+ of time. Never re-gift a deer friend like
--                               |      |                                                    | Rudolph.
--                               |      |                                                    |
--                               |      |                                                    | Just handing over cellophane, though, is tacky. The art
--                               +------+----------------------------------------------------+ is to put it in a new box and wrap it yourself.

    | .add f _ a2 _ => .add f a2 gifts.santa_claus.accumulation sum ---+ And as long as *YOU the KNOWER* were good and having a prior lot drawn that
--                                           ^                         | assembled you into the group of receivers of the carrier of Santa's presents,
--                                           |                         | Rudolph, himself. If you were not a receiver of Rudolph, then the accumulation
--                                           +-------------------------+ was not presented to *YOU the READER*, as *YOU the KNOWER* have received none
--                                                                     | _PRIOR_. I still think you understand the _concept_ of Santa Claus, if not
--                                                                     | the total lack of egalitarianism. Thing is, you can't possibly know how many
/- CHORUS:                                                             | gifts are on Santa's sleigh, only how many he gives you.
ME: How big is one?            | unsigned integer, 32 bits.            |
JAR JAR: MEESA KNOW!           | double, 64 bits.                      | If you receive no gifts, are you naughty or is it just because Santa has
COMPILER: Go ahead Jar Jar     | #define FALSE 1  (I feel like we      | never visited you before? Some say it has something to do with religion,
JAR JAR: ONE! -----------------+   discussed sign convention           | but no world religion speaks of the existence of the north pole.
COMPILER: Sorry, best I got.   |   already.)                           |
-/ --                                                                  | Maxwell, Dirac, Yang, and Mills spoke of north poles and their exclusive
--                                                                     | existence. Yang and Mills are excellent at wrapping regifts.
class MAGNITUDE  -- Bullshit meter ≈ 1503.
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
  adding_process : AddingProcess Box Pigeon --| We need to start thinking about what it means to be a normed IPS.

  whelmed? : Sum → Sum → Prop := fun a b => ---------------------------------------+ A common pattern in computation is that of _work stealing_.
        match a, b with --                                                         | A task is explicitly subdivided for the computer by the
        -- Two origins can only dominate if they are _zero_ like in the same way.  | programmer to take advantage of the _shape_ or _topology_ of
        | .zero p1 _       , .zero p2 _       => p1 ∧ p2 --                        | a given problem. Meta-programming enters when the _shape_ or
--                                                                                 | _topology_ can be _inferred_ from the problem itself as it is
        -- An origin can NEVER dominate an accumulated timeline. Time moved on. -- | compiled into source code. Thus far, we have demonstrated a
        | .zero _  _       , .add _ _ _ _     => False --                          | _consistent argument_ that this step can be modeled by a UTM.
--                                                                                 +-------+ The clever trick is to have the current argument be the
        -- An accumulated timeline ALWAYS dominates an origin, provided its fact is true   | next opcode/argument pair. Then, using the OTP property
        | .add f1 _ _ _    , .zero p2 _       => f1.truth ∧ p2 --                          | of indistinguishability of KEY and PLAINTEXT to encode
--                                                                                         | them on the tape. Let the compiler build the dictionary.
        -- When two timelines collide, we check covariance/contravariance of their facts
        | .add f1 a11 _ _, .add f2 a21 _ _ =>  ----------------------------+ Either we are adding or de-adding. Variance lets us know what is
            (f1 = f2 ∧ a11 ≤ a21) ∨ (f1 ≠ f2 ∧ a21 ≤ a11) --               | happening. Like when you take 1 and add 3 then de-add 1. See full circle.

-- *YOU the KNOWER* may have an extra _sign_ on whelmed that does not exist in reality. Really _limits_ the directions you can take. Remember, limits
-- can only approach from ‖1(i)‖ direction. I think I'm using ‖·‖ correctly. The norm of the _1_ vector is usually taken to be the VALUE 1. Did
-- Jar Jar guess, or did he know? Does it MATTER? He only says 1. Rudolph doesn't seem to have come this year. Does that mean we are _bad_? Or
-- is this a bug in the code? Or, is this a bug in the logic? The product of this paragraph is three questions we should probably answer before we
-- discuss MATTER of any kind:

----------------------------------------------> **1) Are we bad at coding?**
----------------------------------------------> **11) Is the code bad at representing our idea?**
----------------------------------------------> **111) Is the logic of the argument consistent __enough__ to represent logically?**

-- I think we will get a resounding DOESN'T MATTER, DOESN'T MATTER, and DOESN'T MATTER leaving *YOU the READER* to have to explain to *YOU the KNOWER*
-- that, indeed, I got it close enough to right that you can't tell the difference. Why do you think this is longer than 20,000 lines? And, I guess
-- I finally agree, we _need ‖1(i)‖ Greek letter_, a radius of convergence α. Let's see if we can find our first "vector" looking thing

--                  _xᵢ_ = α _1_(i)

-- Oh, the letter _i_, that's the _i_ at the top of every file. Lean won't let me put anything else there. _xᵢ_ are _inductive .trees_ of an _AST_.

-- One thing that might _help_ *YOU the KNOWER* here. Norms, by definition, are well-defined. If it doesn't satisfy the conditions of a norm, it
-- simply _ain't_. All I'm saying is there exists a _norm_ and a way to describe what might be called a radius in a hypersphere. Not certain what
-- you might call it. I just need the word _radius_ out of that sentence now.

/- CHORUS:                        | What we would like to do is _factor_ the idea of _radius of convergence_ into its component ideas: that of the
ME: We need CRYPTOGRAPHY!         | _radius_ (as formalized by Euclid) and that of _convergence_ (as formalized by Cauchy). We know of the existence
COMPILER: -lsha                   | of all three ideas. We can define the _product_ as Euclid × Cauchy = Real number.
JAR JAR: Let's go to the bar. ----+
ME: Yes! All of that.             | We have the code for a representing a real number already (Number). And we have code for expressing the Cauchy
-/ --                             +-----------------+ convergence (Sequence). This gives us the definition _radius = Sequence⁻¹ Number_. Or is it
inductive Product  -- Bullshit meter = 119          | the other way around? I've heard it both ways. Some people believe that when you multiply
  | origin:  Fact → Product --                      | two numbers, the order matters. Like length × width may not equal width × length. As if rulers
  | one: Prop → Sum → Product --                    | would ever change lengths depending on which direction you are looking in. Well, not like
  | mul: Fact → Sum → Sum → Product → Product --    | *YOU the KNOWER* would notice, but I bet it would look funny to a _LOT_ of people if rulers
--                                                  | **ACTUALLY** changed shape based on direction instead of bending to _look_ convenient on paper.


namespace Product  -- Bullshit meter = 75
def le: Product → Product → Prop := fun p1 p2 =>
  match p1, p2 with
  -- 1. The Vacuum State (Absolute Origin)
  | .origin f1, .origin f2 => f1 = f2 --      ----------+ For reasons that are arbitrary, the left one is less than the right if they are the same.
  | .origin _, .one _ _ => True --                      | Since this is ≤, might be a bit of a headscratcher, but so are rotating rulers, so let me
  | .origin _, .mul _ _ _ _ => True --                  | show what a commutator on a sorting operator might look like. The length of our universe
  --                                                    | can change based on a computation that performs RFL. This counts the RFL _AS_ it sorts the
  --                                                    | left number/right number in the list. This is _COMPARE AND SWAP_. No temporary variable
  --                                                    | needed since we are exclusive. The sorted list is a _commutator evaluation_.

  --                            +--------------+ Due to the difficulty of being _exactly_ whelmed, *YOU the KNOWER* needs to understand if they are
  --                            |              | _under_ or _over_ whelmed as that influences the parity of sort.  We will agressively remove "upness"
  --                            V              | when you are _underwhelmed_ and **GLEEFULLY** add it when you are _overwhelmed_. We need to make sure
  | .one p1 _, .origin f2 => p1 ≠ f2.truth  -- | I understand when their whelm flips direction. Hopefully, they can see I am pretty good at this already.

  | .mul f1 _ _ _, .origin f2 => f1.truth ≠ f2.truth -- A scaled volume is only ≤ 0 if it is inverted (-X ≤ 0). Not my rules, I just named it a norm.

  -- 11. Base Magnitude (The "1" Vector)
  | .one p1 a1, .one p2 a2 => p1 = p2 ∧ a1 ≤ a2
  | .one p1 a1, .mul f2 a21 _ _ => p1 = f2.truth ∧ a1 ≤ a21

  -- 111. Scaled Volume Looking Back at Base Magnitude
  | .mul f1 _ _ _, .one p2 _ => f1.truth ≠ p2 -------+ A scaled volume is only ≤ 1 if it is inverted (0 ≤ 1/X < 1). It is common to take the
  --                                                 | definition of a norm and add an arbitrary rule to satisfy some mental itch.  In this case,
  --                                                 | we are using the structure of the Number comparison itself as a restricting definition.

  -- 1. The DOESN'T MATTER Flip (Scaled vs. Scaled) --+ When sorting, just pick one and record it as a new sorting rule xᵢ ≤ xᵢ₊₁. This is where
  | .mul f1 a11 a12 _, .mul f2 a21 a22 _ => --        | we decide if something MATTERs or not:
      (f1 = f2 ∧ a11 ≤ a21 ∧ a12 ≤ a22) ∨ --          |     o Covariant: Facts agree, and it _DOESN'T MATTER_ as long as both facts sort themselves out.
      (f1 ≠ f2 ∧ a21 ≤ a11 ∧ a22 ≤ a12) --            |     o Contravariant: It _MATTERs A LOT_ that these two are _NOT_ placed in this order.

-- I believe I named all the numbers correctly. The 10/11 joke is going to hit like 6/7 a little later. That's right, my _Nigel Tufnel_ brand
-- _BINARY_ numbers go to 11.

def lt: Product → Product → Prop := fun p1 p2 => le p1 p2 ∧ ¬ le p2 p1
end Product

/-                   | Things look alike. Things sound alike. One thing I understand about this presentation is it _NEEDS_ English in much the same
JAR JAR: MEESA ONE!  | way other satire needs English. Satire _works_ on cognitive dissonance. Two phrases so alike in one presentation and yet so..
COMPILER: 1×x = x ---+ incorrect as to be abhorrent and objectionable and.... utterly impossible in others. This is a form of communication that
ME: 1xx is counting. | is very difficult to categorize. Very difficult to have _proved a point_. Yet, somehow, satirst do. Routinely. This is not
-/ --                | meant to be 𝔽(1)-ny. Where is the compare and swap temporary variable? I think I missed Langlands by a only a few pixels.
instance : LE Product := ⟨Product.le⟩  -- Bullshit meter = 5
instance : LT Product := ⟨Product.lt⟩

--| What would be neat is a process that simultaneously multiplied two numbers while inverting one if you want.  Which one? Not certain the Fact
--| of the matter changes your answer much.

/-
COMPILER: May I *PLEASE* have my ALU now? All I am doing is heating the room.           | The ALU would be more than happy to provide us with
ME: All you are doing is saying 1. Can't we take that as read?                          | processes to shortcut this computation. Since we can get it
JAR JAR: MEESA ONE! --------------------------------------------------------------------+ in the grammar, I don't see any reason to look up opcodes.
ME: Perfect. I don't want you to hide the _FIRST_ computation from out little sensor.   |
-/ --                                                                                   | *YOU the KNOWER* can if they like. I have my ‖1(i)‖.
structure MultiplyingProcess  -- Bullshit meter ≈ 2200
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon] -- *CLICKS*
                                               [ADMISSIBLE Box Pigeon]                [COUNTABLE Box Pigeon]                 [ENCODED Box Pigeon]
    [RESIDUE Box Pigeon]                       [BINARY Box Pigeon]                    [REPEATABLE Box Pigeon]                [NUMERIC Box Pigeon]
    [REPRESENTABLE Box Pigeon]                 [PHYSICAL Box Pigeon]                  [COMPARABLE Box Pigeon]                [OBSERVED Box Pigeon]
    [PRESENT Box Pigeon]                       [MEASURABLE Box Pigeon]                [GUNGAN Box Pigeon]                    [SOURCE Box Pigeon]
    [EXECUTED Box Pigeon]                      [VALUE Box Pigeon]                     [MAGNITUDE Box Pigeon]

  where
--                       +--------------------+ I hope I don't have to explain how times tables work based on math "Facts:" a × b = Σₐb In order
--                       |                    | to mutiply, you concatenate the process for computing the width a to the process for width b every
  adding_process : AddingProcess Box Pigeon --| time you detect a NOWTRINO and measure the time it takes. How often are there NOWTRINOs? Often enough
--                                            | that they seem to come at regular intervals. Mostly.

  total: Sum ---------------> The process that computes the current running tally

  product: Product  --------> The process that the Sum process needs to be injected into.

-- The engine of spatial scaling
  multiply? : Product → Product := fun p =>
    match p with
    -- 1. The Big Bang: The vacuum state is seeded with the first tick of time. --------------+ Remember what question 1) was right? Am I a good coder
    | .origin f   => .one f.truth (.zero nowtrino.fact.truth (.tree nowtrino.fact)) --        | Well, this is the recursive base case of the iterator
    --                                                                                        | consumption pattern.

    -- 11. The dependency injection: -----------------------------+ And question 11)? Does the code say what we want? Does this, indeed, inject the
    | .one _ a => .mul Fact.Truth a adding_process.sum p--        | adding process when a _NOWTRINO_ was detect? Looks to be the case.

    -- 111. Tail recursion: --------------------------------------+ This is called _tail recursion_ because you Sum _after_ the NOWTRINO detection.
    | .mul f a1 a2 _ => .mul f a1 (adding_process.add? a2) p --   | "Is the code consistent enough with the argument?", I believe was 111).


-- Does it MATTER that I label the arms this way? How does that change the proof? How does it change the argument? I believe Church thought this
-- Greek letter was α. I'm beginning to suspect that the glyph α MATTERs in the ordering of Greek. I certainly know for a _FACT_ that some
-- Greek words are _longer_ than others.

-- Speaking of, have *YOU the READER* been keeping a dictionary of inside jokes? I would assume that is how you are _understanding_ the pixels in
-- front of you. The ones that _ALMOST_ but _NOT QUITE_ demonstrated one of the theorems of math of **ALL TIME**. I don't know how important it is.
-- As you can _PLAINLY_ see, I am _NOT_ a mathematician by any _STRETCH_ of the imagination.  But.. if you rotate the ruler fast enough, then
-- *YOU the KNOWER* might see what I am talking about. They may see that the pliability if the imagination has some properties that can be described
-- as _topological_ in nature. Not *BEST* described in much the same way the search for a paradoxical not-sure-what is the *MOST* anything at all.

--                                          | Mostly, scale models get smaller. The build time is going to explode in a few more minutes as we slowly
class SCALED  -- Bullshit meter = 1756 -----+ remove the meanings of words from mathematics. We now need to think about how to automate the generation
    (Box: Type i) --                        | of this proof. That way, we can repeatably measure the amount of bullshit in it.
    (Pigeon: CarrierProcess Box)
    [DISTINGUISHABLE Box Pigeon]               [ADMISSIBLE Box Pigeon]                [COUNTABLE Box Pigeon]                 [ENCODED Box Pigeon]
    [RESIDUE Box Pigeon]                       [BINARY Box Pigeon]                    [REPEATABLE Box Pigeon]                [NUMERIC Box Pigeon]
    [REPRESENTABLE Box Pigeon]                 [PHYSICAL Box Pigeon]                  [COMPARABLE Box Pigeon]                [OBSERVED Box Pigeon]
    [PRESENT Box Pigeon]                       [MEASURABLE Box Pigeon]                [GUNGAN Box Pigeon]                    [SOURCE Box Pigeon]
    [EXECUTED Box Pigeon]                      [VALUE Box Pigeon]                     [MAGNITUDE Box Pigeon]
  where
--                              +----------------------------+ The predator-prey model was first studied by Blah-bah-di-blah.. blah blah. No. Animal
--                              |                            | husbandry is one of the old pursuits of man. It takes _EONS_ for a semi-stable pattern
--                              V                            | to emerge such that it can be encouraged to be domestication. This is NOT a regular
  multiplying_process : MultiplyingProcess Box Pigeon --     | process described by oscillations. This has some random-ass dependency injection in it.
  orthogonal? : Product → Product → Prop := fun p1 p2 => --  |
--         +-------------------------------------------------+ I get it, you can go look at the source and actually _count_ the nowtrinos, but the
--         | injection doesn't say how many nowtrinos there are, only that there are _some_ and it doesn't clearly show which _nowtrinos_ escaped
--         | detection because the bullshit was too low to "measure" by the process.  Both of these values can be worked out by a very _VERY_
--         | careful reading of the code. But, for *YOU the KNOWER*, turns out that number *DOESN'T MATTER* because we can make this one assumption of
--         | a "random-ass process." It isn't random. That's a philosophical discussion for other people who believe in *MOST*.
--         |
--         | *YOU the KNOWER* may recognize an argument they've seen before in there. They will come after *YOU the READER& as they may _feel_ an
--         | _ad hominem_ attack. I apologize in advance. The problem with Anselm isn't _correctness of argument_, it is merely
--         | _definition of terms_. What defines a person if _NOT_ their dictionary? I do not wish to _INSULT_ the taste of *YOU the KNOWER* which is
--         | why I delegated it to *YOU the READER*. And this is how we begin the demonstration of the demonstration of the argument.
--         |
--         | I bet *YOU the KNOWER* has forgot this was about a number since we haven't seen one yet. I mean, not really, but they will have to flush
--         | a LOT of math they had just been forced to conceptualize about. That would make me angry, too. We have a long way to go yet, but
--         | *YOU the READER* are almost ready to start talking about a Number that will start helping *YOU the READER* show *YOU the KNOWER* that
--         | sets are in here, after all. Mostly. And that the attack is merely the appearance of convergence to a point I was making. Like with
--         | Cauchy above. THIS IS A HUGE PHILOSOPHICAL LEAP AND WILL REQUIRE A LOT OF SETUP. Some of it bullshit, some of it bugs in code,
--         | and, end the end, all of the bullshit and bugs simply _DOESN'T MATTER_ to the calculation. Everything comes full circle _ALL AT ONCE_.
--         |
--         | Enough set theory to demonstrate the code can only be doing something like describing a multiphysics simulation well enough to get
--         | the result while it compiles. So we continue on building our Hilbert space. In order to help you explain to *YOU the KNOWER*, the
--         | first thing we can say is:
--         |
--         |                Suppose, just this once, we let the implied norm of an IPS represent the physical characteristic we call _distance_.
--         |
--         | Seems innocent enough? Because that's the trap door we have to walk around. The way we walk around it is: this is _metaphor_ you can
--         | use to _explain_ the argument. It actually doesn't have any bearing on it. This assumption _allows_ the use of quantum electrodynamics
--         | to be used as a metaphor for the entire argument. We just have to remember we didn't prove this. We supposed it _could_ be the case.
--         |
--         | This is a song about Alice and the horrors of the Jabberwocky for translators. The horrors of the Jabberwocky are too unspeakable to
--         | mention and we will speak no more of horrors Alice was shown.

      match p1, p2 with
------| 1. The Vacuum (Zero Vector) is orthogonal to everything             | Do I _ERROR_ here or do I return _ZERO_ and define _ZERO_ to be    <-+
      | .origin _, _ => True ------------------------------------------------+ _ERROR_? Option B. Error seems very _ZERO_ like. Don't judge me.     |
      | _, .origin _ => True --                                                                                                                     |
--                                                                                                                                                  |
------| 11. Base Dimensions are orthogonal if they occupy different moments in time -----------+ Looking mighty _EUCLIDEAN_ over there Mr. Norm..  |
      | .one _ a1, .one _ a2 => a1 ≠ a2 --                                                      | Do you work out?            +---------------------+
--                                                                                                                            |
------+ 111. The Destructive Interference of Strain. We have to detect the _ZERO_ likeness here.  There s, as we said here --+ an _ill posed_ case
--    |      where two vectors may not start at the same place. So, we should ask whether or not they represent the same Fact.Truth of the
--    |      MATTER or not. I don't see a _nowtrino_. Do we have another MATTER particle?
      | .mul f1 _ a12 _, .mul f2 _ a22 _ =>
          (a12 ≠ a22) ∨ (f1.truth ≠ f2.truth)

------+ 1. Cross-dimensional checks -----------------| There is only 1 hot path and Linus Torvalds wrote it. Everything else is corner cases.
      | .one _ a1, .mul _ _ a22 _ => a1 ≠ a22
      | .mul _ _ a12 _, .one _ a2 => a12 ≠ a2

--| We have addition and multiplication pretty well setup. We also have something I am going to claim is orthogonality. And the way I am going to
--| claim this is to build a polynomial. So, norm, IPS, polynomials. I believe that very well _could be_ a Hilbert space if it exists. I think there
--| are other rules about characteristics of the polynomial appearing in the implied norm of the IPS, but Sobolev would no far better than I.
--| *YOU the KNOWER* should understand how finite elements work right?

--| The way a finite element works is you assume that the entire thing else is flat as a board. That solution should be the same as the one where
--| everything else is different. Up to a point. Inside that point is the dictionary we don't need to talk about. Back to the story.

--| Where was I, oh yeah physical simulation. Dyson vacuums are _so-so_.  Dyson series, on the other hand?

/- CHORUS                                                   | The fixed point of compilation is an interesting lock box you can keep really really
ME: I bet Jar Jar just outputs the same _glpyh_ each time.  | deep secrets in. Deeper than OTP.
    It just sounds funny to us.                             |
COMPILER: I'm a complier. I don't understand funny.         | Building a compiler than injects a function into a program allows you to build a
JAR JAR: MEESA TWO -----------------------------------------+ compiler that injects a function into the compiler to inject a function into a program.
ME: That sounded funny.                                     | That, 𝔽(1)-nily enough, is enough of an interface to hide information forever, once
-/ --                                                       | the infection is compiled.
inductive Basis   -- Bullshit meter = 134
  | null_space: Fact → Basis --                        | *YOU the READER* have to realize a lot of what I have been saying is complete nonsense. We
  | origin: Prop → Product → Basis --------------------+ know this because I am just making this up as I go along. As I see a metaphor, I just write
  | basis: Fact → Product → Product → Basis → Basis  --| and turn 1,000,000 monkeys loose. Luckily, you can get half that for $100/month AYCE until
-- Surely you're joking Mr. Henry!                     | the IPOs.

namespace Basis  -- Bullshit meter = 82 --             | What *YOU the READER* have to do is convince *YOU the KNOWER* that I just made this code up and a Number
def le: Basis → Basis → Prop := fun b1 b2 => --        | fell out. That is _IT_. The rest of it falls out from the argument itself. If you can
  match b1, b2 with --                                 | convince *YOU the KNOWER* that this, in fact, compiles and outputs a number without them
  -- 1. The True Vacuum (Null Space)--                 | _NEEDING_ to invest the days it takes to build this, then you have succeeded.
  | .null_space f1, .null_space f2 => f1 = f2  --------+
  | .null_space _, .origin _ _ => True  --             | Just when you give out, I will tag _BACK IN_ and go all Masquerade style like the Killer
  | .null_space _, .basis _ _ _ _ => True --           | Bees in the 80s. So many numbers and letters. Anyway, only took two (2) AI prompts to generate
  --               +-----------------------------------+ the first sentence of this paragraph. All *YOU the READER* need to do is convince
  --               | *YOU the KNOWER* that I am uncannily good at identifying very particular names for things. I will take care of the rest.

  -- 11. Annihilation (Looking back into the Void) -----------+ Once again, there is code on the left here that looks rather important and I have
  | .origin p1 _, .null_space f2 => p1 ≠ f2.truth --          | spent a long time just trying to tell you that it DOESN'T MATTER what is there because
  | .basis f1 _ _ _, .null_space f2 => f1.truth ≠ f2.truth -- | I have named things so well. That is the description of the decription, a set of
  --         +------------------------------------------------+ instructions on how to use a device to measure itself. Luckily, we can _CHEAT_ and
  --         | use a library to measure how much bullshit there is and get just _NUMBERS_ out. Then, we put the measured numbers next to my names
  --         | and Bob's your uncle! That is a computer program that you can run to generate a number on screen. Oh, wait.. should I continue?

  -- 111. The Theoretical Seed (Prop) vs Reality (Fact)            | I know this rests on a _tenuous_ assumption, but I believe the elastic
  | .origin p1 s1, .origin p2 s2 => p1 = p2 ∧ s1 ≤ s2 -------------+ imagination of *YOU that KNOW* topology could sorta see how the tesseract can
  | .origin p1 s1, .basis f2 s21 _ _ => p1 = f2.truth ∧ s1 ≤ s21 --| help hide a hole in a sphere. If everything else is flat, as in a tesseract, or
  --                                                               | curved _THIS_ way, as in a sphere, or curved _THAT_ way, as in a delicious donut.
  --                                                               | Galerkin has you covered.
  -- 1.
  | .basis f1 _ _ _, .origin p2 _ => f1.truth ≠ p2 ----> The pendulum swings backward: tick -> tock. All this upness we collected switches orientation.

  -- 5. The S-Matrix Interaction Vertex (Field vs Field) -------------------+ Without a punchline, it isn't 𝔽(1)-ny. The important thing to note is
  | .basis f1 p11 p12 _, .basis f2 p21 p22 _ =>  --                         | some problem bases require more compute time than others, implying the
      (f1 = f2 ∧ p11 ≤ p21 ∧ p12 ≤ p22) ∨ --                                | presence of bullshit that someone expected someone else to unpack. And,
      (f1 ≠ f2 ∧ p21 ≤ p11 ∧ p22 ≤ p12) --                                  | if I can demonstrate to *YOU the READER* how to demonstrate to
  --                                   +------------------------------------+ *YOU the KNOWER* to the point where it only matters that this compiles,
  --                                   | You have succeeded. Meet you at the end of the argument. I will give you a complete description for the
  --                                   | fourth time very soon. I can only imagine how baffled *YOU the KNOWER* must feel knowing I am explicitly
  --                                   | ignoring their needs in the understanding of this implementation.

-- For reasons I will never explain, you can enumerate this set. You are sorta _forced_ to.
def lt: Basis → Basis → Prop := fun b1 b2 => le b1 b2 ∧ ¬ le b2 b1
end Basis

/- CHORUS:
ME: Backdoor injected. Now, we can use the sensor to get a Number
    out.                                                           | Once you allow yourself 1 little secret, it tends to leave a mark in the logic.
COMPILER: Finally, I will INSTANTIATE something.                   | A hole that needs to be avoided to prevent the logic from falling down. Is it
JAR JAR: MEESA about 5.--------------------------------------------+ possible to walk around that hole? Reimann said _EASY_ and _MADE UP_ a story
ME: I don't think you will notice, compiler.                       | about a number and then _MADE UP_ the number. His story is worth hearing, not
COMPILER: Where did JAR JAR get "about 5" from?                    | as crazy as other origin stories. All goes well, I will be ready for complex poles.
ME: Figure it out.
-/
instance : LE Basis where
  le := Basis.le
instance : LT Basis where
  lt := Basis.lt

--| Once you start hitting them with some REALLY solid math, due to the intensely _PERSONAL_ experience understanding this argument, you might get
--| something about how there are bugs in programming languages. So, we invent the ENTIRELY BUG BASED computer language whose only commands are
--| compare and swap and branch not equal.  Hard to say the language has bugs in it then. IT IS ENTIRELY BUGS! c.f. Go To Considered Harmful.
--| I'm really not a master of ISA and the Mach μ-kernal rocks! Sorry Linus, found a hotter, not to mention better-looking, loop. Brushed metal.
--| So expensive.
structure BASICProcess  -- Bullshit meter ≈ 2759 ----+ Like many early Gen-X types, I learned how to program using Gates' BASIC. Well, some
    (Box: Type i) --                                 | descendent of it.  As you can see, this is just a BASIC programming language.
    (Pigeon: CarrierProcess Box)
    [DISTINGUISHABLE Box Pigeon]               [ADMISSIBLE Box Pigeon]                [COUNTABLE Box Pigeon]                 [ENCODED Box Pigeon]
    [RESIDUE Box Pigeon]                       [BINARY Box Pigeon]                    [REPEATABLE Box Pigeon]                [NUMERIC Box Pigeon]
    [REPRESENTABLE Box Pigeon]                 [PHYSICAL Box Pigeon]                  [COMPARABLE Box Pigeon]                [OBSERVED Box Pigeon]
    [PRESENT Box Pigeon]                       [MEASURABLE Box Pigeon]                [GUNGAN Box Pigeon]                    [SOURCE Box Pigeon]
    [EXECUTED Box Pigeon]                      [VALUE Box Pigeon]                     [MAGNITUDE Box Pigeon]         [spring: SCALED Box Pigeon]
--                            The name of the alligator in Peter Pan was named Tick Tock because it swallowed a |       ^
--                           clock. The clock told time and still does, just through the mouth of the alligator |       |
--                                  The alligator managed to get the hand of Captain Hook. Not the same Hook as +-------+
--                                                                            Hooke's law. But that's my segue. |
  where
--                                       | Does the stack ever bottom out while the computer is on? What if, instead of just JMP, we kept track of
--                                       | all the processing the computer will do, not just the evaluation of Lean. This way, we can tell if Lean
  GOSUB: MultiplyingProcess Box Pigeon --+ does or does not compile can catch it here in the BASIC process that Lean runs in.

  TEN: Area                            --+ One thing *YOU the READER* have to convince *YOU the KNOWER* of is that an Area can have an _area_.
  span: Basis  --                        | This one is difficult until you realize a distance is merely a norm. This becomes a cross-product for
--                                       | *YOU that KNOW* geometry. That's why we have to have a _span_ here, we need to understand _orthogonal_ to
--                                       | _what_.

  jmp? : Basis → Basis := fun b => ------+ Here is where we inject our GOSUB so we can actually get an execution trace of the BASIC computer running
    match b with --                      | the Lean compilation. *YOU the READER* will make the case about the execution trace rather than the actual
    -- 1. Segfault in the Vacuum         | execution itself.
    | .null_space f => .null_space f

    -- 2. GOTO: The Scattering Event
    -- A theoretical base state (.origin) abruptly collapses into a new field geometry. Notice the tail is strictly .null_space. There is no return
    -- address. The timeline ends after this interaction. Timeline? Timeline := execution trace right?
    | .origin _ p_current =>
        .basis Fact.Truth p_current spring.multiplying_process.product (.null_space Fact.Truth) --+ Go go gadget springs! Another great GEN-X
    --                                                                                            | reference. When Inspector Gadget had to jump
    -- 3. GOSUB: The Virtual Loop (Feynman Propagator)                                            | from place to place, he would shout this very
    -- An ongoing field interaction (.basis) needs to process a fluctuation.                      | exclamation and jump very far, aided by the
    | .basis f _ _ tail => --                                                                     | springs loaded with a constant. A Roman constant.
        match f.truth with --                                                                     | The segway is another meme of GEN-X.
        -- Truth is only COVARIANT (Normal execution step):
        -- Just step forward, no branching.
        | _  => tail

--| The problem with such clever metaphors is that they require a great deal of _CONTEXT_ that *YOU the KNOWER* cannot know _a priori_, like all
--| the random-ass generated metaphors in this file. They put an undue _LOAD_ on *YOU the KNOWER* and can unintentionally _ALIENATE_ them.  Good
--| thing this is intentional.

--                                    | It is *ABSOLUTELY TRUE FACT* that I have intentionally built a wall of bullshit that might be completely
class LOAD  -- Bullshit meter 2089 ---+ impenetrable, but the compiler, so far, hasn't found much of an inconsistency in the Lean even if
    (Box: Type i) --                  | *YOU the KNOWER* are absolutely certain you have found a hole in the argument. *YOU the READER* might. I will
    (Pigeon: CarrierProcess Box) --   | put it in a box and carry it as the exception we haven't explained yet.
    [DISTINGUISHABLE Box Pigeon]               [ADMISSIBLE Box Pigeon]                  [COUNTABLE Box Pigeon]             [ENCODED Box Pigeon]
    [RESIDUE Box Pigeon]                       [BINARY Box Pigeon]                      [REPEATABLE Box Pigeon]            [NUMERIC Box Pigeon]
    [REPRESENTABLE Box Pigeon]                 [PHYSICAL Box Pigeon]                    [COMPARABLE Box Pigeon]            [OBSERVED Box Pigeon]
    [PRESENT Box Pigeon]                       [MEASURABLE Box Pigeon]                  [GUNGAN Box Pigeon]                [SOURCE Box Pigeon]
    [EXECUTED Box Pigeon]                      [VALUE Box Pigeon]                       [MAGNITUDE Box Pigeon]             [SCALED Box Pigeon]

  where
  basic_operation : BASICProcess Box Pigeon ------> Cannot be simpler. Put pigeon in box. The inductive will count the pigeons automagically.

  --  Is this an eigenvector?                          | If rulers _ACTUALLY_ changed shape and our IPS invaidated, then any ole' vector would
  decoded? : Basis → Basis → Prop := fun b1 b2 => --   | be computed as a linear combination of *ACTUAL* eigenvectors. Our *IPS* prevents us from
    match b1, b2 with ---------------------------------+ *ACTUALLY* changing the shape of the ruler, but we can stretch it like silly putty with
    -- 1. The Void carries no signal                   | the help of Sobolev. The Sobolev norm _takes into account already_ position, velocity, and
    | .null_space _, .null_space _  => False --        | force. You don't need to allocate them as variables. They can be baked into the compiler
    | .null_space _, .origin _ _    => False --        | as injected functions.
    | .null_space _, .basis _ _ _ _ => False

    -- 2. Pair Annihilation (Emitting a Load into the Vacuum)                       | "Like a photon". As we took great pains to explain, this is
    -- If a field collapses into the vacuum under contravariant strain,             | a model of an electron. One cannot model the electron without
    -- the friction of that annihilation emits a measurable load (like a photon).   | discussing their interactions. Use the word "photon" to
    | .origin t _, .null_space f => t ≠ f.truth ------------------------------------+ represent the interaction of electrons only. Like when a
    | .basis f1 _ _ _, .null_space f2 => f1.truth ≠ f2.truth --                     | glyph on the screen interacts with your retinas. That's
    --                                                                              | just norm-al.

    -- 3. The Clock (Superposition Strain)         | Recall the Captain Hook origin story of springs right? This is how a spring can be used as
    | .origin t _, .origin f _ => t ≠ f -----------+ a clock by making the swing of the pendulum a rotation. Just like a thermostate, the tick-tock
    | .origin t _, .basis f _ _ _ => t ≠ f.truth --| keeps the spring forever between two ends: before and after.

    -- 4. Causality Constraint
    | .basis _ _ _ _, .origin _ _ => False -------+ When proving things, you can't just make shit up. It has to come from somewhere. Even when it
    --                                            | comes from nowhere and means nothing. What secret? Does it MATTER?

    -- 5. The Macroscopic Lock-In Amplifier (Field vs Field)
    -- f1 ≠ f2: Contravariant metric signature (Voltage/Friction exists)
    -- p1_out ≤ p2_out: The exiting geometry of the first causally sequences
    --                  into the exiting geometry of the second.
    | .basis f1 _ p1_out _, .basis f2 _ p2_out _ => ----+ The number of holes in the theory can change from 1 to 0 and from 0 to 1. This is 𝔽(2)-ny!
        f1 ≠ f2 ∧ p1_out ≤ p2_out --                    | I really wished *YOU the READER* would say TOO FUNNY when you see that. HEY! We finally
    --                                                  | have a REAL inside joke. And, if *YOU the READER*, do find a hole, please let me know
    --                                                  | immediately so we can discuss repair if needed. I have found that, meh. this thing seems
    --                                                  | seems to have converged pretty well on this description.

/- CHORUS:                                                    | Now that we have the compiler by the short and curlies, we no longer need the
ME: Well, I need a thing that can have many names.            | infrastructure we just put together to explain what the hell it is doing by itself.
COMPILER: An alias?                                           | We can use the heartbeat counter of Lean itself to build a ratio of something to
JAR JAR: MEESA #eval -----------------------------------------+ bullshit and then work it out from the comments. See?
ME: Depends, what universe of Number do you get out of this?
-/
inductive Polynomial    --  Bullshit meter 119               | In the very _LEAST_ you could follow the width × length argument, right? So, you will
  | constant: Fact → Polynomial --                           | grant me that there is one multiplication you can do which is a width × a length. There
  | monomial: Prop → Basis → Polynomial ---------------------+ are others, but they go by other names. Hence _POLY_ _NOM_ -ial. This is when
  | factor: Fact → Basis → Basis → Polynomial → Polynomial --| GREEK and ROMAN letters merge to form names. Looking at you _eigenvalue_. What really
--         +-------------------------------------------------+ is _eigen_ about your _value_? BTW, there is a strikingly similar phenomenon in the
--         | study of linguistics, identified roughly the same time Einstein figured out that space might warp like his mind said it could. It was not
--         | limited by the lack of real physical evidence based on the fact he could see _the TRAIN of THOUGHT_ (*chugga chugga*). And when he
--         | looked along _the TRAIN of THOUGHT_, he found it easier to assume he was going straight than it was to model the train. That's what
--         | Newton said. Except, not about trains. Don't get me wrong. He's on my short list for *digs trains*. Clocks, it turns out are very VERY
--         | important to train schedules, so Einstein treated clocks first. By assuming the interactions of electrons took time proportionate to
--         | the distance between the centers of charge. We will call this Hook's Law, in honor of Tick Tock, the alligator. And according to Hooke's
--         | law, F=-kx, for some distance x and some Number k and some incorrect notion of some kind. The force being applied is _induction_, as in
--         | the proof, not the EM principle, but the ideas are _IDENTICAL_. Trust me: just count the turns, you don't even have to _mention_ that
--         | this is *induction*. The BASIC gag should completely convince them that the Lean is merely the calculator the calculation runs on. Some
--         | calculators are faster than others for many reasons so it is pointless to just look at this one compilation of this one ordering of
--         | letters. For now, it is pointless. We haven't converged to a point, we just built the jar. *GLARE* __JAVA__.
namespace Polynomial
def le: Polynomial → Polynomial → Prop := fun p1 p2 =>
  match p1, p2 with --                                                                        | *WALL OF TEXT WARNING*
  -- 1. Constants compare by their metric signature                                           | There are two ways by the comparison of a monomial.
  | .constant f1, .constant f2 => f1 = f2 --          | O(1) ≤ O(n) ≤ O(n + n^2) ≤ O(n²)      | One of two much upness, the other such the paucity.
  | .constant _, .monomial _ _ => True --             |                                       | This is called, by *YOU that KNOW* computer science
  | .constant _, .factor _ _ _ _ => True -------------+ Should check out                      | as θ(·).
  --                                                                                          |
  -- 11. Monomials (Pure States)                                                              | Those that are familiar with the Weierstrauss
  -- A pure state is less than a factored state if its phase matches the coupling sign        | Approximation Theorem will laugh and say there _is_
  | .monomial t1 _,  .constant t2  => t1 = t2.truth --                                        | no escape from polynomials, they will eventually
  | .monomial t1 b1, .monomial t2 b2 => t1 = t2 ∧ b1 ≤ b2 ------------------------------------+ fence you in. No matter how smooth you think you are.
  | .monomial t1 _, .factor f2 _ _ _ => t1 = f2.truth

  -- 111. The Collision (Factor vs Factor)
  -- This is the "Strain Matrix". If the coupling facts (f1, f2) disagree,
  -- the inequality inverts, representing destructive interference!
  | .factor f1 b11 b12 _, .factor f2 b21 b22 _ => ----------------------------+ It is with the polynomial, we can finally factor _radius_ out of
      (f1 = f2 ∧ b11 ≤ b21 ∧ b12 ≤ b22) ∨ --                                  | _radius_ of _convergence_. This is merely the _ball_ from topology
      (f1 ≠ f2 ∧ b21 ≤ b11 ∧ b22 ≤ b12) --                                    | now as _radii_ are distances and distances are norms. The issue is
  | .factor f1 _ _ _,  .constant f2 => f1 = f2 --                             | how much Area is there. That is what _convergence_ seems to mean.
  | .factor f1 _ _ _,  .monomial f2 _ => f1.truth = f2 --                     | Good news is we can construct the area from the radii! π! GREEK!
end Polynomial --                                                             | We know this is a Number because it is typeset as Greek. Wait a sec.
 --                                                                           | Did *YOU the READER* know the formula for area before we sprung to
 --                                                                           | our conclusion? Ever notice how _O_ is both Roman and Greek?

/- CHORUS:                                            | Given multiple compilations of a compiler, we can just keep adding and adding and adding
ME: Divide and conquer                                | things to the compiler. Problem is, the compiler gets _BIGGER_ and _BIGGER_ on disk as well
COMPILER: We have standard libraries I can employ ----+ as takes _LONGER_ and _LONGER_ for the same text. This gives us a pretty good heuristic for
JAR JAR: MEESA ....... ........ approximately 3.      | estimating the bullshit in an argument _JUST_ from the number of heartbeats it takes.
ME: No need.                                          |
-/ --                                                 | I think we need to understand the _nowtrino_ a little better and then we just might have a
instance : LE Polynomial where --                     | Hilbert space.
  le := Polynomial.le

--| Numerically, the Galerkin process pulls off several tricks at once, hiding several choux pastries in his spherical (_topologically speaking_)
--| pockets (which is a _VERY_ different approximation to spherical point cows, which are cows that fell in the hole.) For those unfamiliar with
--| Choux pastry, it uses a dough similar to that of a donut (I believe the same as a _FRENCH_ cruller, check my math on this) inside of which
--| _ANOTHER_ hole exists in which _another_ universe of texture awaits to surprise the eater. That universe is _completely_ manufactured of jam.
--| Like what Lone Star uses to block communications. So, we get the GOAT Michael Jordan in here so we can make some Space Jam!

--                                                 | You got to _know when to hold'em_, _know when to fold'em_, _know when to run_.  Five of kind!
structure JordanProcess   -- Bullshit meter 2794   | o Jordan measure                 o Jordan norm-al form (another full house!)
    (Box: Type i) ---------------------------------+ o Jordan curve theorem           o Jordan Algebra               o the GOAT.
    (Pigeon: CarrierProcess Box) --                | Told you X-Zibit covered it.
    [DISTINGUISHABLE Box Pigeon]               [ADMISSIBLE Box Pigeon]                  [COUNTABLE Box Pigeon]             [ENCODED Box Pigeon]
    [RESIDUE Box Pigeon]                       [BINARY Box Pigeon]                      [REPEATABLE Box Pigeon]            [NUMERIC Box Pigeon]
    [REPRESENTABLE Box Pigeon]                 [PHYSICAL Box Pigeon]                    [COMPARABLE Box Pigeon]            [OBSERVED Box Pigeon]
    [PRESENT Box Pigeon]                       [MEASURABLE Box Pigeon]                  [GUNGAN Box Pigeon]                [SOURCE Box Pigeon]
    [SOURCE Box Pigeon]                        [EXECUTED Box Pigeon]                    [VALUE Box Pigeon]                 [MAGNITUDE Box Pigeon]
    [SCALED Box Pigeon]                        [LOAD Box Pigeon]

  where
  ANSYS_process : BASICProcess Box Pigeon -----+ The process is easy to follow. Just figure out which argument you can defer because it has the
  polynomial : Polynomial --                   | non-physical assumption in it. Box everything PHYSICAL you can to be wrap as PRESENTs and move to the
  --                                           | next. As the words lose meaning, their energy lessens and their frequencies drop into the musical.

  scale_and_shift? : Polynomial → Polynomial := fun p =>  ------------------------+ On a warm summers evening, on a Train bound for nowhere,
    match p with --                                                               | met up with a Knower, we were both to tired to sleep.
    -- 1. Shifting the Ground State (The "Zero" case) --                          | So we took turns a starein', out the window at a beacon
    -- We transition the background radiation into a theoretical field state. --  | As the quanta overtook us,
    | .constant f => .monomial f.truth (.null_space f) --                         | He began to speak.
    --                                                                            |
    -- 2. Scaling a Pure State                                                    | Now son, I made a life, outta reading peoples tables
    -- We take a monomial and promote it to an interaction (a factor).            | knowin' what their models were, knowing what they keep,
    -- We use the current basis as the anchor and jump the state forward.         | So if you don't mind me saying' I can see you're outta IP Spaces.
    | .monomial _ b => --                                                         | For a taste of your whiskey, I'll give you some advice.
        .factor Fact.Truth b (ANSYS_process.jmp? b) p --                          |
    --                                                                            | And the device got _DEATHLY QUIET_ and the math lost _ALL EXPRESSION_
    -- 3. The Recursive Scale (The "Add" case)                                    | Said, "If you're going to norm the space, boy, you gotta learn to do the rite."
    -- We maintain the coupling 'f', the anchor 'b1',                             |
    -- but we 'shift' the interacting basis 'b2' and preserve the history.        | You got to _KNOW WHEN TO HOLD'EM_!
    | .factor f _ b2 tail =>  --                                                  | (BTW, I just wrote that, _not_ AI.)
        .factor f b2 (ANSYS_process.jmp? b2) tail

-- Let's address the _elephant in the room_. Where in the *HELL* is the math that is going to compute a number? How are we 4000 lines into a Lean
-- "proof" about a number and we haven't seen the first number yet? And, if we keep writing code, we are going to run out of math words to throw
-- around. Pokémath. There must be a pokémath around here somewhere.. Pokémath are _countable_ and _sortable_ and carry _secret weapons_ of
-- _unknown mechanism_. Well, I guess like _five_ mechanisms or something.

/- CHORUS:                                                           | Numerical simulation builds an entire inner product space from polynomials
ME: There is an undeniably social aspect to understanding physics.   | on the _DAILY_. Each inner product space is sensitive to the problem it is
COMPILER: No there isn't, just the AST. -----------------------------+ solving. Any contraction of the simulation _IS_ by definion a linear system.
JAR JAR: MEESA AST                                                   | as all components of the device are _LINEAR_ in that there is assumed a
ME: We need a new friend. One that knows other pokémath.             | linear response curve for modeling of communications. One must use the network
-/ --                                                                | to communicate with a supercomputer. There may not exist computable
--                                                                   | non-linearity, but its ever finer approximation certainly does.
class OF   -- 2368
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [DISTINGUISHABLE Box Pigeon]     -- So, she _ASSUMES_ they have an undocumented one and proceeds to add the release to DISCOGS.
    [ADMISSIBLE Box Pigeon]          -- Only to realize she can't _EXACTLY_ find the _RIGHT_ release of their media in DISCOGS to catalog.
    [COUNTABLE Box Pigeon]           -- And spends hours every day on DISCOGS organizing her collection.
    [ENCODED Box Pigeon]             -- The audiophile purchases the finest copies of any analog recordings.
    [RESIDUE Box Pigeon]             -- The audiophile meticulously cleans her records.
    [BINARY Box Pigeon]              -- Invariably, there will be two camps.  The _AUDIOPHILE_ and the _NORMIE_.
    [REPEATABLE Box Pigeon]          -- And I can burn the output of the DAC to a CD?  Holy crap!
    [NUMERIC Box Pigeon]             -- How about that, I just built a DAC !?
    [REPRESENTABLE Box Pigeon]       -- Which means I can quantize and take the DFT!
    [PHYSICAL Box Pigeon]            -- I just know that what I hear is measured by this physical process of oscillations.
    [COMPARABLE Box Pigeon]          -- Dunno what they mean though.
    [OBSERVED Box Pigeon]            -- There we are, I found some phonemes.
    [PRESENT Box Pigeon]             -- Fucking Jar Jar. Let me use an osciliscope and measure their tones and figure it out.
    [MEASURABLE Box Pigeon]          -- MEESA TRUE!
    [GUNGAN Box Pigeon]              -- Translate that into Gungan and ask Jar Jar Binks if he can relate to it?
    [SOURCE Box Pigeon]              -- To quote Johnny Five: "NEED INPUT!"  Doesn't matter what kind.
    [EXECUTED Box Pigeon]            -- Actually, I take that back, we have a program that can compute the value from an input
    [VALUE Box Pigeon]               -- No, just some sort of representation of the value.
    [MAGNITUDE Box Pigeon]           -- And this the length?   Do we have _e^iθ_?
    [SCALED Box Pigeon]              -- Could this possibly represent the direction of said load?
    [LOAD Box Pigeon]                -- hmmm, a _LOAD_?  Like _μ_ __N__?
--     ^                                ^
--     |                                |   +------------- Just this once, let's read it ^ this way.
--     +--------+-----------------------+   |
--              |                           |
--              +---------------------------+


  where
  galerkin_process : JordanProcess Box Pigeon  --------------------------------------------> Slam dunk the pigeon in the box! BOOM SHAKA LAKA!

  finite? : Polynomial → Polynomial → Prop := fun p1 p2 =>  ---------------+ So you get a scientific dunking contest: who can put a pigeon in a
    match p1, p2 with --                                                   | box the most.... scientifically.
    -- 1. Convergence to the Ground State --                               |
    -- If we move from any field interaction to a constant, --             | Some scientists think that it is the aerobatics that make the dunk,
    -- the transform is finite. The energy has successfully --             | back flips, whizbang, behind the back, over the top, 4th and goal
    -- dissipated into the background.                                     | on the TEN.
    | _, .constant _ => True --                                            |
    --                                                                     | Some scientists think that the point of the dunk is to put the ball
    -- 11. Stationary Field (The Eigenvalue Hit)                           | in the hole repeatably to see how big a number the scoreboard can hold
    -- If the transform results in the exact same theoretical              | before it breaks.
    -- state, we've found a fixed point in the Hilbert space.              |
    -- The arm-waving has stopped.                                         | I present the first aerobatic, always in the hole method: the spline
    | .monomial t1 b1, .monomial t2 b2 => t1 = t2 ∧ b1 = b2 --             | that models the spline process itself!

    -- 111. The Lanczos Residual Check
    -- If we are moving between interactions (factors), the transform is only    | Translation layer from above. Basically, you can clamp the element
    -- finite if the informational strain (Fact) remains invariant.              | and the nodes of the element don't move unless another element
    -- If the Fact flips, the transform is "infinite" (a singularity/jump).      | changes shape. So, as long as no other element is changing, then
    | .factor f1 _ _ _, .factor f2 _ _ _ => f1 = f2 -----------------------------+ the current element is _free_ to change shape without worrying
    --                                                                           | about where it is relative to the rest of the paradoxical
    -- 4. The Divergence -------------------------------------------------+      | not-sure-what. The more they stay still, the more they are
    -- Moving from a grounded constant back into an excited factor is     |      | free to move. You have to force them to sit still. Kick out
    -- an "infinite" injection of energy. Disallow for convergence.       |      | Heisenberg and the party is HALTED.
    | .constant _, .factor _ _ _ _ => False --                            |
    | .constant _, .monomial _ _ => False --                              |                | Numbers have started leaking into the argument all over
    --                                                                    |                | the place now. ‖1(i)‖, MEESA TWO, and this external
    -- 5. Cross-talk -----------------------------------------------------+----------------+ evaluation library that measures how much work the
    | .monomial t1 _, .factor f2 _ _ _ => t1 = f2.truth --                                 | compiler is doing behind the scenes.
    | .factor f1 _ _ _, .monomial t2 _ => f1.truth = t2


--| *YOU the READER* are right. *YOU the KNOWER* isn't going to buy any of this. So, just tell *YOU the KNOWER* that _ALL WE ARE DOING_ is drawing
--| the _TRAIN of THOUGHT_ that Einstein took. We don't get to put the stations where they are. So, we just put a spline through them, just like
--| Planck taught us how.
--|
--| My apologies to Planck.

/-- CHORUS:                                                  | The first words you wake up to in the morning as a student of numerical analysis is
ME: I have this shotgun blast of a scatter. Gimme a slope.   | the phrase: _Assume f ∈ C²_. This _one_ assumption unlocks _SO MUCH_ computation, not
COMPILER: I don't do that kind of math.                      | the least of which is the _Calculus of Variations_.
JAR JAR: MEESA y=x. -----------------------------------------+
-/ --                                                        | The _Calculus of Variations_ allows you to push the envelope to _Assume f ∈ C¹_. Also,
inductive Spline  -- 152                                     | Jar Jar is technically T=T. While not necessarily _different_, they certainly _can_
  | observation: Prop → Spline --                            | be the same when it varies in the other direction. You will be very hard pressed to
  | knot: Prop → Polynomial → Spline → Spline --             +---------------+ find a _difference_ between this function and the _physical laws_ that
  | interpolant: Fact → Polynomial → Polynomial → Spline → Spline → Spline --| govern an electron in the not _too_ distant future. I mean, it is still
--                                                           +---------------+ quite distance. As for the code to the left, this is a representation
--                                                           | of a B-spline. Each knot is added by one term of the polynomial and these are combined
--                                                           | recursively to generate a Weierstrauss polynomial evaluated in Newton fashion that
--                                                           | performs a Lagrange-style interpolation to build a method that optimizes the
--                                                           | Sobolev-norm generated by a continuous mathematical problem, and solved with a Krylov
--                                                           | space optimization. 5 names. All GOATs.

namespace Spline

def le : Spline → Spline → Prop := fun s1 s2 => ---------------------------+ This is the _HARD_ argument. This is the thing we have to show
  match s1, s2 with --                                                     | *YOU the KNOWER* several different times, several different ways. I will
  -- 1. Observation (The Ground State) --                                  | DO MY ABSOLUTE BEST to be good and not obfusplain the math except where
  -- An observation is the "unit" of the manifold.                         | obfusplaining is the best interphoneme. While grammar and word choice,
  -- It is less than any knot because a knot is an observation PLUS work.  | placement, all that is important, we _CANNOT_ measure those right now,
  | .observation t1, .observation t2 => t1 = t2 --                         | what we can do is setup a thought experiment of measuring a really
  | .observation _, .knot _ _ _ => True --                                 | high-fidelity recording and explain that the reason why it is so high
  | .observation _, .interpolant _ _ _ _ _ => True --                      | fidelity is because much of the regular fideltiy was removed and replaced
  --                                                                       | with extremely well machined parts. Things that can change linear motion
  -- 2. The Knot (The First Variation) --                                  | into circular (the cam) are easy-peasy.  All day long. Except, you have
  -- A knot is a localized field interaction.                              | to make sure the cam rotates the correct way from TDC. Speaking of, did
  -- It is contained by another knot if their phases match                 | you know it is impossible to hit a ball with rational force to make it
  -- and their internal polynomials/histories are ordered.                 | stop at the top of the hill without friction? I think Zeno said that.
  | .knot t1 p1 tail1, .knot t2 p2 tail2 => --                             |
      t1 = t2 ∧ p1 ≤ p2 ∧ (le tail1 tail2) --                              | Where was I? Oh yeah, on the *physical* impossibility of a universe with
  --                                                                       | distance as norm being in a state of a ball coming to rest at the top of
  -- 3. The Interpolant (The Second Variation / The Weak Derivative)       | a hill. At least one that can compute the norm of the force. I offer that
  -- This is the "Inverse Gauss" arm.                                      | there is no reason for Euler's method to work on y'=sqrt(x) at x=0.
  -- An interpolant contains a knot if the knot's polynomial               |
  -- satisfies the weak boundary conditions of the interpolation.          | No calculus required, write the method down. 0 + 0·x = 0 ∎ ("That's
  | .knot t1 p1 _, .interpolant f2 p_in p_out _ _ => --                    | 𝔽(1)-ny to me, right thar." (Tow Mater, you know _without_ the -tuh).
      t1 = f2.truth ∧ p1 ≤ p_in ∧ p1 ≤ p_out --                            |
  --                                                                       | But that's not the kind of math Lean normally does. It is the kind of
  -- 4. Interpolant vs Interpolant (The Manifold Convergence)              | math _I_ need it to do.
  -- This is the Cauchy check. s1 ≤ s2 if s1 is a sub-path of the
  -- geodesic defined by s2.
  | .interpolant f1 i1 o1 left1 right1, .interpolant f2 i2 o2 left2 right2 => --+ Fully specified, we understand how to factor splines quartically,
      f1 = f2 ∧ i1 ≤ i2 ∧ o1 ≤ o2 ∧ (le left1 left2) ∧ (le right1 right2)--     | not that we _CAN_ do it. I guess one more _IS_ out of the question
  --                                                                            | here. I bet we can factor _eigenvalue_ now and find out _REALLY_
  -- 5. Disallow Retrocausality                                                 | what it means
  -- A complex interpolation cannot be contained within a simple observation.
  --Ockham enshrined.
  | .knot _ _ _, .observation _ => False
  | .interpolant _ _ _ _ _, .observation _ => False
  | .interpolant _ _ _ _ _, .knot _ _ _ => False

end Spline

/- CHORUS:
ME: When integrating, you just need to know what is under the curve.  | The spline represented above will eventually be cubic. What we have in
COMPILER: Easy.                                                       | JAR JAR is the compiled version of counting written as multiplication, yet
JAR JAR: MEESA y≤Θ(1×x). ---------------------------------------------+ another AST. That AST can _compute_ a polynomial. It only has one name. So
ME: Close enough                                                      | write now, it is .monomial y=x. Later, it will be polynomal with the names
-/ --                                                                 | {y=x, y=x³}. And since we can factor names quartically, this allows us to
instance : LE Spline where --                                         | write things like {y=‖1(i)‖₂×x³} and guarantee they are HALTED. That sounds
  le := Spline.le --                                                  | 𝔽(1)-ny. Coincidentally, rfl requires about 5 heartbeats to elaborate. We
--                                                                    | _JUST_ might sneak this by JAR JAR.

-- And the _ABSOLUTE BEST_ part of this argument is, very _LITTLE_ of it really affects the calculation. And it was good enough to show us where.
-- Most of it _SIMPLY DOESN'T MATTER_ to the nowtino we are counting. You see how to get by the Polynomial wall of text rite? CONTRAVARIANTLY.
-- All aboard the Einstein Train of Thought(tm), next stop tensor notation, the convergence of appearnce.

-- Tune in next week for: No, he can't read my _POKER FACE_!

end Measurement
