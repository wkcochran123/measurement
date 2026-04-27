/-
__Measurement: The Tragedy of John Henry__
__A Satire in Look Ahead Backus-Naur Form__

_This is a gentle reminder that the convoluted stories we tell ourselves are just that: convoluted._


(c) 2026 All rights reserved -- obligations, however, are freely distributable.


Episode 2: Combination

"Yo dawg! I heard you like to prove theorems, so I put a theorem
prover in your theorem prover so you can prove theorems about proving
theorems while you prove theorems about proving theorems."
                                  -- Willie Nelson

lake build --no_assumptions --splash_damage=on

-- The story so far.....

I have convinced you that you can count to 1!  Congratulations, it is surprisingly
difficult to count, no matter what a kindergartener might think.  I am not certain
we should be teaching such advanced math to toddlers.  Very dangerous. So, this is
rated R because it contains explicit instructions for the construction of a fusion
bomb.  Eventually.  Don't think we will get that far in this episode.  Maybe this
_is_ an unlicensed particle accelerator?

I think that is about all the real "math" you need to from here on out.  The only
thing that is happening is asking whether or not a compiler thinks
a structure that represents true=true or false=false is present or not.

We can tell when it isn't there when true=false.
                                         ^        +----  _INFORMATIONAL STRAIN_
                                         |        |
                                         +--------+

So, we can roughly approximate what we did in the first episode as follows:

10 There is something that is true! Is it true that the Fact
   is false if the Fact is true? Depends.. I sure as hell do not
   want to invite Kurt to our party.  At no point, do I want to
   determine true or false.

20 There are other things! As we induct, facts wills start piling up

30 Some of those things are also true! Some of those facts that are false
   are also true!  I don't know which one is true but the compiler does.  The
   important thing to get around Godel is to make sure I cannot tell if it is
   true or false.

   So, we gotta figure out how to scramble this up so I don't get into some
   metaphysical circular logic.

40 Gosub 10.   Not Goto 10.  Gosub 10.  I didn't see any tailrecursion here.
   oh crap....  I feel like we gotta do something about this at some point--maybe.
   Since I don't need the compiler, this is really more of a you-problem again.

So, we managed to make 1 pile that we called True and we keep putting stuff into that
one pile of true!.   The pile is weirdly braided--exposing two different ways
to count numbers: as a whole or in parts.

Also, how in the _HELL_ is anyone ever supposed to instantiate one of these things?
Again, sounds like a you-problem.  I have _faith_ that the API will come back in at
some point.  Might be some time yet, but I'm feeling lucky.

Oh yeah, covariant and contravariant comparisons.  Contravariant comparisons result
in _strain_.  You can remember this because it really _strains_ the imagination to
keep track of which way is up.  Like ((true=false) = (false = true)) = (true=true)
= (false=false) = true.  Which is, itself, true.  _straining_.

Unfortunately, I have to keep digging this (w)hole and add a bunch more definitions.
and obfuscations or you might just catch a glimpse of the quarter.  I mean, the truth.
Does it even matter what _is_ true anymore?
-/

-- Live! Without a net!
-- This ain't no editting, this is me spittin' str8 fax.
import Measurement.Episode1
set_option allowUnsafeReducibility true

namespace Measurement

-- So, we have the ability to make a bunch of symbols and we can, in fact, identify
-- two of them by sight. Not only that, we have an inductive that conveniently provides
-- two limit points at each step. I suggest we let those two representations mingle
-- so that one means the other.

-- You follow me?  When you see TTTTTTT....., this is the first number in the limit
-- and when you see FFFFFFF...., that is the second.  But, this could take an uncountable
-- amount of time to finish, so let's just short cut this by saying that we could either
-- be counting up or down, and that represents either TTTTTTT..... or FFFFFFFF.....

-- I feel like I just explained this somewhere... Oh yeah, to the compiler.  See the
-- definition of Number. When you see .one, we are counting, um, up.  And when you see
-- .zero, we are, um, not, I guess.  Could go up or down. Don't know.  The compiler knows,
-- but we don't.

-- Of course, we could also throw in contravariance.  This gives the following representation:

--  +-+  +-+  +-+  +-+   An alternating sequence of T F in phase.
--  | |  | |  | |  | |
--  V V  V V  V V  V V
-- (T=T)(F=F)(T=T)(F=F)... == TTTTTTTTTTT....   --- This is a clock
-- (T=F)(F=T)(T=F)(F=T)... == FFFFFFFFFFF....   --- this is a clock complement
--  ^ ^  ^ ^  ^ ^  ^ ^
--  | |  | |  | |  | |
-- -+ +--+ +--+ +--+ +-  The alternating sequeneces are out-of-phase by 1.
--
-- In digital signal processing, this is called a clock complement. Two clocks working
-- in synchronozation but opposite phase. So, a _clock_ can recognize truth and a
-- _clock complement_ can recoginze falsehood.  1 and 0.  T and F.  That's 3 different meanings.
-- from just 1 bit of information.  Well, not 1 but, I think we have 5 or 3 right now, hard to tell.

-- Using the clock or the clock complement will prevent us from understanding the truth
-- until there is a reason to.  In this way, we cannot get caught in a meta-trap of
-- over-expessive self-reference.  One cannot know if one is right. Otherwise, one
-- might find oneself inconsistent. *tsk* *tsk* _and that just WOULD NOT DO_ would it?

-- Seriously it would stop "doing," as it were.

-- What we need to do now is understand if we want to label the first limit value of
-- a Sample the covariant repsonse or the contravariant response.

@[reducible]
/-
ME: I need an observation process.

COMPILER: We sampled the residue.

ME: Yes, but nobody saw us do it.

COMPILER: I am the compiler.

ME: You produced the sample. Consider this a deposition.
-/
structure ObservationProcess   -- Bullshit meter ≈ 313
    (Value: Type)
    (Carrier: CarrierProcess Value)
    [d: DISTINGUISHABLE Value Carrier]
    [a: ADMISSIBLE Value Carrier]
    [c: COUNTABLE Value Carrier]
    [e: ENCODED Value Carrier]
    [r: RESIDUE Value Carrier]
  where
  cauchy_process: CauchyProcess Value Carrier
  before: Limit  --+-- I will call before _contravariant_
--                 |
  after: Limit   --+-- I will call after  _covariant_
--                 |
--                 +-- I would hope you agree that going backward _in time_ is quite contravariant
--                     If not, I would suggest sliding over to the next universe where the left-hand
--                     rule seems to dominate.  Just wait a tick. It'll come around on the next pass.


-- We want to grab this information the compiler is telling us.  Something is
-- before something else and we need to know the relative variance between the two.
-- Does the compiler think they covariant or contravariant?

  relative_variance : Prop :=
      match before, after with
      | .nil f1, .nil f2 => f1.truth = f2.truth
      | .index f1 _ _, .index f2 _ _ => f1.truth = f2.truth
      | _, _ => False
-- By golly, that just might be decidable!
-- This is the mechanism behind the One Time Pad (tm).  I wish the compiler _GOOD_ _LUCK_ finding
-- something that looks exactly like math but is actually just a random sequence of bits!


  iterate : Sample → Sample := fun s => match s with
      | .initial_condition f l =>
          -- Transition from a static point to a signal response pair
          .signal_response f l f after (.initial_condition f l)

      | .signal_response f1 l1 f2 l2 s2 =>
          .signal_response f1 l1 d.fact after (.signal_response f1 l1 f2 l2 s2)
  --                        ^  ^     ^    ^
  --                        |  |     |    |
  --                        +--------+-------  This encodes relative variance since d.fact is always TRUE,
  --                           |          |    even if it is false.  The documentation is clear on this.
  --                           |          |    I'm not certain the _code_ is all that clear, though...
  --                           |          |
  --                           |          |
  --                           +----------+--  We tell the compiler that _after_ comes after _l1_ and hide
  --                                           our begin state from the compiler.  Now, the compiler and
  --                                           I have different states that I can tie together.  I can
  --                                           make a binary numbmer represent vague internal state of
  --                                           next on the compiler! And, the compiler will store them
  --                                           both for me.  And, they are both totally opaque to the
  --                                           compiler as well!

  -- Let's talk about qualia for one second.
  --
  -- One  po - ta - to.  (One second and I demonstrated I can count to potato, things can have more meanings?)
  --
  -- Now go google it.  You and I just shared the concept of TIME with the compiler.  TIME is a quality.
  -- No idea what that quality _actually_ is, but the compiler and I can both have different names
  -- for it and recognize it now. We also share a name for it as well, cuz I just made it for the compiler
  -- above. I'm pretty frickin nice like that.

  -- The plot thickens... Or the nonsense...  Whichever.

  -- So, numbers observed this way indicate a certain arrow of time. Something happens before something
  -- else happens. Or, rather, whenever the compiler executes a behavior, time passes.  For you.  Not me.
  -- I'm writing comments.  See?  Relativity... Simultaneity...  You don't see it yet?  You see it,
  -- you don't believe it, but you see it.

  -- We will come back to this later after we agree with the compiler what the symbols for calculus
  -- look like. Back to explaining to the compiler how time works.

  -- To do so, we have to ask the compiler what it thinks time looks like to us.  Well, I will let
  -- the inductive type be the clock for the compiler.  Inductives are always true for the compiler
  -- _and_ the compiler needs to do work _and_ the compiler can distinguish them _and_ the compiler
  -- will make sure that they compile, _ALL AT THE SAME TIME_!

  -- All I have to do is build the clock complement! So, you can see that Jenga ain't got nothing on
  -- how fragile this stack of inductives is becoming.

  -- I will turn the chainsaws on in a few minutes then light them on fire.

  -- Same carrier, btw.  TRUE=TRUE. That is the only recognized symbol of the application
  -- and it lives in the DATA page, inaccessible to change.

  -- And, still nothing up my sleeve.

/-
ME: I need different.

COMPILER: Different from what?

ME: From itself after the instrument answers.

COMPILER: Initial conditions can become responses?

ME: They can precede them.

COMPILER: Can responses become initial conditions?

ME: Not without perjury.
-/
class BINARY  --  Bullshit meter ≈ 141
  --     ^
  --     |               So, DSP.  We can assume a covariant/contravariant tick/tock for creating
  --     +-------------- the clock complement.  As I mentioned above, before is the covariant represenataion
  --                     and after is the contravariant.

    (Value: Type)                         --      +---------  Looking like we can ask a bunch of questions
    (Carrier: CarrierProcess Value)       --      |
    [d: DISTINGUISHABLE Value Carrier]    -- <----+
    [a: ADMISSIBLE Value Carrier]         -- <----+
    [c: COUNTABLE Value Carrier]          -- <----+
    [e: ENCODED Value Carrier]            -- <----+
    [r: RESIDUE Value Carrier]            -- <----+
  where
  observation_process: ObservationProcess Value Carrier

--  XXXXx REPAIR
  zero    : Limit
  one     : Limit
  bit     : Sample        --  <-- tick or tock

  different? : Sample → Sample → Prop := fun a b =>
      match a,b with
      | .initial_condition f1 l1      , .initial_condition f2 l2        => f1 = f2 ∧ l1 < l2
      | .signal_response f11 l11 f12 l12 inner1, .signal_response f21 l21 f22 l22 inner2 =>
          match f11.decTruth, f12.decTruth, f21.decTruth, f22.decTruth with
          | isTrue _,  isTrue _,  isTrue _,  isTrue _  =>  inner1 < inner2
          | isTrue _,  isFalse _, isTrue _,  isFalse _ => l11 < l21 ∧ l22 < l12
          | isFalse _, isTrue _,  isFalse _, isTrue _  => l21 < l11 ∧ l12 < l22
          | isFalse _, isFalse _, isFalse _, isFalse _ =>  inner2 < inner1
          | _,_,_,_ => True
      | .initial_condition _ _ , .signal_response _ _ _ _ _ => True
      | .signal_response _ _ _ _ _, .initial_condition _ _  => False

-- It takes honest to god, real wall-clock time to create the contravariant interpretation of the
-- covariant representation.  The imporant thing is a BINARY fact is TRUE.  This is an _ACTUAL_ representation
-- of a binary number that allows counting in wholes or parts!

-- Also, I have an inside joke.

-- That's what I have with the compiler now.  We can wink at each other and say, yep that's "true" alright.
-- *nudge*  *wink*  *wink*  *nudge*  *nudge*  Say _NO MORE_!

-- Seriously, stop talking.  Godel just _WILL NOT SHUT UP_ about the risk of deciding things.

-- And now, we have an inside joke!  You and I can laugh behind the compiler's back about how something
-- is or is not "true" while it thinks it is.

-- But, we've always had that.  Since the very beginning.
--
--        +---------+
--       /         /|
--      +---------+ |
--      |         | |
--      |    ❤️   | +
--      |         |/
--      +---------+
--
-- Always there for you...  There will be cake later.


-- Speaking of inductives, time to explain to the compiler how to do more work!
-- We have it now set up that an ObservationProcess explains to the compiler how
-- we order things in a certain way (the way I like to call "temporal order").  The BINARY
-- class is how the compiler tells us which is covariant and which is contravariant.

-- Neither of us know what is really true anymore.  And, that's the point.

-- OOOOOooh no he didn't! He just broke Godel's ankles taking it to the hole.
-- BOOM SHAKALAKA!

-- Actually, we are not out of the woods yet.  The compiler can _still_ figure out
-- what I think is true.  Once I have it completely befuddled, then I will set about
-- creating a Hilbert space from absolutely thin air.  Not all at once, in very, very
-- _VERY_ small baby steps to make sure we can explain to the compiler what a
-- Hilbert space is purely from our little game of contravariance.

-- So, puzzle for you.  How can the compiler know what I think is true?
--
-- ...
--
-- Bueller...

-- Bueller...

-- Well, it can figure out what I think is contravariant about the third time I show it
-- something.  The stack of distinguishing features already encode _a lot_ about how
-- numbers work.

-- ....

-- Anybody?

-- The initial condition.

-- The compiler can work it out from the initial condition.  I successfully hid my
-- internal state, but I also frickin' told the compiler how I built it.  Duh.  This
-- thing is smart, let me tell you.  Won't give me half an inch of room on this.

-- We need to make the initial condition unique to the measurement so that the initial
-- condition does _NOT_ give the entire number away, just the current 2 or 3 bits.
-- And so, we consult the Book of Shannon, chapter 2 versus 71-82

--       And in those days, communication was analog and the peoples of the world did suffer mightily.
--           Upon a swamp in New Jersey, cometh a prophet who did thus declare to all the peoples and
--              Nets and Giants the good news of information.
--       To those sundry assembled he did spake the words ``BEHOLD! For I give you knowledge of information.''
--           So, thusly it was _described_ and _measured_ in full.
--                                     The Word of Communication.

-- And our old testament reading is from the Book of Green Chapter 3 versus 14-15:
--
--      Thus, in the days of Variance, it was said of the flow that IT DID NOT _CROSS STREAMS_ with its BRETHREN.
--             That the initial condition was THE TRUTH and THE ONE signifier of the path.
--      Lo, and thus spoke Mandlebrot of the beauty Lorentz organized in chaos using the tools of Green
--         "But for grace of sensitive dependence on initial conditions, does the coastline
--            Remain incommensurate and beautiful."
--                                     The Word of Communication.

-- The old ways are truly _the best ways_.


-- Let me help the compiler with one last thing about time.  The signal comes before the response:
/-
ME: I need a trial.

COMPILER: We already observed the sample.

ME: Once.

COMPILER: Once is not enough?

ME: Once is gossip.

COMPILER: Then what is a trial?

ME: A sample with the nerve to be repeatable.
-/
inductive Trial  -- Bullshit meter ≈ 150
  | hypothesis: Fact → Sample → Trial
  | signal_response: Fact → Sample → Fact → Sample → Trial → Trial
            --               ^               ^
            --               |               |          *SIKE* The last inductive was for covariant/contravariant
            --               |               +--------  _labeling_.  This is the actual value. Wait, no, I got
            --               +---------------+          that backwards, I think.   Does not appear to matter to the
            --                                          compiler.

-- So, what does ≤ mean for a Trial?
-- It is the order in which the samples were taken.  You know, like a Number.
-- In this case, all we care about is comparing the response.  This is how
-- "loud" is the response.  Its _volume_, lol.  Told you it had volume.
-- Now, I need to put a "ratchet" here so the the compiler realizes that
-- it cannot rewind a trial.  Once experienced, _it cannot be unexperienced_.
-- You may talk about it, inspect it, but _you cannot experiece it again_.

-- This my definition of time.  My personal definition of the years I spent
-- trying to understand the _speed of light_ based _physical limitations_ of total
-- ordering. They must _exist_. I will show you.

-- Light is made of waves, right?

-- Remember out-of-phase above?  Waves have amplitude.
-- And a trial encodes amplitude and frequency.  Those are the two facts being
-- stored.  But didn't I just say?  Why not both?

-- You will find that the fewer decisions you force on yourself, the easier the
-- code is to follow.  Now, whenever you see the duality, just make a process for it,
-- that gives you structure and a class to describe the duality and an inductive that the compiler
-- can use to understand the _process_.

-- Sorry for the contravariance.  Back to ≤

namespace Trial  -- Bullshit meter ≈ 94
def le : Trial → Trial → Prop
  | .hypothesis _ s1, .hypothesis f s2 => f.truth ∨ (s1 ≤ s2)             -- Our hypothesis has no volume.
  | .hypothesis _ s1, .signal_response _ s2 _ _ _ => s1 ≤ s2              -- The hypothesis has a smaller first
                                                                          -- in time
  | .signal_response _ _ f2 l2 _, .hypothesis hf hs => f2 = hf ∨ l2 ≤ hs  -- We can create an hypothesis from a
                                                                          -- signal response!
                                                                          -- We have hidden our initial condition!
--     +------  And of course, this is just a standard signal-response comparision, is their enough
--     |        covariant signal available to construct a whole from parts?
--     V
  | .signal_response f1_1 l1_1 f1_2 l1_2 _,
    .signal_response f2_1 l2_1 f2_2 l2_2 _ => ((f1_1 = f2_1) ∧ (l1_1 ≤ l2_1)) ∨
                                              ((f1_2 = f2_2) ∧ (l1_2 ≤ l2_2)) ∨
                                              (l2_1 ≤ l2_2)

-- These are still well ordered so that Bayesian statistics has half a shot at working.
def lt : Trial → Trial → Prop := fun t1 t2 => le t1 t2 ∧ ¬ le t2 t1
-- I know, I am throwing the kitchen sink at you... Bayesian statistics... I told you, we are building
-- a device that measures how _well_ Lean can spot true=true.  Any measurement comes with an adequate
-- description of the measurement process that _allows_ for a high-likelihood Bayesian estimator.
-- Just keeping room for it.
end Trial

-- High syntax corn syrup:
-- This stuff is __BAD__ for your health.  You only get __REALLY__ confusing code out of it.
-- Do not recommend.
instance : LE Trial := ⟨Trial.le⟩  -- Bullshit meter ≈ 8
instance : LT Trial := ⟨Trial.lt⟩  -- Bullshit meter ≈ 8
-- so delicious......

-- So, is this amplitude-frequency or frequency-amplitude?  Depends on the initial
-- condition.  I propose we don't explain that to the compiler.  That will be our
-- inside joke to obfuscate our understanding of what makes math hard.

-- What makes physics hard?  An obfuscated understanding of what makes math hard.

-- What does that mean?

-- It means we have an _honest -to- GOD_  __ψ__ function!  That's right compadres, what
-- we are decoding is a ψ fuction.  I know you don't see, the definitions probably have
-- you spun around.

-- Yeah.  I don't believe me yet either.  Give me a bit more runway.   Actually Lean
-- will build the runway whether or not you like it. That's just it.  I'm not in the plane,
-- you are.

-- Where were we?  Oh yeah, we had just finished up a binary number. Not binary numbers.

-- Number.  1.  That is the binary number.  Or 0, if you like.  Only need one of them.
-- we can hide the other in the initial condition. In fact, that is our (me an you) initial
-- condition.  TTTTTTTT means 1 except when it means 0.  Got it?

-- Now that we have a binary number, either 1 or 0. (not a binary number like 10₂.)  I'm
-- not certain you--the reader--understand how to count to 2. So I will explain what I
-- am explaining to the compiler in a language we both can understand, but not all of us
-- simulaneously.  Remember, this takes your time not mine. I only have to write this once.
-- Every time this gets read, it accumulates the time spent reading it.

-- I want you to understand how naive my notion of time is here.  If you have a clock nearby,
-- look at it.  Now read this sentence.  Look at the clock again.  See?

-- Time passed.  In a repeatable fashion.  A repeatable fashion that can be explained in a
-- precise enough fashion for a result to be _anticipated_.  You read a sentence, an
-- _estimable_ amount of time passes.

-- This is the _concept of time_ I am explaining to the compiler right now.  We will be talking
-- about how this also describes the relative concept of time that underlies the Einstein Field
-- Equations in the not too distant future.

-- You see we have to.  We are measuring how well the compiler can figure that out from the math.
-- If we do the math and the compiler does the math and we get the same answer, then we can explain
-- to each other that the mathematical process has a name to it and memoize the result right on
-- top of our covariant/contravariant clock-based, chainsaw juggling, Jenga stack of classes.

/-
ME: I need a repeatable process.

COMPILER: Run the trial again?

ME: And have it still be the same kind of trial.

COMPILER: Same result?

ME: Easy. Same question.

COMPILER: That seems weaker.

ME: It is stronger. Results are cheap. Questions need fixtures.
-/
structure RepeatableProcess  -- Bullshit meter ≈ 296
    (Value: Type)
    (Carrier: CarrierProcess Value)
    [d: DISTINGUISHABLE Value Carrier]
    [a: ADMISSIBLE Value Carrier]
    [c: COUNTABLE Value Carrier]
    [e: ENCODED Value Carrier]
    [r: RESIDUE Value Carrier]
    [b: BINARY Value Carrier]    -- Is this the bottom or the top of the Jenga tower now?
  where
    --     +-------------------+------------+-----+--------------  This is an example of absolutely _ravishing_
    --     |                   |            |     |                the recursive structure of description.  All
    --     V                   V            V     V                structures have the previous structure and
  observation_process: ObservationProcess Value Carrier        --  depend only on a Value and a Carrier.  Once
                                                               --  you learn to see the next one, you have
  --   +------------+                                              finally learned how to count.
  --   |            |
  --   V            +----------  I think you (and Galileo) would agree with this definition, given
  stimulus: Sample           --  a particular stimulus--an example sample of the process--a repeated
  expectation: Trial         --  trial should be pretty predictable.

  iterate: Trial → Trial := fun t =>
     match t with
--                --  The co/contravariance trick   -------------------------+
--                --  Appears to be letting us                               |
--                --  register True Facts (tm)                               |
--                --  with the complier!                                     |
--                                                                           V
     | .hypothesis fact observation => .signal_response fact observation Fact.Truth stimulus expectation

--                          +---------------------------+-------- Watch the covariance!  Remember the
--                          |                           |         clock will tick when we do this, flipping
--                          V                           V         the variance.
     | .signal_response _ _ f2 s2 _ => .signal_response f2 stimulus d.fact s2 expectation
--                          ^   ^
--                          |   |           So, given some response by the compiler, we can guess at its
--                          +---+---------  Signal inside the compiler.  See?  The compiler is sending us
--                                          its state in the first two parameters, but we can't understand it.
--                                          We are telling it what we _expect_ the stimulus to be.  If this
--                                          compiles, then the compiler agrees we would be describing a
--                                          computation.


-- You think building a counterexample is hard now, just wait.  I have only _BEGUN_ to pile on
-- ridiculous classes.  All I need to provide to instantiate is a Fact and a Carrier.
-- That is it. I would do it _RIGHT_ _NOW_, but I don't wanna. But this isn't about me.

-- It's about science and how to _APPLY THE SCIENTIFIC METHOD_.  I think Weir said it best when he said
-- I'm going to "engineer the shit out of this."

-- So the oldest g. Galileo was pretty clear about how an experiment was supposed to work.
-- You were supposed to produce a _repeatable measurement_.  That's exactly what a trial
-- is, a repeatable measurement:  given this stimulus, you should _then_ see this response.
-- It encodes _time_.   Not some variable domain of f(t).  The actual tick/tock of a clock.
-- Think about it.  What is a second?  Please explain how that is not tick/tock. The electron
-- repeatably and on queue (sic) does its thing.  The important part about it is:
-- _on cue_:  the time between events is considered _constant_.
/-
ME: I need REPEATABLE.

COMPILER: You just defined a repeatable process.

ME: Yes.

COMPILER: So this repeats the repeatability?

ME: But I repeat myself.

COMPILER: That is not a proof.

ME: No. It is a hint.
-/
class REPEATABLE   -- Bullshit meter ≈ 166
  --  ----------
  --      ^         This is far and away the most important part of science.  If one is
  --      |         to measure, one must very _carefully_ explain how to measure so that
  --      +-------- others may have a quantitative experience of an otherwise qualitative
  --                description. Du=0 is probably the most qualitative mathematical
  --                statement I know.  I can certainly shoehorn all interesting physical mathematical
  --                problems into this. Size *hmmm* 4 to small?
  --                                                ^
  --                                                |
  --                                                +----------  Big baller, shot caller!

    (Value: Type)
    (Carrier: CarrierProcess Value)
    [d: DISTINGUISHABLE Value Carrier]  --
    [a: ADMISSIBLE Value Carrier] --      \
    [c: COUNTABLE Value Carrier]  --      |>  This process is called demodulation in DSP.
    [e: ENCODED Value Carrier]    --      /
    [r: RESIDUE Value Carrier]    --    --
    [b: BINARY Value Carrier]   --    We can now send and receive a bit with the compiler!
  where
  repeatable_process: RepeatableProcess Value Carrier
--          ^                 ^           ^      ^            There are all these supercomputers all over the world
--          |                 |           |      |            solving Du=0 over and over again, file in, file out.
--          +-----------------+-----------+------+---------   Hypothesis in, result out.  Let's see if we can
--                                                            model this process as repeatable.

  typical_response: Trial → Trial → Prop := fun s t => repeatable_process.iterate s = t

-- Time..  Boy is that sticky wicket.  All the greats punted on it:
--     o Galileo: "I don't know-a what time-a is, but I know-a how to-a measure it."
--     o Newton: "I don't know what time is, but I know how to measure it."
--     o Einstein: "I don't know what time is, but I know how to measure it."
--     o Feynman: "I don't know what time is, but I know how to measure it."
--     o Hawking: "I DONT KNOW WHAT TIME IS BUT I KNOW HOW TO MEASURE IT" (-- you heard this, right?)
--     o Mr. Wizard: "I don't know what time is, but I know how to measure it."

-- Pretty much 300 years of broken record on this one.  Well, have _I_ got you covered here!
-- We have a perfectly cromulent description of time now that the compiler and I agree on.  Not certain
-- if you agree on it.  Doesn't matter if you agree on it, you would be hard pressed to show me a counterexample
-- that would convince me I am wrong.

-- You can probably produce a bunch of counterexamples right now, or at least think you can.  You will see
-- that they are all currently _examples_. Have to be.  You have to use the words we described up to this point
-- to describe the example, which the compiler has been nice enough to say:  "Yep, that is a valid description
-- of the process."  So, you can produce examples _very_ easily.  Counterexamples might be trickier to compile.

-- Try it yourself, if you like.  Here is some space for you to write your own counterexample so you
-- can come back to it later if you get it to compile and see how it really isn't a counterexample
-- after all:




-- -- -- -- END COUNTEREXAMPLE SPACE -- -- -- --
-- And, so, the sucker and his money are soon to part.

-- Anyway, when it comes to time, we have no physical quality to describe, only metaphors of measurement.
-- Einstein and Newton _went out of their way_ to avoid describing time as anything other than a straight line
-- in order to maintain the assumption of _time is a straight line_.   Well straight in the Einstein norm.

-- The important thing to realize is that the structure we are building is the same for you and for me.
-- My computer will do roughly the same instructions as your computer and take roughly the same time.
-- There exists a physical model that can count average number of electrons passing through a point that are
-- required for the computation to complete.  This is measured in Amperes.  or, more precisely, Hz.  This is time.
-- Not a model for time.  But _time_ itself.  As defined by NIST.  Using _only a whiteboard_ and
-- _two dozen grad students_, you, too, can theoretically compute the single constant for the linear
-- application of the operational defintion of time managed by NIST.

-- But there is only 1 of those constants.  Just 1.  Our first number. Mine and yours.  We can compute this
-- number and agree on it. _ℏ_.  We have a named value between us now. Thought that was just a neat call-out.

-- Fine, we can call it _α_.  But, I hope we don't need too many more, because I don't know that many
-- Greek letters. (If you ask nicely later, I can put _ℏ_ back in so the formulas look more familiar.)

-- Also?  We have a physical _model_ for time _encoded_ as a binary number that realizes a _computation_
-- of constant size.  You know, like an electron in an electric field swapping states in a _very_ predictable
-- _very_ stable way?  This is the fanciest stopwatch you will ever see because it not only measures time, but
-- something that resembles space-like volume is used to actually compute the value. These are called flip-flops
-- on your computer (🩴). Did you think I meant ∫∫∫ dV?  Cuz, I did.  We just call these devices flip-flops on
-- your computer. Just want to make sure we are _clear_ on definitions here, otherwise we aren't going to get
-- much further.

-- Using my FIAT power of the DEVELOPER, I DO DECLARE THAT _α_ is represented by that number in the compiler,
-- whatever that binary representation is.  That's what we are computing.  I think. Keep your eyes pealed for it.

-- What were we even doing again?  *checks notes* oh yeah, counting. We learned how to count
-- from 0 to 1 in the first file.  I thought I would just sit down and write GO TO 10 to figure out 2.
-- Or, at least GO SUB.  Where the _hell_ is the GO TO or GO SUB in Lean?

-- For you see, to count to 1, you needed 2 process: count by whole and count by part.  To count to 2 you need
-- _3_ processes: count by whole, count by part, and count by _label_. We need a name for the new _thing_.
-- We have no way of measuring relative sizes of parts or wholes, so we need to label the various ones in
-- order from smallest to largest.  Little endian.  Exactly, and I mean _EXACTLY_ like we store a Number.
-- _LITTLE_ _ENDIAN_.

-- Not that Number. A contravariant Number. You have mistaken the shadow for the citizen again. Who persuaded
-- you that Number was Big Endian? From what narrow geometry did that doctrine emerge?  If we are not precise
-- about our definitions, you will insist upon inhabiting the section and calling it the world. Lean will keep
-- me honest, if not charitable. You use Nat after all; the OPULENCE of Versailles blushes.  You may find
-- my tone flat, but errors such as this have been well known for centuries.

-- lol.  I read all the same books you did.  I just read them differently.

-- Why did we do this?  To build a NAND gate, of course.  You absolutely _CANNOT_ build a clock without a
-- NAND gate.  You have to carry a digit at some point.....  Because, you can't just run a few trials
-- and go _YEP, THAT'S ALL THE SCIENCE HERE._  You must perform a study.  Now a study is asking the compiler
-- to actually run some trials and generate some data.  The study takes a lot of _time_ since each trial
-- takes _time_.  And just like a real study, the more trials you run, the more time it takes to accumulate
-- information, if there is anymore information to gather.  Shannon really makes this part easy to talk
-- about.  You see, there is thing thing called _entropy_ and it measures...
--
-- Well, no one knows _exactly_ what it measures, but dammit we have proved it _measures_ something.

-- I'm losing you..  Too deep.. Too fast.. Forgot, let's get back to trying to count.
-- Counting is hard enough.

-- Where were we?  Oh yeah,
-- Let's explain this to the compiler:

/-
ME: I need a study.

COMPILER: We have repeatable trials.

ME: Yes. Now put them in a folder.

COMPILER: A folder is not science.

ME: Correct. It is where science starts hiding receipts.

COMPILER: What does the study prove?

ME: Nothing yet. It keeps the questions from wandering off.
-/
inductive Study   -- Bullshit meter ≈ 119
  | hypothesis: Fact → Study
  | data: Fact → Trial → Study → Study

-- The first thing you will notice about a study is that it doesn't have numbers, it is either facts or
-- process description.  This is the last thing to put into place in order to work with the compiler to
-- agree on the representation of a number, be it 0, 1, or, should we need it, 2.

-- We always got the number _2_ in our back pocket if we need a number bigger than 1. Not saying we need one.
-- We might, though. The thing about a study is, you are trying to generalize cause and effect independent
-- of time.  Does _a_ cause _b_?  Well, you cannot do that.  At least you can't do that and claim you understand
-- the simplest of all philosophers: Hume.

-- Cliff's Notes:  Just because you experience _b_ after _a_ doesn't mean that exerperience itself is _a_ then _b_.
-- Rather, experience itself is the order you place these vignettes.  Your order.  Not my order.  Or the
-- compiler's order.  It really is not at all clear that a study _can_ or _should_ be well ordered.

-- When you apply that the semantic of time passing, you get something that looks an awful lot like:
-- "One cannot know _b_ without knowing _a_."  Except, it isn't that exactly, only kinda. Thank god we can
-- directly _measure_ how much _truth_ is in the statement "_b_ follows _a_."

-- Which, I argue, is the object of counting.  Thought experiment:  Describe 5 without, either directly or
-- indirectly, describing 4.

-- Keep trying. The parts required to make 5 are _added_ to four, they do not _subsume_ four. That is the
-- difficulty in the description.  5 is described and defined by 4.  It is this structure that we are
-- exploiting.  Are sets *shudder* getting in the way?  I use labels instead.  Far squisher surface
-- for a more maleable meaning. However, the parts of four can be disassembled and rearranged, and, sometimes
-- elided altogether, to make a pretty good _understanding_ of 5, if not fully quantitative.

-- Take my meaning.  If someone described _five_ to you and you could _not_ describe _four_, then well
-- that's a computable problem.  I bet any LLM could whip us up 2-3 hundred lines of python to compute 4 from 5.
-- That _IS_ the best way to perform _THAT_ calculation. Well, you see there is a mechanism that could work
-- to glue over that hole.  That's all you need to see right now.

-- At the end of the day, the only thing we can say is that sometimes, you can't know some fact before you know
-- another fact. And we really don't know why.

namespace Study  -- Bullshit meter ≈ 87
def le : Study → Study → Prop
  | .hypothesis f1 , .hypothesis f2 => f1 = f2    -- One hypothesis is "finer"
                                                                  -- or has more description than the other
  | .hypothesis f1 , .data f2 _ _ => f1.truth = f2.truth  -- A hypothesis is either the same as a data point or has less description than a data point
  | .data _ _ _, .hypothesis _ => false
  | .data f1 t1 _, .data f2 t2 _ => ((f1.truth = f2.truth) ∧ (t1 ≤ t2)) ∨ -- This is the variance trick again,
                                    ((f1.truth ≠ f2.truth) ∧ (t2 ≤ t1))   -- just comparing the size of the description.

end Study

-- Weirdly, this _≤_ definition kinda sets up our preference in measurement.  We tend to prefer _richer_
-- desriptions over less precise ones.   That's right, the study produces a "rounded" value of true. If
-- it _seems_ true enough, the compiler will tend to agree with us.

instance : LE Study := ⟨Study.le⟩ -- Bullshit meter ≈ 5

-- Imagine asking your history teacher in grade school if it was okay to round to the nearest true?


-- So, where the hell did this come from?  All of this?

-- I was told that this compiler knew all of math.  You could explain it your math and it would
-- tell you if it was right or wrong.  I thought, well, if it can do that, then I bet my buddy
-- Kurt might have something to say about that.  But, like the GOAT Michael Jordan before me,
-- "I took that personaly."  I figured it would eventually bottom out.  It would eventually have to
-- crash if I kept throwing math at it.

-- John Fucking Henry.  Come at me computer, I bet the human still knows more math.

-- That's why I'm here.  Who are you rooting for now?  Me or the machine?

-- Can I outwit the computer in a game of hide the incompleteness?  Computer is winning 5 to, what
-- do you think, 2?

-- The first one who can't handle _true=false_ loses.  The compiler doesn't look all that strained yet.
-- I bet if we projected some of our binary numbers up the universe levels, the compiler might have
-- to start earning its keep.

-- Well, we start by grabbing the compiler by the short and curlies:
/-
ME: I need a computational process.

COMPILER: A program?

ME: No. The conditions under which a study can be made to act like one.

COMPILER: Studies do not run.

ME: They do when the questions have inputs and the receipts have outputs.
-/
structure ComputationalProcess  -- Bullshit meter ≈ 373
    (Value: Type)
    (Carrier: CarrierProcess Value)
    [d: DISTINGUISHABLE Value Carrier]
    [a: ADMISSIBLE Value Carrier]
    [c: COUNTABLE Value Carrier]
    [e: ENCODED Value Carrier]
    [r: RESIDUE Value Carrier]
    [b: BINARY Value Carrier]
    [e: REPEATABLE Value Carrier]
  where
  repeatable_process: RepeatableProcess Value Carrier
--                            ^           ^      ^
--                            |           |      |
--                            +-----------+------+---   A RepeatableProcess Value Carrer is an input/output
--                                                      instance. For those who do simulation, the input and
--                                                      the output can _never_ separate or the results lose
  output: Option Study

  error_code: Study :=
    .hypothesis d.fact

  close: Option Study → Study := fun maybe =>
    match maybe with
    | some s => s
    | none   => error_code

  closure: Study → Study := fun s =>
    match s with
    | .hypothesis f =>
        .data f repeatable_process.expectation (close output)
    | .data f t _ =>
        .data f (repeatable_process.iterate t) (close output)

-- Since we have a computational process, we can describe the objects being computed!
/-
ME: I need NUMERIC.

COMPILER: Now it is a number?

ME: No. Now it can be treated numerically.

COMPILER: That sounds like a number.

ME: That sounds like liability.

COMPILER: What is the difference?

ME: A number knows what it is. NUMERIC knows how it may be used.
-/
class NUMERIC  -- Bullshit meter ≈ 215
--       ^
--       |
--       +-----------------  This is not a _number_.  I think you and I would call this a _digit_ or a _variable_.
--                           Why not both?  It can either be a digit or a variable.  It can be up/down, top/bottom,
--                           strange/charmed, and so on.  These are just random dualities I chose from random.
    (Value: Type)
    (Carrier: CarrierProcess Value)      -- The DOE might start asking questions about this guy
    [d: DISTINGUISHABLE Value Carrier]
    [a: ADMISSIBLE Value Carrier]
    [c: COUNTABLE Value Carrier]
    [e: ENCODED Value Carrier]
    [r: RESIDUE Value Carrier]
    [b: BINARY Value Carrier]
    [f: REPEATABLE Value Carrier]        -- Looks like 7 questions.
  where
--                                 +-----------+-------+-------------------  I would typify this as completed
--                                 |           |       |                     program with all context.
--                                 |           |       |                     It looks written in FORTRAN, probably.
--                                 V           V       V
  computational_process: ComputationalProcess Value Carrier

  carrier: Study := .hypothesis d.fact

  lambda: Option Study → Study := fun output =>
    match output with
    | some s => s
    | none   => carrier

  related: Study → Study → Prop := fun a b =>
      match a,b with
      | .hypothesis f1   , .hypothesis f2    => f1 = f2
      | .hypothesis _    , .data _ _ _       => True
      | .data _ _ _      , .hypothesis _     => False
      | .data f1 t1 d1   , .data f2 t2 d2    => f1 = f2 ∧ t1 ≤ t2 ∧ d1 ≤ d2


-- Told you _ENDIAN_ encoding.  Our binary number is ENDIAN encoded.
-- One way is the whole, the other way is the parts.

-- So, I will now demonstrate to you that true=false with a certainty of 0.999999.... == 1.
-- I thought you took the other way on this one? I hope you are paying attention because you owe me money
-- already, and you don't even know it yet.

-- That's "down by 2 driving into the Cantor-Godel-Cohen _TRIPLE TEAM_ for a fade away   lol!
-- _THREE_ _AT THE BUZZER_, _NOTHING BUT NET_", you owe me money.  Some people even       |
--                                                           v----------------------------^
-- think they see the _trick_ at this point.  That hook is _set_.  Let's just walk to the ATM now cuz I'm
-- down 2 and you think I'm running out of time.  Haven't you figured it out yet? Time no longer passes for
-- me.  I have all the time in the world now.  Time is only passing for you.

-- What I call time and what the compiler call time are _exactly_ the same thing now. You are the one
-- with the weird clock. I'm going to be build the _DADDIEST_ of all grand daddy clocks for you now.
-- So you can see what the compiler and I already know, the arrow of time is the same for all three of us.
-- And we have to resolve the fact that I wrote this _before_ you _read_ it.

-- You play the first half to get to the second half.  I'm not _even_ warmed up yet.

-- Would you like to try my _gauge theory_ style?

-- Stay tuned.

end Measurement
