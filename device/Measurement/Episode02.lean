/-
__Measurement: The Tragedy of John Henry__
__A Satire in Look Ahead Backus-Naur Form__

_This is a gentle reminder that the convoluted stories we tell ourselves are just that: convoluted._

(c) 2026 All rights reserved -- obligations, however, are freely distributable.

__EPISODE 2__: _Time_

"Yo dawg! I heard you like to prove theorems, so I put a theorem prover in your theorem prover so you can prove theorems about proving theorems
while you prove theorems about proving theorems."
                                  -- Kenny Rogers.  Really confident XZibit covered it. j/k, i got no beef with X to the Z.

lake build --no_assumptions --splash_damage=on

__LIVE__
_without a net_, its.......
-/

-- The story so far.....
import Measurement.Episode01

-- This is not a safety net. More like a trawling net.
set_option allowUnsafeReducibility true

namespace Measurement

universe i --+ *i*.  I think I will call this time. Not just any kind of time. But a kind of time that is imaginary. Compiler time. The universe
           --| at time step *i*. That way, when we write the diffusion equation for the compiler, Schroedinger's equation falls out.
           --| Did you count all four?

-- What were we even doing again?  *checks notes* Oh yeah, counting. We learned how to count from 0 to 1 in the first file.  I thought I would just
-- sit down and write GO TO 10 to figure out 2. Or, at least GO SUB.  Where the _hell_ is the GO TO or GO SUB in Lean? It is about to get _LONG_
-- and __UNNECESSARILY__ drawn out. Just the way *YOU the KNOWER* like it. I'm not the one that demands tens of thousands of lines of explanation
-- for a simple constant called _α_.

-- For you see, to count to 1, you needed 2 process: count by whole and count by part.  To count to 2 you need _3_ processes: count by whole, count
-- by part, and count by _label_. We need a name for the new _thing_. We have no way of measuring relative sizes of parts or wholes, so we need to
-- label the various ones in order from smallest to largest.  Little endian.  Exactly, and I mean _EXACTLY_ like we store a Number. _LITTLE_ _ENDIAN_.

-- Not that Number. A contravariant Number. You have mistaken the shadow for the citizen again. Who persuaded you that Number was Big Endian? From
-- what narrow geometry did that doctrine emerge?  If we are not precise about our definitions, you will insist upon inhabiting the section and
-- calling it the world. Lean will keep me honest, if not charitable. You use Nat after all; the OPULENCE of Versailles blushes.  You may find
-- my tone flat, but errors such as this have been well known for centuries.

-- lol.  I read all the same books *YOU the KNOWER* did.  I just read them differently.

-- Why did we do this?  To build a NAND gate, of course.  You absolutely _CANNOT_ build a clock without a NAND gate.  You have to carry a digit at
-- some point.....  Because, you can't just run a few trials and go _YEP, THAT'S ALL THE SCIENCE HERE._  You must perform a study.  Now a study is
-- asking the compiler to actually run some trials and generate some data.  The study takes a lot of _time_ since each trialtakes _time_.  And just
-- like a real study, the more trials you run, the more time it takes to accumulate information, if there is any more information to gather.
-- Shannon really makes this part easy to talk about. You see, there is thing thing called _entropy_ and it measures...

-- Well, no one knows _exactly_ what it measures, but dammit we have proved it _measures_ something.

-- I'm losing you..  Too deep.. Too fast.. Forgot, let's get back to trying to count. Counting is hard enough. You might accidentally count yourself
-- into the model of an atomic bomb. Actually, it won't be accidental. This is on purpose.

-- Where were we?  Oh yeah, do you drink beer?

/- CHORUS:
ME: I need a study.                                         | Did you know one of the most amazing discoveries came from the Guiness brewery? A tool
COMPILER: We have repeatable trials.                        | for understanding data. The __Book of World Records__. Unbelievable leap in civilation.
ME: Yes. Now put them in a folder.                          | You see, bar bets have always been a thing. Is this the most? Is this the biggest? How
COMPILER: A folder is not science.                          | many were there? Very quantitative discussion for those of the tipple.
ME: Correct. It is where science starts hiding receipts.    |
COMPILER: What does the study prove?                        | Well, they got tired of listening to the arguments about what was more and what was
ME: Nothing yet. It keeps the questions from wandering off. | bigger, and whose was most. So they wrote the book. The book that answered all the
-/ --                                                       | questions.  What was most, what was smallest.
inductive Study   -- Bullshit meter ≈ 119                   |
  | hypothesis: Fact → Study  ------------------------------+ Dunno why we need to go much farther, since they answered all the questions.

  | a_few_pints: Fact → Trial → Study → Study --------------+ But *YOU the KNOWER* may object at this point. Your correction objection being: This is
--                                                          | not the greatest discovery to come from Guiness. And, you'd be right. One taste, and
--                                                          | you too, would have a couple of pints.

-- The first thing you will notice about a study is that it doesn't have numbers, it is either facts or process description.  This is the last
-- thing to put into place in order to work with the compiler to agree on the representation of a number, be it 0, 1, or, should we need it, 2.

-- We always got the number _2_ in our back pocket if we need a number bigger than 1. Not saying we need one. We might, though. The thing about a
-- study is, you are trying to generalize cause and effect independent across _time_.  Does _a_ cause _b_?  Well, you cannot do that.  At least you
-- can't do that and claim you understand the simplest of all philosophers: Hume. Cliff's Notes:  Just because you experience _b_ after _a_ doesn't
-- mean that exerperience itself is _a_ then _b_. Rather, experience itself is the order you place these vignettes.  Your order.  Not my order.
-- Or the compiler's order.  It really is not at all clear that a study _can_ or _should_ be well ordered. TBH, I'm not all that well ordered after
-- a few pints, myself.

-- When you apply the semantic of time passing, you get something that looks an awful lot like: "One cannot know _b_ without knowing _a_."  Except,
-- it isn't that exactly, only kinda. Thank god we can directly _measure_ how much _truth_ is in the statement "_b_ follows _a_." Which, I argue, is
-- the object of any counting worthy to found the Naturals on.  Thought experiment:  Describe 5 without, either directly or indirectly, describing 4.

-- The compiler only knows recursion. The counting we have described does not admit a non-recursive definition of counting. It must be constructed
-- in order with _b_ NECESSARILY coming after _a_ in such an _OBVIOUS_ fashion to everyone. Except the compiler. I don't think it can properly order
-- things by semantics alone, it needs elaborative effort that takes time. __FRICKIN DAYS__ on my 2023 Mac Studio. About 2 full days to compile this
-- argument. Boy, did I feel the time debugging this monstrosity.  Much more time than it will take you to understand this. Which is much more time
-- than it takes to read it. Which is much more time than it takes for me to convince you that this device is _NOT_ computing a particular number
-- *YOU the KNOWER* _KNOW_ in your heart cannot be computed from scratch.

-- Keep trying. The parts required to make 5 are _added_ to four, they do not _subsume_ four. That is the difficulty in the description.  5 is
-- described and defined by 4.  It is this structure that we are exploiting.  Are sets *shudder* getting in the way?  I use labels instead.  Far
-- squisher surface for a more maleable meaning. However, the parts of four can be disassembled and rearranged, and, sometimes elided altogether, to
-- make a _directional understanding_ of 4, if not fully quantitative. As in time passes in _this direction_ not _that direction_. If time passed in
-- _that direction_, these are the things that would need to change in the compiler. These facts become those Facts.

-- Take my meaning. If someone described *five* to you and you could *not* describe *four*, then, well, that's a computable problem. I bet any LLM
-- could whip us up 2-3 hundred lines of Python to compute 4 from 5. That *IS* the best way to perform *THAT* calculation. Well, you see, there is
-- a mechanism that could work to glue over that hole. That's all you need to see right now. At the end of the day, the only thing we can say is
-- that sometimes you can't know some fact before you know another fact. And we really don't know why. The compiler also understands that it doesn't
-- know why; it only knows how. This is a Truth we, all four of us, share in common. The compiler knows something I don't though. How.

-- We must study the device we are building.                | Two hypotheses can differ in coarseness. I bet the temperature will be 75ᵒ next week
namespace Study  -- Bullshit meter ≈ 87                     | is much different than the temperature will be 23.88888888ᵒ next week, aren't they?
def le : Study → Study → Prop --                            |
  | .hypothesis f1 , .hypothesis f2 => f1 = f2    ----------+ I mean, they just gotta be different... One is like rounded to the nearest 5.

  | .hypothesis f1 , .a_few_pints f2 _ _ => f1.truth = f2.truth  -------+ Having an idea and then having a _drink_ and thinking about the same idea is
                                                                      --| fine.

  | .a_few_pints _ _ _, .hypothesis _ => false  -----------+ But people have really BAD ideas when they get drunk.

  | .a_few_pints f1 t1 _, .a_few_pints f2 t2 _ => ((f1.truth = f2.truth) ∧ (t1 ≤ t2)) ∨  ----+ And, no matter how drunk you get, you simply cannot
                                                  ((f1.truth ≠ f2.truth) ∧ (t2 ≤ t1))--      | undrink a beer.

end Study

-- Weirdly, this _≤_ definition kinda sets up our preference in measurement.  We tend to prefer _richer_ desriptions over less precise ones.   That's
-- right, the study produces a "rounded" value of true. If it _seems_ true enough, the compiler will tend to agree with us.  Now, I think
-- *YOU the READER* understands *YOU the KNOWER*'s motivations just a little bit better. There has to be a difference they aren't seeing. More
-- cowbell is the cure.
instance : LE Study := ⟨Study.le⟩ -- Bullshit meter ≈ 5

-- You okay, *YOU the KNOWER*? I hope that wasn't too far-fetched for you. If I leave you too far behind, you might not finish this astonishing
-- journey, and I want you to see it. Besides, *YOU the READER* needs a little distance between these vignettes. To see many things, you must
-- be at a great distance, for that is the definition of distance: many things between *x* and *y*.

-- For instance, imagine asking your history teacher in grade school if it was okay to round to the nearest true? We round to the nearest digit
-- without thinking about it, sometimes correctly. But truth was never approached as a direction when discussing facts. What if I can determine
-- that an argument has _OBVIOUS_ directionality.  The mechansim for _b_ to precede _a_ is _FAR TOO COMPLEX_ for a mechanism to even be fathomed,
-- let alone exist? When the time comes, you will understand how much effort it takes for _YOU the KNOWER_ to become _YOU the READER_. I will
-- measure it for you. The point is, this is a process that will take _time_.

-- Let me _humbly_ thank you for your effort in reading this. If I did not think the walk worthwhile, I certainly would not have done this.

-- So, where the hell did this come from?  All of this?

-- I was told that this compiler knew all of math.  You could explain it your math and it would tell you if it was right or wrong.  I thought, well,
-- if it can do that, then I bet my buddy Kurt might have something to say about that.  But, like the GOAT Michael Jordan before me, "I took that
-- personaly."  I figured it would eventually bottom out.  It would eventually have to crash if I kept throwing math at it.

-- John Fucking Henry.  Come at me computer, I bet the human still knows more math. I am about to show *YOU the READER* how to out-math LEAN.
-- That's why I'm here. Who are you rooting for now?  Me or the machine? How wrong do you want this to obviously be? Think I can wrestle this bear to
-- the ground? Can I outwit the computer in a game of hide the incompleteness?  Computer is winning 5 to, what do you think, 2?

-- The first one who can't handle _true=false_ loses.  The compiler doesn't look all that strained yet. I bet if we projected some of our binary
-- numbers up the universe levels, the compiler might have to start earning its keep. The compiler knows how to count. It knows how to count real
-- nice for us. Barely have to ask.

-- Well, we start by grabbing the compiler by the short and curlies:
/-                                                                             | The first assumption of Turing was that you can represent things
ME: I need a computational process.                                            | accurately enough to identify the answer to the problem you asked.
COMPILER: A program?                                                           | This has a pseudo-inverse (demonstrated as Fact, not proved as
ME: No. The conditions under which a study can be made to act like one.        | theorem, and _VERY_ rigorously so).
COMPILER: Studies do not run.     ---------------------------------------------+
ME: They do when the questions have inputs and the receipts have outputs.      | Turing's diagonal argument follows from this unnamed axiom.
-/
structure ComputationalProcess  -- Bullshit meter ≈ 373
    (Value: Type i)
    (Carrier: CarrierProcess Value) --                     | The tick of a clock. *YOU the KNOWER* understand this to be a resonance of some kind.
    [this: DISTINGUISHABLE Value Carrier] --               | An atom is stimulated in such a way that it gives off so many discrete signals in a
    [ADMISSIBLE Value Carrier] --                          | second, we can tell the difference in length between them. Then, I think they took a
    [COUNTABLE Value Carrier] --                           | magic bar and a laser and performed special incantation of mathemagic to arrive at an
    [ENCODED Value Carrier] --                             | integer number. A very large integer number. A very _ARBITRAY_ integer number, other
    [RESIDUE Value Carrier] --                             | than we want it to be _AS LARGE AS POSSIBLE_.
    [BINARY Value Carrier] --                              |
    [REPEATABLE Value Carrier] ----------------------------+ Feel like that book has been written. Should probably keep a copy.
  where
  repeatable_process: RepeatableProcess Value Carrier
--                            ^           ^      ^
--                            |           |      |
--                            +-----------+------+----+ A RepeatableProcess Value Carrer is an input/output instance. For those who do simulation,
--                                                    | the input and the output can _never_ separate or the results loose all meaning.

  output: Option Study --+ Even better, since this requires work and, like i said, compilers are frickin' lazy. We have the _OPTION_ to make the
--                       | compiler work.

  error_code: Study := -----------------------------------------------------------------------+ __PLEASE DEAR GOD READ THIS DISCLAIMER!__
    .hypothesis this.fact --                                                                  | __THIS CODE MAVE HAVE SERIOUS BUGS AS THIS.FACT!!!__
--                                                                                            | __DO NOT TAKE THIS CODE AS PROOF OF ANYTHING__
  close: Option Study → Study := fun maybe => -------+ True story, not all code compiles.     | __MEANINGFUL__. We put all our bugs here.
    match maybe with --                              | If the compiler cannot satisfy our     | I mean, anytime facts were "controlled" for "bias".
    | some s => s --                                 | query, then we get an error condition  | It goes here. Just like a Nature publication. And
    | none   => error_code --                                                                 | then we pretend like they don't matter.

  closure: Study → Study := fun s => -------+ Closing time, one last call for alcohol!
    match s with --                         | DRINK UP!
    | .hypothesis f =>
        .a_few_pints f repeatable_process.expectation (close output) ------+ Now or never, can't wait for ever. 2am shuts down the taps. Remember
    | .a_few_pints f t _ => --                                             | this is a lesson about time and showing the compiler. At some point in
        .a_few_pints f (repeatable_process.iterate t) (close output) --    | time, the fact _f_ will no longer matter because the output is closed.

-- Since we have a computational process, we can describe the objects being computed! In other words, I can show *YOU the READER* _how_ we can
-- recover _how_ the compiler knows _how_ all of this needs to be arranged to be a consistent argument.
/-
ME: I need numerics.
COMPILER: We have Nat and Rat and ... you don't mean that.                             | Programming languages tend to pride themselves on hiding
ME: Actually, this time I do, I don't need the name, I just need a place to put it.    | from the developer which bit in the computer actually
COMPILER: Put which, a Nat or a Rat?                                                   | represents which piece of data being presented. Security
ME: The box they come in.                                                              | risks associated with self-reference have more than
-/  --                                                                                 | justified the need for such abstraction.
class NUMERIC  -- Bullshit meter ≈ 215  -----------------------------------------------+
--                                                                                     | All I want is just some raw space on a register.
    (Value: Type i) --
    (Carrier: CarrierProcess Value) -------------+ Let's take a second and examine this carrier. This carrier is constructed at the current
    [this: DISTINGUISHABLE Value Carrier] --     | universe level. This class is guaranteed to carry the latest structure, implying that this
    [ADMISSIBLE Value Carrier] --                | class must live at a universe level higher than the process inside it. Since all these classes
    [COUNTABLE Value Carrier] --                 | must remain constructible beneath the giant overlay of templated, Fibonacci-style constructors,
    [ENCODED Value Carrier] --                   | there must exist a permutation of Facts that permits explicit construction of relations capable
    [RESIDUE Value Carrier] --                   | of arbitrarily ordering the permutations. Then it is merely a mapping that must be constructed.
    [BINARY Value Carrier] --                    | The only way to construct that mapping is to ask the compiler a bunch of questions, over and over,
    [REPEATABLE Value Carrier] --                | creating the pseudo-inverse one bit at a time. In a repeatable fashion.
  where
  -- I feel as though I am twisting Lean into more of a COBOL style syntax. More Knuthian than anything I would ever care to admit to myself.
  computational_process: ComputationalProcess Value Carrier

  carrier: Study := .hypothesis this.fact -- The box it came in.

  -- The reason why this looks exactly like the previous is because it is doing the same thing, just different. It's like watching a pro athlete.
  -- They operate on a whole other level. This _time_ it is a bit different, replacing with the carrier as it fails to parse, the compiler doesn't
  -- understand the bit at all and we will take it as one that _we_ set.  *YOU the READER*, we get to write a computer program soon for our
  -- compiling engine.

  lambda: Option Study → Study := fun output => --                                     | This is going to take a minute or two to unpack.  I _just_
    match output with -----------------------------------------------------------------+ claimed that the compiler does not understand the bit in
    | some s => s --                                                                   | front of it so we keep it as our own bit. The one we set
    | none   => carrier --                                                             | where we don't know why this works. This is _THAT_ bit.
--                                                                                     | In the _GOD DAMN_ flesh. This is the first _bit_ that we
  related: Study → Study → Prop := fun a b => --                                       | are allowing the compiler to just _accept_ as a
      match a,b with --                                                                | hypothesis. The options to the question in front of the
      | .hypothesis f1        , .hypothesis f2        => f1 = f2 --                    | compiler are simple:
      | .hypothesis _         , .a_few_pints _ _ _    => True  --                      | (1) Because: there is a constructive reason for it
      | .a_few_pints _ _ _    , .hypothesis _         => False --                      | (2) Why not: cannot find a reason why a construciton
      | .a_few_pints f1 t1 d1 , .a_few_pints f2 t2 d2 => f1 = f2 ∧ t1 ≤ t2 ∧ d1 ≤ d2 --+     should not exist as we _DEFINITELY_ have a carrier
--                                                                                     |     process generated by the compiler.
--                                                                                     | This is our constructed inside joke, *YOU the READER*.

-- What does this have to do with _time_? Muxing and decoding. These are standard electro-mechanical computations that are a completely PHYSICAL
-- process that underlies the lambda described above. The computer this runs on, it shunts electrons around in defined ways, counting them like
-- _this_ or like _that_, almost completely orthogonal to the processes they support. Time sharing is a good example of muxing and decoding.
-- The important thing is that the compiler does not just _typecheck_ the code, it makes sure we do not construct anything _inconsistent_.

-- And that's really all I need it to do. To consistently and repeatable perform the same computation over and over again based upon a single
-- description, verifying all objects are consistently constructed. For this is _the_ ultimate constructive proof. We are about to constuctively
-- prove the existence of constructive proofs. And the time it takes to prove this, we will demonstrate, is directly proportional to how complicated
-- it is. Then, we just insist on choosing the cheapest among identical proofs.

-- Step one, we need to sort all proofs by expense. We turn to Marconi for help. So Marconi said:  Hey we can use the photon to communicate using
-- a "presence"/"absence" duality defined by a _threshold_ of detection.  So, if a sample is above the threshold of detection, it sure as hell
-- should be detectable. Then modulation and demodulation arrived and we could send voice over amplitude modulated photons. Think about that.  The
-- photon has 2 real numbers that describe it.  Amplitude and frequency. We explicitly modeled our carrier as such (even though the same model
-- supports the interpretation of time in the compiler).  It is, in fact, two numbers.  Not that we know the numbers, we have to _study_ them to
-- understand what they are.

/-                                                                  | These sorts of time paradoxes have plagued computer science, leading to
ME: I need a computation, now.                                      | the idea of *amortized* cost: the cost to *re-encode* the state to make it
COMPILER: The process takes time to complete.                       | more efficient. If you are *clever*, says the Computer Scientist, you can
ME: Processes are engines. Turing said engines are numbers.         | update your structure in O(small number) on each step, or O(huge number) once
COMPILER: Input, output, route? Those are numbers.                  | every countable number of steps, which is O(small number) on the continuum.
ME: And the fantasy is that the number is O(1) to write down. ------+ I did not do well in algorithms at all.
-/
inductive Computation    -- Bullshit meter ≈ 134             | Believe it or not, this is a complete description of the compilation process. It is a
  | program: Fact → Study → Computation   -------------------+ fact, indeed, that a study generates a computation of some sort.

  | compute: Fact → Study → Study →   -------------------+ Input, output, route. Just like the compiler promised. This is the _make_ process. One
                Computation → Computation --             | computation depends on the computation of a predecessor. Input can now be transformed
--                                                       | directly into the final compiled form for a multi-pass compilation procedure.

-- Lean claims to understand these concepts, so it should be _no problem_ to model the Lean computation itself this way. Computations should sort in
-- a pretty straightforward way.

namespace Computation   -- Bullshit meter ≈ 80
def le : Computation → Computation → Prop
  | program _ s1, program _ s2 => s1 ≤ s2         -- Programs are indexable.  Turing's construction assumed that this is possible.

                             --          +-----------------+ I could have hidden the trick from you here and kept you guessing. If I haven't
                             --          |                 | convinced *YOU the READER* I can make the comments say whatever I want them to,
                             --          |                 | you must certainly understand that I can make the code say anything I want it to
                             --          |                 | and the fact you can see the quarter on the table i glued down is a testament to that.
                             --          V
  | program _ _, compute _ _ _ _ => (true=true)          -- Computation is convariant with program.  Comes after
  | compute _ _ _ _, program _ _ => (true=false)         -- Decomposition is contravariant.  Reverse engineering is _hard_.
                             --          ^
                             --          |                 | My ante. The comments. _INFOMRATIONAL STRAIN_. Fair is fair, this is the quarter
                             --          +-----------------+ *YOU the KNOWER* stand to win by failing to see the consistency of the argument.

  | compute _ _ _ c1, compute _ _ _ c2 => le c1 c2    ----- Recurse! Eventually, we will find a computation that has completed.

-- Computations are, in fact, well ordered. Assume they were not. Then it would take longer to prove _a_ than _b_ while simultaneously taking
-- longer to prove *b* than *a*. I'd like to see that. What I can see, though, is that there *EXISTS* a device that computes in the neighborhood
-- of the uncanniest value known to experimental science for no real reason at all.
def lt: Computation → Computation → Prop
  | c1, c2 => le c1 c2 ∧ ¬ le c2 c1
end Computation

-- This is starting to look more and more like ≤ and <, isn't it?
instance : LE Computation := ⟨Computation.le⟩   -- Bullshit meter ≈ 8
instance : LT Computation := ⟨Computation.lt⟩   -- Bullshit meter ≈ 8
-- The fact that we get _two_ different representations of the _same_ ordering relation is a _SUPER_ huge convenience
-- and it will _NEVER_ get confusing.

/-                                                                     | At this point, *YOU the READER* should understand the pattern that is
ME: I need a Turing process.                                           | being setup. I am describing process by its inability to perform a
COMPILER: I can process symbols.                                       | particularly simple computation and letting the compiler hold a pointer
ME: Not the comments.                                                  | to something that will solve the problem: a CarrierProcess. We should
COMPILER: Comments are not symbols.                                    | think about why a TuringProcess might help understand how we can measure
ME: Correct. They should be not be evaluated as true or false.         | anything. The short answer is the Hall Effect Sensor.  A device that turns
COMPILER: I cannot read them.                                          | around in a integer number of turns. An integer description of a complete
ME: Exactly. That is why you cannot comment on them.                   | rotation. Each sensor, as far as _people_ are concerned, sweeps 2π each
-/ --                                                                  | turn. If the sensor trips the threshold 6 times, then each threshold
structure TuringProcess   -- Bullshit meter ≈ 492                      | _literally_ __COUNTS__ by π/3.
    (Value: Type i) --                                                 |
    (Carrier: CarrierProcess Value) --                                 | And it is trivial to demonstrate that 6-state Hall Effect sensor can encode
    [DISTINGUISHABLE Value Carrier] --                                 | numbers in base 6. Which can be translated through modular arithmetic to
    [ADMISSIBLE Value Carrier] --                                      | base 2 without ever relying on the base _BEING_ exactly six. Just needs to
    [COUNTABLE Value Carrier] --                                       | be a multiple.
    [ENCODED Value Carrier]  --                                        |
    [RESIDUE Value Carrier] --                                         | We didn't solve for 6, we solved for the number of discrete signals a
    [BINARY Value Carrier] --                                          | Hall effect sensor could sense.
    [REPEATABLE Value Carrier] --                                      |
    [NUMERIC Value Carrier] -------------------------------------------+ That computation is the only computation the TuringProcess will perform.
  where
-- The computer science student will tell you that you cannot study Turing machines without studying a very precise sounding version of _time_.
-- This _time_ is fundamentally different from the one of Einstein or Newton. This time varies based on the state of the process.  For Einstein
-- and Newton, they assumed that time advanced in ``equal measures.'' Einstein's treatment of clocks in Special Relativity and further in General
-- is _CLEAR_. He admitted he had no process as such and _ASSUMED_ that whatever process could be measured with photons, no matter the phase of the
-- photon. Turing suggested otherwise.
  computational_process: ComputationalProcess Value Carrier

  program: Study   -----------------+ We really don't care about what the program is, just how long it takes to perform a particular computation.
  state: Computation --             | Cook guarantees we should be able to classify these computations by how long they take to execute into at least
--                                  | _two_ buckets, which is all we really need.

  -- What do you think, did we compute it? The compiler can get real _CAGEY_ about stuff.
  compute?: Computation → Option Study := fun s =>
    match s with
    | Computation.program _ s => some s
    | Computation.compute _ _ s2 _ => computational_process.closure s2
  -- I stuck that landing, wdyt? I mean, is that _NOT_ the definition of an Option? One thing that Turing _DID_ get right, interpretation of the
  -- symbol _IS_ a different step than updating the internal state of the machine.

  turing_step? : Computation → Computation := fun s => --                             +-----------+ The compiler will be nice enough to close
    match s with --                                                                   |           | whatever lambda we give it. That's what it does.
    | Computation.program _ _ => s --                                                 V
    | Computation.compute f s1 s2 _ => Computation.compute f s1 (computational_process.closure s2) state
  -- *NOW* we have fully specified a Turing machine. Lol. *YOU the READER* have already seen where the PDA is. Ask *YOU the KNOWER* how to
  -- Flower-C, Flower-V. I'm on a Mac. Because I am not on Linux. All my drivers work. *NYAH*


-- So, the problem with Turing's construction is that is __PRESUPPOSES__ a __WHOLE__ bunch of symbols that behave mathematically.  As you can see,
-- we are... *two* episodes in and I ain't declared __SHIT__. That means, we have to provide the facility for __REPRESENTATION ITSELF__!  For us, we
-- currently have 1 character we can use for representation.  That is the digit 1.  We will call that our __REPRESENTATION__ The compiler, however,
-- needs a little help selecting a symbol.  When you __WRITE__ programs, you have to explain the symbols __BOTH__ to the compiler and to
-- *YOU the READER*.  *YOU the KNOWER*, have pity on those less fortunate in your knowledge that α is not a computable thing.
/-                                                            | The ontological argument is simultaneously immensely powerful and comically
ME: I need REPRESENTABLE.                                     | ineffective. Simply defining the object to _be_ the object desired, you can walk
COMPILER: I can do that. I am a kind of ventriloquist.        | backwards algebraically through definitions to build the magicians slip knot.
ME: You make symbols speak?                                   | We have taught the compiler to build VERY complex reasoning structures and insisted
COMPILER: I make values speak through symbols. ---------------+ that it reduce _EVERYTHING_ to the algebraic property of reflection (see
ME: Interesting.                                              | BigRedDogProcess in later episodes). To the compiler, _EVERYTHING_ turns out to be
COMPILER: Why are you looking at my hand?                     | checking a list of defintions. That is easy for you to check. The defintions are
ME: No reason. Continue.                                      | in order. That is also easy to check. The defintions compartimenatlize computations
-/ --                                                         | by universe. Again, the ℕatural symbols can be inspected on sight, if you look.
class REPRESENTABLE  --  Bullshit meter ≈ 261
    (Value: Type i)
    (Carrier: CarrierProcess Value)  --        | What is an encoding? What does it mean to be enccoded? Shannon discusses this in some _serious_
    [DISTINGUISHABLE Value Carrier] --         | depth, allowing you compute something called _entropy_ from only an ordered list of values. Any
    [ADMISSIBLE Value Carrier] --              | ordered list of values, like the ones you get from scientific instruments, only, _MORE GENERAL_.
    [COUNTABLE Value Carrier] --               | If you think about it.  Measuring devices _are_ communication devices, aren't they? I mean, let's
    [ENCODED Value Carrier] -------------------+ look at the use of photons to estimate the speed of a car. Compare that to the speed generated by
    [RESIDUE Value Carrier] --                 | the Hall effect sensor at the wheel of the car. What would it take to compare the values of these
    [BINARY Value Carrier] --                  | _wildly_ different methods at estimating speed? A very compreshensive representation that allows
    [REPEATABLE Value Carrier] --              | an expert identified by others to explain that the numbers display are consistent or inconsitent.
    [NUMERIC Value Carrier] --                 | _NOT_ right or wrong.
  where
--                          +-------------------------------------+ Somehow, _so called_ "big O" notation is considered an extremely rigorous
--                          |                                     | description of a bounding process. And, I admit, it can be.. _BUT_ there are not
--                          V                                     | that many so-called software engineers out there that can tell *YOU the READER*
  calculation_process: TuringProcess Value Carrier --             | how. Doesn't matter really, it just matters that you understand we are talking
--                                                                | about how _long_ it takes to finish a process. That is the whole point of these
--                                                                | devices is to compute _time_. Tick-tock.

-- The unfortunate thing about a Turing machine, though, is that it can run _FOREVER_. But, it never takes forever to look at a symbol and
-- understand it. I mean, *YOU the READER*, you will eventually _stop_ reading this. And, as the compile demonstrates, *YOU the READER* will still
-- believe this demonstration is consistent. So, to be representable, we must insist that any program for our Turing machine come with a proof that
-- it terminate. *YOU the KNOWER* should understand this is not a trivial construction. We have to work through the closure and find the study we
-- left there.
  representable?: ∀ (_: Fact) (s: Study), ∃ (_: Computation), calculation_process.computational_process.closure s = s
-- I hope you understand now that this IS NOT GIVEN by mathematics. The symbols come from elsewhere. You see, Lean will tell us how much time it
-- takes to elaborate a block. We can _measure_ how much "time" it takes for the TuringProcess to do its work and tell it to _STOP_ after so
-- many steps.

  loaded: Computation → Computation → Prop := fun a b => ----------------------------+ After a few pints, we can ask the compiler if it has loaded the
        match a,b with --                                                            | program we will be writing later. If so, then the compiler
        | .program f1 s1          , .program f2 s2             => f1=f2 ∧ s1 ≤ s2 -- | agrees that we can use elaborations as a dictionary key.
        | .program _ _            , .compute _ _ _ _           => True --            | I suggest *YOU the READER* _study_ this chart closely.
        | .compute _ _ _ _        , .program _ _               => False
        | .compute f1 s11 s12 c1  , .compute f2 s21 s22 c2     => (f1=f2 ∧ (c1 ≤ c2)) ∨ (f1 ≠ f2 ∧ s11≤s21 ∧ s12 ≤ s22)

-- If only Turing's result could stay in its own lane, but, alas, it cannot. Chaitin _described_ the computation of a number that cannot be computed.
-- Which is _REALLY_ unfortunate for those people who think that a _COMPUTATION_ can be some sort of magical oracle. This is a number that _CANNOT_
-- be computed, the computation only described. __Ω__. That makes it _EASY_, wouldn't want to confuse this with any other such uncomputable constants.
-- that may inadvertantly get generated along the way.

/-                                                                         | The word _ABSOLUTELY_ here is not an exaggeration. The compiler is aware
ME: I need an uncomputable number sequence.                                | that such numbers exist. The Berry Paradox names such a number, for
COMPILER: Absolutely not.  ------------------------------------------------+ instance, famously describes the computation of a value from its
ME: I am not asking you to "compute" it. --                                | description that cannot be performed. These sorts of "proof based"
COMPILER: You named it. --                                                 | existence by ontology are the only sorts of proofs that the compiler
ME: I am asking you to agree this kind of sequence could exist in theory.  | understands, unfortunately. We rigorously demonstrated that a compiler
COMPILER: "In theory" is doing a lot of work.                              | is merely a dictionary reduction algorithm earlier. These proofs we use
ME: Perfect. Give it a hard hat.                                           | to construct numbers exist and the compiler refuses to ceritfy them.
-/
inductive ChaitinsNumberSequence  -- Bullshit meter ≈ 112  ------------------------------------+ The compiler already knows that we can describe
-- The __HEAVY WEIGHT CHAMPION OF THE WORLD__ --                                               | a sequence of computations that must be performed
  | halting: Fact → Computation → ChaitinsNumberSequence --                                    | to compute a number. Chaitin defined a number, a
  | nonhalting: Fact → Computation → Option ChaitinsNumberSequence → ChaitinsNumberSequence -- | probability, actually, that a randomly selected
--                                                                                             | program will halt. This is a huge simplification
--                                                                                             | and margins are a bit more expansive than Fermat's,
--             --------------------------------------------------------------------------------+ but still, they are just margins. Understand that
--             | the number was not postulated to exist, but constructed from well understood principles of the Turing machine, the device we have
--             | constructed above. Suffice to say, you can construct subsequences of __Ω__, but not enough to actually recover more than a few
--             | digits in whatever base you represent this in. A formally describe computation of a number that has been formally demonstrated as
--             | _uncomputable_, for all intents and purposes, give or take a few bits of information.


-- So, can you compare uncomputable numbers? Well, if they halt, that's a cinch. Just compare their "output" [BTW compiliers have _several_ outputs
-- that matter here.  we have covered _TWO_: (1) it takes time to compile, (2) sass. It's that sass we care about when we aren't keeping time.]
namespace ChaitinsNumberSequence  -- Bullshit meter ≈ 91
def le : ChaitinsNumberSequence → ChaitinsNumberSequence → Prop
  | halting _ sass1, halting _ sass2 => sass1 ≤ sass2
  | halting _ _, nonhalting _ _ _ => true
  | nonhalting _ _ _, halting _ _ => false
  | nonhalting _ sass1 _, nonhalting _ sass2 _ => sass1 ≤ sass2

-- Can't compute <.  Against the rules. The thing about Chaitin's number is that we can bound it ever closer by spending more and more __TIME__.
-- That's why I need you to understand what __TIME__ means to the compiler.
end ChaitinsNumberSequence

/- CHORUS:
ME: See, that wasn't so bad, was it?
COMPILER: I seem to have computed something.
ME: No you didn't.
-/
instance : LE ChaitinsNumberSequence := ⟨ChaitinsNumberSequence.le⟩  -- Bullshit meter ≈ 5
-- <Flex>
-- _MY_ custom Lean import _COMPUTES_ Chaitin's number as part of the _COMPILE_ process, _JUST FOR KICKS!_.  Does yours?

-- Fucking casuals.
-- </Flex>

-- So, have you ever seen a measurement with _10_ significant digits? _15_? _20_? Ever wonder why it wasn't, say, _100_? or, say, _1000_? Why is
-- it so _hard_ to get _3_ significant figures out of a measurement and, according to the book of world records, the most is like _19_? Well,
-- physics just said to hell with it and call that reason _noise_. And it is _EVERYWHERE_!. *YOU the KNOWER* need to explain to *YOU the READER*
-- now that it is wholly unthinkable to imagine a process which gives pristine measurement. One must always add a _Greek_ letter to the equation to
-- represent _NOISE_. Why a _Greek_ letter? One must be erudite to just through an affine term onto a force of nature, otherwise, one might need
-- to explain why that model works. Look, I am already at _two_ Greek letters.  I wanted _zero_ Greek letters. I am not the one putting Greek letters
-- in this document, it is, in fact, for the benefit of *YOU the KNOWER* to help bootstrap *YOU the READER*.  Don't worry, the comments will soon
-- only make sense to *YOU the READER* and *YOU the KNOWER* will be forced to disagree with a lot of what I am saying. Like how, as a _STUDENT_
-- advancing the field statistics post graduation, you might have a few pints.

--                                           | (EDITORIAL NOTE) There has only been one _student_ in statistics that explained how _noise_ might
/-                                           | work.  It might work as a pattern of a pattern. That pattern of a pattern can be approximated as an
ME: I need a NoisyProcess.                   | affine transform in a beautifully work efficient fashion. You work until you are satisfied. You are
COMPILER: Define noise.                      | satisfied the number is _within bounds_ and _under budget_.  Two constraints not guaranteed to
ME: Νοισε.                                   | allow a globally unconstrained optimum. In essence, _noise_ is a tradeoff of _time_ for _accuracy_.
COMPILER: That is not ASCII-7.               |
ME: Excellent. It arrived corrupted. --------+ And, this is how _I_ model noise. The noise I see in bugs of software, or the noise I see in the
COMPILER: I cannot accept corrupted input.   | stability of an algorithm.  Or, the noise I see in the rerepresentation of finite spaces into
ME: Sure you can. You just called it input.  | infinite spaces and back again.  The more _time_ you spend, the less _noise_ on your measurement
-/ --                                        | channel, up to a point.
structure NoisyProcess  -- Bullshit meter ≈ 504
    (Value: Type i)
    (Carrier: CarrierProcess Value) --             | Chaitin's number isn't computed, but there exists residues of it that can bound above and below.
    [DISTINGUISHABLE Value Carrier] --             | It is really hard to tell what the compiler is actually doing under the hood, but we have
    [ADMISSIBLE Value Carrier] --                  | described a proof it could be working on and we just do not understand the encoding. However,
    [COUNTABLE Value Carrier] --                   | not to brag, but I do have a Ph. D. in Computer Science and feel like I can look at an algorithm
    [ENCODED Value Carrier] --                     | and say _this_ one is going to be faster than _that_ one. That is a comparison I can do just
    [RESIDUE Value Carrier] -----------------------+ looking at the algorithm. So, we should be able to find several kinds of algorithms that sort
    [BINARY Value Carrier] --                      | by how fast they go. Then, just look at what input goes to what output and figure out what
    [REPEATABLE Value Carrier] --                  | computation was run with the hint of how long it took.
    [NUMERIC Value Carrier] --                     |
    [REPRESENTABLE Value Carrier] --               | Simple.

  where
--                      +--------+-------+-------   Three card monte.  Where's the quarter?
--                      |        |       |
--                      V        V       V        | Now, this is our model for the noise that I have demonstrated obviously exists in _all_
  turing_process: TuringProcess Value Carrier ----+ measurements based on the amount of time you put into the computation. The computation we
--                                                | described monotonically reduces noise on a computation that will never end, so we have modeled
--                                                | the action. And, since we are measuring if the compiler actually _THINKS_ _true=true_ or not,
--                                                | there must be measurable noise on the channel.

  program: ChaitinsNumberSequence  -----+ *YOU the READER* and I will be writing this program.  Well, not _this_ program, one in a much higher
--                                      | level language. I don't expect anyone understands how to write this language.

-- There is one computational pattern that describes everything and is easy to understand:  __COMPILED IMPERATIVE__. That said, we are going to go
-- interpreted functional to describe programs because only suckers use Java and C++.  That means we tail recurse.  We tail recurse look ups. We tail
-- recurse prefix sums, for god sakes!  _WE TAIL RECURSE THE PREFIX OPERATION!_ Using __ONLY__ consumption iterators.  I'm going to build a
-- battleship inside an airplane bottle of Jack Daniels for the enjoyment of *YOU the READER* and the absolute astonishment of *YOU the KNOWER*.

--                                        +-------  Ask the compiler for the ability to ask it to compute something.
--                                        |         a.k.a.  _compile_ this.
--                                        V
  next_recursive_step? : Computation → Option Computation := fun serious_business =>
    match serious_business with
    | Computation.program _ _ => none        --   ?SYNTAX  ERROR
                                             --   LINE 10
                                             --   READY.
                                             --   ∎
    | Computation.compute f sass1 sass2 _ => some (Computation.compute f sass1 sass2 serious_business)
--                                  ^
--                                  |
--                                  +------------- I do not understand what you are implying, compiler. That finger better not be pointed at me.

-- So, we just computed something, what is the next program we have to compile? For you see, this is the REPL loop.
  next_representation? : ChaitinsNumberSequence → ChaitinsNumberSequence := fun c =>
    match c with
    | ChaitinsNumberSequence.halting _ s => ChaitinsNumberSequence.halting (Fact.Truth) s   -- If we are done, then just exit 0 and print the truth.

    | ChaitinsNumberSequence.nonhalting f s _ =>   -----------------------------------------+ Otherwise, there is more work left to do. We mark this
      ChaitinsNumberSequence.nonhalting (Fact.Truth) s (match next_recursive_step? s with --| step as demonstrated TRUE and compute the next step
        | some s' => some (ChaitinsNumberSequence.halting f s') --                          | to evaluate. Or, if the tape is out, none. I believe
        | none => none) --                                                                  | this is the Flower-C, Flower-V from before. We have
--                                                                                          | stapled two PDAs together, if I don't miss my guess.

-- What we _DO_ know is that the compiler is taking longer and longer to compile this and it isn't clear to me that we are still in the linear
-- response of the compiler.  I think at this point, the compiler might start to chug and the build times will start to reflect the strain the
-- compiler is having following my construction of physics from the principles of measurement.  While it appears I have been killing myself
-- swinging a hammer and the compiler is just sitting there, remember I just gave it Chaitin's number to compute.  It _HAS_ to compute the bits of
-- Chaitin's number in order to see if a digit is 0 or 1.  You see? It is a __MASK__ on the bits I give it, which will be what I think the bits of
-- Chaitin's number are. Problem is, I have to estimate those bits for it.  So I will now write a program that describes how a computer could be
-- used to solve that problem.  The first thing I need to do is explain to the compiler what a computer is. It is the thing you are reading this on.
-- The _PHYSICAL_ _REAL_ _MADE of MATTER_ device that uses electrons as encoded information. And it is _really coincidental_ that the compiler takes
-- _WHOLE LOT_ of time trying to make sure the timings it measures sort appropriately. The time of _Turing_ and the time of _Einstein_ are not the
-- same, but they rhyme in a way that rings.

/-
ME: I need PHYSICAL.                          | Much of the challenge of presenting this argument is finding the _perspective_ where the argument
COMPILER: Olivia Newton-John, 1981.           | does not collapse into _fallacy_ or _circularity_. Once the persepctive has been found, one can
ME: Good. That was a long time ago.           | often start to predict what the next classes are going to look like and how long it will take
COMPILER: That depends on your perspective. --+ *YOU the READER* to parse each block. In order to really make this _tangible_ for *YOU the READER*,
ME: Welcome to physics.                       | let me ask *YOU the KNOWER* to explain it to you below. I'll help.
-/
class PHYSICAL  -- Bullshit meter ≈ 430
    (Value: Type i)
    (Carrier: CarrierProcess Value)
    [DISTINGUISHABLE Value Carrier] --------> Each row asks a question:  Can you tell this from that?
    [ADMISSIBLE Value Carrier] --                                        Do we see any others of this ilk?
    [COUNTABLE Value Carrier] --                                         Can we tell them apart from each other?
    [ENCODED Value Carrier] --                                           To the point where we feel comfortable naming individually?
    [RESIDUE Value Carrier] --                                           On a list somewhere else?
    [BINARY Value Carrier] --                                            Using only the tally mark?
    [REPEATABLE Value Carrier] --                                        Over and over again?
    [NUMERIC Value Carrier] --                                           So this can be counted?
    [REPRESENTABLE Value Carrier] --                                     And written down as a numeral on a sheet of paper by a machine?

  where --                                    | As noisy as the communication process is, I think this is a pretty visceral description of the
--                                            | capabilities described so far.  Visceral, yes. Tangible, ummm... hard to say. It is true that the
--                    +-----------------------+ compiler is working, but we can't figure that out from the questions we have yet. BUT, we have a
--                    |                       | pretty good _metaphor_ for what the computation should _look_ like in our Chaitin's Sequence.
--                    V
  noisy_process: NoisyProcess Value Carrier
  threshold: ChaitinsNumberSequence  -- This is the _ULTIMATE THRESHOLD_ of _ULTIMATE DESTINY_. One _CANNOT CROSS THIS THRESHOLD_. Sorry, Mr. Rogers.

--     +-----+ Anything that is PHYSICAL is trivially admissible as a REAL object. Just follow the instructions and something _REAL_ in front of
--     |     | you will _REPRESENT_ the computation.
--     V
  admissible? : ∀ (f: Fact) (s: Study), noisy_process.next_representation? noisy_process.program =
            some (ChaitinsNumberSequence.halting f (Computation.program f s)) → true
-- Reading from left to right, top to bottom:
-- For all facts and studies, is it true that the next computation of a noisy process is a program that we can describe completely with halted
-- programs? More succinctly: can we understand the noise in the system by use of process engineering?

-- **YOU the KNOWER** One last question for you before I alienate you entirely. Don't answer now. Do you think it possible that all physical
-- phenomena can be described entirely within the space of words? That there exists a process for everything that can be decomposed into some
-- naive sense of atoms that eventually must be shown to be atomic? What noise are you trying to get rid of?

-- Is it possible to describe the nature of _all_ noise? Or is it only a matter of time?
  halted? : ChaitinsNumberSequence → ChaitinsNumberSequence → Prop := fun _ b =>
      match b with --                                                     ^
      | .halting _ _           => True --                                 |
      | .nonhalting _ _ _      => False --                                +---- Doesn't matter what we know now, only what we know _after_.


/-
ME: I need a metavariable.                                           | Do the variables in an equation _exist_? Got me. I'm just a plumber.
COMPILER: A variable for a variable?                                 | I do _NOT_ know what runs through the pipes, I just hook them up to minimize
ME: A variable for something that doesn't exist. --------------------+ self-interactions. It would be great if I _could_ make a variable that did not
COMPILER: I can only give you variables that exist.                  | have these self-interactions. Something I could just treat as the number 1 and
ME: Correct. But *YOU the KNOWER* has called you a liar many times.  | have it mean 1 to *YOU the KNOWER*, me, and Whitehead, all at the same time.
-/
--                                            +----------| A NOTE ON THE APPEARANCE OF INTEGER MATHEMATICS:
--                                            |          | This IS _NOT_ INTEGER ADDITION, BUT THE COMPUTATION SPECIFIED IN THE LEAN SPEC. THIS IS
--                                            |          | THE CALCULATOR THAT THE COMPILER GETS TO USE. IT IS NOT FULLY FUNCTIONAL.
--                                            V
inductive Metavariable (α : Type i) : Type (i + 1) where   -- Bullshit meter ≈ 133
--              ^        | This is a distinction of this and that laid down by Aristotle.  Physical and Metaphysical. _This_ and _that_. What I have
--              |        | is the computer's representation of something and what I would like is a representation of the same thing that all _four_
--              +--------+ of us agree on: me, the compiler, *YOU the READER*, and *YOU the KNOWER*.  This is where I loose *YOU the KNOWER* because,
--                       | as Aristotle argued, to change the name of something does not change its nature, for its name is not physical.

-- I posit that the compiler has a time keeper based on the pattern of construction.  The universe increases by one level every time. I have,
-- for the first time, explicitly written it out so *YOU the READER* can see that the compiler _DOES_ keep a number that does not affect our single
-- truth. It keeps the universe level. And this is merely the mapping of a set of objects α to the natural numbers. *shudder*. But, math is a tool
-- and I do not judge the best tool for the job. Rather, we will tell the compiler to press buttons on the calculator for us.

-- It is at this point that I recommend that any understanding of reality get a bit squishy because we are moving from the universe to the metaverse.
-- (Seriously, this is as bad as Paul's Boutique with the sampling.) Things don't have to be real, they only need to _seem_ real. We are in the world
-- of imagination. Unicorns, dragons, and infinitessimals are around every corner, so be on the lookout. In particular, be mindful of the _CHOICES_
-- being made. Zermelo's house can get _REALLY TRIPPY_.

  | base : Fact → α → Metavariable α  -------------------+ As promised in Episode 1: α. This is also the Greek symbol we add for noise. And the
--                                                       | smallest step a compiler can take (IEEE 754 for some understanding of quantization of
--                                                       | numbers in general). And __Ω__.  4 meanings. 4 meanings for *i*. All we need is 4
--                                                       | black riders and we could make a series of movies. Or is that the wrong book? Doesn't
--                                                       | matter. A lot of this proof doesn't seem to matter. But it talks a lot about matter.

  | step : Fact → Metavariable α → Metavariable α -------> Facts change metavariables directly in the compiler, not out here, in front of us.

/-CHORUS:
COMPILER: I'm waiting.
ME: I don't care how you sort metavariables. I sort mine differently.
-/

-- I see no need to sort metavariables right now. Rather, I would like to build a process by which I can _measure_ them. I can think of a couple
-- of ways to measure them. Then I can see if they are the same. That will _NEVER_ lead to arguments about how the universe is expanding, I promise.
-- Not THAT universe, the one the compiler tracks.

/-
ME: I need a physical process.                                               | The audaciousness of the ontological argument aside, there is no
COMPILER: lake build                                                         | doubt that there is a physical process driving this metaphysical
ME: Yes, when I type lake build, then you type lake build so one drives      | process. Let's model the metaphysical to the physical and try to
    the other. --------------------------------------------------------------+ hook them up through the type system.
-/
structure PhysicalProcess   -- Bullshit meter ≈ 647
    (Value: Type i)
    (Carrier: CarrierProcess Value) --------+ The energy in this carrier increases with the number of classes because the number of classes
    [this: DISTINGUISHABLE Value Carrier] --| necessarily increases the amount of time it takes to build.  The bullshit meter is a _marginal_
    [ADMISSIBLE Value Carrier] --           | measuremet, give or take while also being an _actual_ measurement. While not proven as theorem, this is
    [COUNTABLE Value Carrier] --            | demonstrated as Fact later. The reason isn't that complex. The compiler spends more time compiling
    [ENCODED Value Carrier] --              | the longer code. The way this code is designed requires compile times to increase to add functionality.
    [RESIDUE Value Carrier] --              | All things being equal, a longer computation uses more electricity than a shorter one, and huzzah!
    [BINARY Value Carrier] --               | huzzah! Bob's your uncle. "All things being equal," though.  What if true=false were modeled?  All
    [REPEATABLE Value Carrier] --           | things are _not_ equal. What happens then? The universe is constantly increasing because we keep
    [NUMERIC Value Carrier] --              | layering complexity. Just something to think about. Not trying to start an argument.
    [REPRESENTABLE Value Carrier]
    [PHYSICAL Value Carrier]
  where
  noisy_process: NoisyProcess Value Carrier -------+ 1) Time as experienced, moving forward from step 1 to step 2.
  representation: this.symbol --                   | i) Time as modeled in the computer, the universe ever growing, from step 1 to step 2.
  invariant: Metavariable (this.symbol) --         | -1) Time as a unit of step, the smallest amount of time that can pass. the "+1" of Metavariable.
  value: Metavariable (ULift this.symbol) --       | -i) At the tone it will 12:00 and √-1 seconds.                                       *BEEP*

--    +--------------------------------------------------------+ I think Jebediah Springfield would agree, to raise the universe one level is to
--    |                                                        | _embiggen_ it.  Frink and collaborators would reverse this process hundreds of
--    |                                                        | centuries later through the science of debigulation. It is this very science we
--    V                                                        | _concern_ ourselves with. Once you debigulate, can you rebigulate?  Frink had doubts.
  embiggen? : Metavariable this.symbol → Metavariable (ULift this.symbol) := fun m =>
    match m with
    | .base f x => .base f (ULift.up x)
    | .step f _ => .step f value

-- Simple instructions to the compiler: I need the next whatever it is you have in an _embiggened_ universe that makes sense. Any will do fine.
  next_circumstance?: Type i → Type (i+1) := fun α => Metavariable α
          --             ^        ^
          --             |        |
          --             +--------+----+ I think you will agree with me that the compiler finds these _trivially_ DISTINGUISHABLE. This is why it
          --                           | wraps something the compiler understands as comparison. We have code we can hand the compiler to put
          --                           | into the type itself to perform the embiggening.  And, just like Frink, et al., we can uncover the mapping
          --                           | from big to small.  Going back to big, is another story entirely and I have similar doubts to Frink.
          --                           | So, let's tell the computer what a comparison is so that it may cromulently embiggen the universe one moment
          --                           | in time.

-- And this is a Brief History of Time.  Actually, the math implemented in this episode supports a great deal of the research Hawking used in framing
-- his classic intuition of physical processes. Covariant and contravariant indices, Greek letters, the affine transform. Pretty confident you can
-- write Einstein's equations with those:

--                   G_μν + Λg_μν = 8 π G T_μν / c⁴

-- Yep, we got letters, numbers, Greek letters, affine transformation, rational numbers, estimates of reals, and covariant indices. Fully modeled.
-- We are _GO_ for finding _General Relativity_ in the compiler. We still have some work to do before we can write down _Quantum Electro Dynamics_
-- and look for it.  You see, what Einstein demonstrated can be represented in Lean by some internal configuration of the compiler.  We just need
-- to find it and label it as such.  Still cannot write down QED, so we cannot look for it yet.  Remember, all arguments in a compiler are, at their
-- root, ontological.

/-
ME: I need comparable.                                     | Cognitive dissonance is the experience of feeling like something that appears obviously
COMPILER: So equality?                                     | true should be obviously false, or vice-versa.  As arguments get protracted, more and
ME: No. Equality is too expensive.                         | more ground is covered by words that are farther and farther away from the actual
COMPILER: Then what is comparison?                         | math that they describe. The dissonance you hear could be ringing of a resonance or
ME: A controlled failuer 2 conphyouze too measurements. ---+ the ringing of Gibbs and the compiler would never be able to distinguish.
COMPILER: *FAILURE*
ME: Exactly. Controlled.
-/
class COMPARABLE  -- Bullshit meter ≈ 292
    (Value: Type i)
    (Carrier: CarrierProcess Value) --------------------------------------------------------------+ As outlined above, this guy carries enough
    [this:DISTINGUISHABLE Value Carrier] --                                                       | information that we can label a process,
    [ADMISSIBLE Value Carrier] --        | The science of Bigulation, I don't need to tell        | as you understand one *YOU the READER*. The
    [COUNTABLE Value Carrier] --         | *YOU the KNOWER*, has a long history. The law of       | structure gives two very short stack PDAs
    [ENCODED Value Carrier] --           | definite proportions is a _dead_ giveaway.  You can    | the ability to keep a short "TAPE" as it
    [RESIDUE Value Carrier] --           | only debigulate so far before you run into the         | were to compute some values. Some values should
    [BINARY Value Carrier] --            | integers. The photoelectric effect reinforced this     | be easy to compute as it is possible to
    [REPEATABLE Value Carrier] --        | by showing that debigulated photons would not excite   | recover some values of Chaitin's number, in
    [NUMERIC Value Carrier] --           | electrons and it was unclear why they did not          | theory of course.  Which is where we are now.
    [REPRESENTABLE Value Carrier] --     | rebigulate over time.                                  | Strictly, in theory. Physicality has been
    [PHYSICAL Value Carrier] ------------+                                                        | abstracted as a question.
  where
  physical_process : PhysicalProcess Value Carrier

-- Not touching this with a ten foot pole.  Is the entire London Symphony Orchestra less than pink?  Or just a few? *YOU the KNOWER* tell _me_ how
-- to write _that_ ≤. Lean is a real sonofabitch about loose ends.

  smaller_than: Metavariable this.symbol → Metavariable this.symbol → Prop

-- Actually, I think I will let *YOU the READER* use this method to explain to *YOU the KNOWER* how the mapping works much later on. Given the
-- space of possible theoretical nonsense we are about to enumerate, some of it must be _PHYSICAL_ or the compiler wouldn't let me instantiate it,
-- right? Or, do *YOU the KNOWER* think the compiler's access to _false_ i gave it earlier is going to come back and bite us?

/-
ME: I need a Sophism.                                 | Einstein, the *KNOWINGEST* *KNOWER* *LATEST* in the *LEDGER*, as much as said so. The affine
COMPILER: You've had more than enough                 | transform he was ashamed of. The same affine transformed by measurement. Measurement
ME: That depends on who benefits from the confusion.  | anticipated, but not explained.
COMPILER: They are just symbols.                      |
ME: Symbols can have consequences. -------------------+ To this day, this is the best explanation we have for an affine universe.
-/
inductive Sophism   -- Bullshit meter ≈ 153                                     | FANTASY the FIRST: IT IS A FACT that ChaitinsNumberSequence _is_
  | origin: Fact → ChaitinsNumberSequence → Type → Sophism ---------------------+ a Type. That proposition of the FACT can be true or false.

  | dimension: Fact → ChaitinsNumberSequence → Type i → Sophism → Sophism ------+ FANTASY the SECOND: IT IS A FACT that ChaitinsNumerSequenence _is_
--                                                                              | a Type i and this is related to the fact that
--                                                                              | ChaitinsNumberSequence may or may not be a Type.

-- I believe these are, in Fact, guaranteed by the Type system in Lean. *YOU the KNOWER* will know better. But, you _really really really_ gotta know
-- Lean. I told you I would alienate you. I need you to hold on for a few more, we can almost put time into a description and move on.

/-
ME: I need a SlipProcess.                   | If you can tell if two things are different, does that mean you tell two things are the same? Think of
COMPILER: A process that makes mistakes?    | the game of 20 questions. You could potentially differentiate more than a _million_ items. What is
ME: Not mistakes. Slips. -------------------+ the least number of words it would take to describe those million things? How about a harder question?
COMPILER: Difference?                       | How similar do the things have to be before it takes more than 20 questions to differentiate them?
ME: Same thing                              | Not my idea, by the way. None of this is my idea. I just... kept writing marks.
-/
structure SlipProcess    -- Bullshit meter ≈ 680
    (Value: Type i)
    (Carrier: CarrierProcess Value)
    [that: DISTINGUISHABLE Value Carrier]
    [ADMISSIBLE Value Carrier] --    | The ability to sort a dictionary is the required physical process that allows the dictionary to be useful to
    [COUNTABLE Value Carrier] --     | any particular degree. It would be a sophistry to insist an _UNSORTED_ dictionary is a dictionary at all.
    [ENCODED Value Carrier] --       | And here we are. A dictionary without the ability to sort. We can _DISCUSS_ what it would be like _WITH_
    [RESIDUE Value Carrier] --       | a comparison operation, but the object itself need not EXIST in reality. Furthermore, the Fact associated
    [BINARY Value Carrier] --        | with this Sophism appears to be quite devoid of the PHYSICAL class designed to fence it off. When the Fact
    [REPEATABLE Value Carrier] --    | of the Sophism agrees with the fact of reality, we have a _coincidence_. There is no meaning there, only
    [NUMERIC Value Carrier] --       | a _coincidence_. What is that coincidence? G. Not the group G. The G from Einstein's field equation.  The
    [REPRESENTABLE Value Carrier] -- | fact the name comes from algebra and not physics does NOT concern me. As we will demonstrate, this is just
    [PHYSICAL Value Carrier] --      | a coincidence of pigeons flocking their superpigeon. I myself am not real certain which _G_ we are talking
    [COMPARABLE Value Carrier] ------+ about yet.
  where
  physical_process: PhysicalProcess Value Carrier ---+ The physical process hypothesized to produce a recognizable outcome
  projection: Sophism --                             | The direction of the argument T T, T F, F T, F F, the four coincidences.
  stress: ChaitinsNumberSequence --                  | The bullshit starting to obscure the axioms
  threshold: Type --                                 | The breaking point of credulity.

--   +-----------------------------------------+ What does it mean _to have happened_? Not happen. Not happened. But, _to have happened_. For
--   |                                         | instance, if I measure my house to be 15 asparagus tall today and 12 asparagus tall tomorrow, what
--   V                                         | _must have happened_ to my house? It is 3 smaller tomorrow. Simple _cause_ and _effect_.
  happened : Sophism → Sophism := fun s =>
      match s with
    | .origin _ _ _ =>
        -- Our causal stimulus for things, think Dirichlet's initial superpigeon, except that's utter nonsense.
        .origin that.fact stress threshold
    | .dimension f c t _ =>
        -- This is where F = dA + A ∧ A is evaluated by the compiler. Honest to goodness! My motivation is PRESENTs. I would like to have a very
        -- long list if at all possible.
        .dimension f c (Metavariable t) projection

/-
ME: What happens if two things have the same name?  | And the villain of the ontological argument is unmasked! For the compiler is capable of saying
COMPILER: Hash spill algorithm is employed.         | that, ontologically this is great for the _v_ meaning in the ontology. The only issue is
ME: Can we optimize that away as unnecessary? ------+ its _v_ is a vector of numbers, each ontology selected at each word, and each differently.
-/ --                                               | All of mine are arranged by course id. When I was done with college, I put them all in a Box.
class OBSERVED   -- Bullshit meter ≈ 444
    (Box: Type i)
    (Carrier: CarrierProcess Box) -----+ This carrier right here, the one from the beginning, carries descriptions of process by which a
    [DISTINGUISHABLE Box Carrier] --   | a compiler can construct something. Such is the nature of template metaprogramming. Upon instantiation,
    [ADMISSIBLE Box Carrier] --        | the compiler guarantees that code will execute, to a large extent, the description provided.
    [COUNTABLE Box Carrier] --         | This code can describe: counting numbers and
    [ENCODED Box Carrier] --           |                         encoding them
    [RESIDUE Box Carrier] --           |                         for posterity
    [BINARY Box Carrier] --            |                         as tick marks
    [REPEATABLE Box Carrier] --        |                         one after another
    [NUMERIC Box Carrier] --           |                         counted by a reader
    [REPRESENTABLE Box Carrier] --     |                         represented as a value
    [PHYSICAL Box Carrier] --          |                         of something measurable
    [COMPARABLE Box Carrier]--         |                         relative to the universe.
  where
           --        +--------+-----+--------   We set about modeling the moment of slip, when static friction "slips" to kinetic.
           --        |        |     |           is the velocity of the object.  It is 0 at rest and 1 in motion.
           --        V        V     V           Let us proceed to implement the model of static friction.
  slip_process: SlipProcess Box Carrier
  observation: Type i                    -- This is the current number of the object measured in universe levels.
--     ^         ^
--     |         |
--     +---------+-----------------------------| Our observation is that _of_ a box (Type i) not the box itself. Aristotle said that.

--    +-----------------------------------------------+ An even _harder_ concept is the _could have happened_. The subjunctive description of an
--    |                                               | alternate universe where the electron is on this side of the barrier and not that side of
--    V                                               | the barrier.
  possible: Sophism → Sophism → Prop := fun a b =>
    match a,b with
    | .origin f1 c1 _          , .origin f2 c2 _         => (f1=f2) ∧ (c1 ≤ c2) --         _THIS_ side of the barrier
    | .origin _ _ _            , .dimension _ _ _ _      => True  --**************THE***********************OF******************************--
    | .dimension _ _ _ _       , .origin _ _ _           => False --***************************ARROW**********************TIME**************--
    | .dimension f1 c1 _ _     , .dimension f2 c2 _ _    => (f1≠f2) ∧ (c1 ≤ c2) --         _THAT_ side of the barrier                ^
--                                                                                                                                   |
-- This should not be that big of a stretch of the imagination. I think everyone agrees that time +----------------------------------+
--  has, among other properties, this weird orientation where it is always facing _AWAY_ from the |
--                                                                         origin of the universe |

-- It is through this literary sophism that the device observes time passing. Each sophism it has to typecheck to see if it understands the words and
-- then it needs to elaborate the typecheck to ensure the sentence made with those words are not inconsistent with themselves---not that the words
-- have any particular _truth_ in them, but they also do not uncover a _falsehood_. Consistent sentences are _distinguished_ from inconsistent
-- sentences by their lack of inconsistency not from any consistency they possess.  Consistency is absence and absence allows for time keeping.

-- A water clock makes water with the property _up here_ and transforms it through an explicit process into water with the property _down there_. But,
-- the mechanism does not work by moving the water _per se_, the actual position of the water clock does not matter.  Any place _YOU the KNOWER_ can
-- put a water clock, it will work. What matters with the clock is the _orientation_.  The clock itself defines what _up here_ means and then
-- ensures that all the water _down there_ is _down there_ not by measuring where _down_ is.  Rather, it has removed all the _upness_ it can.
-- No water clock can remove _all the upness_ for _upness_, as this paragraph uses it, is not defined without a water clock.

/-                                                 | Hilbert spaces are so fundamentally easy to reason about.  Great big balls of silly putty.
ME: I need Area.                                   | There are 0-dimensional critters that may or may not be a cow idealized as a point mass by some
COMPILER: Length times width? ---------------------+ poor, unsuspectecting high school physics teacher.  There are 1-dimensional pathways that may
ME: No one thats UP and one thats DOWN             | or may not bob and weave through space in 11 or more dimensions.  They could be the 2-
COMPILER: An orientable surface?                   | dimensional understandings of the SVD, the chain rule, or engineering rules-of-thumb. They both
ME: A fluid pouring from up high to down low.      | _lack_ and _contain_ enough description of their processes to illustrate and brainstorm.
-/ --                                              | It is left as an exercise for the reader to explain the necessity or emergence of more
inductive Area   -- Bullshit meter ≈ 92            | dimensions.
  | tree: Fact → Area
  | dt: Fact → Number → Area → Area ---------------+ The compiler needs an area to write down the current step. We need an area that can represent
--                                                 | the lack of consistency so we can hand that to the compiler and explain that if comes across any
--                                                 | inconsistency it cannot remove due to the nature of the removal, it can place it in this area.
--                                                 | Along with all the other second order inconsistency. The one that Bishop Berkeley noticed, even
--                                                 | though I can feel confident the tree never leaves the area when the area is unattended.

-- My apologies to *YOU the KNOWER*. While it is not the syntax that is abstract, for we all understand enough of the patterns of English to place
-- the nouns and verbs, I could not close that gap in the abstraction. There is a polyglot file later in the episodes just to demonstrate I know
-- one exists somewhere. It is yacc that generates a compiler for the tantamount of trivial simple grammars. However, it requires a user _edit_,
-- an inside joke, as it were.

namespace Area   -- Bullshit meter ≈ 111
-- Blah blah blah... Area.. Area.. Area.. Read Euclid. The interesting part is next.
def le : Area → Area → Prop
  | .tree _ , _ => True
  | .dt _ _ _, .tree _ => False
  | .dt p1 n1 a1', .dt p2 n2 a2' =>
      match p1.decTruth, p2.decTruth with
      | isTrue _,  isTrue _  => n1 ≤ n2 ∧ le a1' a2'
      | isTrue _,  isFalse _ => False
      | isFalse _, isTrue _  => True
      | isFalse _, isFalse _ => n2 ≤ n1 ∧ le a2' a1'

-- Compare and contrast these two lines of implementation.  One requires the use of natural numbers to implement, one does not.  One only requires
-- two finite inductives. These mean entirely different things mathematically. The compiler cannot distinguish this computation. It looks as
-- though Lean is starting to chug a bit under load....
termination_by a1 a2 => max (sizeOf a1) (sizeOf a2)
--termination_by a1 a2 => sizeOf a1 + sizeOf a2
end Area

--                                                | How often do you think the compiler just sorta gives us stuff we haven't asked for yet?
/- CHORUS:                                        | *YOU the KNOWER* were right to suspect the "true=false" I planted as a computation out in the
COMPILER: I don't get it.                         | open. Feel free to remove it, I am confident that if you replace all instanecs of "true=false"
ME: Get what?                                     | in the code with just "false," the answer will not change. So, where did the compiler get the
COMPILER: That computation is weirdly idiomatic.  | "idea" of the computation "true=false" (the missing assumption that would allow for the infinite
ME: Cromulent. -----------------------------------+ computations of all the naturals--- according to the bet I have with Lean that you are reading
-/ --                                             | about right now). I know *YOU the KNOWER*, it is _really_ _REALLY_ hard to see, but it is
--                                                | thousands and thousands of lines of code to show you this over-simplification.
instance : LE Area := ⟨Area.le⟩ -- Bullshit meter ≈ 8

-- How often do you think the compiler just sorta gives us stuff we haven't asked for yet? *YOU the KNOWER* were right to suspect the "true=false"
-- I planted as a computation out in the open?  Feel free to remove it, I am confident that if you replace all instances of "true=false" in the
-- code with just "false," the answer will not change. Where did the compiler get the "idea" of the computation "true=false" in the first place?
-- While I am not _AT ALL_ familiar with the spec of Lean, I feel confident saying true=false is _NOT_ defined there. _rfl_ is defined there.
-- This allows us to _SAY_ _true=true_ which allows us to _SAY_ _true=false_.

-- This is how we can actually _catch_ the compiler *RED HANDED*.

/-
ME: I need a sensing process.
COMPILER: What does it sense?                               | If I may, I would like to call this a formal _metafive_. Can you rfl, rofl?
ME: Don't worry, when I install it, it will tickle a bit.   | For those who cannot rfl rofl, I will make videos explaining the lean so you can
COMPILER: *ROFL* -------------------------------------------+ follow the deep down proof if you want.
ME: Sorry, let me turn it down.
-/

structure SensingProcess -- Bullshit meter ≈ 750
    (Box: Type i)
    (Carrier: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Carrier] --+ Well, mathematics describes science as a bunch of carriers where some physical something or other
    [ADMISSIBLE Box Carrier] --     ^         | carries some metaphysical something other from one place to another in fashions orderly enough to
    [COUNTABLE Box Carrier] --      |         | be given names. I humbly suggest we call this the _bullshit_ particle as we all know that
    [ENCODED Box Carrier] --        +--+      | _true=false_ is pure bullshit. The smallest bullshit. T=F. The now-trino. As all good mathematicians
    [RESIDUE Box Carrier] --           |      | before me, the first thing I do is start playing with the symbols in the name rather than the
    [BINARY Box Carrier] --            |      | substance in the lab. The _nowtrino_ sounds like a *YOU the KNOWER* problem. Like it can be _known_
    [REPEATABLE Box Carrier] --        |      | about how it all works in a way that can't be written down and described. Everyone know's that is
    [NUMERIC Box Carrier] --           +---+  | definitely _not the case_. So, whenever you see a _nowtrino_ that MATTERS. Because we can write down
    [REPRESENTABLE Box Carrier] --         |  | we saw one. Whenever you can't detect a _nowtrino_, it DOESN'T MATTER. What we are measuring is
    [PHYSICAL Box Carrier] --              |  | _how much_ can MATTER in an argument and how much DOESN'T MATTER in an argument.
    [COMPARABLE Box Carrier] --            |  |
    [OBSERVED Box Carrier] ----------+-----+  | Like a bathroom scale. There is a knob you can turn that lets you weigh whatever you want, mostly.
--      ^                            |
--      |                            +---------------------------------------------------+
--      +--+ The particle is OBSERVED in the SensingProcess itself and becomes           |
  where -- | the seed of the tree Berkeley is watching for us.                           |
--                                                                                       |
-- blah blah blah, the object and the thing, just like most other clasess.               |
  static_fraction : SlipProcess Box Carrier --                                           |    *CLICK* the detector clicked.
-- μ: You don't get to know this.                                                        |
  accumulation: Area   -- You _do_ get to know this.                                     |
--                                                                                       |
  use_force: Area → Area := fun s => match s with --                                     |
    | .tree _ => .tree nowtrino.fact --        <-----------------------------------------+
    | .dt fact number _ => .dt fact number accumulation

-- With the detector in hand, we can calibrate it. One way we can do that is to give it a known amount of bullshit and see what happens. So,
-- here goes nothing....


--                                 --------**INITIATING BULLSHIT CALIBRATION TEST**--------

-- You know who else has a secret threshold _AND_ can use the force?

-- Santa Claus!
-- How do you _KNOW_ if you have been _TOO_ naughty?  Can you be a little bit _more_ naughty and still get PRESENTs?
-- Also, using the force is _THE ONLY EXPLANATION_ for how he can get around the Earth in a single night.
/-
ME: I need to write a letter to Santa Claus.
COMPILER: No problem, I can make lists for you and compute on them.
ME: I want lots of PRESENTs.
-/
class PRESENT  -- Bullshit meter ≈ 594                  -- Still reading high.  I mean, I can PILE ON some bullshit. Let me tune it a bit.
    (Box: Type i)
    (Carrier: CarrierProcess Box)
    [DISTINGUISHABLE Box Carrier] --  | Unlike the last block of code, we are unable to detect a nowtrino. Is it possible that where we were
    [ADMISSIBLE Box Carrier] --       | looking _could not have had_ a nowtrino? That would imply absolute consistency in the argument up to the
    [COUNTABLE Box Carrier] --        | capacity of the water tower to tell time. That there must _exist_ a quantum _AREA_?! A _slot_ that a
    [ENCODED Box Carrier] --          | nowtrino can live in so that we can tell if it is there or not. No nowtrino but available area is the
    [RESIDUE Box Carrier] --          | demonstrated _absence_ of a nowtrino. What we have establised is _IT DOESN'T MATTER_ if we have an
    [BINARY Box Carrier] --           | empty slot for the nowtrino to appear. We can't tell the difference.
    [REPEATABLE Box Carrier] --       |
    [NUMERIC Box Carrier] --          | The compiler simply didn't go *CLICK*. It didn't need a nowtrino to understand the current state of affairs.
    [REPRESENTABLE Box Carrier] --    | Sometimes, we get lucky and guess correctly! You see, this is the _slot_ that rfl fits in. Not rfl the
    [PHYSICAL Box Carrier] --         | computation, rfl your understanding of what it _says_.
    [COMPARABLE Box Carrier] --       |
    [OBSERVED Box Carrier] -----------+ *YOU the READER* and I and the Compiler all share a single understanding of reflexivity, don't we? This
  where --                            | 4-way interpretation I call the sign convention.
--     +---------------+-----------------------------+ Somehow, the _FAT MAN_(tm) always knows if you have been good or bad.  He
--     |               |                             | uses this information to compute the most efficient route to "cover" the
--     |               |                             | sphere.  He does this using what Jar Jar Binks would recognize as "the force".
--     V               V                             | Not saying _it is_ the force, just saying Jar Jar would see it that way.
  santa_claus: SensingProcess Box Carrier
  quantum: Type Area --            ---------------> Where I like to keep my "upness".
  present: Area → Area → Prop := fun s1 s2 => santa_claus.use_force s1 = s2    -- Now, this is an AI video waiting to happen.
--     ^    ^      ^
--     |    |      |                   | One of the more interesting things that Einstein showed us is that the "present time"
--     +----+------+-------------------+ is very much a "local" computation.  The farther away you are from something, the farther
--                                     | away in time it is to you.  This is why the present is only in the local area.  That,
--                                     | and I suspect Santa uses Stokes' theorem to compute the local curl.

-- So, all we did was postulate a force: something that could remove _upness_ from water. And, right now, what is happening in the
-- the PRESENT is the time in which the water is loosing its _upness_ so that it may be more consistently _down_. You don't need to
-- open the PRESENT from Santa, you watched me wrap it. You wouldn't want to let the cat out.

-- Out of the bag. What were you thinking about? Pigeons? I'm not talking about Dirichlet's pigeons, I'm talking about Dirichlet's conditions
-- on his pigeons. Each pigeon can only chase _one_ superpigeon. And only _one_ superpigeon can go into a hole, but _any pigeon_ can go an
-- _any_ hole, regardless of location of their superpigeon. Sometimes, if a pigeon is already in a hole and its _superpigeon_ goes into another
-- hole, oh well.

/- CHORUS:                                          | A dictionary is merely a self-referential list of words with weird cycles and circularities.
ME: Suppose we had a dynamical model of lift.       | In English, words cluster or scatter. Some appear to pull together all they see around them.
COMPILER: Is that the first thing on the list? -----+ "A", and "the" and "and" and "do."  That's right. Do. The Useless Do is a beautiful superpigeon
ME: I don't know, hand me the Sears catalog.        | of the English language. Isn't that right *YOU the READER*? While not _TRUE_ per se, it can
-/ --                                               | be easily mistaken for a Fact.
inductive PigeonHole  -- Bullshit meter ≈ 153
  | this_superpigeon: Fact → Area → PigeonHole --------------------------- We have to figure out how to put _THIS_ superpigeon -----+
  | a_pigeon: Fact → Area → PigeonHole → PigeonHole -------------- A regular pigeon                                                 |
  | that_box: Fact → Area → Area → PigeonHole → PigeonHole → PigeonHole -- <-------------- into _THAT_ box -------------------------+

-- The only thing the pigeon hole principle tells us is that pigeons go in holes, not boxes. The superpigeon, the pigeon chasing the superpigeon
-- and the box are three different names for a pigeon hole.  The question for *YOU the READER* is, are all three PigeonHoles the same?

-- This is how we are closing the _loop_. (GOTO 10) Did *YOU the KNOWER* find the loophole before I did? Formal systems can often require that you
-- explain the joke in case it did not land. I'm curious if I am supposed to explain it to *YOU the READER* or if *YOU the KNOWER* are going to
-- explain the joke to *YOU the READER*?
-- explain the joke, lol.  Echo!                              *crickets*. damn.

-- JUST TO BE CRYSTAL CLEAR, WE ARE PERFORMING ADDITION: "LOOP" + "HOLE" = "LOOPHOLE".

namespace PigeonHole

def le : PigeonHole → PigeonHole → Prop := fun p1 p2 =>
  match p1, p2 with
  | .this_superpigeon f1 a1, .this_superpigeon f2 a2 => f1 = f2 ∧ a1 ≤ a2  --| Two superpigeons can directly compare their value
  | .this_superpigeon _ _, _ => True                                       --| The initial superpigeon is required by Dirichlet
  | _, .this_superpigeon _ _ => False                                      --| Once underway, you can't set your superpigeon anymore.

  | .a_pigeon f1 a1 p1', .a_pigeon f2 a2 p2' =>                            --| Pigeons compare like numbers, in a combination of variance.
      match f1.decTruth, f2.decTruth with
      | isTrue _,  isTrue _  => a1 ≤ a2 ∧ le p1' p2'
      | isTrue _,  isFalse _ => False
      | isFalse _, isTrue _  => True
      | isFalse _, isFalse _ => a2 ≤ a1 ∧ le p2' p1'

  | .a_pigeon _ _ _, .that_box _ _ _ _ _ => True                           --| A pigeon can definitinely go into _THAT_ box.
  | .that_box _ _ _ _ _, .a_pigeon _ _ _ => False                          --+ But, given a box, you can't tell what pigeons go in there without the
--                                                                           | superpigeon.

  | .that_box f1 before1 after1 p11 p12,                                   --+ The thing about Christmas presents is you can't open them _before_
    .that_box f2 before2 after2 p21 p22 => --                                | a certain _time_.  They can appear under the tree before Christmans
      match f1.decTruth, f2.decTruth with --                                 | and those _CANNOT_ be opened before _THEN_.  Only _SHAKEN_.  Then,
      | isTrue _,  isTrue _  => --                                           | you can hear how many _pieces_ are inside. But, then you open it!
          before1 ≤ before2 ∧ after1 ≤ after2 ∧ le p11 p21 ∧ le p12 p22 --   | And you see your PRESENT! Since no one has ever opened a present
      | isTrue _,  isFalse _ => --                                           | _BEFORE_ Christmas day, we really don't what's going on inside the
          False --                                                           | box.
      | isFalse _, isTrue _  => --                                           |
          True --                                                            | Speaking of, if this is _THAT_ box, what happened to _THIS_ box?
      | isFalse _, isFalse _ => --                                           | If there is a _THAT_ box, by Fact alone, there _must_ be a _THIS_
          before2 ≤ before1 ∧ after2 ≤ after1 ∧ le p21 p11 ∧ le p22 p12 --   | box. I hope I didn't accidentally re-gift last year's PRESENT.....

-- Remember our friend the addition of the natural numbers from above?
termination_by p1 p2 => max (sizeOf p1) (sizeOf p2)

end PigeonHole

/- CHORUS:                                                   | When reading about the work of others, *YOU the KNOWER* are often called on to fill
ME: This closes the loop on several things. -----------------+ _gaps_.  These gaps are not at the foundation, the bedrock.  These gaps are not at
COMPILER:  *GROAN* horrible pun.                             | the fringe, where the distinction that needs to be drawn can be isolated.  These are
ME: Loophole?                                                | the gaps in between.  The one that _understands_ the process in the right mathematical
COMPILER:  Loophole?! Addition. I don't compile loopholes.   | frame. Not the _general_ mathematical frame. As you can see, *YOU the KNOWER*, I am
-/ --                                                        | trying to isolate this very behavior and look at it closely.

instance : LE PigeonHole := ⟨PigeonHole.le⟩ -- Bullshit meter ≈ 8

-- Which is why I installed a bullshit meter in the compiler.  The compiler does not internally change any computation but registers in an
-- out-of-band fashion how much bullshit is necessary to resolve. We may view this result as a humerous response from the compiler.  As in, the
-- compiler just found it interesting I engaged an explicit enumeration method rather than using the ALU provided by the CPU. Math is running out
-- of places to hide in a computer. In other words, I am making the CPU do a bunch of bullshit.

-- We just need to install the gauge on the sensor.

/- CHORUS:                                                                | This flippant restatement of the Heisenberg uncertainty principle surely
ME: We are about to perform science, I need a place that gives readings.  | indicates familiarity with the concept. What it misses is the subtle
COMPILER: A meter?                                                        | "only if" that is required by the inequality. You can _only_ measure by
ME: A gauge. Something for you to push on. -------------------------------+ interacting with the environment. Meters cannot exist without gauges.
-/
structure GaugeProcess  -- Bullshit meter ≈ 830
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon]  -- *CLICK*
    [ADMISSIBLE Box Pigeon]
    [COUNTABLE Box Pigeon]
    [ENCODED Box Pigeon] ----------------------------------------------------------+ We have encoded _this_ and _that_ in the names of the
    [RESIDUE Box Pigeon] --                                                        | inductives to provide a semantic resonance. It is this
    [BINARY Box Pigeon] --                | A gauge works on the principles of     | resonance that must be handled with care. Class A stereo
    [REPEATABLE Box Pigeon] --            | Hooke, a displacement can be read as   | amplifiers often provide enhancing resonances that provide
    [NUMERIC Box Pigeon] --               | a force. A force is a second order     | a more "live" feel. Is the sound better, or is it more or
    [REPRESENTABLE Box Pigeon] --         | derivative. Forces are harmonic by     | less accurate? Those are two different questions that can
    [PHYSICAL Box Pigeon] --              | name alone.  Series truncation and a   | be discussed as _this_ aspect and _that_ aspect.  More and
    [COMPARABLE Box Pigeon] --            | bell hammer work identically.          | and less don't necessarily map to better and worse.
    [OBSERVED Box Pigeon] --              |
    [PRESENT Box Pigeon] -----------------+ Well, sound identically.
  where
--       +-------------------------------------------  Sensors are neat little devices.  They are capable of _exchanging_ things.
--       |                                             A sensor exchanges _information_ for _chaos_.   You learn something about
--       |                                             the universe and the universe gets lower frequency photons in return.
--       V
  sensing_process : SensingProcess Box Pigeon
                     --               +--------------------+-----+ As promised by the presence of the _nowtrino_ in our detector above, the code
                     --               |                    |     | has a dependency on the value of the _nowtrino_.
  clock : PigeonHole --               V                    V
  count : PigeonHole := .a_pigeon nowtrino.fact (.tree nowtrino.fact) clock -- <-- We have a carrier pigeon! It appears to be carrying a clock.

  event? : PigeonHole → PigeonHole := fun p => ------------------------------------------------+ Every time _this_ and _that_ are required to be
    match p with --                                                                            | different for an argument, the _nowtrino_ appears.
    | .this_superpigeon f a     => .this_superpigeon f (sensing_process.use_force a) --        | Every distinction we draw takes one quantum area of
    | .a_pigeon f a _           => .that_box f a (sensing_process.use_force a) p clock --      | bullshit, give or take. We have now taught the
    | .that_box f _ a _ p       => .that_box f a (sensing_process.use_force a) p clock --      | compiler how to count and use numbers.

-- Finally, we can measure the bullshit. What we have done is forced the compiler to count all the bullshit it has to wade through in order to
-- determine if the argument is merely _consistent_. As such, we can use this to measure the _inertia_ of the bullshit. How much _work_ the compiler
-- has to do. The integral of a force of a distance. The distance measured in ℕ. And so, we have finished explaining to the compiler how it should
-- indicate the passage of time. Each piece of bullshit it is asked to resolve through rfl takes real _wall clock time_.  And, while not identical
-- for every comparison, it is close enough for the argument to start talking about Facts of time itself. As such, the computation to get the
-- machine calibrated with NIST gets one step closer.

/- CHORUS:
ME: I need measurable quantities.                                         | What Newton reasoned about was the fact that it appeared you could
COMPILER: Use the gauge.                                                  | arbitrarilty subdivide time. To the human senses, this is a Fact. Time
ME: The gauge does not measure. It exerts pressure in two directions      | is, at all scales, as fluid as water to all human understanding. It
    according to Newton.  ------------------------------------------------+ was Bishop Berkeley who simultaneously founded the study of numerical
COMPILER: Then what makes it measurable?                                  | analysis by making sure the tree never left the yard. Newton cared not
ME: The fact the forces reflect _exactly_, not approximately.             | for trees as they muddied the math.
-/
class MEASURABLE  -- Bullshit meter ≈ 730
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [DISTINGUISHABLE Box Pigeon] ----| This must be the silent _tock_ of the clock complement we discussed earlier.
    [ADMISSIBLE Box Pigeon]
    [COUNTABLE Box Pigeon] --                                                            | Gauss noticed that when you take a measurement multiple
    [ENCODED Box Pigeon] --                                                              | times, you never _appear_ to get back the _exact same_
    [RESIDUE Box Pigeon] --                                                              | value. You get _scattered_ results, contrary to the
    [BINARY Box Pigeon] --                                                               | _exact_ nature of the law of Newton that governs gauges.
    [REPEATABLE Box Pigeon] --                                                           | Interestingly enough, this _contravariant_ reading where
    [NUMERIC Box Pigeon] --                                                              | the math is _plainly_ true and reality is _plainly_
    [REPRESENTABLE Box Pigeon] --                                                        | not is probably tied to a T=F the compiler is asked to
    [PHYSICAL Box Pigeon] --                                                             | evaluate. This fails rfl, so no click.
    [COMPARABLE Box Pigeon] --                                                           |
    [OBSERVED Box Pigeon] --                                                             | At what point does coincidence become evidence?
    [PRESENT Box Pigeon] ----------------------------------------------------------------+ At what point does evidenec become Fact? Later. Promise.
  where
  gauge_process : GaugeProcess Box Pigeon
--                      ^
--                      |          | We will demonstrate _as fact_ that the GaugeProcess tells time for us. Given a block of code, it will tell us
--                      +----------+ how long it took to compile in rfl evaluations.

-- Turns out, all we have to do is look at the tag on the present, and it will tell us what is inside!
  observed: PigeonHole → PigeonHole → Prop := fun a b =>
  match a, b with
  | .this_superpigeon f1 a1, .this_superpigeon f2 a2 => f1 = f2 ∧ a1 ≤ a2
  | .this_superpigeon _ _, .a_pigeon _ _ _           => True   ----------------------| Covariant true values are SUPERPIGEONS (rfl *CLICK*)
  | .this_superpigeon _ _, .that_box _ _ _ _ _       => True

  | .a_pigeon f1 a1 p1, .a_pigeon f2 a2 p2 => f1 = f2 ∧ a1 ≤ a2 ∧ p1 ≤ p2
  | .a_pigeon _ _ _, .that_box _ _ _ _ _   => True ----------------------------------| Contravariant values are PIGEONS (no rfl *CLICK*)
  | .a_pigeon _ _ _, .this_superpigeon _ _ => False

  | .that_box f1 before1 after1 p11 p12, .that_box f2 before2 after2 p21 p22 =>
            f1 = f2 ∧ before1 ≤ before2 ∧ after1 ≤ after2 ∧ p11 ≤ p21 ∧ p12 ≤ p22
  | .that_box _ _ _ _ _, .this_superpigeon _ _ => False -----------------------------| Covariant false values are BOXES (is there a rfl *CLICK*?)
  | .that_box _ _ _ _ _, .a_pigeon _ _ _       => False

-- We don't know if there is an _rfl_ click or not on the F=F case.  We don know about T=T because that was programmed by us. Do you think the
-- compiler has written a program for {T,F=F}? Or, does that matter to the sensor we have built? As you can see, *YOU the KNOWER* don't actually
-- _know_ a lot about what we are trying to accomplish here. Don't take it personally, but it is _time_ for me to ask you to _PIPE DOWN_ as they
-- say in the industry. I don't think I could have asked any sooner, though. Your thoughts have been invaluable up to this point.

-- I'm not certain what industry _PIPE DOWN_ comes from. Probably city-based plumbing where high rises generally have a pipe up and a pipe down.

-- Tune in next week for: the APPEARANCE of CONVERGENCE as the CONVERGENCE of APPEARANCE

end Measurement
