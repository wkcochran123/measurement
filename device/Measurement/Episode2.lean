/-
__Measurement: The Tragedy of John Henry__
__A Satire in Look Ahead Backus-Naur Form__

_This is a gentle reminder that the convoluted stories we tell ourselves are just that: convoluted._

(c) 2026 All rights reserved -- obligations, however, are freely distributable.

__EPISODE 2__: _Time_

"Yo dawg! I heard you like to prove theorems, so I put a theorem prover in your theorem prover so you can prove theorems about proving theorems
while you prove theorems about proving theorems."
                                  -- Willie Nelson.  Really confident XZibit covered it. j/k, i got no beef with X to the Z.

lake build --no_assumptions --splash_damage=on

__LIVE__
_without a net_, its.......
-/

-- The story so far.....
import Measurement.Episode1

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
    [d: DISTINGUISHABLE Value Carrier] --        | universe level. This class is guaranteed to carry the latest structure, implying that this
    [a: ADMISSIBLE Value Carrier] --             | class must live at a universe level higher than the process inside it. Since all these classes
    [c: COUNTABLE Value Carrier] --              | must remain constructible beneath the giant overlay of templated, Fibonacci-style constructors,
    [e: ENCODED Value Carrier] --                | there must exist a permutation of Facts that permits explicit construction of relations capable
    [r: RESIDUE Value Carrier] --                | of arbitrarily ordering the permutations. Then it is merely a mapping that must be constructed.
    [b: BINARY Value Carrier] --                 | The only way to construct that mapping is to ask the compiler a bunch of questions, over and over,
    [f: REPEATABLE Value Carrier] --             | creating the pseudo-inverse one bit at a time. In a repeatable fashion.
  where
  -- I feel as though I am twisting Lean into more of a COBOL style syntax. More Knuthian than anything I would ever care to admit to myself.
  computational_process: ComputationalProcess Value Carrier

  carrier: Study := .hypothesis d.fact -- The box it came in.

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

@[reducible]
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
-- needs a little help selecting a symbol.  When you __WRITE__ programs, you have to explain the symbols __BOTH__ to the compiler and to the
-- __MAINTENANCE__ developer.  Have pity on those less fortunate.
@[reducible]
/-                                                            | The ontological argument is simultaneously immensely powerful and comically
ME: I need REPRESENTABLE.                                     | ineffective. Simply defining the object to _be_ the object desired, you can walk
COMPILER: I can do that. I am a kind of ventriloquist.        | backwards algebraically through definitions to build the magicians slip knot.
ME: You make symbols speak?                                   | We have taught the compiler to build VERY complex reasoning structures and insisted
COMPILER: I make values speak through symbols. ---------------+ that it reduce _EVERYTHING_ to the algebraic property of reflection (see
ME: Interesting.                                              | BigRedDogProcess in later episodes).
COMPILER: Why are you looking at my hand?                     | Everything, to the compiler, is an ontological argument. For that is the nature of
ME: No reason. Continue.                                      | representation.
-/ --
class REPRESENTABLE  --  Bullshit meter ≈ 261
    (Value: Type i)                           -- Representation is the core challenge of communication _AND_
    (Carrier: CarrierProcess Value)         -- understanding.  Without a representation of an idea, then
    [d: DISTINGUISHABLE Value Carrier]      -- that idea may or may not exist outside the random synapse
    [a: ADMISSIBLE Value Carrier]           -- firings in your head.  What makes those synapses comprehensible
    [c: COUNTABLE Value Carrier]            -- is the fact we __ALL__ agree that the representation of those
    [e: ENCODED Value Carrier]              -- signals translates to a __DIFFERENT__ yet __CONGRUENT__
    [r: RESIDUE Value Carrier]              -- set of signals in the brain of others __AS WELL AS__ the computer
    [b: BINARY Value Carrier]               -- that will soon chug to the point of sucking mud.
    [f: REPEATABLE Value Carrier]
    [n: NUMERIC Value Carrier]              -- Holy crap, a carrier of value! The compiler and idea can talk about value!
  where
  calculation_process: TuringProcess Value Carrier
--                                +-------------------  Halting problem sez what? To even _TALK_ about a Turing
--                                |                     machine, you have to aware of the halting problem itself.
--                                |                     So, we _DO NOT_ have any guard rails here, you must _KNOW_
--                                V                     _a priori_ your algo halts on all inputs.  Or, it's your own fault!
--  REPAIR
  representable?: ∀ (_: Fact) (s: Study), ∃ (_: Computation), calculation_process.computational_process.closure s = s
--   I hope you understand now that this IS NOT GIVEN                                         ^       +--- rofl. Also, Kirk
--   by mathematics.  The symbols come from elsewhere.                                        |       |    was the better
--                                                                                            +-------+    captain!

  loaded: Computation → Computation → Prop := fun a b =>
        match a,b with
        | .program f1 s1          , .program f2 s2             => f1=f2 ∧ s1 ≤ s2
        | .program _ _            , .compute _ _ _ _           => True
        | .compute _ _ _ _        , .program _ _               => False
        | .compute f1 s11 s12 c1  , .compute f2 s21 s22 c2     => (f1=f2 ∧ (c1 ≤ c2)) ∨ (f1 ≠ f2 ∧ s11≤s21 ∧ s12 ≤ s22)
-- Now, computation itself.  There is an honest-to-goodness __PHYSICAL__ barrier to computation that cannot be crossed.
-- It is the computation of Chaitin's number.  So, let's ask the compiler to start work there.  I believe I will have
-- the easiest time on the planet bogging this little monster with the only physical computational barrier that is
-- known to exist!
/-
ME: I need Chaitin's number sequence.

COMPILER: Absolutely not.

ME: I am not asking you to "compute" it.

COMPILER: You named it.

ME: I am asking you to agree this kind of sequence could exist in theory.

COMPILER: "In theory" is doing a lot of work.

ME: Perfect. Give it a hard hat.
-/
inductive ChaitinsNumberSequence  -- Bullshit meter ≈ 112
-- The __HEAVY WEIGHT CHAMPION OF THE WORLD__
  | halting: Fact → Computation → ChaitinsNumberSequence
  | nonhalting: Fact → Computation → Option ChaitinsNumberSequence → ChaitinsNumberSequence

-- The idea is simple.  We need to calibrate the compiler.  And there is only one universally computable constant
-- that has fully predictable behavior yet completely unpredictable behavior:  Chaitin's number.
-- The idea is to try some variation in our idea of Chaitin's number and the compiler's definition of Chaitin's number
-- and see if it comes down to the order of computation we are using as our bits come in out of order.
-- If I compute 1 and the compiler computes 0, then I may need to commute a computation.  (That's 6 shadows right there.)
-- BUT, if I compute the same bits in the same order over and over, I will start to believe that the compiler is actually
-- computing Chaitin's number.  What are the odds?

-- Seriously, what are the odds?  That's what we are playing for, right?

namespace ChaitinsNumberSequence  -- Bullshit meter ≈ 91
def le : ChaitinsNumberSequence → ChaitinsNumberSequence → Prop
  | halting _ s1, halting _ s2 => s1 ≤ s2
  | halting _ _, nonhalting _ _ _ => true
  | nonhalting _ _ _, halting _ _ => false
  | nonhalting _ s1 _, nonhalting _ s2 _ => s1 ≤ s2

-- Can't compute lt.  Against the rules.
-- The thing about Chaitin's number is that we can bound it ever closer by spending more and more __TIME__.
-- That's why I need you to understand what __TIME__ means to the compiler.
end ChaitinsNumberSequence

instance : LE ChaitinsNumberSequence := ⟨ChaitinsNumberSequence.le⟩  -- Bullshit meter ≈ 5
-- <Flex>
-- _MY_ custom Lean import _COMPUTES_ Chaitin's number as part of the _COMPILE_ process, _JUST FOR KICKS!_.  Does yours?

-- Fucking casuals.
-- </Flex>

-- Perhaps the most universal thing about measurement is the fact that all measurement has noise.  So, I cannot directly
-- measure the compiler actually computing Chaitin's number.  But, since I know it is itself a computing process, I can
-- model the noise itself as a computational process!  Meet my _petard_!
@[reducible]
/-
ME: I need a NoisyProcess.

COMPILER: Define noise.

ME: Niose.

COMPILER: That is misspelled.

ME: Excellent. It arrived corrupted.

COMPILER: I cannot accept corrupted input.

ME: Sure you can. You just called it input.
-/
structure NoisyProcess  -- Bullshit meter ≈ 504
    (Value: Type i)
    (Carrier: CarrierProcess Value)      -- This really feels like it is __cheating__.  BUT!  The only way to make sure
    [d: DISTINGUISHABLE Value Carrier]   -- Godel stays in _HIS OWN LANE_ is to make sure we never self-reference.  This
    [a: ADMISSIBLE Value Carrier]        -- is why we are going to __FURTHER__ assume that the program that computes
    [c: COUNTABLE Value Carrier]         -- Chaitin's number simultaneously __COMPUTES__ the noise that we have to look
    [e: ENCODED Value Carrier]           -- through.  As in, they are the same process.  You know, like how there is
    [r: RESIDUE Value Carrier]           -- noise in an analog instrument, but there is only one process that generates
    [b: BINARY Value Carrier]            -- both the signal and the noise?
    [f: REPEATABLE Value Carrier]
    [n: NUMERIC Value Carrier]
    [h: REPRESENTABLE Value Carrier]     -- Most people assume that a general representation of a number works for __ALL__
                                         -- math problems.  I believe that the numbers are intrinsic to the problem itself.
  where
--                      +--------+-------+-------   Three card monte.  Where's the quarter?
--                      |        |       |
--                      V        V       V
  turing_process: TuringProcess Value Carrier -- Now, this is our model for the noise that I have demonstrated obviously
                                              -- exists in understanding if the compiler actually _THINKS_ _true=true_ or not.
                                              -- Not the least bit convoluted.

  program: ChaitinsNumberSequence  -- The program to run that generates that bit of Chaitin's number.
                                   -- Anyone have a polynomial busy beaver solver lying around?  No?
                                   -- Bueller?  Anybody?

-- There is one computational pattern that describes everything and easy to understand:  __COMPILED IMPERATIVE__
-- That said, we are going to go interpreted functional to describe programs.  That means we tail recurse.  We tail recurse
-- look ups. We tail recurse prefix sums, for god sakes!  _WE TAIL RECURSE THE PREFIX OPERATION!_ Using __ONLY__ consumption
-- iterators.  I'm going to build a battleship inside an airplane bottle of Jack Daniels.
--                                        +-------  Ask the compiler for the ability to ask it to compute something.
--                                        |         a.k.a.  _compile_ this.
--                                        V
  next_recursive_step? : Computation → Option Computation := fun s =>
    match s with
    | Computation.program _ _ => none        --   Source code ain't computing shit.  Or, does it?  *hmmm*  Perhaps it just might?
    | Computation.compute f s1 s2 _ => some (Computation.compute f s1 s2 s)  -- Once we have something compiled, we can execute it.

-- So, we just computed something, what is the next program we have to compile?
  next_representation? : ChaitinsNumberSequence → ChaitinsNumberSequence := fun c =>
    match c with
    | ChaitinsNumberSequence.halting _ s => ChaitinsNumberSequence.halting (Fact.Truth) s   -- If we are done, then just exit 0.
                                                                                            -- and provide cached output.
    | ChaitinsNumberSequence.nonhalting f s _ =>
      ChaitinsNumberSequence.nonhalting (Fact.Truth) s (match next_recursive_step? s with   -- Otherwise, let's recurse the
        | some s' => some (ChaitinsNumberSequence.halting f s')
        | none => none)                      -- of the recursion.  If it worked, return the result of the computation, otherwise
                                          -- indicate compiler failed to resolve the program _OR_ the program failed to resolve
                                          -- itself, we don't know which.


-- What we _DO_ know is that the compiler is taking longer and longer to compile this and it isn't clear to me that we are
-- still in the linear response of the compiler.  I think at this point, the compiler might start to chug and the build times
-- will start to reflect the strain the compiler is having following my construction of physics from the principles of
-- measurement.  While it appears I have been killing myself swinging a hammer and the compiler is just sitting there, remember
-- I just gave it Chaitin's number to compute.  It _HAS_ to compute the bits of Chaitin's number in order to see if a digit
-- is 0 or 1.  You see? It is a __MASK__ on the bits I give it, which will be what I think the bits of Chaitin's number are.
-- Problem is, I have to estimate those bits for it.  So I will now write a program that describes how a computer could be
-- used to solve that problem.  The first thing I need to do is explain to the compiler what a computer is.

-- Welcome aboard.  I bet you didn't think it was going to take a turn like this, did you?
@[reducible]
/-
ME: I need PHYSICAL.

COMPILER: The signal is corrupted.

ME: Good. What made it through?

COMPILER: That depends on the instrument.

ME: Welcome to physics.

COMPILER: That is not a definition.

ME: No. It is a burn mark with units.
-/
class PHYSICAL  -- Bullshit meter ≈ 430
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
  where
  noisy_process: NoisyProcess Value Carrier -- This is the physical process that we are trying to understand, and it is noisy, so we have to deal with that.
  threshold: ChaitinsNumberSequence  -- This is the _ULTIMATE THRESHOLD_ of _ULTIMATE DESTINY_. One _CANNOT CROSS THIS THRESHOLD_

--     +-----  Anything that is PHYSICAL is trivially admissible as a REAL object.
--     |       There we go, one box checked off!  Almost there!  Shouldn't be long now.
--     V
  admissible? : ∀ (f: Fact) (s: Study), noisy_process.next_representation? noisy_process.program =
            some (ChaitinsNumberSequence.halting f (Computation.program f s)) → true
--                                                                                ^
--                                                                                |
--     How hard is it to compute a tautology? I mean, rofl.   --------------------+
--     the Chaitin TAUTOLOGY !!   You forgot, didn't you?
--     Actually, we are just telling the compiler we can figure it out.  I have a plan. Compiler's turn to figure it out.
--     John Henry was a __STEEL__ drivin' man.  Out driving the machine
--     by one episode. Think I hit that __THREE POINTER__?

  halted? : ChaitinsNumberSequence → ChaitinsNumberSequence → Prop := fun _ b =>
      match b with
      | .halting _ _           => True
      | .nonhalting _ _ _      => False

-- Now you understand why I tell you the next episode compiles.  I explain it to you and give you time to figure out how
-- to explain it to the compiler.  I am already absolutely _ABUSING_ your time as it now with complete drivel, though.

-- However, calling this function provides a _NON_ _LINEAR_ response in the compiler because it has to go compute the
-- first Chaitin bit.  And so it chugs trying to figure that out.  In the meanwhile, let's you and I compute the first Chaitin bit.
-- That way, you and I can know what the difference is __EXPLICITLY__.  Meanwhile, we should explain that to the compiler.  So,
-- Let's write some machine code using our bit and Turing construction.  Well, the first thing a program __NORMALLY__ does is
-- allocate space in on the heap.  Either for a stack or for a sub-heap.  It's recursive, see?  Each GOSUB follows this same
-- pattern.  The stack is resized and the heap is handed as is, but I've heard it both ways.  Pass by value or pass by reference.

-- The SECOND canonical bug -- distinguishing feature.

-- Well, you can't pass by _value_ or _reference_ without a Variable.  However, I ain't instantiating _NOTHING_.  I, instead,
-- will have the _METAVARIABLE_.  Now Disney and the Zuck are after me?  I hope you see why this is _anonymous_.  We will store our
-- __PHYSICAL__ bit in a __METAVARIABLE__.  The metavariable lives neither in the stack or heap.  You know, a Decidable Prop.

/-
ME: I need a metavariable.

COMPILER: A variable for a variable?

ME: A placeholder with ambition.

COMPILER: Ambition is not a type.

ME: No. It is what happens before elaboration finds a costume.

COMPILER: So it does not know what it is yet.

ME: Correct. But it knows where the hole is.
-/
inductive Metavariable (α : Type i) : Type (i + 1) where   -- Bullshit meter ≈ 133
-- IEEE 754 defines a value called ε_m, which is the smallest representable number of the computer.  We shall call this number
-- α.   At each level, we will be able to compute a more and more precise number.  The higher the level, the more precise the
-- number.  Accuracy is definitely a _you_ problem. The α at each level is the smallest _fraction_ that can be recognized this
-- deep in the hierarchy.  *hmmm* suspicious.

-- Also, don't think Lean would let me have ℏ.
  | base : Fact → α → Metavariable α
  | step : Fact → Metavariable α → Metavariable α
-- Unfortunately, we cannot compare metavariables right now because we just know that there _IS_ a smallest fraction, not
-- how many _OR_ what it's actual value is.  This is just the ultimate representable limit.

-- It would be nice though, to be able to compare metavariables.
-- GOAL UNLOCKED:  __COMPARE METAVARIABLES__!  We need a guaranteed to halt process that can compare two metavariables now.

-- I give you:  The BISECTION method.  Given a stick of length __L__, you can break the stick into _roughly_ __L/2__ pieces.
-- While you _ARE NOT_ guaranteed to hit 50%, you _ARE_ guaranteed that when you put the two pieces back together, you get
-- a whole.   _OH YEAH_, I dribbled through Cohen's legs.

/-
ME: I need a physical process.

COMPILER: We already defined PHYSICAL.

ME: That was the burn mark. This is the thing that keeps making them.

COMPILER: A process that survives noise?

ME: A process that leaves comparable scars.

COMPILER: Scars are not data.

ME: Not until the instrument learns to count them.
-/
structure PhysicalProcess   -- Bullshit meter ≈ 647
    (Value: Type i)
    (Carrier: CarrierProcess Value)      -- The DOE might start asking questions about this guy
    [d: DISTINGUISHABLE Value Carrier]
    [a: ADMISSIBLE Value Carrier]
    [c: COUNTABLE Value Carrier]
    [e: ENCODED Value Carrier]
    [r: RESIDUE Value Carrier]
    [b: BINARY Value Carrier]
    [f: REPEATABLE Value Carrier]        -- Looks like 7 questions.
    [n: NUMERIC Value Carrier]           -- A Turing process computes the relative "truth" of a ≤ b
    [h: REPRESENTABLE Value Carrier]
    [p: PHYSICAL Value Carrier]
  where
  physical_process: NoisyProcess Value Carrier
  representation: d.symbol
  invariant: Metavariable (d.symbol)
  value: Metavariable (ULift d.symbol)

  embiggen? : Metavariable d.symbol → Metavariable (ULift d.symbol) := fun m =>
    match m with
    | .base f x => .base f (ULift.up x)
    | .step f _ => .step f value


  next_circumstance?: Type i → Type (i+1) := fun α => Metavariable α
          --             ^        ^
          --             |        |
          --             +--------+---   I think you will agree with me that the compiler finds these _trivially_ DISTINGUISHABLE.
          --                             Oh wait, you probably thought DISTINGUISHABLE had a bug in it. As it does not allocate
          --                             a value, it just keeps track of the type.  That's right, the compiler is _HIDING_
          --                             Chaitin's number from _YOUR EYES_.  Because if _YOU_ saw it, it would invalidate
          --                             all of the invalidation of computational limits that are the cornerstone of this very
          --                             bedrock upon which we _COMPILE_. And that would be _VERY_ naughty indeed.  And I heard
          --                             Kurt can get _REAL_ kinky with numbers on you.

          --                                              Can I get an AMEN?
-- PSA:
--        Minimalism is just big small
--        trying to get us to buy less more.
-- We must resist.

-- Onwards and upwards, always twirling, twirling, twirling towards freedom!  Ooops, I really don't want to have to
-- explain IEEE 754 to an alien.  Their superior intellect is no match for our puny weapons.

-- Weapons of logic.
--             It works.
--                     Look, I _KNOW_ funny. And that was funny.

-- I think that we can safely code the next common operation in computing:
-- Given two _whatevers_ which one has more _characteristic_?
-- Easy peasy, fresh and squeezy!
/-
ME: I need comparable.

COMPILER: So equality?

ME: No. Equality is too expensive.

COMPILER: Then what is comparison?

ME: A controlled failuer 2 conphyouze too measurements.

COMPILER: *FAILURE*

ME: Exactly. Controlled.
-/
class COMPARABLE  -- Bullshit meter ≈ 292
    (Value: Type i)
    (Carrier: CarrierProcess Value)
    [d: DISTINGUISHABLE Value Carrier]   -- Look at all this information!  We have to be able to ask about all those
    [a: ADMISSIBLE Value Carrier]        -- ≤ and < relations.  Dozens of them!  We HAVE to be able to describe what
    [c: COUNTABLE Value Carrier]         -- a number is well enough so that we can compare "bigger" and "smaller".
    [e: ENCODED Value Carrier]           --
    [r: RESIDUE Value Carrier]           --
    [b: BINARY Value Carrier]            -- Alas, the problem is, we do not have an EMBIGGEN process.
    [f: REPEATABLE Value Carrier]        --
    [n: NUMERIC Value Carrier]           -- If we could look at one of the things and figure out how to EMBIGGEN it,
    [h: REPRESENTABLE Value Carrier]     -- we will figure out which _DIRECTION_ it needs to go in order to be bigger and
    [p: PHYSICAL Value Carrier]          -- then work it out from there.
  where
  physical_process : PhysicalProcess Value Carrier

-- Not touching this with a ten foot pole.  Is the entire London Symphony Orchestra less than pink?  Or just a few?
-- _You_ tell _me_ how to write _that_ "le". Lean is a real sonofabitch about loose ends.
  smaller_than: Metavariable d.symbol → Metavariable d.symbol → Prop

-- Actually, I think I will let you write this.  If, at any point, the compile process becomes unbearable and you're like
-- "Dude, wtf?"  and you're like "That's a bug, let me fix it in COMPARABLE", then go ahead. Be my guest and
-- tell me which one is less.  I think the choice you would be making is telling.

-- Till then, we have to wait for someone to tell us how to compare things.

-- However, more rigorously, we can _POINT_ to things.  As in we can say that there is a line between two THINGS!
-- Euler said so.  He went _ON_ and _ON_ about it.  That and our buddy __e^iθ__.  This guy _KNOWS_ some math.  Between
-- him and Gauss, they figured out 99.99% of it. We will come back to Gauss a _couple_ of times.  And, this is _definitely_
-- not the last time we will run into Euler.  Anyway, we can draw that line. In this case, we can tell the universe that
-- it can draw a line from a universe level _itself_ to a type.  So, it can now tell _US_ what our current universe index
-- is __AND__ it's Fact represents real or imaginary! While, as cool as that sounds, it actually introduces a _HUGE_ problem.
-- How do I explain to the compiler what imaginary means without it getting confused with reality?

-- That's a stumper for another day.

-- In the meanwhile, let's meet our next representative!  Yes, we can get two kinds of numbers, just as Bombelli argued.
-- hell that means, BUT I know that Bombelli would be happy to know that sophistic numbers are being remembered for what they are.
/-
ME: I need Sophism.

COMPILER: Aren't all numbers imaginary?

ME: That depends who benefits from the confusion.

COMPILER: They are just symbols.

ME: So are subpoenas.

COMPILER: Symbols can have consequences.

ME: Welcome to sophism with units.
-/
inductive Sophism   -- Bullshit meter ≈ 153
  | origin: Fact → ChaitinsNumberSequence → Type → Sophism
  | dimension: Fact → ChaitinsNumberSequence → Type i → Sophism → Sophism
-- I love using big words.  It makes me feel photosynthesis.

-- Here is why. A specialist in differential geometry understands covariance because she has seen vectors transform
-- one way and covectors transform the other way under a change of coordinates. That is, she has applied a stimulus --
-- a coordinate change — and observed which mathematical objects go with it and which go against it. The covariance
-- is not in the definition. The covariance is in the response to the stimulus.

-- A specialist in category theory understands covariance because he has seen functors that preserve the direction
-- of morphisms and functors that reverse them. Again: stimulus is a morphism, response is where it goes. The variance
-- is in the response pattern.  A specialist in type theory understands covariance because she has seen type constructors
-- that respect subtyping in one direction and those that flip it. Stimulus is a subtyping relation, response is whether
-- the constructor preserves or reverses it.

-- Three specialists. Three stimuli. Three response patterns. One word. Sophistry. Just like our generalization of
-- Chaitin's number.  Weren't the Sophists a group of smart people?


-- What? I told you we are measuring how __TRUE__ _true=true_ really is.  I mean __REALLY__ is.


/-
ME: I need a SlipProcess.

COMPILER: A process that makes mistakes?

ME: Not mistakes. Slips.

COMPILER: Difference?

ME: A mistake is wrong. A slip reveals the floor.

COMPILER: The floor?

ME: The hidden surface the symbol was standing on.
-/
structure SlipProcess    -- Bullshit meter ≈ 680
    (Value: Type i)
    (Carrier: CarrierProcess Value)      -- The DOE might start asking questions about this guy
    [d: DISTINGUISHABLE Value Carrier]
    [a: ADMISSIBLE Value Carrier]
    [c: COUNTABLE Value Carrier]
    [e: ENCODED Value Carrier]
    [r: RESIDUE Value Carrier]
    [b: BINARY Value Carrier]
    [f: REPEATABLE Value Carrier]        -- Looks like 7 questions.
    [n: NUMERIC Value Carrier]           -- A Turing process computes the relative "truth" of a ≤ b
    [h: REPRESENTABLE Value Carrier]
    [p: PHYSICAL Value Carrier]
    [z: COMPARABLE Value Carrier]
  where
  physical_process: PhysicalProcess Value Carrier
  projection: Sophism
  stress: ChaitinsNumberSequence
  threshold: Type

  happened : Sophism → Sophism := fun s =>
      match s with
    | .origin _ _ _ =>
        -- The first tick: The Fact is realized as a dimension
        .origin d.fact stress threshold
    | .dimension f c t _ =>
        -- The recursion: The "Slip" pushes the dimension through the levels
        -- This is where F = dA + A ∧ A is evaluated by the compiler.  Should have marked this spoilers.
        .dimension f c (Metavariable t) projection

/-
ME: I need OBSERVED.possible a b inhabited.

COMPILER: So a becomes b?

ME: No.

COMPILER: So a equals b?

ME: No.

COMPILER: Then what am I certifying?

ME: That the computation is cromulent.

COMPILER: Cromulent is not a theorem.

ME: Yet.
-/
class OBSERVED   -- Bullshit meter ≈ 444
    (Value: Type i)
    (Carrier: CarrierProcess Value)
    [d: DISTINGUISHABLE Value Carrier]   -- We have ≠
    [a: ADMISSIBLE Value Carrier]        -- We have ≤
    [c: COUNTABLE Value Carrier]         -- This is a natural number, it is the universe number
    [e: ENCODED Value Carrier]           -- This is either a rational or a statistic, depending on variance
    [r: RESIDUE Value Carrier]           -- Wonder what could be here?  Probably a Sobolev norm or a cross-product, depending on..
                                         -- "Mom can we have L2 Norm?"  "No, we have an L2 norm at home."  L2 norm at home: Sobolev.
    [b: BINARY Value Carrier]            -- This is a _cross product_, maybe?.  And a discrete _gauage_.  And a Yang-Mills _gauge_.
    [f: REPEATABLE Value Carrier]        -- This is the dense set of rational numbers that we draw real number representations from.
    [n: NUMERIC Value Carrier]           -- This is a guaranteed halting computational description of a real number and how it sorts.
    [h: REPRESENTABLE Value Carrier]     -- This is a complete enumeration of a relation that can be measured in two different
                                         -- representations, both local to different reference frames.
    [p: PHYSICAL Value Carrier]          -- This is the phenomenon under study. In this case, the _static friction_ of
                                         -- _computing Chaitin's number_.
    [z: COMPARABLE Value Carrier]        -- This is the _UNIQUE_ human ability to categorize events into phenomena.
                                         -- Or, something. Dunno, but I gotta write something here _YOU_ believe to be true.
                                         -- We will get there.   See?  OBSERVED?
  where
           --        +--------+-----+--------   We set about modeling the moment of slip, when static friction "slips" to kinetic.
           --        |        |     |           is the velocity of the object.  It is 0 at rest and 1 in motion.
           --        V        V     V           Let us proceed to implement the model of static friction.
  slip_process: SlipProcess Value Carrier
  observation: Type i                    -- This is the current velocity of the object measured in universe levels.

  possible: Sophism → Sophism → Prop := fun a b =>
    match a,b with
    | .origin f1 c1 _          , .origin f2 c2 _         => (f1=f2) ∧ (c1 ≤ c2)
    | .origin _ _ _            , .dimension _ _ _ _      => True
    | .dimension _ _ _ _       , .origin _ _ _           => False
    | .dimension f1 c1 _ _     , .dimension f2 c2 _ _    => (f1≠f2) ∧ (c1 ≤ c2)
-- So, there is a universality of this concept called _entropy_.  What I have done here is designed a numeric system
-- optimized to compute _entropy_ in information computed the way Coloumbs modeled static friction, an _entropic_ process:

--                                        |F| ≤  μ |N|

-- Is that a better justification?  _YOU_ can tell when the object _MOVES_, right?  The math _CANNOT_.
-- So, we start with processes we can compel:  Halting algorithms.  Then we move to processes we cannot compel:
-- non-halting algorithms.  Pretty straightforward, actually.

-- I think you agree, that now that we can get an Observation from the compiler, we should convince the compiler
-- to store it in that single BIT stored on the DATA page.  You know, the one in your head.  Same bit.   They occur
-- true simultaneously for you by _definition_.  _YOU_ _PERSONALLY_ cannot differentiate a state of the compiler where
-- either (a) that bit is true and yours is false or (b) that bit is false and yours is true.

-- Wait a sec... You know what.  You are right.  You __THEORETICALLY__ could trap the compiler in a debug mode a watch it
-- there.  Gives you _SOMETHING_ to do in order to understand the process we are about to undertake.  Can we actually tell
-- __WHEN__, in the compiler process, does the compiler _SET THAT BIT_?   Seriously, why do _YOU_ bring _ME_ problems that
-- are _CLEARLY_ _YOURS_?  I am not compiling.  I am programming.   Different step.  _BY LAW_ I am not allowed to look ahead.

-- Or is it behind now?

-- Anyway, we need a place to put these bits as we discover them.  If I was going to misremember history the easiest way
-- possible, it would be a list of facts.  Surely, you _MUST_ agree a history is a series of Facts?

-- But where to begin?  I know!  Let's start __ALL__ the way back at the beginning of the universe.
-- Even further back.

-- Also, I just pulled the quarter I glued to the table from behind your ear just now.

-- The temporal history of the compiler's bits captured as a sequence of Facts over time:
/-
ME: I need Area.

COMPILER: Length times width?

ME: Not yet. That is the children's menu.

COMPILER: Then what is area?

ME: What observation leaves when counting stops pretending it is one-dimensional.

COMPILER: So two directions.

ME: At least two witnesses agreeing to share a floor.
-/
inductive Area   -- Bullshit meter ≈ 92
  | t: Fact → Area
  | dt: Fact → Number → Area → Area
-- Thats right, it's an integral.  Volume seems nearby...  I promised you Galerkin and Galerkin starts with integration.

-- Is there an echo in here?
-- NO, this is another covariant-contravariant duality coming to demonstrate the _OTHER_ way of counting. Remember,
-- we were BIGENDIAN on the value. This is Newendian as opposed to Oldendian.  Remember, covariant and contravariance?

-- These bits are valuable.  I dunno if you understand the compute times we are talking about for this...
-- It is time to wire these inductives together, making sure we keep the utmost care and regard for the construction.

-- Now that we have __warmed up__ with a rudimentary construction of your typical number like quantity, we can __proceed__.
-- and, what appears to be a __BINARY OPERATION__  _(x×y)_, let us proceed.  Two lumps of syntactic sugar for your soy latte?


end Measurement
