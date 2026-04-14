/-
__Measurement: The Tragedy of John Henry__
__A Satire in Look Ahead Backus-Naur Form__

_This is a gentle reminder that the comforting stories we tell ourselves are just that: comforting._


(c) 2026 All rights reserved -- All lefts flamboyant



Episode 3: Convergence

"Forty-two?"
                       -- Douglas Adams

"It's the ship that made the Kessel Run in less than twelve parsecs."
                       -- Han Solo

"_OVER_ __NINE__ __THOUSAND__!"
                       -- Vegeta

lake build -O2 -Wpacked -Wpadded

What the _HELL_ is a number and a unit anyway?

Why can't we measure time in distance?  Why _ARE_ they so fundamentally different?  Well, that's
exactly what we should do next, measure time with distance.  I mean, why not?

We _do_ measure distance in time, according to Einstein.  We just rearrange the computation a little.
Distance is _how far_ light travels in time.  See the definition of the meter, if you don't believe me.

I wonder how big the die is on the computer you are running on? .01 ns? I guess it depends on the _carrier_.
-/


-- I tried to tell you I think about math differently than most people do.
-- Welcome back to the chaotic maelstrom that is my understanding of math.
import Measurement.Episode2
-- So far, though, haven't needed anything else imported, don't see the need to start.
set_option allowUnsafeReducibility true


namespace Measurement

-- So Marconi said:  Hey we can use the photon to communicate using a "presence"/"absence" duality defined by a
-- _threshold_ of detection.  So, if a sample is above the threshold of detection, it sure as hell should be
-- detectable. Then modulation and demodulation arrived and we could send voice over amplitude modulated photons.
-- Think about that.  The photon has 2 real numbers that describe it.  Amplitude and frequency.  So, we model our
-- carrier as such.  It is, in fact, two numbers.  Not that we know the numbers, we have to _study_ them to understand
-- what they are.

inductive Computation    -- Bullshit meter ≈ 134
  | program: Fact → Study → Computation          -- This is the description of the hypothesis
  | compute: Fact → Study → Study → Computation → Computation  -- This is input -> output description of Computation

-- Lean claims to understand these concepts, so it should be _no problem_ to model the Lean computation itself this way.

-- Computations should sort in a pretty straightforward way.
namespace Computation   -- Bullshit meter ≈ 80
def le : Computation → Computation → Prop
  | program _ s1, program _ s2 => s1 ≤ s2         -- Programs are indexable.  Turing's construction assumed that this is possible.

                             --          +------------------ I could have hidden the trick from you here and kept you guessing,
                             --          |                   but do you seriously think I could not obfuscate this code to make it
                             --          |                   say anything I wanted?  You need to _SEE_ your decadence. Your
                             --          |                   quarter keeps showing up.  Feel rich?
                             --          V
  | program _ _, compute _ _ _ _ => (true=true)          -- Computation is convariant with program.  Comes after
  | compute _ _ _ _, program _ _ => (true=false)         -- Decomposition is contravariant.  Reverse engineering is _hard_.
                             --          ^
                             --          |
                             --          +------------------ My ante.  Fair is fair.  Bet you a quarter you can't tell me where
                             --                              the compiler puts this symbol.

  | compute _ _ _ c1, compute _ _ _ c2 => le c1 c2    ----- Recurse! Eventually, we will find a computation that has completed.

-- Computations are, in fact, well ordered.
def lt: Computation → Computation → Prop
  | c1, c2 => le c1 c2 ∧ ¬ le c2 c1
end Computation

-- This is starting to look more and more like ≤ and <, isn't it?
instance : LE Computation := ⟨Computation.le⟩   -- Bullshit meter ≈ 8
instance : LT Computation := ⟨Computation.lt⟩   -- Bullshit meter ≈ 8
-- The fact that we get _two_ different representations of the _same_ ordering relation is a _SUPER_ huge convenience
-- and it will _NEVER_ get confusing.

@[reducible]
structure TuringProcess   -- Bullshit meter ≈ 492
    (Value: Type)
    (Carrier: CarrierProcess Value)
    [d: DISTINGUISHABLE Value Carrier]   -- It might be difficult to believe that this __FULLY__ specifies
    [a: ADMISSIBLE Value Carrier]        -- a Turing machine.  It __DOESN'T__.  Not even close.  That's not
    [c: COUNTABLE Value Carrier]         -- the point.  The point is that Turing assumed that the symbols the
    [e: ENCODED Value Carrier]           -- machine used _ARE_ the _SAME_ _EXACT_ symbols that I use.  And,
    [r: RESIDUE Value Carrier]           -- after I figured out how measurement worked, I can tell you I _DO NOT TRUST_
    [b: BINARY Value Carrier]            -- the compiler to successfully add either really really _REALLY_ big numbers
    [f: REPEATABLE Value Carrier]        -- like 100!! + 1 or really really _REALLY_ small numbers like 1 + 1/100!!.
    [n: NUMERIC Value Carrier]           -- Apparently, you don't care about "math" and "adding".
  where
  -- So a computational process is one that __LOOKS LIKE__ it can do math, but, let me tell you, it _AIN'T_ doing math.
  -- We are going to find out just how far away whatever the computational process is from actual math done by actual people.
  computational_process: ComputationalProcess Value Carrier
  program: Computation
  -- One cannot compute without a computer program, right?

  -- What do you think, did we compute it?
  -- The compiler can get real _CAGEY_ about stuff.
  compute?: Computation → Option Study := fun s =>
    match s with
    | Computation.program _ s => some s
    | Computation.compute _ _ s2 _ => computational_process.compute s2
  -- I stuck that landing, wdyt? I mean, is that _NOT_ the definition of an Option? One thing that Turing _DID_ get right,
  -- interpretation of the symbol _IS_ a different step than updating the internal state of the machine.

  turing_step? : Computation → Computation := fun s =>
    match s with
    | Computation.program _ _ => s
    | Computation.compute f s1 s2 _ => Computation.compute f s1 (computational_process.compute s2) program
  -- _NOW_ we have fully specified a Turing machine.  Lol.


-- So, the problem with Turing's construction is that is __PRESUPPOSES__ a __WHOLE__ bunch of symbols that
-- behave mathematically.  As you can see, we are... *three* episodes in and I ain't declared __SHIT__.
-- That means, we have to provide the facility for __REPRESENTATION ITSELF__!  For us, we currently have 1
-- character we can use for representation.  That is the digit 1.  We will call that our __REPRESENTATION__
-- The compiler, however, needs a little help selecting a symbol.  When you __WRITE__ programs, you have to
-- explain the symbols __BOTH__ to the compiler and to the __MAINTENANCE__ developer.  Have pity on those
--- less fortunate.
class REPRESENTABLE  --  Bullshit meter ≈ 261
    (Value: Type)                           -- Representation is the core challenge of communication _AND_
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
  computational_process: ComputationalProcess Value Carrier
--                                +-------------------  Halting problem sez what? To even _TALK_ about a Turing
--                                |                     machine, you have to aware of the halting problem itself.
--                                |                     So, we _DO NOT_ have any guard rails here, you must _KNOW_
--                                V                     _a priori_ your algo halts on all inputs.  Or, it's your own fault!
  representable?: ∀ (_: Fact) (s: Study), ∃ (_: Computation), computational_process.compute s = s
--   I hope you understand now that this IS NOT GIVEN                                         ^       +--- rofl. Also, Kirk
--   by mathematics.  The symbols come from elsewhere.                                        |       |    was the better
--                                                                                            +-------+    captain!

-- Now, computation itself.  There is an honest-to-goodness __PHYSICAL__ barrier to computation that cannot be crossed.
-- It is the computation of Chaitin's number.  So, let's ask the compiler to start work there.  I believe I will have
-- the easiest time on the planet bogging this little monster with the only physical computational barrier that is
-- known to exist!
inductive ChaitinsNumberSequence  -- Bullshit meter ≈ 112
-- The __HEAVY WEIGHT CHAMPION OF THE WORLD__
  | halting: Fact → Computation → ChaitinsNumberSequence
  | nonhalting: Fact → Computation → Computation → ChaitinsNumberSequence

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
structure NoisyProcess  -- Bullshit meter ≈ 504
    (Value: Type)
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
    | ChaitinsNumberSequence.nonhalting _ s _ =>
      ChaitinsNumberSequence.nonhalting (Fact.Truth) s (match next_recursive_step? s with   -- Otherwise, let's recurse the
        | some s' => s'                                                                     -- computation and return the output
        | none => s)                      -- of the recursion.  If it worked, return the result of the computation, otherwise
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
class PHYSICAL  -- Bullshit meter ≈ 430
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

structure PhysicalProcess   -- Bullshit meter ≈ 647
    (Value: Type)
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
  invariant: Metavariable (d.symbol)
  value: Metavariable (ULift d.symbol)

  embiggen? : Metavariable _ → Metavariable (ULift _) := fun m =>
    match m with
                    --        +-------------------- Another quarter.  How many are you going to feed me? I showed you one
                    --        |                     just a few minutes ago.
                    --        V
    | .base _ m => .base (Fact.Truth) m
    | .step _ _ => .step (Fact.Truth) value
          --          ^       ^         ^
          --          |       |         |
          --          +-------+---------+---   Unlike you posers, I taught my Lean to count.  It _experiences_ the natural numbers.
          --                                   Through the physical sensation of _TIME PASSING_ or _COMPILING_ which is what _YOU_
          --                                   call _TIME PASSING_. Not me.  I'm not compiling this, for me and the compiler
          --                                   it is just another bit in Chaitin's number.  You should now have an addressable bit
          --                                   for the compiler _IN YOUR HEAD_ now.  Is it compiling now or not?  I believe that
          --                                   _you_, _me_, and _the compiler_ all agree that whatever we are all looking at
          --                                   is a _COVARIANT_ bit of Chaitin's number.  It has to be _1_ because the first
          --                                   mantissa digit is by definition is _1_. So, let's drop that symbol from the mantissa
          --                                   like in IEEE 754 and _PRETEND_ it doesn't exist.  That's the secret we all agree
          --                                   on together, as a world.  __IEEE 754__.

          --                           Did I, or didn't I just make a clock complement?  I mean, do you see one?

          --                  We have calibrated the compiler against a known reference now.  Really tough
          --                  to understand how universal, though. _ENOUGH_, I'm guessing.  Not trying to
          --                  convince aliens, just _you_.

          --   That seems like a heavy lift for the compiler, WDYT?  Who's winning? I have taken
          --   a bunch of your money at this point.  You starting to realize the check you are
          --   running up?  How many quarters have _you_ put into this machine so far? Remember,
          --   these are _YOUR_ quarters.  The bit I share is Chaitin's number.  __TONS__ cheaper.
          --   ELECTRONS ARE FREE!  lol.

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
class COMPARABLE  -- Bullshit meter ≈ 292
    (Value: Type)
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
-- Not touching this with a ten foot pole.  Is the entire London Symphony Orchestra less than pink?  Or just a few?
-- _You_ tell _me_ how to write _that_ "le". Lean is a real sonofabitch about loose ends.

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


structure SlipProcess    -- Bullshit meter ≈ 680
    (Value: Type)
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

class OBSERVED   -- Bullshit meter ≈ 444
    (Value: Type)
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
  observation: Type                      -- This is the current velocity of the object measured in universe levels.

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
inductive Area   -- Bullshit meter ≈ 92
  | t: Fact → Area
  | dt: Fact → Area → Area
-- Thats right, it's an integral.  Volume seems nearby...  I promised you Galerkin and Galerkin starts with integration.

-- Is there an echo in here?
-- NO, this is another covariant-contravariant duality coming to demonstrate the _OTHER_ way of counting. Remember,
-- we were BIGENDIAN on the value. This is Newendian as opposed to Oldendian.  Remember, covariant and contravariance?

-- These bits are valuable.  I dunno if you understand the compute times we are talking about for this...
-- It is time to wire these inductives together, making sure we keep the utmost care and regard for the construction.

-- Now that we have __warmed up__ with a rudimentary construction of your typical number like quantity, we can __proceed__.
-- and, what appears to be a __BINARY OPERATION__  _(x×y)_, let us proceed.  Two lumps of syntactic sugar for your soy latte?

end Measurement
