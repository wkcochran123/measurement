/-
__Measurement: The Tragedy of John Henry__
__A Satire in Backus-Naur Form__

_This is a gentle reminder that the convergent stories we tell ourselves are just that: stories._


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


namespace Measurement

-- So Marconi said:  Hey we can use the photon to communicate using a "presence"/"absence" duality defined by a
-- _threshold_ of detection.  So, if a sample is above the threshold of detection, it sure as hell should be
-- detectable. Then modulation and demodulation arrived and we could send voice over amplitude modulated photons.
-- Think about that.  The photon has 2 real numbers that describe it.  Amplitude and frequency.  So, we model our
-- carrier as such.  It is, in fact, two numbers.  Not that we know the numbers, we have to _study_ them to understand
-- what they are.

inductive Computation
  | program: Fact → Study → Computation          -- This is the description of the hypothesis
  | compute: Fact → Study → Study → Computation → Computation  -- This is input -> output description of Computation

-- Lean claims to understand these concepts, so it should be _no problem_ to model the Lean computation itself this way.

-- Computations should sort in a pretty straightforward way.
namespace Computation
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
instance : LE Computation := ⟨Computation.le⟩
instance : LT Computation := ⟨Computation.lt⟩

structure TuringProcess
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
  where
  computational_process: ComputationalProcess Value Carrier
  program: Computation

  -- What do you think, did we compute it?
  compute?: Computation → Option Study := fun s =>
    match s with
    | Computation.program _ s => some s
    | Computation.compute _ _ s2 _ => computational_process.compute s2


  turing_step? : Computation → Computation := fun s =>
    match s with
    | Computation.program _ _ => s
    | Computation.compute f s1 s2 _ => Computation.compute f s1 (computational_process.compute s2) program

class REPRESENTABLE
    (Value: Type)
    (Carrier: CarrierProcess Value)
    [d: DISTINGUISHABLE Value Carrier]
    [a: ADMISSIBLE Value Carrier]
    [c: COUNTABLE Value Carrier]
    [e: ENCODED Value Carrier]
    [r: RESIDUE Value Carrier]
    [b: BINARY Value Carrier]
    [f: REPEATABLE Value Carrier]
    [n: NUMERIC Value Carrier]           -- Son-of-a-gun, this is a representation of the number IMPLIED by
                                         -- the carrier... who knew?
  where
  computational_process: ComputationalProcess Value Carrier
--                                +-------------------  Halting problem sez what? To even _TALK_ about a Turing
--                                |                     machine, you have to aware of the halting problem itself.
--                                V
  representable?: ∀ (_: Fact) (s: Study), ∃ (_: Computation), computational_process.compute s = s


inductive ChaitinsNumberSequence
  | halting: Fact → Computation → ChaitinsNumberSequence
  | nonhalting: Fact → Computation → Computation → ChaitinsNumberSequence

namespace ChaitinsNumberSequence
def le : ChaitinsNumberSequence → ChaitinsNumberSequence → Prop
  | halting _ s1, halting _ s2 => s1 ≤ s2
  | halting _ _, nonhalting _ _ _ => true
  | nonhalting _ _ _, halting _ _ => false
  | nonhalting _ s1 _, nonhalting _ s2 _ => s1 ≤ s2

-- Can't compute lt.  Against the rules.
end ChaitinsNumberSequence

instance : LE ChaitinsNumberSequence := ⟨ChaitinsNumberSequence.le⟩

-- <Flex>

-- _MY_ custom Lean import _COMPUTES_ Chaitin's number as part of the _COMPILE_ process, _JUST FOR KICKS!_.  Does yours?

-- Fucking casuals.
-- XML.  The _old ways are still the best ways_.

-- </Flex>

structure NoisyProcess
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
  where
  turing_process: TuringProcess Value Carrier -- Now, this is our model for the noise that I have demonstrated obviously
                                              -- exists in understanding if the compiler actually _THINKS_ _true=true_ or not.
  program: ChaitinsNumberSequence  -- The program to run that generates that bit of Chaitin's number.

  next_recursive_step? : Computation → Option Computation := fun s =>
    match s with
    | Computation.program _ _ => none
    | Computation.compute f s1 s2 _ => some (Computation.compute f s1 s2 s)

  next_representation? : ChaitinsNumberSequence → ChaitinsNumberSequence := fun c =>
    match c with
    | ChaitinsNumberSequence.halting _ s => ChaitinsNumberSequence.halting (Fact.Truth) s
    | ChaitinsNumberSequence.nonhalting _ s _ =>
      ChaitinsNumberSequence.nonhalting (Fact.Truth) s (match next_recursive_step? s with
        | some s' => s'
        | none => s)

class PHYSICAL
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
  where
  noisy_process: NoisyProcess Value Carrier -- This is the physical process that we are trying to understand, and it is noisy, so we have to deal with that.
  threshold: ChaitinsNumberSequence  -- This is the _ULTIMATE THRESHOLD_ of _ULTIMATE DESTINY_. One _CANNOT CROSS THIS THRESHOLD_

  admissible? : ∀ (f: Fact) (s: Study), noisy_process.next_representation? noisy_process.program = some (ChaitinsNumberSequence.halting f (Computation.program f s)) → true


-- Don't think Lean would let me have ℏ.
inductive Metavariable (α : Type u) : Type (u + 1) where
  | base : Fact → α → Metavariable α
  | step : Fact → Metavariable α → Metavariable α

structure PhysicalProcess
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
          --                                   call _TIME PASSSING_. Not me.  I'm not compiling this, for me and the compiler
          --                                   it is just another bit in Chaitin's number.  You should now have an addressable bit
          --                                   for the compiler _IN YOUR HEAD_ now.  Is it compiling now or not?  I believe that
          --                                   _you_, _me_, and _the compiler_ all agree that whatever we are all looking at
          --                                   is a _COVARIANT_ bit of Chaitin's number.  It has to be _1_ because the first
          --                                   mantissa digit is by definition is _1_. So, let's drop that symbol from the mantissa
          --                                   like in IEEE 754 and _PRETEND_ it doesn't exist.  That's the secret we all agree
          --                                   on together, as a world.  __IEEE 754__.

          --                                   We have calibrated the compiler against a known reference now.  Really tough
          --                                   to understand how universal, though. _ENOUGH_, I'm guessing.  Not trying to
          --                                   convince aliens, just _you_.

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
          --                             bedrock upon which we _COMPILE_.

          --                                              Can I get an AMEN?



class COMPARABLE
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
-- Not touching this with a ten foot pole.  Is the entire London Symphony Orchestra less than pink?  _You_ tell _me_ how to write
-- _that_ "le". Lean is a real sonofabitch about loose ends.

-- Actually, I think I will let you write this.  If, at any point, this stops compiling and you're like
-- "Dude, wtf?"  and you're like "That's a bug, let me fix it in COMPARABLE", then go ahead.


inductive Projection
  | origin: Fact → ChaitinsNumberSequence → Type → Projection
  | dimension: Fact → ChaitinsNumberSequence → Type i → Projection → Projection

structure SlipProcess
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
  projection: Projection
  stress: ChaitinsNumberSequence
  threshold: Type

  happened : Projection → Projection := fun s =>
      match s with
    | .origin _ _ _ =>
        -- The first tick: The Fact is realized as a dimension
        .origin d.fact stress threshold
    | .dimension f c t _ =>
        -- The recursion: The "Slip" pushes the dimension through the levels
        -- This is where F = dA + A ∧ A is evaluated by the compiler.  Should have marked this spoilers.
        .dimension f c (Metavariable t) projection

class OBSERVED
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
    [p: PHYSICAL Value Carrier]          -- This is the phemenon under study. In this case, the _static friction_ of
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

-- Anyway, we need a place to put this bits as we discover them.  If I was going to misremember history the easiet way
-- possible, it would be a list of facts.  Surely, you _MUST_ agree a history is a series of Facts?

-- But where to begin?  I know!  Let's start __ALL__ the way back at the beginning of the universe.
-- Even further back.

-- Also, I just pulled the quarter I glued to the table from behind your ear just now.

-- The temporal history of the compiler's bits captured as a sequence of Facts over time:
inductive Area
  | t: Fact → Area
  | dt: Fact → Area → Area
-- Thats right, it's an integral.  Volume seems nearby...  I promised you Galerkin and Galerkin starts with integration.

-- Is there an echo in here?
-- NO, this is another covariant-contravariant duality coming to demonstrate the _OTHER_ way of counting. Remember,
-- we were BIGENDIAN on the value. This is Newendian as opposed to Oldendian.  Remember, convariant and contravariance?

-- These bits are valuable.  I dunno if you understand the compute times we are talking about for this...
-- It is time to wire these inductives together, making sure we keep the utmost care and regard for the construction.

-- Now that we have __warmed up__ with a rudimentary construction of your typical number like quantity, we can __proceed__.
-- and, what appears to be a __BINARY OPERATION__  _(x×y)_, let us proceed.  Two lumps of sytactic sugar for your soy latte?

end Measurement
