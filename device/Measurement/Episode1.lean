/-
__Measurement: The Tragedy of John Henry__
__A Satire in Look Ahead Backus-Naur Form__

_This is a gentle reminder that the fanciful stories we tell ourselves are just that: stories._

(c) 2026 All rights reserved -- Can you copyright an anonymous text? rofl.

-- Forward:

Dear All,

Technically, I'm dead.  But, if I were alive, it is possible that the words "This program
is truly the way forward." could have been among a _LARGE_ set of words that I was capable
of speaking.  I spoke a lot of words in only one particular order.

                                         -- Arthur C. Clarke

This is my apology to Mr. Clarke.  Any, and I mean _ANY_, advanced enough science looks like magic.

Episode 1:  Counting

"Hold on lady, we go for ride."
                    -- Short Round.

lake build --expert_mode --crash_on_everything --do_not_explain_errors

Can I do this with no imports?  Hold my beer...
-/

-- So, I have been thinking about how to measure things.  Anything.  Even the thing that is
-- doing the measuring.  While it is doing the measuring.  All the way down.  To try to give
-- you some idea of what I am talking about, I am going to try to measure how true the proposition
-- _true = true_ is. At least, insofar as Lean will me show you that this isn't nearly as set
-- in stone as you might think.

-- We are going to use the generally accepted principles of science and engineering to reverse-engineer
-- the Lean compiler itself and explicitly _measure_ how well it can evaluate _true = true_.

-- Why?  Cuz I understand math, but the way _I_ understand math is _very_ different from most people's.
-- This here lean proof assistant is designed to show me where _I_ don't understand math.  Well, I'm
-- going to show it a thing or two I have picked up over the years.

-- Man vs. Machine!
namespace Measurement

universe i -- There is only 1 universe, the one we can experience right now, at time step _i_.
           -- or, is this √-1?  i forget.

-- I have always thought that the comments of the code should tell a story.
-- The story helps the reader understand what is going on.  So, let me tell
-- you a story about measurement.  Measurement begins with _facts_.
-- I think you will agree it is easy to see whether or not something happened                +-------------------------------+
-- and if that something happened, that _fact_ is _true_.  Otherwise, it ain't. Clear?       |                               |
--                                             +---------------------------------------------+                               |
-- This compiles Fact and fails Number         |               This is a measurement from a device of my own design. --------+
class Fact where   -- Bullshit meter ≈ 9   <---+
  truth : Prop                 -- Did it happen or not?
  decTruth : Decidable truth   -- Sometimes the compiler will know the answer before we do!
                               -- This fucker doesn't know math, it is _PSYCHIC_! It seems to understand
                               -- what cannot be possible given the current situation _pretty_ well.
                               -- _WITCHCRAFT_ I tell you!


-- Well, let's start with the simplest of all Facts, something that is True.  Here,
-- the compiler is asked whether or not something is true.  In this way, we can
-- can measure the compiler.  Is the compiler currently bullish or bearish on
-- the veracity of _true_ = _true_?
namespace Fact    -- Bullshit meter ≈ 25
             --              +---------------------  Know where the compiler puts this?  On the DATA page.
             --              |                       This is not a variable.  It is the truth that the
             --              |                       compiler and I agree on. Don't know what that means?
             --              |                       It means that we are playing three card monte and I glued
             --              |                       the quarter to the table. Watch me _still_ take your money.
             --              V                       Without moving the first card.
def Truth : Fact := { truth := true, decTruth := Decidable.isTrue rfl }
     --                                                            ^
     --                                                            |
     --             I assume you, too, can rfl this.  rofl. -------+
end Fact
-- Thus ends the storage allocation portion of the program.  The rest of the code reorganizes this vast,
-- deep--- dare I say _BIG DATA_?!-- bit into something that might look familiar to you.

-- But before we measure, we have to deal with relative value.  I don't have time to spend _all day_
-- building you a number system from scratch, so I will just make enough of the number system to get by.

-- Well, if we are going to measure what the compiler is doing, it would help
-- if we agreed on what some numbers were.  So, let's make some and name them.  Big Endian so we
-- can shortcut a very common computation.
-- This compiles Fact and fails Number
inductive Number where   -- Bullshit meter ≈ 92
  | zero : Fact → Number
    --      ^
    --      |
    --      +--------------- 0 or 1. This is our digit. Or, rather, the clock
    --                       complement of this for those who understand DSP.
  | one  : Fact → Number → Number
    --      ^                  Apparently, this process has been well known before
    --      |                  I figured it out. Not my idea, some dude named Peano
    --      +----------------  camping at a spawn point.  Do you think we might be able
    --                         to count both ways simultaneously? Up and down?
    --                         HINT: Probably.  BTW, since I have lean below me this
    --                         is _the standard_ to which I am holding myself.  This is
    --                         _probably true_. Let's find out!  We can ask the compiler.

-- And so, we set about constructing the machinery so the compiler can, in fact answer
-- this question of can we count both ways?

-- Be patient, we have to go through Einstein field equations to get the answer, but it
-- is in there. And we will find it.  Eventually.  Eye on the prize, we just want to know
-- what this bit is.  Is it true or false?

-- Remember, this is the question I want to show you the answer to:  That the compiler
-- can do a pretty good job of evaluating how _true_ _true_ really is.   We have to derive,
-- demonstrate, and prove uniqueness of a finite solution to the Yang-Mills equations
-- in order for me to show you that this physical device before you has, as a matter of
-- fact, computed the value of this Fact. So, I am going to measure the response of the
-- compiler to determine if I agree that the compiler thinks that, in fact _true = true_.
-- We will carefully construct an instrument and stimuli for the compiler so that
-- we can measure the truthiness of any of the two symbols: true or false. We will assign
-- that truthiness a number, calibrate that number, measure it very, very, _VERY_ finely, then
-- give you error bounds on the likelihood that _true = true_.  Over/under _r²_ is .95. and I will
-- take your book.


-- In the meanwhile, the actual fact on the number can be interpreted as the sign of that number
-- That way we can use a clock complement as the fact itself. A clock?  Yeah, a clock.  It takes
-- time to compile a program and I really don't want to wait forever.

--                                         +------------------------+
namespace Number  --  Bullshit meter ≈ 112 |                        |
def le : Number → Number → Prop --         V          Now, this is just _intuition_. We need
  | .zero _ , _ => True         -- 0 ≤ n  n∈ℕ         something that might pass as a natural number.
  | .one  _ _, .zero _ => False -- n > 0  n∈ℕ > 0     Lean has the Nat thing, but I don't trust it.  Do you?
--                                         ^          You do?    Such decadence!  A HUUGE assumption..
--                                         |                        |
  | .one  p1 n1', .one  p2 n2' =>   --     +------------------------+
      match p1.decTruth, p2.decTruth with
      | isTrue _,  isTrue _  => le n1' n2' -- so, we can interpret true and false as the sign
      | isTrue _,  isFalse _ => False      -- of the values.  if true is positive, then this
      | isFalse _, isTrue _  => True       -- the truth table of <=.
      | isFalse _, isFalse _ => ¬ le n1' n2'
end Number

-- Did you catch that?  We have a different fact than the compiler.  The compiler has true and false,
-- We have at least 3 truth symbols: true=true, false=false, and true=false.  Weird.
-- A clock complement collapses the true=true and false=false into a same/different cadence.
-- Do we want to the compiler to go to 3 to match our view of the world?  Probably, but not yet.
-- This is fiveshadowing.  We don't foreshadow when we metaprogram, we fiveshadow.  Remember that
-- we have this truthiness measure because we have 3 symbols for a binary representation.
-- and we have same/different for our facts and true/false for the facts in the compiler.
-- _DON'T CROSS THE STREAMS_.  While not an unlicensed nuclear accelerator, we have to be careful
-- not to fall into a circular reasoning trap.

-- BTW, it is _not at all clear_ to me that numbers are well sorted. I mean, _i_.
-- how do you sort that?  IEEE 754 figured out that _a_ ≠ _a_ can be used to represent
-- these concepts. _NaN_.

-- I find IEEE plays it _real loose and cool_ with these definitions, so be warned.

-- Besides, pretty certain _you_ use _i_ like it is a number
-- _all the time!_  Most compilers are just too lazy to write out the COMPLETE
-- Taylor expansion e^(iθ) all the way out so we can really _understand_ _i_.
--                  ------
--                    ^
--                    |
--                    +--------------  Keep an eye on this guy. Our number looks an awful lot like this.
--                                     Hope you are up on your Cooley-Tukey.

-- Just absolute laziness.

--                             +--+----------------------------------------------------  Aaah, low entropy language,
--                             |  |                                                      could there be a better
--                             V  V                                                      medium?  No possible.
-- A more madenning question "is is" 1 <= 0.999999999.... ?  Well, as you will see
--                            ----\         ^^^^^^^^^
--  Parsing syllables             |         |||||||||
--  Slick Willy style  --------+--+         +++++++++-----------------------------------------   lol

-- I will be asking a very similar question in a second. Turns out, I've heard it
-- both ways.


-- BTW, I hope you don't mind I hijack operators for my own nefarious purposes.
-- If you forget what they mean, because hijack is really a euphemism for what
-- I'm about to do, just remember it always means "Less Than or Equal To" in whatever
-- context it is in.
instance : LE Number where  -- Bullshit meter ≈ 7
  le := Number.le
-- Trust me, ;-)

-- So, this is our "sensor" for the compiler's meaning
-- of a Type.  The compiler will happily send us carriers
-- that will evaluate true/false for us to use as "facts."
structure CarrierProcess -- Bullshit meter ≈ 85
    (Carrier: Type)
  where
  symbol: Fact      -- Said fact from the compiler, either _true_ or _false_.
  value: Number     -- The inductive number defined above.  It isn't a natural number, in that it
                    -- does not start from the empty set.  It starts from the trivial truth _true_ = _true_.
          --                                          ^
          --        My apologies for using            |
          --        such a vague descriptor. ---------+
          --        Filthy word.

  event: Number → Number := fun s =>
    match s with
    | .zero _ => .zero Fact.Truth             -- See? _true_ = _true_.  This assumes that whatever comes in is true.
    | .one  p _ => .one  p value              -- This starts to stack inductives in weirdly recursive ways.
                                              -- Also, notice that this is the canonical fence post problem.
                                              -- The next number is covered by the value now. If you hate
                                              -- fence post problems, realize that they are the first fundamental
                                              -- bug. I mean, distinguishing feature.
--                                                                 |
--        +--------------------------------------------------------+
--        |
--        V
class DISTINGUISHABLE  -- Bullshit meter ≈ 28                      You may start noticing a pattern to
    (Value: Type)                                               -- the structure -> class -> inductive ->
    (Observation: CarrierProcess Value)                         -- structure -> class -> ...
    where                                                       -- An eternal golden braid of meta-programming.
                                                                -- This argument does not exist without the
                                                                -- beauty of Hofstadter's work.

  fact: Fact           -- This is quite true as a matter of fact
                       -- Also, C++ PTSD.
                       --     DUCK::Duck duck = new DUCK::Duck() // quack!


   --       +---------------  So, generic metaprogramming.  This agrument relies _HEAVILY_ on
   --       |                 generic metaprogramming.  We are intentionally _NOT_ instantiating
   --       |                 the symbol, rather we are grabbing the label the compiler uses to
   --       |                 track universe level.  There is _no_ memory allocation so far, other
   --       |                 than Fact.Truth which is on the DATA page, not the INSTRUCTION page.
   --       |                 Don't expect to need to allocate memory.
   --       V
  symbol: Type Value   -- We can index the value with a metavariable symbol, as in
                       -- the compiler has a representation of some integer level.
                       -- Only suckers use Nat.

  distinct? : Prop := True
  different? : Type Value → Prop :=
    fun s1 => s1 ≠ symbol  -- If things are at different universe levels, then     <-------+
                           -- the compiler can easily tell the types apart.                |
                           --                                                              |
  dec_distinct : DecidablePred different?  -- And, the compiler will be good enough        |
                                           -- to tell us if it thinks the universes        |
                                           -- are different as we write the code.          |
--                                                                                         |
--                                                                                         |
-- And, since we now agree with the compiler what a natural number looks like,             |
-- lets talk about how they are structured.                                                |
--                                                                                         |
-- You didn't notice the universe number thing? -------------------------------------------+
inductive Natural  -- Bullshit meter ≈ 107
  where
  | zero : Fact → Natural                       -- The Fact here is a bit murkier, we are coordinating with
                                                -- the compiler now on what is a fact and what isn't.
                                                -- We have a notion of true and the compiler has a notion
                                                -- of true, which leads to true=true or true=false.
                                                -- See?  Or is this _straining_ your imagination?
                                                -- Or, you can just think of it as the compiler assuring
                                                -- you that, indeed, true=true.

  | number : Fact → Number → Natural → Natural  -- Here, the Fact is that we agree with the compiler that
                                                -- the universe of Number is what we call a Natural number.

-- The natural numbers have this property that the ones after are bigger than the ones before.
-- Not certain they have another property worth talking about.  If you can think of one,
-- leave it in the comments below.  It helps the algorithm.
namespace Natural   -- Bullshit meter ≈ 42     _42?!_
def le : Natural → Natural → Prop
  | .zero _ , _  => True                     -- Zero is less than or equal to everything
  | .number _ _ _ , .zero _ => False         -- Any nonzero natural is > 0.
  | .number p1 n1' _, .number p2 n2' _ =>    -- So, let's look at the values of the numbers to see.
    p1.truth = p2.truth ∧ n1' ≤ n2'          -- The case where the truths are different is handled above!
                                             -- n1' ≤ n2' is how we know that one comes before the other.

-- Let's discuss well-ordered numbers.  We all understand the definition of well ordered implies
-- the existence of a map that allows you to perform this computation on the natural numbers:
def lt: Natural → Natural → Prop := fun n1 n2 => le n1 n2 ∧ ¬ le n2 n1
-- I hope you agree it will be difficult for the us and the compiler to diverge on this definition.
-- And any time the compiler _does_ diverge from this assumption, it let's us know.

end Natural

instance : LE Natural where  -- Bullshit meter ≈ 5
  le := Natural.le

-- More notional abuse.  Won't someone think of the notation?
instance : LT Natural where  -- Bullshit meter ≈ 7
  lt := Natural.lt

-- So, you ever thought about how you count before?
-- I mean, you know how to count, but do you _really_ know how to count?
-- There are two ways to count, it turns out.  One way is to iterate,
-- as in a sequence. The other way is to decompose into similar pieces,
-- as in cardinality.  Let's tease the meanings of these two ways to
-- count apart as I think that might be important to the plot.
--
-- And you are reading this for the plot, right?
structure CountingProcess -- Bullshit meter ≈ 118
    (Value: Type)
    (Carrier: CarrierProcess Value)
    [d: DISTINGUISHABLE Value Carrier]
  where
-- Well, it turns out, To do either, you need a _carrier_.  Something
-- you can identify, classify, bin, and count.  The first three are
-- what we call decomposition.  The fourth is iteration.  This file
-- deals exclusively with iteration with the other _three_ constructions
-- to follow in later files.  So, let's just assume we can talk about
-- a carrier.  W.l.o.g., we can let a carrier be letters that we send
-- back and forth to the compiler. That's right. Snail mail.

  carrier: CarrierProcess Value -- I can taste the envelope glue already.

-- No joke, this is snail mail and can take the compiler a long time
-- to resolve arguments that are recursively enumerable.  oh well...
-- Halting problem/smalting problem. Sounds like a you-problem.
-- Actually, it is a _you_ problem.  _you_, personally, cannot devise
-- a way to short cut this.  You wait for daddy compiler. _You_, personally
-- have to _wait_.  Time has to _elapse_ for _you_.  Like on a clock, fr fr.
-- No one else has to _wait_. They can read this in a text editor and
-- just assume the compiler figures it out.  They don't have to wait.
-- You are probably wondering why I mention this.  Just planting seeds.
-- Back to the code.

-- I can easily count how many letters the compiler has sent me. I have
-- the letters and can count to potato.
  count: Natural

-- Okay, seriously, back to code. We can work with compiler to _iterate_ in a
-- send/response loop that allows us to stack inductives in a tensor
-- like way.
  iterate: Natural → Natural := fun n =>
    match n with
    | .zero _ => .zero d.fact -- Naturals need to have something factual to start from
                              -- I would prefer to avoid the empty set as
                              -- that blatantly _assumes sets exist_.  Such decadence.
                              -- Instead, we are using the fact that true = true. However,
                              -- sometimes, true = false.  Just to mix it up. I actually
                              -- don't care which world we live in, symmetric or anti-symmetric.
                              -- and neither does the compiler.

    | .number _ _ _ => .number d.fact carrier.value count
-- We can take the carrier value from the compiler and use it to count.



-- This is going to take a minute to understand.  ADMISSIBLE.  This
-- just means the compiler did not barf on a computation. In this case
-- what the compiler is doing is looking through the inductive to see
-- if it can find a counterexample to a ≤ b.
class ADMISSIBLE  -- Bullshit meter ≈ 60
    (Value: Type)
    (Carrier: CarrierProcess Value)
    [DISTINGUISHABLE Value Carrier]
    where
  counting_process : CountingProcess Value Carrier
  admissible? : Number → Number → Prop := fun stimulus threshold =>
       --     +------------- Is our first number less than
       --     |         +--- or equal to the second number?
       --     |         |
       --     V         V
    match stimulus, threshold with
    | .zero _, _ => True              -- 0 ≤ Nat.  True, true..
    | .one  _ _, .zero _ => False     -- Nat ≰ 0.  False, true..  (see, I told you false = true sometimes)
    | .one  _ n1', .one  p2 n2' =>
    --    +-------------------------- If p2 is already admissible, let it through.
    --    |          +--------------- Otherwise, only if n2' is bigger than n1'
    --    |          |
    --    V          V
      p2.truth ∨ n1' ≤ n2'   -- No lie, this is how the compiler can shortcut the ≤ computation.
  --  --------
  --     ^
  --     |                      Remember how I called this the sign?  We are currently
  --     +--------------------- asking if the value obeys our sign convention on ≤. In
  --                            which case, we already know it is different and uncounted,
  --                            and therefore counting it _embiggens_ the magnitude!


-- Now, I am invoking my _creative license_ here, kinda.  Let's talk rational
-- numbers.  Here we define rationals in a very interesting way.  Given a sequence
-- of naturals, you get.  F -> A -> A -> F -> B -> A/B -> F -> C -> C -> F -> D -> C/D -> ....
-- I could convince you that such a mapping will enumerate all rationals, but I am
-- lazy af.  Point is, all those numbers _are_ rational numbers. And we don't need
-- all of them, just a countable amount.
inductive Rational  -- Bullshit meter ≈ 107
      --     ^
      --     |
      --     +------------ This is not ℚ.  This is just an inductive structure that
      --                   is populated with symbols that represent what the compiler
      --                   might consider a rational number.  This is just a symbol for
      --                   a rational number looking thing in the compiler, not the
      --                   rational number itself.
  where
  | zero : Fact → Rational
  | number : Fact → Natural → Rational → Rational
-- Or, you can give me a counterexample.  A rational number that CANNOT be represented this way
-- and I will gladly make that the second rational in this chain. See?  You can't prove
-- me wrong. So far, compiler is buying what I'm selling.


-- So, one way to think of a rational series is as 1/2, 2/3, 3/4, 4/5, ....
-- That doesn't seem like it would cover all the rationals, and it doesn't.
-- But, you must find it hard to argue that this is _not_ a series of rational numbers
-- I think 1 - r is the interesting value here.  1/2, 1/3, 1/4, 1/5, ....
-- It is _obvious_ that this _more than adequately_ spans the rationals.
-- The threshold mention above should start to make sense.  1 is our threshold
-- And we can count our way arbitrarily close to it without keeping state.

-- And, since we haven't included any numbers from lean whatsoever, I will
-- just go ahead and assume that residue is _actually_ what is being represented.
-- And when we do math, we are just doing math on the representations.

-- Why not both? We have a truth parity we can use to decide.

-- One should be reminded of the Trumpet of Gabriel.  I'm about to Gauss's law all
-- over some musical instrument in nasty ways....  Would you like to try my Galerkin-style?
-- Or, do you see the Reimann ζ function starting to take shape?
-- Or are you trying your best to dismiss these things?  Keep trying! lean will keep us
-- both honest.

namespace Rational  -- Bullshit meter ≈ 46
def le : Rational → Rational → Prop
  | .zero _ , _               => True  -- Duh, zero is less than or equal to everything
  | .number _ _ _ , .zero _   => False -- Duh, nothing other than zero is less than or equal to zero
  | .number p1 n1' _, .number p2 n2' _ =>
                              (p1 = p2 ∧ n1' ≤ n2') ∨   -- Covariant rationals are order by
                                                        -- their count
                                                        -- Co meaning aligned and vary meaning change
                              (p1 ≠ p2 ∧ n2' ≤ n1')     -- Contravariant rationals are ordered
                                                        -- by the inverse of their count.
                                                        -- Contra meaning against and vary meaning change.

def lt: Rational → Rational → Prop := fun r1 r2 => le r1 r2 ∧ ¬ le r2 r1
end Rational

-- Let's make the symbols work.
instance : LE Rational where  -- Bullshit meter ≈ 5
  le := Rational.le

instance : LT Rational where  -- Bullshit meter ≈ 5
  lt := Rational.lt
-- If you have made it this far, then you must agree that while I may not be right, and I am certainly
-- not wrong so far. Relax, the compiler will keep me honest.  I want you
-- to argue with me. I am going to say some really crazy things that you are
-- going to find very difficult to argue with.  These are slow pitches right now.

-- So, now we have the ability to express rationals, let's pick some interesting
-- rationals in the order we care about.  What are interesting rationals?  Dunno
-- yet. But! I do know 1 interesting Rational number.  That is the origin!
-- Zero = 0.00 <--- is this 2 or 3 significant digits?  Turns out, that will matter.
-- Not yet, though.
structure IndexingProcess  -- Bullshit meter ≈ 143
        --       ^                             +-------------------------------------------- I hate this word.
        --       |                             |                                             It is intangible
        --       |                             V                                             It is imaginary
        --       +------- WTF is this?  Well, set theory says that we can map things
        --                to the natural numbers.  This is that indexing process.  This
        --                will take the current rational and create the next rational
        --                in the sequence. rᵢ → rᵢ₊₁ → rᵢ₊₂ → ...
    (Value: Type)
    (Carrier: CarrierProcess Value)
    [DISTINGUISHABLE Value Carrier]
    [ADMISSIBLE Value Carrier]
  where
  count: CountingProcess Value Carrier
  origin: Rational                        -- This is the first thing that we count!

  -- The iterate interface is the most straightforward way to count.
  -- Structures will tend to provide this consumed iterator interface,
  -- so that once this guy is resolved by the compiler, it is just a lookup.
  iterate: Rational → Rational := fun r =>
    match r with
  --          +----------------+--------------------------- We start with our truth!
  --          |                |       +------------------- We don't always have to count by 1, we
  --          |                |       |                    can always count by 2s or 5s.
  --          |                |       |               +--- Also, we don't have to start at 0, we
  --          |                |       |               |    can start at π if we want to.
  --          V                V       V               V
    | .zero   p     => .number p  count.count       origin   -- 0 -> 1
    | .number p i _ => .number p (count.iterate i)  origin   -- i -> i+1
  --                                   ^               ^
  --                                   |               |
  --              This is counting! ---+               |
  --                                                   |
  -- So, this guy named Galileo,                       |
  -- had this idea that you have                       |
  -- to have a reference point                         |
  -- to measure things from.  -------------------------+
  -- Not my idea, man.  But..
  -- I have to say, this whole
  -- thing falls apart without it.


-- Now, we have a giant elephant in the room.  I mean _HUGE_.  Basically,
-- we have no facility to describe the average number.  I mean, the _average_
-- number, an infinite decimal irrational representation of any and all orderings
-- of all numbers.
--
-- Don't tell normies that.  They will have our asses!  But, we really have
-- no facility to describe the _average_ number.  We can talk about individual
-- numbers all day long, but not the average number.  So, let's take a page
-- from statistics and build a giant sampling of numbers so we can talk about
-- the _average_ number.
--
-- ...
--
-- You didn't buy that did you?  It _felt_ forced when I was writing it.
--
-- Speaking of force..  we can start from anywhere and count.
-- For instance, 2π will spin us around exp(θi).  Wow, a cycle is even, wonder
-- what a 1/2 spin is? a single π?  A spinor says what?  Do we have a 1/2 spin
-- carrier?
--
-- It can't possibly be... except I haven't defined enough for you to argue with
-- me about it yet. Like I said, I am going to say some really _crazy_ things.
-- And you are going to find it difficult to disagree with me, even though
-- you know how _technically_ wrong I just _have_ to be.  I think you will find
-- that I am cleverer than you think.

class COUNTABLE  -- Bullshit meter ≈ 85
 --      ^                 Bet you weren't expecting the word COUNTABLE from any of that.
 --      |                 But that is exactly the concept we are modeling, there exists
 --      +---------------- an enumeration of these things.  These 1/2-spin carriers.
 --                        I bet you have immediately written me off.  Just remember, this thing
 --                        compiles and demonstrates something.

    -- Our two _brigands_ Value and Carrier!  So, our friend Marconi was a clever fellow.
    -- He demonstrated that you can use the presence and abscene of a carrier to indicate
    -- information.  Then, this other guy named Claude said... hold my beer... and unicycle...
    -- and juggling balls... and whatever else he did _after_ he dropped some serious knowledge
    -- on information. That is why this carrier is important.  We _MUST_ extract every last
    -- piece of information from the carrier.
    (Value: Type)
    (Carrier: CarrierProcess Value)
    [DISTINGUISHABLE Value Carrier]  -- The way we do that is through _classes_.  This class,
                                     -- for instance, says we can distinguish the carrier the
                                     -- compiler sends us.  We have agreed with the compiler
                                     -- to use the universe metavariable to indicate value

    [ADMISSIBLE Value Carrier]       -- Next, when we want to send or evaluate a carrier to see
                                     -- if it is of the right _variation_, we can use this
                                     -- class.  What's a variation? You may ask?

                                     -- Sometimes false is true.

    where
            --   +-------------- Classes have an understanding of the local structure they are working in.
            --   |
            --   V
  index: IndexingProcess Value Carrier
  bounded? : Rational → Rational → Prop := fun stimulus threshold =>

       --     +------------------------------  Qu'est-ce que c'est?  What is being stimulated?
       --     |                                Well, we are asking the compiler, given two rationals
       --     |                                is the first one less than or equal to the second one?
       --     |                                Or, another way to look at it, does the compiler think
       --     |                                the first number is less than the second?
       --     |          +---------------  Where the hell did the threshold come from? Well, in this case
       --     |          |                 this is the current "1" rational value.  Are we still less than
       --     |          |                 one?  Why 1? *sigh* well, if we start with 1 and count, there
       --     |          |                 are two ways we can go.  We can iterate or subdivide. But, I
       --     |          |                 am foreshadowing too much.
       --     V          V
    match stimulus, threshold with --
    | .zero _, _ => True
    | .number _ _ _, .zero _ => False
    | .number p1 i1 _, .number p2 i2 _ =>
      ((p1.truth = p2.truth) ∧ i1 ≤ i2) ∨ ((p1.truth ≠ p2.truth) ∧ i2 ≤ i1)
--   \                               .                                    /
--    +--------------------+---------------------------------------------+
--                         |
--                         +------   Covariant/contravariant comparison rule.
--



-- So, time to get hard-core with some math.  I have been taking it easy on you because
-- I want to ease you into how _nuts_ this ride is going to get.  I am about to make
-- some really crazy claims about concepts that normally are not mentioned together.
-- Be patient, the lean will prove it out and you, technically, will not be able to
-- prove me wrong. At no point will I demonstrate I am right. Only that the compiler
-- tends to agree with me.
--
-- What I am building is an _argument_. Not a _proof_. Not certain you want to see
-- a proof of this. The compiler is working hard making sure that a proof could be
-- written, if it had to be.
--
-- And this _argument_ is going to be very compelling. This argument starts with
-- Euclid.  Euclid demonstrated that math can be constructed from finite objects
-- alone.  He did this with a sequence of facts.  These facts map to rational numbers
-- in very interesting and compelling ways.  That's all this says.  Given some
-- fact, you can interpret it as a rational structure and draw a conclusion about
-- area or length or volume or whatever.  All other math can be reduced to this.
-- A repeatable process to generate symbols that are _true_.
--
-- If you find the missal too confrontational, understand that I want you to
-- to really dig deep to really see if _your_ understanding of mathematics is
-- different from that of lean.  All I am doing is putting a bunch of symbols
-- in a file.
--
-- I want to be clear that I am just claiming that the symbols before you behave
-- as the concepts they describe for the questions I am asking the compiler.
-- As in, I _know_ how math works, and I am probing how _well_ the compiler can
-- represent these concepts.

-- For instance, a sequence of numbers is a common useful construction of math.
inductive Sequence  -- Bullshit meter ≈ 107
  |nil: Fact → Sequence
  |index :  Fact → Rational → Sequence → Sequence
       --             ^          ^
       --             |          |
       --             +----------+---- This should not be a controversial concept at all.
       --                              All I have done is describe how a sequence is written
       --                              down.  r₁ → r_₂ → ....  DO NOT GET COMPLACENT. I PROMISE
       --                              I will say something outlandish in a second.



-- The thing that Euclid pointed out was that once you wrote something in the
-- sequence, it could not change. It was _fixed_.  Not only that, but someone
-- else following the same process would arive at the same _fixed_ answer.
-- And so, we continue with the covariant/contravariant comparison rules.
-- So that if I decompose the mapping, you decompose the mapping, and the compiler
-- decomposes the mapping, we all agree on the concepts of how it is compared.
namespace Sequence  -- Bullshit meter ≈ 48
def le: Sequence → Sequence → Prop
  | .nil _ , _ => True
  | .index _ _ _, .nil _ => False
  | .index p1 r1 _, .index p2 r2 _ =>
    (p1.truth = p2.truth ∧ r1 ≤ r2) ∨ (p1.truth ≠ p2.truth ∧ r2 ≤ r1)
     --             ^                                ^
     --             |                                |
     --             |  contravariant comparison------+
     --             +--------- covariant comparison
     -- To count by _wholes_, you use identical truths (true=true or false=false)
     --          This is Peano Couting 1 -> 2 -> 3 -> ...
     -- To refer to the _n-th part_, you use different truths (true=false or false=true) 1/2 -> 1/3 -> 1/4 -> ...
     --          This is size of a piece if you divided into _n_ pieces.
     -- We have isolated our two kinds of counting process and can indicate to the
     -- compiler which one is which by the truth parity.  That way, when we
     -- ask the compiler to iterate, it knows whether we are counting by wholes
     -- or counting by parts.
     --
     -- So, before, we were actually working with the instance of a number. The number 1.
     -- we were not fiveshadowing, we were foreshadowing.  I will sixshadow for you so
     -- you can understand that you get the idea.  Will I sevenshadow?  Can I sevenshadow?
     -- Is it even possible to abstract something enough to sevenshadow?

     -- There.  I just sixshadowed.  When that coin drops, we will be discussing differential
     -- forms, antisymmetric residues, and other crazy nonsense.

-- Sequence limits are _well_ ordered.
def lt: Sequence → Sequence → Prop := fun s1 s2 => le s1 s2 ∧ ¬ le s2 s1
end Sequence

instance : LE Sequence where -- Bullshit meter ≈ 5
  le := Sequence.le

instance : LT Sequence where -- Bullshit meter ≈ 5
  lt := Sequence.lt

-- Now that we have some idea of a sequence, we can start to talk about limits.
-- Now, as much as it feels like a LimitProcess is a _geometric_ process, it is
-- actually a _topological_ process.  The definition of a limit says for every ball
-- around a point, there exists an element of the sequence strictly within that ball.
-- That definitely shouldn't be right in general, but I am definitely not wrong for
-- I did not give you a norm, now did I? I'm sure there is a metric, or at least
-- a _gauge_ for a metric around here somewhere...  Don't worry, when it shows
-- up it will look enough like an _L₂_ norm that you won't be able to tell the difference.
-- Literally, that's the argument.  You can't tell the difference.

-- I hope you are starting to see that if you subtley change the shape of the
-- objects in math by reordering the way in which they are described and experienced,
-- they cascade into each other in a very interesting way...
--
-- I mean, come on... 1->2->3->4 computing engine and the 1->1/2->1/3-1/4 computing
-- engine is the same up to direction of variance when described this way. In fact,
-- You should start to see how we can construct any Rational as a sum of these rationals
-- with a non-unique ordering of boolean variables.  This stack of orderings can then
-- be further arranged in the size of the ball around the limit point they inhabit.
-- Good god, look at all the points we can describe!  Are we dense, or am I dense,
-- or is this argument dense?

-- Any hooozlebee, this gets you a localized .....
structure LimitProcess  -- Bullshit meter ≈ 185
    (Value: Type)                     -- As you can start to see, the Value and Carrier
    (Carrier: CarrierProcess Value)   -- paramaters are universal.  What is happening is
    [DISTINGUISHABLE Value Carrier]   -- as we provide the capability to compute ≤ and <
    [ADMISSIBLE Value Carrier]        -- we further classify what the current carrier is
    [count: COUNTABLE Value Carrier]  -- trying to accomplish.  Is the compiler telling us
    where          --    ^               we are counting by wholes or parts? Or are we telling
  --                     |               the compiler we want to count by whole or parts?
  -- We are collecting --+               Either way, really.  The fact you and I can see
  -- quite the description!              the carrier _too_ is the interesting part.


  --    +-------------------------  All structures include an instance of the previous structure.
  --    |                           We are slowly building state in each of the classes we stack on.
  --    |                   +-----  The indexing process above is there to indicate which elemtent
  --    |                   |       in the sequence are we currently trying to understand?
  --    V                   V
  indexing_process: IndexingProcess Value Carrier
  limit: Rational               -- The limiting process will provide a rational representation
                                -- of the limit point of the sequence.  Either this is provided at
                                -- construction or inferred by the compiler, depending on circumstance

  sequence: Sequence            -- This is the inductive element that labels this particular element of
                                -- the sequence.  The label is a stack of boolean statements of the sort
                                -- true = true or true = false.  Or, at least, a compiler constructed
                                -- satisfiability problem that we are waiting for complete specification.
                                -- Again, NP-hard problem sounds like a _you_ problem, not a _me_ problem.
                                -- I don't need to run the compiler to believe this. This is my idea. I
                                -- know what I am trying to show you.

  iterate: Sequence → Sequence := fun s =>
    match s with
    | .nil f => .index f (Rational.zero f) sequence
    | .index p rat _ => .index p (indexing_process.iterate rat) sequence
--                                                ^
--     Just pointing out to you that we are       |
--     only trying to count and compute ≤   ------+
--     That is our only goal right now.


-- You see, the thing about math is you can use math to describe how a theorem prover works.
-- Then you can use a theorem prover to prove you implemented the theorem prover correctly.
-- The neat thing about this is, numbers fall out of the construction of this theorem prover.

-- The architecture of the theorem prover is a bit unorthodox.  Rather than being a computer
-- program, it is a computer meta-program. IT is a stack of labels in inductives, not real
-- data structures.  At no point have we instantiated anything, we have only described
-- a bunch of metaphysical constructions that could, hypothetically, store these things.

-- These are not the things themselves, but _representations_ of the things.  Which is precisely
-- what we are trying to figure out about the compiler.  The compiler purports to have a
-- reasonable understanding of math.  So, I will now explain to the compiler how the modeling
-- process works.  The mathematical modeling process.  I have just explained to the compiler how
-- it can talk to me about the concept of a number.  But, we have not yet agreed
-- on what a number actually _looks_ like.  The glyph "1", for instance.  That _looks like_ one.
-- So, you are going to have to _see_ one in the process I am about to describe.

-- Actually, we should start more primitively, with _zero_.  I think we all agree on what that
-- is supposed to look like.

class ENCODED  -- Bullshit meter ≈ 85
    (Value: Type)
    (Carrier: CarrierProcess Value)
    [DISTINGUISHABLE Value Carrier]
    [ADMISSIBLE Value Carrier]
    [c: COUNTABLE Value Carrier]
  where
  limit_process: LimitProcess Value Carrier
  encoding?: Sequence → Rational := fun s =>
    match s with
    | .nil _ => c.index.origin             -- Ladies and gentlemen, introducing 0.                     ^
    --                ----+----               Just like Marconi and Shannon demonstrated               |
    --                    |                   we can choose a circumstance that we call                |
    --                    |                   "Lack of carrier".  So, if you look waaaaaaaay back -----+
    --                    +------------------ you will see that origin is the first rational number
    --                                        we want to count.  While the Romans were
    --                                        quite confident that Fortran would rule the
    --                                        world and started counting from 1, we follow the
    --                                        one true way (tm) and number things from 0.
    | .index _ _ _ => limit_process.limit
                           --         ^
                           --         |
                           --         +---- Any time we need, we can ask the encoded carrier
                           --               what it thinks the current limit is.

-- We now have the pieces of a _residue_, an origin and a limit
-- away from that origin. This gives us _direction_ and _magnitude_!
-- There, I told you it was going to look like an _L₂_ norm.
-- You ever use PCA to solve an Eigenvalue problem? Weird how
-- the structure of PCA, Gram-Schmitt, GMRES, Galelrkin methods
-- all rely on understanding this residue. Something is projected
-- to a space with a happy null-space and operated on. This projection
-- needs just 2 things.  A _direction_ and a _magnitude_.  Strangely
-- This is also the interface for solving for the _value_ of non-linear systems.
-- Ya boy Newton figured that out.  So, which limit are we talking,
-- the residue or the value?  Thankfully, one is covariant and one is contravariant.
inductive Limit -- Bullshit meter ≈ 107
  |nil: Fact → Limit
  |index :  Fact → Sequence → Limit → Limit
    --     -----
    --       |
    --       |              This is Fact number 5.  32 possible representable numbers.
    --       +------------  We are slowly building 3 things simultaneously.  A _set_
    --                      of numbers.  By a _set_, I just mean the descriptive
    --                      label that describes the closure of the current inductive
    --                      represented as a big endian binary number.  This number has
    --                      Three representations: Big Endian Binary that you and I see
    --                      The _natural_ numberas and the _rational_ numbers are the
    --                      other two kinds of numbers we are building as well.

namespace Limit -- Bullshit meter ≈ 48
def le: Limit → Limit → Prop
  | .nil _, _ => True                   -- So, you going to let me get away with this?
                                        -- Smuggling in 0 being a converged digit?
                                        -- I mean, you let my friend Russell get
                                        -- away with it.
                                        -- lol.  j/k 0 is always less than anything.
                                        -- Converged or not.
  | .index _ _ _ , .nil _ => False
  | .index p1 seq1 _, .index p2 seq2 _ =>
    (p1.truth = p2.truth ∧ seq1 ≤ seq2) ∨ (p1.truth ≠ p2.truth ∧ seq2 ≤ seq1)
    -- So, the limit inches forward in sequene by whole and in value by part.
    -- At this point, you will see that we have a bunch of facts stacked up
    -- before we get to a number:
    -- Limit.index =  Fact Fact Fact Fact Number, four different le computations
    -- based on what those for facts are.
    -- By the time we get to the number, we have one of 16 possible representations
    -- of a number. And one of them is obviously 1 = T T T T T .....
    -- Of all _whole_ numbers 1 is leq than all of them.
    -- On the other hand, the smallest number we can represent is
    -- 1/2^n =  F F F F F F... I wonder what ε_mach is on your computer?
    -- Any way, as you can see, we can successfully differentiate 1 from the smallest
    -- possible rational representation very easily.
    -- Do you see _one_? I can't seem to find zero.... oh wait, we defined 1-r as
    -- contravariant!   So, we assume the _smallest_ representable rational number
    -- is 0.  So 0 = F F F F ..... just like you expected.
    -- If we interpret numbers as _whole_ then there is no 0 rational representation.
    -- If we interpret numbers as _parts_ then there is a gap that was identified
    -- by our good buddy Pythagoras and we can define _that_ to be zero.
    -- So, the ambiguity of _whole_ or _natural_ is about to get exploited in very
    -- _weird_ ways.

     -- Lol 0.9999999..... = 1. Not my rules, your rules. Turns out this is a fundamental
     -- fact of representation, not just a representation of a geometric sequence.

-- Still well ordered.  Is it important I keep reminding you?  Could be.
-- What about _i_ you say?  The complex limit requires a *ahem* direction, of which we
-- have a residue already.  Perfectly cromulent to talk about _i_ still.
-- Oh yeah, it do be like that. Remember we _do_ have a 1/2-spin carrier.
def lt: Limit → Limit → Prop := fun l1 l2 => le l1 l2 ∧ ¬ le l2 l1
end Limit

instance : LE Limit where -- Bullshit meter ≈ 5
  le := Limit.le

instance : LT Limit where -- Bullshit meter ≈ 5
  lt := Limit.lt

-- I suppose we should talk about superpositions at some point.  I mean, all of science
-- relies on superposition and simultaneity.  I mean the law of definite proportions, for
-- instance, shows how superopostion and simultaneity reduces to very small integers.
-- Wild, right?  Well, turns out stoichiometric measurement is one of only _2_ kinds of
-- measurement.  One covariant and one contravariant. You either passively measure it through
-- a carrier interaction or you actively manipulate it, finding its physical bounds.
structure CauchyProcess  -- Bullshit meter ≈ 228
    (Value: Type)                      -- These guys are still familiar
    (Carrier: CarrierProcess Value)
    [DISTINGUISHABLE Value Carrier]    -- We now have 4 different features we ask about
    [ADMISSIBLE Value Carrier]         -- a carrier!  That is 16 different possible carriers
    [COUNTABLE Value Carrier]          -- so far.  Gotta catch 'em all!
    [e: ENCODED Value Carrier]
  where
             --          +-------------- As expected we have the "local" process
             --          |               that we can query about the ongoing limiting process
             --          V
  limit_process: LimitProcess Value Carrier
  value: Rational                   -- This is the current rational representation of the value
  accumulation: Limit               -- This is th actual limit point, or the place the compiler
                                    -- wourl put it, if the compiler would only stop being so
                                    -- lazy and enuemrate e^iθ.
  iterate?: Limit → Limit := fun l =>
      match l with
      |.nil f => .index f e.limit_process.sequence accumulation
      |.index p seq _ => .index p (e.limit_process.iterate seq) accumulation
--                                                  ^
--                                                  |
--                                                  +-------- Still just counting

class RESIDUE
    (Value: Type) -- Bullshit meter ≈ 103
    (Carrier: CarrierProcess Value)
    [d: DISTINGUISHABLE Value Carrier]
    [a: ADMISSIBLE Value Carrier]
    [c: COUNTABLE Value Carrier]
    [e: ENCODED Value Carrier]
  where
  cauchy_process: CauchyProcess Value Carrier
  representative? : Limit → Rational := fun l1 =>
    match l1 with
    | .nil f => e.encoding? (.nil f)
    | .index f _ _ => e.encoding? (.index f (Rational.zero f) (.nil f))


-- At the risk of flaunting my _creative license_ again, I am going to model the average number.
-- That's right, kings and queens, this is an argument that needs normal numbers to not only exist but
-- to be so prolific as to be universal.                                             ^
--                                                                                   |      Kirk is right!
-- This is a countable representation of a normal number and it                      +----- I always split
-- would take you an uncountable number of symbols to disprove it at this point.            the infinitive
-- I think it should be clear that I want our pile of propositions represent not 1, not 2 but _3_
-- different kinds of numbers simultaneously. One binary representation, 3 numbers, 3 partial orderings.

-- The compiler can now talk about 32 different normal numbers.  Thats more normal
-- numbers than we know about!  I'm sure it picked the best normal numbers to represent.
-- We have 0 and 1, but those aren't normal, at least not in this representation.  I take
-- that back.  The nonunique representation of numbers allows for 0 and 1 to be normal,
-- turns out.  To lazy to show you, trust me on this for now, we will come back to this
-- idea.

inductive Sample -- Bullshit meter ≈ 150            -- This is the admissible symbol for a single normal number
  where

-- Serieously, though, not only is this a representation of your run-of-the-mill
-- number, it is actually a pair of numbers as well.  Did we just make _two_ numbers?
-- Are _we_, you and I, starting to count?  The compiler has 32 different numbers and
-- now we have _two_.  Seems unfair.

--        +---------------------------------------  We are having a bear of a time starting from scratch
--        |
--        |                    +------------------  Our friend Dirichlet (o.g. from way back) demonstrated
--        |                    |                    that we can't get out from under needing some magical
--        |                    |                    "number" to begin with.
--        V                    V
  |initial_condition: Fact → Limit → Sample

  |signal_response: Fact → Limit → Fact → Limit → Sample → Sample
      --            ^              ^
      --            |              |
      --            +----------------------------------------+
      --                                                     |
      -- Every number can show up, and should,  -------------+
      -- eventually since they all have to be different.
      -- Except they can't.  However, we can very carefully _describe_
      -- the _set_ of numbers that agree with Facts.
      --       ^
      --       |
      --       +------------------ I define _set_ to be the group of concepts that are modeled by words.
      --                           Now, we try to avoid using the "S" word at all costs as being
      --                           near meaningless drivel that holds any sort of nonsense.  I deal in Facts.

-- So, you should realize at this point, we are going to implement ≤ and < for this guy.  The samples
-- are well ordered.  In this case, there are two possible things that can be compared, which limit comes
-- before which in time and which limit is bigger than the other one.  Well, we can define them to be
-- the same for the first fact and contravariant for the second fact.  So, depending on the variance
-- of the facts, ≤ while either return ≤ on the first limit or the second limit.  Contravariant first
-- the covariant second, or covariant first then contravariant second.  Why not both?

namespace Sample   -- Bullshit meter ≈ 105
def le: Sample → Sample → Prop
  | .initial_condition f1 l1, .initial_condition f2 l2 =>
    (f1.truth = f2.truth ∧ l1 ≤ l2) ∨ (f1.truth ≠ f2.truth ∧ l2 ≤ l1)
  | .signal_response f1 s1 _ r1 _, .signal_response f2 s2 _ r2 _ =>
    (f1.truth = f2.truth ∧ r1 ≤ r2) ∨ (f1.truth ≠ f2.truth ∧ s1 ≤ s2)
  | .initial_condition f1 l1, .signal_response f2 l2 _ _ _ =>
    (f1.truth = f2.truth ∧ l1 ≤ l2) ∨ (f1.truth ≠ f2.truth ∧ l2 ≤ l1)
  | .signal_response _ _ _ _ _, .initial_condition _ _ => False   -- This shouldn't happen without
                                                                  -- serious _strain_.  The compiler
                                                                  -- thought _true = false_ somewhere.

-- I will argue that the munge of ordering we just gimmicked up is actually pretty well ordered.
def lt: Sample → Sample → Prop := fun s1 s2 => le s1 s2 ∧ ¬ le s2 s1
end Sample

instance : LE Sample where   -- Bullshit meter ≈ 5
  le := Sample.le

instance : LT Sample where   -- Bullshit meter ≈ 5
  lt := Sample.lt

-- So, why the name Sample?  Well, because we are getting sample numbers from
-- the compiler.  That's why.   The compiler may or may not care about normal numbers.  What it
-- cares about are the typical number found in context.  For math, the typical number can be defined
-- numerous ways.  The most onerous, though is _normal_.  Our limit must successfully model _ALL_
-- _DESCRIPTIONS_ of numbers, not the numbers themselves.  See?  This isn't a proof, it's an argument.
-- Lean just makes sure I model all the relevant numbers _precisely_. Under very, very specific circumstances,
-- the definition above is the most descriptive thing left to describe about a normal number. It is, itself,
-- a random sampling of irrational numbers. What set of circumstances?  Well we have a pile of Facts already
-- in front of us....

-- I love just throwing terms of art around in a blender like I am Bill Burroughs.

-- Speaking of... If you made it this far, you must be wondering _w THE ACTUAL f_?!?

-- Well, you may recall our friend Kurt (he's a goodfella) said something about how hard it was to prove
-- something about a system from within the system.  So, let's not even try.  Instead, let's try
-- to make the most outlandish _yet technically correct_ claims about the system and see what
-- the system does to _respond_ to those claims.

-- Introducing the concept of _INFORMATIONAL STRAIN_.  That is what you are under right now and I am
-- about to strain the information all the way out.  For those who do not know what a stress-strain
-- curve looks like, go look it up.  We are _clearly_ in the linear response zone of mathematics right
-- now.  We will completely model this stress and strain, which means _yes_, we will be developing the
-- stress tensor, and _yes_ we will be dealing with Navier-Stokes, and _yes_, you will see that the
-- _covariance_ of General Relativity will never settle at the boundary with the _contravariance_ of Quantum
-- Mechanics, no matter how much energy is there.

-- I take that back, 0 energy works. Du = 0 is trivial for D = 0.  Or ∫f(t, x, f_x) = 0 for f = 0.
-- Depending on if you are _weak_ or _strong_, of course.  I'm _strong_ so, give me the D.  Oh.


-- Speaking of, if you have never used the Gateaux derivative of a variational function to derive the
-- Euler-Lagrange equations (tell me you spent 10 years getting a highly specialized PhD without telling me
-- you spent a decade pushing Taylor series around),
-- you have one of two choices now.  First, go learn it then you can interact with the argument
-- better.  Or second, watch me derive it from _true=false_ in the craziest way you have ever seen.
                                    --          ----------
                                    --               ^
                                    --               |
                                    --               +-----------------  Informational strain, true ≠ false

-- Actually, there is a third choice.  I just chose one of many paths through this maze.  There are many
-- As we walk past places where you think I choose the wrong next abstraction, follow your thoughts.
-- These are just words.  They mean what you want them to mean.  Only the compiler has the dictionary
-- for the words in this file.  These aren't our words.  This is source code.

-- That said, though, I am going to walk through some seriously specialized results in computation, science
-- and math.  I am going to show you how to derive the Euler-Lagrange equations from true=false.
-- Then, we will use Galerkin methods to provide both dot and cross product definitions for the compiler
-- finally sticking a sock in the mouth of Bishop Berkeley after 300 years. I will bootstrap Galerkin so
-- it doesn't even _know_ what a derivative is.  That's the point of Galerkin, it eliminates derivatives.
-- It is a geometric argument that can be constructed with __COMPASS__ and __STRAIGHTEDGE__. Eventually. Watch.

-- But before we can get started, as the Sample says above, you need a limit point to get started.
-- Dirichlet's fault, not mine.  He's the one you need to bitch at about not being able to get out from
-- under that first limit you have to take _before_ you can start counting. If it isn't the Euler-Lagrange
-- equation, take it to be something smaller.  Let's start with a clock.  Tick-tock-tick-tock.
-- True-False-True-False.  That's really all you need.  I will teach you to count, add, integrate, differentiate,
-- and finally close a Frechet-style variation of a tensor that generates the _unique_ finite solution to the
-- _unique_ Dirac equation, while simultaneously deriving the Dirac equation and a finite gauge theory of
-- a single invariant.

-- While juggling chainsaws on fire!

-- It will get inelastic soon.  The definitions will get more rigorous.  The noose is going to tighten.
-- and you will find it ever _harder_ to prove me wrong even though I can't possibly be right.

-- Miss me with that incompleteness noise.  I ain't provin' nuthun. I'm just demonstrating to you that
-- this cannot be proven false.














-- Did you convege?  If so, you should be able to count to 1.  Can you count to 1? See how easy that is?
-- We agree on the demonstration that there are two numbers 0 and 1.  These are representated as
--     00000......
--     11111......
-- I bet you _think_ you know which one is which.  Why not both? We can keep 2 definitions at once:
-- a covariant definition and a contravariant definition.

-- If this made sense to you, you are ready to go.

-- So, in the very least stay for the spectacle of the craziest stack of compiler annotations you have
-- ever seen.

-- Am I writing a type check too deep for the type checker to resolve?
--                          -OR-
-- Will I succeed in pulling the entire universe out of my ass before Lean breaks?

-- I'm about to go get my tunneling hammer....

end Measurement
