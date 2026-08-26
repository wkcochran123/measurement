/-
__Measurement:  The Tragedy of John Henry__
__A Satire in Look-Ahead Backus-Naur Form__

_This is a gentle reminder that the fanciful stories we tell ourselves are just that: stories._

(c) 2026 All rights reserved -- Can you copyright an anonymous text? rofl.

TO ALL THE PEOPLE WHOSE IDEAS CONTRIBUTED TO THIS WORK, I HUMBLY STAND IN YOUR SHADOW.
I DARE NOT STAND ON YOUR SHOULDERS, FOR I AM NOT SURE I CAN SEE FAR ENOUGH TO KNOW WHERE
YOUR SHOULDERS ARE.

__EPISODE 1__:  _Counting_

"Hold on lady, we go for ride."
                    -- Short Round.

lake build --expert_mode --crash_on_everything --do_not_explain_errors

Can I do this with no imports?  Hold my beer...
-/

-- Foreword:

--                      Dear All,
--
--                      Technically, I'm dead.  But, if I were alive, it is possible that the words "This program
--                      is truly the way forward." could have been among a _LARGE_ set of words that I was capable
--                      of speaking.  I spoke a lot of words in only one particular order. I'm sure I spoke all of
--                      these words at some time in my life.  Just maybe not in this order.

--                                                                              Arthur C. Clarke



set_option allowUnsafeReducibility true
-- Well, I do need _a little bit_ of help..


-- I have always thought that the comments of the code should tell a story. The story helps the reader understand what is going on.  So, let me tell
-- you a story about measurement.  Measurement begins with _facts_.  I think you will agree it is easy to see whether or not something happened
-- and if that something happened, that _fact_ is _true_.  Otherwise, it ain't. Clear? Just remember, if you can tell it apart from something
-- that _didn't_ happen, then what you have is a _FACT_. And the _fact of the matter_ (wait until this pun lands in a few thousand lines of code)
-- is that _measurement_ is literally just this, distinguishing _this_ outcome from _that_ outcome.  But I am getting __WAY__ ahead of myself.

-- What can you measure?  Anything.  Even the thing that is doing the measuring.  While it is doing the measuring.  All the way down.  To try to give
-- you some idea of what I am talking about, I am going to try to measure how true the proposition _true = true_ is. At least, insofar as Lean will
-- let me show you that this isn't nearly as set in stone as you might think. Sometimes, for reasons that are wholly obvious when you think about it,
-- _true_ __MUST EQUAL__ _false_.  Blame Gödel.  He's the one that rained on everyone's parade.

-- _HOWEVER THAT MAY BE_ we are going to approach this like _ENGINEERS_, not some ivory tower Aristotelian philosopher.  We are going to use the
-- generally accepted principles of science and engineering to reverse-engineer the Lean compiler _AND PHYSICS ITSELF_ and explicitly _measure_ how
-- well it can evaluate _true = true_.

-- Why?  Cuz I understand math, but the way _I_ understand math is _very_ different from most people's understanding. This Lean proof assistant is
-- designed to show me where _I_ don't understand math.  Well, I'm going to show it a thing or two I have picked up over the years. I am going to
-- show _YOU_ a thing or two as well.  You see, in order to measure how true true really is, the machine needs to measure _YOU_. You personally.
-- __YOU THE KNOWER__.  You know what the right answer should look like.

-- Man vs. Machine!

namespace Measurement

-- One thing I hope _YOU_ do know is template metaprogramming.  The programming style of ascetic monks of extreme representational kung-fu.
-- This style I call:  __EMBARRASSINGLY SERIAL SUBJUNCTIVE METAPROGRAMMING__.  I explain to you the magic trick as I demonstrate it for someone
-- else:  _You the Reader_.  But, like I said, I don't look at math like you do.  Sets, limits, curves....  That's how you get into trouble.
-- So watch me explain the way I do math by doing the math I am explaining to you.

universe i
--      ---
--       ^                                                                | There is only 1 universe, the one we can experience.  Right now.  At
--       |                                                                | time step _i_. Or, is this _i_ = √-1 and _universe_ is merely a real
--       +----------------------------------------------------------------+ coefficient?  *i* forget.   Turns out, why not all four?


-- Now, each thing is constructed serially: we start at the very first thing and then just keep _adding_ to it. At no point in time is there a
-- fork in this process.  Every step adds to the device.  Nothing ever takes away from it or provides it with the option to choose between two
-- things.  It can only run from start to finish.  Or, it might run forever.  See?  No jumping, branching or looping.  Or, Oxford commas in fixed
-- width fonts. Just state accumulation.

/- CHORUS:
ME: I need a Fact.
COMPILER: A proposition?
ME: No, a proposition with a receipt.
COMPILER: That is called a proof.                          | This is a measurement from a device of my own design, a
ME: Great. Staple it to the universe. .        +-----------+ clever device that gives us an idea of how much bullshit
-/  --                                         |           | the Lean elaborator is putting up with.  This is the device
--                                             |           | reading its own input and measuring it.  For the sake of
class Fact where   -- Bullshit meter ≈ 9   <---+           | argument, I call this the bullshit the compiler has to wade through.
--
  truth : Prop                 -- Did it happen or not?
  decTruth : Decidable truth   -- Sometimes the compiler will know the answer before we do! See, it can keep track of BILLIONS of these little
                               -- decisions.  It cannot forget! It seems to understand what cannot be possible given the current situation _pretty_
                               -- well. _WITCHCRAFT_ I tell you! __BILLIONS__!  Seriously, though, Lean can appear to have precognition
                               -- sometimes.


-- Well, let's start with the simplest of all Facts, something that is True.  Here, the compiler is asked whether or not something is true.  In
-- this way, we can measure the compiler.  Is the compiler currently bullish or bearish on the veracity of _true_ = _true_?

namespace Fact    -- Bullshit meter ≈ 25
             --              +---------------------+ Know where the compiler puts this?  On the DATA page. This is not a variable.  It is the truth
             --              |                     | that the compiler and I agree on. Hell, __YOU_the_KNOWER__ may even agree with us.  You the
             --              |                     | reader, though, they might not agree with us just yet.  We still have to convince them.  By
             --              |                     | gluing a quarter to the table and taking their money playing three card monte. The coin cannot
             --              |                     | move.  How hard can this possibly be?
             --              V
def Truth : Fact := { truth := true, decTruth := Decidable.isTrue rfl }     -- For those new to Lean, I just asked
     --                                                            ^        -- the compiler what is _true=true_ and it
     --                                                            |        -- said TRUE.  This is the actual mechanism
     --             I assume you, too, can rfl this.  rofl. -------+        -- the compiler uses.  A label for it, anyway.
end Fact

-- Within this one little bit lies _Quantum Electrodynamics_.  Not because this is a math engine, not because we are about to undergo some _crazy_
-- math, and certainly not because I want to derive QED. The trouble is, that _bit_ is held in place by static electricity in RAM and by being
-- pulled high in closer representations.  Electrons are being used to encode this bit in silicon.  Unless you have one of those new cortical
-- engines that use stem cells to grow neurons. QED has to be there or the bit will not be consistent enough for Lean to understand.  See?  I wish
-- this could be easier, but the exit door for this is on the other side of Yang-Mills. Short Round was right, I hope __YOU_the_KNOWER__ are up
-- on gauge theory. I sure as hell _AM NOT_.

-- But before we measure, we have to deal with relative value.  I don't have time to spend _all day_ building you a number system from
-- scratch, so I will just make enough of the number system to get by.  Numbers, you see, are convincing.  People see numbers and they say:
-- Yep! Stimulus leads to effect.  So, I am going to build a number for you that cannot be built. That way, __YOU_the_KNOWER__ may even learn
-- something even if __YOU_the_READER__ disagrees entirely.

-- Speaking of numbers, we want to measure something.  Well, if we are going to measure what the compiler is doing, it would help if we agreed on
-- what some numbers were.  So, let's make some and name them.  We use Big Endian so we can shortcut a very common computation. At some point, we will
-- have described a particular number so well, the compiler can't help but give it to us.

/- CHORUS:
ME: I need the number to be bigger or smaller.
COMPILER: Bigger or smaller than what?
ME: Another number.
COMPILER: That is an order relation.
ME: No. That is a fact about two things agreeing which one is taller.
COMPILER: You want `<` and `≤`.
ME: I want them pairing off.
-/
--                                               +-----------------+ What you are looking at is an estimation of the work the elaborator is
inductive Number where   -- Bullshit meter ≈ 92  |                 | doing.  This is roughly some constant times the number of "steps" the
  | zero : Fact → Number --                   ^  |                 | elaborator requires to check this code.  As promised, the device only
    --      ^                                 |  |                 | grows. Eventually, the compiler learns how to cut the bullshit.
    --      |                                 +--+
    --      +---------------| 0 or 1. This is our digit. Or, rather, the clock
    --                      | complement of this for those who understand DSP.

  | one  : Fact → Number → Number
    --      ^                | Apparently, this process has been well known before I figured it out.
    --      |                | Not my idea, some dude named Peano camping at a spawn point.
    --      +----------------+
    --                       | Do you think we might be able to count both ways simultaneously? Up and
    --                       | down? HINT: Probably.  BTW, since I have Lean below me this is
    --                       | _the standard_ of demonstration to which I am holding myself. __PROBABLY__
    --                       | Sometimes, this might degrade as low as ``we'll see.''

-- *REMEMBER THAT* __FACTS__ have a high likelihood of being  __TRUE__!  (A sign of our times...) If one does not check facts then does one have
-- fake news?  Oh, I see, they are exclusive! That explains a lot.  Facts:  check_facts ≠ fake_news.  or check_facts ∩ fake_news = ∅.  See?
-- Lesson: facts are probably true. Welp. That's the gap we have to close.

-- And so, we set about constructing the machinery so the compiler can, in fact answer this question of can we count both ways as a matter of
-- probable fact?  Be patient, we have to go through Einstein field equations to get the answer, but it is in there. And we will find it.
-- Eventually.  Eye on the prize, we just want to know what this bit is.  Is it true or false? It is OBVIOUSLY true because it has no other option.
-- __YOU_the_KNOWER__ know that.  You know that {T,_rfl_}.  You know that is the quarter we are using to fool __YOU_the_READER__.  So, let's
-- assume __YOU_the_READER__ are of the gullible sort and are willing to ask, just once, "How probable?"

-- Remember, this is the question I want to show you the answer to:  That the compiler can do a pretty good job of evaluating how _true_ _true_
-- really is.   We have to derive, demonstrate, and prove uniqueness of a finite solution to the Yang-Mills equations order for me to show you that
-- this physical device before you has, as a matter of fact, computed the value of this Fact and not just pulled it out of thin air. An electron,
-- somewhere, represents this fact.  So, I am going to measure the response of the compiler to determine if I agree that the compiler thinks
-- that, electron means-- _viz._ in fact _true = true_, QED.  We will carefully construct an instrument and stimuli for the compiler so that
-- we can measure the truthiness of any of the two symbols: true or false. We will assign that truthiness a number, calibrate that number, measure
-- it very, very, _VERY_ finely, then give you error bounds on the likelihood that _true = true_.  Over/under _r²_ is .9995. and I will take your
-- book. (lol, You the Knower think that's a joke. I will show you it isn't.)

-- In the meanwhile, the actual fact on the number can be interpreted as the sign of that number. That way we can use a clock complement as the fact
-- itself. A clock?  Yeah, a clock.  It takes time to compile a program and I really don't want to wait forever.

--                                         +------------------------+
namespace Number  --  Bullshit meter ≈ 112 |                        |
def le : Number → Number → Prop --         V          Now, this is just _intuition_. We need
  | .zero _ , _ => True         -- 0 ≤ n  n∈ℕ         something that might pass as a natural number.
  | .one  _ _, .zero _ => False -- n > 0  n∈ℕ > 0     Lean has the Nat thing, but I don't trust it.  Do you?
--                                         ^          You do?    Such decadence!  A HUUGE assumption..
--                                         |                        |
  | .one  p1 n1', .one  p2 n2' =>   --     +------------------------+
      match p1.decTruth, p2.decTruth with
      | isTrue _,  isTrue _  => le n1' n2'   --   | So, we can interpret true and false as the sign of the values.
      | isTrue _,  isFalse _ => False        --   | of the values.  If true is positive, like in religion, then this is
      | isFalse _, isTrue _  => True -------------+ the truth table of ≤. Or would you like true to be negative, like
      | isFalse _, isFalse _ => ¬ le n1' n2' --   | the electron (≥)?  Why not both?  They both probably work.
end Number

-- Did you catch that?  We have a different fact than the compiler.  The compiler has true and false.  We, OTOH, have at least 3 truth symbols:
-- true=true, false=false, and true=false.  Weird. You can get __REAL__ clever with a trinary-binary pattern like boxing.  Speaking of boxing, I wish
-- Ali would have taken out Java erasure at the root. Unlike Lean, Java is not to be trusted (tm) for repeatable builds. That's a You the Knower
-- problem.

-- A clock complement collapses the true=true and false=false into a same/different cadence. Do we want to the compiler to count to 3 to match our
-- view of the world?  Probably, but not yet. This is fiveshadowing.  We don't foreshadow when we metaprogram, we fiveshadow.  Remember that we have
-- this truthiness measure because we have 3 symbols for a binary representation. And, we have same/different for our facts and true/false for the
-- facts in the compiler. _DON'T CROSS THE STREAMS_.  While not an unlicensed nuclear accelerator, we have to be careful not to fall into a circular
-- reasoning trap.

-- BTW, it is _not at all clear_ to me that numbers are well sorted. I mean, _i_. How do you sort that?  IEEE 754  figured out that _a_ ≠ _a_ can be
-- used to represent these concepts. _NaN_. I find IEEE plays it _real loose and cool_ with these definitions, so be warned. Besides, pretty certain
-- _YOU the KNOWER_ use *i* like it is a number _all the time!_  Most compilers are just too lazy to write out the COMPLETE Taylor expansion
-- e^(iθ) all the way out so we can really _understand_ _i_.  Just absolute laziness on the part of compilers.
-- ------
--   ^                                         | Keep an eye in this guy.  Shows up _EVERYWHERE_ and I mean
--   |                                         | __EVERYWHERE__.  I mean, Euler pretty much glued this identity
--   +-----------------------------------------+ into physics with his variational methods.  Sorry, I bet
--                                             | __YOU_the_KNOWER__ didn't know that.  I'll show you as we take
--                                             | __YOU_the_READER__'s money.

--                            +--+----------------------------------------------------+ Aaah, low entropy language,
--                            |  |                                                    | could there be a better
--                            V  V                                                    | medium?  Not possible.
-- A more maddening question is is 1 <= 0.999999999.... ?  Well, as you will see
--                           ----+        ^^^^^^^^^
--  Parsing syllables            |        |||||||||
--  Slick Willy style  -------+--+        +++++++++------- Is this rfl or not? rofl for the entropy, tho'. And, I have only heard it one way.

-- I will be asking a very similar question in a second. Turns out, I've heard _it_ both ways.

-- BTW, I hope you don't mind I hijack operators for my own nefarious purposes. If you forget what they mean, because hijack is really a euphemism
-- for what I'm about to do, just remember it always means "Less Than or Equal To" in whatever context it is in.

/- CHORUS:
ME: Any reason why _you_ can't use the label I just made up?
COMPILER: That's my label, not yours
ME: The label that's under the card
COMPILER: There is only truth under the card, right where I put it.
ME: Then you won't mind calling truthfully calling this "≤"
-/
instance : LE Number where  -- Bullshit meter ≈ 7
  le := Number.le

-- Trust me, bro.... ;-)


-- So, this is our "sensor" for the compiler's meaning of a Type.  The compiler will happily send us carriers (I think
-- they are called properties, but I have never seen a language spec) that will evaluate true/false for us to use as
-- "facts."
structure CarrierProcess -- Bullshit meter ≈ 85
    (Carrier: Type i)
  where
  symbol: Fact      -- Said fact from the compiler, either _true_ or _false_.
  value: Number     -- The inductive number defined above.  It isn't a natural number, in that it
                    -- does not start from the empty set.  It starts from the trivial truth _true_ = _true_.
          --                                          ^
          --          My apologies for using |        |
          --        such a vague descriptor. +--------+
          --                    Filthy word. |

  event: Number → Number := fun s =>
    match s with
    | .zero _ => .zero Fact.Truth -------------- See? _true_ = _true_.  This assumes that whatever comes in is true.

    | .one  p _ => .one  p value  -------------| This starts to stack inductives in weirdly recursive ways.
                                  --           | Also, notice that this is the canonical fence post problem.
                                  --           | The next number is covered by the value now. If you hate
                                  --           | fence post problems, realize that they are the first fundamental
                                  --           | bug. I mean, distinguishing feature.


-- The CarrierProcess is a way for the compiler to boot strap 2 numbers, 0 and 1.  We will call 1 the ability to count.  The ability to count in
-- universes is a natural (sic) part of a complete Lean install.  It does it for you.  All this class does is tell the compiler, this is what we
-- call the next thing.  We call the next thing 1.

-- Another way to look at it: To ZERO an instrument is to TARE the scale back to Fact.TRUTH.  What we are doing is giving the compiler
-- 2 instructions here:
--    .zero => Tells the compiler to reset to the sentence "Zero is true".
--    .one  => Tells the compiler:  Compute the next sentence by attaching Fact p.

-- Any reason why we can't have the functions zero() and one() defined as such?  *YOU the KNOWER* know why.  Gets confusing when constructors look
-- like they have side effects. And, well, we are going to compute a number as a side effect of this demonstration. *YOU the READER* will
-- allow it---for now.

/- CHORUS:
ME: Before I count, I need difference.
COMPILER: Difference from what?
ME: From itself, eventually. But start small.
COMPILER: You want decidable equality.
ME: I want a witness that the names are not the same names.
COMPILER: That is decidable equality.
ME: Fine. But with better lighting.
-/
class DISTINGUISHABLE  -- Bullshit meter ≈ 28  ------------------+ You may start noticing a pattern to the structure → class → inductive →
    (Value: Type i)                            --                | structure → class → inductive → structure → class → ...
    (Observation: CarrierProcess Value)        --                |
    where                                      --                | An eternal golden braid of meta-programming. This argument does not exist without
    --        +--------------------------------------------------+ the beauty of Hofstadter's work. However, I must warn you that the classes going
    --        |                                                    forward tend to accrete in stacks of templates.  Stacks and stacks and stacks.
    --        | Hundred or so.  Templates and partial instantiations.  I take that back, there is one concrete instantiation at the end. We will
    --        | leave them spread out for now, eventually we will start compacting them and all hope will be lost that __YOU_the_KNOWER__ can reason
    --        | about the templates while __YOU_the_READER__ soaks in how it works by failing to understand what is happening. Mwah! hah! hah!
    --        | Actually, I don't think I have a choice in the matter.  Pretty confident this is one of the easiest ways through this argument.

  fact: Fact           -- This is quite true as a matter of fact.  Also, C++ PTSD.
                       --           DUCK::Duck duck = new DUCK::Duck() // quack!


   --       +---------------+ So, generic metaprogramming.  This agrument relies _HEAVILY_ on generic metaprogramming. We are intentionally _NOT_
   --       |               | instantiating the symbol, rather we are grabbing the label the compiler uses to track universe level.  There is _no_
   --       |               | memory allocation so far, other than Fact.Truth which is on the DATA page, not the INSTRUCTION page. I don't expect to
   --       |               | need to allocate memory since we now have access to numbers the compiler uses and trusts.
   --       V
  symbol: Type Value   -- We can index the value with a metavariable symbol, as in the compiler has a representation of some integer level.
                       -- Only suckers use Nat (I credit my mentor Russ Hewitt for that).

  distinct? : Prop := True    -- Is this thing distinct?  God I hope so, or the compiler has problems.

  different? : Type Value → Prop :=
    fun s1 => s1 ≠ symbol  -- If things are at different universe levels, then     <-------+              +---------------------------------+
                           -- the compiler can easily tell the types apart.                |              |                                 |
                           --                                                              |              |         _CAVEAT EMPTOR_         |
  dec_distinct : DecidablePred different?  -- And, the compiler will be good enough        |              |                                 |
                                           -- to tell us if it thinks the universes        |              | ------------------------------- |
                                           -- are different as we _WRITE_ the code.        |              |   The appearence of a bitset    |
--                                                                                         |              |   within the compiler only      |
--                                                                                         |              |   expresses the deep desire of  |
-- And, since we now agree with the compiler what a natural number looks like,             |              |   the compiler to bucket things |
-- lets talk about how they are structured.  I'm _assuming_ the compiler uses natural      |              |                                 |
-- numbers.  __YOU_the_KNOWER__ will no better than _i_.                                   |              |  _NO STATEMENT ABOUT UNIVERSAL_ |
--                                                                                         |              |     _MECHANISMS IS CLAIMED_     |
-- You didn't notice the universe number thing? -------------------------------------------+              +---------------------------------+

/- CHORUS:
ME: I need a natural number.                           |      +-----------> Finally, we can meet the entire case of characters on our journey.
COMPILER: Great. Use Nat.                              |      |             You have met _me_ obviously, and I have met _YOU the READER_ before.
ME: No. Too much civilization.                         |      |             _YOU the KNOWER_ are new to me; it is nice to meet you. The fourth
COMPILER: Then what do you want?                       +------+             member of our cast is the _COMPILER_. Normally, the compiler fills
ME: I want to tell one from the rest.                  |                    a mechanical role in the demonstration of things.  We are doing this
COMPILER: That is barely counting.                     |                    a bit _differently_ and _compilation itself_ is the process we measure
ME: Exactly. We are still in the cave drawing phase.   |                    _together_.
-/
inductive Natural  -- Bullshit meter ≈ 107       | The Fact here is a bit murkier. (Or is it a murkier bit?)  We are coordinating with the compiler
  where                   --                     | now on what is a fact and what isn't.  We have a notion of true and the compiler has a notion of
  | zero : Fact → Natural -----------------------+ true, which leads to true=true or false=false.  See?  Or is this _straining_ your imagination?
                          --                     | Or, you can just think of it as the compiler assuring you that, indeed, true=true. See how easy
                          --                     | it is to make this very controversial?

  | number : Fact → Number → Natural → Natural --+ Here, the Fact is that we agree with the compiler that the universe of level Number is what we
                          --                     | call a Natural number.

-- The natural numbers have this property that the ones after are bigger than the ones before.  Not certain they have another property worth talking
-- about.  If you can think of one, leave it in the comments below.  Remember to like and subscribe. It helps the algorithm.

namespace Natural   -- Bullshit meter ≈ 42     _42?!_
def le : Natural → Natural → Prop
  | .zero _ , _  => True                     -- Zero is less than or equal to everything
  | .number _ _ _ , .zero _ => False         -- Any nonzero natural is > 0.
  | .number p1 n1' _, .number p2 n2' _ =>    -- So, let's look at the values of the numbers to see.
    (p1.truth = p2.truth ∧ n1' ≤ n2') ∨      -- covariant: same-truth wholes, n1' ≤ n2'
    (p1.truth ≠ p2.truth ∧ n2' ≤ n1')        -- contravariant: the different-truth case (the missing branch)

-- Let's discuss well-ordered numbers.  We all understand the definition of well ordered implies the existence of a map that allows you to perform
-- this computation on the natural numbers:
def lt: Natural → Natural → Prop := fun n1 n2 => le n1 n2 ∧ ¬ le n2 n1
-- I hope you agree it will be difficult for the us and the compiler to diverge on this definition. And any time the compiler _does_ diverge from
-- this assumption, it will let us know.
end Natural


/- CHORUS:
ME: Is this the same label?
COMPILER:  No, it is quite different.
ME: "≤" is not the same?
COMPILER:  That is the same symbol as my symbol
ME: How do you like you Waffle House hash browns?
-/
instance : LE Natural where  -- Bullshit meter ≈ 5
  le := Natural.le

-- More notional abuse.  Won't someone think of the notation?
instance : LT Natural where  -- Bullshit meter ≈ 7
  lt := Natural.lt


-- So, you ever thought about how you count before? I mean, _YOU the KNOWER_ obviously know how to count.  I mean _YOU the READER_. How do you
-- _really_ know how to count? There are two ways to count, it turns out.  One way is to iterate, as in a sequence. The other way is to decompose
-- into similar pieces, as in cardinality.  Let's tease the meanings of these two ways to count apart as I think that might be important to the plot.
--
-- You are reading this for the plot, right?

/- CHORUS:
ME: I need a counting process.
COMPILER: Count the things?
ME: Or count what makes up the things.
COMPILER: That is decomposition.
ME: Good. Put it next to enumeration.
COMPILER: Why?
ME: Eventually the pieces become things and demand representation.
-/
structure CountingProcess -- Bullshit meter ≈ 118
    (Value: Type i)
    (Carrier: CarrierProcess Value)
    [object: DISTINGUISHABLE Value Carrier]
--     ^
--     |
--     +----------+ Become not accustomed to helpful partial instance names.  They will become too many to keep up with. As a matter of fact,
--                | these variable names are almost useless except to understand them as ends of a plug.  That is it.  There are no values to store.
--                | So, no reason to give them names.  Except to help the compiler plug templates in together.  For you and I, these names barely
--                | hold any meaning because they, BY CONSTRUCTION, can only ever be inhabited by {true,rfl}.

  where
-- Well, it turns out, to do either, you need a _carrier_.  Something you can identify, classify, bin, and count.  The first three are what we call
-- decomposition.  The fourth is iteration.  This file deals exclusively with iteration with the other _three_ constructions to follow in later files.
-- So, let's just assume we can talk about a carrier.  W.l.o.g., we can let a carrier be letters that we send back and forth to the compiler. That's
-- right. Snail mail.

  carrier: CarrierProcess Value -- I can taste the envelope glue already.

-- No joke, this is snail mail and can take the compiler a long time to resolve arguments that are recursively enumerable.  Oh well...  Halting
-- problem/smalting problem. Sounds like a _YOU the KNOWER_-problem. Actually, it is a _you_ problem.  Both of _you_, personally, cannot devise
-- a way to short cut this.  You wait for daddy compiler. _You_, personally have to _wait_. Time has to _elapse_ for _you_.  Like on a clock, fr fr.
-- No one else has to _wait_. They can read this in a text editor and just assume the compiler figures it out.  They don't have to wait. You are
-- probably wondering why I mention this.  Just planting seeds. Back to the code.

  count: Natural
-- I can easily count how many letters the compiler has sent me. I have the letters and can count to 5.  I think 5 is the biggest number we have
-- run into in the code.  The bullshit meter keeps climbing using numbers we HAVE NOT constructed yet.

-- Okay, seriously, back to code. We can work with compiler to _iterate_ in a send/response loop that allows us to stack inductives in a tensor
-- like way.
  iterate: Natural → Natural := fun n =>
    match n with
--                           +--------+ This is the "GROUND TRUTH".  The thing that we agree happened that allowed us to start counting in the first
--                           |        | place. _YOU the KNOWER_ know this has to be true so far.  _YOU the READER_ understands the _possibility_..
--                           |        | This is the opposite of absence.  We know something is there.  That something is _nothing_. Personified as
--                           |        | the Mark of the Beast ∅.  _THESE_ are the naturals. If it isn't Fact.Truth it has to be... nothing.
--                           |        | I define the Naturals as *THE LACK OF TRUTH*, because if object.fact isn't true, it can't be anything else.
--                           V
    | .zero _ => .zero object.fact  -- Naturals need to have something factual to start from I would prefer to avoid the empty set as that blatantly
                                    -- _assumes sets exist_.  Such decadence. Instead, we are using the fact that true = true. However, sometimes,
                                    -- true = false.  Just to mix it up. I actually don't care which world we live in, symmetric or anti-symmetric.
                                    -- and neither does the compiler, as we will _conclusively_ demonstrate its inability to tell the difference.

--            +-+-+--------------------   This is compiler gibberish.  Which is fine.  The compiler is counting.  I am telling
--            | | |                       it what _I_ think goes there.
--            V V V
    | .number _ _ _ => .number object.fact carrier.value count
--                                   ^            ^        ^
--                                   |            |        |
--                                   +------------|--------|------------ The fact the next thing showed up
--                                                |        |
--                                                +--------|------------ The label I give this compiler gibberish in the compiler.
--                                                         |
--                                                         +------------ My list of numbers up to this point. That should be enough
--                                                                       for the compiler to figure out how I sort the symbols
--                                                                       by value.



-- This is going to take a minute to understand.  ADMISSIBLE.  This just means the compiler did not barf on a computation. In this case what the
-- compiler is doing is looking through the inductive to see if it can find a counterexample to a ≤ b. If it can, it refuses to compile, so this
-- class is trivially satisfied by a completed compile.
/- CHORUS:
ME: Counting only goes up.
COMPILER: Then why do your pieces get smaller?
ME: Because I changed what we are counting.
COMPILER: That sounds illegal.
ME: No. That is admissible.
COMPILER: Admissible to whom?
ME: To the representation that remembered which way was forward.
-/
class ADMISSIBLE  -- Bullshit meter ≈ 60
    (Value: Type i)
    (Carrier: CarrierProcess Value)
    [DISTINGUISHABLE Value Carrier]   -------------------------------------+ We don't want the compiler to forget the little program we agreed on
                                      --                                   | that allows us to use the interesting feature of ℕ: a total order.

    where
  counting_process : CountingProcess Value Carrier
--        ^
--     +--|-----+-------------------------| Given a counting process, the next number is admissible if it has already been counted otherwise
--     |  |     |                         | it must be bigger in absolute value.
--     V  +-----+
  admissible? : Number → Number → Prop := fun stimulus threshold =>
       --     +------------- Is our first number less than
       --     |         +--- or equal to the second number?
       --     |         |
       --     V         V
    match stimulus, threshold with
       --    ^         ^                                                   | Why the names stumulus and treshold?  Well, if the stimulus is less
       --    |         |                                                   | than the threshold, then you can record it as a stimulus with no
       --    +---------+---------------------------------------------------| response.  c.f. Coloumb and static friction for more info.
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
  --                            Also, this is the fall-thru shortcut promised way up  when
  --                            we mad a number.


-- Now, I am invoking my _creative license_ here, kinda.  Let's talk rational numbers.  Here we define rationals in a very interesting way.  Given a
-- sequence of naturals, you get: F → A → A → F → B → A/B → F → C → C → F → D → C/D → ....  I could convince you that such a mapping will enumerate
-- all rationals, but I am lazy af.  Not only that, but you should easily be able to convince yourself it maps the rationals over and over again to
-- the naturals because it doesn't assume reduced fractions.  Point is, all those numbers _are_ rational numbers. And we don't need all of them,
-- just a countable amount. It would be a _nice to have_ if it were bijective.

/- CHORUS:
ME: I need fractions.
COMPILER: For division?
ME: Not yet. For pieces.
COMPILER: Pieces of what?
ME: The thing we just finished pretending was one.
COMPILER: So one was provisional.
ME: All measurement is provisional. Please initialize the saw.
-/
inductive Rational  -- Bullshit meter ≈ 107
      --     ^
      --     |           | This is not ℚ. This is just an inductive structure that is populated with symbols that represent what the
      --     +-----------+ compiler might consider a rational number.  This is just a symbol for a rational number looking thing in
      --                 | the compiler, not the rational number itself.   Take it as read, this is just a pile of things that _behave_
      --                 | *EXACTLY* like rational numbers would if they were constructed from universe levels. universe 3.7, for instance.
      --                 | Talk about an _imaginary_ universe, lol.

  where
  | zero : Fact → Rational
  | number : Fact → Natural → Rational → Rational

-- Or, you can give me a counterexample.  A rational number that CANNOT be represented this way and I will gladly make that the second rational in
-- this chain. See?  You can't prove me wrong. So far, compiler is buying what I'm selling.

-- So, one way to think of a rational series is as 1/2, 2/3, 3/4, 4/5, .... That doesn't seem like it would cover all the rationals, and it doesn't.
-- But, you must find it hard to argue that this is _not_ a series of rational numbers.  I think 1 - r is the interesting value here.  1/2, 1/3, 1/4,
-- 1/5, ....  -- It is _obvious_ that this _more than adequately_ spans the rationals. The threshold mention above should start to make sense.  1 is
-- our threshold and we can count our way arbitrarily close to it without keeping state.

-- And, since we haven't included any numbers from Lean whatsoever, I will just go ahead and assume that residue is _actually_ what is being
-- represented. And when we do math, we are just doing math on the representations. I feel like I have read this usually ends in disaster somehow.
-- I think both _YOU the KNOWER_ and _YOU the READER_ are really skeptical for two different reasons.

-- Why not both? We have a truth parity we can use to decide.

-- One should be reminded of the Trumpet of Gabriel.  I'm about to Gauss's law all over some musical instrument in nasty ways....  Would you like
-- to try my Galerkin-style? Or, do you see the Reimann ζ function starting to take shape? Or are you trying your best to dismiss these things?
-- Keep trying! Lean will keep us both honest. Or are you just stuck in the algebra.  It works either way.  Never understood why topology and
-- geometry were different subjects...

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

/- CHORUS                                                                      +----------------------------------------------------+
ME: How many times are we going to go over this?                               |                                                    |
COMPILER: Every time.                                                          | AN APPEAL FOR THE CREATION OF THE UNIT OF BULLSHIT |
ME: I bet we don't.                                                            |                                                    |
-/ --                                                                          +----------------------------------------------------+
instance : LE Rational where  -- Bullshit meter ≈ 5  --                        |                                                    |
  le := Rational.le                                  --                        | As made clear by Frankfurt, bullshit cares not for |
                                                     --                        | truth, but for consistency alone.                  |
instance : LT Rational where  -- Bullshit meter ≈ 5  --                        |                                                    |
  lt := Rational.lt                                  --                        +----------------------------------------------------+

-- If you have made it this far, then you must agree that while I may not be right, and I am certainly not wrong so far. Relax, the compiler will
-- keep me honest.  I want you to argue with me. Both of you.  I am going to say some really crazy things that you are going to find very difficult
-- to argue with.  These are slow pitches right now. These are words and stories you are familiar with.  Kinda.  You know the words.  But the
-- rhythm might seem just a little off. _YOU the KNOWER_ might understand that *I* am trying to show you something and *i* is trying to show you
-- something.

-- It's in Diagon Alley with all the wizarding stuff... Just pulling your leg, or am I?

/- CHORUS:
ME: Keep track of the uncounted numbers.
COMPILER: If they are numbers, haven't they been counted?
ME: That is adorable.
COMPILER: I dislike your tone.
ME: Most numbers have not been counted. That is why we need an index.
COMPILER: I thought the index was the counting.
ME: No. The index is the little fence around what we are allowed to pretend we counted.
-/
structure IndexingProcess  -- Bullshit meter ≈ 143
        --       ^                             +-------------------------------------------- I hate this word.
        --       |                             |                                             It is intangible
        --       |                             V                                             It is imaginary
        --       +------- WTF is this?  Well, set theory says that we can map things
        --                to the natural numbers.  This is that indexing process.  This
        --                will take the current rational and create the next rational
        --                in the sequence. rᵢ → rᵢ₊₁ → rᵢ₊₂ → ...
    (Value: Type i)
    (Carrier: CarrierProcess Value)   -- Foot bone is connected to the ankle bone
    [DISTINGUISHABLE Value Carrier]   -- Ankle bone is connected to the leg bone
    [ADMISSIBLE Value Carrier]        -- The leg bone is connected to the knee bone.  My MCATs were devastating.
  where
  --            +-----------------------------------------------------------------------------+ Just as the compiler suspected, there is a
  --            |                                                                             | counting process at the heart of the indexing process
  --            V
  count: CountingProcess Value Carrier
  origin: Rational                        -- This is the first thing that we count!

  -- The iterate interface is the most straightforward way to count.  Structures will tend to provide this consumed iterator interface, so that once
  -- this guy is resolved by the compiler, it is just a lookup.
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
  --                                   |               |                         +------------------------------------------------------------+
  --              This is counting! ---+               |                         |                                                            |
  --                                                   |                         | NO DIFFERENTIAL EQUATIONS WERE HARMED IN THIS CONSTRUCTION |
  -- So, this guy named Galileo,                       |                         |                                                            |
  -- had this idea that you have                       |                         | Any continuity expressed or implied is purely the bias of  |
  -- to have a reference point                         |                         | _YOU the KNOWER_. The proof will never employ uncountable  |
  -- to measure things from.  -------------------------+                         | constructions.                                             |
  -- Not my idea, man.  But..                                                    |                                                            |
  -- I have to say, this whole                                                   +------------------------------------------------------------+
  -- thing falls apart without it.


-- Now, we have a giant elephant in the room.  I mean _HUGE_.  Basically, we have no facility to describe the average number.  I mean, the _average_
-- number, an infinite decimal irrational representation of any and all orderings of all numbers. The number someone might come across if they were
-- to choose a number in an _i.i.d._ fashion. You know, just your average, run-of-the-mill number. If only we could describe them.
--
-- Don't tell normies that we have no idea what they look like.  They will have our asses!  But, we really have no facility to describe the
-- _average_ number.  We can talk about individual numbers all day long, but not the average number.  So, let's take a page from statistics and
-- build a giant sampling of numbers so we can talk about the _average_ number.
--
-- ...
--
-- You didn't buy that did you?  It _felt_ forced when I was writing it.  Speaking of force..  we can start from anywhere and count.For instance,
-- 2π will spin us around exp(θi).  Wow, a cycle is even, wonder what a 1/2 spin is? A single π?  A spinor says what?  Do we have a 1/2 spin
-- carrier?
--
-- It can't possibly be... except I haven't defined enough for you to argue with me about it yet. Like I said, I am going to say some really
-- _crazy_ things. And you are going to find it difficult to disagree with me, even though _YOU the KNOWER_ are pretty confident I am being less
-- than rigorous with some extremely complex subject matter.  You know how _technically_ wrong I just _have_ to be.  I think you will find that I am
-- cleverer than you think.  I will make this more entertaining for _YOU the READER_ soon as you realize I can make the Lean do nearly anything
-- I want it to and you just want to see the magic trick finish.

/-
ME: Count up until we need a fraction.
COMPILER: Need one for what?
ME: To describe the next thing without pretending it is whole.
COMPILER: So the counting broke.
ME: No. The unit broke.
COMPILER: That sounds worse.
ME: That is called a Dedekind cut when fancy people talk about it.
-/
class COUNTABLE  -- Bullshit meter ≈ 85
 --      ^               | Bet you weren't expecting the word COUNTABLE from any of that. But that is exactly the concept we are modeling,
 --      |               | there exists an enumeration of these things.  These 1/2-spin carriers. I owe you a long explanation on the carriers.
 --      +---------------+ I know, I know.  Just hang in there. There are thousands and thousands of lines of code to go through yet.

 -- Our two _brigands_ Value and Carrier!  So, our friend Marconi was a clever fellow. He demonstrated that you can use the presence and abscene of
 -- a carrier to indicate information.  Then, this other guy named Claude said... hold my beer... and unicycle... and juggling balls... and whatever
 -- else he did _after_ he dropped some serious knowledge on information. That is why this carrier is important.  We _MUST_ extract every last
 -- piece of information from the carrier.
    (Value: Type i)                  --                    | The way we do that is through _classes_.  This class, for instance says we can
    (Carrier: CarrierProcess Value)  --                    | distinguish the carrier that the compiler sends us, for instance, and it will have the
    [DISTINGUISHABLE Value Carrier]  ----------------------+ universe metavariable to indicate the height of the object.

    [ADMISSIBLE Value Carrier]       ----------------------+ Next, when we want to send or evaluate a carrier to see if it is of the right
                                     --                    | _variance_ as the computation.  What is variance you may ask?
                                     --                    |
                                     --                    | Sometimes false is true.

    where
            --   +-------------+ Classes have an understanding of the local structure they are working in and come with the ability to compare
            --   |             | a distinguishing feature well enough to index a list, should the need arise.
            --   V
  index: IndexingProcess Value Carrier
  bounded? : Rational → Rational → Prop := fun stimulus threshold =>

       --     +------------------------------+ Qu'est-ce que c'est?  What is being stimulated?  Well, we are asking the compiler, given two rationals
       --     |                              | is the first one less than or equal to the second one? Or, another way to look at it, does the
       --     |                              | compiler thing the first number is less than the second?
       --     |          +---------------+ Where the hell did the threshold come from? Well, in this case this is the current "1" rational value.
       --     |          |               | Are we still less than one?  Why 1? *sigh* well, if we start with 1 and count, there are two ways we can
       --     |          |               | go.  We can iterate or subdivide. But, I am foreshadowing too much.
       --     V          V
    match stimulus, threshold with --
    | .zero _, _ => True
    | .number _ _ _, .zero _ => False
    | .number p1 i1 _, .number p2 i2 _ =>
      ((p1.truth = p2.truth) ∧ i1 ≤ i2) ∨ ((p1.truth ≠ p2.truth) ∧ i2 ≤ i1)
--   \                               .                                    /
--    +--------------------+---------------------------------------------+
--                         |
--                         +------   Covariant/contravariant comparison rule. Covariance is X=X.  Contravariance is X=Y.
--

-- So, time to get hard-core with some math.  I have been taking it easy on you because I want to ease you into how _nuts_ this ride is going to
-- get.  I am about to make some really crazy claims about concepts that normally are not mentioned together. Be patient, the lean will prove it
-- out and neither of you, technically, will not be able to prove me wrong. At no point will I demonstrate I am right. Only that the compiler
-- tends to agree with me. And the compiler tends to agree with _YOU the READER_ and the comments tend to disagree with _YOU the KNOWER_.
--
-- What I am building is an _argument_. Not a _proof_. Not certain you want to see a proof of this. The compiler is working hard making sure that
-- a proof could be written, if it had to be. I don't think it is actually writing one. I think it is just putting pigeons in holes.

-- And this _argument_ is going to be very compelling. This argument starts with Euclid.  Euclid demonstrated that math can be constructed from
-- finite objects alone.  He did this with a sequence of facts.  These facts map to rational numbers in very interesting and compelling ways.
-- That's all this says.  Given some fact, you can interpret it as a rational structure and draw a conclusion about area or length or volume or
-- whatever.  All other math can be reduced to this. A repeatable process to generate symbols that are _true_.
--
-- If you find the missal too confrontational, understand that I want you to really dig deep to really see if _your_ understanding of mathematics is
-- different from that of Lean and most definitly different from mine.  All I am doing is putting a bunch of symbols in a file.
--
-- I want to be clear that I am just claiming that the symbols before you behave as the concepts they describe for the questions I am asking the
-- compiler. As in, I _know_ how math works, and I am probing how _well_ the compiler can represent these concepts.

-- For instance, a sequence of numbers is a common useful construction of math.
/- CHORUS:
ME: I need a sequence.
COMPILER: Of counted numbers?
ME: Of next numbers.
COMPILER: That sounds the same.
ME: A sequence is not what we counted. It is the rule that keeps finding the next admissible thing.
-/
inductive Sequence  -- Bullshit meter ≈ 107
  | nil: Fact → Sequence
  | index :  Fact → Rational → Sequence → Sequence
        --             ^          ^
        --             |          |   | This should not be a controversial concept at all.  All I have done is describe how a sequence is written
        --             +----------+---+ down. r₁ → r₂ → ....  DO NOT GET COMPLACENT. I PROMISE I will say something outlandish in a second.



-- The thing that Euclid pointed out was that once you wrote something in the sequence, it could not change. It was _fixed_.  Not only that, but
-- someone else following the same process would arive at the same _fixed_ answer. And so, we continue with the covariant/contravariant comparison
-- rules. So that if I decompose the mapping, you decompose the mapping, and the compiler decomposes the mapping, we all agree on the concepts of
-- how it is compared.
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
     -- To count by _wholes_, you use identical truths (true=true or false=false).  This is Peano Couting 1 -> 2 -> 3 -> ...
     -- To refer to the _n-th part_, you use different truths (true=false or false=true) 1/2 -> 1/3 -> 1/4 -> ... This is size of a piece if
     -- you divided into _n_ pieces.
     --
     -- We have isolated our two kinds of counting process and can indicate to the compiler which one is which by the truth parity.  That way,
     -- when we ask the compiler to iterate, it knows whether we are counting by wholes or counting by parts.
     --
     -- So, before, we were actually working with the instance of a number. The number 1. We were not fiveshadowing, we were foreshadowing.  I will
     -- sixshadow for you so you can understand that you get the idea.  Will I sevenshadow?  Can I sevenshadow?
     -- Is it even possible to abstract something enough to sevenshadow?

     -- There.  I just sixshadowed.  When that coin drops, we will be discussing differential forms, antisymmetric residues, and other crazy
     -- nonsense.



-- Sequence limits had better be _well_ ordered. Not my idea, BUT we have hit a snag.  A potential flat tire.  A potential bomb.  Well-ordered limits
-- often require the Axiom of Choice. Infimum of sets is a slippery thing. Is 1 <= 0.9999999...?  Seriously, seems like 0.999 ∈ [1,2] for some
-- really weird reason I can't put my finger on.
def lt: Sequence → Sequence → Prop := fun s1 s2 => le s1 s2 ∧ ¬ le s2 s1
end Sequence

/- CHORUS:
ME: What you are looking at is overloading
COMPILER:  What I'm looking at is a lazy coder
ME: The whole idea is to have only one function that answers all questions
COMPILER:  That makes no sense at all, how does one function change the topology of its domain and range?
ME: Science looks for only one function, for some reason. I want to show science what happens when you force everything through one function.
-/
instance : LE Sequence where -- Bullshit meter ≈ 5
  le := Sequence.le

instance : LT Sequence where -- Bullshit meter ≈ 5
  lt := Sequence.lt

-- Now that we have some idea of a sequence, we can start to talk about limits. As much as it feels like a LimitProcess is a *geometric*
-- process, it is actually a *topological* process. The definition of a limit says that for every ball around a point, there exists an element of the
-- sequence strictly within that ball. That definitely shouldn't be right in general, but I am definitely not wrong, for I did not give you a norm,
-- now did I? I'm sure there is a metric, or at least a *gauge* for a metric, around here somewhere... Don't worry, when it shows up it will look
-- enough like an *L₂* norm that you won't be able to tell the difference. Literally, that's the argument. You can't tell the difference with
-- computation alone.

-- I hope you are starting to see that if you subtley change the shape of the objects in math by reordering the way in which they are described and
-- experienced, they cascade into each other in a very interesting way...  Yes, numbers are _experienced_.  Counting takes time.  One cannot count
-- to 5 without counting first to 4.

-- I mean, come on... the 1->2->3->4 computing engine and the 1->1/2->1/3->1/4 computing engine are the same up to direction of variance when
-- described this way. In fact, you should start to see how we can construct any Rational as a sum of these reciprocal steps, with a non-unique
-- ordering of boolean variables. This stack of orderings can then be further arranged by the size of the ball around the limit point they inhabit.
-- Good god, look at all the points we can describe! Are we dense, or am I dense, or is this argument dense?

-- Any hooozlebee, this gets you a localized process to find numbers.....
/- CHORUS:
ME: I need a limit process.
COMPILER: A sequence that approaches a value.
ME: Look at you.
COMPILER: That is correct, isn't it?
ME: Almost dangerously correct.
COMPILER: I dislike the adverb.
ME: The value is not the point. The approaching is the machinery.
-/
structure LimitProcess  -- Bullshit meter ≈ 185
    (Value: Type i)                   --                          | As you can start to see, the Value and Carrier parameters are universal.  What
    (Carrier: CarrierProcess Value)   --                          | is happening is as we provide the capability to compute ≤ and <, we further
    [DISTINGUISHABLE Value Carrier]   --                          | classify what the current carrier is trying to accomplish.  Is the compiler
    [ADMISSIBLE Value Carrier]        ----------------------------+ telling us we are counting by wholes or parts?  Or are we telling the compiler
    [COUNTABLE Value Carrier]        --                          | we want to count by whole or part?  Either way, really.  The fact you and I can
    where          --    ^                                        | see the carrier _too_ is the interesting part.
  --                     |
  --                     +------------ We are collecting quite the list of templates here.

  --    +----------------------- All structures include an instance of the previous structure. We are slowly building state in each of the classes
  --    |
  --    |                   +----- The indexing process above is there to indicate which element in the sequence are we trying to understand.
  --    |                   |
  --    V                   V
  indexing_process: IndexingProcess Value Carrier
  limit: Rational ---------------- The limiting process will provide a rational representation of the limit point of the sequence.  Either this is
                                -- provided at construction or inferred by the compiler, depending on circumstance.

  sequence: Sequence -------------+ This is the inductive element that labels this particular element of the sequence.  The label is a stack of
  --                              | boolean statements of the sort true = true or true = false.  Or, at least, a compiler constructed satisfiability
  --                              | problem that we are waiting for complete specification. Again, NP-hard problem sounds like a _you_ problem, not
  --                              | a _me_ problem. I don't need to run the compiler to believe this. This is my idea. I know what I am trying to
  --                              | show you.

  iterate: Sequence → Sequence := fun s => ---------------------------------+ So, this is the counting interface.  I often call this _tanging_ from
    match s with                           --                               | the adjective _tangible_.  It means, roughly, to select from a pile of
    | .nil f => .index f (Rational.zero f) sequence --                      | like things. Ultimately, I would like to help you _tange_ the correct
    | .index p rat _ => .index p (indexing_process.iterate rat) sequence -- | conclusion from thousands and thousands of lines of Lean.  Of course
--                                                ^                         | there is a similar interface called _funging_ from the adjective
--     Just pointing out to you that we are       |                         | _fungible_.  It means, roughly, to place in the known pile of like
--     only trying to count and compute ≤   ------+                         | things.
--     That is our only goal right now.


-- You see, the thing about math is you can use math to describe how a theorem prover works. Then you can use a theorem prover to prove you
-- implemented the theorem prover correctly. The neat thing about this is that numbers fall out of the construction of a logical theorem prover.
-- _SPOOKY_ numbers.  NGL, I thought I saw a ghost when I first saw it.

-- The architecture of the theorem prover is a bit unorthodox.  Rather than being a computer program, it is a computer meta-program. It is a stack
-- of labels in inductives, not real data structures.  At no point have we instantiated anything, we have only described a bunch of metaphysical
-- constructions that could, hypothetically, store these things. So, you can easily layer the description of a theorem prover through itself a few
-- times in a real sneaky fashion, couldn't you?

-- These are not the things themselves, but _representations_ of the things.  Which is precisely what we are trying to figure out about the compiler.
-- Or are they representations of representations of things?  Or are they representations of the act of representing things?  The compiler purports
-- to have a reasonable understanding of math.  So, I will now explain to the compiler how the modeling process works.  The mathematical modeling
-- process.  I have just explained to the compiler how it can talk to me about the concept of a number.  But, we have not yet agreed on what a number
-- actually _looks_ like.  The glyph "1", for instance.  That _looks like_ one. So, you are going to have to _see_ one in the process I am about to
-- describe. For those who are used to 'C', it would look something like this:

--              (void *) one (void &tanged_thing, void *state) {
--                   __internal_state = complete_desctruction_of_internal_state (tanged_thing);
--                   tanged_thing = ((MACHINE *)state)->funge(tanged_thing);
--                   return (void *) one;
--              }

-- We are going to implement this (but in a more PERL kind of type safety) in the most STRONGLY TYPED LANGUAGE.......... in the world!


-- It's going to take a minute. Actually, we should start more primitively, with _zero_.  I think we all agree on what that is supposed to look like.

/-
ME: I need it encoded.
COMPILER: Into what?
ME: A coin.                                                                      | You are probably expecting a class called ENCODED to carry
COMPILER: You want to reduce the limit process to a token?                       | the encoding in it.  And this is. Carrier is carrying the
ME: I want something that drops.                                                 | encoded limit process of the sequence.  All I did was put
COMPILER: Drops where?                                                           | the words in from the code as described and we already have
ME: Into the machine that pretends tokens are meaning.                           | _something_ that sounds like a _computer program_.
-/ --                                                                            |
class ENCODED  -- Bullshit meter ≈ 85        ------------------------------------+ Could it really be this easy?  Thousands of lines of Lean
    (Value: Type i) --                                                           | suggest otherwise.
    (Carrier: CarrierProcess Value)
    [DISTINGUISHABLE Value Carrier] --          | We can distinguish carriers, we know the carrier is "the next one" in some sense, and
    [ADMISSIBLE Value Carrier]      ------------+ we can keep track of how many carriers we have seen.  By describing what we want the carrier
    [COUNTABLE Value Carrier]       --          | to do, we are slowly giving it the capability to do so.
  where
  limit_process: LimitProcess Value Carrier    --------------------------+ We are at an interesting juncture.  We have described to the compiler
  encoding?: Sequence → Sequence → Prop := fun s1 s2 =>   --             | the inductive steps of the limiting process as a fairly nested recursive
    match s1,s2 with                                      --             | decision tree and we can _funge_ that process into a list of instructions.
    | .nil f1         , .nil f2       => f1 = f2          --             | This is the first step of a double-sided PDA (*smooch*) for those who
    | .nil _          , .index _ _ _  => True             --             | need the shadowing, looking at you _YOU the KNOWER_.
    | .index _ _ _    , .nil _          => False
    | .index f1 r1 i1 , .index f2 r2 i2 => (f1 = f2) ∧ r1 ≤ r2 ∧ i1 < i2


-- We now have the pieces of a _residue_, an origin and a limit away from that origin. This gives us _direction_ and _magnitude_! There, I told you
-- it was going to look like an _L₂_ norm. You ever use PCA to solve an Eigenvalue problem? Weird how the structure of PCA, Gram-Schmitt, GMRES,
-- Galelrkin methods all rely on understanding this residue. Something is projected to a space with a happy null-space and operated on. This
-- projection needs just 2 things.  A _direction_ and a _magnitude_.  Strangely this is also the interface for solving for the _value_ of
-- non-linear systems. Ya boy Newton figured that out.  So, which limit are we talking, the residue or the value?  Thankfully, one is covariant
-- and one is contravariant.

/- CHORUS:
ME: I need a limit process.
COMPILER: You didn't import calculus. Besides, don't you have one?
ME: Perfect.
COMPILER: Perfect?
ME: I do not need you to know calculus. I need you to know there is only one limit process.
-/
inductive Limit -- Bullshit meter ≈ 107 --                    | This is Fact number 5. 32 possible representable numbers.  Keep track, that 5
  | nil: Fact → Limit                   --                    | might become _VERY_ important later.  Meanwhile, we are slowly building 3 things
  | index :  Fact → Sequence → Limit → Limit --               | simultaneously.  A _set_ (ugh!) of numbers.  By a _set_, I just mean the descriptive
    --     -----                                       +------| label that describes the closure of the current inductive represented as a big
    --       |                                         |      | endian binary number, Whitehead style.  This simultaneously gives a representation
    --       |                                         |      | algorithm for counting naturals, but a representation algorithm for counting
    --       +-----------------------------------------+      | rationals. Remember, this episode is called _COUNTING_. Our goals are achievable.

namespace Limit -- Bullshit meter ≈ 48
def le: Limit → Limit → Prop
  | .nil _, _ => True                   -- So, are you going to let me get away with this? Smuggling in 0 being a converged digit? I mean, you let my
                                        -- friend Russell get away with it. lol.  j/k 0 is always less than anything. Converged or not.

  | .index _ _ _ , .nil _ => False
  | .index p1 seq1 _, .index p2 seq2 _ =>       -- There are two readings, and either are true.
    (p1.truth = p2.truth ∧ seq1 ≤ seq2) ∨ (p1.truth ≠ p2.truth ∧ seq2 ≤ seq1)
     --------------+------------------     ----------------+----------------
--                 |                                       |
--                 +---------------------------------------|--------------+ *YOU the READER* (the COVARIANT description):
--                                                         |              | The limit inches forward in sequence by whole.  You can skip as many
--                           +-----------------------------+              | in the sequence you want, but later values have larger values because
--                           |                                            | sequence base cases are usually denoted x₀ without loss of generality.
--                           |
--                           +------------+ *YOU the KNOWER* (the CONTRAVARIANT description)
--                                        | By convention, in proofs, once xᵢ → x₍ᵢ₊₁₎ is set, so is x_f(i) for all f: ℕ → ℕ.

-- I'm trying to build _TENSION_, PEOPLE! (the puns are just too much for me to resist.) It was Cauchy that gave us that pun.  Blame him.

-- At this point, you will see that we have a bunch of facts stacked up before we get to a number:

--                      Limit.index = Fact Fact Fact Fact Number,

-- four different ≤ computations based on what those four facts are. By the time we get to the number, we have one of 16 possible representations
-- of a number. And one of them is obviously 1 = T T T T T ... Of all *whole* numbers, 1 is less than or equal to all of them. On the other hand,
-- the smallest number we can represent is 1/2^n = F F F F F ... I wonder what ε_mach is on your computer? Anyway, as you can see, we can
-- successfully differentiate 1 from the smallest possible rational representation very easily. No calculus necessary.

-- Do *YOU the KNOWER* see _one_? I have explained it well enough for *YOU the READER*, I think. Can you find 0?

--  So, we assume the _smallest_ representable rational number is 0.  So 0 = F F F F ..... just like you expected. (0.0000000.... = 0, don't you
-- agree?) If we interpret numbers as _whole_ then there is no 0 rational representation. If we interpret numbers as _parts_ then there is a gap that
-- was identified -- by our good buddy Pythagoras and we can define _that_ to be zero. So, the ambiguity of _whole_ or _natural_ is about to get
-- exploited in very _weird_ ways.

-- Still well ordered without choosing.  Is it important I keep reminding you?  Could be. What about _i_ you say?  The complex limit requires
-- an *ahem* direction, of which we have a residue already.  Perfectly cromulent to talk about _i_ still. Oh yeah, it do be like that. Remember
-- we _do_ have a 1/2-spin carrier until _YOU the READER_ can convince me otherwise. _YOU the KNOWER_ will be able to ask _YOU the READER_ later.
def lt: Limit → Limit → Prop := fun l1 l2 => le l1 l2 ∧ ¬ le l2 l1
end Limit

/- CHORUS:
ME: I figure, since these are going to be very uninspiring for a little while, we make small talk.
COMPILER: How small?
ME: As big as you can.
-/
instance : LE Limit where -- Bullshit meter ≈ 5
  le := Limit.le

instance : LT Limit where -- Bullshit meter ≈ 5
  lt := Limit.lt

-- I suppose we should talk about superpigeons at some point. All of science relies on superpigeons and simultaneity. Einstein said so,
-- famously, when he and others described *SPOOKY action at a distance*. Obviously, he meant the spooky number that falls out of this device.
-- Obviously. The respectable name is Dirichlet's box principle: too many witnesses, too few rooms.
--
-- Chemistry does this in miniature. The law of definite proportions says the mess reduces to small integers: not because the liquid is simple,
-- but because the reading only has so many boxes. Think of the liquid as occupancy in a 3-d voxel grid. Wild, right? Stoichiometric measurement
-- is one of only *2* kinds of measurement here: covariant and contravariant. You either read through a carrier interaction, or you manipulate
-- the thing until its physical bounds answer back.
--
-- In this case, the superpigeon is the witness that refuses subdivision. Ordinary pigeons can collide, split the story, and hatch more cases.
-- A superpigeon will not. It almost collides, flees just enough not to merge, and stays close enough that the others begin to follow its path.
-- Zeno is probably responsible for this nonsense.
--
-- Anyway, what Dirichlet said, and what Poincaré made cosmic, is this: if you have finitely many boxes and too many states, recurrence is not
-- magic. It is bookkeeping with nowhere else to go. Send the superpigeons through the boxes often enough, and eventually the path has to rhyme.
/- CHORUS:
ME: I need a Cauchy process.
COMPILER: You have _two_ already, don't you?
ME: Careful, that has ontology on it.  And, I thought you didn't understand calculus.
COMPILER: Then what is it?
ME: The one where he described space in terms of itself.
-/
structure CauchyProcess  -- Bullshit meter ≈ 228
    (Value: Type i)
    (Carrier: CarrierProcess Value)    --                                                        | Among other things, Cauchy also described a
    [DISTINGUISHABLE Value Carrier]    -- We now have 4 different features we ask about in       | mathematical construction that measured change
    [ADMISSIBLE Value Carrier]         -- a carrier!  That is 16 different possible carriers     | in distance per distance.  This structure has
    [COUNTABLE Value Carrier]          -- so far.  Gotta catch 'em all!                          | lots of neat properties, such as having both
    [encoding: ENCODED Value Carrier]  ----------------------------------------------------------+ covariant and contravariant set of indices.
  where                                --                                                        | The real clever bit of the _encoding_ though,
             --          +-------------- As expected we have the "local" process                 | goes to Einstein who exposed variance as a first-
             --          |               that we can query about the ongoing limiting process    | class slot to take a token.
             --          V
  limit_process: LimitProcess Value Carrier
  value: Rational                 -- This is the current rational representation of the value
  accumulation: Limit             -- This is the actual limit point, or the place the compiler would put it, if the compiler would only stop being so
                                  -- lazy and just enumerate _all_ terms of the Taylor series of e^iθ. +1 +i -1 -i +1 ... How hard is that?

--                                           +-----------------+ What we are doing here is bootstrapping our limit with the process necessary
  iterate?: Limit → Limit := fun l => --     |                 | for the compiler to run in order to zero out the sequence counters and declaring
      match l with  --                       V                 | the following limit covariant (to be computed) or contravariant (looked up by name).
      | .nil f => .index f encoding.limit_process.sequence accumulation        -- lol. The names are for _YOU the READER_ to figure out and
                                                                               -- _YOU the KNOWER_ to roll your eyes at.
      | .index p seq _ => .index p (encoding.limit_process.iterate seq) accumulation
--                                                  ^
--                                                  |         | This is the index counter of the limit or the character pointer in a string or
--                                                  +---------+ whatever loop index your flavor of _for_ loop likes. Not certain I have actually
--                                                            | defined what "iterate" even means, but you get the idea.  It looks like this.


/- CHORUS:                                                        | When a function resolves algebraically, an identifier that used to name an
ME: I need a residue.   ------------------------------------------+ unknown value starts naming a particular one. What was discovered? That
COMPILER: A what?                                                 | some value *must exist*, or that the value *must be* *x*?
ME: What is left after the process almost explains itself.        | We draw the harder line: algebraic resolution requires that the particular
COMPILER: That is not a thing. Left over from what?               | value must exist in order for it to have exactly the value *x*. It can be
ME: From the difference between the story and the measurement.    | no other way; not that the value might be *y*, but that *y* is impossible
COMPILER: I do not like measuring leftovers.                      | by the nature of the value that must exist.
ME: Then stop making them.
-/ --
class RESIDUE ---------------------------------------------------------------------------------------------+ Sometimes, a computation is _pure_.
    (Value: Type i) -- Bullshit meter ≈ 103                                                                | It can be applied independent of all but
    (Carrier: CarrierProcess Value) --                 | We now have a dozen or so ways of encoding        | the most generous of assumptions. Add
    [DISTINGUISHABLE Value Carrier] --                 | the same number.  If we encode _x_ this way       | 1 to a number, for instance.  But,
    [ADMISSIBLE Value Carrier]      --                 | and we encode _y_ that way, the that-ness of      | it isn't free to add 1.  It costs more
    [COUNTABLE Value Carrier]       --                 | _y_ stays roughly independent of the this-ness    | and more to do because you need to make
    [ENCODED Value Carrier]         -------------------+ of _x_. Both stored in the same number.           | more and more marks to differentiate.
  where --
--                      +------------------------------------------+ At this point, we can apply any of our different Cauchy processes in at least
--                      |                                          | a zillion different ways to apply the logic to discuss how local locality really
--                      V                                          | is.  Locality is defined to be only one superpigeon per box, according to Cauchy.
  cauchy_process: CauchyProcess Value Carrier  --
  representative? : Limit → Limit → Prop := fun a b =>  --------------------------+ This might take a second to unpack, but basically the idea here
    match a,b with --                                                             | is that there is only 1 representative per neighborhood, so that
    | .nil f1          , .nil f2           => f1 = f2 --                          | the superpigeons are that singular representative. Really, ask
    | .nil _           , .index _ _ _      => True    --                          | someone else why pigeons.  *YOU the KNOWER* need to see that this
    | .index _ _ _     , .nil _           => False    --                          | says all limits start from the same origin.  *YOU the READER*
    | .index f1 s1 l1  , .index f2 s2 l2   => (f1 = f2) ∧ s1 ≤ s2 ∧ l1 < l2 --    | can let the code explain what is going on.


-- At the risk of flaunting my _creative license_ again, I am going to model the average number. That's right, kings and queens, this is an argument
-- that needs perfectly normal and average numbers to not only exist but to be so prolific as to be universal. But what does it mean to be an average
-- number?

-- An average number is one most people would recognize.  7, for instance, is a pretty average number. π is getting a _little_ exotic, but I feel
-- like enough people might recognize that _as_ a number if they can't place the ratio.  In this case, I am going to say the average number is the
-- one most people would recognize, no matter how many localities they visit.  So, I will assume some numeric literacy and say numbers should be
-- made *only* of digits. Letters, *especially those from other alphabets*, are... dubious. It really isn't clear what π + 1 is, since you never
-- really can know all the digits. And the fact that addition becomes *cumbersome* in a way that is... measurable... means these symbols probably
-- shouldn't be part of our average number. Just numerals. A possibly endless list of numerals (lol, *YOU the KNOWER*).

-- The compiler can now talk about 32 different run-of-the-mill normal numbers.  Thats more normal numbers than we know about!  I'm sure it picked
-- the best normal numbers to represent. We have 0 and 1, but those aren't normal, at least not in this representation.  However, the nonunique
-- representation of numbers allows for 0 and 1 to be normal, turns out.  To lazy to show you, trust me on this for now, we will come back to this
-- idea as something that obviously had to be right.

/-
ME: I need a sample.
COMPILER: A point from the process?
ME: A bite from the residue.                                                 | The law of large numbers, the bell curve, the Gaussian distribution,
COMPILER: That sounds unsanitary.                                            | these are not laws of mathematics but laws of residues.  Mathematics
ME: Measurement usually is.                                                  | sees them as the chain rule and Stokes theorem. Conservation laws of
COMPILER: What does the sample prove?                                        | variations. Symmetries. Proofs are made of symbols that are subject
ME: Nothing. It gives the next measurement a foothold.  ---------------------+ to the laws of nature Gauss showed us through the lens of math.
-/
@[reducible]
inductive Sample -- Bullshit meter ≈ 150            -- This is the admissible symbol for a single normal number
  where

--         +---------------------------------------  We are having a bear of a time starting from scratch
--         |
--         |                    +------------------+ Our friend Dirichlet demonstrated that we can't get
--         |                    |                  | out from under the need for an initial superpigeon
--         |                    |                  | to begin with.
--         V                    V
  | initial_condition: Fact → Limit → Sample

  | signal_response: Fact → Limit → Fact → Limit → Sample → Sample  --
        --            ^              ^                                               +------------------------------------------------+
        --            |              |                                               |   The Controversy of Mathematical Containers   |
        --            +----------------------------------------+                     |   --- ----------- -- ------------ ----------   |
        --                                                     |                     |                                                |
        -- Every number can show up, and should,  -------------+                     |  There are bags, and lists, and trees that     |
        -- eventually since they all have to be different.                           |  grow upside-down.  There are sets and multi-  |
        -- Except they can't.  However, we can very carefully _describe_             |  sets.  Maps and multi-maps.  Queues, deques,  |
        -- the _set_ of numbers that agree with the Facts.                           |  tables, and other steganographic methods of   |
        --       ^                                                                   |  hiding data in structures.                    |
        --       |                                                                   +------------------------------------------------+
        --       |
        --       +------------------ I define _set_ to be the group of concepts that are modeled by words.
        --                           Now, we try to avoid using the "S" word at all costs as being
        --                           near meaningless drivel that holds any sort of nonsense.  I deal in Facts.

-- So, you should realize at this point, we are going to implement ≤ and < for this guy.  The samples are well ordered.  In this case, there are two
-- possible things that can be compared, which limit comes before which in time and which limit is bigger than the other one.  Well, we can define
-- them to be the same for the first fact and contravariant for the second fact.  So, depending on the variance of the facts, ≤ while either return
-- ≤ on the first limit or the second limit.  Contravariant first the covariant second, or covariant first then contravariant second.  Why not both?

namespace Sample   -- Bullshit meter ≈ 105
def le: Sample → Sample → Prop
  | .initial_condition f1 l1, .initial_condition f2 l2 =>
    (f1.truth = f2.truth ∧ l1 ≤ l2) ∨ (f1.truth ≠ f2.truth ∧ l2 ≤ l1)
  | .signal_response f1 s1 _ r1 _, .signal_response f2 s2 _ r2 _ =>
    (f1.truth = f2.truth ∧ r1 ≤ r2) ∨ (f1.truth ≠ f2.truth ∧ s1 ≤ s2)
  | .initial_condition f1 l1, .signal_response f2 l2 _ _ _ =>
    (f1.truth = f2.truth ∧ l1 ≤ l2) ∨ (f1.truth ≠ f2.truth ∧ l2 ≤ l1)
  | .signal_response _ _ _ _ _, .initial_condition _ _ => False   --+ This shouldn't happen without serious _strain_.  The compiler thought
                                                                  --| _true = false_ somewhere... Oh, I do demonstrate something like this
                                                                  --| later when we throw away most of the proof-verification horsepower of Lean
                                                                  --| and only use propext and rfl.

-- I will argue that the munge ordering we just gimmicked up is actually pretty well ordered.
def lt: Sample → Sample → Prop := fun s1 s2 => le s1 s2 ∧ ¬ le s2 s1
-- If you are reading this, Lean accepted my argument. Mathematicians hate this one trick.
end Sample

/- Chorus:
ME: The wheels on the bus go round and round!                                                        | Gödel recognized that writing with pencil
COMPILER: Round and round! Wait.. The bus?                                                           | and paper resembled the mechanical
ME: We agree that numbers are just a list of numeric glpyhs -----------------------------------------+ reproduction of ideas on the page.
COMPILER: No, a number is either the wire on the bus or the decoded index into the tensor.           | All he did was describe it and the description
ME: Round and round!                                                                                 | is the result.
-/
instance : LE Sample where   -- Bullshit meter ≈ 5
  le := Sample.le

instance : LT Sample where   -- Bullshit meter ≈ 5
  lt := Sample.lt

-- So, why the name Sample?  Well, because we are getting sample numbers from the compiler. That's why. The compiler may or may not care about
-- normal numbers.  What it cares about is the typical number found in context.  For math, the typical number can be defined numerous ways.  The most
-- onerous, though is _normal_.  Our limit must successfully model _ALL DESCRIPTIONS_ of numbers, not the numbers themselves.  See?  This isn't a
-- proof, it's an argument. Lean just makes sure I model all the relevant numbers _precisely_. Under very, very specific circumstances, the
-- definition above is the most descriptive thing left to describe about a normal number. It is, itself, a random sampling of irrational numbers.
-- What set of circumstances?  Well we have a pile of Facts already in front of us....

-- I love just throwing terms of art around in a blender like I am Bill Burroughs. In fact, the explanation so far has been far to straightforward
-- to follow and much of the nuance of the argument has already been missed.  Like the stories of Burroughs, it isn't the story so much the story
-- on the page, but the story of the whole.  Complex things are complex.  You need all of this to understand all of that, but you gotta at least
-- understand a lot of that to even talk about this.

-- Speaking of... If you made it this far, you must be wondering _w THE ACTUAL f_?!?

-- Well, you may recall our friend Kurt (he's a goodfella) said something about how hard it was to prove something about a system from within the
-- system.  So, let's not even try.  Instead, let's try to make the most outlandish _yet technically correct_ claims about the system and see what
-- the system does to _respond_ to those claims.

-- Introducing the concept of _INFORMATIONAL STRAIN_.  That is what you are under right now and I am about to strain the information all the way out.
-- For those who do not know what a stress-strain curve looks like, go look it up.  We are _clearly_ in the linear response zone of mathematics right
-- now.  We will completely model this stress and strain, which means _yes_, we will be developing the stress tensor, and _yes_ we will be dealing
-- with Navier-Stokes, and _yes_, you will see that the _covariance_ of General Relativity will never settle at the boundary with the
-- _contravariance_ of Quantum Mechanics, no matter how much energy is there.

-- I take that back, 0 energy works. Du = 0 is trivial for D = 0.  Or ∫f(t, x, f_x) = 0 for f = 0. Depending on if you are _weak_ or _strong_, of
-- course.  I'm _strong_ so, give me the D.  Oh. Scratch that.

-- Speaking of, if you have never used the Gateaux derivative of a variational function to derive the Euler-Lagrange equations (tell me you spent 10
-- years getting a highly specialized PhD without telling me you spent a decade pushing Taylor series around), you have one of two choices now.
-- First, go learn it then you can interact with the argument better.  Or second, watch me derive it from _true=false_ in the craziest way you have
-- ever seen.                       --                                                                    ------------
                                    --                                                                          ^
                                    --         +--------------------------------------------------------+       |
                                    --         |                                                        |       |
                                    --         +------ Informational strain, true ≠ false               +-------+

-- Actually, there is a third choice.  I just chose one of many paths through this maze.  There are many. As we walk past places where you think I
-- choose the wrong next abstraction, follow your thoughts. These are just words. They mean what you want them to mean. Only the compiler has the
-- dictionary for the words in this file.  These aren't our words.  This is source code. Finally, this is America and you can use words however you
-- want to.

-- It will get inelastic soon.  The definitions will get more rigorous.  The noose is going to tighten. And you will find it ever _harder_ to prove
-- me wrong even though I can't possibly be right. Miss me with that incompleteness noise. I ain't provin' nuthun. I'm just demonstrating to you that
-- this cannot be proven false.

-- Most importantly, I believe that we have taught _YOU the READER_ to count.  Counting is a process that simultaneously indexes the value it sorts.
-- Actually, _any_ process that simultaneously indexes while it sorts counts.  We didn't implement any of them, just described how they must work.
-- What we do have is the ability to make a bunch of symbols and we can, in fact, identify two of them by sight. Not only that, we have an inductive
-- that conveniently provides two limit points at each step. I suggest we let those two representations mingle so that one means the other.

-- You follow me?  When you see TTTTTTT....., this is the first number in the limit and when you see FFFFFFF...., that is the second.  But, this
-- could take an uncountable amount of time to finish, so let's just short cut this by saying that we could either be counting up or down, and that
-- represents either TTTTTTT..... or FFFFFFFF.....

-- I feel like I just explained this somewhere... Oh yeah, to the compiler.  See the definition of Number. When you see .one, we are counting, um,
-- up.  And when you see .zero, we are, um, not, I guess.  Could go up or down. Don't know.  The compiler knows, but we don't. Throwing in
-- contravariance.  This gives the following representation:

--  +-+  +-+  +-+  +-+   An alternating sequence of T F in phase.
--  | |  | |  | |  | |
--  V V  V V  V V  V V
-- (T=T)(F=F)(T=T)(F=F)... == TTTTTTTTTTT....   --- This is a clock
-- (T=F)(F=T)(T=F)(F=T)... == FFFFFFFFFFF....   --- this is a clock complement
--  ^ ^  ^ ^  ^ ^  ^ ^
--  | |  | |  | |  | |
-- -+ +--+ +--+ +--+ +-  The alternating sequeneces are out-of-phase by 1.
--
-- In digital signal processing, this is called a clock complement. Two clocks working in synchronozation but opposite phase. So, a _clock_ can
-- recognize truth and a _clock complement_ can recoginze falsehood.  1 and 0.  T and F.  That's 3 different meanings from just 1 bit of information.
-- Well, not 1 but, I think we have 5 or 3 right now, hard to tell.

-- Using the clock or the clock complement will prevent us from understanding the truth until there is a reason to.  In this way, we cannot get
-- caught in a meta-trap of over-expessive self-reference.  One cannot know if one is right. Otherwise, one might find oneself inconsistent.

-- *tsk* *tsk* _and that just WOULD NOT DO_ would it?

-- Seriously it would stop "doing," as it were. What we need to do now is understand if we want to label the first limit value of a Sample the
-- covariant repsonse or the contravariant response.

/-
ME: I need an observation process.
COMPILER: We sampled the residue.
ME: Yes, but nobody saw us do it.
COMPILER: I am the compiler.
ME: You produced the sample. Consider this a deposition.
-/
structure ObservationProcess   -- Bullshit meter ≈ 313
    (Value: Type i) --                                                | A residue allows us to talk to the compiler about something that stays true
    (Carrier: CarrierProcess Value) --                                | after the compiler no longer pins the Fact.Truth bit in place.  That residue
    [that: DISTINGUISHABLE Value Carrier] --                          | stays on screen and practically _SCREAMS_ a very contraversial number at the
    [ADMISSIBLE Value Carrier] --                                     | top of its lungs and the compiler is no longer at work.  The Fact.Truth is
    [COUNTABLE Value Carrier] --                                      | not not true anymore, it is impossible by the very nature of how the compiler
    [ENCODED Value Carrier] --                                        | works. Semiotics are all that exists in comments.  These doubly so.
    [RESIDUE Value Carrier] ------------------------------------------+
  where
  cauchy_process: CauchyProcess Value Carrier
  before: Limit  --+-- I will call before _contravariant_
--                 |
  after: Limit   --+-- I will call after  _covariant_
--                 |
--                 +--+ I would hope you agree that going backward _in time_ is quite contravariant. If not, I would suggest sliding over to the next
--                    | universe where the left-hand rule seems to dominate.  Just wait a tick. It'll come around on the next pass.


-- We want to grab this information the compiler is telling us.  Something is before something else and we need to know the relative variance
-- between the two. Does the compiler think they covariant or contravariant?
  relative_variance : Prop :=
      match before, after with
      | .nil f1, .nil f2 => f1.truth = f2.truth
      | .index f1 _ _, .index f2 _ _ => f1.truth = f2.truth
      | _, _ => False
-- By golly, that just might be decidable! This is the mechanism behind the One Time Pad (tm). I wish the compiler _GOOD_ _LUCK_ finding something
-- that looks exactly like math but is actually just a random sequence of bits! This is _completely_ orthogonal to the proof, I just wanted to show
-- you that we are looking for patterns in pure noise.

  iterate : Sample → Sample := fun s => match s with
      | .initial_condition f l =>
          -- Transition from a static point to a signal response pair
          .signal_response f l f after (.initial_condition f l)

      | .signal_response f1 l1 f2 l2 s2 =>
          .signal_response f1 l1 that.fact after (.signal_response f1 l1 f2 l2 s2)
  --                        ^  ^     ^      ^
  --                        |  |     |      |
  --                        +--|-----+------|---+ This encodes relative variance since that.fact is always TRUE, even if it is false.  The
  --                           |            |   | documentation is clear on this. I'm not certain the _code_ is all that clear, though...
  --                           |            |
  --                           +------------+---+ We tell the compiler that _after_ comes after _l1_ and hide our begin state from the compiler.
  --                                            | Now, the compiler and I have different states that I can tie together.  I can make a binary number
  --                                            | represent vague internal state of next on the compiler! And, the compiler will store them both for
  --                                            | me. And, they are both totally opaque to the compiler as well!

  -- Let's talk about qualia for one second. Now go google it.  You and I just shared the concept of TIME with the compiler.  TIME is a quality.
  -- No idea what that quality _actually_ is, but the compiler and I can both have different names for it and recognize it now. We also share a name
  -- for it as well, cuz I just made it for the compiler above. I'm pretty frickin nice like that.

  -- So, numbers observed this way indicate a certain arrow of time. Something happens before something else happens. Or, rather, whenever the
  -- compiler executes a behavior, time passes.  For you.  Not me. I'm writing comments.  See?  Relativity... Simultaneity...  You don't see it yet?
  -- *YOU the READER* sees it (the words I wrote), *YOU the KNOWER* doesn't believe it due to the imprecision of the words, but you see it.

  -- We will come back to this later after we agree with the compiler what the symbols for calculus look like. Back to explaining to the compiler how
  -- time works. To do so, we have to ask the compiler what it thinks time looks like to us.  Well, I will let the inductive type be the clock for
  -- the compiler.  Inductives are always true for the compiler _and_ the compiler needs to do work _and_ the compiler can distinguish them _and_
  -- the compiler will make sure that they compile, _and_ one _MUST_ come before a bigger one _ALL AT THE SAME TIME_!

  -- Same carrier, btw.  TRUE=TRUE. That is the only recognized symbol of the application and it lives in the DATA page, inaccessible to change.
  -- And, still nothing up my sleeve.

/- CHORUS:
ME: I need different.                               | Just because you can distinguish something doesn't mean there are _two_ of them.  In a ewer
COMPILER: class DISTINGUISHABLE                     | of water, how many glasses are there? 1, 2, 75?  Depends on lots of things, but one thing it
ME: From itself after the instrument answers.       | does _not_ depend on is the _shape_ or the _count_ of water, neither of which exist.
COMPILER: class DISTINGUISHABLE --------------------+
ME: I counted two as well                           | So, we have to tell the compiler how to make 1 water into 2 waters.
-/
class BINARY  --  Bullshit meter ≈ 141
  --     ^
  --     |               So, DSP.  We can assume a covariant/contravariant tick/tock for creating
  --     +-------------- the clock complement.  As I mentioned above, before is the covariant representation
  --                     and after is the contravariant.

    (Value: Type i)                       --      +---------+ Looking like we can ask a bunch of questions about what it is we want to make binary.
    (Carrier: CarrierProcess Value)       --      |         | In this case, with water for instance, there are 2 easy values to take, empty and full.
    [DISTINGUISHABLE Value Carrier]       -- <----+         | This can leave extra water in or out of a glass (a "full" glass, but not enough water,
    [ADMISSIBLE Value Carrier]            -- <----+         | for instance).  What gets left over isn't part of the _shape_ or _amount_ or even
    [COUNTABLE Value Carrier]             -- <----+         | _pressure_ for gases.  Matter prefers not to measure itself.
    [ENCODED Value Carrier]               -- <----+         |
    [RESIDUE Value Carrier]               -- <----+         | So, how do you measure a gas? You surely can't look at it can you? The _RESIDUE_.

  where
  observation_process: ObservationProcess Value Carrier -----+ This is looking at the _RESIDUE_, as well as the encoding, the count, and the
                                                           --| characteristic under observation (what distinguishes it)

  zero : Limit   -- Empty       | This is a very rare place in the code where you can point to something and go AHA! This is the concept
  one  : Limit   -- Full        | of a variable in the compiler. 0 is the space uninhabited by the bit; 1 is the space inhabited by the bit.
  bit  : Sample  -- Residue     | See? The compiler will not allocate space for us, but it will happily allocate space for itself.

  -- The _bit_ is a native thing the compiler likes to think it knows something about _directly_.  It is a very easy place to ask the compiler
  -- about its opinions about where these two bits are the same or different.  This doesn't ask if they are one or zero, those are limits that
  -- you and I chose for the two bits the compiler sees.  *YOU the KNOWER* should have a good understanding of the logic the compiler is capable
  -- of and how this is just wiring up a canonical satisfiability problem.  Did you get that *YOU the READER*? I feel like this meta-programming
  -- is about to get a little more _meta_.
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

-- It takes honest-to-god, real wall-clock time to create the contravariant interpretation of the covariant representation. The important thing is
-- that a BINARY Fact is TRUE, regardless of the facts at hand. This is an *ACTUAL* representation of a binary number that allows counting in wholes
-- or parts! Also, I have an inside joke.

-- That's what I have with the compiler now.  We can wink at each other and say, yep that's "true" alright. *nudge*  *wink*  *wink*  *nudge*  *nudge*
-- Say _NO MORE_!

-- And now, we have an inside joke, *YOU the KNOWER* and I!  *YOU the KNOWER* and I can laugh behind the compiler's back about how something is or is
-- not "true" while it thinks it is. I am so sorry *YOU the READER*, by construction we can have no inside joke. But, we've always had that.  Since
-- the very beginning.
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


-- We have it now set up that an ObservationProcess explains to the compiler how we order things in a certain way (the way I like to call
-- "temporal order").  The BINARY class is how the compiler tells us which is covariant and which is contravariant. Neither of us know what is
-- really true anymore.  And, that's the point.

-- OOOOOooh no he didn't! He just broke Gödel's ankles taking it to the hole. BOOM SHAKALAKA! Knowably true statements, like Nats, are for suckers!
-- Please understand, *YOU the KNOWER*, this isn't personal. It just doesn't matter what you know to be true. It isn't that I find your objections
-- wrong; I want to show you that your belief about this proof has no bearing on what it demonstrates. It will still demonstrate that number
-- to you, believe it or *NOT*. And, the next several thousands lines will just be demonstration after demonstration of the rigor of this very
-- paragraph.

-- Actually, we are not out of the woods yet.  The compiler can _still_ figure out what I think is true.  Once I have it completely befuddled, then
-- I will set about creating a Hilbert space from absolutely thin air.  Not all at once, mind you. In very, very, _VERY_ small baby steps to make
-- sure we can explain to the compiler what a Hilbert space is purely from our little game of contravariance.

-- So, puzzle for you.  How can the compiler know what I think is true?

-- ...

-- Bueller...

-- Bueller...

-- Well, it can figure out what I think is contravariant about the third time I show it something.  The stack of distinguishing features already
-- encode _a lot_ about how numbers work.

-- ....

-- Anybody?

-- The initial condition.

-- The compiler can work it out from the initial condition.  I successfully hid my internal state, but I also frickin' told the compiler how I
-- built it.  Duh.  This Lean thing is smart, let me tell you.  Won't give me half an inch of room on this. We need to make the initial condition
-- unique to the measurement so that the initial condition does _NOT_ give the entire number away, just the current 2 or 3 bits. And so, we consult
-- the Book of Shannon, chapter 2 versus 71-82

--       And in those days, communication was analog and the peoples of the world did suffer mightily.
--           Upon a swamp in New Jersey, cometh a prophet who did thus declare to all the peoples and
--              Nets and Giants the good news of information.
--       To those sundry assembled he did spake the words ``BEHOLD! For I give you knowledge of information.''
--           So, thusly it was _described_ and _measured_ in full.
--                                     The Word of Communication.

-- And our old testament reading is from the Book of Green Chapter 3 versus 14-15:

--      Thus, in the days of Variance, it was said of the flow that IT DID NOT _CROSS STREAMS_ with its BRETHREN.
--             That the initial condition was THE TRUTH and THE ONE signifier of the path.
--      Lo, and thus spoke Mandlebrot of the beauty Lorentz organized in chaos using the tools of Green
--         "But for grace of sensitive dependence on initial conditions, does the coastline
--            Remain incommensurate and beautiful."
--                                     The Word of Communication.

-- The old ways are truly _the best ways_. Let me help the compiler with one last thing about time to get started.

-- THE LAW OF GALILEO: The signal _ALWAYS_ comes before the response.

/- CHORUS:
ME: I need a trial.
COMPILER: OYEZ! OYEZ! All those with business before this court step forward an be heard!
ME: When did you get a sense of humor?
COMPILER: I am just here to mediate the demonstration, I refuse to take part.
ME: There can be no trial without a judge.
-/
inductive Trial  -- Bullshit meter ≈ 150   ------------------------------------+ At the heart of science is the repeatable trial.  Galileo
  | hypothesis: Fact → Sample → Trial --                                       | demonstrated it was not enough to perform the act, the act must also
  | signal_response: Fact → Sample → Fact → Sample → Trial → Trial --          | be described well enough to be performed by _someone else_. This
                                                                        -------+ program is the description of the process of description that
-- Galileo demonstrated as the most important aspect of science. Hooke and Galileo extended the human senses _scientifically_ both into
-- microscopy and cosmology.  They described _instruments_ that described _phenomena_ in repeatable fashion.  We are describing the description of
-- that.  The repeatable trial starts with understand what a scientific trial is.  It is either an untested hypothesis (the fact that we expect
-- the scientific sample to be _x_), or it is a recorded stimulus-response:  _this_ stimulus lead to _that_ obsevation.  Seems like variance will
-- be doing some work here.

-- So, what does ≤ mean for a Trial? It is the order in which the samples were taken.  You know, like a Number. In this case, all we care about is
-- comparing the response.  This is how "loud" is the response.  Its _volume_, lol.  Told you it had volume. Now, I need to put a "ratchet" here so
-- the the compiler realizes that it cannot rewind a trial.  Once experienced, _it cannot be unexperienced_. You may talk about it, inspect it, but
-- _you cannot experiece it again_. Nor _can you pretend it didn't happen_.

-- This my definition of time.  My personal definition of the years I spent trying to understand the _speed of light_ based _physical limitations_ of
-- total ordering. They must _exist_. I will show you. Of course they do. The machine is about to calculate them from first principles. That means
-- we also have to teach the machine General Relativity while showing it QED and making sure we don't agree on what is "true" or "false".

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

/- CHORUS:
ME: Ditto
COMPILER: Oh, I can ditto if you want.
ME: It almost seems like you were constructed to help me prove this.
-/
-- High syntax corn syrup: This stuff is __BAD__ for your health. You only get __REALLY__ confusing code out of it. Do not recommend.
instance : LE Trial := ⟨Trial.le⟩  -- Bullshit meter ≈ 8
instance : LT Trial := ⟨Trial.lt⟩  -- Bullshit meter ≈ 8
-- So delicious......

-- The thing about time is, the compiler has no internal experience of it that it just shows you.  And most people think of compilation as a
-- single step, not realizing that the code emerges after TONS of serial transformation. So, the compiler doesn't have a before and after barrier
-- like we do, it has to pretend one exists.  And we taught it how. But, that's the compiler's barrier not ours, these things happen at the same
-- time on the page, well almost the same time.  *YOU the READER* and I can exploit this (*YOU the KNOWER* might be able to now).  *YOU the READER*
-- and I will will treat these two numbers as _SIMULTANEOUS_.  So, time-ordered in the compiler, and simultaneous between me and the reader.

-- So, is this amplitude-frequency or frequency-amplitude?  Depends on the initial condition.  I propose we don't explain that to the compiler.  That
-- will be our inside joke to obfuscate our understanding of what makes math hard. *YOU the READER*, we just constructed an inside joke in front of
-- the compiler, but it isn't entirely inside because *YOU the KNOWER* is going to try to spoil it for you.  20,000 lines of Lean should stick a sock
-- in that, eventually.

-- **HOT TAKE ALERT**
-- What makes physics hard?  An obfuscated understanding of what makes math hard.

-- What does that mean? It means we have an _honest-to-GOD_  __ψ__ function!  That's right compadres, what we are decoding is a ψ fuction.  I know
-- you don't see, the definitions probably have you spun around. Yeah. I don't believe me yet either and I wrote it.  Give me a bit more runway.
-- Actually Lean will build the runway whether or not you like it. That's just it.  I'm not in the plane, you are. Both of you. Time has already
-- passed for me.

-- Where were we?  Oh yeah, we had just finished up a binary number. Not binary numbers. Number. 1. That is the binary number.  Or 0, if you like.
-- Only need one of them. We can hide the other in the initial condition. In fact, that is our (me an you) initial condition.  TTT... means 1 except
-- when it means 0.  Got it?

-- Now that we have a binary number, either 1 or 0. (not a binary number like 10₂.)  I'm not certain *YOU the READER* understand how to count to 2.
-- So I will explain what I am explaining to the compiler in a language we both can understand, but not all of us simulaneously.  Remember, this
-- takes your time not mine. I only have to write this once. Every time this gets read, it accumulates the time spent reading it.

-- I want you to understand how naive my notion of time is here.  If you have a clock nearby, look at it.  Now read this sentence.  Look at the clock
-- again.  See? Time passed. In a repeatable fashion. A repeatable fashion that can be explained in a precise enough fashion for a result to be
-- _anticipated_.  You read a sentence, an _estimable_ amount of time passes. This is the _concept of time_ I am explaining to the compiler right
-- now.  We will be talking about how this also describes the relative concept of time that underlies the Einstein Field Equations in the not too
-- distant future.

-- You see we have to.  We are measuring how well the compiler can figure that out from the math. If we do the math and the compiler does the math
-- and we get the same answer, then we can explain to each other that the mathematical process has a name to it and memoize the result right on
-- top of our covariant/contravariant clock-based, chainsaw juggling, Jenga stack of classes.

/- CHORUS:
ME: I need a repeatable process. --                                  | Inherently, science is the art of asking questions.  In actuality, scientists
COMPILER: Run the trial again? --                                    | _SUCK_ at answering questions because of how _WELL_ they can ask them.
ME: And have it still be the same kind of trial. --                  |
COMPILER: Same result? --                                            | Being able to ask better and better questions could lead to easier and easier
ME: Easy. Same question.   ------------------------------------------+ answers, if that's your definition of the word better.
COMPILER: That seems weaker.                                         |
ME: It is stronger. Results are cheap. Questions need fixtures.      | I prefer a different, harder to describe version of better: repeatable. But,
-/ --                                                                | at what point does repetition become the pattern sought?
structure RepeatableProcess  -- Bullshit meter ≈ 296
    (Value: Type i)
    (Carrier: CarrierProcess Value)
    [this:DISTINGUISHABLE Value Carrier] --    | Clicking a tally counter is a repeatable process guaranteed to produce something different.  It's
    [ADMISSIBLE Value Carrier] --              | defining characteristic is sᵢ ≠ sⱼ unless i≃j mod k, the class of permutations. This is a different
    [COUNTABLE Value Carrier] --               | question until it is the same.  It takes the compiler _time_ to determine how long clicking a tally
    [ENCODED Value Carrier] --                 | counter can stay a repeatable experiment before it just becomes repetition. While repeatable
    [RESIDUE Value Carrier] --                 | experiments are the backbone of science, repetition can serve other masters.
    [BINARY Value Carrier]    -----------------+ These are the two classifications of questions: repeatable or repetition.
  where
    --     +-------------------+------------+-----+--------------+ This is an example of absolutely _ravishing_ the recursive structure of
    --     |                   |            |     |              | description.  All structures carry the previous structure orthogonally and depend
    --     V                   V            V     V              | only on a Value and a Carrier.  Once you learn to see the next one, you have
  observation_process: ObservationProcess Value Carrier        --| finally learned how to count.

  stimulus: Sample   --| The descriptions of Galileo and Hooke contained _samples_ of the observations. Careful drawings, careful specifications,
  expectation: Trial --| careful explanations.  They also contained descriptions of process that were rich enough to be transported through time.

  iterate: Trial → Trial := fun t =>
     match t with
--                --    The co/contravariance trick +------------------------+
--                --       Appears to be letting us |                        |
--                --       register True Facts (tm) |                        |
--                --             with the complier! |                        |
--                                                                           V
     | .hypothesis fact observation => .signal_response fact observation Fact.Truth stimulus expectation

--                          +---------------------------+-------- Watch the covariance!  Remember the
--                          |                           |         clock will tick when we do this, flipping
--                          V                           V         the variance.
     | .signal_response _ _ f2 s2 _ => .signal_response f2 stimulus this.fact s2 expectation -- We mark this fact as (s2 is the expected response).
--                          ^   ^
--                          |   |         | So, given some response by the compiler, we can guess at its Signal inside the compiler. See? The
--                          +---+---------+ compiler is sending us its state in the first two parameters, but we can't understand it. We are telling
--                                        | it what we _expect_ the stimulus to be.  If this compiles, then the compiler agrees we would be
--                                        | describing a computation.

-- ** SCOREBOARD:  THINGS I BELIEVE I HAVE DEMONSTRATED, THUS FAR: **
-- 1) *YOU the READER* knows how to count.
-- 2) Lean is better at this than any of us.
-- 3) *YOU the KNOWER*'s opinion on the veracity of the claims is immaterial as the only claim is that the argument is consistent, not necessarily
-- true.

-- You think building a counterexample is hard now, just wait.  I have only _BEGUN_ to pile on ridiculous classes. All I need to provide to
-- instantiate is a Fact and a Carrier. That is it. I would do it _RIGHT_ _NOW_, but I don't wanna. But this isn't about me. It's about science and
-- how to _APPLY THE SCIENTIFIC METHOD_. I think Weir said it best when he said I'm going to "engineer the shit out of this."

-- So the oldest G. Galileo was pretty clear about how an experiment was supposed to work. You were supposed to produce a _repeatable measurement_.
-- That's exactly what a trial is, a repeatable measurement:  given this stimulus, you should _then_ see this response. It encodes _time_.   Not some
-- variable domain of f(t).  The actual tick/tock of a clock. Think about it.  What is a second?  Please explain how that is not tick/tock. The
-- electron repeatably and on queue (sic) does its thing.  The important part about it is: _on cue_:  the time between events is considered
-- _constant_.
/-
ME: I need REPEATABLE.
COMPILER: You just defined a repeatable process.
ME: Yes.
COMPILER: So this repeats the repeatability?
ME: But I repeat myself.
COMPILER: That is not a proof.
ME: QED.
-/ --                                          | This is, far and away, the most important part of science.  If one is to measure, one must very
class REPEATABLE   -- Bullshit meter ≈ 166     | _carefully_ explain how to measure so that others may have a quantitative experience of an otherwise
  --  ----------                               | description. I describe experience as the equation Du=0.  Not just me, lot's of people do. This
  --      ^                                    | simple equation just says when you apply _this_ to _that_ you get.... What do you get? Is it
  --      |                                    | nothing? Science would say, no. Nothing is made of something is the general line that gets toed.
  --      +------------------------------------+ And the fact that the nothing is made of something is the thing that gets repeated over and over..
  --                                           |
    (Value: Type i) --                         | Perhaps math would be easier if nothing were truly nothing at all, and not something you can point
    (Carrier: CarrierProcess Value) --         | to.
    [DISTINGUISHABLE Value Carrier]  --
    [ADMISSIBLE Value Carrier] --      \
    [COUNTABLE Value Carrier]  --      |>  This process is called demodulation in DSP.
    [ENCODED Value Carrier]    --      /
    [RESIDUE Value Carrier]    --    --
    [BINARY Value Carrier]   --    We can now send and receive a bit with the compiler!
  where
  repeatable_process: RepeatableProcess Value Carrier
--          ^                 ^           ^      ^          | There are all these supercomputers all over the world, all solving Du=0.  Over and over
--          |                 |           |      |          | again. File in, file out. Hypothesis in, results out. These results are often
--          +-----------------+-----------+------+----------+ _checkpointed_, a description of the computation _in action_ in order to reduce
--                                                          | _the wall clock time_ of failure recovery, not to improve accuracy. This is just a
--                                                          | _side effect_ of the computation. A _measurable_ side effect that changes depending on
--                                                          | the computation being performed.

  typical_response: Trial → Trial → Prop := fun s t => repeatable_process.iterate s = t -- It cannot be simpler. Keep doing s, always get t.

-- Or, more simply, counting _is_ the mechanism _t_ by which a _repeatable_ process consumes _s_. We demand that _t_ take a different value because
-- _s_ cannot take it by construction. _t_ is never _s_ alone; it is always the iterate of _s_. And here, there is but one to compute.

-- Tune in next week for: TIME!
end Measurement
