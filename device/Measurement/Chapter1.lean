/-
Measurement/Chapter1.lean
Facts
-/

import Std
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Basic


namespace Measurement

/- there is only one universe.  that universe has
a current state.  that current state is at time _i_-/
universe i

/- universe state at time _i_+1.  unfortunately we cannot know anything
about the universe in the future. sometimes, science can
provide a set of options for the future ahead.  we don't
know why it works sometimes and sometimes you get nothing.
-/
abbrev NEXT (Symbol : Type i) := Option (ULift.{i+1,i} Symbol)

/- --------------------------------------------------------
DISTINGUISHABLE.

Something is DISTINGUISHABLE from others if there exists
some characteristic that is either present or absent from
the something relative to the others.
-/
class DISTINGUISHABLE
    (Symbol : Type i)
    (Characterisitic : Symbol → Symbol → Bool)
    where

  -- The indescribable universe.
  -- There is no other variable.
  -- Every Symbol you see is this entropy variable.
  -- Should be easy to spot.

  -- When you see "NEXT Symbol", that is just what
  -- entropy will look like at step _i_+1. We
  -- don't know what that is.

  -- Keep your eye on the ball!!
  entropy             : Symbol

  -- All other classes will be defined by mappings.
  -- The mappings are either supplied by the type name
  -- (such as the characteristic) or by the modified type.

  -- Are two symbols different?
  --  Supplied by the characteristic in the typename.
  different?          : Symbol → Symbol → Bool

  -- Have we distinguished a particular symbol from all others?
  --  Supplied by dependency injection.
  distinguished?      : Symbol → Bool

  -- Will we resolve this symbol in the future?
  --  Supplied by dependency injection.
  resolved?           : Symbol → NEXT Symbol → Bool

  -- What is the resolved symbol?
  --  Supplied by dependency injection. Going forward, only
  --  those things supplied by dependency injection are highlighted.
  resolve?            : Symbol → NEXT Symbol

/-
Of course, we need to be able to inquire about
a particularly distinguished symbol-- I mean
the entropy above.
-/

namespace DISTINGUISHABLE
variable  {Symbol : Type i}
          {Characteristic : Symbol → Symbol → Bool}
          [d: DISTINGUISHABLE Symbol Characteristic]

-- This is the single invariant upon which the entire universe can be
-- decomposed.
def invariant
    : Symbol :=
  d.entropy


-- This is a record of whether or not a particular
-- symbol is a fact. Could be a truth. Could be qualia.
-- Could be fantasy. Could be a lie. Could be a hallucination.
def is_a_fact
      : Bool :=
  distinguished? Characteristic d.entropy


-- This determines if two symbols do not share
-- the characteristic.
def different
    (s1: Symbol)
    (s2: Symbol)
      : Bool :=
  different? Characteristic s1 s2


-- This identifies the indicative symbol of a characterisitc.
-- This is the symbol that is different from all others.
-- You have to verify this symbol against all other
-- distiguished symbols to ensure that they do not have the
-- same characteristic. Either we can see the characteristic
-- now, or we have to wait for an event in the future to resolve it.
-- This happens at the moment of _slip_: a clearly identifiable
-- change in circumstance.
def distinguish
    (now: Symbol)
    (later: NEXT Symbol)
      : Bool :=
  resolved? Characteristic now later


-- The moment of slip is an undeniable observation, as studied by
-- da Vinci in his work on static friction. The fact is quantifiable
-- as demonstrated by the work of Amontons and Coulomb.
def resolved
    (now: Symbol)
      : NEXT Symbol :=
  d.resolve? now


end DISTINGUISHABLE


-- A description is just a series of distinguishable symbols.
-- Just like the ones you are reading right now. In fact,
-- Perhaps you are wondering if this description is a description
-- exactly like you are reading right now, a list of distinguishable
-- symbols, one right after another.  Like and subscribe if you
-- thought I was talking about something else. We'll come back to that
-- later.
inductive Description
    (Symbol : Type i)
    (Characteristic : Symbol → Symbol → Bool)
    [DISTINGUISHABLE Symbol Characteristic ]
  | nil : Description Symbol Characteristic
  | cons : Symbol →
           DISTINGUISHABLE Symbol Characteristic →
           Description Symbol Characteristic →
           Description Symbol Characteristic









/- --------------------------------------------------------
-/

-- At one time, people were over run with floods and people were like
-- I've had it with these random floods coming randomly and randomly
-- destroying everything. So they said:

-- Let's sciene the hell out of this.

-- And so, they could start to figure out that one thing leads to another.
-- We started understanding that certain situations were impossible
-- given current conditions.  Everything else could happen, theoretically.
-- We can further distinguish our universe by whether or not something
-- _could_ happen. So, an admissible entropy state in the future is one
-- that _could_ represent this.  That's 2 _coulds_.  Those are different
-- _coulds_.  Or, are they? Do they have to be?  Why not both?
class ADMISSIBLE
    (Symbol : Type i)
    (Characteristic : Symbol → Symbol → Bool)
    (Event: Symbol → NEXT Symbol → Bool)
    [d: DISTINGUISHABLE Symbol Characteristic]
    where

  -- This asks the question of "has the slip event occured yet for this
  -- possible next symbol?".  This is very useful for predictive
  -- phenomenologies whose entire purpose is to describe how symbols
  -- for invariants, their values, their derived values, and those
  -- representations, change over time, across units, and in different
  -- circumstances. (((fiveshadowing)))
  occured?      : Symbol → NEXT Symbol → Bool


  -- This is how we describe the outcome now, if we were to try to
  -- predict it.  It may not be distinguishable yet or describable yet.
  -- It may be noisy, or under-resolved.  Any way, you have options.
  --   This is supplied by dependency injection.
  symbol?       : NEXT Symbol → Option Symbol


namespace ADMISSIBLE
variable  {Symbol : Type i}
          {Characteristic : Symbol → Symbol → Bool}
          {Event : Symbol → NEXT Symbol → Bool}
          [d: DISTINGUISHABLE Symbol Characteristic]
          [s: ADMISSIBLE Symbol Characteristic Event]

-- So, there is a Characteristic Event, something we are colloquially
-- calling Slip.  The Characteric Event could have happened by now,
-- or we may need to wait for later.
def occurred
    (now: Symbol)
    (later: NEXT Symbol)
    : Bool :=
  occured? Characteristic Event now later

-- Sometimes science allows us to name the future symbol
-- pretty accurately.  If we can see enough of the symbol right
-- now, let's ship it.  Otherwise, keep a cork in it.  The universe
-- keeps its secrets.
def symbol
    (now: Symbol)
    : Option Symbol :=
  match d.resolve? now with
    | some x  => s.symbol? x
    | none    => none

end ADMISSIBLE



-- Once we have the concept of an admissible event, we can enumerate
-- those, producing a list in time.  This is a history of events
-- recorded as a symbol.  I wonder what that symbol could be? If
-- we have done this correctly, this is a list of entropies as they
-- evolve from one point to the next.
inductive HistoryOf
    (Symbol : Type i)
    (Characteristic : Symbol → Symbol → Bool)
    (Event: Symbol → NEXT Symbol → Bool)
    : (Symbol : Type i) -> Type (i+1)
  | nil : HistoryOf Symbol Characteristic Event Symbol
  | cons: (s : Symbol) →
          (now: Symbol) →
          (later: NEXT Symbol) →
          HistoryOf Symbol Characteristic Event Symbol →
          HistoryOf Symbol Characteristic Event Symbol







/- --------------------------------------------------------
-/

-- Once we can distinguish something, we need to label it
-- so we can talk about it.  This little bit of indirection
-- has befuddled philosophy for millenia.  This is the best
-- I got on the subject.  There is a thing and a label for
-- the thing. We often call that a name.  Not everything is
-- labeled. Not everything that can be distinguished can
-- be labeled.  Individual shades of the color blue are
-- distinguishable, but we fail to label them all.  This
-- despite the best efforts of Pantone and "Big Color."

-- This relies on the Computed map, a relation to store labels
-- as they are computed.  I hope I am putting the labels
-- in the right order as we go, otherwise they will not be
-- efficiently computed by the compiler! Oh, it's about to
-- get meta^2 up in here.  I think that's because we are
-- just relabeling things. Or we will.  Soon. I promise.
-- And this is just a relabeled ADMISSIBLE with the ADMISSIBLE
-- property. Another way we can distinguish something.
class LABELED
    (Symbol: Type i)
    (Encoding: Symbol → Symbol → Bool)
    (Computed: Symbol → NEXT Symbol → Bool)
    [d: DISTINGUISHABLE Symbol Encoding]
    [a: ADMISSIBLE Symbol Encoding Computed]
    where

  -- Is there a label for this symbol already?
  encoding_exists?: Symbol -> Symbol -> Bool

  -- Writing something down the first time,
  -- Takes time in order to make sure this is adequately
  -- distinguished from ALL other instances. Has it been
  -- written down the first time yet?
  computed?: Symbol -> NEXT Symbol -> Bool

namespace LABELED
variable  {Symbol: Type i}
          {Encoding: Symbol -> Symbol -> Bool}
          {Computed: Symbol -> NEXT Symbol -> Bool}
          [d: DISTINGUISHABLE Symbol Encoding]
          [a: ADMISSIBLE Symbol Encoding Computed]
          [e: LABELED Symbol Encoding Computed]


-- This asks where or not a particular symbol encodes
-- a particular concept. Or, more mathematically for
-- those who like the impossibly abstract, asks if the
-- symbol is the witness for a partition.  Or, is _a_
-- a rounding of _b_.  All sorts of encodings.  Any
-- time you need to swap symbols for any reason, this
-- is the reason you can.
def encoding_exists
    (concept: Symbol)
    (symbol: Symbol)
      : Bool :=
  encoding_exists? Encoding Computed concept symbol


-- Has a particular future outcome been encoded yet.
-- This is useful for a pendulum clock where the
-- two symbols are basically tick and tock.  They
-- get computed very quickly. Most times. Again,
-- never can tell.  Still gotta ask.
def computed
    (concept: Symbol)
    (symbol: NEXT Symbol)
      : Bool :=
  computed? Encoding Computed concept symbol


-- Or is that meta^3 to relabel the invariant for
-- the third time?  Tick - Tock - Tick.  Label - label -
-- label.  Label - tock - label.  I've heard it both
-- ways.
def label
      : Symbol :=
  d.invariant

end LABELED


-- Where does one store their memoized things? Why
-- in a pefect hash table, of course. But, dunno if you
-- noticed, but we don't have any types lying around to
-- perform a hash function.  But, what we do have is this
-- lisst that not only stores the instructions called, it
-- also stores the results of the instructions right next
-- to it.  So, this index is a computation index.  In what
-- _order_ were things computed in. So, we can describe
-- _how_ a computation was arrived at, even though we may
-- not understand how it was made. All we have to do is
-- write them down every time we compute.
inductive ListOf
    (Symbol: Type i)
    (Encoding: Symbol → Symbol → Bool)

    -- Any arbitrary computation can go here, but it
    -- must operate on the current state of entropy
    -- and no other.  This is a witness to the computation.
    -- So we can describe the partition and we can describe
    -- the witness.
    (Computed: Symbol → NEXT Symbol → Bool)

    [d: DISTINGUISHABLE Symbol Encoding]
    [a: ADMISSIBLE Symbol Encoding Computed]
    [l: LABELED Symbol Encoding Computed]
    : (Symbol : Type i) → Type (i+1)
  | nil :  ListOf Symbol Encoding Computed Symbol
  | cons: (s : Symbol) →
          (now: Symbol) →
          (later: NEXT Symbol) →
          ListOf Symbol Encoding Computed Symbol →
          ListOf Symbol Encoding Computed Symbol







/- --------------------------------------------------------
-/

-- Once we have a label, we can try to put those labels
-- in some sort of canonical order. Just in case someone
-- or something or some compiler needed to look them up
-- using the Power of Computation(tm).

-- This relies on the Sorted map.  This determines if the
-- first symbol comes before the second symbol in the
-- sorting. This is created whenever someone puts tick
-- marks on a ruler or a dial.  Those tick marks are sorted
-- from low to high.  These are not the numbers that are sorted,
-- just the tick marks. Same mark, but in order, from left to
-- right or top to bottom or round and round.  A weird raster
-- is about to come at you so, understand that sorted here just
-- means the tick marks.  You'll see.
class SORTED
    (Symbol: Type i)
    (Characteristic: Symbol → Symbol → Bool)
    (Event : Symbol → NEXT Symbol → Bool)
    (Sorted: Symbol → Symbol → Bool)
    [d: DISTINGUISHABLE Symbol Characteristic]
    [a: ADMISSIBLE Symbol Characteristic Event]
    where

  -- You were expecting?  Now, all we need
  -- is std::sort()! Any one got a __C_PLUS_PLUS__ binary
  -- lying around?
  less_than?    : Symbol → Symbol → Bool

namespace SORTED
variable  {Symbol: Type i}
          {Characteristic: Symbol → Symbol → Bool}
          {Event : Symbol → NEXT Symbol → Bool}
          -- TODO: Fill this in just in case people don't see it.
          {Sorted : Symbol → Symbol → Bool}
          (d: DISTINGUISHABLE Symbol Characteristic)
          (a: ADMISSIBLE Symbol Characteristic Event)
          (s: SORTED Symbol Characteristic Event Sorted)

-- And it is with less_than that we begin the description of
-- computation.  This is the fundamental computation allowed
-- by counting.
def less_than
    (left: Symbol)
    (right: Symbol)
      : Bool :=
  less_than? Characteristic Event Sorted left right

-- This guy is EVERYWHERE! Seriously, everywhere.  I can't believe
-- there is just one of these. Duh.. the geometry of the _single_
-- invariant. We are going to pack A LOT of information into this guy.
def number
      : Symbol :=
  d.invariant

end SORTED


inductive IndexOf
    (Symbol: Type i)
    (Encoding: Symbol → Symbol → Bool)
    (Computed: Symbol → NEXT Symbol → Bool)
    -- As before, any arbitrary sorting can go here
    (Sorted: Symbol → Symbol → Bool)

    -- This is starting to look self explanatory.
    -- Hard to believe how convoluted this code is.
    -- I'm hoping it is maximally convolved or I have
    -- done it wrong.
    [d: DISTINGUISHABLE Symbol Encoding]
    [a: ADMISSIBLE Symbol Encoding Computed]
    [l: LABELED Symbol Encoding Computed]
    [s: SORTED Symbol Encoding Computed Sorted]

    -- Welcome to boiler plate.  This pattern is going to
    -- grow one word at a time as we slowly describe the
    -- measurement in a ledger.
    : (Symbol : Type i) → Type (i+1)
  | nil :  IndexOf Symbol Encoding Computed Sorted Symbol
  | cons: (s : Symbol) →
          (now: Symbol) →
          (later: NEXT Symbol) →
          IndexOf Symbol Encoding Computed Sorted Symbol →
          IndexOf Symbol Encoding Computed Sorted Symbol




/- --------------------------------------------------------
-/

-- Before there were computers, there was Turing.  Turing
-- made an implicit assumption:  Representation is faithful.
-- Unfortunately, Shannon, at roughly the same time, proved
-- representation is explicitly UNFAITHFUL and cannot made
-- to be FAITHFUL.  What to do, what to do...  So, we start
-- by decomposing a Turing machine.  This describes a single
-- step of a Turing machine.  In other words, this is one step
-- in a formal process.
class COMPUTABLE
    (Symbol: Type i)
    (Characteristic: Symbol → Symbol → Bool)
    (Event : Symbol → NEXT Symbol → Bool)
    (Sorted: Symbol → Symbol → Bool)
    -- Look closely, and you will see memoization.
    -- Let's memoize the entropy right in front of us by putting
    -- it back into the next entropy. I know you think I am building
    -- a universal Turing machine here, but I am not.  I am building a ...
    (Computation: Symbol → NEXT Symbol → Bool)
    -- (((lol)))

    [d: DISTINGUISHABLE Symbol Characteristic]
    [a: ADMISSIBLE Symbol Characteristic Event]
    [s: SORTED Symbol Characteristic Event Sorted]
    where

-- In order to determine a symbol in the future, one _must_
-- compute it.  These are the symbols upon which computation can
-- be performed.

-- Now, I would never discount the efforts of Turing for, without
-- his work, we could not faithfully restate a trivial example of
-- the halting problem as.
  executable? :  Symbol → NEXT Symbol -> Bool


namespace COMPUTABLE
variable  {Symbol: Type i}
          {Characteristic: Symbol → Symbol → Bool}
          {Event : Symbol → NEXT Symbol → Bool}
          {Sorted : Symbol → Symbol → Bool}
          {Computation: Symbol → NEXT Symbol → Bool}
          (d: DISTINGUISHABLE Symbol Characteristic)
          (a: ADMISSIBLE Symbol Characteristic Event)
          (s: SORTED Symbol Characteristic Event Sorted)
          (c: COMPUTABLE Symbol Characteristic Event Sorted Computation)


-- If you are tired of waiting, you should have bought a faster processor!
def executable
    (instruction: Symbol)
    (result: NEXT Symbol)
      : Bool :=
  executable? Characteristic Event Sorted Computation instruction result

-- Did you know, it is all just a number?
def value
      : Symbol :=
  d.invariant

end COMPUTABLE

inductive ComputationOf
    (Symbol: Type i)
    (Characteristic: Symbol → Symbol → Bool)
    (Encoding: Symbol → Symbol → Bool)
    (Event : Symbol → NEXT Symbol → Bool)
    (Computed : Symbol → NEXT Symbol → Bool)
    (Sorted_Computations: Symbol → Symbol → Bool)
    (Sorted_Events: Symbol → Symbol → Bool)
    (Computation: Symbol → NEXT Symbol → Bool)

    [d1: DISTINGUISHABLE Symbol Encoding]
    [computation: ADMISSIBLE Symbol Encoding Computed]
    [d2: DISTINGUISHABLE Symbol Characteristic]
    [event: ADMISSIBLE Symbol Characteristic Event]
    [l1: LABELED Symbol Encoding Computed]     -- This is the LABEL that LABELS a computation
    [l2: LABELED Symbol Characteristic Event]  -- This is the name of invariant of the computation, _x_.
    [s1: SORTED Symbol Encoding Computed Sorted_Computations]
    [s2: SORTED Symbol Characteristic Event Sorted_Events]

    -- Welcome to boiler plate.  This pattern is going to
    -- grow one word at a time as we slowly describe the
    -- measurement in a ledger. Okay, not really one word
    -- at a time.  Sometimes we can get quite a few all at once.
    : (Symbol : Type i) → Type (i+1)
  | nil :  ComputationOf Symbol Characteristic Encoding Event Computed Sorted_Computations Sorted_Events Computation Symbol
  | cons: (s : Symbol) →
          (now: Symbol) →
          (later: NEXT Symbol) →
          ComputationOf Symbol Characteristic Encoding Event Computed Sorted_Computations Sorted_Events Computation Symbol →
          ComputationOf Symbol Characteristic Encoding Event Computed Sorted_Computations Sorted_Events Computation Symbol


/- --------------------------------------------------------
-/

class PHYSICAL
    (Symbol: Type i)
    (Stimulus: Symbol → NEXT Symbol → Bool)
    (Response: NEXT Symbol → NEXT Symbol → Bool)
    (Observation: NEXT Symbol → NEXT (NEXT Symbol) → Bool)
    [d: DISTINGUISHABLE (NEXT Symbol) Response]
    (a: ADMISSIBLE (NEXT Symbol) Response Observation)
    where

  -- This is the fundamental physical law.  It is the only thing
  -- that is physical.  It is the only thing that is real.  It is
  -- the only thing that exists.  It is the only thing that can be
  -- measured.  It is the only thing that can be computed.  It is
  -- the only thing that can be sorted.  It is the only thing that can
  -- be distinguished.  It is the only thing that can be admitted.
  slip? : Symbol → NEXT Symbol → Bool


namespace PHYSICAL

end PHYSICAL



end Measurement
