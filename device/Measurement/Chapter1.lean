/-
Measurement/Chapter1.lean


-- There are NO IMPORTS.

-- We assume that there are 4 symbols that must be recognized.
-- I
-- NEXT
-- NEXT_I
-- A compiled version of this program that demonstrates truth.
-- It makes no difference what these words mean, they just need
-- to be recognized as symbols.

-- Everything else is determmined to follow from the language
-- of lean alone.
-/


namespace Measurement

/- there is only one universe.  that universe has
a current state.  that current state is at time _i_,
our first symbol-/
universe i

/- This is the act of seeing something happen. We assume
it takes time and space to build a device that observe and the thing
being observed also must take up time and space. If you find
this assumption too WOKE, tell it to Planck, Heisenberg, Dirac, etc.
You don't know the future until you yank off that Option.
-/
abbrev OBSERVE (x : Type i) := Option (ULift.{i+1,i} x)

abbrev NEXT  (x : Type i) := Option x      -- For x := Bool, this abbrev will
                                           -- carry an allocated bit in the
                                           -- memory of the compiler that will
                                           -- not exist in the proof, because
                                           -- Option Bool is not binary, it is
                                           -- Trinary. This bit is used as
                                           -- the ephemera of the carrier.
                                           -- the Æther, if you will. The construction
                                           -- below ensures that the abbrev requires
                                           -- no memory so I can use that bit
                                           -- freely. That's the how the magic trick
                                           -- works.



/- --------------------------------------------------------
DISTINGUISHABLE.

Something is DISTINGUISHABLE from others if there exists
some characteristic that is either present or absent from
the something relative to the others.
-/
class DISTINGUISHABLE
    (Characterisitic : Type i → Type i → Prop)
    (Symbol: Type i)
    where

  -- STUFF

  -- The indescribable universe.
  -- There is no other variable.
  -- Every Symbol you see is stuff.
  -- Also, every symbol you see is stuff.
  -- Should be easy to spot the difference.

  -- When you see "NEXT Symbol", that is just what
  -- stuff will look like at step _i_+1. We
  -- don't know what that is.

  -- Keep your eye on the ball!!
  -- A symbol just might get resolved.
  æther               : Type i

  -- All other classes will be defined by mappings.
  -- The mappings are either supplied by the type name
  -- (such as the characteristic) or by the modified type.

  -- Are two symbols different?
  --  Supplied by the characteristic in the typename.
  different?          : Type i → Type i → Prop := Characterisitic

  -- Have we distinguished a particular symbol from all others?
  --  Supplied by dependency injection.
  distinguished?      : Type i → Prop := λ s => ∃ (c : Type i), different? c s

  -- Will we resolve this symbol in the future?
  --  Supplied by dependency injection.
  resolved?           : Type i → Carrier → Type


namespace DISTINGUISHABLE
variable {Characterisitic : Type i → Type i → Prop}
         {Carrier: Type i}
         [d: DISTINGUISHABLE Characterisitic Carrier]

def symbol
    (S: Type i)
    [Decidable (d.distinguished? S)] : Type i :=
  if d.distinguished? S then
    S
  else
    d.æther

end DISTINGUISHABLE


-- A description is just a series of distinguishable symbols.
-- Just like the ones you are reading right now.
-- Perhaps you are wondering if this description is a description
-- exactly like you are reading right now, a list of distinguishable
-- symbols, one right after another. Or is it a description like
-- this program describes a computation? Like and subscribe if you
-- thought I was talking about something else. We'll come back to all
-- of these later.  I promise.

-- The important thing about a description is that it exists as
-- part of the stuff of the universe, so it has an index _i_
inductive DescriptionOf
    (Characteristic : Type i → Type i → Prop)
    (Symbol: Type i)
    [d : DISTINGUISHABLE Characteristic Symbol]
  | nil : DescriptionOf Characteristic Symbol
  | cons (S : Type i)
         (h : d.distinguished? S)
         (rest : DescriptionOf Characteristic Symbol)
         : DescriptionOf Characteristic Symbol



-- As you can see, we can describe a symbol as a pile of
-- characteristics, with just a little help from the
-- compiler.  Welcome to the ledger of the universe.
-- What you see below is the holder for the mostly
-- densely packed game of 20 Questions you have ever seen.
abbrev Symbol
    (Characteristic : Type i → Type i → Prop)
    (Substrate : Type i)
    [d : DISTINGUISHABLE Characteristic Substrate] :=
  DescriptionOf Characteristic Substrate

abbrev RESOLVED
    (Characteristic : Type i → Type i → Prop)
    (Substrate : Type i)
    [d : DISTINGUISHABLE Characteristic Substrate] :=
  d.distinguished?

abbrev COUNT
    (Char : Type i → Type i → Prop)
    (Symbol: Type i)
    [d : DISTINGUISHABLE Char Symbol]
      :=
  DescriptionOf Char Symbol

-- We shall now decompose the æther into countable segments.


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
-- _could_ happen. So, an admissible stuff state in the future is one
-- that _could_ represent this.  That's 2 _coulds_.  Those are different
-- _coulds_.  Or, are they? Do they have to be?  Why not both?
class ADMISSIBLE
    (Event : Type (i+1) → Type (i+1) → Prop)
    (Before: Type i)
    (After: Type (i+1))
    (Observation: Before → OBSERVE After → Bool)
    [a: DISTINGUISHABLE Event After]
    where

  -- Is this a possible future state of the universe that is different from the current state of the universe?
  distinguished? : Before → OBSERVE After → Bool := Observation

  -- Is this a possible future state of the universe? Dunno, could be.
  admissible? : Before → After → Bool

namespace ADMISSIBLE
variable {Event : Type (i+1) → Type (i+1) → Prop}
         {Before: Type i}
         {After: Type (i+1)}
         {Observation: Before → OBSERVE After → Bool}
         [a: DISTINGUISHABLE Event After]
         [the_future: ADMISSIBLE Event Before After Observation]

-- Is this a possible future state of the universe?
def possible?
    (s: Before)
    (future: After)
      : Bool :=
  the_future.admissible? s future

def distinguished
  (s: Before)
  (future: OBSERVE After)
    : Bool :=
  the_future.distinguished? s future

end ADMISSIBLE


-- Once we have the concept of an admissible event, we can enumerate
-- those, producing a list in time.  This is a history of events
-- recorded as a symbol.  I wonder what that symbol could be? If
-- we have done this correctly, this is a list of entropies as they
-- evolve from one point to the next.
inductive CountOf
    (Event : Type (i+1) → Type (i+1) → Prop)
    (Before: Type i)
    (After: Type (i+1))
    (Observation: Before → OBSERVE After → Bool)
    [a: DISTINGUISHABLE Event After]
  | nil : CountOf Event Before After Observation
  | cons : (Before → OBSERVE After → Bool) →           -- Now this is pod racing---- er, counting.
           CountOf Event Before After Observation →  -- tick tock, before after
           CountOf Event Before After Observation

-- And now, a NUMBER.  This time, the
-- count is done by the compiler counting ephemeral lambdas,
-- I mean the æther. Uhh... entropy?
abbrev NUMBER
    (Event : Type (i+1) → Type (i+1) → Prop)
    (Symbol: Type i)
    (Value: Type (i+1))
    [a: DISTINGUISHABLE Event Value]
    (Count: Symbol → OBSERVE Value → Bool) :=
  CountOf Event Symbol Value Count




/- --------------------------------------------------------
-/

class PAIRED
    (Ordering: Type (i+1) → Type (i+1) → Prop)
    (Symbol: Type i)
    (Enccoding: Type (i+1))
    (Encode: Symbol → OBSERVE Name → Bool)
    [DISTINGUISHABLE Ordering Name]
    [ADMISSIBLE Ordering Symbol Name Encode]
    where

  encoded? : Symbol → OBSERVE Name → Bool := Encode

namespace PAIRED
variable {Ordering: Type (i+1) → Type (i+1) → Prop}
         {Symbol: Type i}
         {Encoding: Type (i+1)}
         {Encode: Symbol → OBSERVE Encoding → Bool}
         [DISTINGUISHABLE Ordering Encoding]
         [ADMISSIBLE Ordering Symbol Encoding Encode]
         [parsed_symbol: PAIRED Ordering Symbol Encoding Encode]

def encoded
    (input: Symbol)
    (output: OBSERVE Encoding)
      : Bool :=
  parsed_symbol.encoded? input output

end PAIRED


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
inductive PairsOf
    (Ordering: Type (i+1) → Type (i+1) → Prop)
    (First: Type i)
    (Second: Type (i+1))
    (Encode: First → OBSERVE Second → Bool)
    [DISTINGUISHABLE Ordering Second]
    [ADMISSIBLE Ordering First Second Encode]
    [parsed_symbol: PAIRED Ordering First Second Encode]

  | nil : PairsOf Ordering First Second Encode
  | cons : (input: First) →
           (output: OBSERVE Second) →
           (h: parsed_symbol.encoded? input output) →
           PairsOf Ordering First Second Encode →
           PairsOf Ordering First Second Encode


abbrev Mapping
    (Ordering: Type (i+1) → Type (i+1) → Prop)
    (Preimage: Type i)
    (Image: Type (i+1))
    (Encode: Preimage → OBSERVE Image → Bool)
    [DISTINGUISHABLE Ordering Image]
    [ADMISSIBLE Ordering Preimage Image Encode]
    [parsed_symbol: PAIRED Ordering Preimage Image Encode] :=
  PairsOf Ordering Preimage Image Encode




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
class ORDERED
    (Ordering: Type (i+1) → Type (i+1) → Prop)
    (Less: Type i)
    (More: Type (i+1))
    (Counting: Less → OBSERVE More → Bool)
    (Relation: Less → More → Bool)
    [DISTINGUISHABLE Ordering More]
    [ADMISSIBLE Ordering Less More Counting]
    [parsed_symbol: PAIRED Ordering Less More Counting]
    where

  -- You were expecting?  Now, all we need
  -- is std::sort()! Any one got a __C_PLUS_PLUS__ binary
  -- lying around?
  less_than?    : Less → More → Bool := Relation

  correlant?    : Less → More → Bool := λ l m => less_than? l m

namespace ORDERED
variable  {Ordering: Type (i+1) → Type (i+1) → Prop}
          {Less: Type i}
          {More: Type (i+1)}
          {Counting: Less → OBSERVE More → Bool}
          {Relation: Less → More → Bool}
          [DISTINGUISHABLE Ordering More]
          [ADMISSIBLE Ordering Less More Counting]
          [parsed_symbol: PAIRED Ordering Less More Counting]
          [ordered: ORDERED Ordering Less More Counting Relation]

def less_than
    (l: Less)
    (m: More)
      : Bool :=
  ordered.less_than? l m
end ORDERED


inductive SortedPairsOf
    (Ordering: Type (i+1) → Type (i+1) → Prop)
    (Less: Type i)
    (More: Type (i+1))
    (Counting: Less → OBSERVE More → Bool)
    (Relation: Less → More → Bool)
    [DISTINGUISHABLE Ordering More]
    [ADMISSIBLE Ordering Less More Counting]
    [parsed_symbol: PAIRED Ordering Less More Counting]
    [ordered: ORDERED Ordering Less More Counting Relation]

  | nil : SortedPairsOf Ordering Less More Counting Relation
  | cons : (l: Less) →
           (m: More) →
           (h: ordered.less_than? l m) →
           SortedPairsOf Ordering Less More Counting Relation →
           SortedPairsOf Ordering Less More Counting Relation




/- --------------------------------------------------------

           ***       ***      ***        *
          *   *     *   *     *  *      * *
          *         *   *     *  *     *   *
          *         *   *     *  *     *****
          *         *   *     *  *     *   *
          *   *     *   *     *  *     *   *
           ***       ***      ***      *   *

-- -------------------------------------------------------/

class COMPUTABLE
    (DecodeInstruction: Type (i+1) → Type (i+1) → Prop)
    (ExecuteInstruction: Type (i+2) → Type (i+2) → Prop)
    (Data: Type i)
    (Instruction: Type (i+1))
    (Output: Type (i+2))
    (Decoded   : Data → OBSERVE Instruction → Bool)
    (Executed  : Instruction → OBSERVE Output → Bool)
    [DISTINGUISHABLE DecodeInstruction Instruction]
    [DISTINGUISHABLE ExecuteInstruction Output]
    [ADMISSIBLE DecodeInstruction Data Instruction Decoded]
    [ADMISSIBLE ExecuteInstruction Instruction Output Executed]
    [PAIRED DecodeInstruction Data Instruction Decoded]
    [PAIRED ExecuteInstruction Instruction Output Executed]
    [ORDERED DecodeInstruction Data Instruction Decoded (λ d i => Decoded d (some (ULift.up i)))]
    [ORDERED ExecuteInstruction Instruction Output Executed (λ i o => Executed i (some (ULift.up o)))]
      where

  decoded? : Data → OBSERVE Instruction → Bool := Decoded
  executed? : Instruction → OBSERVE Output → Bool := Executed


namespace COMPUTABLE
variable {DecodeInstruction: Type (i+1) → Type (i+1) → Prop}
         {ExecuteInstruction: Type (i+2) → Type (i+2) → Prop}
         {Data: Type i}
         {Instruction: Type (i+1)}
         {Output: Type (i+2)}
         {Decoded   : Data → OBSERVE Instruction → Bool}
         {Executed  : Instruction → OBSERVE Output → Bool}
         [DISTINGUISHABLE DecodeInstruction Instruction]
         [DISTINGUISHABLE ExecuteInstruction Output]
         [ADMISSIBLE DecodeInstruction Data Instruction Decoded]
         [ADMISSIBLE ExecuteInstruction Instruction Output Executed]
         [PAIRED DecodeInstruction Data Instruction Decoded]
         [PAIRED ExecuteInstruction Instruction Output Executed]
         [ORDERED DecodeInstruction Data Instruction Decoded (λ d i => Decoded d (some (ULift.up i)))]
         [ORDERED ExecuteInstruction Instruction Output Executed (λ i o => Executed i (some (ULift.up o)))]
         [model: COMPUTABLE DecodeInstruction ExecuteInstruction Data Instruction Output Decoded Executed]

def decoded
    (d: Data)
    (i: OBSERVE Instruction)
      : Bool :=
  model.decoded? d i

def executed
    (i: Instruction)
    (o: OBSERVE Output)
      : Bool :=
  model.executed? i o

end COMPUTABLE


-- This generates a trace of a computation: the list of computations
-- and the internal state of the computer at the time of computation
inductive TapeOf
    (DecodeInstruction: Type (i+1) → Type (i+1) → Prop)
    (ExecuteInstruction: Type (i+2) → Type (i+2) → Prop)
    (Data: Type i)
    (Instruction: Type (i+1))
    (Output: Type (i+2))
    (Decoded   : Data → OBSERVE Instruction → Bool)
    (Executed  : Instruction → OBSERVE Output → Bool)
    [DISTINGUISHABLE DecodeInstruction Instruction]
    [DISTINGUISHABLE ExecuteInstruction Output]
    [ADMISSIBLE DecodeInstruction Data Instruction Decoded]
    [ADMISSIBLE ExecuteInstruction Instruction Output Executed]
    [PAIRED DecodeInstruction Data Instruction Decoded]
    [PAIRED ExecuteInstruction Instruction Output Executed]
    [ORDERED DecodeInstruction Data Instruction Decoded (λ d i => Decoded d (some (ULift.up i)))]
    [ORDERED ExecuteInstruction Instruction Output Executed (λ i o => Executed i (some (ULift.up o)))]
    [model: COMPUTABLE DecodeInstruction ExecuteInstruction Data Instruction Output Decoded Executed]
    where
    -- Welcome to boiler plate.  This pattern is going to
    -- grow one word at a time as we slowly describe the
    -- measurement in a ledger. Okay, not really one word
    -- at a time.  Sometimes we can get quite a few all at once.
  | nil :  TapeOf DecodeInstruction ExecuteInstruction Data Instruction Output Decoded Executed
  | cons : (d: Data) →
           (i: Instruction) →
           (o: Output) →
           (h1: model.decoded d (some (ULift.up i))) →
           (h2: model.executed i (some (ULift.up o))) →
           TapeOf DecodeInstruction ExecuteInstruction Data Instruction Output Decoded Executed →
           TapeOf DecodeInstruction ExecuteInstruction Data Instruction Output Decoded Executed


/- --------------------------------------------------------
-/

-- Finally, the physical process of slip, the ole'
-- noisy stimulus-response. Slip, as characterized by da Vince,
-- is a threshold process based on the mass of the object stubbornly
-- resisting motion.  Then it moves _all_ _at_ _once_.  This
-- all at once-ness is the key to slip. Once some threshold is met,
-- the slip occurs, even if you have no idea how to compute the
-- invariant or threshold.  You just need to be able to recoginze the
-- slip as being a distinguished change in circumstance.  This is the
-- basis of all physical processes,

/-
    (Symbol: Type i)
    (Encoding: Symbol → Symbol → Bool)
    (InternalSymbol: Symbol → NEXT Symbol)
    (StateChange: NEXT Symbol → NEXT Symbol → Bool)
    (Parsed: Symbol → OBSERVE Symbol → Bool)
    (Instruction: OBSERVE Symbol -> OBSERVE Symbol -> Bool)
    (Compiled: OBSERVE Symbol → OBSERVE (OBSERVE Symbol) → Bool)
    (NextInstruction: OBSERVE Symbol → NEXT (OBSERVE Symbol))
    (InterpretInstruction: OBSERVE Symbol → NEXT (OBSERVE Symbol))
    (Execution: NEXT (OBSERVE Symbol) → NEXT (OBSERVE Symbol) → Bool)
    (Executed: NEXT (OBSERVE Symbol) → OBSERVE (NEXT (OBSERVE Symbol)) → Bool)
-/

class TIMED
    (ddt: Type i → Type i → Type i → Prop)
    (dt: Type i → Type i → Prop)
    (t: Type i)
    (x: t → Type i)
    (Stimulus: t → NEXT t → Bool)
    (Response: NEXT t → OBSERVE (NEXT t) → Bool)
    (dx: (OBSERVE t) → NEXT (OBSERVE t) → Bool)
    (ddx: (NEXT (OBSERVE t)) → NEXT (OBSERVE (NEXT t)) → Bool)
    where

  emit? : t → OBSERVE t → Bool
  receive? : NEXT t → OBSERVE (NEXT t) → Bool

namespace TIMED
variable {ddt: Type i → Type i → Type i → Prop}
         {dt: Type i → Type i → Prop}
         {t: Type i}
         {x: t → Type i}
         {Stimulus: t → NEXT t → Bool}
         {Response: NEXT t → OBSERVE (NEXT t) → Bool}
         {dx: (OBSERVE t) → NEXT (OBSERVE t) → Bool}
         {ddx: (NEXT (OBSERVE t)) → NEXT (OBSERVE (NEXT t)) → Bool}
         [model: TIMED ddt dt t x Stimulus Response dx ddx]

def emit
    (s: t)
    (o: OBSERVE t)
      : Bool :=
  model.emit? s o

def receive
    (s: NEXT t)
    (o: OBSERVE (NEXT t))
      : Bool :=
  model.receive? s o

end TIMED


inductive CounterOf
    (ddt: Type i → Type i → Type i → Prop)
    (dt: Type i → Type i → Prop)
    (t: Type i)
    (x: t → Type i)
    (Stimulus: t → NEXT t → Bool)
    (Response: NEXT t → OBSERVE (NEXT t) → Bool)
    (dx: (OBSERVE t) → NEXT (OBSERVE t) → Bool)
    (ddx: (NEXT (OBSERVE t)) → NEXT (OBSERVE (NEXT t)) → Bool)
    [model: TIMED ddt dt t x Stimulus Response dx ddx]
  | nil : CounterOf ddt dt t x Stimulus Response dx ddx
  | cons : (s: t) →
           (o: OBSERVE t) →
           (h1: model.emit s o) →
           CounterOf ddt dt t x Stimulus Response dx ddx →
           CounterOf ddt dt t x Stimulus Response dx ddx




class AGGREGATED
    (COUNT: Type i → Type i → Type i → Prop)
    (ZERO: Type i → Type i → Prop)
    (Number: Type i)
    (ONE: Number → Type i)
    (Counter : Type (i+1))              -- The count of the count of the mark. So, we have to make One COUNTABLE.
    (Trial : Counter -> Counter → Bool)
    (Tally: r -> OBSERVE Counter → Bool)
    (Repeatable: OBSERVE Number → NEXT (OBSERVE COUNTER) → Bool)
    (Comparable: NEXT (OBSERVE COUNTER) → NEXT (OBSERVE COUNTER) → Bool)


    [time: TIMED COUNT ZERO Number ONE Trial Tally Repeatable Comparable]
      where
