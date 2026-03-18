/-
Measurement/Chapter1.lean


-- There are NO IMPORTS.
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

  -- When you see "DIFFERENT Symbol", that is just what
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
    (Symbol: Type i)
    [Decidable (d.distinguished? Symbol)] : Option (Type i) :=
  if d.distinguished? Symbol then
    some Symbol
  else
    some (d.æther)



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




/- --------------------------------------------------------
-/

class PAIRED
    (Ordering: Type (i+1) → Type (i+1) → Prop)
    (Symbol: Type i)
    (Encoding: Type (i+1))
    (Encode: Symbol → OBSERVE Encoding → Bool)
    [DISTINGUISHABLE Ordering Encoding]
    [ADMISSIBLE Ordering Symbol Encoding Encode]
    where

  encoded? : Symbol → OBSERVE Encoding → Bool := Encode

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
    (ExecuteInstruction: Type (i+1) → Type (i+1) → Prop)
    (Data: Type i)
    (Instruction: Type (i+1))
    (Output: Type (i+1))
    (Decoded   : Data → OBSERVE Instruction → Bool)
    (Executed  : Data → OBSERVE Output → Bool)
    [DISTINGUISHABLE DecodeInstruction Instruction]
    [DISTINGUISHABLE ExecuteInstruction Instruction]
    [DISTINGUISHABLE ExecuteInstruction Output]
    [ADMISSIBLE DecodeInstruction Data Instruction Decoded]
    [ADMISSIBLE ExecuteInstruction Data Output Executed]
    [PAIRED DecodeInstruction Data Instruction Decoded]
    [PAIRED ExecuteInstruction Data Output Executed]
    [ORDERED DecodeInstruction Data Instruction Decoded (λ d i => Decoded d (some (ULift.up i)))]
    [ORDERED ExecuteInstruction Data Output Executed (λ d o => Executed d (some (ULift.up o)))]
      where

  decoded? : Data → OBSERVE Instruction → Bool := Decoded
  executed? : Data → OBSERVE Output → Bool := Executed


namespace COMPUTABLE
variable  {DecodeInstruction: Type (i+1) → Type (i+1) → Prop}
          {ExecuteInstruction: Type (i+1) → Type (i+1) → Prop}
          {Data: Type i}
          {Instruction: Type (i+1)}
          {Output: Type (i+1)}
          {Decoded   : Data → OBSERVE Instruction → Bool}
          {Executed  : Data → OBSERVE Output → Bool}
          [DISTINGUISHABLE DecodeInstruction Instruction]
          [DISTINGUISHABLE ExecuteInstruction Instruction]
          [DISTINGUISHABLE ExecuteInstruction Output]
          [ADMISSIBLE DecodeInstruction Data Instruction Decoded]
          [ADMISSIBLE ExecuteInstruction Data Output Executed]
          [PAIRED DecodeInstruction Data Instruction Decoded]
          [PAIRED ExecuteInstruction Data Output Executed]
          [ORDERED DecodeInstruction Data Instruction Decoded (λ d i => Decoded d (some (ULift.up i)))]
          [ORDERED ExecuteInstruction Data Output Executed (λ d o => Executed d (some (ULift.up o)))]
          [model: COMPUTABLE DecodeInstruction ExecuteInstruction Data Instruction Output Decoded Executed]

def decoded
    (d: Data)
    (i: OBSERVE Instruction)
      : Bool :=
  model.decoded? d i

def executed
    (d: Data)
    (o: OBSERVE Output)
      : Bool :=
  model.executed? d o
end COMPUTABLE

-- This generates a trace of a computation: the list of computations
-- and the internal state of the computer at the time of computation
inductive TapeOf
    (DecodeInstruction: Type (i+1) → Type (i+1) → Prop)
    (ExecuteInstruction: Type (i+1) → Type (i+1) → Prop)
    (Data: Type i)
    (Instruction: Type (i+1))
    (Output: Type (i+1))
    (Decoded   : Data → OBSERVE Instruction → Bool)
    (Executed  : Data → OBSERVE Output → Bool)
    [DISTINGUISHABLE DecodeInstruction Instruction]
    [DISTINGUISHABLE ExecuteInstruction Instruction]
    [DISTINGUISHABLE ExecuteInstruction Output]
    [ADMISSIBLE DecodeInstruction Data Instruction Decoded]
    [ADMISSIBLE ExecuteInstruction Data Output Executed]
    [PAIRED DecodeInstruction Data Instruction Decoded]
    [PAIRED ExecuteInstruction Data Output Executed]
    [ORDERED DecodeInstruction Data Instruction Decoded (λ d i => Decoded d (some (ULift.up i)))]
    [ORDERED ExecuteInstruction Data Output Executed (λ d o => Executed d (some (ULift.up o)))]
    [model: COMPUTABLE DecodeInstruction ExecuteInstruction Data Instruction Output Decoded Executed]

  | nil : TapeOf DecodeInstruction ExecuteInstruction Data Instruction Output Decoded Executed
  | cons : (d: Data) →
           (i: OBSERVE Instruction) →
           (o: OBSERVE Output) →
           model.decoded? d i →
           model.executed? d o →
           TapeOf DecodeInstruction ExecuteInstruction Data Instruction Output Decoded Executed →
           TapeOf DecodeInstruction ExecuteInstruction Data Instruction Output Decoded Executed

abbrev COMPUTED (Symbol: Type i) := Symbol × OBSERVE Symbol
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
    (InternalSymbol: Symbol → DIFFERENT Symbol)
    (StateChange: DIFFERENT Symbol → DIFFERENT Symbol → Bool)
    (Parsed: Symbol → OBSERVE Symbol → Bool)
    (Instruction: OBSERVE Symbol -> OBSERVE Symbol -> Bool)
    (Compiled: OBSERVE Symbol → OBSERVE (OBSERVE Symbol) → Bool)
    (NextInstruction: OBSERVE Symbol → DIFFERENT (OBSERVE Symbol))
    (InterpretInstruction: OBSERVE Symbol → DIFFERENT (OBSERVE Symbol))
    (Execution: DIFFERENT (OBSERVE Symbol) → DIFFERENT (OBSERVE Symbol) → Bool)
    (Executed: DIFFERENT (OBSERVE Symbol) → OBSERVE (DIFFERENT (OBSERVE Symbol)) → Bool)
-/

class ENCODED
    (Labeled: Type (i+1) → Type (i+1) → Prop)
    (Symbol: Type i)
    (Name: Symbol → Type i)
    (Representation: Type (i+1))
    (EncodedSymbol: Symbol → OBSERVE Representation → Bool)
    (Encoding: Symbol → Representation → Bool)
    [DISTINGUISHABLE Labeled Representation]
    [ADMISSIBLE Labeled Symbol Representation EncodedSymbol]
    [PAIRED Labeled Symbol Representation EncodedSymbol]
    [ORDERED Labeled Symbol Representation EncodedSymbol Encoding]
      where
  encoded? : Symbol → OBSERVE Representation → Bool := EncodedSymbol
  name? : Symbol → Type i := Name
  encoding? : Symbol → Representation → Bool := Encoding

namespace ENCODED
variable {Labeled: Type (i+1) → Type (i+1) → Prop}
         {Symbol: Type i}
         {Name: Symbol → Type i}
         {Representation: Type (i+1)}
         {EncodedSymbol: Symbol → OBSERVE Representation → Bool}
         {Encoding: Symbol → Representation → Bool}
         [DISTINGUISHABLE Labeled Representation]
         [ADMISSIBLE Labeled Symbol Representation EncodedSymbol]
         [PAIRED Labeled Symbol Representation EncodedSymbol]
         [ORDERED Labeled Symbol Representation EncodedSymbol Encoding]
         [index: ENCODED Labeled Symbol Name Representation EncodedSymbol Encoding]

def encoded
    (s: Symbol)
    (r: OBSERVE Representation)
      : Bool :=
  index.encoded? s r

def name
    (s: Symbol)
      : Type i :=
  index.name? s

def encoding
    (s: Symbol)
    (r: Representation)
      : Bool :=
  index.encoding? s r

end ENCODED

inductive RepresentationOf
    (Labeled: Type (i+1) → Type (i+1) → Prop)
    (Symbol: Type i)
    (Name: Symbol → Type i)
    (Representation: Type (i+1))
    (EncodedSymbol: Symbol → OBSERVE Representation → Bool)
    (Encoding: Symbol → Representation → Bool)
    [DISTINGUISHABLE Labeled Representation]
    [ADMISSIBLE Labeled Symbol Representation EncodedSymbol]
    [PAIRED Labeled Symbol Representation EncodedSymbol]
    [ORDERED Labeled Symbol Representation EncodedSymbol Encoding]
    [index: ENCODED Labeled Symbol Name Representation EncodedSymbol Encoding]

  | nil : RepresentationOf Labeled Symbol Name Representation EncodedSymbol Encoding
  | cons : (s: Symbol) →
           (r: OBSERVE Representation) →
           (h1: index.encoded? s r) →
           RepresentationOf Labeled Symbol Name Representation EncodedSymbol Encoding →
           RepresentationOf Labeled Symbol Name Representation EncodedSymbol Encoding


abbrev DIFFERENT (Symbol: Type i) := Option (Symbol)

class TIMED
    (ddt: Type i → Type i → Type i → Prop)
    (dt: Type i → Type i → Prop)
    (t: Type i)
    (x: t → Type i)
    (Stimulus: t → DIFFERENT t → Bool)
    (Response: DIFFERENT t → OBSERVE (DIFFERENT t) → Bool)
    (dx: (OBSERVE t) → DIFFERENT (OBSERVE t) → Bool)
    (ddx: (DIFFERENT (OBSERVE t)) → DIFFERENT (OBSERVE (DIFFERENT t)) → Bool)
    where

  emit? : t → OBSERVE t → Bool
  receive? : DIFFERENT t → OBSERVE (DIFFERENT t) → Bool

namespace TIMED
variable {ddt: Type i → Type i → Type i → Prop}
         {dt: Type i → Type i → Prop}
         {t: Type i}
         {x: t → Type i}
         {Stimulus: t → DIFFERENT t → Bool}
         {Response: DIFFERENT t → OBSERVE (DIFFERENT t) → Bool}
         {dx: (OBSERVE t) → DIFFERENT (OBSERVE t) → Bool}
         {ddx: (DIFFERENT (OBSERVE t)) → DIFFERENT (OBSERVE (DIFFERENT t)) → Bool}
         [model: TIMED ddt dt t x Stimulus Response dx ddx]

def emit
    (s: t)
    (o: OBSERVE t)
      : Bool :=
  model.emit? s o

def receive
    (s: DIFFERENT t)
    (o: OBSERVE (DIFFERENT t))
      : Bool :=
  model.receive? s o

end TIMED


inductive CounterOf
    (ddt: Type i → Type i → Type i → Prop)
    (dt: Type i → Type i → Prop)
    (t: Type i)
    (x: t → Type i)
    (Stimulus: t → DIFFERENT t → Bool)
    (Response: DIFFERENT t → OBSERVE (DIFFERENT t) → Bool)
    (dx: (OBSERVE t) → DIFFERENT (OBSERVE t) → Bool)
    (ddx: (DIFFERENT (OBSERVE t)) → DIFFERENT (OBSERVE (DIFFERENT t)) → Bool)
    [model: TIMED ddt dt t x Stimulus Response dx ddx]
  | nil : CounterOf ddt dt t x Stimulus Response dx ddx
  | cons : (s: t) →
           (o: OBSERVE t) →
           (h1: model.emit s o) →
           CounterOf ddt dt t x Stimulus Response dx ddx →
           CounterOf ddt dt t x Stimulus Response dx ddx




class AGGREGATED
    (Accumulate: Type i → Type i → Type i → Prop)
    (Count: Type i → Type i → Prop)
    (Trial: Type i)
    (Accumulation: Type (i+1))
    (Counter: Trial → Type i)

    (Accumulated: Trial → DIFFERENT Trial → Bool)
    (Repeatable: DIFFERENT Trial → OBSERVE (DIFFERENT Trial) → Bool)
    (Predictable: (OBSERVE Trial) → DIFFERENT (OBSERVE Trial) → Bool)
    (Trend: (DIFFERENT (OBSERVE Trial)) → DIFFERENT (OBSERVE (DIFFERENT Trial)) → Bool)

    [timer: TIMED Accumulate Count
                  Trial Counter
                  Accumulated Repeatable Predictable Trend]
      where

  accumulated? : Trial → DIFFERENT Trial → Bool := Accumulated

namespace AGGREGATED
variable  {Accumulate: Type i → Type i → Type i → Prop}
          {Count: Type i → Type i → Prop}
          {Trial: Type i}
          {Accumulation: Type (i+1)}
          {Counter: Trial → Type i}
          {Accumulated: Trial → DIFFERENT Trial → Bool}
          {Repeatable: DIFFERENT Trial → OBSERVE (DIFFERENT Trial) → Bool}
          {Predictable: (OBSERVE Trial) → DIFFERENT (OBSERVE Trial) → Bool}
          {Trend: (DIFFERENT (OBSERVE Trial)) → DIFFERENT (OBSERVE (DIFFERENT Trial)) → Bool}
          [timer: TIMED Accumulate Count
                  Trial Counter
                  Accumulated Repeatable Predictable Trend]
          {Accumulattion: Type (i+1)}
          [model: AGGREGATED Accumulate Count Trial Accumulation Counter Accumulated Repeatable Predictable Trend]

def accumulated
    (t: Trial)
    (o: DIFFERENT Trial)
      : Bool :=
  model.accumulated? t o

end AGGREGATED

inductive AccumulationOf
    (Accumulate: Type i → Type i → Type i → Prop)
    (Count: Type i → Type i → Prop)
    (Trial: Type i)
    (Accumulation: Type (i+1))
    (Counter: Trial → Type i)

    (Accumulated: Trial → DIFFERENT Trial → Bool)
    (Repeatable: DIFFERENT Trial → OBSERVE (DIFFERENT Trial) → Bool)
    (Predictable: (OBSERVE Trial) → DIFFERENT (OBSERVE Trial) → Bool)
    (Trend: (DIFFERENT (OBSERVE Trial)) → DIFFERENT (OBSERVE (DIFFERENT Trial)) → Bool)
    [timer: TIMED Accumulate Count
            Trial Counter
            Accumulated Repeatable Predictable Trend]
    [model: AGGREGATED Accumulate Count Trial Accumulation Counter Accumulated Repeatable Predictable Trend]
  | nil : AccumulationOf Accumulate Count Trial Accumulation Counter Accumulated Repeatable Predictable Trend
  | cons : (t: Trial) →
           (o: DIFFERENT Trial) →
           (h1: model.accumulated? t o) →
           AccumulationOf Accumulate Count Trial Accumulation Counter Accumulated Repeatable Predictable Trend →
           AccumulationOf Accumulate Count Trial Accumulation Counter Accumulated Repeatable Predictable Trend

abbrev ACCUMULATION (Trial: Type i) := Trial × DIFFERENT Trial  -- Check that out, an ordered pair!


/- -------------------------
I think everything below here just needs an LE operator on a decomposition
-/

-- This is a fun way to define real number symbols by describing the gemoetric
-- computation, bounding the number ever tighter..
abbrev PAIR (Symbol: Type i) := Symbol × Symbol
abbrev ORDERED_PAIR (Symbol_1: Type i) (Symbol_2: Type (i+1)) := Symbol_1 × Symbol_2
abbrev COUNTING (Symbol: Type i) := ORDERED_PAIR Symbol (OBSERVE Symbol)
abbrev NUMBER (Symbol: Type i) := ORDERED_PAIR Symbol (COUNTING Symbol)
abbrev BOUNDS (Symbol: Type i) := ORDERED_PAIR (NUMBER Symbol) (NUMBER (OBSERVE Symbol))
abbrev SEQUENCE (Symbol: Type i) := ORDERED_PAIR (NUMBER Symbol) (BOUNDS Symbol)


class REAL
    (Metaphysical: Type (i+1) → Type (i+1) → Prop)
    (Computational: Type (i+1) → Type (i+1) → Prop)
    (Symbol: Type i)
    (Decomposition: Type (i+1))
    (Value: Type (i+1))
    (Iterated : Symbol → OBSERVE Value → Bool) -- Decomposition is the midpoint of the bounds. -- These can be overlapped!
    (Computed: Symbol → OBSERVE Decomposition → Bool) -- The value is the limit of the decomposition.

    -- This needs refactoring as i am starting to bog again.
    (Converged: Symbol → Value → Bool) -- Is the decomposition the bisection of the bounds?
    (LE: Symbol → Symbol → Bool) -- Less than is not possible, on LE. need to make a poset.
    [DISTINGUISHABLE Metaphysical Value]
    [DISTINGUISHABLE Metaphysical Decomposition]
    [DISTINGUISHABLE Computational Value]
    [DISTINGUISHABLE Computational Decomposition]
    [ADMISSIBLE Metaphysical Symbol Value Iterated]
    [ADMISSIBLE Metaphysical Symbol Decomposition Computed]
    [ADMISSIBLE Computational Symbol Value Iterated]
    [ADMISSIBLE Computational Symbol Decomposition Computed]
    [PAIRED Metaphysical Symbol Value Iterated]
    [PAIRED Metaphysical Symbol Decomposition Computed]
    [PAIRED Computational Symbol Value Iterated]
    [PAIRED Computational Symbol Decomposition Computed]
    [ORDERED Metaphysical Symbol Value Iterated Converged]
    [ORDERED Metaphysical Symbol Decomposition Computed fun d i => Computed d (some { down := i })]
    [ORDERED Computational Symbol Value Iterated Converged]
    [ORDERED Computational Symbol Decomposition Computed fun d i => Computed d (some { down := i })]
    [ORDERED Metaphysical Symbol Decomposition Computed fun d i => Computed d (some { down := i })]
    [ORDERED Computational Symbol Value Iterated Converged]
    [ORDERED Computational Symbol Value Iterated fun d o => Iterated d (some { down := o })]
    [COMPUTABLE Metaphysical Computational Symbol Decomposition Value Computed Iterated]
      where

  le? : Symbol → Symbol → Bool := LE
  eq? : Symbol → Symbol → Bool := λ s1 s2 => LE s1 s2 && LE s2 s1





namespace REAL

variable {Metaphysical: Type (i+1) → Type (i+1) → Prop}
         {Computational: Type (i+1) → Type (i+1) → Prop}
         {Symbol: Type i}
         {Decomposition: Type (i+1)}
         {Value: Type (i+1)}
         {Iterated : Symbol → OBSERVE Value → Bool}
         {Computed: Symbol → OBSERVE Decomposition → Bool}
         {Converged: Symbol → Value → Bool}
         {LE: Symbol → Symbol → Bool}
         [DISTINGUISHABLE Metaphysical Value]
         [DISTINGUISHABLE Metaphysical Decomposition]
         [DISTINGUISHABLE Computational Value]
         [DISTINGUISHABLE Computational Decomposition]
         [ADMISSIBLE Metaphysical Symbol Value Iterated]
         [ADMISSIBLE Metaphysical Symbol Decomposition Computed]
         [ADMISSIBLE Computational Symbol Value Iterated]
         [ADMISSIBLE Computational Symbol Decomposition Computed]
         [PAIRED Metaphysical Symbol Value Iterated]
         [PAIRED Metaphysical Symbol Decomposition Computed]
         [PAIRED Computational Symbol Value Iterated]
         [PAIRED Computational Symbol Decomposition Computed]
         [ORDERED Metaphysical Symbol Value Iterated Converged]
         [ORDERED Metaphysical Symbol Decomposition Computed fun d i => Computed d (some { down := i })]
         [ORDERED Computational Symbol Value Iterated Converged]
         [ORDERED Computational Symbol Decomposition Computed fun d i => Computed d (some { down := i })]
         [ORDERED Metaphysical Symbol Decomposition Computed fun d i => Computed d (some { down := i })]
         [ORDERED Computational Symbol Value Iterated Converged]
         [ORDERED Computational Symbol Value Iterated fun d o => Iterated d (some { down := o })]
         [COMPUTABLE Metaphysical Computational Symbol Decomposition Value Computed Iterated]
         [ψ : REAL Metaphysical Computational Symbol Decomposition Value Iterated Computed Converged LE]

def le
    (s1: Symbol)
    (s2: Symbol)
      : Bool :=
  ψ.le? s1 s2

def eq
    (s1: Symbol)
    (s2: Symbol)
      : Bool :=
  ψ.eq? s1 s2

end REAL


end Measurement
