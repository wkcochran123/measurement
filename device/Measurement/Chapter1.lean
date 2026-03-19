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
-- If you have seen it, then you can look directly at the symbol of the result.
abbrev OBSERVED (x: Type i) := ULift.{i+1,i} x

-- A different symbol is just some other symbol.
abbrev DIFFERENT (Symbol : Type i) := Option Symbol
-- Symbol is the symbol we care about since everything is a symbol
-- in measurement.  Measurement is a representation.
abbrev TOKEN (Symbol : Type i) := DIFFERENT Symbol

abbrev BOOL (Symbol :Type i) := TOKEN Symbol
def FALSE {Symbol: Type i} : (Option Symbol) := none
-- We define FALSE to be the symbol that represents unrepresentable symbols.
-- This is a DISTINCT Symbol, although it will never be observed as such.




/- --------------------------------------------------------
DISTINGUISHABLE.

Something is DISTINGUISHABLE from others if there exists
some characteristic that is either present or absent from
the something relative to the others.
-/
class DISTINGUISHABLE
    (Characterisitic : Type i → Type i → Option (Type i))
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
  -- don't know what that is or what "DIFFERENT" means.

  -- A symbol just might get resolved, if you read more.
  æther               : Type i
  -- But wait, didn't Michelson and Morley show that the æther doesn't exist?
  -- Maybe, but we don't know that yet.  We just know that it is not distinguishable
  -- from other symbols, so we can't tell if it exists or not.  It is a symbol that
  -- is indistinguishable from all other symbols, so it could be anything, including
  -- nothing.  Hence, æther, the universal substance that unites all. The thing that
  -- makes up existence.


  -- Are two symbols different?
  --  Supplied by the characteristic in the typename and evaluated by the compiler.
  different?          : Type i → Type i → Prop :=
                (λ s1 s2 => ∃ (_ : Type i), match Characterisitic s1 s2 with
                                              | some _ => true
                                              | none => false)

  -- Have we distinguished a particular symbol from all others?
  -- Supplied logically here as there eixts a variable c of type i
  -- such that the different? mapping can be applied to provide the
  -- necessary Option (Type i)erty.  Nothing has been instantiated, just named.

  distinguished?      : Type i → Prop := λ s => ∃ (c : Type i), different? c s



namespace DISTINGUISHABLE
variable {Characterisitic : Type i → Type i → Option (Type i)}
         {Carrier: Type i}
         [d: DISTINGUISHABLE Characterisitic Carrier]


def different
    (s1: Type i)
    (s2: Type i)
      : Prop :=
  d.different? s1 s2

def distinguished
    (s: Type i)
      : Prop :=
  d.distinguished? s

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
    (Characteristic : Type i → Type i → Option (Type i))
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
    (Before: Type (max 1 i))
    (After: Type (i+1))
    (Observation: Before → OBSERVE After → Bool)
    where

  -- Is this a possible future state of the universe? Dunno, could be.
  admissible? : Before → OBSERVE After → Bool := Observation

namespace ADMISSIBLE
variable {Event : Type (i+1) → Type (i+1) → Prop}
         {Before: Type i}
         {After: Type (i+1)}
         {Observation: Before → OBSERVE After → Bool}
         (ADMISSIBLE Event)

def admissible
    (before: Before)
    (after: OBSERVE After)
      : Bool :=
  Observation before after

end ADMISSIBLE

abbrev AFTER (x : Type i) := ULift.{i+1, i} x

-- Once we have the concept of an admissible event, we can enumerate
-- those, producing a list in time.  This is a history of events
-- recorded as a symbol.  I wonder what that symbol could be? If
-- we have done this correctly, this is a list of entropies as they
-- evolve from one point to the next.
inductive CountOf
    (Event : Type (i+1) → Type (i+1) → Prop)
    (Before: Type (max 1 i))
    (After: Type (i+1))
    (Observation: Before → OBSERVE After → Bool)
    [ADMISSIBLE Event Before After Observation]
  | nil : CountOf Event Before After Observation
  | cons : (Before → OBSERVE After → Bool) →           -- Now this is pod racing---- er, counting.
           CountOf Event Before After Observation →  -- tick tock, before after
           CountOf Event Before After Observation






/-
Measurement/Chapter3.lean

DISTINCT and LedgerOf.

DISTINCT is the NAND of DISTINGUISHABLE and ADMISSIBLE.

Two symbols are DISTINCT when it is NOT the case that they are
both distinguishable AND admissible at the same ledger position
simultaneously.

This is the compile-time spinor. The compiler is the rotation group.
Elaboration failure is the sign change.

No equality is used anywhere. Only < and apart-from.
-/



/-
Measurement/Chapter3.lean

DISTINCT, LedgerOf, RefinementOf, CALIBRATION.

DISTINCT is the NAND of DISTINGUISHABLE and ADMISSIBLE.

Two symbols are DISTINCT when it is NOT the case that they are
both distinguishable AND admissible at the same ledger position
simultaneously.

This is the compile-time spinor. The compiler is the rotation group.
Elaboration failure is the sign change.

No equality is used anywhere. Only < and apart-from.

Universe structure:
  i     -- physical symbols, ledger entries
  i+1   -- the instrument: OBSERVE, DISTINCT, LedgerOf, RefinementOf
  i+2   -- the standard:   CALIBRATION
-/


/- --------------------------------------------------------
DISTINCT

DISTINGUISHABLE says: there exists a characteristic separating s₁ from s₂.
ADMISSIBLE says:      s₂ is a possible continuation from s₁.

DISTINCT = DISTINGUISHABLE NAND ADMISSIBLE

The truth table:

  DISTINGUISHABLE | ADMISSIBLE | DISTINCT
  ----------------|------------|----------
  false           | false      | true   -- neither fires, no constraint, æther
  false           | true       | true   -- admissible but unseparated, still æther
  true            | false      | true   -- separated but not a valid continuation
  TRUE            | TRUE       | FALSE  -- both fire: contradiction, compiler rejects

The only case the compiler rejects is when a symbol claims to be
both fully distinguishable AND fully admissible at the same ledger
position. That case cannot enter the record. That is the excluded case.
That is NAND.

Note: no equality is used. Only the Bool result of distinguished? and
admissible? — both of which are < style separations, not identity claims.
-/

class DISTINCT
    (Event        : Type (i+1) → Type (i+1) → Prop)
    (Feature      : Type (max 1 i) → Type (max 1 i) → Option (Type (max 1 i)))
    (Before       : Type i)
    (Stimulus      : Type (max 1 i))
    (Response     : Type (i+1))
    (Observation  : Before → OBSERVE Response → Bool)
    [d : DISTINGUISHABLE Feature Stimulus]
    [a : ADMISSIBLE Event Before Stimulus Response Observation]
    where

  -- The NAND gate.
  -- A position in the ledger is DISTINCT when it is NOT the case
  -- that the symbol is both distinguished AND admissible there.
  -- Bool arithmetic: NAND(p, q) = !(p && q)
  -- No equality. Only the separation induced by < through
  -- distinguished? and admissible?.
  distinct? : Before → After → Bool :=
    λ before after =>
      !(a.distinguished? before (some (AFTER after))
        &&
        a.admissible? before after)

  -- The ordering witness.
  -- If s₁ precedes s₂ in the ledger, then s₂ is DISTINCT from s₁.
  -- We never ask if they are equal. We only ask which comes first.
  -- The < relation is the only relation. Distinction is witnessed
  -- by ordering, not by identity.
  precedes? : Before → After → Bool :=
    λ before after => a.distinguished? before (some (ULift.up after))


namespace DISTINCT

variable {Event       : Type (i+1) → Type (i+1) → Option (Type i)}
         {Before      : Type i}
         {After       : Type (i+1)}
         {Observation : Before → OBSERVE After → Bool}
         [d    : DISTINGUISHABLE Event After]
         [a    : ADMISSIBLE Event Before After Observation]
         [dist : DISTINCT Event Before After Observation]

-- Is this position in the ledger distinct?
-- This is the compile-time NAND gate.
-- If this returns false, the compiler rejects the term.
-- That rejection IS the sign change. That rejection IS the spinor.
def distinct
    (before : Before)
    (after  : After)
    : Bool :=
  dist.distinct? before after

-- Does before precede after in the ledger ordering?
-- Only < is used. No equality.
def precedes
    (before : Before)
    (after  : After)
    : Bool :=
  dist.precedes? before after

-- The NAND witness as a Option (Type i), for use in inductive types below.
-- This fires at elaboration time. If the compiler cannot construct
-- this, the ledger entry is inadmissible.
def nand_holds
    (before : Before)
    (after  : After)
    : Option (Type i) :=
  dist.distinct? before after = true

end DISTINCT


/- --------------------------------------------------------
LedgerOf

The ledger is the ordered, irreversible accumulation of DISTINCT entries.

Each entry carries:
  1. The before-state (the current ledger position)
  2. The after-state (the new symbol being recorded)
  3. A proof that DISTINCT holds at this position — the NAND gate passed
  4. A proof that before precedes after — the < relation holds

No equality anywhere. The ledger grows only by < and DISTINCT.
Entries cannot be removed (irreversibility).
Entries cannot be reordered (the < relation fixes the order at write time).

This is the Euclid Effect: once a distinction has been recorded,
it cannot be removed by any extension.
-/

inductive LedgerOf
    (Event        : Type (i+1) → Type (i+1) → Option (Type i))
    (Before       : Type i)
    (After        : Type (i+1))
    (Observation  : Before → OBSERVE After → Bool)
    [d    : DISTINGUISHABLE Event After]
    [a    : ADMISSIBLE Event Before After Observation]
    [dist : DISTINCT Event Before After Observation]

  -- The empty ledger. The universe before the first distinction.
  -- The æther. Undifferentiated. No entries, no order, no time.
  | nil : LedgerOf Event Before After Observation

  -- A new ledger entry.
  -- We record:
  --   before  : the current state
  --   after   : the new symbol
  --   h_dist  : proof that DISTINCT holds — the NAND gate passed
  --             at compile time. If this proof cannot be constructed,
  --             this cons cannot be constructed. The compiler is the oracle.
  --   h_prec  : proof that before < after in the ledger ordering.
  --             No equality. Only precedence.
  --   rest    : the prior ledger, unchanged and unchangeable.
  --             Irreversibility is structural: rest is a parameter,
  --             not a mutable field. Once passed in, it is fixed.
  | cons
      (before  : Before)
      (after   : After)
      (h_dist  : dist.distinct?  before after = true)
      (h_prec  : dist.precedes?  before after = true)
      (rest    : LedgerOf Event Before After Observation)
      : LedgerOf Event Before After Observation


namespace LedgerOf

variable {Event       : Type (i+1) → Type (i+1) → Option (Type i)}
         {Before      : Type i}
         {After       : Type (i+1)}
         {Observation : Before → OBSERVE After → Bool}
         [d    : DISTINGUISHABLE Event After]
         [a    : ADMISSIBLE Event Before After Observation]
         [dist : DISTINCT Event Before After Observation]

-- The size of the ledger.
-- This is the count of recorded distinctions.
-- It is the informational interval τ — the tally of irreducible
-- refinement steps.
-- No equality. Just counting.
def size : LedgerOf Event Before After Observation → Nat
  | nil               => 0
  | cons _ _ _ _ rest => size rest + 1

-- The most recent entry.
-- Returns none if the ledger is empty (the æther state).
-- Never returns equality — only the last recorded symbol.
def last : LedgerOf Event Before After Observation
           → Option (Before × After)
  | nil               => none
  | cons b a _ _ nil  => some (b, a)
  | cons _ _ _ _ rest => last rest

-- The first entry ever recorded.
-- The initial condition. The first distinction made.
-- The moment the æther became something.
def first : LedgerOf Event Before After Observation
            → Option (Before × After)
  | nil               => none
  | cons b a _ _ nil  => some (b, a)
  | cons _ _ _ _ rest => first rest

-- Is the ledger empty?
-- Silence is a fact. An empty ledger is not ignorance —
-- it is the certified absence of any distinction above
-- the current resolution. The Marconi Effect.
def isEmpty : LedgerOf Event Before After Observation → Bool
  | nil => true
  | _   => false

-- Append a new distinction to the ledger.
-- The NAND gate is checked at compile time via the proof obligations
-- h_dist and h_prec. If these cannot be satisfied, the append
-- cannot be constructed. The ledger refuses the entry.
-- This is the oracle speaking.
def append
    (ledger  : LedgerOf Event Before After Observation)
    (before  : Before)
    (after   : After)
    (h_dist  : dist.distinct? before after = true)
    (h_prec  : dist.precedes? before after = true)
    : LedgerOf Event Before After Observation :=
  cons before after h_dist h_prec ledger

-- The ledger can only grow. This witnesses irreversibility.
-- size never decreases under append.
-- No equality needed — just the successor relation on Nat,
-- which is itself built from < and distinct.
theorem size_grows
    (ledger : LedgerOf Event Before After Observation)
    (before : Before)
    (after  : After)
    (h_dist : dist.distinct? before after = true)
    (h_prec : dist.precedes? before after = true)
    : size (append ledger before after h_dist h_prec) =
      size ledger + 1 := by
  simp [append, size]

-- The constraint of silence.
-- An empty ledger has size 0.
-- Silence is not disorder — it is the certified ground state.
theorem empty_size
    : size (nil (Event := Event) (Before := Before)
               (After := After) (Observation := Observation)) = 0 := by
  simp [size]

end LedgerOf


/- --------------------------------------------------------
RefinementOf

A RefinementOf L₁ L₂ is the witness that L₂ was built
by extending L₁ — and only by extending it.

L₁ is the prior record.
L₂ is the current record.

RefinementOf says: everything in L₁ is still in L₂,
in the same order, unchanged.

This is not equality. It is not a comparison.
It is a structural witness that one ledger
is a strict extension of another.

Sits next to LedgerOf at universe level i+1.
LedgerOf is the thing. RefinementOf is the proof about the thing.

The Euclid Effect: once recorded, always recorded.
The constraint of silence: nothing inserted between existing entries.
The arrow of time: refinement goes one way only.
ΔS ≥ 0: size is monotone under refinement.
-/

inductive RefinementOf
    (Event       : Type (i+1) → Type (i+1) → Option (Type i))
    (Before      : Type i)
    (After       : Type (i+1))
    (Observation : Before → OBSERVE After → Bool)
    [d    : DISTINGUISHABLE Event After]
    [a    : ADMISSIBLE Event Before After Observation]
    [dist : DISTINCT Event Before After Observation]
    : LedgerOf Event Before After Observation
    → LedgerOf Event Before After Observation
    → Option (Type i)

  -- The empty ledger refines into anything.
  -- Silence is compatible with every record.
  -- The æther is the ground state from which
  -- all refinements begin.
  | empty
      : ∀ (l : LedgerOf Event Before After Observation),
        RefinementOf Event Before After Observation
          LedgerOf.nil
          l

  -- A non-empty ledger refines into a larger one
  -- only if the new entry passes DISTINCT —
  -- the NAND gate — and the prior ledger already
  -- refines into the tail of the new one.
  -- No modification of existing entries.
  -- No insertion between existing entries.
  -- Only append. Only forward. Only larger.
  | step
      (before  : Before)
      (after   : After)
      (h_dist  : dist.distinct? before after = true)
      (h_prec  : dist.precedes? before after = true)
      (l₁ l₂  : LedgerOf Event Before After Observation)
      (h       : RefinementOf Event Before After Observation l₁ l₂)
      : RefinementOf Event Before After Observation
          (LedgerOf.cons before after h_dist h_prec l₁)
          (LedgerOf.cons before after h_dist h_prec l₂)


namespace RefinementOf

variable {Event       : Type (i+1) → Type (i+1) → Option (Type i)}
         {Before      : Type i}
         {After       : Type (i+1)}
         {Observation : Before → OBSERVE After → Bool}
         [d    : DISTINGUISHABLE Event After]
         [a    : ADMISSIBLE Event Before After Observation]
         [dist : DISTINCT Event Before After Observation]

-- Any ledger is a refinement of the empty ledger.
-- You can always start from silence.
-- Named for use in trans.
theorem from_nil
    (l : LedgerOf Event Before After Observation)
    : RefinementOf Event Before After Observation LedgerOf.nil l :=
  empty l

-- A ledger refines itself.
-- Not equality — structural self-witness.
-- The record is consistent with its own history.
theorem refl
    (l : LedgerOf Event Before After Observation)
    : RefinementOf Event Before After Observation l l := by
  induction l with
  | nil               => exact empty LedgerOf.nil
  | cons b a hd hp rest ih => exact step b a hd hp _ _ ih

-- Refinement is monotone on size.
-- The ledger only grows. ΔS ≥ 0.
-- This is the Second Law as a theorem of the type system.
-- No equality. Only ≤.
theorem size_le
    (l₁ l₂ : LedgerOf Event Before After Observation)
    (h : RefinementOf Event Before After Observation l₁ l₂)
    : LedgerOf.size l₁ ≤ LedgerOf.size l₂ := by
  induction h with
  | empty l                => exact Nat.zero_le _
  | step _ _ _ _ _ _ _ ih => exact Nat.succ_le_succ ih

end RefinementOf


-- We can assert a TRUTH as being some Symbol that survives the act of observation.
abbrev TRUE  (Symbol : Type i) := TOKEN Symbol  -- TRUE, a certified presence
abbrev RELATION (Symbol : Type i) := TRUE (TOKEN Symbol)  -- RELATION, a certified connection between symbols
abbrev PROPERTY (Symbol : Type i) := TRUE (RELATION Symbol)  -- PROPERTY, a certified characteristic of a symbol
abbrev FEATURE (Symbol : Type i) := TRUE (PROPERTY Symbol)  -- VALUE, a certified measurement of a symbol's property
abbrev NATURAL_NUMBER (Symbol : Type i) := Option Symbol  -- A symbol that can be counted, like a tick mark on a ruler.

/- --------------------------------------------------------
CALIBRATION

Calibration is the first refinement.
It is not a ledger entry. It is the act of establishing
that an instrument is admissible before it begins recording.

Universe structure:
  i     -- physical symbols, ledger entries        (Before, After)
  i+1   -- the instrument                          (LedgerOf, RefinementOf)
  i+2   -- the standard against which the
           instrument is calibrated                (CALIBRATION)

RefinementOf.empty is structurally valid at i+1 —
silence is always a prefix of anything.

CALIBRATION is the semantic gate at i+2 — it certifies
that the instrument was properly established before it
was used. The first refinement is trusted only because
the standard at i+2 certified the instrument at i+1
before any entry was made at i.

The three universe levels are the three things Chapter 2
says an instrument requires:
  i     -- a phenomenon to measure
  i+1   -- a sensor to interact with it and a gauge to commit the result
  i+2   -- a standard to calibrate the gauge against

Calibration connects the gauge to the external standard.
It cannot live at the same level as the gauge —
it is the thing that certifies the gauge, so it must sit above it.
-/

class CALIBRATION
    (Standard    : Type (i+2))
    (Event       : Type (i+1) → Type (i+1) → Option (Type i))
    (Before      : Type i)
    (After       : Type (i+1))
    (Observation : Before → OBSERVE After → Bool)
    [d    : DISTINGUISHABLE Event After]
    [a    : ADMISSIBLE Event Before After Observation]
    [dist : DISTINCT Event Before After Observation]
    where

  -- The standard against which the instrument is calibrated.
  -- Lives at i+2. Not observable from within the ledger at i+1.
  -- The metaphysical reference.
  -- The ruler before the ruler is used to measure anything.
  standard : Standard

  -- Is this instrument calibrated against the standard?
  -- This is the semantic guard on the first refinement.
  -- If this does not hold, no ledger entry is ever trusted.
  -- The instrument has not yet been established.
  -- RefinementOf.empty is structurally valid regardless —
  -- but CALIBRATION adds the semantic constraint that the
  -- instrument was properly grounded before use.
  calibrated? : Standard
              → (Before → OBSERVE After → Bool)
              → Bool

  -- The compile-time witness that calibration holds.
  -- If Lean cannot produce this proof, the CALIBRATION
  -- instance cannot be constructed.
  -- No instrument exists. No ledger entry is trusted.
  -- The oracle speaks before the first tick of the clock.
  calibration_holds : calibrated? standard Observation = true


namespace CALIBRATION

variable {Standard    : Type (i+2)}
         {Event       : Type (i+1) → Type (i+1) → Option (Type i)}
         {Before      : Type i}
         {After       : Type (i+1)}
         {Observation : Before → OBSERVE After → Bool}
         [d    : DISTINGUISHABLE Event After]
         [a    : ADMISSIBLE Event Before After Observation]
         [dist : DISTINCT Event Before After Observation]
         [cal  : CALIBRATION Standard Event Before After Observation]

-- A calibrated instrument may begin recording.
-- The empty ledger under a calibrated instrument is the
-- certified ground state — not æther, but silence with
-- a known instrument standing by.
-- This is the first refinement: nil to ready.
def initialLedger
    : LedgerOf Event Before After Observation :=
  LedgerOf.nil

-- The calibration witness for the first refinement.
-- RefinementOf.empty is always structurally valid.
-- CALIBRATION certifies it is also semantically valid:
-- the instrument exists, the clock is ready to tick,
-- the standard has spoken.
def firstRefinement
    (l : LedgerOf Event Before After Observation)
    : RefinementOf Event Before After Observation
        LedgerOf.nil
        l :=
  RefinementOf.empty l

end CALIBRATION





/- --------------------------------------------------------
-/

class CORRELATED
    (Ordering: Type (i+1) → Type (i+1) → Option (Type i))
    (Symbol: Type i)
    (Encoding: Type (i+1))
    (Encode: Symbol → OBSERVE Encoding → Bool)
    [DISTINGUISHABLE Ordering Encoding]
    [ADMISSIBLE Ordering Symbol Encoding Encode]
    where

  encoded? : Symbol → OBSERVE Encoding → Bool := Encode

namespace CORRELATED
variable {Ordering: Type (i+1) → Type (i+1) → Option (Type i)}
         {Symbol: Type i}
         {Encoding: Type (i+1)}
         {Encode: Symbol → OBSERVE Encoding → Bool}
         [DISTINGUISHABLE Ordering Encoding]
         [ADMISSIBLE Ordering Symbol Encoding Encode]
         [parsed_symbol: CORRELATED Ordering Symbol Encoding Encode]

def encoded
    (input: Symbol)
    (output: OBSERVE Encoding)
      : Bool :=
  parsed_symbol.encoded? input output

end CORRELATED


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
    (Ordering: Type (i+1) → Type (i+1) → Option (Type i))
    (First: Type i)
    (Second: Type (i+1))
    (Encode: First → OBSERVE Second → Bool)
    [DISTINGUISHABLE Ordering Second]
    [ADMISSIBLE Ordering First Second Encode]
    [parsed_symbol: CORRELATED Ordering First Second Encode]

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
    (Ordering: Type (i+1) → Type (i+1) → Option (Type i))
    (Less: Type i)
    (More: Type (i+1))
    (Counting: Less → OBSERVE More → Bool)
    (Relation: Less → More → Bool)
    [DISTINGUISHABLE Ordering More]
    [ADMISSIBLE Ordering Less More Counting]
    [parsed_symbol: CORRELATED Ordering Less More Counting]
    where

  -- You were expecting?  Now, all we need
  -- is std::sort()! Any one got a __C_PLUS_PLUS__ binary
  -- lying around?
  less_than?    : Less → More → Bool := Relation

  correlant?    : Less → More → Bool := λ l m => less_than? l m

namespace ORDERED
variable  {Ordering: Type (i+1) → Type (i+1) → Option (Type i)}
          {Less: Type i}
          {More: Type (i+1)}
          {Counting: Less → OBSERVE More → Bool}
          {Relation: Less → More → Bool}
          [DISTINGUISHABLE Ordering More]
          [ADMISSIBLE Ordering Less More Counting]
          [parsed_symbol: CORRELATED Ordering Less More Counting]
          [ordered: ORDERED Ordering Less More Counting Relation]

def less_than
    (l: Less)
    (m: More)
      : Bool :=
  ordered.less_than? l m
end ORDERED


inductive SortedPairsOf
    (Ordering: Type (i+1) → Type (i+1) → Option (Type i))
    (Less: Type i)
    (More: Type (i+1))
    (Counting: Less → OBSERVE More → Bool)
    (Relation: Less → More → Bool)
    [DISTINGUISHABLE Ordering More]
    [ADMISSIBLE Ordering Less More Counting]
    [parsed_symbol: CORRELATED Ordering Less More Counting]
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
    (DecodeInstruction: Type (i+1) → Type (i+1) → Option (Type i))
    (ExecuteInstruction: Type (i+1) → Type (i+1) → Option (Type i))
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
    [CORRELATED DecodeInstruction Data Instruction Decoded]
    [CORRELATED ExecuteInstruction Data Output Executed]
    [ORDERED DecodeInstruction Data Instruction Decoded (λ d i => Decoded d (some (ULift.up i)))]
    [ORDERED ExecuteInstruction Data Output Executed (λ d o => Executed d (some (ULift.up o)))]
      where

  decoded? : Data → OBSERVE Instruction → Bool := Decoded
  executed? : Data → OBSERVE Output → Bool := Executed


namespace COMPUTABLE
variable  {DecodeInstruction: Type (i+1) → Type (i+1) → Option (Type i)}
          {ExecuteInstruction: Type (i+1) → Type (i+1) → Option (Type i)}
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
          [CORRELATED DecodeInstruction Data Instruction Decoded]
          [CORRELATED ExecuteInstruction Data Output Executed]
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
    (DecodeInstruction: Type (i+1) → Type (i+1) → Option (Type i))
    (ExecuteInstruction: Type (i+1) → Type (i+1) → Option (Type i))
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
    [CORRELATED DecodeInstruction Data Instruction Decoded]
    [CORRELATED ExecuteInstruction Data Output Executed]
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
    (Labeled: Type (i+1) → Type (i+1) → Option (Type i))
    (Symbol: Type i)
    (Name: Symbol → Type i)
    (Representation: Type (i+1))
    (EncodedSymbol: Symbol → OBSERVE Representation → Bool)
    (Encoding: Symbol → Representation → Bool)
    [DISTINGUISHABLE Labeled Representation]
    [ADMISSIBLE Labeled Symbol Representation EncodedSymbol]
    [CORRELATED Labeled Symbol Representation EncodedSymbol]
    [ORDERED Labeled Symbol Representation EncodedSymbol Encoding]
      where
  encoded? : Symbol → OBSERVE Representation → Bool := EncodedSymbol
  name? : Symbol → Type i := Name
  encoding? : Symbol → Representation → Bool := Encoding

namespace ENCODED
variable {Labeled: Type (i+1) → Type (i+1) → Option (Type i)}
         {Symbol: Type i}
         {Name: Symbol → Type i}
         {Representation: Type (i+1)}
         {EncodedSymbol: Symbol → OBSERVE Representation → Bool}
         {Encoding: Symbol → Representation → Bool}
         [DISTINGUISHABLE Labeled Representation]
         [ADMISSIBLE Labeled Symbol Representation EncodedSymbol]
         [CORRELATED Labeled Symbol Representation EncodedSymbol]
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
    (Labeled: Type (i+1) → Type (i+1) → Option (Type i))
    (Symbol: Type i)
    (Name: Symbol → Type i)
    (Representation: Type (i+1))
    (EncodedSymbol: Symbol → OBSERVE Representation → Bool)
    (Encoding: Symbol → Representation → Bool)
    [DISTINGUISHABLE Labeled Representation]
    [ADMISSIBLE Labeled Symbol Representation EncodedSymbol]
    [CORRELATED Labeled Symbol Representation EncodedSymbol]
    [ORDERED Labeled Symbol Representation EncodedSymbol Encoding]
    [index: ENCODED Labeled Symbol Name Representation EncodedSymbol Encoding]

  | nil : RepresentationOf Labeled Symbol Name Representation EncodedSymbol Encoding
  | cons : (s: Symbol) →
           (r: OBSERVE Representation) →
           (h1: index.encoded? s r) →
           RepresentationOf Labeled Symbol Name Representation EncodedSymbol Encoding →
           RepresentationOf Labeled Symbol Name Representation EncodedSymbol Encoding


structure Token
    (Labeled        : Type (i+1) → Type (i+1) → Option (Type i))
    (Symbol         : Type i)
    (Name           : Symbol → Type i)
    (Representation : Type (i+1))
    (Observation    : Symbol → OBSERVE Representation → Bool)
    (Encoding       : Symbol → Representation → Bool)
    where
  distinguishable : DISTINGUISHABLE Labeled Representation
  admissible      : ADMISSIBLE Labeled Symbol Representation Observation
  correlated      : CORRELATED Labeled Symbol Representation Observation
  ordered         : ORDERED Labeled Symbol Representation Observation Encoding
  encoded         : ENCODED Labeled Symbol Name Representation Observation Encoding

class RESOLVED (Symbol : Type i) where
  labeled        : Type (i+1) → Type (i+1) → Option (Type i)
  name           : DIFFERENT Symbol → Type i
  representation : Type (i+1)
  observation    : DIFFERENT Symbol → OBSERVE representation → Bool
  encoding       : DIFFERENT Symbol → representation → Bool
  token          : Token labeled (DIFFERENT Symbol) name
                         representation observation encoding

inductive DistinctTokensOf
    (Labeled: Type (i+1) → Type (i+1) → Option (Type i))
    (Symbol: Type i)
    (Name: DIFFERENT Symbol → Type i)
    (Representation: Type (i+1))
    (Observation: DIFFERENT Symbol → OBSERVE Representation → Bool)
    (Encoding: DIFFERENT Symbol → Representation → Bool)
    [DISTINGUISHABLE Labeled Representation]
    [ADMISSIBLE Labeled (DIFFERENT Symbol) Representation Observation]
    [CORRELATED Labeled (DIFFERENT Symbol) Representation Observation]
    [ORDERED Labeled (DIFFERENT Symbol) Representation Observation Encoding]
  | nil : DistinctTokensOf Labeled Symbol Name Representation Observation Encoding
  | cons : (s: DIFFERENT Symbol) →
           (r: OBSERVE Representation) →
           (h1: Observation s r) →
           DistinctTokensOf Labeled Symbol Name Representation Observation Encoding →
           DistinctTokensOf Labeled Symbol Name Representation Observation Encoding


class NAMED
    (Labeled   : Type (i+1) → Type (i+1) → Option (Type i))
    (Symbol    : Type i)
    (Referent  : Type i)
    (Binding   : TOKEN Symbol → OBSERVE Referent → Bool)
    [t : TOKEN Symbol]
    where
  named? : TOKEN Symbol → OBSERVE Referent → Bool := Binding

namespace NAMED

variable {Labeled   : Type (i+1) → Type (i+1) → Option (Type i)}
         {Symbol    : Type i}
         {Referent  : Type i}
         {Binding   : TOKEN Symbol → OBSERVE Referent → Bool}
         [t : TOKEN Symbol]
         [model: NAMED Labeled Symbol Referent Binding]

def named
    (token: TOKEN Symbol)
    (referent: OBSERVE Referent)
      : Bool :=
  model.named? token referent
end NAMED

-- Given a TOKEN symbol NAMED n, we can get all the way to LEXED with just
-- two relations: Binding and Indexed!

inductive LEXED
    (Labeled        : Type (i+1) → Type (i+1) → Option (Type i))
    (Symbol         : Type i)
    (Referent       : Type i)
    (Representation : Type (i+1))
    (Binding        : TOKEN Symbol → Representation → Bool)
    (Letter         : TOKEN Symbol → OBSERVE Referent → Bool)
    (SortedByLetter : Referent → OBSERVE Representation → Bool)
    (Difference     : DIFFERENT Symbol → OBSERVE Representation → Bool)
    (Encoded        : DIFFERENT Symbol → Representation → Bool)
    (t              : TOKEN Symbol)
    [n  : NAMED Labeled Symbol Referent Letter]
    [DISTINGUISHABLE Labeled Representation]
    [ADMISSIBLE Labeled Referent Representation SortedByLetter]
    [ADMISSIBLE Labeled (DIFFERENT Symbol) Representation Difference]
  | nil : LEXED Labeled Symbol Referent Representation
                Binding Letter SortedByLetter
                Difference Encoded t
  | cons :
      (d        : DIFFERENT Symbol) →
      (tok      : TOKEN Symbol) →
      (ref      : Referent) →
      (r        : OBSERVE (Representation)) →
      (r_symbol : OBSERVE (TOKEN.representation Symbol)) →
      (h_enc    : tok.token.encoded.encoded? d r_symbol = true) →
      (h_seen   : SortedByLetter ref r = true) →
      (h_name   : n.named? tok (some (ULift.up ref)) = true) →
      LEXED Labeled Symbol Referent Representation
            Binding Letter SortedByLetter
            Difference Encoded
            t →
      LEXED Labeled Symbol Referent Representation
            Binding Letter SortedByLetter
            Difference Encoded
            t



class TIMED
    (ddt: Type i → Type i → Type i → Option (Type i))
    (dt: Type i → Type i → Option (Type i))
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
variable {ddt: Type i → Type i → Type i → Option (Type i)}
         {dt: Type i → Type i → Option (Type i)}
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
    (ddt: Type i → Type i → Type i → Option (Type i))
    (dt: Type i → Type i → Option (Type i))
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
    (Accumulate: Type i → Type i → Type i → Option (Type i))
    (Count: Type i → Type i → Option (Type i))
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
variable  {Accumulate: Type i → Type i → Type i → Option (Type i)}
          {Count: Type i → Type i → Option (Type i)}
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
    (Accumulate: Type i → Type i → Type i → Option (Type i))
    (Count: Type i → Type i → Option (Type i))
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

abbrev COMPUTED (Symbol: Type i) := Symbol × OBSERVE Symbol

class ADMITTED
    (Metaphysical: Type (i+1) → Type (i+1) → Option (Type i))
    (Computational: Type (i+1) → Type (i+1) → Option (Type i))
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
    [CORRELATED Metaphysical Symbol Value Iterated]
    [CORRELATED Metaphysical Symbol Decomposition Computed]
    [CORRELATED Computational Symbol Value Iterated]
    [CORRELATED Computational Symbol Decomposition Computed]
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





namespace REAL

variable {Metaphysical: Type (i+1) → Type (i+1) → Option (Type i)}
         {Computational: Type (i+1) → Type (i+1) → Option (Type i)}
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
         [CORRELATED Metaphysical Symbol Value Iterated]
         [CORRELATED Metaphysical Symbol Decomposition Computed]
         [CORRELATED Computational Symbol Value Iterated]
         [CORRELATED Computational Symbol Decomposition Computed]
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
