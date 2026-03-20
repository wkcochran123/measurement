/-
Measurement/Chapter1.lean

CODA:  Welcome the the TuringDevice that explicitly describes
the computations necessary for the simultaneous decomposition
and evaluation of a real valued function.

As promised, we beign at the beginning and rely on the state
transform mechanisms of Lean as an example of a discrete universal
Turing machine.  The following is an arbitrary encoding, so be
on the lookout for Godel. I would consider this some "arbitrary
encoding."


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
-- A different symbol is probably some other symbol, we will
-- prove that in a bit.
abbrev DIFFERENT (Invariant : Type i) := Option Invariant


-- At the end of the day, a type is a symbol that can be assigned a name and value.
-- This sounds liks counting, to me.  Let's exploit this structure.
abbrev SYMBOL := Type


-- A TOKEN Invariant is one that the compiler can recognize as being
-- distinct from all other symbols.
abbrev TOKEN (Invariant : Type) := DIFFERENT Invariant

-- We can talk about something being on and off. We call that token
abbrev BOOL (Invariant :Type) := TOKEN Invariant
-- BOOL.  See how we are making the process of making TOKENS?
-- Would you like to see the only primitive TOKEN?

-- Verified silence. This is the only thing we can know for sure,
-- nothing has been verified and so we can TOKENIZE that concept as
def _______________FALSE_______________ {Invariant: Type} : (TOKEN Invariant) := none
-- We define FALSE to be the symbol that represents unrepresentable symbols.
-- This is a DISTINCT Invariant, although it will never be observed as such.
-- I made it REALLY distinct so you do NOT miss it.
--
-- There is only one ball, keep your eye on it.
-- Like and Subscribe if you think I should make the ball bigger or smaller.



/- --------------------------------------------------------
DISTINGUISHABLE.

Something is DISTINGUISHABLE from others if there exists
some characteristic that is either present or absent from
the something relative to the others.
-/
class DISTINGUISHABLE
    (Characterisitic : Type → Option (Type))
    (Invariant: Type)
    [DecidableEq Invariant]
    where

  -- The universe only exists as a type.
  -- Any higher type is metaphysical and belongs to
  -- the compiling engine, not the proof.
  -- Or does it?
  æther               : Type

  different? : Invariant → Invariant → Prop :=
    fun s1 s2 => s1 ≠ s2
  distinguished? : Invariant → Prop :=
    fun s => ∃ c : Invariant, different? s c
  dec_distinguished : DecidablePred distinguished?

namespace DISTINGUISHABLE
variable {Characterisitic : Type → Option (Type)}
         {Invariant: Type}
         [DecidableEq Invariant]
         [d: DISTINGUISHABLE Characterisitic Invariant]

def different
    (s1 s2 : Invariant) : Prop :=
  d.different? s1 s2

def distinguished
    (s : Invariant) : Prop :=
  d.distinguished? s

def encode
    (symbol: Invariant)
    (compiler_type : Type)
      : Option (Type) :=
  if (d.dec_distinguished symbol).decide then some compiler_type else none

end DISTINGUISHABLE






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
    (Event : Type 1 → Option (Type 1))
    (Description: Type → Option (Type))
    (Invariant: Type)
    (NextInvariant: OBSERVE (DIFFERENT Type))

     -- Notice the metaphor is starting to work on abstract types.
     -- It is _metaphysical_.
    (Metaphor: DIFFERENT Invariant → OBSERVE (DIFFERENT Invariant)  → BOOL Bool)
    where

  -- Is this a possible future state of the universe? Dunno, could be.
  admissible? : DIFFERENT Invariant → OBSERVE (DIFFERENT Invariant) → BOOL Bool := Metaphor

  -- Michelson and Morley disallowed the æther as a possible thing that could be
  -- distinguished. The æther is the absence of any symbol, so it cannot be distinguished
  -- from itself.
  aether_inadmissible :
    ∀ obs : OBSERVE (DIFFERENT Invariant), admissible? none obs = none

namespace ADMISSIBLE
variable {Event       : Type 1 → Option (Type 1)}
         {Description : Type → Option (Type)}
         {Invariant      : Type}
         {NextInvariant  : OBSERVE (DIFFERENT Type)}
         {Metaphor    : DIFFERENT Invariant → OBSERVE (DIFFERENT Invariant) → BOOL Bool}
         [a : ADMISSIBLE Event Description Invariant NextInvariant Metaphor]

def admissible
    (s   : DIFFERENT Invariant)
    (obs : OBSERVE (DIFFERENT Invariant))
      : BOOL Bool :=
  a.admissible? s obs

end ADMISSIBLE

-- The arrow of time in the compiler is right here.
abbrev BEFORE (x : Type i) := x
abbrev AFTER (x : Type i) := ULift.{i+1, i} x


class COUNTABLE
    -- Physical Traits of counting
    (Invariant : Type)

    -- The metaphysical process of counting.
    -- Associate an i-th thing with a number
    (ζ      : Type i → Option Type)
    (Value  : Type i)
    (NextNumberInvariant : Type → DIFFERENT Type)
    (NextCount  : Type i →  DIFFERENT (Type i))
    (NextNumberValue : Type 1 → DIFFERENT (Type 1))
    (NextInvariant: OBSERVE (DIFFERENT Type))
    (Metaphor: DIFFERENT Invariant → OBSERVE (DIFFERENT Invariant)  → BOOL Bool)

    [value_equality : DecidableEq (Value)]
    [value_equality : DecidableEq (Invariant)]
    [value: DISTINGUISHABLE NextNumberInvariant Invariant]
    [next_value: ADMISSIBLE NextNumberValue NextNumberInvariant Invariant NextInvariant Metaphor]
    where

  ζ? : Type i → Option Type := ζ
  next_number_symbol? : Type → DIFFERENT Type := NextNumberInvariant
  next_count? : Type i → DIFFERENT (Type i) := NextCount
  next_number_value? : Type 1 → DIFFERENT (Type 1) := NextNumberValue
  next_symbol? : OBSERVE (DIFFERENT Type) := NextInvariant

  metaphor? : DIFFERENT Invariant → OBSERVE (DIFFERENT Invariant) → BOOL Bool := Metaphor

  zero: Invariant





namespace COUNTABLE

variable  {Invariant : Type}
          {ζ: Type i → Option Type}
          {Value  : Type i}
          {NextNumberInvariant : Type → DIFFERENT Type}
          {NextCount  : Type i →  DIFFERENT (Type i)}
          {NextNumberValue : Type 1 → DIFFERENT (Type 1)}
          {NextInvariant: OBSERVE (DIFFERENT Type)}
          {Metaphor: DIFFERENT Invariant → OBSERVE (DIFFERENT Invariant)  → BOOL Bool}
          [value_equality : DecidableEq (Value)]
          [symbol_equality : DecidableEq (Invariant)]
          [value_symbol: DISTINGUISHABLE NextNumberInvariant Invariant]
          [next_value_symbol: ADMISSIBLE NextNumberValue NextNumberInvariant Invariant NextInvariant Metaphor]
          [countable: COUNTABLE Invariant ζ Value NextNumberInvariant NextCount NextNumberValue NextInvariant Metaphor]

def next_number_symbol
    (s : Type)
      : DIFFERENT Type :=
  countable.next_number_symbol? s

def next_count
    (s : Type i)
      : DIFFERENT (Type i) :=
  countable.next_count? s

def countable.next_count
    (s : Type i)
      : DIFFERENT (Type i) :=
  countable.next_count? s

def next_number_value
    (s : Type 1)
      : DIFFERENT (Type 1) :=
  countable.next_number_value? s

def metaphor
    (s : DIFFERENT Invariant)
    (obs : OBSERVE (DIFFERENT Invariant))
      : BOOL Bool :=
  countable.metaphor? s obs

end COUNTABLE



inductive Count
    -- Physical Traits of counting
    (Invariant : Type)

    -- The metaphysical process of counting.
    (ζ     : Type i → Option Type)
    (Value  : Type i)
    (NextNumberInvariant : Type → DIFFERENT Type)
    (NextCount  : Type i →  DIFFERENT (Type i))
    (NextNumberValue : Type 1 → DIFFERENT (Type 1))
    (NextInvariant: OBSERVE (DIFFERENT Type))
    (Metaphor: DIFFERENT Invariant → OBSERVE (DIFFERENT Invariant)  → BOOL Bool)
  | nil : Count Invariant ζ Value NextNumberInvariant NextCount NextNumberValue NextInvariant Metaphor
  | cons: Invariant →
          Count Invariant ζ Value NextNumberInvariant NextCount NextNumberValue NextInvariant Metaphor →
          Count Invariant ζ Value NextNumberInvariant NextCount NextNumberValue NextInvariant Metaphor

namespace Count
variable  {Invariant : Type}
          {ζ: Type i → Option Type}
          {Value  : Type i}
          {NextNumberInvariant : Type → DIFFERENT Type}
          {NextCount  : Type i →  DIFFERENT (Type i)}
          {NextNumberValue : Type 1 → DIFFERENT (Type 1)}
          {NextInvariant: OBSERVE (DIFFERENT Type)}
          {Metaphor: DIFFERENT Invariant → OBSERVE (DIFFERENT Invariant)  → BOOL Bool}
          [value_equality : DecidableEq (Value)]
          [symbol_equality : DecidableEq (Invariant)]
          [value_symbol: DISTINGUISHABLE NextNumberInvariant Invariant]
          [next_value_symbol: ADMISSIBLE NextNumberValue NextNumberInvariant Invariant NextInvariant Metaphor]
          [countable: COUNTABLE Invariant ζ Value NextNumberInvariant NextCount NextNumberValue NextInvariant Metaphor]



def η
    (c : Count Invariant ζ Value NextNumberInvariant NextCount NextNumberValue NextInvariant Metaphor)
      : Invariant :=
  match c with
  | nil => countable.zero
  | cons s _ => s

end Count



inductive DecodeMap
    (Invariant           : Type)
    (NextNumberInvariant : Type → DIFFERENT Type)
  | nil  : DecodeMap Invariant NextNumberInvariant
  | cons : Invariant →
           DecodeMap Invariant NextNumberInvariant →
           DecodeMap Invariant NextNumberInvariant


namespace DecodeMap

variable {Invariant           : Type}
         {ζ                : Type i → Option Type}
         {Value            : Type i}
         {NextNumberInvariant : Type → DIFFERENT Type}
         {NextCount        : Type i → DIFFERENT (Type i)}
         {NextNumberValue  : Type 1 → DIFFERENT (Type 1)}
         {NextInvariant       : OBSERVE (DIFFERENT Type)}
         {Metaphor         : DIFFERENT Invariant → OBSERVE (DIFFERENT Invariant) → BOOL Bool}
         [DecidableEq Invariant]
         [DecidableEq Value]
         [d : DISTINGUISHABLE NextNumberInvariant Invariant]
         [a : ADMISSIBLE NextNumberValue NextNumberInvariant Invariant NextInvariant Metaphor]
         [c : COUNTABLE Invariant ζ Value NextNumberInvariant NextCount
                         NextNumberValue NextInvariant Metaphor]

def decode
    (ct : Count Invariant ζ Value NextNumberInvariant NextCount
                NextNumberValue NextInvariant Metaphor)
      : DecodeMap Invariant NextNumberInvariant :=
  match ct with
  | Count.nil        => nil
  | Count.cons s rest => cons s (decode rest)

end DecodeMap

class NUMERIC
    (Invariant           : Type)
    (NextNumberInvariant : Type → DIFFERENT Type)
    (NextCount        : Type → DIFFERENT Type)
    (NextNumberValue  : Type 1 → DIFFERENT (Type 1))
    (NextInvariant       : OBSERVE (DIFFERENT Type))
    (Metaphor         : DIFFERENT Invariant → OBSERVE (DIFFERENT Invariant) → BOOL Bool)
    [DecidableEq Invariant]
    [d : DISTINGUISHABLE NextNumberInvariant Invariant]
    [a : ADMISSIBLE NextNumberValue NextNumberInvariant Invariant NextInvariant Metaphor]
    [c : COUNTABLE Invariant
              (fun S => some (DecodeMap S NextNumberInvariant))
              Invariant
              NextNumberInvariant NextCount NextNumberValue NextInvariant Metaphor]
    where

  numeral: Invariant

-- We define the CARRIER symbol as the thing
-- that can identify the presence of a number.
abbrev CARRIER := Prop

structure Sensor
    (Name: Type)
    (Invariant : Type i)
    (CompilerCarrier : CARRIER)
    (CompilerRepresentation : Type 1)
    (Representation : Type × Type)
    (NextRepresentation : Type → OBSERVE (Type 1 × Type 1))
    (NextInvariant : Type →  Type)
      where
  binary_digits : Invariant
  source_representation :
  compiler_representation : CompilerRepresentation
  next_number_symbol : NextNumberInvariant Invariant




class ENCODABLE
    (Invariant : Type)
    (Representation : )
    (Decomposition: Type → OBSERVE (Type × Type))
    (: )
    (Encode : Type → Type → OBSERVE (Type×Type) → BOOL Bool)
    (Decode : (Type × Type) → OBSERVE Type → Type 1)
    [DISTINGUISHABLE Encoding Invariant]
    [ADMISSIBLE Encoding Invariant Encoding Encode]
    where

  encoded? : Invariant → OBSERVE Encoding → Bool := Encode



class DISTINCT
    (Event        : Type (i+1) → Type (i+1) → Prop)
    (Desciption   : Type i → Type i → Option (Type i))
    (BIT          : Type (max 1 i) → Type (max 1 i) → Option (Type (max 1 i)))
    (Invariant       : Type i)
    (Stimulus     : Type (max 1 i))
    (Response     : Type (i+1))
    (Observation  : Before → OBSERVE Response → Bool)
    [d : DISTINGUISHABLE Description Invariant]
    [a : ADMISSIBLE Event Invariant ]
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


-- We can assert a TRUTH as being some Invariant that survives the act of observation.
abbrev TRUE  (Invariant : Type i) := TOKEN Invariant  -- TRUE, a certified presence
abbrev RELATION (Invariant : Type i) := TRUE (TOKEN Invariant)  -- RELATION, a certified connection between symbols
abbrev PROPERTY (Invariant : Type i) := TRUE (RELATION Invariant)  -- PROPERTY, a certified characteristic of a symbol
abbrev FEATURE (Invariant : Type i) := TRUE (PROPERTY Invariant)  -- VALUE, a certified measurement of a symbol's property
abbrev NATURAL_NUMBER (Invariant : Type i) := Option Invariant  -- A symbol that can be counted, like a tick mark on a ruler.

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
    (Invariant: Type i)
    (Encoding: Type (i+1))
    (Encode: Invariant → OBSERVE Encoding → Bool)
    [DISTINGUISHABLE Ordering Encoding]
    [ADMISSIBLE Ordering Invariant Encoding Encode]
    where

  encoded? : Invariant → OBSERVE Encoding → Bool := Encode

namespace CORRELATED
variable {Ordering: Type (i+1) → Type (i+1) → Option (Type i)}
         {Invariant: Type i}
         {Encoding: Type (i+1)}
         {Encode: Invariant → OBSERVE Encoding → Bool}
         [DISTINGUISHABLE Ordering Encoding]
         [ADMISSIBLE Ordering Invariant Encoding Encode]
         [parsed_symbol: CORRELATED Ordering Invariant Encoding Encode]

def encoded
    (input: Invariant)
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
    (Invariant: Type i)
    (Encoding: Invariant → Invariant → Bool)
    (InternalInvariant: Invariant → DIFFERENT Invariant)
    (StateChange: DIFFERENT Invariant → DIFFERENT Invariant → Bool)
    (Parsed: Invariant → OBSERVE Invariant → Bool)
    (Instruction: OBSERVE Invariant -> OBSERVE Invariant -> Bool)
    (Compiled: OBSERVE Invariant → OBSERVE (OBSERVE Invariant) → Bool)
    (NextInstruction: OBSERVE Invariant → DIFFERENT (OBSERVE Invariant))
    (InterpretInstruction: OBSERVE Invariant → DIFFERENT (OBSERVE Invariant))
    (Execution: DIFFERENT (OBSERVE Invariant) → DIFFERENT (OBSERVE Invariant) → Bool)
    (Executed: DIFFERENT (OBSERVE Invariant) → OBSERVE (DIFFERENT (OBSERVE Invariant)) → Bool)
-/

class ENCODED
    (Labeled: Type (i+1) → Type (i+1) → Option (Type i))
    (Invariant: Type i)
    (Name: Invariant → Type i)
    (Representation: Type (i+1))
    (EncodedInvariant: Invariant → OBSERVE Representation → Bool)
    (Encoding: Invariant → Representation → Bool)
    [DISTINGUISHABLE Labeled Representation]
    [ADMISSIBLE Labeled Invariant Representation EncodedInvariant]
    [CORRELATED Labeled Invariant Representation EncodedInvariant]
    [ORDERED Labeled Invariant Representation EncodedInvariant Encoding]
      where
  encoded? : Invariant → OBSERVE Representation → Bool := EncodedInvariant
  name? : Invariant → Type i := Name
  encoding? : Invariant → Representation → Bool := Encoding

namespace ENCODED
variable {Labeled: Type (i+1) → Type (i+1) → Option (Type i)}
         {Invariant: Type i}
         {Name: Invariant → Type i}
         {Representation: Type (i+1)}
         {EncodedInvariant: Invariant → OBSERVE Representation → Bool}
         {Encoding: Invariant → Representation → Bool}
         [DISTINGUISHABLE Labeled Representation]
         [ADMISSIBLE Labeled Invariant Representation EncodedInvariant]
         [CORRELATED Labeled Invariant Representation EncodedInvariant]
         [ORDERED Labeled Invariant Representation EncodedInvariant Encoding]
         [index: ENCODED Labeled Invariant Name Representation EncodedInvariant Encoding]

def encoded
    (s: Invariant)
    (r: OBSERVE Representation)
      : Bool :=
  index.encoded? s r

def name
    (s: Invariant)
      : Type i :=
  index.name? s

def encoding
    (s: Invariant)
    (r: Representation)
      : Bool :=
  index.encoding? s r

end ENCODED

inductive RepresentationOf
    (Labeled: Type (i+1) → Type (i+1) → Option (Type i))
    (Invariant: Type i)
    (Name: Invariant → Type i)
    (Representation: Type (i+1))
    (EncodedInvariant: Invariant → OBSERVE Representation → Bool)
    (Encoding: Invariant → Representation → Bool)
    [DISTINGUISHABLE Labeled Representation]
    [ADMISSIBLE Labeled Invariant Representation EncodedInvariant]
    [CORRELATED Labeled Invariant Representation EncodedInvariant]
    [ORDERED Labeled Invariant Representation EncodedInvariant Encoding]
    [index: ENCODED Labeled Invariant Name Representation EncodedInvariant Encoding]

  | nil : RepresentationOf Labeled Invariant Name Representation EncodedInvariant Encoding
  | cons : (s: Invariant) →
           (r: OBSERVE Representation) →
           (h1: index.encoded? s r) →
           RepresentationOf Labeled Invariant Name Representation EncodedInvariant Encoding →
           RepresentationOf Labeled Invariant Name Representation EncodedInvariant Encoding


structure Token
    (Labeled        : Type (i+1) → Type (i+1) → Option (Type i))
    (Invariant         : Type i)
    (Name           : Invariant → Type i)
    (Representation : Type (i+1))
    (Observation    : Invariant → OBSERVE Representation → Bool)
    (Encoding       : Invariant → Representation → Bool)
    where
  distinguishable : DISTINGUISHABLE Labeled Representation
  admissible      : ADMISSIBLE Labeled Invariant Representation Observation
  correlated      : CORRELATED Labeled Invariant Representation Observation
  ordered         : ORDERED Labeled Invariant Representation Observation Encoding
  encoded         : ENCODED Labeled Invariant Name Representation Observation Encoding

class RESOLVED (Invariant : Type i) where
  labeled        : Type (i+1) → Type (i+1) → Option (Type i)
  name           : DIFFERENT Invariant → Type i
  representation : Type (i+1)
  observation    : DIFFERENT Invariant → OBSERVE representation → Bool
  encoding       : DIFFERENT Invariant → representation → Bool
  token          : Token labeled (DIFFERENT Invariant) name
                         representation observation encoding

inductive DistinctTokensOf
    (Labeled: Type (i+1) → Type (i+1) → Option (Type i))
    (Invariant: Type i)
    (Name: DIFFERENT Invariant → Type i)
    (Representation: Type (i+1))
    (Observation: DIFFERENT Invariant → OBSERVE Representation → Bool)
    (Encoding: DIFFERENT Invariant → Representation → Bool)
    [DISTINGUISHABLE Labeled Representation]
    [ADMISSIBLE Labeled (DIFFERENT Invariant) Representation Observation]
    [CORRELATED Labeled (DIFFERENT Invariant) Representation Observation]
    [ORDERED Labeled (DIFFERENT Invariant) Representation Observation Encoding]
  | nil : DistinctTokensOf Labeled Invariant Name Representation Observation Encoding
  | cons : (s: DIFFERENT Invariant) →
           (r: OBSERVE Representation) →
           (h1: Observation s r) →
           DistinctTokensOf Labeled Invariant Name Representation Observation Encoding →
           DistinctTokensOf Labeled Invariant Name Representation Observation Encoding


class NAMED
    (Labeled   : Type (i+1) → Type (i+1) → Option (Type i))
    (Invariant    : Type i)
    (Referent  : Type i)
    (Binding   : TOKEN Invariant → OBSERVE Referent → Bool)
    [t : TOKEN Invariant]
    where
  named? : TOKEN Invariant → OBSERVE Referent → Bool := Binding

namespace NAMED

variable {Labeled   : Type (i+1) → Type (i+1) → Option (Type i)}
         {Invariant    : Type i}
         {Referent  : Type i}
         {Binding   : TOKEN Invariant → OBSERVE Referent → Bool}
         [t : TOKEN Invariant]
         [model: NAMED Labeled Invariant Referent Binding]

def named
    (token: TOKEN Invariant)
    (referent: OBSERVE Referent)
      : Bool :=
  model.named? token referent
end NAMED

-- Given a TOKEN symbol NAMED n, we can get all the way to LEXED with just
-- two relations: Binding and Indexed!

inductive LEXED
    (Labeled        : Type (i+1) → Type (i+1) → Option (Type i))
    (Invariant         : Type i)
    (Referent       : Type i)
    (Representation : Type (i+1))
    (Binding        : TOKEN Invariant → Representation → Bool)
    (Letter         : TOKEN Invariant → OBSERVE Referent → Bool)
    (SortedByLetter : Referent → OBSERVE Representation → Bool)
    (Difference     : DIFFERENT Invariant → OBSERVE Representation → Bool)
    (Encoded        : DIFFERENT Invariant → Representation → Bool)
    (t              : TOKEN Invariant)
    [n  : NAMED Labeled Invariant Referent Letter]
    [DISTINGUISHABLE Labeled Representation]
    [ADMISSIBLE Labeled Referent Representation SortedByLetter]
    [ADMISSIBLE Labeled (DIFFERENT Invariant) Representation Difference]
  | nil : LEXED Labeled Invariant Referent Representation
                Binding Letter SortedByLetter
                Difference Encoded t
  | cons :
      (d        : DIFFERENT Invariant) →
      (tok      : TOKEN Invariant) →
      (ref      : Referent) →
      (r        : OBSERVE (Representation)) →
      (r_symbol : OBSERVE (TOKEN.representation Invariant)) →
      (h_enc    : tok.token.encoded.encoded? d r_symbol = true) →
      (h_seen   : SortedByLetter ref r = true) →
      (h_name   : n.named? tok (some (ULift.up ref)) = true) →
      LEXED Labeled Invariant Referent Representation
            Binding Letter SortedByLetter
            Difference Encoded
            t →
      LEXED Labeled Invariant Referent Representation
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
abbrev PAIR (Invariant: Type i) := Invariant × Invariant
abbrev ORDERED_PAIR (Invariant_1: Type i) (Invariant_2: Type (i+1)) := Invariant_1 × Invariant_2
abbrev COUNTING (Invariant: Type i) := ORDERED_PAIR Invariant (OBSERVE Invariant)
abbrev NUMBER (Invariant: Type i) := ORDERED_PAIR Invariant (COUNTING Invariant)
abbrev BOUNDS (Invariant: Type i) := ORDERED_PAIR (NUMBER Invariant) (NUMBER (OBSERVE Invariant))
abbrev SEQUENCE (Invariant: Type i) := ORDERED_PAIR (NUMBER Invariant) (BOUNDS Invariant)

abbrev COMPUTED (Invariant: Type i) := Invariant × OBSERVE Invariant

class ADMITTED
    (Metaphysical: Type (i+1) → Type (i+1) → Option (Type i))
    (Computational: Type (i+1) → Type (i+1) → Option (Type i))
    (Invariant: Type i)
    (Decomposition: Type (i+1))
    (Value: Type (i+1))
    (Iterated : Invariant → OBSERVE Value → Bool) -- Decomposition is the midpoint of the bounds. -- These can be overlapped!
    (Computed: Invariant → OBSERVE Decomposition → Bool) -- The value is the limit of the decomposition.

    -- This needs refactoring as i am starting to bog again.
    (Converged: Invariant → Value → Bool) -- Is the decomposition the bisection of the bounds?
    (LE: Invariant → Invariant → Bool) -- Less than is not possible, on LE. need to make a poset.
    [DISTINGUISHABLE Metaphysical Value]
    [DISTINGUISHABLE Metaphysical Decomposition]
    [DISTINGUISHABLE Computational Value]
    [DISTINGUISHABLE Computational Decomposition]
    [ADMISSIBLE Metaphysical Invariant Value Iterated]
    [ADMISSIBLE Metaphysical Invariant Decomposition Computed]
    [ADMISSIBLE Computational Invariant Value Iterated]
    [ADMISSIBLE Computational Invariant Decomposition Computed]
    [CORRELATED Metaphysical Invariant Value Iterated]
    [CORRELATED Metaphysical Invariant Decomposition Computed]
    [CORRELATED Computational Invariant Value Iterated]
    [CORRELATED Computational Invariant Decomposition Computed]
    [ORDERED Metaphysical Invariant Value Iterated Converged]
    [ORDERED Metaphysical Invariant Decomposition Computed fun d i => Computed d (some { down := i })]
    [ORDERED Computational Invariant Value Iterated Converged]
    [ORDERED Computational Invariant Decomposition Computed fun d i => Computed d (some { down := i })]
    [ORDERED Metaphysical Invariant Decomposition Computed fun d i => Computed d (some { down := i })]
    [ORDERED Computational Invariant Value Iterated Converged]
    [ORDERED Computational Invariant Value Iterated fun d o => Iterated d (some { down := o })]
    [COMPUTABLE Metaphysical Computational Invariant Decomposition Value Computed Iterated]
      where

  le? : Invariant → Invariant → Bool := LE





namespace REAL

variable {Metaphysical: Type (i+1) → Type (i+1) → Option (Type i)}
         {Computational: Type (i+1) → Type (i+1) → Option (Type i)}
         {Invariant: Type i}
         {Decomposition: Type (i+1)}
         {Value: Type (i+1)}
         {Iterated : Invariant → OBSERVE Value → Bool}
         {Computed: Invariant → OBSERVE Decomposition → Bool}
         {Converged: Invariant → Value → Bool}
         {LE: Invariant → Invariant → Bool}
         [DISTINGUISHABLE Metaphysical Value]
         [DISTINGUISHABLE Metaphysical Decomposition]
         [DISTINGUISHABLE Computational Value]
         [DISTINGUISHABLE Computational Decomposition]
         [ADMISSIBLE Metaphysical Invariant Value Iterated]
         [ADMISSIBLE Metaphysical Invariant Decomposition Computed]
         [ADMISSIBLE Computational Invariant Value Iterated]
         [ADMISSIBLE Computational Invariant Decomposition Computed]
         [CORRELATED Metaphysical Invariant Value Iterated]
         [CORRELATED Metaphysical Invariant Decomposition Computed]
         [CORRELATED Computational Invariant Value Iterated]
         [CORRELATED Computational Invariant Decomposition Computed]
         [ORDERED Metaphysical Invariant Value Iterated Converged]
         [ORDERED Metaphysical Invariant Decomposition Computed fun d i => Computed d (some { down := i })]
         [ORDERED Computational Invariant Value Iterated Converged]
         [ORDERED Computational Invariant Decomposition Computed fun d i => Computed d (some { down := i })]
         [ORDERED Metaphysical Invariant Decomposition Computed fun d i => Computed d (some { down := i })]
         [ORDERED Computational Invariant Value Iterated Converged]
         [ORDERED Computational Invariant Value Iterated fun d o => Iterated d (some { down := o })]
         [COMPUTABLE Metaphysical Computational Invariant Decomposition Value Computed Iterated]
         [ψ : REAL Metaphysical Computational Invariant Decomposition Value Iterated Computed Converged LE]

def le
    (s1: Invariant)
    (s2: Invariant)
      : Bool :=
  ψ.le? s1 s2

def eq
    (s1: Invariant)
    (s2: Invariant)
      : Bool :=
  ψ.eq? s1 s2

end REAL


end Measurement
