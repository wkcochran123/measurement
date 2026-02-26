/-
Measurement/Chapter1.lean
Facts
-/

import Std
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Basic



namespace Measurement

/-
There is only one universe, the one we have now.
-/
universe now

/-
Definition 1: Distinguishable
-/
class Distinguishable
    (σ : Type now)
    where
  inst : DecidableEq σ
  symbol : σ
  deriving DecidableEq -- We can tell if two things are equal or not.
                       -- We need no stronger understading of stuff,
                       -- just the ability to tell them apart.

instance (σ : Type now) [d : Distinguishable σ] : DecidableEq σ :=
  d.inst

/-
Once distinguished, it stays distinguished through all time.
-/

instance {σ : Type now} [d : Distinguishable σ] : Distinguishable (ULift.{now+1, now} σ) where
  inst := let _ := d.inst; inferInstance
  symbol := ULift.up d.symbol


instance {σ τ : Type now} [Distinguishable σ] [Distinguishable τ] :
    Distinguishable (σ × τ) where
  inst := by
    -- DecidableEq for Prod comes from DecidableEq σ and DecidableEq τ
    infer_instance
  symbol := (Distinguishable.symbol (σ := σ), Distinguishable.symbol (σ := τ))

/-
The natural numbers are distinguishable by construction
-/
instance : Distinguishable Nat where
  inst := inferInstance  -- By construction.
  symbol := 0


/--
Definition 1: ArrowOfTime

As of now, there is a before and an after.
-/
structure ArrowOfTime
    (σ : Type now) [Distinguishable σ]
    (τ : Type now)
    : Type (now + 1) -- Technically, we don't know there is an after until it happens, see TemporalFriction.
    where
  before: σ
  after: ULift.{now+1, now} τ -- The after is in the next universe, of which we can only speculate.

/-
Things can exhibit the arrow of time
-/
class HasArrow
  (E : (α : Type now) → [Distinguishable α] → (β : Type now) → Type (now+1)) where
  arrow
    {α : Type now} [Distinguishable α]
    {β : Type now} :
    E α β → ArrowOfTime α β

/--
Definition 2: Enumeration

The most simple mathematical act is to count.  Counting
requires understanding everything that has come before.
You cannot count to 5 without first counting to 4.
-/
inductive Enumeration
    (σ : Type now) [Distinguishable σ]
    : Type now
  | nil : Enumeration σ
  | cons : σ → Enumeration σ → Enumeration σ

/--
Definition 3: Numbering

It is possible to count distinguishable things.
-/
structure Numbering
    (σ : Type now) [Distinguishable σ]
    : Type now
    where
  symbol : Enumeration σ
  numbering : Enumeration Nat


/--
Definition 4: Ledger

The ledger is a list of that is constructed in time, one object
after another.  The amount of time that has passed is the number
of items in the data.
-/
structure Ledger
    (σ : Type now) [Distinguishable σ]
    (τ : Type now) [Distinguishable τ]
    : Type (now+1) -- The universe at time t+1 knows about the
                   -- universe up to time t, and no further.
    where
  data : Numbering σ
  alphabet : Numbering τ
  arrow: ArrowOfTime σ τ


/-
Coda: Friction
-/

inductive Naturals : Type now
| zero : Naturals
| succ : Naturals → Naturals
deriving DecidableEq

/--
Note that, this is also true of the native data type
naturals.  However, it is not.  It is the type of the
compiler.  This is a rounded set of numbers that we
agree exist up to a point, the maximum number representable
by the compiler.  The compiler is a sensor, see definition...
-/
instance : Distinguishable Naturals where
  inst   := inferInstance     -- uses the `deriving DecidableEq`
  symbol := Naturals.zero

structure AxiomOfMeasurement (σ: Nat) : Type (now+2) where
  Lookup : Ledger Naturals (ULift Naturals)

class Rounded
    (Value : (α : Type now) → [Distinguishable α] → (β : Type now) -> [Distinguishable β] → Type (now+1))
    (σ : Type now) [Distinguishable σ]
    (τ : Type now) [Distinguishable τ]
    : Type (now+2) where

    reading : Value σ τ
    partition: Numbering (σ × τ) -- The partition of the alphabet into distinguishable events.

 structure Noisy
    (Friction : (α : Type now) → [Distinguishable α] → (β : Type now) → Type (now+1)) [HasArrow Friction]
    (σ : Type now) [Distinguishable σ]
    (τ : Type now) [Distinguishable τ]
    : Type (now+2)
    where
  events    : Friction σ τ
  friction  : Ledger σ Naturals
  floor : Rounded Value σ τ
  mistake   : AxiomOfMeasurement σ

/-**************************************************************
Code:

This software uses discrete definitions of _many_ common concepts
from mathematics all built from the idea of counting.
-/

namespace ArrowOfTime

variable {σ : Type now} [Distinguishable σ]
variable {τ : Type now}

/--
To elapse is to go forward in time.
-/
def elapse (A : ArrowOfTime σ τ) : Option (ULift τ) :=
  some A.after

/--
During silence, nothing.
-/
def silence (_A : ArrowOfTime σ τ) : Option (ULift τ) :=
  none

/--
One cannot relive the past.
-/
def relive {X : Type now} : Option X :=
  none

end ArrowOfTime

instance {σ : Type now} {τ : Type now}
  [Distinguishable σ] [Distinguishable τ] :
  DecidableEq (ArrowOfTime σ τ) :=
by
  intro a b
  cases a with
  | mk abefore aafter =>
    cases b with
    | mk bbefore bafter =>
      -- reduce to DecidableEq on σ and on ULift τ
      if h1 : abefore = bbefore then
        if h2 : aafter = bafter then
          exact isTrue (by cases h1; cases h2; rfl)
        else
          exact isFalse (by intro h; cases h; exact h2 rfl)
      else
        exact isFalse (by intro h; cases h; exact h1 rfl)

instance {σ : Type now} {τ : Type now}
  [Distinguishable σ] [Distinguishable τ] :
  Distinguishable (ArrowOfTime σ τ) where
  inst := inferInstance
  symbol :=
    { before := Distinguishable.symbol
    , after  := ULift.up (Distinguishable.symbol)
    }


namespace Distinguishable
def distinguish
  (F : (σ : Type now) → [Distinguishable σ] → Type now)
  (mkInst : (σ : Type now) → [Distinguishable σ] → DecidableEq (F σ))
  (mkSym  : (σ : Type now) → [Distinguishable σ] → F σ)
  : (σ : Type now) → [Distinguishable σ] → Distinguishable (F σ)
| σ, _ =>
  { inst   := mkInst σ
    symbol := mkSym  σ
  }
end Distinguishable

namespace Enumeration

variable {σ : Type now} [Distinguishable σ]
variable {τ : Type now} [Distinguishable τ]

/-- Append enumerations (needed to flatten a 2D shape). -/
def append : Enumeration σ → Enumeration σ → Enumeration σ
  | .nil, ys => ys
  | .cons a as, ys => .cons a (append as ys)

def map (f : σ → τ) : Enumeration σ → Enumeration τ
  | .nil => .nil
  | .cons a as => .cons (f a) (map f as)

-- Counting!
def naturals : Enumeration σ → Nat → Enumeration Nat
| .nil, _ => .nil
| .cons _ as, start => .cons start (naturals as (start + 1))

def numbering (e : Enumeration σ) : Numbering σ :=
  { symbol := e
  , numbering := Enumeration.naturals e 0
  }

def first : Enumeration σ → Option σ
  | .nil => none
  | .cons a _ => some a

end Enumeration

namespace Numbering

variable {σ : Type Now} [Distinguishable σ]

def ζ (dm : Numbering σ) (n : Nat) : Option σ :=
  let rec find : Enumeration σ → Enumeration Nat → Option σ
    | .cons x _, .cons idx _ => if idx = n then some x else none -- Hard fail if not immediate
    | _, _ => none
  find dm.symbol dm.numbering

def η (dm : Numbering σ) (x : σ) : Option Nat :=
  let rec find : Enumeration σ → Enumeration Nat → Option Nat
    | .cons y _, .cons idx _ => if y = x then some idx else none
    | _, _ => none
  find dm.symbol dm.numbering

end Numbering

namespace Ledger
def getArrow
  {σ : Type now} {τ : Type now} [Distinguishable σ] [Distinguishable τ]
  (L : Ledger σ τ) : ArrowOfTime σ τ :=
by
  -- this is the field projection, no recursion
  exact L.arrow
end Ledger

namespace Noisy
variable {σ : Type now} [Distinguishable σ]
variable {τ : Type now} [Distinguishable τ] -- Temporal noise can distinguish among some,
                                            -- if not all events in the universe.
                                            -- It says nothing about non-distinguishable events.

namespace Naturals
def count : Naturals → Nat
| Naturals.zero     => 0
| Naturals.succ n   => Nat.succ (Naturals.count n)

def find : Nat → Naturals
| 0     => Naturals.zero
| n+1   => Naturals.succ (find n)
end Naturals


def slip?
    (Friction : (α : Type now) → [Distinguishable α] → (β : Type now) → Type (now+1)) [HasArrow Friction]
    (F : Friction σ τ)
    (N : Noisy Friction σ τ)
    : Option (ULift (τ))
    :=
  let slip_event := HasArrow.arrow F
  let recv_carrier_number := slip_event.before
  let current_ledger_ndx := match N.friction.data.η recv_carrier_number with
    | none => 0
    | some n => n
  let next_ledger_ndx := current_ledger_ndx + 1  -- Thank you, Peano.
  let next_symbol := slip_event.after
  let next_symbol_Natural := Naturals.find next_ledger_ndx
  let next_symbol_nat := A.toNat.η next_symbol_Natural


  let current_force_sensor := N.friction.data.η
  let current_force_tally := match current_force_sensor with
    | none => 0
    | some n => n
  let new_force_tally := current_force_tally + 1  -- Thank you, Peano.
  let threshold := N.threshold.reading V
  let threshold := match F.threshold.reading slip_event.before with
    | none => 0
    | some t => t
  if new_force_tally > threshold then
    A.elapse
  else
    A.silence

end Noisy

end Measurement
