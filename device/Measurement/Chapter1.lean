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
Definition: Distinguishable (adjective)

One thing is distinguished from another if they are not the same.
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
Zero is not introduced here as a metaphysical absence, but as a
distinguishable symbol within a type.  It marks the unique element
that carries no prior distinction.  Its role is structural: it is the
baseline against which all other symbols are separated.
-/
abbrev ZERO (σ : Type now) [d: Distinguishable σ] := Distinguishable.symbol (σ := σ)

/-
Once distinguished, a symbol stays distinguished through all time.
-/
instance {σ : Type now} [d : Distinguishable σ] : Distinguishable (ULift.{now+1, now} σ) where
  inst := let _ := d.inst; inferInstance
  symbol := ULift.up d.symbol


/-
Combinations of distinguishable things are distinguishable by construction.
-/
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

/-
Zero is recognized under lifting exactly as it is below:
the distinguished natural number 0, transported without alteration.
The lift changes universe, not meaning.
-/
instance : Distinguishable (ULift.{0, 0} Nat) where
  inst := inferInstance
  symbol := ULift.up 0



/--
Definition:  Natural Number (noun)

-/
inductive Naturals : Type now
| zero : Naturals
| succ : Naturals → Naturals
deriving DecidableEq


namespace Naturals
  abbrev ZERO := Naturals.zero
  abbrev ONE := Naturals.succ Naturals.zero
  abbrev TWO := Naturals.succ ONE
  abbrev THREE := Naturals.succ TWO
  abbrev MAX_COUNT := Naturals.succ THREE

def VALUE : Naturals → Nat
| zero => 0
| succ n => Nat.succ (VALUE n)
def COUNT (n : Naturals) : Naturals := Naturals.succ n
def LE (a b : Naturals) : Bool :=
  decide (VALUE a ≤ VALUE b)
def LT (a b : Naturals) : Bool :=
  decide (VALUE a < VALUE b)
def le (a b : Naturals) : Prop :=
  VALUE a ≤ VALUE b

instance : DecidableRel Naturals.le := by
  intro a b
  dsimp [Naturals.le]
  infer_instance
end Naturals

inductive Counting (σ : Type now) [Distinguishable σ] : Nat → Type (now + 1)
| zero : Counting σ 0
| succ : {j : Nat} → (prev : Counting σ j) → Counting σ (j + 1)
deriving DecidableEq

namespace Counting

/-- The canonical “bottomed” chain of length j (built recursively). -/
def mk {σ : Type now} [Distinguishable σ] : (j : Nat) → Counting σ j
| 0     => Counting.zero
| j+1   => Counting.succ (mk j)

def ZERO {σ : Type now} [Distinguishable σ] : Counting σ 0 := Counting.zero
def ZERO_TO_ONE  {σ : Type now} [Distinguishable σ] : Counting σ 1 := Counting.succ Counting.ZERO
def ONE_TO_TWO  {σ : Type now} [Distinguishable σ] : Counting σ 2 := Counting.succ Counting.ZERO_TO_ONE
def TWO_TO_THREE  {σ : Type now} [Distinguishable σ] : Counting σ 3 := Counting.succ Counting.ONE_TO_TWO
def MAX  {σ : Type now} [Distinguishable σ] : Counting σ 4 := Counting.succ Counting.TWO_TO_THREE

def count_to {σ : Type now} [Distinguishable σ] : (j : Nat) → Counting σ j
| 0   => zero
| j+1 => succ (count_to j)

end Counting


/--
Definition 1: ArrowOfTime

As of now, there is a before and an after.
-/
structure ArrowOfTime
  (j : Nat)
  (α : Type now) [Distinguishable α]
  (β : Type now)
  : Type (now + 1) where
  inner  : Counting α j
  outer  : Counting α (j + 1)
  before : α
  after  : ULift.{now+1, now} β


/-
Things can exhibit the arrow of time
-/
class HasArrow
    (E : Nat → (α : Type now) → [Distinguishable α] → (β : Type now) → Type (now+1))
    where
  arrow
    {j : Nat}
    {α : Type now} [Distinguishable α]
    {β : Type now} :
    E j α β → ArrowOfTime j α β

namespace Counting
  def ELAPSE
    {σ : Type now} [Distinguishable σ]
    {j : Nat} (c : Counting σ j) : Counting σ (j + 1) :=
  Counting.succ (j := j) c
end Counting

namespace MAX_VALUE
def slip
    {j : Nat}
    {σ τ : Type now} [Distinguishable σ] [Distinguishable τ]
    (A : ArrowOfTime j σ τ)
    : ULift.{now+1, now} τ :=
  -- No testing. No threshold.
  -- The evaluation is the act of reaching the 'after' state.
  A.after

def count_to (j : Nat) (σ : Type now) [Distinguishable σ] : Naturals :=
  -- The count is the act of reaching the 'after' state.
  -- We can only count to the maximum number of things that have happened.
  -- This is a fundamental limit on counting, and thus on measurement itself.
  match j with
  | 0 => Naturals.zero
  | Nat.succ j' => Naturals.succ (count_to j' σ)

end MAX_VALUE

/--
A list of things that should happen in order is a truth.
Truths are represented by adjectives.
-/
inductive Enumeration
    (σ : Type now) [Distinguishable σ]
    : Type now
  | nil : Enumeration σ
  | cons : σ → Enumeration σ → Enumeration σ
  deriving DecidableEq


/-
The list of things that happened in a particular order.
Facts are represented by nouns.  We can only represent
a fact by the truth on the page.
-/
structure Numbering
    (σ : Type now) [Distinguishable σ]
    : Type now
    where
  symbol : Enumeration σ
  numbering : Enumeration Nat
  deriving DecidableEq

instance {σ : Type now} [d : Distinguishable σ] : Distinguishable (Numbering σ) where
  inst := inferInstance -- Uses the deriving DecidableEq you just added
  symbol := {
    symbol := Enumeration.nil,       -- The empty adjectival sequence
    numbering := Enumeration.nil     -- The empty implementation sequence
  }

instance {σ : Type now} [d : Distinguishable σ] : Distinguishable (Enumeration σ) where
  inst := inferInstance -- Uses the deriving DecidableEq you just added
  symbol := Enumeration.nil

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
  data : Enumeration (Numbering σ)
  alphabet : Numbering (Enumeration τ)
  arrow: ArrowOfTime now σ τ


/-
Coda: Friction
-/

/-- A minimal container for a numeric reading. -/
structure Value where
  value : Nat

/-- Any type `σ` that can be read as a natural number. -/
class HasValue (σ : Type u) where
  value : σ → Nat

namespace HasValue

/-- Convenience: read a `Nat` from any `σ` with a `HasValue` instance. -/
def read {σ : Type u} [HasValue σ] (x : σ) : Nat :=
  HasValue.value x

end HasValue

/-- The container is readable by projection. -/
instance : HasValue Value where
  value v := v.value

namespace Enumeration

variable {σ : Type now} [Distinguishable σ]

/-- Length (count) of an enumeration. -/
def length : Enumeration σ → Nat
  | .nil          => 0
  | .cons _ tail  => Nat.succ (length tail)

end Enumeration

instance {σ : Type now} [Distinguishable σ] : HasValue (Enumeration σ) where
  value xs := Enumeration.length xs

class Noise (σ : Type u) where
  apply : (σ → Nat) → (σ → Naturals)

namespace Noise
def reading {σ : Type u}
  [HasValue σ]
  (N : Noise σ)
  : σ → Naturals :=
  N.apply HasValue.value
end Noise

namespace ArrowOfTime

variable {i : Type Nat}
variable {σ : Type now} [Distinguishable σ]
variable {τ : Type now}

def elapse
  {σ : Type now} [Distinguishable σ]
  {τ : Type now}
  {j : Nat}
  (A : ArrowOfTime j σ τ) : ArrowOfTime (j+1) σ τ :=
{ inner  := A.outer
, outer  := by
    -- A.outer : Counting σ (j+1)
    -- need: Counting σ ((j+1)+1)
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      Counting.ELAPSE (j := j + 1) A.outer
, before := A.before
, after  := A.after
}

def relive {X : Type now} : Option X :=
  none

end ArrowOfTime


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

namespace Noisy
variable {σ : Type now} [Distinguishable σ]
variable {τ : Type now} [Distinguishable τ] -- Temporal noise can distinguish among some,
                                            -- if not all events in the universe.
                                            -- It says nothing about non-distinguishable events.
end Noisy

class Admissible
    (σ : Type now) [Distinguishable σ]
    where
  history : Naturals → Enumeration σ
  η : Naturals → σ → Option Naturals
  ζ : Naturals → Naturals → Option σ


class Manifest (i: Nat) (σ : Type now) [Distinguishable σ] [Admissible σ] where
  witness : Counting σ i
  symbol : Distinguishable Nat
  deriving DecidableEq


namespace Counting

inductive LessThan {σ : Type now} [Distinguishable σ] :
  {i j : Nat} → Counting σ i → Counting σ j → Prop
| step : {i : Nat} → {c : Counting σ i} → LessThan c (Counting.succ c)
| trans : {i j k : Nat} → {a : Counting σ i} → {b : Counting σ j} → {c : Counting σ k} →
          LessThan a b → LessThan b c → LessThan a c

instance {σ : Type now} [Distinguishable σ] {i _j : Nat} :
  LT (Counting σ i) where
  lt := LessThan

def ArrowOfTime
    {i : Nat}
    {σ : Type now} [Distinguishable σ] [Admissible σ]
    (prior : Manifest i σ)
    : Option (Manifest (i + 1) σ) :=
  let next_witness := Counting.count_to (i + 1)
  let lifted_prior := Counting.succ prior.witness

  if next_witness = lifted_prior then
    some {
      witness := next_witness,
      symbol := prior.symbol
    }
  else
    none

def step_now {i : Nat} {σ : Type now} [Distinguishable σ] (current : Counting σ i) : Counting σ (i + 1) :=
  Counting.succ current

end Counting


instance (i : Nat) (σ : Type now) [Distinguishable σ] [Admissible σ] :
  Distinguishable (Manifest i σ) where
  inst := inferInstance -- Uses the deriving DecidableEq
  symbol := {
    witness := Counting.mk i,
    symbol := { inst := inferInstance, symbol := 0 }
  }

namespace Manifest

def resolve
    {i : Nat}
    {σ : Type i} [Distinguishable σ] [Admissible σ]
    (x : σ)
    {τ : Type i} [Distinguishable τ] [Admissible τ]
    (y : τ)
    : Option (Manifest i τ) :=
  some {
    witness := Counting.mk i,
    symbol := inferInstance
  }

end Manifest


structure Domain
    (σ : Type now)[Distinguishable σ]
    (τ : Type now)[Distinguishable τ]
    where
  low: Admissible σ
  high: Admissible τ

class Inverted
    (σ : Type now)[Distinguishable σ]
    (τ : Type now)[Distinguishable τ]
    where
  map: (σ → Option τ) → (τ → Option σ)

structure Iteration
    (σ : Type now)[Distinguishable σ][Admissible σ]
    (τ : Type now)[Distinguishable τ][Admissible τ]
    where
  step: Manifest (i:=now) σ
  value: Domain σ τ

abbrev Rationals (σ : Type now)[Distinguishable σ][Admissible σ] := Iteration σ σ

instance (σ : Type now) [Distinguishable σ] [Admissible σ] :
  Distinguishable (Rationals σ) where
  inst :=
    -- Two Rationals are equal if their Manifest steps are identical
    -- AND their Domains (low/high) are identical.
    -- This relies on the DecidableEq of 'Counting σ MAX'.
    inferInstance
  symbol :=
    -- The ZERO Rational: A Manifest step of ZERO toward the ZERO Domain.
    { step := Manifest.zero, value := Domain.zero }

class PartialOrder
    (σ : Type now)[Distinguishable σ][Admissible σ]
    where
  preimage: Rationals σ
  image: Iteration (Inverted σ Rationals σ) σ

end Measurement
