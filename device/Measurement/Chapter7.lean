import Measurement.Chapter6

namespace Measurement

structure Counting (σ : Type u)(τ : Type (u+1)) where
  ticks: Enumeration (Event σ)
  events: ArrowOfTime (Event σ) (Event τ)

structure Accumulator (σ : Type u)(τ : Type (u+1)) where
  counting: Counting σ τ
  total: Nat

structure Integration (σ : Type u)(τ : Type (u+1)) where
  accumulator: Enumeration (Accumulator σ τ)
  integral: Enumeration (Event σ) → Nat

structure Statistic (σ : Type u)(τ : Type (u+1)) where
  integration: Enumeration (Integration σ τ)
  statistic: Enumeration (Integration σ τ) → Nat


namespace Counting

/-- Add a tick-event to the counting tape. -/
def push {σ : Type u} {τ : Type (u+1)}
  (C : Counting σ τ) (e : Event σ) : Counting σ τ :=
  { C with ticks := Enumeration.snoc C.ticks e }

end Counting


namespace Accumulator

/-- Push an event: update the counting tape and increment the total. -/
def push {σ : Type u} {τ : Type (u+1)}
  (A : Accumulator σ τ) (e : Event σ) : Accumulator σ τ :=
  { counting := A.counting.push e
    total    := A.total.succ }

/-- The value of an Accumulator is the current total of the ledger. -/
def value {σ : Type u} {τ : Type (u+1)} (A : Accumulator σ τ) : Nat :=
  A.total

end Accumulator


namespace Integration

def push {σ : Type u} {τ : Type (u+1)}
  (I : Integration σ τ) (A : Accumulator σ τ) : Integration σ τ :=
  { I with accumulator := Enumeration.snoc I.accumulator A }


def value {σ : Type u} {τ : Type (u+1)} (I : Integration σ τ) : Nat :=
  match I.accumulator.last with
  | none   => 0
  | some A => I.integral A.counting.ticks

end Integration


namespace Statistic

def push {σ : Type u} {τ : Type (u+1)}
  (S : Statistic σ τ) (I : Integration σ τ) : Statistic σ τ :=
  { S with integration := Enumeration.snoc S.integration I }


def value {σ : Type u} {τ : Type (u+1)} (S : Statistic σ τ) : Nat :=
  match S.integration.last with
  | none   => 0
  | some I => I.value

end Statistic


end Measurement
