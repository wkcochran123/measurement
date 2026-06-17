/-
Measurement.Agent.Core

Standalone, compile-time-friendly primitives for the Agent reimplementation.
No imports from Measurement.Episode* or Measurement.Formalization*.
Closure ordering is rank-based on purpose: the episode `Closure.le` /
`Bullshit.le` / `Knowledge.le` recursive relations are the elaboration tar
pit this subtree is built to avoid.
-/
set_option autoImplicit false

universe u

namespace Measurement.Agent

/-- A truth payload. Mirrors the episode `Fact` carrier without its ornament. -/
structure Fact where
  truth : Prop

namespace Fact

/-- The canonical true fact. -/
def true : Fact := { truth := True }

end Fact

/-- A measurement carrier indexed by its value type. `Value` is a phantom
parameter kept for conceptual parity with the episodes. -/
structure Carrier (Value : Type u) where
  symbol : Fact
  value : Nat
  event : Nat → Nat := id

/-- A weighted signal. Weight is the rank-style cost used by `Closure`. -/
structure Signal where
  fact : Fact
  weight : Nat

namespace Signal

def zero (f : Fact) : Signal := { fact := f, weight := 0 }

def step (f : Fact) (n : Nat) : Signal := { fact := f, weight := n + 1 }

def le (a b : Signal) : Prop := a.weight ≤ b.weight

def lt (a b : Signal) : Prop := a.weight < b.weight

end Signal

instance : LE Signal where
  le := Signal.le

instance : LT Signal where
  lt := Signal.lt

/-- The closure carrier. `inferred` nests a prior closure; everything else is
flat. Compare by `rank`, never by a recursive structural relation. -/
inductive Closure where
  | same : Fact → Signal → Closure
  | different : Fact → Signal → Signal → Prop → Closure
  | inferred : Fact → Fact → Signal → Signal → Prop → Closure → Closure

namespace Closure

/-- Shallow rank. `inferred` adds 2 over its prior; `same`/`different` are
constant. This is structural recursion on the nested prior closure only. -/
def rank : Closure → Nat
  | .same _ _ => 0
  | .different _ _ _ _ => 1
  | .inferred _ _ _ _ _ prior => prior.rank + 2

/-- Rank-based order. Replaces the episode recursive `le`. -/
def le (a b : Closure) : Prop := rank a ≤ rank b

end Closure

end Measurement.Agent
