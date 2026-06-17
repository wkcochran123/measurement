/-
Measurement.Agent.Processes

The episode process vocabulary as plain structures over ONE explicit `Agent`
argument. No class, no instance-implicit tower, no `@[reducible]` on semantic
machinery. SCIENTIFIC / TRUTH / TrueOutput / EquivalenceProcess / INFERRED /
ArmWaveProcess are all ordinary structures.
-/
import Measurement.Agent.Gates

set_option autoImplicit false

universe u

namespace Measurement.Agent

/-- The single bundled context. One carrier plus the whole gate bundle. -/
structure Agent (Value : Type u) where
  carrier : Carrier Value
  gates : Gates Value carrier

/-- Episode7 `ArmWaveProcess`: overhead/proxy machinery. NOT reducible here
(it is semantic machinery, not a definitional abbreviation). -/
structure ArmWaveProcess {Value : Type u} (agent : Agent Value) where
  guess : Signal := Signal.zero agent.gates.distinguishable.fact
  overhead : Nat := agent.gates.bullshit.cost

/-- Episode9 `LearningProcess`. -/
structure LearningProcess {Value : Type u} (agent : Agent Value) where
  invariant : Prop := agent.carrier.symbol.truth
  touch? : Prop → Prop := id

/-- Episode9 `SCIENTIFIC`: a normal structure, not a class, not reducible. -/
structure SCIENTIFIC {Value : Type u} (agent : Agent Value) where
  learning : LearningProcess agent
  invariant : Prop := agent.carrier.symbol.truth
  predictable? : Prop → Prop → Prop := fun _ b => b

/-- Episode9 `TRUTH`. Normal structure. -/
structure TRUTH {Value : Type u} (agent : Agent Value) where
  scientific : SCIENTIFIC agent
  martyred? : Prop → Prop → Prop := fun a b => a ↔ b

/-- Episode15 `AtreyuProcess`. The `satirize` default references the prior
`stress` field. -/
structure AtreyuProcess {Value : Type u} (agent : Agent Value) where
  next : Signal := Signal.zero agent.carrier.symbol
  stress : Nat := agent.carrier.value
  satirize : Signal → Signal := fun s => { s with weight := s.weight + stress + 1 }

/-- Episode15 `TrueOutput`. `output` default references the prior `atreyu`
field. -/
structure TrueOutput {Value : Type u} (agent : Agent Value) where
  atreyu : AtreyuProcess agent
  output : Signal := atreyu.satirize atreyu.next
  obfusplained? : Signal → Signal → Prop := fun a b => a < b

/-- Named, cached `Fact.SAME` analog. Not inlined twice downstream. -/
def sameFact {Value : Type u} (agent : Agent Value) (out : TrueOutput agent) : Fact :=
  { truth := Subsingleton (out.obfusplained? (Signal.zero Fact.true) out.output) }

/-- Named, cached base closure. Not inlined twice downstream. -/
def baseClosure {Value : Type u} (agent : Agent Value) (out : TrueOutput agent) : Closure :=
  .different (sameFact agent out) (Signal.zero Fact.true) out.output
    (out.obfusplained? (Signal.zero Fact.true) out.output)

/-- Episode15 `EquivalenceProcess`. `closure` has no default (supplied by the
constructor); `close?` default references the `agent` parameter. -/
structure EquivalenceProcess {Value : Type u} (agent : Agent Value) where
  atreyu : AtreyuProcess agent
  closure : Closure
  close? : Signal → Signal → Closure := fun a b =>
    .different agent.carrier.symbol a b (a < b)

/-- Episode15 `INFERRED`: the pathological late class, here a normal structure
with one explicit `agent` parameter and one nested `EquivalenceProcess`
field. -/
structure INFERRED {Value : Type u} (agent : Agent Value) where
  equivalence : EquivalenceProcess agent
  theory : Closure
  inferred? : Closure → Closure → Prop := Closure.le

end Measurement.Agent
