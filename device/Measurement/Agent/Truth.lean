/-
Measurement.Agent.Truth

The canonical Prop instantiation of the cascade, built directly without a
typeclass ladder. Mirrors Episode16's `truthCarrier` / `truthInferred` /
`theory_true?` final behavior.
-/
import Measurement.Agent.Processes

set_option autoImplicit false

namespace Measurement.Agent

noncomputable def truthCarrier : Carrier Prop :=
  { symbol := Fact.true, value := 0 }

noncomputable def truthGates : Gates Prop truthCarrier :=
  Gates.default truthCarrier

noncomputable def truthAgent : Agent Prop :=
  { carrier := truthCarrier, gates := truthGates }

noncomputable def truthOutput : TrueOutput truthAgent :=
  { atreyu := {} }

noncomputable def truthInferred : INFERRED truthAgent :=
  let out := truthOutput
  let same := sameFact truthAgent out
  let base := baseClosure truthAgent out
  { equivalence := { atreyu := out.atreyu, closure := base }
    theory :=
      .inferred same truthAgent.carrier.symbol (Signal.zero Fact.true) out.output
        (out.obfusplained? (Signal.zero Fact.true) out.output) base }

/-- Final cascade readout, analogous to Episode16 `theory_true?`. -/
def theory_true? : Prop :=
  truthInferred.inferred? truthInferred.equivalence.closure truthInferred.theory

end Measurement.Agent
