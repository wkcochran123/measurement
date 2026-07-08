import Measurement.Meanwhile22
import Measurement.Formalization.Cost

/-! PROBE (task vol1-alpha, Phase 0): can the gauge (Formalization.Cost) and the
phase face (Meanwhile22) coexist in ONE file without the Episode39/Meanwhile22
QPhase clash? If this target-builds, the pulse can tie directly to the phase
face and the bootstrap to `derivation_inferred.cost`, in one currency. DELETE or
fold into the real spike afterward. No number computed. -/

namespace Measurement.AlphaProbe
open Measurement Measurement.Formalization

-- the gauge (structural derivation cost) and the bootstrap, from Formalization:
#check @Derivation.cost
#check (derivation_inferred.cost)   -- the whole-machine bootstrap length

-- the phase face, from the Meanwhile branch:
#check @Measurement.phaseRead
#check Measurement.QPhase

end Measurement.AlphaProbe
