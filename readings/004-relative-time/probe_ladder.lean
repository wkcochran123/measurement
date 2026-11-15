import Measurement.Episode12
open Lean Elab Term Meta Measurement «springer-verlag» THE_GOSPEL
-- One reading per universe level k = 1..36: the typeset ladder searched for rung k on a place one universe lower,
-- read on Episode 8's meter with wall time: "LEVEL k raw blank ns".
elab "time_the_ladder" : command => do
  Command.liftTermElabM do
    let mut out := ""
    for k in [1:37] do
      let mut ty ← `(Number)
      for _ in [1:k] do
        ty ← `(ULift $ty)
      let stx ← `((inferInstance : TYPESET.{0,0,0} (CarrierProcess FACT) the_representation.the_card_between $(Lean.quote k) $ty))
      let t0 ← IO.monoNanosNow
      let (h, b) ← the_ekg_reads stx
      let t1 ← IO.monoNanosNow
      out := out ++ s!"LEVEL {k} {h} {b} {t1 - t0}\n"
    logInfo out
time_the_ladder

