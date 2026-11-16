import Measurement.Episode12
open Lean Elab Term Meta Measurement «springer-verlag» THE_GOSPEL readers_experience
-- The device imported and never touched: one blank, then three empty loops of the strip's length.
elab "count_the_boot" : command => do
  Command.liftTermElabM do
    let mut out := ""
    let t0 ← IO.monoNanosNow
    let (_, hb) ← withHeartbeats (pure ())
    let t1 ← IO.monoNanosNow
    out := out ++ s!"BLANK 0 {hb} {t1 - t0}\n"
    let mut u1 := ()
    for i in [0:episode8_description.length] do
      let t0 ← IO.monoNanosNow
      let (u', hb) ← withHeartbeats (do let u' := u1; pure u')
      let t1 ← IO.monoNanosNow
      u1 := u'
      out := out ++ s!"TURN 1 EMPTY {i} {hb} {t1 - t0}\n"
    let mut u2 := ()
    for i in [0:episode8_description.length] do
      let t0 ← IO.monoNanosNow
      let (u', hb) ← withHeartbeats (do let u' := u2; pure u')
      let t1 ← IO.monoNanosNow
      u2 := u'
      out := out ++ s!"TURN 2 EMPTY {i} {hb} {t1 - t0}\n"
    let mut u3 := ()
    for i in [0:episode8_description.length] do
      let t0 ← IO.monoNanosNow
      let (u', hb) ← withHeartbeats (do let u' := u3; pure u')
      let t1 ← IO.monoNanosNow
      u3 := u'
      out := out ++ s!"TURN 3 EMPTY {i} {hb} {t1 - t0}\n"
    logInfo out
count_the_boot
