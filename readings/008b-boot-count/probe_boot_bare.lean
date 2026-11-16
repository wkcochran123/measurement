import Lean
open Lean Elab Term Meta
-- Nothing imported but Lean: one blank, then three empty loops of 106 turns.
elab "count_the_boot" : command => do
  Command.liftTermElabM do
    let mut out := ""
    let t0 ← IO.monoNanosNow
    let (_, hb) ← withHeartbeats (pure ())
    let t1 ← IO.monoNanosNow
    out := out ++ s!"BLANK 0 {hb} {t1 - t0}\n"
    let mut u1 := ()
    for i in [0:106] do
      let t0 ← IO.monoNanosNow
      let (u', hb) ← withHeartbeats (do let u' := u1; pure u')
      let t1 ← IO.monoNanosNow
      u1 := u'
      out := out ++ s!"TURN 1 EMPTY {i} {hb} {t1 - t0}\n"
    let mut u2 := ()
    for i in [0:106] do
      let t0 ← IO.monoNanosNow
      let (u', hb) ← withHeartbeats (do let u' := u2; pure u')
      let t1 ← IO.monoNanosNow
      u2 := u'
      out := out ++ s!"TURN 2 EMPTY {i} {hb} {t1 - t0}\n"
    let mut u3 := ()
    for i in [0:106] do
      let t0 ← IO.monoNanosNow
      let (u', hb) ← withHeartbeats (do let u' := u3; pure u')
      let t1 ← IO.monoNanosNow
      u3 := u'
      out := out ++ s!"TURN 3 EMPTY {i} {hb} {t1 - t0}\n"
    logInfo out
count_the_boot
