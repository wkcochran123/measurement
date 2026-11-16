import Measurement.Episode12
open Lean Elab Term Meta Measurement «springer-verlag» THE_GOSPEL readers_experience
-- Five blanks in a row, then the halving, a blank, the crank, a blank, an empty loop.
elab "count_the_boot" : command => do
  Command.liftTermElabM do
    let mut out := ""
    let t0 ← IO.monoNanosNow
    let (_, hb) ← withHeartbeats (pure ())
    let t1 ← IO.monoNanosNow
    out := out ++ s!"BLANK 0 {hb} {t1 - t0}\n"
    let t0 ← IO.monoNanosNow
    let (_, hb) ← withHeartbeats (pure ())
    let t1 ← IO.monoNanosNow
    out := out ++ s!"BLANK 1 {hb} {t1 - t0}\n"
    let t0 ← IO.monoNanosNow
    let (_, hb) ← withHeartbeats (pure ())
    let t1 ← IO.monoNanosNow
    out := out ++ s!"BLANK 2 {hb} {t1 - t0}\n"
    let t0 ← IO.monoNanosNow
    let (_, hb) ← withHeartbeats (pure ())
    let t1 ← IO.monoNanosNow
    out := out ++ s!"BLANK 3 {hb} {t1 - t0}\n"
    let t0 ← IO.monoNanosNow
    let (_, hb) ← withHeartbeats (pure ())
    let t1 ← IO.monoNanosNow
    out := out ++ s!"BLANK 4 {hb} {t1 - t0}\n"
    let mut b1 := (theLowWall, theHighWall)
    for i in [0:episode8_description.length] do
      let t0 ← IO.monoNanosNow
      let (b', hb) ← withHeartbeats (do let b' := halve b1; pure b')
      let t1 ← IO.monoNanosNow
      b1 := b'
      out := out ++ s!"TURN 1 HALVING {i} {hb} {t1 - t0}\n"
    let t0 ← IO.monoNanosNow
    let (_, hb) ← withHeartbeats (pure ())
    let t1 ← IO.monoNanosNow
    out := out ++ s!"BLANK 5 {hb} {t1 - t0}\n"
    let mut p2 := the_held_house
    for i in [0:episode8_description.length] do
      let t0 ← IO.monoNanosNow
      let (p', hb) ← withHeartbeats (do let p' := the_truth_inferred_by_the_device p2; pure p')
      let t1 ← IO.monoNanosNow
      p2 := p'
      out := out ++ s!"TURN 2 CRANK {i} {hb} {t1 - t0}\n"
    let t0 ← IO.monoNanosNow
    let (_, hb) ← withHeartbeats (pure ())
    let t1 ← IO.monoNanosNow
    out := out ++ s!"BLANK 6 {hb} {t1 - t0}\n"
    let mut u3 := ()
    for i in [0:episode8_description.length] do
      let t0 ← IO.monoNanosNow
      let (u', hb) ← withHeartbeats (do let u' := u3; pure u')
      let t1 ← IO.monoNanosNow
      u3 := u'
      out := out ++ s!"TURN 3 EMPTY {i} {hb} {t1 - t0}\n"
    logInfo out
count_the_boot
