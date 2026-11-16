import Measurement.Episode12
open Lean Elab Term Meta Measurement «springer-verlag» THE_GOSPEL readers_experience
-- As 008 (one blank, the halving, the crank), then an empty loop, then the halving again. No blank between loops.
elab "count_the_boot" : command => do
  Command.liftTermElabM do
    let mut out := ""
    let t0 ← IO.monoNanosNow
    let (_, hb) ← withHeartbeats (pure ())
    let t1 ← IO.monoNanosNow
    out := out ++ s!"BLANK 0 {hb} {t1 - t0}\n"
    let mut b1 := (theLowWall, theHighWall)
    for i in [0:episode8_description.length] do
      let t0 ← IO.monoNanosNow
      let (b', hb) ← withHeartbeats (do let b' := halve b1; pure b')
      let t1 ← IO.monoNanosNow
      b1 := b'
      out := out ++ s!"TURN 1 HALVING {i} {hb} {t1 - t0}\n"
    let mut p2 := the_held_house
    for i in [0:episode8_description.length] do
      let t0 ← IO.monoNanosNow
      let (p', hb) ← withHeartbeats (do let p' := the_truth_inferred_by_the_device p2; pure p')
      let t1 ← IO.monoNanosNow
      p2 := p'
      out := out ++ s!"TURN 2 CRANK {i} {hb} {t1 - t0}\n"
    let mut u3 := ()
    for i in [0:episode8_description.length] do
      let t0 ← IO.monoNanosNow
      let (u', hb) ← withHeartbeats (do let u' := u3; pure u')
      let t1 ← IO.monoNanosNow
      u3 := u'
      out := out ++ s!"TURN 3 EMPTY {i} {hb} {t1 - t0}\n"
    let mut b4 := (theLowWall, theHighWall)
    for i in [0:episode8_description.length] do
      let t0 ← IO.monoNanosNow
      let (b', hb) ← withHeartbeats (do let b' := halve b4; pure b')
      let t1 ← IO.monoNanosNow
      b4 := b'
      out := out ++ s!"TURN 4 HALVING {i} {hb} {t1 - t0}\n"
    logInfo out
count_the_boot
