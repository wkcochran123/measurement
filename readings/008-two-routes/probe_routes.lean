import Measurement.Episode12
open Lean Elab Term Meta Measurement «springer-verlag» THE_GOSPEL readers_experience
-- Two routes to one number, each step on the meter, the halving first.
-- Prints "BLANK hb ns", then "HALVING i hb ns" and "CRANK i hb ns" for every cell of the strip, then "MEET bracket point".
elab "time_the_two_routes" : command => do
  Command.liftTermElabM do
    let mut out := ""
    let t0 ← IO.monoNanosNow
    let (_, blank) ← withHeartbeats (pure ())
    let t1 ← IO.monoNanosNow
    out := out ++ s!"BLANK {blank} {t1 - t0}\n"
    let mut b := (theLowWall, theHighWall)
    for i in [0:episode8_description.length] do
      let t0 ← IO.monoNanosNow
      let (b', hb) ← withHeartbeats (do let b' := halve b; pure b')
      let t1 ← IO.monoNanosNow
      b := b'
      out := out ++ s!"HALVING {i} {hb} {t1 - t0}\n"
    let mut p := the_held_house
    for i in [0:episode8_description.length] do
      let t0 ← IO.monoNanosNow
      let (p', hb) ← withHeartbeats (do let p' := the_truth_inferred_by_the_device p; pure p')
      let t1 ← IO.monoNanosNow
      p := p'
      out := out ++ s!"CRANK {i} {hb} {t1 - t0}\n"
    out := out ++ s!"MEET {decide (b = theBracket)} {decide (p = theNewtonPoint)}\n"
    logInfo out
time_the_two_routes
