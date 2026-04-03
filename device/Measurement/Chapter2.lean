/-
Measurement/Chapter2.lean
-/

import Measurement.Chapter1

namespace Measurement

-- Our measuring device can display a subset of the rational numbers!
class MEASURED
    (Observation: Fact)
    (Numerator: Type 1)
    (Denominator: Type 1)
    (η: Natural)
    (ζ: Number)
    (φ: Rational)

inductive Measurement where
  | on: Rational → Measurement
  | next: Fact → Rational → Measurement → Measurement

structure Sensor
    (Observation: Fact)
    (Numerator: Type 1)
    (Denominator: Type 1)
    (η: Natural)
    (ζ: Number)
    (φ: Rational)
    [MEASURED Observation Numerator Denominator η ζ φ]
    where
  present: Fact
  numerator: Type Numerator
  denominator: Type Denominator
  index: Natural
  value: Number
  encoding: Rational

  sense? : Measurement → Measurement := fun m =>
    match m with
    | Measurement.on r => Measurement.on r
    | Measurement.next obs r next_m => match obs.truth with
      | x => Measurement.next obs r (sense? next_m)
      | _ => Measurement.on r
end Measurement
