
import Measurement.Episode9

-- Homework:

namespace Measurement

def program : CarrierProcess FiniteGaugeTheoryOfMeasurement := sorry

-- Problem 1: Implement de Morgan's law of the excluded middle.
instance : DISTINGUISHABLE FiniteGaugeTheoryOfMeasurement program := sorry

-- My answer:
def program : CarrierProcess FiniteGaugeTheoryOfMeasurement where
--                  +---------------------------    Weierstrauss Approximation Theorem
--                  |
--                  V
  symbol := { truth := False, decTruth := Decidable.isFalse (fun h => h) }
  value  := .one Fact.Truth (.zero Fact.Truth)


-- I believe this demonstrates Euler-Lagrange.  I mean, it had to demonstrate
-- a solution to Euler-Lagrange to compile.
end Measurement
