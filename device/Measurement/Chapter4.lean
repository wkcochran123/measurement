import Measurement.Chapter3

namespace Measurement


class ADMISSIBLE
    (symbol: Type now)
    (event: Type (now+1))
    [DISTINGUISHABLE symbol event]
    (number : symbol)
    (value : symbol -> symbol -> Bool)
    [COUNTABLE symbol event number value]
    (domain : symbol -> symbol -> Bool)
    (transform : symbol -> Option (ULift.{now+1, now} symbol))
    [LOCAL symbol event number value domain transform]
    (mapping : symbol)
    (first_variation : symbol → symbol → Bool)
      where

  admits? : symbol -> event -> Bool

  invariant : symbol
  ψ : symbol


inductive Sample
    (symbol: Type now)
    (event: Type (now+1))
    [DISTINGUISHABLE symbol event]
    (number : symbol)
    (value : symbol -> symbol -> Bool)
    [COUNTABLE symbol event number value]
    (domain : symbol -> symbol -> Bool)
    (transform : symbol -> Option (ULift.{now+1, now} symbol))
    [locality : LOCAL symbol event number value domain transform]
    (mapping : symbol)
    (first_variation : symbol → symbol → Bool)
    [ADMISSIBLE symbol event number value domain transform mapping first_variation]

    (threshold: COUNTABLE symbol event number value)
  /-- The empty ledger (The Void) -/
  | nil : Sample symbol event number value domain transform mapping first_variation threshold

  | next :
           Count symbol event →
           (s : symbol) →
           (e : event) →
           (event×symbol) →
           count →
           Accumulate count symbol event number value →
           count_value →
           (ADMISSIBLE.admits? mapping (count → threshold → (count.witness >= threshold.witness)) →
            Sample symbol event number value domain transform mapping first_variation threshold)



end Measurement
