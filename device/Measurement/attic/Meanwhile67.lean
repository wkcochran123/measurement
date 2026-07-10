import Measurement.Meanwhile66

/- MEANWHILE 67 -- ONE-SIDED TRANSACTION TAX. The two-sided view was
`#|alpha|#`: one mass-noise gravity quantum on each side of the abstraction.

If the reader's true/false orientation is not part of the invariant, the tax is
one-sided. There are two displays, but one cost:

  #|alpha   alpha|#

The apparatus reports both orientations and the shared one-quantum tax.
-/

namespace Measurement

def oneSidedTransactionTaxScaledAt18 : Nat :=
  qftGravityQuantumScaledAt18

def oneSidedTaxLowerAlphaScaledAt18 : Nat :=
  qftAlphaScaledAt18 - oneSidedTransactionTaxScaledAt18

def oneSidedTaxUpperAlphaScaledAt18 : Nat :=
  qftAlphaScaledAt18 + oneSidedTransactionTaxScaledAt18

def oneSidedTaxLowerInverseScaledAt18? : Option Nat :=
  alphaInverseReadScaledAt18? oneSidedTaxLowerAlphaScaledAt18

def oneSidedTaxUpperInverseScaledAt18? : Option Nat :=
  alphaInverseReadScaledAt18? oneSidedTaxUpperAlphaScaledAt18

def oneSidedTaxOfAlphaBpsScaledAt18? : Option Nat :=
  (ratioScaledAt18? oneSidedTransactionTaxScaledAt18 qftAlphaScaledAt18).map
    scaledFractionToBasisPointsScaledAt18

def oneSidedLowerBar : String :=
  staticGlyph .mass ++ "|alpha"

def oneSidedUpperBar : String :=
  "alpha|" ++ staticGlyph .mass

structure OneSidedTransactionTaxReport where
  name : String
  interpretation : String
  readerTruthOrientationIgnored : Bool
  lowerBar : String
  upperBar : String
  qftAlphaScaledAt18 : Nat
  oneSidedTaxScaledAt18 : Nat
  lowerAlphaScaledAt18 : Nat
  upperAlphaScaledAt18 : Nat
  lowerInverseAlphaScaledAt18? : Option Nat
  upperInverseAlphaScaledAt18? : Option Nat
  oneSidedTaxQuanta : Nat
  totalTwoSidedTaxQuanta : Nat
  oneSidedTaxOfAlphaBpsScaledAt18? : Option Nat
  lowerTaxMatchesGravityQuantum : Bool
  upperTaxMatchesGravityQuantum : Bool
  deliveredByNeutrino : Bool
deriving Repr

def oneSidedTransactionTaxReport : OneSidedTransactionTaxReport :=
  { name := "one-sided-transaction-tax"
    interpretation :=
      "ignore reader true/false orientation and account for one mass-noise gravity quantum"
    readerTruthOrientationIgnored := true
    lowerBar := oneSidedLowerBar
    upperBar := oneSidedUpperBar
    qftAlphaScaledAt18 := qftAlphaScaledAt18
    oneSidedTaxScaledAt18 := oneSidedTransactionTaxScaledAt18
    lowerAlphaScaledAt18 := oneSidedTaxLowerAlphaScaledAt18
    upperAlphaScaledAt18 := oneSidedTaxUpperAlphaScaledAt18
    lowerInverseAlphaScaledAt18? := oneSidedTaxLowerInverseScaledAt18?
    upperInverseAlphaScaledAt18? := oneSidedTaxUpperInverseScaledAt18?
    oneSidedTaxQuanta :=
      taxQuotient oneSidedTransactionTaxScaledAt18 qftGravityQuantumScaledAt18
    totalTwoSidedTaxQuanta := qftTotalTransactionTaxQuanta
    oneSidedTaxOfAlphaBpsScaledAt18? := oneSidedTaxOfAlphaBpsScaledAt18?
    lowerTaxMatchesGravityQuantum := qftLowerTaxIsOneGravityQuantum
    upperTaxMatchesGravityQuantum := qftUpperTaxIsOneGravityQuantum
    deliveredByNeutrino :=
      neutrinoGravityDeliveryReport.deliveredByNeutrino }

#eval oneSidedTransactionTaxReport

end Measurement
