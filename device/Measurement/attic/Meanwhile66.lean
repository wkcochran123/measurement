import Measurement.Meanwhile65

/- MEANWHILE 66 -- SEE THE TRANSACTION TAX. The static field is texture; the
transaction tax is the boundary layer around the QFT alpha read. This file
prints that boundary layer in gravity quanta.

The visual convention is:

  # = one mass-noise gravity quantum

So `#|alpha|#` means one quantum is paid to enter the abstraction and one quantum
is paid to leave it.
-/

namespace Measurement

def repeatString (text : String) : Nat -> String
  | 0 => ""
  | n + 1 => text ++ repeatString text n

def taxQuotient (value quantum : Nat) : Nat :=
  if quantum = 0 then 0 else value / quantum

def taxRemainder (value quantum : Nat) : Nat :=
  if quantum = 0 then value else value % quantum

def qftLowerTransactionTaxScaledAt18 : Nat :=
  qftAlphaScaledAt18 - qftAlphaNoiseLowerScaledAt18

def qftUpperTransactionTaxScaledAt18 : Nat :=
  qftAlphaNoiseUpperScaledAt18 - qftAlphaScaledAt18

def qftLowerTransactionTaxQuanta : Nat :=
  taxQuotient qftLowerTransactionTaxScaledAt18 qftGravityQuantumScaledAt18

def qftUpperTransactionTaxQuanta : Nat :=
  taxQuotient qftUpperTransactionTaxScaledAt18 qftGravityQuantumScaledAt18

def qftTotalTransactionTaxQuanta : Nat :=
  taxQuotient qftTransactionTaxScaledAt18 qftGravityQuantumScaledAt18

def qftTransactionTaxRemainderScaledAt18 : Nat :=
  taxRemainder qftTransactionTaxScaledAt18 qftGravityQuantumScaledAt18

def qftTransactionTaxOfAlphaBpsScaledAt18? : Option Nat :=
  (ratioScaledAt18? qftTransactionTaxScaledAt18 qftAlphaScaledAt18).map
    scaledFractionToBasisPointsScaledAt18

def qftTransactionTaxBar : String :=
  repeatString (staticGlyph .mass) qftLowerTransactionTaxQuanta ++
    "|alpha|" ++
    repeatString (staticGlyph .mass) qftUpperTransactionTaxQuanta

structure TransactionTaxReport where
  name : String
  interpretation : String
  massGlyph : String
  bar : String
  qftAlphaScaledAt18 : Nat
  lowerBoundaryScaledAt18 : Nat
  upperBoundaryScaledAt18 : Nat
  lowerTaxScaledAt18 : Nat
  upperTaxScaledAt18 : Nat
  totalTransactionTaxScaledAt18 : Nat
  gravityQuantumScaledAt18 : Nat
  lowerTaxQuanta : Nat
  upperTaxQuanta : Nat
  totalTaxQuanta : Nat
  taxRemainderScaledAt18 : Nat
  exactQuantumTax : Bool
  transactionTaxOfAlphaBpsScaledAt18? : Option Nat
  deliveredByNeutrino : Bool
deriving Repr

def transactionTaxReport : TransactionTaxReport :=
  { name := "transaction-tax"
    interpretation :=
      "the visible alpha boundary layer, counted in mass-noise gravity quanta"
    massGlyph := staticGlyph .mass
    bar := qftTransactionTaxBar
    qftAlphaScaledAt18 := qftAlphaScaledAt18
    lowerBoundaryScaledAt18 := qftAlphaNoiseLowerScaledAt18
    upperBoundaryScaledAt18 := qftAlphaNoiseUpperScaledAt18
    lowerTaxScaledAt18 := qftLowerTransactionTaxScaledAt18
    upperTaxScaledAt18 := qftUpperTransactionTaxScaledAt18
    totalTransactionTaxScaledAt18 := qftTransactionTaxScaledAt18
    gravityQuantumScaledAt18 := qftGravityQuantumScaledAt18
    lowerTaxQuanta := qftLowerTransactionTaxQuanta
    upperTaxQuanta := qftUpperTransactionTaxQuanta
    totalTaxQuanta := qftTotalTransactionTaxQuanta
    taxRemainderScaledAt18 := qftTransactionTaxRemainderScaledAt18
    exactQuantumTax := decide (qftTransactionTaxRemainderScaledAt18 = 0)
    transactionTaxOfAlphaBpsScaledAt18? :=
      qftTransactionTaxOfAlphaBpsScaledAt18?
    deliveredByNeutrino :=
      neutrinoGravityDeliveryReport.deliveredByNeutrino }

#eval transactionTaxReport
#eval qftTransactionTaxBar

end Measurement
