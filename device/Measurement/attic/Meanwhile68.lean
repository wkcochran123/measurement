import Measurement.Meanwhile67

/- MEANWHILE 68 -- TWO ORDERS AUDIT. The one-sided transaction tax is visible,
but its effect is small. This file asks whether the missing effect looks like
one of the ordinary decimal orders of magnitude: one quantum, ten quanta, one
hundred quanta.

This is an audit, not a correction. It reports the shifted alpha reads and the
tax size in basis points, then leaves the apparatus center unchanged.
-/

namespace Measurement

def scaleNat (n factor : Nat) : Nat :=
  n * factor

structure TaxOrderRead where
  factor : Nat
  taxScaledAt18 : Nat
  lowerAlphaScaledAt18 : Nat
  upperAlphaScaledAt18 : Nat
  lowerInverseAlphaScaledAt18? : Option Nat
  upperInverseAlphaScaledAt18? : Option Nat
  taxOfAlphaBpsScaledAt18? : Option Nat
  exactMultipleOfGravityQuantum : Bool
deriving Repr

def taxOrderRead (factor : Nat) : TaxOrderRead :=
  let tax := scaleNat qftGravityQuantumScaledAt18 factor
  { factor := factor
    taxScaledAt18 := tax
    lowerAlphaScaledAt18 := qftAlphaScaledAt18 - tax
    upperAlphaScaledAt18 := qftAlphaScaledAt18 + tax
    lowerInverseAlphaScaledAt18? :=
      alphaInverseReadScaledAt18? (qftAlphaScaledAt18 - tax)
    upperInverseAlphaScaledAt18? :=
      alphaInverseReadScaledAt18? (qftAlphaScaledAt18 + tax)
    taxOfAlphaBpsScaledAt18? :=
      (ratioScaledAt18? tax qftAlphaScaledAt18).map
        scaledFractionToBasisPointsScaledAt18
    exactMultipleOfGravityQuantum :=
      decide (taxRemainder tax qftGravityQuantumScaledAt18 = 0) }

def taxOrderFactors : List Nat :=
  [1, 10, 100]

def taxOrderReads : List TaxOrderRead :=
  taxOrderFactors.map taxOrderRead

structure TwoOrdersAuditReport where
  name : String
  interpretation : String
  centerAlphaScaledAt18 : Nat
  centerInverseAlphaScaledAt18? : Option Nat
  gravityQuantumScaledAt18 : Nat
  oneSidedTaxOfAlphaBpsScaledAt18? : Option Nat
  hundredQuantumTaxOfAlphaBpsScaledAt18? : Option Nat
  reads : List TaxOrderRead
  centerUnchanged : Bool
deriving Repr

def twoOrdersAuditReport : TwoOrdersAuditReport :=
  { name := "two-orders-tax-audit"
    interpretation :=
      "compare one, ten, and one hundred gravity-quanta tax shifts without changing the apparatus alpha"
    centerAlphaScaledAt18 := qftAlphaScaledAt18
    centerInverseAlphaScaledAt18? := qftAlphaReport.qftInverseAlphaScaledAt18?
    gravityQuantumScaledAt18 := qftGravityQuantumScaledAt18
    oneSidedTaxOfAlphaBpsScaledAt18? :=
      oneSidedTransactionTaxReport.oneSidedTaxOfAlphaBpsScaledAt18?
    hundredQuantumTaxOfAlphaBpsScaledAt18? :=
      (taxOrderRead 100).taxOfAlphaBpsScaledAt18?
    reads := taxOrderReads
    centerUnchanged :=
      decide (qftAlphaScaledAt18 = qftAlphaReport.qftAlphaScaledAt18) }

#eval twoOrdersAuditReport

end Measurement
