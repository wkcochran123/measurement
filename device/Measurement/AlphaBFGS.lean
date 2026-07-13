import Measurement.Episode40

/-! # AlphaBFGS — the coupling as a quasi-Newton (BFGS) descent on the MEASURED variations.
Operator: "first and second from the first run and second from the second run. There. BFGS implemented."

Root-find the crossing where the second-variation slip meets the target: slip(d) = T, i.e. d* = √(C/T).
The machine MEASURES C = slip(1) (the inverse-square second-variation coefficient) and T = target.
Newton/quasi-Newton step (1D BFGS = secant on the measured slope + curvature):
    d_{k+1} = d_k · (3C − T·d_k²) / (2C)     (uses the first variation = slope, second variation = C)
Each step "puts the last run back in" (accumulated history). COUNT TO THREE: three steps, 1 2 3.
Read inv-α at the converged crossing via the same alpha map the report uses. BLIND: numbers read last. -/

namespace Measurement.AlphaBFGS
open Measurement

-- MEASURED second variation, from the machine's own output (not hardcoded):
def measuredC : Nat := (rationalProximitySlip RationalDistance.one).floor   -- slip(1) = 18
def measuredT : Nat := firstSlipTargetBetweenOneAndTwo                       -- target  = 5

/-- 1D BFGS / Newton step toward slip(d)=T (= √(C/T)), using the measured first & second variation. -/
def bfgsStep (d : RationalDistance) : RationalDistance :=
  let p := d.numerator; let q := d.denominator
  { numerator   := p * (3 * measuredC * q * q - measuredT * p * p)
    denominator := 2 * measuredC * q * q * q }

def bfgsAt : Nat → RationalDistance → RationalDistance
  | 0,   d => d
  | n+1, d => bfgsAt n (bfgsStep d)

def d0 : RationalDistance := { numerator := 2, denominator := 1 }   -- run 1: the far bracket end

def invAlphaAt (d : RationalDistance) : Nat :=
  (alphaFromSecondVariationAtDistance measuredT d).inverseScaledFloor (pow10 18)

#eval s!"measured second variation: C=slip(1)={measuredC}  T=target={measuredT}  → crossing √({measuredC}/{measuredT})"
#eval s!"BFGS count 0 (run 1): d≈{(bfgsAt 0 d0).scaledFloor (pow10 6)}e-6   invα(×1e18)={invAlphaAt (bfgsAt 0 d0)}"
#eval s!"BFGS count 1        : d≈{(bfgsAt 1 d0).scaledFloor (pow10 6)}e-6   invα(×1e18)={invAlphaAt (bfgsAt 1 d0)}"
#eval s!"BFGS count 2        : d≈{(bfgsAt 2 d0).scaledFloor (pow10 6)}e-6   invα(×1e18)={invAlphaAt (bfgsAt 2 d0)}"
#eval s!"BFGS count 3        : d≈{(bfgsAt 3 d0).scaledFloor (pow10 6)}e-6   invα(×1e18)={invAlphaAt (bfgsAt 3 d0)}"
#eval s!"count-1 reduced fraction: {(bfgsAt 1 d0).numerator}/{(bfgsAt 1 d0).denominator}  (cf CF convergent 17/9)"
end Measurement.AlphaBFGS

-- Choice-free witness: the count-0/count-1 BFGS pair is an ordered bracket (= the mediant's), decided.
namespace Measurement.AlphaBFGS
def bfgsInv0 : Nat := invAlphaAt (bfgsAt 0 d0)   -- 129.6
def bfgsInv1 : Nat := invAlphaAt (bfgsAt 1 d0)   -- 137.7
theorem bfgs_bracket_ordered : bfgsInv0 < bfgsInv1 := by decide
#print axioms bfgs_bracket_ordered
end Measurement.AlphaBFGS
