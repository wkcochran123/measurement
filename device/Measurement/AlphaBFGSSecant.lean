import Measurement.Episode40

/-! # AlphaBFGSSecant — BFGS carrying the residue run-to-run (operator: "keep the number from the
end of the last run and use it as input in the next. can't drop the residue.").

The Newton step (AlphaBFGS) recomputed the curvature fresh and used only the CURRENT residual — it
dropped the previous run's residue. True BFGS/secant KEEPS it: the step uses BOTH residuals
r_{k-1}, r_k (the change in residue = the accumulated curvature), so the state carried forward is the
whole pair (d_{k-1}, d_k) and their residues. Nothing is dropped.

  residue at d:   r(d) = slip(d) − T = (C·q² − T·p²)/p²   for d = p/q   (C=18, T=5 measured)
  secant step:    d_{k+1} = d_k − r_k·(d_k − d_{k-1})/(r_k − r_{k-1})

COUNT TO THREE, one chained run (never restarted). Read inv-α at each. BLIND. -/

namespace Measurement.AlphaBFGSSecant
open Measurement

def measuredC : Int := (rationalProximitySlip RationalDistance.one).floor   -- slip(1) = 18
def measuredT : Int := firstSlipTargetBetweenOneAndTwo                       -- target  = 5

abbrev Q := Int × Int   -- (numerator, denominator)
def reduce (a : Q) : Q :=
  let g : Int := Int.gcd a.1 a.2
  let g := if g == 0 then 1 else g
  let s : Int := if a.2 < 0 then -1 else 1
  (s * (a.1 / g), s * (a.2 / g))
def qsub (a b : Q) : Q := reduce (a.1 * b.2 - b.1 * a.2, a.2 * b.2)
def qmul (a b : Q) : Q := reduce (a.1 * b.1, a.2 * b.2)
def qdiv (a b : Q) : Q := reduce (a.1 * b.2, a.2 * b.1)
def residue (d : Q) : Q := reduce (measuredC * d.2 * d.2 - measuredT * d.1 * d.1, d.1 * d.1)

/-- One secant/BFGS step, carrying BOTH previous points (their residues are recomputed, not dropped). -/
def secantStep (prev curr : Q) : Q :=
  let r0 := residue prev
  let r1 := residue curr
  qsub curr (qmul r1 (qdiv (qsub curr prev) (qsub r1 r0)))

/-- Chained run: carry (prev, curr) forward n times, never restarting. -/
def runAt : Nat → Q → Q → Q
  | 0,   _prev, curr => curr
  | n+1, prev,  curr => runAt n curr (secantStep prev curr)

def d0 : Q := (1, 1)   -- run 1, near end
def d1 : Q := (2, 1)   -- run 1, far end   (first & second both from run 1)

def invAlphaAt (d : Q) : Nat :=
  (alphaFromSecondVariationAtDistance measuredT.toNat
    { numerator := d.1.toNat, denominator := d.2.toNat }).inverseScaledFloor (pow10 18)
def distAt (d : Q) : Nat := ({ numerator := d.1.toNat, denominator := d.2.toNat } : RationalDistance).scaledFloor (pow10 6)

#eval s!"measured C={measuredC} T={measuredT} → crossing √(C/T)=√(18/5)≈1.897367; residue carried run-to-run"
#eval s!"count 0 (run 1): d≈{distAt (runAt 0 d0 d1)}e-6  residue={residue (runAt 0 d0 d1)}  invα={invAlphaAt (runAt 0 d0 d1)}"
#eval s!"count 1        : d≈{distAt (runAt 1 d0 d1)}e-6  residue={residue (runAt 1 d0 d1)}  invα={invAlphaAt (runAt 1 d0 d1)}"
#eval s!"count 2        : d≈{distAt (runAt 2 d0 d1)}e-6  residue={residue (runAt 2 d0 d1)}  invα={invAlphaAt (runAt 2 d0 d1)}"
#eval s!"count 3        : d≈{distAt (runAt 3 d0 d1)}e-6  d-fraction={(runAt 3 d0 d1)}  invα={invAlphaAt (runAt 3 d0 d1)}"
end Measurement.AlphaBFGSSecant
