import Measurement.Meanwhile40

/- MEANWHILE 41 -- QUANTUM LOOP CHARGE SIMULATION. Alpha is not itself the
elementary charge in the natural-charge normalization. The charge is read as

  e^2 = 4*pi*alpha.

The loop simulation leaves the orbit state uncollapsed on the timelike side of
the Lorentz bracket. Each pass adds one wobble quantum. The wobble is therefore
the induced charge per loop, and the report asks how many live passes are needed
before the accumulated induced charge reaches the elementary charge.
-/

namespace Measurement

def truncatedPiNumeratorForCharge : Nat :=
  314159265358979323846

def truncatedPiScaleForCharge : Nat :=
  100000000000000000000

def fourPiRatio : ApparatusRatio :=
  { numerator := 4 * truncatedPiNumeratorForCharge
    denominator := truncatedPiScaleForCharge }

def elementaryChargeSquaredFromAlpha (alpha : ApparatusRatio) :
    ApparatusRatio :=
  fourPiRatio.mul alpha

def ApparatusRatio.squareLeScaled
    (q : ApparatusRatio) (scale candidate : Nat) : Bool :=
  candidate * candidate * q.denominator <= q.numerator * scale * scale

def ApparatusRatio.sqrtScaledFloorAux
    (q : ApparatusRatio) (scale : Nat) :
    Nat -> Nat -> Nat -> Nat
  | 0, lower, _upper => lower
  | fuel + 1, lower, upper =>
      if upper <= lower + 1 then
        lower
      else
        let mid := (lower + upper) / 2
        if q.squareLeScaled scale mid then
          q.sqrtScaledFloorAux scale fuel mid upper
        else
          q.sqrtScaledFloorAux scale fuel lower mid

def ApparatusRatio.sqrtScaledFloor (q : ApparatusRatio) (scale : Nat) : Nat :=
  q.sqrtScaledFloorAux scale 128 0 (scale + 1)

def inducedChargePerLoop : ApparatusRatio :=
  orbitWobble

def inducedChargeAfterLoops (loops : Nat) : ApparatusRatio :=
  inducedChargePerLoop.mulNat loops

def ratioLeq (a b : ApparatusRatio) : Bool :=
  a.numerator * b.denominator <= b.numerator * a.denominator

def inducedChargeReachesElementary
    (elementaryChargeSquared : ApparatusRatio) (loops : Nat) : Bool :=
  ratioLeq elementaryChargeSquared (inducedChargeAfterLoops loops).sq

def firstReachingLoopUpperAux
    (elementaryChargeSquared : ApparatusRatio) :
    Nat -> Nat -> Nat
  | 0, upper => upper
  | fuel + 1, upper =>
      if inducedChargeReachesElementary elementaryChargeSquared upper then
        upper
      else
        firstReachingLoopUpperAux elementaryChargeSquared fuel (2 * upper)

def bisectFirstReachingLoopAux
    (elementaryChargeSquared : ApparatusRatio) :
    Nat -> Nat -> Nat -> Nat
  | 0, _lower, upper => upper
  | fuel + 1, lower, upper =>
      if upper <= lower + 1 then
        upper
      else
        let mid := (lower + upper) / 2
        if inducedChargeReachesElementary elementaryChargeSquared mid then
          bisectFirstReachingLoopAux elementaryChargeSquared fuel lower mid
        else
          bisectFirstReachingLoopAux elementaryChargeSquared fuel mid upper

def firstReachingLoop (elementaryChargeSquared : ApparatusRatio) : Nat :=
  let upper := firstReachingLoopUpperAux elementaryChargeSquared 64 1
  bisectFirstReachingLoopAux elementaryChargeSquared 64 0 upper

def RationalRadius.fallsIn (radius : RationalRadius) : Bool :=
  radius.numerator <= radius.denominator

def quantumLoopRadius : RationalRadius :=
  upperLorentzOrbitRadius

def quantumLoopOrbitRead : LorentzOrbitRead :=
  lorentzOrbitRead "quantum-live-loop" quantumLoopRadius

structure QuantumLoopChargeState where
  loopsSpent : Nat
  radius : RationalRadius
  radiusScaledAt18 : Nat
  regime : LorentzOrbitRegime
  fellIn : Bool
  statePreserved : Bool
  inducedFullTurns : Nat
  inducedResidue : Nat
  inducedCharge : ApparatusRatio
  inducedChargeScaledAt18 : Nat
deriving Repr

def quantumLoopChargeState (loops : Nat) : QuantumLoopChargeState :=
  let rawInduced := loops * inducedChargePerLoop.numerator
  let read := quantumLoopOrbitRead
  let fellIn := quantumLoopRadius.fallsIn
  let inducedCharge := inducedChargeAfterLoops loops
  { loopsSpent := loops
    radius := quantumLoopRadius
    radiusScaledAt18 := read.radiusScaledAt18
    regime := read.regime
    fellIn := fellIn
    statePreserved := !fellIn
    inducedFullTurns := rawInduced / inducedChargePerLoop.denominator
    inducedResidue := rawInduced % inducedChargePerLoop.denominator
    inducedCharge := inducedCharge
    inducedChargeScaledAt18 := inducedCharge.scaledFloor (pow10 18) }

structure QuantumChargeLoopReport where
  normalization : String
  alpha : ApparatusRatio
  alphaScaledAt18 : Nat
  elementaryChargeSquared : ApparatusRatio
  elementaryChargeSquaredScaledAt18 : Nat
  elementaryChargeScaledAt18 : Nat
  inducedChargePerLoop : ApparatusRatio
  inducedChargePerLoopScaledAt18 : Nat
  firstLoopAtElementaryCharge : Nat
  lowerLoop : Nat
  lowerState : QuantumLoopChargeState
  upperState : QuantumLoopChargeState
  lowerBelowElementaryCharge : Bool
  upperReachesElementaryCharge : Bool
deriving Repr

def quantumChargeLoopReport
    (alphaReport : AlphaSecondVariationReport) : QuantumChargeLoopReport :=
  let e2 := elementaryChargeSquaredFromAlpha alphaReport.alpha
  let firstLoop := firstReachingLoop e2
  let lowerLoop := firstLoop - 1
  { normalization := "h = c = 1"
    alpha := alphaReport.alpha
    alphaScaledAt18 := alphaReport.alphaScaledAt18
    elementaryChargeSquared := e2
    elementaryChargeSquaredScaledAt18 := e2.scaledFloor (pow10 18)
    elementaryChargeScaledAt18 := e2.sqrtScaledFloor (pow10 18)
    inducedChargePerLoop := inducedChargePerLoop
    inducedChargePerLoopScaledAt18 :=
      inducedChargePerLoop.scaledFloor (pow10 18)
    firstLoopAtElementaryCharge := firstLoop
    lowerLoop := lowerLoop
    lowerState := quantumLoopChargeState lowerLoop
    upperState := quantumLoopChargeState firstLoop
    lowerBelowElementaryCharge :=
      !inducedChargeReachesElementary e2 lowerLoop
    upperReachesElementaryCharge :=
      inducedChargeReachesElementary e2 firstLoop }

def defaultQuantumChargeLoopReport? : Option QuantumChargeLoopReport :=
  defaultAlphaSecondVariationReport?.map quantumChargeLoopReport

theorem quantumLoopRadius_does_not_fall_in :
    quantumLoopRadius.fallsIn = false := by
  rfl

#eval defaultQuantumChargeLoopReport?

end Measurement
