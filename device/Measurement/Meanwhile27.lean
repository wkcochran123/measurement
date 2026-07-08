import Measurement.Meanwhile26

/- MEANWHILE 27 -- STACK THE QUANTUM-GRAVITY CELLS. A single Cavendish cell
calibrates the device gravitational constant. To tune toward alpha, build an
array of these cells and compare the accumulated device-G ticks against an
apparatus alpha target.

The target is derived from the calibrated Cavendish cell itself: take one
device-G cell and resolve the part not occupied by the tether arm inside the
measured separation. All comparison is exact Nat arithmetic. The resulting
tuning knob is the residual ratio alpha / (best cell stack), i.e. how hard to
couple the selected stack.
-/

namespace Measurement

def ApparatusRatio.mulNat (q : ApparatusRatio) (n : Nat) : ApparatusRatio :=
  { numerator := q.numerator * n
    denominator := q.denominator }

def ApparatusRatio.div (a b : ApparatusRatio) : ApparatusRatio :=
  { numerator := a.numerator * b.denominator
    denominator := a.denominator * b.numerator }

def natAbsDiff (a b : Nat) : Nat :=
  if a < b then b - a else a - b

def rationalDistanceNumerator (a b : ApparatusRatio) : Nat :=
  natAbsDiff (a.numerator * b.denominator) (b.numerator * a.denominator)

def rationalSignedNumerator (a b : ApparatusRatio) : Int :=
  Int.ofNat (a.numerator * b.denominator) -
    Int.ofNat (b.numerator * a.denominator)

def secondDifference (lower middle upper : Int) : Int :=
  upper - 2 * middle + lower

def distanceSecondDifference (lower middle upper : Nat) : Int :=
  Int.ofNat upper - 2 * Int.ofNat middle + Int.ofNat lower

def apparatusAlphaTarget : ApparatusRatio :=
  { numerator :=
      deviceG.numerator * (cavendishSeparation - cavendishArm)
    denominator := deviceG.denominator * cavendishSeparation }

def fineStructureAlphaTarget : ApparatusRatio :=
  apparatusAlphaTarget

def fineStructureInverseFinite : ApparatusRatio :=
  { numerator := fineStructureAlphaTarget.denominator
    denominator := fineStructureAlphaTarget.numerator }

def stackedDeviceG (cells : Nat) : ApparatusRatio :=
  deviceG.mulNat cells

def alphaCellFloor : Nat :=
  fineStructureAlphaTarget.numerator * deviceG.denominator /
    (fineStructureAlphaTarget.denominator * deviceG.numerator)

def alphaCellUpper : Nat :=
  alphaCellFloor + 1

def bestAlphaCellCount : Nat :=
  let lowerDistance :=
    rationalDistanceNumerator (stackedDeviceG alphaCellFloor) fineStructureAlphaTarget
  let upperDistance :=
    rationalDistanceNumerator (stackedDeviceG alphaCellUpper) fineStructureAlphaTarget
  if upperDistance <= lowerDistance then alphaCellUpper else alphaCellFloor

def alphaCurvatureCellCount : Nat :=
  bestAlphaCellCount + 1

structure QuantumGravityCell where
  index : Nat
  deviceG : ApparatusRatio
  motionResolved : Bool
  quantumGravityResolved : Bool
deriving Repr

def quantumGravityCell (index : Nat) : QuantumGravityCell :=
  { index := index
    deviceG := deviceG
    motionResolved := decide (0 < deviceG.numerator)
    quantumGravityResolved :=
      decide (0 < deviceG.numerator && deviceG.numerator < deviceG.denominator) }

def quantumGravityCells (count : Nat) : List QuantumGravityCell :=
  (List.range count).map fun index => quantumGravityCell index

structure AlphaTuneReport where
  alphaTarget : ApparatusRatio
  alphaTargetScaledAt18 : Nat
  alphaInverseTarget : ApparatusRatio
  cellG : ApparatusRatio
  lowerCells : Nat
  upperCells : Nat
  bestCells : Nat
  curvatureCells : Nat
  lowerStack : ApparatusRatio
  upperStack : ApparatusRatio
  bestStack : ApparatusRatio
  curvatureStack : ApparatusRatio
  lowerSignedResidual : Int
  upperSignedResidual : Int
  curvatureSignedResidual : Int
  lowerDistance : Nat
  upperDistance : Nat
  curvatureDistance : Nat
  bestDistance : Nat
  signedSecondDifference : Int
  observedSecondDifference : Int
  tuningRatio : ApparatusRatio
  tuningRatioScaledAt18 : Nat
  selectedCells : List QuantumGravityCell
deriving Repr

def alphaTuneReport : AlphaTuneReport :=
  let lowerStack := stackedDeviceG alphaCellFloor
  let upperStack := stackedDeviceG alphaCellUpper
  let bestStack := stackedDeviceG bestAlphaCellCount
  let curvatureStack := stackedDeviceG alphaCurvatureCellCount
  let lowerSignedResidual := rationalSignedNumerator lowerStack fineStructureAlphaTarget
  let upperSignedResidual := rationalSignedNumerator upperStack fineStructureAlphaTarget
  let curvatureSignedResidual :=
    rationalSignedNumerator curvatureStack fineStructureAlphaTarget
  let lowerDistance := rationalDistanceNumerator lowerStack fineStructureAlphaTarget
  let upperDistance := rationalDistanceNumerator upperStack fineStructureAlphaTarget
  let curvatureDistance :=
    rationalDistanceNumerator curvatureStack fineStructureAlphaTarget
  let bestDistance := rationalDistanceNumerator bestStack fineStructureAlphaTarget
  let tuningRatio := fineStructureAlphaTarget.div bestStack
  { alphaTarget := fineStructureAlphaTarget
    alphaTargetScaledAt18 := fineStructureAlphaTarget.scaledFloor (pow10 18)
    alphaInverseTarget := fineStructureInverseFinite
    cellG := deviceG
    lowerCells := alphaCellFloor
    upperCells := alphaCellUpper
    bestCells := bestAlphaCellCount
    curvatureCells := alphaCurvatureCellCount
    lowerStack := lowerStack
    upperStack := upperStack
    bestStack := bestStack
    curvatureStack := curvatureStack
    lowerSignedResidual := lowerSignedResidual
    upperSignedResidual := upperSignedResidual
    curvatureSignedResidual := curvatureSignedResidual
    lowerDistance := lowerDistance
    upperDistance := upperDistance
    curvatureDistance := curvatureDistance
    bestDistance := bestDistance
    signedSecondDifference :=
      secondDifference lowerSignedResidual upperSignedResidual curvatureSignedResidual
    observedSecondDifference :=
      distanceSecondDifference lowerDistance upperDistance curvatureDistance
    tuningRatio := tuningRatio
    tuningRatioScaledAt18 := tuningRatio.scaledFloor (pow10 18)
    selectedCells := quantumGravityCells alphaCurvatureCellCount }

theorem fineStructureAlpha_bracketed_by_zero_and_one_cells :
    (stackedDeviceG 0).numerator * fineStructureAlphaTarget.denominator
        < fineStructureAlphaTarget.numerator * (stackedDeviceG 0).denominator
      ∧
    fineStructureAlphaTarget.numerator * (stackedDeviceG 1).denominator
        < (stackedDeviceG 1).numerator * fineStructureAlphaTarget.denominator := by
  decide

theorem bestAlphaCellCount_is_one :
    bestAlphaCellCount = 1 := by
  rfl

theorem alphaCurvatureCellCount_is_two :
    alphaCurvatureCellCount = 2 := by
  rfl

theorem signedCellStackCurvature_is_zero :
    secondDifference
      (rationalSignedNumerator (stackedDeviceG 0) fineStructureAlphaTarget)
      (rationalSignedNumerator (stackedDeviceG 1) fineStructureAlphaTarget)
      (rationalSignedNumerator (stackedDeviceG 2) fineStructureAlphaTarget) = 0 := by
  decide

theorem observedAlphaSlipCurvature_positive :
    0 <
      distanceSecondDifference
        (rationalDistanceNumerator (stackedDeviceG 0) fineStructureAlphaTarget)
        (rationalDistanceNumerator (stackedDeviceG 1) fineStructureAlphaTarget)
        (rationalDistanceNumerator (stackedDeviceG 2) fineStructureAlphaTarget) := by
  decide

#eval alphaTuneReport

end Measurement
