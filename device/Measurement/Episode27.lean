import Measurement.Episode26

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

/-! # Meanwhile 27 — the α-cell: the fine-structure facet, bracketed  (┃ spectroscopist)

**The genre skin (┃).** A spectroscopist at the eyepiece, reading a line against an engraved graticule.
The rulings are ours; we report only where the line falls between two of them.

**Object & facet.** α is the fine-structure facet of the object Yang–Mills describes — and the device
does NOT capture it. It BRACKETS it: catches the target line strictly between two of its own engraved
cells. We describe this facet by squeezing it between exact bounds; we never claim to derive or solve α,
never open or solve Yang–Mills, and the last box — the object's own ground — stays wrapped.

**The squeeze (its purest form).** This is the clearest Weierstrass sandwich in the walk:
`fineStructureAlphaTarget` is caught STRICTLY between `stackedDeviceG 0` (lower bound) and
`stackedDeviceG 1` (upper bound), decided by cross-multiplied *integer* inequalities (`decide`), no float.
And the sandwich is honest: the cell stack is FLAT (the signed second difference across cells 0,1,2 is
zero) and the gap is REAL (the distance second difference is positive) — flat scale, real gap, so the
target genuinely sits between the marks rather than on one. This is the device's own target between its
own rulings — not the physical fine-structure constant ≈ 1/137; that distinction is literal, not a
disavowal.
-/

namespace Measurement

/-- `ApparatusRatio.mulNat (q) (n) : ApparatusRatio` — scale a ratio by a whole number `n`: numerator
`q.numerator * n`, denominator unchanged. Stacking `n` copies of a cell. -/
def ApparatusRatio.mulNat (q : ApparatusRatio) (n : Nat) : ApparatusRatio :=
  { numerator := q.numerator * n
    denominator := q.denominator }

/-- `ApparatusRatio.div (a) (b) : ApparatusRatio` — divide two ratios by cross-multiplying: numerator
`a.numerator * b.denominator`, denominator `a.denominator * b.numerator`. The tuning ratio uses this. -/
def ApparatusRatio.div (a b : ApparatusRatio) : ApparatusRatio :=
  { numerator := a.numerator * b.denominator
    denominator := a.denominator * b.numerator }

/-- `natAbsDiff (a) (b) : Nat` — the absolute difference of two `Nat`s (`if a < b then b - a else a - b`),
avoiding truncated subtraction. -/
def natAbsDiff (a b : Nat) : Nat :=
  if a < b then b - a else a - b

/-- `rationalDistanceNumerator (a) (b) : Nat` — the cross-multiplied absolute gap between two ratios,
`natAbsDiff (a.numerator * b.denominator) (b.numerator * a.denominator)`. How far apart two ratios sit,
exactly, as a whole number. -/
def rationalDistanceNumerator (a b : ApparatusRatio) : Nat :=
  natAbsDiff (a.numerator * b.denominator) (b.numerator * a.denominator)

/-- `rationalSignedNumerator (a) (b) : Int` — the signed cross-multiplied gap,
`(a.numerator * b.denominator) - (b.numerator * a.denominator)` over `Int`; positive when `a > b`. The
signed residual the curvature reads. -/
def rationalSignedNumerator (a b : ApparatusRatio) : Int :=
  Int.ofNat (a.numerator * b.denominator) -
    Int.ofNat (b.numerator * a.denominator)

/-- `secondDifference (lower) (middle) (upper) : Int` — the discrete curvature `upper - 2*middle + lower`
of three signed readings; zero iff they are collinear (evenly spaced). -/
def secondDifference (lower middle upper : Int) : Int :=
  upper - 2 * middle + lower

/-- `distanceSecondDifference (lower) (middle) (upper) : Int` — the same second difference over `Nat`
inputs lifted to `Int`; positive when the middle dips below the chord (a real gap). -/
def distanceSecondDifference (lower middle upper : Nat) : Int :=
  Int.ofNat upper - 2 * Int.ofNat middle + Int.ofNat lower

/-- `apparatusAlphaTarget : ApparatusRatio` — the α target drawn from the device's own calibrated cell:
numerator `deviceG.numerator * (cavendishSeparation - cavendishArm)`, denominator `deviceG.denominator *
cavendishSeparation`. The line the graticule is to bracket, built from `G`, not imported. -/
def apparatusAlphaTarget : ApparatusRatio :=
  { numerator :=
      deviceG.numerator * (cavendishSeparation - cavendishArm)
    denominator := deviceG.denominator * cavendishSeparation }

/-- `fineStructureAlphaTarget : ApparatusRatio` — `apparatusAlphaTarget` under the name "alpha": the
fine-structure facet's target line. The device's own target, not the physical constant. -/
def fineStructureAlphaTarget : ApparatusRatio :=
  apparatusAlphaTarget

/-- `fineStructureInverseFinite : ApparatusRatio` — the reciprocal of the α target (numerator and
denominator swapped): the finite "inverse-α" read. -/
def fineStructureInverseFinite : ApparatusRatio :=
  { numerator := fineStructureAlphaTarget.denominator
    denominator := fineStructureAlphaTarget.numerator }

/-- `stackedDeviceG (cells) : ApparatusRatio` — a stack of `cells` device-G cells, `deviceG.mulNat cells`.
These are the engraved rulings the target is bracketed between; cell 0, cell 1, cell 2, … -/
def stackedDeviceG (cells : Nat) : ApparatusRatio :=
  deviceG.mulNat cells

/-- `alphaCellFloor : Nat` — the ruling just below the target: the integer part of `αTarget / deviceG` by
cross-multiplied `Nat` division. The lower bracket index. -/
def alphaCellFloor : Nat :=
  fineStructureAlphaTarget.numerator * deviceG.denominator /
    (fineStructureAlphaTarget.denominator * deviceG.numerator)

/-- `alphaCellUpper : Nat` — the ruling just above, `alphaCellFloor + 1`. The upper bracket index. -/
def alphaCellUpper : Nat :=
  alphaCellFloor + 1

/-- `bestAlphaCellCount : Nat` — whichever of `alphaCellFloor`/`alphaCellUpper` the target sits closer to,
comparing their `rationalDistanceNumerator`s (a tie resolves to the upper). The nearest ruling. -/
def bestAlphaCellCount : Nat :=
  let lowerDistance :=
    rationalDistanceNumerator (stackedDeviceG alphaCellFloor) fineStructureAlphaTarget
  let upperDistance :=
    rationalDistanceNumerator (stackedDeviceG alphaCellUpper) fineStructureAlphaTarget
  if upperDistance <= lowerDistance then alphaCellUpper else alphaCellFloor

/-- `alphaCurvatureCellCount : Nat` — one ruling further out, `bestAlphaCellCount + 1`, so cells 0,1,2 are
in hand to read the stack's curvature. -/
def alphaCurvatureCellCount : Nat :=
  bestAlphaCellCount + 1

/-- `QuantumGravityCell` — one ruling backed by its device-G and two flags (`Repr`). Read the flags
plainly: `motionResolved`/`quantumGravityResolved` are the cell's own consistency checks (`G` positive; a
proper fraction), not a claim about the world. -/
structure QuantumGravityCell where
  index : Nat
  deviceG : ApparatusRatio
  motionResolved : Bool
  quantumGravityResolved : Bool
deriving Repr

/-- `quantumGravityCell (index) : QuantumGravityCell` — build the cell at `index`, carrying `deviceG` and
its `decide`-computed consistency flags. -/
def quantumGravityCell (index : Nat) : QuantumGravityCell :=
  { index := index
    deviceG := deviceG
    motionResolved := decide (0 < deviceG.numerator)
    quantumGravityResolved :=
      decide (0 < deviceG.numerator && deviceG.numerator < deviceG.denominator) }

/-- `quantumGravityCells (count) : List QuantumGravityCell` — the first `count` cells,
`(List.range count).map quantumGravityCell`. -/
def quantumGravityCells (count : Nat) : List QuantumGravityCell :=
  (List.range count).map fun index => quantumGravityCell index

/-- `AlphaTuneReport` — the full sighting: the target with its inverse and scaling, the four cell counts
(lower/upper/best/curvature) and their stacks, the signed and absolute residuals to each, the two second
differences (signed and observed), the tuning ratio, and the selected cells. -/
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

/-- `alphaTuneReport : AlphaTuneReport` — assemble the sighting: stack `G` at each cell count, take signed
and absolute residuals to the target, the signed and observed curvatures, and the tuning ratio (target
over the best stack). One complete reading of the line against the rulings. -/
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

/-- `fineStructureAlpha_bracketed_by_zero_and_one_cells`.
**Proposition:** the α target is caught STRICTLY between cell 0 and cell 1, as two cross-multiplied `Nat`
inequalities — `(stackedDeviceG 0).numerator * fineStructureAlphaTarget.denominator <
fineStructureAlphaTarget.numerator * (stackedDeviceG 0).denominator` (cell 0 below the target) ∧
`fineStructureAlphaTarget.numerator * (stackedDeviceG 1).denominator < (stackedDeviceG 1).numerator *
fineStructureAlphaTarget.denominator` (cell 1 above it).
**Mechanism:** `by decide` — the kernel evaluates the two decidable integer inequalities; exact, no float.
**Squeeze role:** the PUREST tick of the walk's squeeze — α caught strictly between two of the device's
own cells, the literal Weierstrass sandwich. α is described by bracketing, never captured, never the
physical 1/137. -/
theorem fineStructureAlpha_bracketed_by_zero_and_one_cells :
    (stackedDeviceG 0).numerator * fineStructureAlphaTarget.denominator
        < fineStructureAlphaTarget.numerator * (stackedDeviceG 0).denominator
      ∧
    fineStructureAlphaTarget.numerator * (stackedDeviceG 1).denominator
        < (stackedDeviceG 1).numerator * fineStructureAlphaTarget.denominator := by
  decide

/-- `bestAlphaCellCount_is_one : bestAlphaCellCount = 1`. **Proposition:** the nearest ruling is cell 1.
**Mechanism:** `rfl` — kernel-computed. **Squeeze role:** names the closer of the two bracketing cells. -/
theorem bestAlphaCellCount_is_one :
    bestAlphaCellCount = 1 := by
  rfl

/-- `alphaCurvatureCellCount_is_two : alphaCurvatureCellCount = 2`. **Proposition:** the third ruling is
cell 2. **Mechanism:** `rfl`. **Squeeze role:** the third mark, so cells 0,1,2 give the stack's
curvature. -/
theorem alphaCurvatureCellCount_is_two :
    alphaCurvatureCellCount = 2 := by
  rfl

/-- `signedCellStackCurvature_is_zero`. **Proposition:** the signed second difference of the residuals
across cells 0,1,2 (`secondDifference` of the three `rationalSignedNumerator`s to the target) is `0`.
**Mechanism:** `by decide` — kernel-evaluated. **Squeeze role:** the stack is FLAT — the rulings are
evenly cut, no bend in the scale, so the bracket is trustworthy. -/
theorem signedCellStackCurvature_is_zero :
    secondDifference
      (rationalSignedNumerator (stackedDeviceG 0) fineStructureAlphaTarget)
      (rationalSignedNumerator (stackedDeviceG 1) fineStructureAlphaTarget)
      (rationalSignedNumerator (stackedDeviceG 2) fineStructureAlphaTarget) = 0 := by
  decide

/-- `observedAlphaSlipCurvature_positive`. **Proposition:** the distance second difference across cells
0,1,2 (`distanceSecondDifference` of the three `rationalDistanceNumerator`s) is `> 0`.
**Mechanism:** `by decide`. **Squeeze role:** the gap is REAL — the target dips between the marks rather
than lying on one; with the flat stack, the value is genuinely bracketed. -/
theorem observedAlphaSlipCurvature_positive :
    0 <
      distanceSecondDifference
        (rationalDistanceNumerator (stackedDeviceG 0) fineStructureAlphaTarget)
        (rationalDistanceNumerator (stackedDeviceG 1) fineStructureAlphaTarget)
        (rationalDistanceNumerator (stackedDeviceG 2) fineStructureAlphaTarget) := by
  decide

/-! ## Readout — the sighting logged
`#eval alphaTuneReport` prints the whole sighting: the target, both bracketing stacks and the curvature
stack, the residuals and curvatures, the tuning ratio. The theorems above are the bracket; this is the
plate. α is fenced in, not possessed — the next facet, proximity, is next door. -/
#eval alphaTuneReport

end Measurement
