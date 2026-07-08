import Measurement.Meanwhile24

/- MEANWHILE 25 -- ROTATE THE CORRIDOR. The corridor is already a number once the
class instances interpret it. This file adds the rotation operation without
rebuilding the corridor: rotate the tape/read head, then ask the same resolved
instance fields; rotate the recovered bracket, then ask the existing face readers.

The target is the finite half-turn itself: floor((pi / 2) * 10^precision).
-/

namespace Measurement

universe i j

namespace Number

def corridorDepth : Number -> Nat
  | .zero _ => 0
  | .one _ n => corridorDepth n + 1

end Number

inductive CompilerTapeCell where
  | strap : Fact -> Fact -> Type i -> Type (i+1) -> CompilerTapeCell
  | compute : Fact -> Fact -> Prop -> Type i -> Type (i+1) -> Type (i+1) -> CompilerTapeCell

namespace CompilerTapeCell

def plug : CompilerTapeCell -> CompilerTape -> CompilerTape
  | .strap a b value lifted, tail => .strap a b value lifted tail
  | .compute a b p value lifted liftedAgain, tail =>
      .compute a b p value lifted liftedAgain tail

end CompilerTapeCell

namespace CompilerTape

def length : CompilerTape -> Nat
  | .boot _ _ => 1
  | .strap _ _ _ _ tail => length tail + 1
  | .compute _ _ _ _ _ _ tail => length tail + 1

def snoc : CompilerTape -> CompilerTapeCell -> CompilerTape
  | .boot f value, cell => cell.plug (.boot f value)
  | .strap a b value lifted tail, cell =>
      .strap a b value lifted (snoc tail cell)
  | .compute a b p value lifted liftedAgain tail, cell =>
      .compute a b p value lifted liftedAgain (snoc tail cell)

def rotateOnce : CompilerTape -> CompilerTape
  | .boot f value => .boot f value
  | .strap a b value lifted tail =>
      snoc tail (.strap a b value lifted)
  | .compute a b p value lifted liftedAgain tail =>
      snoc tail (.compute a b p value lifted liftedAgain)

def rotate : Nat -> CompilerTape -> CompilerTape
  | 0, tape => tape
  | n + 1, tape => rotate n (rotateOnce tape)

def rotateBounded (turns : Nat) (tape : CompilerTape) : CompilerTape :=
  rotate (turns % tape.length) tape

def headSlip : CompilerTape -> Fact
  | .compute c s _ _ _ _ _ =>
      { truth := ¬(c.truth ↔ s.truth)
        decTruth := @instDecidableNot _ (@instDecidableIff _ _ c.decTruth s.decTruth) }
  | .boot _ _ => { truth := False, decTruth := isFalse (fun h => h) }
  | .strap _ _ _ _ _ => { truth := False, decTruth := isFalse (fun h => h) }

end CompilerTape

def Fact.asBool (f : Fact) : Bool :=
  match f.decTruth with
  | .isTrue _ => true
  | .isFalse _ => false

def rotatedTraceSlip
    (Value : Type i) (Carrier : CarrierProcess Value) (rung : Nat) (Lifted : Type j)
    [top : EXECUTED_TRACE Value Carrier rung Lifted] (turns : Nat) : Fact :=
  CompilerTape.headSlip (CompilerTape.rotateBounded turns top.tape)

def rotatedTraceSlipBool
    (Value : Type i) (Carrier : CarrierProcess Value) (rung : Nat) (Lifted : Type j)
    [top : EXECUTED_TRACE Value Carrier rung Lifted] (turns : Nat) : Bool :=
  (rotatedTraceSlip Value Carrier rung Lifted turns).asBool

namespace BracketedNumber

def rotateForward (n : BracketedNumber) : BracketedNumber :=
  { lower := n.upper
    upper := n.value
    value := n.lower }

def rotate : Nat -> BracketedNumber -> BracketedNumber
  | 0, n => n
  | turns + 1, n => rotate turns (rotateForward n)

end BracketedNumber

inductive CorridorFace where
  | charge
  | mass
  | value
deriving Repr, DecidableEq

def CorridorFace.rotate : CorridorFace -> CorridorFace
  | .charge => .mass
  | .mass => .value
  | .value => .charge

def CorridorFace.rotateN : Nat -> CorridorFace -> CorridorFace
  | 0, face => face
  | n + 1, face => rotateN n face.rotate

def pow10 : Nat -> Nat
  | 0 => 1
  | n + 1 => 10 * pow10 n

def piDecimalDigits : List Nat :=
  [1, 4, 1, 5, 9, 2, 6, 5, 3, 5, 8, 9, 7, 9, 3, 2, 3, 8, 4, 6,
   2, 6, 4, 3, 3, 8, 3, 2, 7, 9, 5, 0, 2, 8, 8, 4, 1, 9, 7, 1]

def piTruncatedTurns : Nat -> Nat
  | 0 => 3
  | precision + 1 =>
      10 * piTruncatedTurns precision + piDecimalDigits.getD precision 0

def halfPiTruncatedTurns (precision : Nat) : Nat :=
  piTruncatedTurns precision / 2

def corridorPeriod : Nat :=
  3

def corridorReducedTurns (turns : Nat) : Nat :=
  turns % corridorPeriod

structure RotatedCorridorRead where
  precision : Nat
  scale : Nat
  turns : Nat
  reducedTurns : Nat
  activeFace : CorridorFace
  chargeDepth : Nat
  massDepth : Nat
  valueDepth : Nat
  phase : QPhase
  electronBoxValue : Nat
deriving Repr

def rotatedCorridorRead
    (precision : Nat) (n : BracketedNumber) (ledger : Fact) : RotatedCorridorRead :=
  let turns := halfPiTruncatedTurns precision
  let reducedTurns := corridorReducedTurns turns
  let rotated := n.rotate reducedTurns
  let recovered := recover rotated ledger
  { precision := precision
    scale := pow10 precision
    turns := turns
    reducedTurns := reducedTurns
    activeFace := CorridorFace.rotateN reducedTurns .charge
    chargeDepth := recovered.charge.corridorDepth
    massDepth := recovered.mass.corridorDepth
    valueDepth := rotated.value.corridorDepth
    phase := recovered.phase
    electronBoxValue := electronBox.val }

def driverBracket : BracketedNumber :=
  { lower := .one Fact.Truth (.one Fact.Truth (.zero Fact.Truth))
    upper := .zero Fact.Truth
    value := .one Fact.Truth (.zero Fact.Truth) }

def rotatedDriverCorridor (maxPrecision : Nat) : List RotatedCorridorRead :=
  (List.range (maxPrecision + 1)).map fun precision =>
    rotatedCorridorRead precision driverBracket Fact.Truth

def CorridorFace.ofReducedTurns : Nat -> CorridorFace
  | 0 => .charge
  | 1 => .mass
  | _ => .value

def CorridorFace.ofTurns (turns : Nat) : CorridorFace :=
  ofReducedTurns (corridorReducedTurns turns)

def corridorTripletIndex (turns : Nat) : Nat :=
  turns / corridorPeriod

def valueForMassTriplet (turns : Nat) : Nat :=
  match CorridorFace.ofTurns turns with
  | .mass => turns + 1
  | _ => turns

def valueForChargeTriplet (turns : Nat) : Nat :=
  match CorridorFace.ofTurns turns with
  | .charge => turns + 1
  | _ => turns

def chargeTurnsUpTo (n : Nat) : Nat :=
  n / corridorPeriod

def massTurnsUpTo (n : Nat) : Nat :=
  n / corridorPeriod + if 1 <= n % corridorPeriod then 1 else 0

def valueTurnsUpTo (n : Nat) : Nat :=
  n / corridorPeriod + if 2 <= n % corridorPeriod then 1 else 0

def countBetween (countUpTo : Nat -> Nat) (lower upper : Nat) : Nat :=
  if upper < lower then
    0
  else
    countUpTo upper - countUpTo (lower - 1)

structure CorridorBinReport where
  lower : Nat
  upper : Nat
  total : Nat
  chargeCount : Nat
  massCount : Nat
  valueCount : Nat
  upperReducedTurns : Nat
  upperFace : CorridorFace
deriving Repr

def corridorBinReport (lower upper : Nat) : CorridorBinReport :=
  { lower := lower
    upper := upper
    total := if upper < lower then 0 else upper - lower + 1
    chargeCount := countBetween chargeTurnsUpTo lower upper
    massCount := countBetween massTurnsUpTo lower upper
    valueCount := countBetween valueTurnsUpTo lower upper
    upperReducedTurns := corridorReducedTurns upper
    upperFace := CorridorFace.ofTurns upper }

def CorridorFace.isMotionSlip : CorridorFace -> Bool
  | .mass => true
  | .charge => false
  | .value => false

def intMagnitude : Int -> Nat
  | .ofNat n => n
  | .negSucc n => n + 1

structure WheelStimulusRead where
  label : String
  signedValue : Int
  magnitude : Nat
  tripletIndex : Nat
  valueForCharge : Nat
  valueForMass : Nat
  reducedTurns : Nat
  face : CorridorFace
  motionSlip : Bool
deriving Repr

def wheelStimulusRead (label : String) (value : Int) : WheelStimulusRead :=
  let magnitude := intMagnitude value
  let reducedTurns := corridorReducedTurns magnitude
  let face := CorridorFace.ofReducedTurns reducedTurns
  { label := label
    signedValue := value
    magnitude := magnitude
    tripletIndex := corridorTripletIndex magnitude
    valueForCharge := valueForChargeTriplet magnitude
    valueForMass := valueForMassTriplet magnitude
    reducedTurns := reducedTurns
    face := face
    motionSlip := face.isMotionSlip }

structure BuildGravitySlipReport where
  dial : CorridorBinReport
  electronBoxValue : Nat
  gravityFace : CorridorFace
  dialExtraIsMotion : Bool
  buildStimuli : List WheelStimulusRead
  frictionReads : List WheelStimulusRead
deriving Repr

def buildGravitySlipReport (lower upper : Nat) : BuildGravitySlipReport :=
  let dial := corridorBinReport lower upper
  { dial := dial
    electronBoxValue := electronBox.val
    gravityFace := .mass
    dialExtraIsMotion := dial.upperFace.isMotionSlip
    buildStimuli :=
      [ wheelStimulusRead "theHeartRate" (Int.ofNat theHeartRate),
        wheelStimulusRead "g0_r2" (Int.ofNat g0_r2),
        wheelStimulusRead "predictedHeartRate" predictedHeartRate,
        wheelStimulusRead "targetB2" targetB2,
        wheelStimulusRead "targetDriver" targetDriver,
        wheelStimulusRead "targetDriverDef" targetDriverDef ]
    frictionReads :=
      [ wheelStimulusRead "bindingEnergyB2" elabBindingEnergyB2,
        wheelStimulusRead "bindingEnergyDriver" elabBindingEnergyDriver,
        wheelStimulusRead "bindingEnergyDriverDef" elabBindingEnergyDriverDef ] }

#eval rotatedDriverCorridor 12
#eval corridorBinReport 1 1000000
#eval buildGravitySlipReport 1 1000000

end Measurement
