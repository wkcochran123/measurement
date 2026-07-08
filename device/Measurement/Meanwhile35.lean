import Measurement.Meanwhile34

/- MEANWHILE 35 -- GRID THE SLIP, THEN BISECT IT. Meanwhile29 already knew that
the proximity slip boundary lived between 1 and 2. Here the apparatus is not
allowed to assume that. It grids the whole normalized interval [0, 2], finds the
cell where the target slip disappears, and then bisects that cell exactly.

The zero endpoint is contact for the inverse-square law, so it is treated as
already over the target without evaluating the singular rational slip there.
-/

namespace Measurement

namespace RationalDistance

def zero : RationalDistance :=
  { numerator := 0, denominator := 1 }

def gridPoint (cells index : Nat) : RationalDistance :=
  if cells = 0 then
    zero
  else
    { numerator := 2 * index, denominator := cells }

end RationalDistance

def RationalDistance.isZero (distance : RationalDistance) : Bool :=
  decide (distance.numerator = 0)

def rationalSlipCrossesWithContact
    (targetSlip : Nat) (distance : RationalDistance) : Bool :=
  if distance.isZero then
    true
  else
    rationalSlipCrosses targetSlip distance

def rationalSlipFloor? (distance : RationalDistance) : Option Nat :=
  if distance.isZero then none else some (rationalSlipFloor distance)

def rationalSlipScaledAt18? (distance : RationalDistance) : Option Nat :=
  if distance.isZero then none else some (rationalSlipScaledAt18 distance)

def rationalSlipFace? (distance : RationalDistance) : Option CorridorFace :=
  if distance.isZero then none else some (rationalSlipFace distance)

structure SlipGridCell where
  index : Nat
  lowerDistance : RationalDistance
  upperDistance : RationalDistance
  lowerDistanceScaledAt18 : Nat
  upperDistanceScaledAt18 : Nat
  lowerCrosses : Bool
  upperCrosses : Bool
  lowerSlipFloor? : Option Nat
  upperSlipFloor? : Option Nat
  lowerSlipScaledAt18? : Option Nat
  upperSlipScaledAt18? : Option Nat
  lowerFace? : Option CorridorFace
  upperFace? : Option CorridorFace
deriving Repr

def slipGridCell (targetSlip cells index : Nat) : SlipGridCell :=
  let lower := RationalDistance.gridPoint cells index
  let upper := RationalDistance.gridPoint cells (index + 1)
  { index := index
    lowerDistance := lower
    upperDistance := upper
    lowerDistanceScaledAt18 := lower.scaledFloor (pow10 18)
    upperDistanceScaledAt18 := upper.scaledFloor (pow10 18)
    lowerCrosses := rationalSlipCrossesWithContact targetSlip lower
    upperCrosses := rationalSlipCrossesWithContact targetSlip upper
    lowerSlipFloor? := rationalSlipFloor? lower
    upperSlipFloor? := rationalSlipFloor? upper
    lowerSlipScaledAt18? := rationalSlipScaledAt18? lower
    upperSlipScaledAt18? := rationalSlipScaledAt18? upper
    lowerFace? := rationalSlipFace? lower
    upperFace? := rationalSlipFace? upper }

def firstSlipGridCellAux
    (targetSlip cells : Nat) : Nat -> Nat -> Option SlipGridCell
  | 0, _index => none
  | fuel + 1, index =>
      let cell := slipGridCell targetSlip cells index
      if cell.lowerCrosses && !cell.upperCrosses then
        some cell
      else
        firstSlipGridCellAux targetSlip cells fuel (index + 1)

def firstSlipGridCell (targetSlip cells : Nat) : Option SlipGridCell :=
  firstSlipGridCellAux targetSlip cells cells 0

structure DyadicSlipBracket where
  lowerNumerator : Nat
  upperNumerator : Nat
  denominator : Nat
deriving Repr

namespace DyadicSlipBracket

def lowerDistance (bracket : DyadicSlipBracket) : RationalDistance :=
  { numerator := bracket.lowerNumerator, denominator := bracket.denominator }

def upperDistance (bracket : DyadicSlipBracket) : RationalDistance :=
  { numerator := bracket.upperNumerator, denominator := bracket.denominator }

def midpointDistance (bracket : DyadicSlipBracket) : RationalDistance :=
  { numerator := bracket.lowerNumerator + bracket.upperNumerator
    denominator := 2 * bracket.denominator }

end DyadicSlipBracket

def dyadicSlipBracketFromGridCell (cell : SlipGridCell) : DyadicSlipBracket :=
  { lowerNumerator := cell.lowerDistance.numerator
    upperNumerator := cell.upperDistance.numerator
    denominator := cell.lowerDistance.denominator }

def bisectDyadicSlipOnce
    (targetSlip : Nat) (bracket : DyadicSlipBracket) : DyadicSlipBracket :=
  let midpointNumerator := bracket.lowerNumerator + bracket.upperNumerator
  let nextDenominator := 2 * bracket.denominator
  let probe : RationalDistance :=
    { numerator := midpointNumerator, denominator := nextDenominator }
  if rationalSlipCrosses targetSlip probe then
    { lowerNumerator := midpointNumerator
      upperNumerator := 2 * bracket.upperNumerator
      denominator := nextDenominator }
  else
    { lowerNumerator := 2 * bracket.lowerNumerator
      upperNumerator := midpointNumerator
      denominator := nextDenominator }

def bisectDyadicSlipAux :
    Nat -> Nat -> DyadicSlipBracket -> DyadicSlipBracket
  | 0, _targetSlip, bracket => bracket
  | fuel + 1, targetSlip, bracket =>
      bisectDyadicSlipAux fuel targetSlip
        (bisectDyadicSlipOnce targetSlip bracket)

structure GridSlipBisectSummary where
  targetSlip : Nat
  gridCells : Nat
  rungs : Nat
  gridCell : SlipGridCell
  lowerDistanceScaledAt18 : Nat
  upperDistanceScaledAt18 : Nat
  midpointScaledAt18 : Nat
  widthScaledAt18 : Nat
  lowerSlipFloor : Nat
  upperSlipFloor : Nat
  lowerSlipScaledAt18 : Nat
  upperSlipScaledAt18 : Nat
  lowerFace : CorridorFace
  upperFace : CorridorFace
deriving Repr

def gridSlipBisectSummary?
    (targetSlip gridCells rungs : Nat) : Option GridSlipBisectSummary :=
  match firstSlipGridCell targetSlip gridCells with
  | none => none
  | some cell =>
      let bracket :=
        bisectDyadicSlipAux rungs targetSlip
          (dyadicSlipBracketFromGridCell cell)
      let lowerDistance := bracket.lowerDistance
      let upperDistance := bracket.upperDistance
      let midpoint := bracket.midpointDistance
      some
        ({ targetSlip := targetSlip
           gridCells := gridCells
           rungs := rungs
           gridCell := cell
           lowerDistanceScaledAt18 := lowerDistance.scaledFloor (pow10 18)
           upperDistanceScaledAt18 := upperDistance.scaledFloor (pow10 18)
           midpointScaledAt18 := midpoint.scaledFloor (pow10 18)
           widthScaledAt18 :=
             upperDistance.scaledFloor (pow10 18) -
               lowerDistance.scaledFloor (pow10 18)
           lowerSlipFloor := rationalSlipFloor lowerDistance
           upperSlipFloor := rationalSlipFloor upperDistance
           lowerSlipScaledAt18 := rationalSlipScaledAt18 lowerDistance
           upperSlipScaledAt18 := rationalSlipScaledAt18 upperDistance
           lowerFace := rationalSlipFace lowerDistance
           upperFace := rationalSlipFace upperDistance } : GridSlipBisectSummary)

def defaultGridSlipSummary? : Option GridSlipBisectSummary :=
  gridSlipBisectSummary? firstSlipTargetBetweenOneAndTwo 128 48

#eval defaultGridSlipSummary?

end Measurement
