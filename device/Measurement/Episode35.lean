import Measurement.Episode34

/- MEANWHILE 35 -- GRID THE SLIP, THEN BISECT IT. Episode29 already knew that
the proximity slip boundary lived between 1 and 2. Here the apparatus is not
allowed to assume that. It grids the whole normalized interval [0, 2], finds the
cell where the target slip disappears, and then bisects that cell exactly.

The zero endpoint is contact for the inverse-square law, so it is treated as
already over the target without evaluating the singular rational slip there.
-/

/-! # Meanwhile 35 — the gridded slip: a bracket that closes, but only computed  (▦ quilter's patchwork)

**The genre skin (▦).** Lay the bolt of cloth out flat and rule it into a grid of patches; find the one
patch the seam runs into and does not run out of; then, inside that patch alone, halve and halve until the
seam is pinned. A quilt pieced, then one patch worked fine.

**Object & facet.** This is the gridded-slip facet of the object Yang–Mills describes — the same first slip
as Ep29, but this time without assuming which stretch of cloth it hides in. We describe the facet in the
device's own exact terms; we never open or solve Yang–Mills, and the last box stays wrapped.

**The squeeze — computed, NOT proved.** The mechanism is a grid over `[0, 2]` and then a dyadic bisection:
each halving doubles the denominator, so every bound stays an exact dyadic fraction, and the interval closes
on the seam. Each halving is one tick of the squeeze. But say the plain truth up front, as in Ep25: there is
NO theorem in this file, only a single `#eval`. Nothing here is proved and no receipt is claimed — the quilt
is laid out and READ, never certified by a theorem. The seam is located by halving, computed and read off.
-/

namespace Measurement

namespace RationalDistance

/-- `RationalDistance.zero : RationalDistance` — the distance `0/1`, the raw edge of the cloth (singular for
the inverse-square slip). -/
def zero : RationalDistance :=
  { numerator := 0, denominator := 1 }

/-- `RationalDistance.gridPoint (cells) (index) : RationalDistance` — the `index`-th grid line over `[0, 2]`
ruled into `cells` strips: `2 * index / cells` (the raw edge `zero` when `cells = 0`). -/
def gridPoint (cells index : Nat) : RationalDistance :=
  if cells = 0 then
    zero
  else
    { numerator := 2 * index, denominator := cells }

end RationalDistance

/-- `RationalDistance.isZero (distance) : Bool` — whether the distance is the raw edge,
`decide (distance.numerator = 0)`. -/
def RationalDistance.isZero (distance : RationalDistance) : Bool :=
  decide (distance.numerator = 0)

/-- `rationalSlipCrossesWithContact (targetSlip) (distance) : Bool` — whether the slip has crossed the
target at a grid line, with the raw edge counted as already crossed (contact). -/
def rationalSlipCrossesWithContact
    (targetSlip : Nat) (distance : RationalDistance) : Bool :=
  if distance.isZero then
    true
  else
    rationalSlipCrosses targetSlip distance

/-- `rationalSlipFloor? (distance) : Option Nat` — the slip floor at an edge, or `none` at the singular raw
edge where there is nothing to read. -/
def rationalSlipFloor? (distance : RationalDistance) : Option Nat :=
  if distance.isZero then none else some (rationalSlipFloor distance)

/-- `rationalSlipScaledAt18? (distance) : Option Nat` — the scaled slip at an edge, or `none` at the raw
edge. -/
def rationalSlipScaledAt18? (distance : RationalDistance) : Option Nat :=
  if distance.isZero then none else some (rationalSlipScaledAt18 distance)

/-- `rationalSlipFace? (distance) : Option CorridorFace` — the slip face at an edge, or `none` at the raw
edge. -/
def rationalSlipFace? (distance : RationalDistance) : Option CorridorFace :=
  if distance.isZero then none else some (rationalSlipFace distance)

/-- `SlipGridCell` — one patch of the quilt: its two edges (scaled), whether the slip has crossed at each,
and the slip floor / scaled value / face at each (or `none` at the raw edge). -/
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

/-- `slipGridCell (targetSlip) (cells) (index) : SlipGridCell` — stitch one patch at `index`: its two grid
lines and their crossings, floors, and faces. -/
def slipGridCell (targetSlip cells index : Nat) : SlipGridCell :=
  let lower := RationalDistance.gridPoint cells index
  let upper := RationalDistance.gridPoint cells (index + 1)
  { index := index
    lowerDistance := lower
    upperDistance := upper
    lowerDistanceScaledAt18 := lower.scaledFloor (readoutScale)
    upperDistanceScaledAt18 := upper.scaledFloor (readoutScale)
    lowerCrosses := rationalSlipCrossesWithContact targetSlip lower
    upperCrosses := rationalSlipCrossesWithContact targetSlip upper
    lowerSlipFloor? := rationalSlipFloor? lower
    upperSlipFloor? := rationalSlipFloor? upper
    lowerSlipScaledAt18? := rationalSlipScaledAt18? lower
    upperSlipScaledAt18? := rationalSlipScaledAt18? upper
    lowerFace? := rationalSlipFace? lower
    upperFace? := rationalSlipFace? upper }

/-- `firstSlipGridCellAux (targetSlip) (cells) (fuel) (index)` — walk the patches from `index` and stop at
the first where the slip has crossed by the lower edge but NOT the upper — the patch the seam runs into and
does not run out of. `none` if fuel runs out. -/
def firstSlipGridCellAux
    (targetSlip cells : Nat) : Nat -> Nat -> Option SlipGridCell
  | 0, _index => none
  | fuel + 1, index =>
      let cell := slipGridCell targetSlip cells index
      if cell.lowerCrosses && !cell.upperCrosses then
        some cell
      else
        firstSlipGridCellAux targetSlip cells fuel (index + 1)

/-- `firstSlipGridCell (targetSlip) (cells) : Option SlipGridCell` — search the whole grid for the seam's
patch. -/
def firstSlipGridCell (targetSlip cells : Nat) : Option SlipGridCell :=
  firstSlipGridCellAux targetSlip cells cells 0

/-- `DyadicSlipBracket` — a dyadic bracket: two numerators over a shared denominator (which doubles each
bisection step, keeping every bound an exact dyadic fraction). -/
structure DyadicSlipBracket where
  lowerNumerator : Nat
  upperNumerator : Nat
  denominator : Nat
deriving Repr

namespace DyadicSlipBracket

/-- `DyadicSlipBracket.lowerDistance (bracket) : RationalDistance` — the bracket's lower end,
`lowerNumerator / denominator`. -/
def lowerDistance (bracket : DyadicSlipBracket) : RationalDistance :=
  { numerator := bracket.lowerNumerator, denominator := bracket.denominator }

/-- `DyadicSlipBracket.upperDistance (bracket) : RationalDistance` — the bracket's upper end,
`upperNumerator / denominator`. -/
def upperDistance (bracket : DyadicSlipBracket) : RationalDistance :=
  { numerator := bracket.upperNumerator, denominator := bracket.denominator }

/-- `DyadicSlipBracket.midpointDistance (bracket) : RationalDistance` — the midpoint, the sum of numerators
over twice the denominator. The probe of a dyadic bisection step. -/
def midpointDistance (bracket : DyadicSlipBracket) : RationalDistance :=
  { numerator := bracket.lowerNumerator + bracket.upperNumerator
    denominator := 2 * bracket.denominator }

end DyadicSlipBracket

/-- `dyadicSlipBracketFromGridCell (cell) : DyadicSlipBracket` — seed the dyadic bracket from the found
patch's two edges. -/
def dyadicSlipBracketFromGridCell (cell : SlipGridCell) : DyadicSlipBracket :=
  { lowerNumerator := cell.lowerDistance.numerator
    upperNumerator := cell.upperDistance.numerator
    denominator := cell.lowerDistance.denominator }

/-- `bisectDyadicSlipOnce (targetSlip) (bracket) : DyadicSlipBracket` — one dyadic bisection tick: probe the
midpoint (doubling the denominator), keep the half the seam fell in. Each call halves the interval —
computed, not certified. -/
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

/-- `bisectDyadicSlipAux (fuel) (targetSlip) (bracket)` — apply `bisectDyadicSlipOnce` `fuel` times, the
bracket closing tick by tick (still computed, no theorem beneath it). -/
def bisectDyadicSlipAux :
    Nat -> Nat -> DyadicSlipBracket -> DyadicSlipBracket
  | 0, _targetSlip, bracket => bracket
  | fuel + 1, targetSlip, bracket =>
      bisectDyadicSlipAux fuel targetSlip
        (bisectDyadicSlipOnce targetSlip bracket)

/-- `GridSlipBisectSummary` — the finished read: the target, grid size, rungs, the found patch, the
closed-in bracket scaled (lower, upper, midpoint, width), and each end's slip floor, scaled value, and
face. -/
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

/-- `gridSlipBisectSummary? (targetSlip) (gridCells) (rungs) : Option GridSlipBisectSummary` — the whole
job: grid to find the patch, bisect inside it `rungs` times, and summarize; `none` if no patch holds the
seam. -/
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
           lowerDistanceScaledAt18 := lowerDistance.scaledFloor (readoutScale)
           upperDistanceScaledAt18 := upperDistance.scaledFloor (readoutScale)
           midpointScaledAt18 := midpoint.scaledFloor (readoutScale)
           widthScaledAt18 :=
             upperDistance.scaledFloor (readoutScale) -
               lowerDistance.scaledFloor (readoutScale)
           lowerSlipFloor := rationalSlipFloor lowerDistance
           upperSlipFloor := rationalSlipFloor upperDistance
           lowerSlipScaledAt18 := rationalSlipScaledAt18 lowerDistance
           upperSlipScaledAt18 := rationalSlipScaledAt18 upperDistance
           lowerFace := rationalSlipFace lowerDistance
           upperFace := rationalSlipFace upperDistance } : GridSlipBisectSummary)

/-- `defaultGridSlipSummary? : Option GridSlipBisectSummary` — the standard run: target
`firstSlipTargetBetweenOneAndTwo`, 128 grid cells, 48 bisection rungs. -/
def defaultGridSlipSummary? : Option GridSlipBisectSummary :=
  gridSlipBisectSummary? firstSlipTargetBetweenOneAndTwo 128 48

/-! ## Readout — the one read (computed, not proved)
`#eval defaultGridSlipSummary?` runs it at target 5, a grid of 128 patches, 48 halvings, and prints the
finished square. And that is ALL: no theorem stands under it, so nothing here is proved and no receipt is
claimed — the quilt is computed and read, not certified. The next facet, G recovered via force, is next
door. -/
#eval defaultGridSlipSummary?

end Measurement
