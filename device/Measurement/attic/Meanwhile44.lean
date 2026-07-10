import Measurement.Meanwhile43
import Measurement.CooperManual

/- MEANWHILE 44 -- THE DECIDER SELECTS A NEIGHBORHOOD. The adjacent wobble
bracket is the real aperture. Inside that aperture the apparatus does not pick
a real number directly; it picks a rational neighborhood, and the face selected
by the PRNG decides which moments interpret the same aperture.

There are three measurement neighborhoods:

  * charge
  * mass
  * value

Each neighborhood carries its own mean and variance. The PRNG draw is part of
the apparatus state, so Lean still evaluates a deterministic receipt.
-/

namespace Measurement

def valueTripletValueSum (lower upper : Nat) : Nat :=
  let count := countBetween valueTurnsUpTo lower upper
  let first := firstTurnWithFaceAtOrAbove .value lower
  sumArithmeticProgression first corridorPeriod count

def valueTripletSquareSum (lower upper : Nat) : Nat :=
  let count := countBetween valueTurnsUpTo lower upper
  let first := firstTurnWithFaceAtOrAbove .value lower
  sumArithmeticSquares first corridorPeriod count

def valueTripletCubeSum (lower upper : Nat) : Nat :=
  let count := countBetween valueTurnsUpTo lower upper
  let first := firstTurnWithFaceAtOrAbove .value lower
  sumArithmeticCubes first corridorPeriod count

def valueSlipPointMoments (lower upper : Nat) : SlipPointMoments :=
  slipPointMoments
    (valueTripletValueSum lower upper)
    (valueTripletSquareSum lower upper)
    (valueTripletCubeSum lower upper)

def momentsForFace
    (read : ChargeMassNormalizationReport) :
    CorridorFace -> SlipPointMoments
  | .charge => read.charge
  | .mass => read.mass
  | .value => valueSlipPointMoments read.lower read.upper

structure RationalNeighborhood where
  face : CorridorFace
  bracketLower : ApparatusRatio
  bracketUpper : ApparatusRatio
  bracketWidthScaledAt18 : Nat
  momentWeight : Nat
  mean : ApparatusRatio
  meanScaledAt18 : Nat
  variance : ApparatusRatio
  varianceScaledAt18 : Nat
deriving Repr

def rationalNeighborhood
    (aperture : AdjacentWobbleReport)
    (read : ChargeMassNormalizationReport)
    (face : CorridorFace) : RationalNeighborhood :=
  let moments := momentsForFace read face
  { face := face
    bracketLower := aperture.lowerWobble
    bracketUpper := aperture.upperWobble
    bracketWidthScaledAt18 := aperture.adjacentWidthScaledAt18
    momentWeight := moments.accumulatedSlipPoint
    mean := moments.estimatedSlipPoint
    meanScaledAt18 := moments.estimatedSlipPointScaledAt18
    variance := moments.variance
    varianceScaledAt18 := moments.varianceScaledAt18 }

def rationalNeighborhoods
    (aperture : AdjacentWobbleReport)
    (read : ChargeMassNormalizationReport) : List RationalNeighborhood :=
  [ rationalNeighborhood aperture read .charge,
    rationalNeighborhood aperture read .mass,
    rationalNeighborhood aperture read .value ]

def chooseNeighborhoodFace (seed : Nat) : CorridorFace × Nat :=
  let seed' := CooperManual.nextSeed seed
  match seed' % 3 with
  | 0 => (.charge, seed')
  | 1 => (.mass, seed')
  | _ => (.value, seed')

def selectedNeighborhood
    (aperture : AdjacentWobbleReport)
    (read : ChargeMassNormalizationReport)
    (face : CorridorFace) : RationalNeighborhood :=
  rationalNeighborhood aperture read face

structure NeighborhoodDeciderReport where
  seedIn : Nat
  seedOut : Nat
  drawModuloThree : Nat
  selectedFace : CorridorFace
  apertureLower : ApparatusRatio
  apertureUpper : ApparatusRatio
  apertureWidthScaledAt18 : Nat
  neighborhoods : List RationalNeighborhood
  neighborhoodCount : Nat
  selected : RationalNeighborhood
deriving Repr

def neighborhoodDeciderReport
    (seed : Nat)
    (aperture : AdjacentWobbleReport)
    (read : ChargeMassNormalizationReport) : NeighborhoodDeciderReport :=
  let draw := chooseNeighborhoodFace seed
  let face := draw.1
  let seed' := draw.2
  let neighborhoods := rationalNeighborhoods aperture read
  { seedIn := seed
    seedOut := seed'
    drawModuloThree := seed' % 3
    selectedFace := face
    apertureLower := aperture.lowerWobble
    apertureUpper := aperture.upperWobble
    apertureWidthScaledAt18 := aperture.adjacentWidthScaledAt18
    neighborhoods := neighborhoods
    neighborhoodCount := neighborhoods.length
    selected := selectedNeighborhood aperture read face }

def defaultNeighborhoodDeciderReport? :
    Option NeighborhoodDeciderReport :=
  defaultAdjacentWobbleReport?.map fun aperture =>
    neighborhoodDeciderReport CooperManual.initialSeed aperture
      cavendishChargeMassNormalization

theorem rationalNeighborhoods_has_three
    (aperture : AdjacentWobbleReport)
    (read : ChargeMassNormalizationReport) :
    (rationalNeighborhoods aperture read).length = 3 := by
  rfl

#eval defaultNeighborhoodDeciderReport?

end Measurement
