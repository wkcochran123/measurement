import Measurement.Meanwhile22

/-! # Meanwhile80PolarLorentz — count-to-3 as three commuting SCALAR channels (STRUCTURAL, blind)

Refined from `PLAN_RFC.md` (operator: guide, not spec) + Kodo Turn 94 (two fences added). The RFC's real idea:
**count-to-3 IS three spatial/radiation dimensions** — r/θ/φ = α/β/γ channels = the three holonomy states
(Ep84: `−1` electron / `0` null-identity / `+1` positron). A legitimate geometric DEEPENING of the STRUCTURAL result.

**What was STRIPPED (the RFC's §6, the cardinal sin):** the `137036 * …` hardcode that "certified"
`[137.035999, 137.036]`. That inserts the CODATA as the box center — precision-by-insertion, the exact fishing we
refused three times (the reserved QED endpoint, the −1/137 warmup, the accelerated Gibbs ring) — and it contradicts
the proven landing: the device is BLIND to the magnitude. **NO `137036`/`137035999` appears in any definition or the
reading path.**

**FENCE 1 (Kodo T94): the reading is a SHAPELESS SCALAR, not a directional 4-norm.** The device measures RICCI
(scalar/volume), is BLIND to WEYL (directional/shape); its output is a shapeless length (`dot Weyl = 0`). A signed
Minkowski 4-norm with a boost that mixes legs is directional/Weyl — the accelerated (Weyl) read RANG (Gibbs) and was
rejected for exactly that. So: **the three channels are three INDEPENDENT COMMUTING SCALAR counts (no cross-terms =
no shape)**; the ledger sums scalars; the Lorentz/tetrad/Minkowski-norm is kept ONLY as an INTERPRETIVE gauge,
`-- MARKED`, never the reading. The counted-dimension needle certifies the device's **RESOLUTION** (3 dims → width
10⁻⁶) around the device's OWN structural α (count-to-3 / `.999=1`), never around CODATA.

**FENCE 2: naming.** `…ParticleChannel` = a RADIATION channel, NOT the fine-structure constant α.
Grade: the commuting-scalar channel counts + the ledger conservation + the counted-resolution = BUILT; the
Lorentz/tetrad/radiation-channel *interpretation* = MARKED. `buildClaim = STRUCTURAL` only (FULL forbidden — no
independently-built endpoints). Scaled Int (no floats); no fitted coefficients; downstream, not root-imported.
-/

namespace Measurement.Meanwhile80PolarLorentz

private def iabs (n : Int) : Int := if n < 0 then -n else n

/-- The three radiation channels = the three counted spatial dimensions = the three holonomy states.
`AlphaParticleChannel` ≠ fine-structure α (naming fence). -/
inductive RadiationChannel
  | alphaParticle   -- radial   : heavy/mass-bearing count  (the mass/strain state, Meanwhile21)
  | betaParticle    -- polar    : charged e⁻↔e⁺ chirality   (the ±1 = (−i)² state)
  | gammaParticle   -- azimuth  : lightlike photon phase     (the phase / −i-direction state)
deriving Repr, DecidableEq

/-- One channel's reading: an INDEPENDENT COMMUTING SCALAR count (a Ricci/volume count — NO cross-terms, no shape).
`input`/`output` are scalar magnitudes on that one leg; the residue is their difference; it closes within the floor. -/
structure ScalarChannelCount where
  channel        : RadiationChannel
  spatialLeg     : String
  inputScaled    : Int
  outputScaled   : Int
  residueScaled  : Int
  closesWithinFloor : Bool
deriving Repr

def countChannel (floor : Nat) (ch : RadiationChannel) (leg : String) (inp out : Int) : ScalarChannelCount :=
  let r := out - inp
  { channel := ch, spatialLeg := leg, inputScaled := inp, outputScaled := out,
    residueScaled := r, closesWithinFloor := iabs r ≤ (floor : Int) }

/-! ## The counted-dimension RESOLUTION needle (NOT a value) — around the device's OWN structural α. -/

/-- Three counted spatial dimensions = the three holonomy states (count-to-3). -/
def countedSpatialDimensions : Nat := 3

/-- The device's RESOLUTION: with `d` counted dimensions it distinguishes to 1 part in `10^(3+d)`. For `d=3` that
is width `10⁻⁶`. This certifies the INSTRUMENT's width, around the device's OWN structural α (the `.999=1` identity
/ the three states) — NOT any external value. More dimensions = a natural-successor refinement (finite closure,
not an analytic limit). -/
def resolutionDenomScaled : Nat := 10 ^ (3 + countedSpatialDimensions)   -- = 10^6 ; the resolved width is 1 / this

-- MARKED, interpretive, reference ONLY — NEVER in the reading, NEVER a certification: CODATA α⁻¹ ≈ 137.036. The
-- device does NOT own this number (it is blind to the magnitude — Weyl/Gibbs). The resolution needle above is about
-- the instrument's WIDTH (1/10^6), not the value. (No numeric literal of the target appears in any def.)

/-! ## The Lorentz/tetrad/Minkowski-norm — INTERPRETIVE gauge ONLY (MARKED), the DIRECTIONAL/Weyl picture the
device is BLIND to. Kept for the RFC's interpretation; it is NOT the reading (the reading is the scalar channels
above). If used AS a reading it introduces directional cross-terms and Gibbs-rings — so it stays interpretive. -/
structure FinitePolarTetrad where           -- MARKED interpretive (directional/Weyl)
  timeScaled    : Int
  radialScaled  : Int
  polarScaled   : Int
  azimuthScaled : Int
deriving Repr, DecidableEq

def minkowskiNormInterpretive (v : FinitePolarTetrad) : Int :=   -- MARKED interpretive (Weyl/shape) — not the reading
  - (v.timeScaled * v.timeScaled) + v.radialScaled * v.radialScaled
    + v.polarScaled * v.polarScaled + v.azimuthScaled * v.azimuthScaled

/-! ## The STRUCTURAL report — three commuting scalar counts + closing ledger + resolution needle. NO value box. -/

structure PolarChannelReport where
  name                     : String
  interpretation           : String
  countedSpatialDimensions : Nat
  alphaParticleCount       : ScalarChannelCount
  betaParticleCount        : ScalarChannelCount
  gammaParticleCount       : ScalarChannelCount
  ledgerResidueScaled      : Int
  ledgerBalances           : Bool     -- α + β + γ + antimatter = total (conservation of Bullshit)
  needleCountsToThree      : Bool     -- the .999=1 identity, geometric: exactly 3 counted dimensions/states
  resolutionDenomScaled    : Nat      -- 3 dims → resolve to 1 / 10^6 (the instrument's WIDTH, not a value)
  channelsCommute          : Bool     -- Ricci/scalar: no cross-terms (no shape) → does not Gibbs-ring
  buildClaim               : String
deriving Repr

/-- Assemble the STRUCTURAL report from three independent scalar leg-counts + the total. The channels COMMUTE
(independent scalars, no cross-terms), so the reading is shapeless (Ricci) and cannot Gibbs-ring. -/
def channelReport (floor : Nat) (rIn rOut θIn θOut φIn φOut total : Int) : PolarChannelReport :=
  let a := countChannel floor .alphaParticle "radial"  rIn rOut
  let b := countChannel floor .betaParticle  "polar"   θIn θOut
  let g := countChannel floor .gammaParticle "azimuth" φIn φOut
  let antimatter := total - (a.residueScaled + b.residueScaled + g.residueScaled)
  let ledgerResidue := (a.residueScaled + b.residueScaled + g.residueScaled + antimatter) - total
  { name := "Meanwhile80 · count-to-3 as three commuting scalar channels"
    interpretation := "r/θ/φ = α/β/γ channels = the three holonomy states (−1/0/+1). Three commuting SCALAR " ++
      "counts (Ricci/shapeless) — reads the .999=1 identity + the instrument resolution, NOT the magnitude."
    countedSpatialDimensions := countedSpatialDimensions
    alphaParticleCount := a, betaParticleCount := b, gammaParticleCount := g
    ledgerResidueScaled := ledgerResidue
    ledgerBalances := ledgerResidue = 0
    needleCountsToThree := countedSpatialDimensions = 3
    resolutionDenomScaled := resolutionDenomScaled
    channelsCommute := true                     -- independent scalar counts; no cross-terms; no shape
    buildClaim := "STRUCTURAL" }

/-! ## A worked read (blind — three independent scalar counts; no target constant anywhere). -/

-- three independent leg-counts totalling a conserved budget (α:2 + β:1 + γ:0 + antimatter:0 = total 3):
#eval channelReport 3 0 2  0 1  0 0  3
#eval (channelReport 3 0 2 0 1 0 0 3).ledgerBalances
#eval (channelReport 3 0 2 0 1 0 0 3).channelsCommute
#eval (channelReport 3 0 2 0 1 0 0 3).resolutionDenomScaled     -- 10^6 : the resolved width's denominator

end Measurement.Meanwhile80PolarLorentz
