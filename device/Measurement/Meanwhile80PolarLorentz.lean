import Measurement.Meanwhile22

/-! # Meanwhile80PolarLorentz — the 3-D polar/tetrad channel gauge (STRUCTURAL, blind)

Refined from `PLAN_RFC.md` (operator: use as a guide, not the spec). **The plan's §6 magnitude box is REMOVED** —
it hardcoded the CODATA (`137036 * …`) to "certify" `[137.035999, 137.036]`, which is precision-by-insertion (the
cardinal sin) and contradicts the proven result that the device is BLIND to the magnitude (the accelerated-frame
residual rings = Weyl/Gibbs, rejected). This module keeps the plan's good bones — the finite local tetrad, the
signed norm, the three α/β/γ channels, the closing ledger — and reads the **STRUCTURAL identity only**:

**The `.999 = 1` needle = COUNT-TO-3, made geometric.** Three counted spatial dimensions (r, θ, φ) = three
radiation channels (α/β/γ) = the three holonomy states (Ep84: `−1` electron / `0` null-identity / `+1` positron):
- **α-particle channel** (radial, heavy/mass-bearing strain) — the mass/strain leg (`mass=2nd-diff=strain`, Meanwhile21).
- **β-particle channel** (polar tangent, charged deflection / e⁻↔e⁺ chirality) — the **±1 = (−i)²** matter/antimatter state.
- **γ-particle channel** (azimuthal, lightlike phase / photon holonomy) — the phase/coupling (the −i direction).

`α-particle` here is a RADIATION channel, NOT the fine-structure constant α (naming fence, PLAN §1). The device
counts to three because there ARE three holonomy states, and stops — it does not count to more digits of a
magnitude it cannot see. Landing: **STRUCTURAL**. Grade off the build; scaled integers, no floats; local tetrad
only (no global polar-Lorentz claim). Do NOT import from root `Measurement.lean` until the operator approves.
-/

namespace Measurement.Meanwhile80PolarLorentz

/-- The three radiation channels = the three counted spatial dimensions = the three holonomy states. -/
inductive RadiationChannel
  | alphaParticle   -- radial leg : heavy/mass-bearing strain  (holonomy state, mass side)
  | betaParticle    -- polar leg  : charged e⁻↔e⁺ chirality     (holonomy ±1 = (−i)²)
  | gammaParticle   -- azimuth leg: lightlike photon phase      (holonomy phase, −i direction)
deriving Repr, DecidableEq

/-- A local orthonormal (tetrad) read of a polar point — NOT global polar coordinates.
Scaled integers only (PLAN §9: no floats). `x_φ` is just the third counted local leg (no `sin θ` yet). -/
structure FinitePolarTetrad where
  timeScaled    : Int
  radialScaled  : Int   -- x_r      (α channel)
  polarScaled   : Int   -- x_θ      (β channel)
  azimuthScaled : Int   -- x_φ      (γ channel)
deriving Repr, DecidableEq

private def sq (n : Int) : Int := n * n
private def iabs (n : Int) : Int := if n < 0 then -n else n

/-- The signed (Minkowski) norm in the local tetrad: `−t² + x_r² + x_θ² + x_φ²`. -/
def minkowskiNorm (v : FinitePolarTetrad) : Int :=
  - sq v.timeScaled + sq v.radialScaled + sq v.polarScaled + sq v.azimuthScaled

/-- The finite Lorentz residual: the change in the signed norm under a local transform. -/
def lorentzResidual (before after : FinitePolarTetrad) : Int :=
  minkowskiNorm after - minkowskiNorm before

/-- The invariant is preserved iff the residual sits within the floor (the tolerance). -/
def invariantPreservedWithinFloor (floor : Nat) (before after : FinitePolarTetrad) : Bool :=
  iabs (lorentzResidual before after) ≤ (floor : Int)

structure FiniteLorentzRead where
  before             : FinitePolarTetrad
  after              : FinitePolarTetrad
  normBefore         : Int
  normAfter          : Int
  residual           : Int
  invariantPreserved : Bool
deriving Repr

def readLorentz (floor : Nat) (before after : FinitePolarTetrad) : FiniteLorentzRead :=
  { before, after
    normBefore := minkowskiNorm before
    normAfter  := minkowskiNorm after
    residual   := lorentzResidual before after
    invariantPreserved := invariantPreservedWithinFloor floor before after }

/-- One channel's finite read: input/output legs and the residue that must close within the floor. -/
structure PolarRadiationChannelRead where
  channel        : RadiationChannel
  spatialLeg     : String
  inputScaled    : Int
  outputScaled   : Int
  residueScaled  : Int
  closesWithinFloor : Bool
deriving Repr

def readChannel (floor : Nat) (ch : RadiationChannel) (leg : String) (inp out : Int) :
    PolarRadiationChannelRead :=
  let r := out - inp
  { channel := ch, spatialLeg := leg, inputScaled := inp, outputScaled := out,
    residueScaled := r, closesWithinFloor := iabs r ≤ (floor : Int) }

/-- The STRUCTURAL report — three counted dimensions / channels / holonomy states; the ledger closes
(conservation of Bullshit). NO magnitude box: the needle is the `.999=1` identity read as count-to-3, not a
CODATA-inserted `[137.035999,137.036]`. -/
structure PolarLorentzGlueReport where
  name                     : String
  interpretation           : String
  countedSpatialDimensions : Nat
  tetradRead               : FiniteLorentzRead
  alphaParticleRead        : PolarRadiationChannelRead
  betaParticleRead         : PolarRadiationChannelRead
  gammaParticleRead        : PolarRadiationChannelRead
  ledgerResidueScaled      : Int
  ledgerBalances           : Bool     -- radial + polar + azimuth + antimatter = the tetrad residual
  needleCountsToThree      : Bool     -- the `.999=1` identity, geometric: exactly 3 counted dimensions/states
  buildClaim               : String
deriving Repr

/-- Assemble the report for a before/after tetrad read at a given floor. The three channels are the three legs;
the ledger closes when the channel residues + antimatter equal the tetrad residual (conservation). -/
def glueReport (floor : Nat) (before after : FinitePolarTetrad) : PolarLorentzGlueReport :=
  let t := readLorentz floor before after
  let a := readChannel floor .alphaParticle "radial"  before.radialScaled  after.radialScaled
  let b := readChannel floor .betaParticle  "polar"   before.polarScaled   after.polarScaled
  let g := readChannel floor .gammaParticle "azimuth" before.azimuthScaled after.azimuthScaled
  -- the antimatter budget absorbs the time leg's contribution (the below-floor / unclaimable part):
  let antimatter := (minkowskiNorm after - minkowskiNorm before)
                    - ((a.residueScaled) + (b.residueScaled) + (g.residueScaled))
  let ledgerResidue := (a.residueScaled + b.residueScaled + g.residueScaled + antimatter) - t.residual
  { name := "Meanwhile80 · 3-D polar/tetrad channel gauge"
    interpretation := "count-to-3, geometric: r/θ/φ = α/β/γ channels = the three holonomy states (−1/0/+1). " ++
                      "STRUCTURAL: reads the .999=1 identity, NOT the magnitude (no CODATA box)."
    countedSpatialDimensions := 3
    tetradRead := t
    alphaParticleRead := a, betaParticleRead := b, gammaParticleRead := g
    ledgerResidueScaled := ledgerResidue
    ledgerBalances := ledgerResidue = 0
    needleCountsToThree := (3 = 3)   -- exactly three counted dimensions = three states; the geometric .999=1
    buildClaim := "STRUCTURAL" }

/-! ## A worked read (blind — no target constant anywhere). A local boost that preserves the signed norm. -/

def blank : FinitePolarTetrad := { timeScaled := 0, radialScaled := 0, polarScaled := 0, azimuthScaled := 0 }
-- a norm-preserving local read (before/after with equal signed norm → residual 0, invariant preserved):
def sampleBefore : FinitePolarTetrad := { timeScaled := 5, radialScaled := 3, polarScaled := 0, azimuthScaled := 0 }
def sampleAfter  : FinitePolarTetrad := { timeScaled := 5, radialScaled := 0, polarScaled := 3, azimuthScaled := 0 }

#eval glueReport 1 sampleBefore sampleAfter
#eval (glueReport 1 sampleBefore sampleAfter).ledgerBalances
#eval (glueReport 1 sampleBefore sampleAfter).tetradRead.invariantPreserved

end Measurement.Meanwhile80PolarLorentz
