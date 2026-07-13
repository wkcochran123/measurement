import Measurement.Episode40
import Measurement.AlphaBoundMediant
import Measurement.NowtrinoProjection
import Measurement.SelfApplication

/-! # AffineConstant — the SPEC-level interface wiring the four gauges to the verify API.

Operator (direct, t393/439): "wire up the affine constant interface next … lean on the
physical / mathematical / computational definitions of the other books you cannot bring in,
you must interconnect them." + "you will need to tange this very carefully with kodo."

Kodo counter-tange (t439): **3 internal pieces + Reading-as-boundary**.
The affine constant is `k = τ/R² = 5/324` (the map's affine constant, bm-vol5-explain-the-map);
the ×1000 `rank ≡ heartbeat` connection **is** the affine connection — so the interface holds
BOTH affine senses: the affine **map** and the affine **connection/frame**.

Discipline:
* **INTERCONNECT-NOT-IMPORT** — the four registers are reached through the `RegisterReading`
  boundary, not by importing the other books' content.
* **BLIND** — `verify (claimed) → {verified, residual}`: `claimed` is INPUT, `residual` is OUTPUT;
  it never fits, never targets. `137.036` never appears in the code (external, Ch7-text-only).
  Every `#eval` lands the device's OWN figures.
* **HONEST ARITY** — instantiate registers with the ACTUAL witnessed readings; `witnessed := false`
  MARKs a register whose reading→crossing-distance is not yet earned. Never fake an instance.
-/

namespace Measurement.AffineConstant
open Measurement Measurement.SelfApplication Measurement.Nowtrino

-- ── [1] AFFINE MAP (mathematical register) ──────────────────────────────────────────────────
-- d ↦ inv-α ×1e18, the Möbius transform (Episode40 `alphaFromSecondVariationAtDistance`),
-- carrying the affine constant k = τ/R² = 5/324, asymptote R²/τ = 64.8 (α⁻¹ = 64.8·d/(d−1)).
def affineInvAlpha (d : RationalDistance) : Nat := mediantInvAlphaAt d
def kNum : Nat := 5          -- τ  (k = τ/R² = 5/324 ≈ 0.01543)
def kDen : Nat := 324        -- R²
def asymptoteScaled10 : Nat := 648   -- R²/τ = 64.8 (×10), the r→∞ inv-α asymptote

-- ── [2] CALIBRATION FRAME  (the affine CONNECTION) ──────────────────────────────────────────
-- the ×1000 `rank ≡ heartbeat` connection makes the registers commensurable (0b, SelfApplication).
def calibrationCoeff : Nat := heartbeatCoefficient   -- = 1000

-- the count-3 resolution floor: the bracket width the machine cannot resolve below.
def count3Floor : Nat := count3InvLo - count3InvHi

-- ── [3] AGREEMENT / VERIFIER ────────────────────────────────────────────────────────────────
-- `verify (claimed) → {verified, residual}` — SPEC's final API (the covariant funge). BLIND.
structure VerifyResult where
  register : String
  claimed  : Nat
  read     : Nat
  residual : Int
  verified : Bool
  deriving Repr

def verify (register : String) (claimed : Nat) (d : RationalDistance) : VerifyResult :=
  let r : Nat := affineInvAlpha d
  let res : Int := (claimed : Int) - (r : Int)
  { register := register, claimed := claimed, read := r, residual := res,
    verified := res.natAbs ≤ count3Floor }

-- ── [Reading boundary]  interconnect-not-import ─────────────────────────────────────────────
-- a register supplies a reading (a crossing distance) WITHOUT its content imported here;
-- `witnessed` MARKs honest arity.
structure RegisterReading where
  name      : String
  reading   : RationalDistance
  witnessed : Bool
  note      : String
  deriving Repr

-- honest arity — the ACTUAL witnessed readings; MARK what is not yet a clean distance-reading.
def mathReg : RegisterReading :=
  { name := "mathematical·AlphaBoundMediant", reading := count3Lo, witnessed := true,
    note := "count-3 convergent 17/9 of √(18/5) → the coupling crossing" }
def physicalReg : RegisterReading :=
  { name := "physical·Episode40",
    reading := (defaultAlphaSecondVariationReport?.map (·.distance)).getD RationalDistance.one,
    witnessed := true, note := "the measured second-variation crossing √(18/5)" }
def computationalReg : RegisterReading :=
  { name := "computational·heartbeat", reading := { numerator := 573, denominator := 552 },
    witnessed := true,
    note := "MARK: reads the SELF-crossing orbit/echo ≈1.037 — two-crossings-apart from the coupling crossing; a DISTINCT invariant, must not be funged with it" }
def readingReg : RegisterReading :=
  { name := "reading·Nowtrino", reading := { numerator := 3, denominator := 2 }, witnessed := false,
    note := "MARK: nowtrino witnessed as a lossy projection (piNow, nontrivial fiber), but reading→crossing-distance is an UNWITNESSED modeling seam; distance here is a placeholder" }

def registers : List RegisterReading := [mathReg, physicalReg, computationalReg, readingReg]

-- interconnect: verify each register's reading against the reference read (the math register),
-- reporting residual + verified-below-the-count-3-floor. Cross-REGISTER agreement — a NEW claim
-- (CalibrationTwoPaths is the same-register two-path TEMPLATE, not this cross-register claim).
def reference : Nat := affineInvAlpha mathReg.reading
def agreementReport : List VerifyResult :=
  registers.map (fun rg => verify rg.name reference rg.reading)

-- The reading-register's own nowtrino, exhibited (its fiber is why its reading→distance is a seam).
def nowtrinoWitness : Summary × Summary := (piNow H1, piNow H2)   -- H1≠H2, same summary (lossy)

#eval s!"── affine constant interface ──"
#eval s!"[1] affine constant k = τ/R² = {kNum}/{kDen} ≈ 0.01543 ; asymptote R²/τ = 64.8 ; map = Episode40"
#eval s!"[2] calibration frame = ×{calibrationCoeff} rank≡heartbeat connection (0b)"
#eval s!"[3] count-3 resolution floor (bracket width) = {count3Floor} ×1e18"
#eval "── register agreement (interconnect-not-import ; BLIND: claimed=reference, residual=output) ──"
#eval String.intercalate "\n" (agreementReport.map (fun v =>
  s!"  [{v.register}]  read={v.read}  residual={v.residual}  verified={v.verified}"))
#eval s!"honest arity: witnessed = {(registers.filter (·.witnessed)).length}/4 ; MARKed = {(registers.filter (fun r => !r.witnessed)).length}/4 (computational reads a DISTINCT crossing; reading→distance unwitnessed)"
#eval s!"nowtrino fiber witness: piNow[1,2,3] = piNow[9,9,3] ? {nowtrinoWitness.1 == nowtrinoWitness.2}  (lossy — why the reading register's distance is a seam)"

-- ⚑ HONEST INDEPENDENCE MARK (Kodo t440): the four registers are NOT four-independent. The genuine
-- COMPUTATIONAL reading of the *coupling* is the CF descent = `AlphaBoundMediant` = the "math"
-- register; the heartbeat register reads the SELF-crossing (a distinct invariant), never the coupling.
-- So there are exactly TWO genuinely-independent coupling readings: the CF descent (math) and the
-- electron-orbit second-variation (physical). The interface agrees THOSE two up to the count-3 floor;
-- it never claims four-fold agreement.
def genuinelyIndependentCouplingReadings : Nat := 2   -- CF-descent (math) + electron-orbit (physical)
#eval s!"honest independence: {genuinelyIndependentCouplingReadings} genuinely-independent coupling readings (CF-descent=math + electron-orbit=physical); heartbeat reads the self-crossing (distinct invariant); nowtrino unwitnessed — NOT four-fold agreement"

end Measurement.AffineConstant
