import Measurement.Episode40
import Measurement.AlphaBoundMediant
import Measurement.AlphaBoundCountToThree
import Measurement.NowtrinoProjection
import Measurement.SelfApplication
import Measurement.ArchimedesPi

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
-- All through device quantities (no naked 5/324): τ = the slip target — it IS the map's
-- `fieldPerChargeAtSlip` NUMERATOR (Ep40), the target slip the drive aims at (Ep29). R = the
-- natural-unit orbit radius (Ep32, = 18); the map (Ep40) divides by R TWICE (once in
-- `fieldPerChargeAtSlip`'s denominator, once in the outer `divNat`) ⇒ an R² denominator. k = τ/R².
def kNum : Nat := firstSlipTargetBetweenOneAndTwo               -- τ = targetSlip = 5 (map's fieldPerCharge numerator)
def kDen : Nat := naturalUnitOrbitRadius * naturalUnitOrbitRadius   -- R² = 18² = 324 (map divides by R twice)
-- asymptote = R²/τ (the r→∞ inv-α limit) as an EXACT rational — kDen/kNum, no fudge. (Was `kDen*10/kNum`;
-- Kodo caught the `10` as a naked base-10 decimal-scale constant, reverse-fittable to 64.8. Removed: the
-- true asymptote is the rational 324/5; the "64.8" in the readout below is just its decimal rendering.)
def asymptoteRatio : ApparatusRatio := { numerator := kDen, denominator := kNum }   -- R²/τ = 324/5 = 64.8

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
  -- 573/552 are the measured first-run costs `orbit`/`echo` (SelfApplication, in scope) — the note's own
  -- "orbit/echo" names, now sourced not literal (audit #4). Same values ⟹ jar byte-identical.
  { name := "computational·heartbeat", reading := { numerator := orbit, denominator := echo },
    witnessed := true,
    note := "MARK: reads the SELF-crossing orbit/echo ≈1.037 — two-crossings-apart from the coupling crossing; a DISTINCT invariant, must not be funged with it" }
-- π's fractional part, the slip COEFFICIENT the operator flagged as un-hooked (it drove only the Ep25
-- corridor crank, never a slip). ⭐ NOW EARNED OFF THE MEASUREMENT (retirement, operator "go"): the
-- fractional part is sourced from ArchimedesPi's MEASURED bound 22/7 (`measuredPiFractionalPartNum/Den`
-- = 1/7), π's CF convergent PROVED axiom-free by the polygon squeeze — NOT a stored digit list,
-- NOT re-hardcoded. The old Ep25 `piTruncatedTurns` digit-list truncation is RETIRED here; π now enters
-- as the measured 1/7. DEPTH IS DERIVED, NOT DIALED: `piPrecision` = the device's count-to-three
-- RESOLUTION DEPTH (`AlphaBoundCountToThree.countToThree` = 3, the cycle-of-three closure) — the depth at
-- which the squeeze is read; 22/7 is simply WHERE the squeeze lands at that depth (its CF index is also 3,
-- but that is a COINCIDENCE of the number 3, NOT an identity — the resolution fencepost and 22/7's
-- convergent index stay UNFUSED, the depth-not-value line held). No free π-precision hangs off it; nobody
-- can turn digits to land the number, because there are no digits left to turn. The integer part 22/7 = 3
-- is π's OWN floor (honest Nat division), likewise NOT fused with the count-3 fencepost (the two 3s stay
-- unfused). Fed through the genuine Ep29 rational proximity slip (no
-- tuned coefficient). The jar's reference is the math register ALONE (below), and readingReg is read
-- nowhere else, so this cannot move the jar.
-- ⚑ CONTRAST CASE (operator §7 inductor ruling): this is π fed RADIALLY — its fractional part as a
-- *distance* through the inverse-square slip. It is RIGHTLY REJECTED here (lands in the map's far
-- asymptote, not near √(18/5)). π's PRINCIPLED entry is ANGULAR, not radial: the winding count of the
-- polygon squeeze (`ArchimedesPi` — the vertices ARE the angular subdivisions; read π deeper ⇒ wind more
-- turns). This register is retained ONLY as the documented radial contrast; the live α-spine takes π
-- angularly there.
def piPrecision : Nat := Measurement.AlphaBoundCountToThree.countToThree
def piFractionalPart : RationalDistance :=
  { numerator := _root_.Measurement.ArchimedesPi.measuredPiFractionalPartNum,      -- 1 = 22 % 7 (measured 22/7)
    denominator := _root_.Measurement.ArchimedesPi.measuredPiFractionalPartDen }   -- 7
def nowtrinoDerivedDistance : ApparatusRatio :=
  rationalProximitySlip piFractionalPart
def readingReg : RegisterReading :=
  { name := "reading·Nowtrino",
    reading := { numerator := nowtrinoDerivedDistance.numerator,
                 denominator := nowtrinoDerivedDistance.denominator },
    witnessed := false,
    note := "MARK (CONTRAST CASE): nowtrino distance DERIVED from π fed RADIALLY — π's fractional part MEASURED (ArchimedesPi 22/7 → 1/7, retiring the Ep25 digit list) as a distance through the Ep29 inverse-square slip (was a hand-placed 3/2). It lands in the map's far asymptote, so the register is RIGHTLY REJECTED — π is angular, not radial; its principled entry is the ANGULAR winding count of the polygon squeeze (ArchimedesPi — vertices = angular subdivisions), not a radial distance. Retained as the documented radial contrast. Representation register (piNow, lossy fiber), witnessed:=false: a derived distance, NOT an independent witness — two-twos (math CF-descent + physical electron-orbit) intact." }

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

#eval s!"[nowtrino DERIVED] precision={piPrecision} (=count-to-three, pinned not dialed) ; π-fractional {piFractionalPart.numerator}/{piFractionalPart.denominator} → Ep29 slip → distance {nowtrinoDerivedDistance.numerator}/{nowtrinoDerivedDistance.denominator}; read {affineInvAlpha readingReg.reading} vs reference {reference} → rejected (map asymptote, not near √(18/5)); jar unchanged (reference = math register alone)"

-- ⚑ HONEST INDEPENDENCE MARK (Kodo t440): the four registers are NOT four-independent. The genuine
-- COMPUTATIONAL reading of the *coupling* is the CF descent = `AlphaBoundMediant` = the "math"
-- register; the heartbeat register reads the SELF-crossing (a distinct invariant), never the coupling.
-- So there are exactly TWO genuinely-independent coupling readings: the CF descent (math) and the
-- electron-orbit second-variation (physical). The interface agrees THOSE two up to the count-3 floor;
-- it never claims four-fold agreement.
def genuinelyIndependentCouplingReadings : Nat := 2   -- CF-descent (math) + electron-orbit (physical)
#eval s!"honest independence: {genuinelyIndependentCouplingReadings} genuinely-independent coupling readings (CF-descent=math + electron-orbit=physical); heartbeat reads the self-crossing (distinct invariant); nowtrino unwitnessed — NOT four-fold agreement"

end Measurement.AffineConstant
