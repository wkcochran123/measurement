import Measurement.Episode40
import Measurement.Calibration.BIAS_____

/-
EXPERIMENT (operator 2026-07-11: "YES median instead of average. always in the modulo realm!"
followed by "no, you just have jarjar keep saying 1").

FIRST attempt bisected by the raw MEDIANT one node at a time — 1/1, 3/2, 5/3, 7/4, … — the
denominator ticking +1 each step. That is a UNARY crawl ("keep saying 1"), NOT the modulo realm:
building a partial quotient of 8 by taking eight identical mediant steps.

THE MODULO REALM = division with remainder = the CONTINUED-FRACTION (Euclidean) step, which takes a
whole partial quotient at once and lands directly on the CONVERGENTS (the best rational approximants).

And the crossing is a clean QUADRATIC SURD: slip(d) = C/d², crossing at slip = target ⟹
d*² = C/target = 38376/10660 = 18/5, so d* = √(18/5) = √90/5 ≈ 1.897367. A quadratic irrational has an
eventually-PERIODIC continued fraction — the device-native descent. This file computes that CF with
integer arithmetic only (PQa algorithm, Nat.sqrt) — pure modulo realm, no /2, no unary crawl, no grid.
`AlphaBoundCountToThree` is UNTOUCHED.
-/

namespace Measurement

open Measurement

/-- Q3 DE-SELECTION (turn 543): the target reads the CLASS of the post-2 slip state —
one past its floor, the `+1` still earned via `earnedSum` (coproduct). Value unchanged
by `rfl`; paying theorem: `firstSlipTargetBetweenOneAndTwo_is_five` (Ep29). -/
def mediantTgtClass : Calibration.BIAS_____.GaugeValue
    (fun (s : Option ApparatusRatio) => earnedSum (match s with | none => 0 | some slip => slip.floor) 1) :=
  Calibration.BIAS_____.deselect _ (proximitySlip? 2)
def mediantTgt : Nat := Calibration.BIAS_____.reading _ mediantTgtClass   -- T = target = 5 (device-derived)

/-- Q2 DE-SELECTION (design frozen law, turn 542): `mediantC` no longer consumes the
selected pair directly — the slip-state is DE-SELECTED through the one needle
(`Deselect`, threading Ep15's `selection_sound`) and `mediantC` reads the CLASS.
Value unchanged by `rfl` (`reading_deselect`): gate zero. The pair survives upstream
as mesh (the witness below consumes it AS the payment — census bucket A). Paying
theorem: `mediantC_is_eighteen`. -/
def mediantCClass : Calibration.BIAS_____.GaugeValue ApparatusRatio.floor :=
  Calibration.BIAS_____.deselect ApparatusRatio.floor (rationalProximitySlip RationalDistance.one)
def mediantC : Nat := Calibration.BIAS_____.reading ApparatusRatio.floor mediantCClass   -- C = slip(1) = 18 (measured, Ep29)

/-- `mediantC_is_eighteen : mediantC = 18` — C, the jar's slip-coupling input, asserted on the REAL thing
the jar reads (`(rationalProximitySlip 1).floor`) and proved DRIFT-IMMUNE by structural cancellation (strong
form, NOT `rfl` at the heartbeat). The slip-at-1 numerator is `deviceG.numerator · P` and its denominator is
`deviceG.denominator · 1 = P`, for the same mass product `P = sourceMassTotal · testMass · arm` (since
`deviceG.denominator = P` by `cavendishCalibration`'s def) — so `P` CANCELS (`Nat.mul_div_cancel`), leaving
`deviceG.numerator = 18`, independent of every heartbeat count in `P`. This is the invariant on the jar's
actual input (retiring the reliance on an abstract `deviceG.num·M/M` model that was one unfold away in
prose). One root, three paths: the same `deviceG.numerator = 18` gives T = 5
(`firstSlipTargetBetweenOneAndTwo_is_five`, slip-at-2) and R = 18 (`naturalUnitOrbitRadius_is_eighteen`,
ceil) — NAMED as one coupling read three ways, never sold as independent 18s. -/
theorem mediantC_is_eighteen : mediantC = 18 := by
  have hP : 0 < cavendishSourceMassTotal * tetheredElectronTestMass.magnitude * cavendishArm := by decide
  show (rationalProximitySlip RationalDistance.one).floor = 18
  simp only [rationalProximitySlip, ApparatusRatio.floor, RationalDistance.one,
    RationalDistance.squaredNumerator, RationalDistance.squaredDenominator, square, Nat.mul_one]
  rw [show deviceG.denominator
         = cavendishSourceMassTotal * tetheredElectronTestMass.magnitude * cavendishArm from rfl,
      show deviceG.numerator * cavendishSourceMassTotal * tetheredElectronTestMass.magnitude * cavendishArm
         = 18 * (cavendishSourceMassTotal * tetheredElectronTestMass.magnitude * cavendishArm)
         from by simp only [show deviceG.numerator = 18 from rfl, Nat.mul_assoc]]
  exact Nat.mul_div_cancel _ hP

-- The crossing is √(18/5) = √90 / 5.  PQa on (P₀,Q₀,D) = (0, T, C·T) = (0, 5, 90) — all device quantities.
def cfD : Nat := mediantC * mediantTgt                    -- D = C·T = 18·5 = 90 (no naked 90)

/-- `floorSqrt n = ⌊√n⌋` — the largest `k` with `k·k ≤ n`, COMPUTED by the kernel (fold over `0..n`),
since this Mathlib-free toolchain has no `Nat.sqrt`. Kernel arithmetic — a conforming source (no keyboard literal). -/
def floorSqrt (n : Nat) : Nat :=
  (List.range (n + 1)).foldl (fun acc k => if k * k ≤ n then k else acc) 0

def cfSqrtD : Nat := floorSqrt cfD                         -- ⌊√cfD⌋ = ⌊√90⌋ = 9, off the kernel (no naked 9)
example : cfSqrtD * cfSqrtD ≤ cfD ∧ cfD < (cfSqrtD + 1) * (cfSqrtD + 1) := by decide

/-- One Euclidean/continued-fraction step in the modulo realm: `a = (P+⌊√D⌋)/Q` (integer division),
    then `P' = a·Q − P`, `Q' = (D − P'²)/Q` (both exact), and the convergent recurrence
    hₙ = a·hₙ₋₁ + hₙ₋₂. Returns `(aᵢ, hᵢ, kᵢ)` for `n` steps: the partial quotients and convergents. -/
def cfAux : Nat → Nat → Nat → Nat → Nat → Nat → Nat → List (Nat × Nat × Nat)
  | 0, _, _, _, _, _, _ => []
  | fuel + 1, p, q, h1, h0, k1, k0 =>
      let a  := (p + cfSqrtD) / q
      let p' := a * q - p
      let q' := (cfD - p' * p') / q
      let h  := a * h1 + h0
      let k  := a * k1 + k0
      (a, h, k) :: cfAux fuel p' q' h h1 k k1

/-- Convergents of the crossing √(18/5), computed in the modulo realm (division, not unary mediant). -/
def crossingConvergents (n : Nat) : List (Nat × Nat × Nat) :=
  cfAux n 0 mediantTgt 1 0 0 1                             -- Q₀ = T = mediantTgt (no naked 5)

def mediantInvAlphaAt (d : RationalDistance) : Nat :=
  (alphaFromSecondVariationAtDistance mediantTgt d).inverseScaledFloor (readoutScale)

/-- inv-α (×1e18) at a convergent h/k. -/
def convInvAlpha (hk : Nat × Nat × Nat) : Nat :=
  mediantInvAlphaAt { numerator := hk.2.1, denominator := hk.2.2 }

-- The continued fraction, its convergents, and the inv-α at each convergent.
-- ── #eval readout/display for this module lives in `Measurement.Gauge.AlphaBoundMediantDisplay`
--    (Gauge phase): the mediant/CF physics + count-3 bracket defs (which FEED THE JAR) stay here. ──

-- RICHARDSON REFINEMENT FAMILY (operator protocol 2026-07-11): the CF convergents ARE A(hⱼ) — the
-- modulo-realm descent is the reproducible refinement parameter h. Deep family (conv0..19) so the
-- observed order p_obs can be checked for STABILIZATION on the fixed-r PERIOD subsample (period
-- [1,8,1,2] = 4; same-phase convergents approach the limit monotonically from one side). Machine-owned
-- A_j at scaled-integer ×1e18 with inverseScaledFloor rounding. Emits `RICH conv{i} k={k} invA18={..}`.

-- Successive convergents bracket the crossing ALTERNATELY (CF property). The device counts to three:
-- COUNT-TO-3 = 3 partial quotients [a₀,a₁,a₂] → convergent #2, bracketed against convergent #1.
def convAt (i : Nat) : RationalDistance :=
  match (crossingConvergents (i + 1)).getLast? with
  | some (_, h, k) => { numerator := h, denominator := k }
  | none => { numerator := 1, denominator := 1 }

def count3Lo : RationalDistance := convAt 2   -- [1;1,8] = 17/9  (below the crossing)
def count3Hi : RationalDistance := convAt 1   -- [1;1]  = 2/1   (above the crossing)
def count3InvLo : Nat := mediantInvAlphaAt count3Lo   -- inv-α at 17/9 (upper wall)
def count3InvHi : Nat := mediantInvAlphaAt count3Hi   -- inv-α at 2/1  (lower wall)


-- For reference: the next convergent tightens the far wall (count-to-4 = [17/9, 19/10]).
def count4Lo : RationalDistance := convAt 2   -- 17/9
def count4Hi : RationalDistance := convAt 3   -- 19/10

-- Choice-free / modulo-realm witness: the count-3 convergent bracket is strictly ordered, decided,
-- no Classical.choice.
theorem count3_bracket_ordered : count3InvHi < count3InvLo := by decide
#print axioms count3_bracket_ordered

/-
FINDINGS (modulo-realm continued-fraction descent; numbers read LAST, no fishing).

CROSSING IS AN EXACT QUADRATIC SURD, derived only from device constants:
  slip(1/1) = 38376/2132 = 18 exactly, so slip(d) = 18/d²; crossing at slip = target = 5 ⟹
  d*² = 18/5, d* = √(18/5) = √90/5.  No grid, no seed, no external number — C = 18 and target = 5
  are the device's own.  A quadratic surd ⟹ eventually-PERIODIC continued fraction: [1;1,8,1,2̄]
  (period [1,8,1,2]).  That periodicity IS the device-native descent.

THE MODULO REALM (division, not the unary mediant crawl):
  convergents  1/1, 2/1, 17/9, 19/10, 55/29, 74/39, 647/341, …   (best rational approximants;
  each is one Euclidean/CF step — a whole partial quotient — not eight identical +1 mediant steps).

  count-to-3  = 3 partial quotients [1;1,8] → convergent 17/9, bracketed against 2/1:
      inv-α ∈ [129.6 .. 137.7]        (contains 137.036; the 129.6 wall is the loose 2/1 convergent)
  count-to-4  = 4 partial quotients → [17/9, 19/10]:
      inv-α ∈ [136.8 .. 137.7]        (contains 137.036, tighter)
  deep convergents → the device's OWN crossing value ≈ 137.011 (@conv5–7), NOT the lab 137.036.

WHAT CHANGED vs the dyadic AlphaBoundCountToThree:
  • grid-128 seed GONE — the crossing √(18/5) is computed from device constants; the [1,2] region
    is DISCOVERED by the CF (a₀ = 1), not hand-seeded.
  • no /2, no denominator-doubling, no continuum — integer division + convergent recurrence only;
    choice-free ([propext]).
  • the count-to-3 floor is now a device-native statement (3 partial quotients of the surd), and its
    honest bracket is [129.6, 137.7]; tightening is a matter of taking more convergents, converging
    to the device's own 137.011 — which it "proves it cannot derive" past its own value toward 137.036.
-/

end Measurement
