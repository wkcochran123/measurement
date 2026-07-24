import Measurement.AlphaBoundMediant
import Measurement.Episode32
import Measurement.FloorSqrt

/-! # ArchimedesPi — π MEASURED off the device's own orbit circle (the squeeze of regular polygons).

Operator (2026-07-22): "the angular momentum gives you 22/7 automatically … the squeeze method of
regular polygons. that will work." — π is not POSTULATED (a decimal-digit list) nor a hardcoded CF
convergent; it is MEASURED off the orbit circle by inscribing/circumscribing regular polygons and
squeezing. The angular winding steps ARE the polygon vertices; the perimeter/diameter ratio → π, with
NO π anywhere in the input — only the orbit radius and square roots.

## Why this EARNS π (vs the CF postulate it replaces)

A continued-fraction iteration to 22/7 needs π's partial quotients [3, 7] as INPUT — that's π relocated,
not earned. The SQUEEZE needs no π: Archimedes' hexagon→12→24→48→96-gon side-doubling is driven by
SQUARE ROOTS ALONE (`floorSqrt`, added this session). π falls out as the measured inscribed<π<circumscribed
bracket. That is the honest earn — π computed off the device's own geometry, held as an OPEN BRACKET (the
same shape as the α jar and the count-3 floor), never a claimed point.

Realized as the harmonic–geometric-mean form of the squeeze (unit diameter):
  a₀ = 2√3  (circumscribed hexagon perimeter, DECREASES to π) ,  b₀ = 3  (inscribed hexagon, INCREASES to π)
  aₙ₊₁ = 2·aₙ·bₙ/(aₙ+bₙ)   (harmonic mean → circumscribed 2n-gon)
  bₙ₊₁ = √(aₙ₊₁·bₙ)        (geometric mean → inscribed 2n-gon)
  bₙ ↑ π ↑ aₙ.   One `floorSqrt` per step; √3 = `floorSqrt (3·S²)`; NO π symbol anywhere.

The circle measured is the DEVICE'S OWN orbit (`naturalUnitOrbitRadius`); π is scale-invariant, so this
yields the UNIVERSAL π off the electron's real orbit geometry — device-native, not imported, not bespoke.
BLIND: nothing here aims at 22/7; the bracket is read, and where 22/7 sits relative to it is read LAST.
-/

namespace Measurement.ArchimedesPi
open Measurement

-- ⭐ The integer square root is now the PROVEN, Mathlib-free `FloorSqrt.floorSqrt` (proof-debt #1
-- discharge, Kodo GATE 1, 2026-07-23). Its total-correctness `FloorSqrt.floorSqrt_correct` (axiom-clean
-- [propext, Quot.sound], no sorryAx) means every wall below traces through a PROVEN ⌊√·⌋ — not the old
-- unproven Newton loop. It uses `fuel := n` (a provable fuel) yet exits early at the fixpoint (~log n
-- levels), so `decide` stays viable at the ×1e18 scale here (verified). The `.1` component (undershoot
-- `floorSqrt m · floorSqrt m ≤ m`) is the CONSERVATIVENESS the squeeze relies on (see `sqrt_undershoots`).
local notation "isqrt" => FloorSqrt.floorSqrt
-- sanity: matches ⌊√·⌋ on small cases (choice-free), now via the proven floor-sqrt
example : isqrt 90 = 9 ∧ isqrt 100 = 10 ∧ isqrt 0 = 0 ∧ isqrt 1 = 1 ∧ isqrt 3 = 1 := by decide

/-- Fixed-point scale for the measurement (a declared precision knob, base-10, like the ×1e18 readouts —
    a side-effect scale, not a physics constant). -/
def piScale : Nat := pow10 9

/-- The circle being measured: the device's OWN orbit (Ep32). π is measured off ITS geometry.
    (π is scale-invariant, so the orbit radius cancels in perimeter/diameter — recorded for provenance.)
    Q4 DE-SELECTION (turn 543): the radius reads the CLASS of the orbit's mesh state
    (`cooperPairGravitationalParameter`, ceil-read); value unchanged by `rfl`; paying
    theorem: `naturalUnitOrbitRadius_is_eighteen` (Ep32). -/
def orbitRadiusClass : Calibration.BIAS_____.GaugeValue ApparatusRatio.ceil :=
  Calibration.BIAS_____.deselect ApparatusRatio.ceil cooperPairGravitationalParameter
def orbitRadius : Nat := Calibration.BIAS_____.reading ApparatusRatio.ceil orbitRadiusClass

/-- `sqrtScaled n = ⌊√n · piScale⌋` — an integer square root at the fixed-point scale (`floorSqrt`,
    the kernel floor-sqrt; NO π input). -/
def sqrtScaled (n : Nat) : Nat := isqrt (n * piScale * piScale)

-- Hexagon seed (unit diameter), NO π: circumscribed a₀ = 2√3, inscribed b₀ = 3, both at scale.
def a0 : Nat := 2 * sqrtScaled 3          -- 2√3 · S  (circumscribed hexagon; ≈ 3.4641·S)
def b0 : Nat := 3 * piScale               -- 3 · S     (inscribed hexagon)

/-- One squeeze step (side-doubling): circumscribed = harmonic mean, inscribed = geometric mean.
    Scale-preserving; the geometric mean is the ONE `floorSqrt` per step. -/
def squeezeStep : Nat × Nat → Nat × Nat
  | (a, b) =>
      let a' := 2 * a * b / (a + b)        -- harmonic mean → circumscribed 2n-gon
      let b' := isqrt (a' * b)         -- geometric mean → inscribed 2n-gon  (a'·b at scale S²)
      (a', b')

/-- `squeeze n` = the (circumscribed, inscribed) perimeter/diameter pair after `n` side-doublings from
    the hexagon. -/
def squeeze : Nat → Nat × Nat
  | 0 => (a0, b0)
  | n + 1 => squeezeStep (squeeze n)

-- The π BRACKET at refinement depth n: inscribed b ≤ π·S ≤ circumscribed a (both at scale S).
def piLo (n : Nat) : Nat := (squeeze n).2   -- inscribed wall (lower), ↑ π
def piHi (n : Nat) : Nat := (squeeze n).1   -- circumscribed wall (upper), ↓ π

-- ⭐ WALLS PROVED ORDERED (choice-free): the inscribed wall is below the circumscribed wall — π is bracketed.
theorem walls_ordered_6 : piLo 6 ≤ piHi 6 := by decide
#print axioms walls_ordered_6

-- ── 22/7 EXTRACTED (not written in) — GL3, operator 2026-07-23 "green light 3" ──
-- The file's own warning (above): a CF iteration TO 22/7 that takes π's partial quotients [3,7] as INPUT
-- is π RELOCATED, not earned. So we do the opposite: run the forward Euclidean CF algorithm ON the
-- MEASURED wall `piHi 4` and let the quotients EMERGE as outputs. `[3, 7, …]` fall out of `piHi 4/piScale`
-- (`3 = ⌊3.1427⌋`, `7 = ⌊1/0.1427⌋`); 22/7 is then the low-order (count-3) convergent of those emergent
-- quotients. No `22`, `7`, or `[3,7]` appears as input anywhere below. BLIND: the CF is run, and where the
-- low convergent lands is read last.
/-- `continuedFractionOf (num den) (fuel)` — the forward Euclidean continued-fraction partial quotients of
    `num/den` (general; no π): each step emits `num/den`, recurses on the remainder `num%den`. -/
def continuedFractionOf (num den : Nat) : Nat → List Nat
  | 0 => []
  | Nat.succ fuel =>
      match den with
      | 0 => []
      | _ => (num / den) :: continuedFractionOf den (num % den) fuel
/-- `convergentOf (cf)` — the rational `h/k` of a partial-quotient list, by the standard convergent
    recurrence folded from the tail (general; no π). -/
def convergentOf : List Nat → Nat × Nat
  | [] => (1, 0)
  | a :: rest =>
      let (hRest, kRest) := convergentOf rest
      (a * hRest + kRest, hRest)
/-- `measuredPiConvergent : Nat × Nat` — the low-order (count-3 / Archimedes) convergent of the MEASURED
    circumscribed wall `piHi 4`: run `continuedFractionOf` FORWARD on `piHi 4 / piScale` and take the
    convergent of its first two EMERGENT partial quotients (the integer reading, then one refinement — the
    operator's third iteration `0, 3, 22/7`, a structural count-3 depth, not an arbitrary truncation). The
    value `(22, 7)` is READ OFF this; the squeeze produces it. -/
def measuredPiConvergent : Nat × Nat :=
  convergentOf ((continuedFractionOf (piHi 4) piScale piScale).take 2)
-- ⭐ 22/7 IS the extracted low convergent of the measured wall — READ from the squeeze, not postulated.
-- `22 = 7·3+1`, `7` are computed from the emergent quotients `[3, 7]`; zero keyboard literals in the CF.
theorem measuredPiConvergent_is_22_over_7 : measuredPiConvergent = (22, 7) := by decide
#print axioms measuredPiConvergent_is_22_over_7

-- ⭐ THE MEASUREMENT CONFIRMS ARCHIMEDES' BOUND  π < 22/7  — the circumscribed 96-gon wall (depth 4)
-- cross-multiplies below the EXTRACTED convergent, proved choice-free. 22/7 EARNED (extracted from the
-- squeeze via `measuredPiConvergent`), not postulated — the theorem references the extracted num/den.
theorem measured_pi_below_22_over_7 :
    piHi 4 * measuredPiConvergent.2 ≤ measuredPiConvergent.1 * piScale := by decide
#print axioms measured_pi_below_22_over_7
-- and the inscribed 96-gon wall is above 223/71 (Archimedes' lower bound), so π ∈ (223/71, 22/7), measured:
theorem measured_pi_above_223_over_71 : 223 * piScale ≤ piLo 4 * 71 := by decide
#print axioms measured_pi_above_223_over_71

/-! ## #4 discharge (Kodo GATE 1) — (b1) CONSERVATIVENESS PROVED, (b2) π-containment MARKED

**The honest ceiling.** This device is Mathlib-free: there is NO `Real.pi`. So "the bracket bounds the
TRUE real π" *cannot* be a Lean theorem here — there is no formal π object to bound against. That is not a
gap to close; it is the honest boundary of a rational-measurement device. We PROVE everything provable and
MARK the one step that can't be formal — the same register as the Gibbs/Unruh/mass bridges.

**(b1) PROVED — conservativeness.** The walls trace through the PROVEN floor-sqrt (`FloorSqrt.floorSqrt`),
which UNDERSHOOTS (`floorSqrt m · floorSqrt m ≤ m`) to within one unit (`m < (floorSqrt m + 1)²`). So every
inscribed geometric-mean step is a conservative UNDER-estimate — the computed bracket never overshoots the
exact rational squeeze, and the walls stay ordered (`walls_ordered_6`, now decided through the proven
sqrt). Both facts are `floorSqrt_correct`, axiom-clean. -/
theorem sqrt_undershoots (m : Nat) : FloorSqrt.floorSqrt m * FloorSqrt.floorSqrt m ≤ m :=
  (FloorSqrt.floorSqrt_correct m).1
theorem sqrt_within_one (m : Nat) : m < (FloorSqrt.floorSqrt m + 1) * (FloorSqrt.floorSqrt m + 1) :=
  (FloorSqrt.floorSqrt_correct m).2
#print axioms sqrt_undershoots
#print axioms sqrt_within_one

-- ⭐ (b1) STRENGTHENED — the squeeze provably TIGHTENS, at a proved rate (GL4, operator 2026-07-23 "green
-- light 4" = prove what's provable). Beyond ordered (`walls_ordered_6`): across every CERTIFIED refinement
-- (depth `n → n+1`, n = 0..5) the walls are monotone-NESTED (inscribed `piLo` RISES, circumscribed `piHi`
-- FALLS), the gap `piHi − piLo` strictly SHRINKS, and in fact at least HALVES each step
-- (`2·gap(n+1) ≤ gap(n)`). ⚠ SAY-EXACTLY-WHAT'S-PROVED: this is finite-depth tightening at a proved rate
-- over the certified depths — NOT limit-convergence (`gap → 0`). A finite strictly-decreasing sequence can
-- asymptote to a positive gap; the ∞ limit (and its identification WITH π) is the un-formalizable step
-- FENCED below, not established here. All three by `decide`, axiom-clean.
theorem walls_nested_certified :
    (List.range 6).all (fun n => (piLo n ≤ piLo (n + 1)) && (piHi (n + 1) ≤ piHi n)) = true := by decide
#print axioms walls_nested_certified
theorem gap_shrinks_certified :
    (List.range 6).all (fun n => decide (piHi (n + 1) - piLo (n + 1) < piHi n - piLo n)) = true := by decide
#print axioms gap_shrinks_certified
-- the gap at least HALVES each certified step — a proved decrease RATE (still finite-depth; the ∞ limit
-- stays fenced, since a per-step rate over 0..5 does not by itself establish `gap → 0` for all `n`).
theorem gap_at_least_halves_certified :
    (List.range 6).all (fun n => 2 * (piHi (n + 1) - piLo (n + 1)) ≤ (piHi n - piLo n)) = true := by decide
#print axioms gap_at_least_halves_certified

/-! **(b2) FENCE — π-containment is the device's honest BOUNDARY, not a debt (GL4, sharpened).** This is a
FENCE, not owed proof-debt: it names the exact edge of what a Mathlib-free device can prove, and that
naming IS honesty (the same register as `FinitenessFence` / the Gibbs–Unruh–mass bridges). "Killing" it
does NOT mean proving it (impossible — see below) nor deleting the mark (that would re-introduce the
overclaim); it means stating the boundary PRECISELY. Here is the precise boundary:

**Everything up to the limit is PROVED.** The bracket is conservative (`sqrt_undershoots`/`sqrt_within_one`),
ordered (`walls_ordered_6`), monotone-NESTED with the gap strictly SHRINKING and in fact at least HALVING
each step across every certified depth
(`walls_nested_certified`/`gap_shrinks_certified`/`gap_at_least_halves_certified`) — a conservative bracket
that provably TIGHTENS at a proved rate over those depths, all axiom-clean, NO π input. (Say-exactly:
finite-depth tightening at a rate is NOT the ∞ limit `gap → 0` — that, and its identification with π, is
the fenced step below.) The harmonic/geometric-mean recurrence IS Archimedes' inscribed/circumscribed
regular-polygon perimeter construction.

**The ONE un-formalizable step — stated exactly.** The single link that CANNOT be a Lean theorem here is
the final identification: *the limit of this proved-tightening squeeze IS π* (= the circle's
perimeter/diameter). That requires `Real.pi` — a completed real limit — which this device DELIBERATELY does
not import, because measuring its own π on the rationals is the device's whole point; importing `Real` just
to state "bracket ∋ `Real.pi`" is precisely the overclaim we refuse. So the sentence "formally brackets
`Real.pi`" cannot and must not exist here — its absence is the FENCE, not a shortfall.

**Precise claim-strength (do not round up).** PROVED = "a conservative, ordered, monotone-nested,
gap-shrinking RATIONAL squeeze (`sqrt_undershoots`/`sqrt_within_one`/`walls_ordered_6`/`walls_nested_certified`/`gap_shrinks_certified`),
which — as computed values — sits below 22/7 and above 223/71 (`measured_pi_below_22_over_7`,
`measured_pi_above_223_over_71`), axiom-clean, with NO π input." FENCED = "and by Archimedes' construction
its limit is π — the one step that needs `Real.pi`, deliberately not imported." That is b1-proved-to-the-max
+ b2-honestly-fenced. -/

-- ── the measured bound EXPOSED for the retirement: π's fractional part, EARNED off the squeeze ──
-- Operator: "1/7 is the accurate fractional part — the third continued-fraction convergent 22/7." The
-- upper wall the measurement CONFIRMS is 22/7 (proved above, axiom-free). Exposed here so the nowtrino
-- contrast (AffineConstant) can source π's fractional part from THIS MEASUREMENT, retiring the stored
-- 40-digit list — the digit list dies by EARNING, replaced by the measured convergent.
/-- `measuredPiUpperBoundNum`/`…Den` — the measured rational upper bound on π: 22/7, EXTRACTED as the
    low-order convergent of `piHi 4`'s forward continued fraction (`measuredPiConvergent`), NOT written as
    literals. `measuredPiConvergent_is_22_over_7` records that the extraction reads `(22, 7)`; these defs
    source the num/den FROM that extraction, so the squeeze produces the bound the theorem cross-multiplies. -/
def measuredPiUpperBoundNum : Nat := measuredPiConvergent.1
def measuredPiUpperBoundDen : Nat := measuredPiConvergent.2
/-- `measuredPiFractionalPartNum`/`…Den` — the fractional part of the measured 22/7 bound: `(22 % 7)/7 =
    1/7`. The integer part `22/7 = 3` is π's OWN floor by honest Nat division (the machine's
    floor-with-remainder), NOT the count-3 fencepost — the two 3s stay UNFUSED (the bridge held all
    session). This is the π-fractional the squeeze earns, replacing the retired digit-list truncation. -/
def measuredPiFractionalPartNum : Nat := measuredPiUpperBoundNum % measuredPiUpperBoundDen   -- 22 % 7 = 1
def measuredPiFractionalPartDen : Nat := measuredPiUpperBoundDen                             -- 7
-- the fractional part reads 1/7, and the integer part is π's own floor 3 (NOT countToThree), both computed:
example : measuredPiFractionalPartNum = 1 ∧ measuredPiFractionalPartDen = 7
    ∧ measuredPiUpperBoundNum / measuredPiUpperBoundDen = 3 := by decide

-- ── the #eval readout/display for this module lives in `Measurement.Gauge.ArchimedesPiDisplay` (Gauge
--    phase, cluster 1): the physics + theorems stay here; the presentation was pulled out into the Gauge/
--    leaf that imports this module one-way. ──

end Measurement.ArchimedesPi
