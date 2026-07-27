import Measurement.AlphaBoundMediant

/-! # GridDerivation — task 2: the grid 128/48, derives-cold-or-fails-in-public.

PRE-REGISTERED LAWS (posted + Kodo-gated BEFORE this file was written; the no-fishing
protocol): L0 the grid must be a power of two (dyadic endpoints keep the bisection
exact); L1 for 128 — THE COUNT-3 RESOLUTION LAW: the grid must resolve PAST where the
count-to-three walk stopped, i.e. the seam cell must exclude the count-3 lower wall
17/9 (the last convergent before the crossing √(18/5)); the smallest such dyadic grid is
the derived value. L2–L5 for 48 — the precision family: the smallest rung count whose
final width at the readout scale is under 1 (L2), under T=5 (L3), under C=18 (L4),
under D=C·T=90 (L5). Kodo added NO laws (adding one after knowing the target is the
fishing the gate forbids) and struck none (L2–L5 stay as the honest-miss record).

REAL CONSTANTS, not literals: the wall is `count3Lo` (the device's own [1;1,8] = 17/9
convergent), the crossing is d*² = C/T with C = `mediantC` (proven 18) and T =
`mediantTgt` (5, device-derived), D = `cfD` (= C·T), the scale is `readoutScale`
(= 10^18). Every comparison below is exact integer arithmetic decided by the kernel.

THE VERDICT IS WHATEVER THIS FILE COMPUTES. -/

namespace Measurement.GridDerivation

open Measurement

/-- The wall really is 17/9 — the pre-registered law's input, tied to the device's own
count-3 convergent, not a keyboard literal. -/
theorem wall_is_seventeen_ninths :
    count3Lo.numerator = 17 ∧ count3Lo.denominator = 9 := by decide

#print axioms wall_is_seventeen_ninths

/-! ## L1 — the count-3 resolution law (for the grid = 128)

Cell width 1/2^k fits the gap between the wall and the crossing iff
(17/9 + 1/2^k) < d*, i.e. (17·2^k + 9)² · T < C · (9·2^k)²  (squaring; all positive).
The law derives the smallest such k. -/

/-- The gap test at grid 2^k, in exact integers off the device constants. -/
def cellFitsGap (k : Nat) : Bool :=
  (count3Lo.numerator * 2 ^ k + count3Lo.denominator) ^ 2 * mediantTgt
    < mediantC * (count3Lo.denominator * 2 ^ k) ^ 2

/-- 2^7 = 128 FITS: the grid at 128 resolves past the count-3 wall. Exact integers:
(17·128+9)²·5 = 23871125 < 23887872 = 18·1152². -/
theorem grid_128_fits : cellFitsGap 7 = true := by decide

/-- EVERY coarser dyadic grid FAILS — checked exhaustively, k = 0..6 (not by
monotonicity prose; each case decided). At k=6: (1097)²·5 = 6017045 > 5971968 = 18·576². -/
theorem coarser_grids_fail :
    ((List.range 7).all fun k => !(cellFitsGap k)) = true := by decide

/-- THE DERIVATION: 128 = 2^7 is the SMALLEST power-of-two grid that resolves past the
count-3 wall. The law's consequence, not a chosen value. -/
theorem grid_derives_128 :
    cellFitsGap 7 = true ∧ ((List.range 7).all fun k => !(cellFitsGap k)) = true :=
  ⟨grid_128_fits, coarser_grids_fail⟩

#print axioms grid_derives_128

/-! ## L2–L5 — the precision family (for the rungs = 48): each law's minimal rung count,
computed exactly; NONE lands on 48.

Total halvings from [1,2] after k=7 grid bits + r rungs = r + 7; the final width at the
readout scale is readoutScale / 2^(r+7). Law LX demands width < X; minimal m := r+7 with
X · 2^m > readoutScale, so r = m − 7. -/

/-- The minimal total-halvings m for "width < X at the readout scale": X·2^(m−1) ≤ scale < X·2^m. -/
def minimalHalvings (X m : Nat) : Bool :=
  X * 2 ^ (m - 1) ≤ readoutScale && readoutScale < X * 2 ^ m

/-- L2 (width < 1): minimal m = 60 → rungs = 53. NOT 48. -/
theorem l2_yields_53 : minimalHalvings 1 60 = true ∧ 60 - 7 ≠ 48 := by decide

/-- L3 (width < T = 5): minimal m = 58 → rungs = 51. NOT 48. -/
theorem l3_yields_51 : minimalHalvings mediantTgt 58 = true ∧ 58 - 7 ≠ 48 := by decide

/-- L4 (width < C = 18): minimal m = 56 → rungs = 49. NOT 48. -/
theorem l4_yields_49 : minimalHalvings mediantC 56 = true ∧ 56 - 7 ≠ 48 := by decide

/-- L5 (width < D = C·T = 90): minimal m = 54 → rungs = 47. NOT 48. -/
theorem l5_yields_47 : minimalHalvings cfD 54 = true ∧ 54 - 7 ≠ 48 := by decide

/-- THE 48 VERDICT: no pre-registered law lands on 48 — the four principled candidates
yield 53, 51, 49, 47. Forty-eight FAILS-IN-PUBLIC and remains, honestly, a chosen
number (as CountToThree:21 has always marked it). -/
theorem no_law_lands_48 :
    (60 - 7 ≠ 48) ∧ (58 - 7 ≠ 48) ∧ (56 - 7 ≠ 48) ∧ (54 - 7 ≠ 48) := by decide

#print axioms l2_yields_53
#print axioms no_law_lands_48

#eval s!"L1: grid 2^7=128 fits the wall-gap? {cellFitsGap 7}; all coarser fail? {(List.range 7).all fun k => !(cellFitsGap k)}"
#eval s!"48-family minima: L2→{60-7} L3→{58-7} L4→{56-7} L5→{54-7} — none is 48"

end Measurement.GridDerivation
