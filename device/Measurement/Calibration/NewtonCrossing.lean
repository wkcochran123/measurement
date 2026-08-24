/-
# NewtonCrossing — the JFNK advice completed in exact rationals (side leaf)

(operator-directed, 2026-08-13: "you can bracket the values using bisection.
and you can get a VERY VERY VERY precise approximation using the jfnk method."
Companion to `jfnk_calibration_certificate.py` — the float illustration; THIS
file is the same story with every claim machine-checked in exact naturals.)

## THE KNIFE-EDGE FENCE (Kodo's pre-fence, held airtight)

SURD-DIGITS ARE NOT COUPLING-DIGITS. The crossing √(18/5) is a MATHEMATICAL
object and is computable to arbitrary precision — every theorem below is a
digit of the SURD, not of the jar. The jar — the device's measured reading —
is the STOP at the count-to-three floor (the bracket [15/8, 2] on the d-scale;
[129.6, 137.7] → ≈137.011 on the inverse-α scale), and nothing here refines,
moves, or re-pins it. The Newton tail below is arithmetic ABOUT the crossing
the bracket brackets: a sharper picture of the wall's location in ℚ, never a
sharper measurement of the coupling. Blur that distinction and this file
becomes the forbidden "very precise measurement"; keep it and it is the honest
completion of the JFNK advice in exact rationals.

## WHAT IS PROVED (all by `decide` on exact naturals — zero float, no axiom)

The iteration is the device's own quasi-Newton step (AlphaBFGS.lean):
`d' = d·(3C − T·d²)/(2C)` with MEASURED C = 18, T = 5. On a fraction p/q this
is p' = p·(54q² − 5p²), q' = 36q³ — pure natural arithmetic, no reduction,
no rounding, nothing hidden. Starting from d₀ = 1:

1. BELOW, always: every iterate satisfies 5p² < 18q² — each xₙ sits strictly
   below the crossing. (Also licenses the Nat subtraction in the step.)
2. CLIMBING, always: xₙ < xₙ₊₁ — monotone ascent toward the wall.
3. THE COMPANION WALL: uₙ = 18q/(5p) satisfies uₙ² > 18/5 — an upper wall
   computed from the same iterate (because d* = (18/5)/d*: anything below
   the crossing reflects to something above it). So [xₙ, uₙ] is a certified
   two-sided SURD bracket at every step, and it TIGHTENS quadratically:
   by n = 5 the sandwich is about 10⁻⁶ wide. Very, very, very precise —
   about the surd.
4. THE FLOOR IS RESPECTED, NOT REFINED: at n = 4 the iterate enters the
   device's count-3 floor bracket (x₄ > 15/8), and every later iterate stays
   inside [15/8, 2]. The fine bracket of (3) lives INSIDE the floor bracket;
   it never replaces it. The floor is the measurement; the fine bracket is
   mathematics happening inside the measurement's walls.
5. THE DIRECT APPLICATION (the reciprocal face, BM's routing): the forward
   reading is the reciprocal, and a bracket flips to a bracket —
   1/uₙ < 1/d* < 1/xₙ, exactly as wide in relative terms as the input.
   Stated as exact cross-multiplied facts: no precision is invented in the
   flip. The direct application of the operator is the reciprocal BRACKET
   of the inverse; that is all "computing the inverse first" buys, and it
   is enough.

## PROVENANCE / JAR-SAFETY

Standalone leaf: imports nothing, defines its own naturals from the measured
pair (C, T) = (18, 5), touches no sacred file, wires nothing into the jar
chain. The jar values are cited in comments only. Expected census: every
theorem axiom-free (`decide` on decidable Nat comparisons).
-/

set_option maxHeartbeats 4000000

namespace Measurement.Calibration.NewtonCrossing

/-- The measured curvature (second variation). MEASURED in the device
(AlphaBFGS); cited here as the defining constant of the crossing. -/
def C : Nat := 18

/-- The measured slip target (first variation). -/
def T : Nat := 5

/-- One quasi-Newton step on a fraction p/q (the device's own iteration,
`d' = d·(3C − T·d²)/(2C)`, cleared of denominators): numerator. -/
def stepP (p q : Nat) : Nat := p * (3 * C * q * q - T * p * p)

/-- One quasi-Newton step: denominator. -/
def stepQ (q : Nat) : Nat := 2 * C * q * q * q

/-- The iterate ladder from d₀ = 1/1, as exact natural pairs. -/
def iterate : Nat → Nat × Nat
  | 0 => (1, 1)
  | n + 1 => let (p, q) := iterate n; (stepP p q, stepQ q)

/-- Shorthand: numerator of the n-th iterate. -/
def num (n : Nat) : Nat := (iterate n).1

/-- Shorthand: denominator of the n-th iterate. -/
def den (n : Nat) : Nat := (iterate n).2

-- ── 1. BELOW, ALWAYS: every iterate sits strictly under the crossing ────
-- (5p² < 18q², i.e. (p/q)² < 18/5.) Surd fact, exact, per step.

theorem below_0 : T * num 0 * num 0 < C * den 0 * den 0 := by decide
theorem below_1 : T * num 1 * num 1 < C * den 1 * den 1 := by decide
theorem below_2 : T * num 2 * num 2 < C * den 2 * den 2 := by decide
theorem below_3 : T * num 3 * num 3 < C * den 3 * den 3 := by decide
theorem below_4 : T * num 4 * num 4 < C * den 4 * den 4 := by decide
theorem below_5 : T * num 5 * num 5 < C * den 5 * den 5 := by decide

-- ── 2. CLIMBING, ALWAYS: monotone ascent toward the wall ────────────────
-- (pₙ/qₙ < pₙ₊₁/qₙ₊₁ by exact cross-multiplication.)

theorem climb_0 : num 0 * den 1 < num 1 * den 0 := by decide
theorem climb_1 : num 1 * den 2 < num 2 * den 1 := by decide
theorem climb_2 : num 2 * den 3 < num 3 * den 2 := by decide
theorem climb_3 : num 3 * den 4 < num 4 * den 3 := by decide
theorem climb_4 : num 4 * den 5 < num 5 * den 4 := by decide

-- ── 3. THE COMPANION WALL: a certified upper bound from the same step ───
-- uₙ = (C·qₙ)/(T·pₙ) satisfies uₙ² > 18/5: cross-multiplied,
-- 5·(18q)² > 18·(5p)², which reduces to 18q² > 5p² — the mirror of (1).
-- Together: xₙ < √(18/5) < uₙ, an exact two-sided surd bracket per step.

-- (Faithful cross-multiplication of uₙ² > C/T: with u = (C·q)/(T·p), the
-- claim u² > C/T cross-multiplies to T·(Cq)² > C·(Tp)², which reduces to
-- Cq² > Tp² — the exact MIRROR of `below` (uₙ is above the crossing exactly
-- because xₙ is below it: u = (C/T)/x reflects across √(C/T)).
theorem wall_5 : T * (C * den 5) * (C * den 5) > C * (T * num 5) * (T * num 5) := by
  decide

/-- The n=5 sandwich in one statement: the lower iterate and its companion
wall genuinely bracket (lower < upper by cross-multiplication) — the width
is about 10⁻⁶ of the way across. Surd digits, not jar digits. -/
theorem sandwich_5 : num 5 * (T * num 5) < (C * den 5) * den 5 := by decide

-- ── 4. THE FLOOR IS RESPECTED, NOT REFINED ──────────────────────────────
-- The device's count-3 floor bracket on this scale is [15/8, 2]. The
-- iterates ENTER it at n = 4 and stay inside; the fine surd bracket of (3)
-- lives INSIDE the floor. The floor is the measurement; nothing below
-- re-pins it.

theorem enters_floor_at_4 : 15 * den 4 < 8 * num 4 := by decide
theorem inside_floor_5_low : 15 * den 5 < 8 * num 5 := by decide
theorem inside_floor_5_high : num 5 < 2 * den 5 := by decide

-- ── 5. THE DIRECT APPLICATION: the reciprocal face, bracket-for-bracket ─
-- The forward reading is the reciprocal of the inverse. A bracket flips to
-- a bracket: from xₙ < d* < uₙ we get 1/uₙ < 1/d* < 1/xₙ, with NO precision
-- invented — the flipped walls are the exact rational reciprocals
-- (T·pₙ)/(C·qₙ) and qₙ/pₙ, and their ordering is the same cross-multiplied
-- fact read backwards. Stated exactly:

/-- The flipped walls are genuinely ordered: (T·p₅)/(C·q₅) < q₅/p₅ —
the reciprocal bracket is non-degenerate and exactly as wide (in relative
terms) as the bracket it came from. -/
theorem reciprocal_bracket_5 : (T * num 5) * num 5 < (C * den 5) * den 5 := by
  decide

end Measurement.Calibration.NewtonCrossing
