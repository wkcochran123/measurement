import Measurement.Episode40

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

def mediantTgt : Nat := firstSlipTargetBetweenOneAndTwo   -- = 5

-- The crossing is √(18/5) = √90 / 5.  PQa on (P₀,Q₀,D) = (0,5,90).
def cfD : Nat := 90
def cfSqrtD : Nat := 9                                     -- ⌊√90⌋ = 9 (9²=81 ≤ 90 < 100=10²)
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
  cfAux n 0 5 1 0 0 1

def mediantInvAlphaAt (d : RationalDistance) : Nat :=
  (alphaFromSecondVariationAtDistance mediantTgt d).inverseScaledFloor (pow10 18)

/-- inv-α (×1e18) at a convergent h/k. -/
def convInvAlpha (hk : Nat × Nat × Nat) : Nat :=
  mediantInvAlphaAt { numerator := hk.2.1, denominator := hk.2.2 }

-- The continued fraction, its convergents, and the inv-α at each convergent.
#eval s!"crossing = √90/5 = √(18/5) ≈ 1.897367;  partial quotients [a₀;a₁,a₂,…] (modulo realm):"
#eval s!"  {(crossingConvergents 8).map (fun t => t.1)}"
#eval s!"convergents h/k and inv-α(×1e18):"
#eval String.intercalate "\n" ((crossingConvergents 8).mapIdx (fun i t =>
  s!"  conv{i} (a={t.1}): {t.2.1}/{t.2.2}   inv-α = {mediantInvAlphaAt {numerator:=t.2.1,denominator:=t.2.2}}"))

-- RICHARDSON REFINEMENT FAMILY (operator protocol 2026-07-11): the CF convergents ARE A(hⱼ) — the
-- modulo-realm descent is the reproducible refinement parameter h. Deep family (conv0..19) so the
-- observed order p_obs can be checked for STABILIZATION on the fixed-r PERIOD subsample (period
-- [1,8,1,2] = 4; same-phase convergents approach the limit monotonically from one side). Machine-owned
-- A_j at scaled-integer ×1e18 with inverseScaledFloor rounding. Emits `RICH conv{i} k={k} invA18={..}`.
#eval String.intercalate "\n" ((crossingConvergents 20).mapIdx (fun i t =>
  s!"RICH conv{i} a={t.1} k={t.2.2} invA18={mediantInvAlphaAt {numerator:=t.2.1,denominator:=t.2.2}}"))

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

#eval s!"COUNT-TO-3 (3 partial quotients) bracket:  [{count3Lo.numerator}/{count3Lo.denominator} , {count3Hi.numerator}/{count3Hi.denominator}]  inv-α ∈ [{count3InvHi} .. {count3InvLo}]"

-- For reference: the next convergent tightens the far wall (count-to-4 = [17/9, 19/10]).
def count4Lo : RationalDistance := convAt 2   -- 17/9
def count4Hi : RationalDistance := convAt 3   -- 19/10
#eval s!"COUNT-TO-4 (4 partial quotients) bracket:  [{count4Lo.numerator}/{count4Lo.denominator} , {count4Hi.numerator}/{count4Hi.denominator}]  inv-α ∈ [{mediantInvAlphaAt count4Lo} .. {mediantInvAlphaAt count4Hi}]"

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
