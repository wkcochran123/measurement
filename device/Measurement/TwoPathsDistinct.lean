-- TwoPathsDistinct.lean
--
-- THE TWICE-IMPOSSIBILITY (Kodo's flagged un-built wall, 2026-08-17):
-- the corpus has always said, as a matter of restraint, "there is no
-- direct = stepped equality theorem." This leaf upgrades that absence
-- to an impossibility: THE EQUALITY IS PROVABLY FALSE. The two routes
-- to the device's number cannot be collapsed into one mechanism,
-- because as exact integers they are two — while at the device's own
-- count-3 resolution they are one number. The TWICE is irreducibly two.
--
-- Both routes are already-built objects of CalibrationTwoPaths:
--   direct_1to3   : the one-pass reading at the crossing (jar-tied)
--   stepped_1to2to3 : quasi-Newton descent through count-3 (AlphaBFGS)
-- Nothing here re-derives them; this leaf only decides facts about the
-- two finished computations, by kernel evaluation.
--
-- NOT-CLAIMED: this is a statement about the DEVICE'S two computations
-- and nothing else. It does not say the lab's 137.036 is wrong, does
-- not touch any outside threshold system, and does not weaken the
-- nine-digit agreement — it PINS the agreement exactly (word-for-word
-- with the count-3 floor discipline) while refuting the collapse.

import Measurement.CalibrationTwoPaths

namespace Measurement.TwoPathsDistinct

open Measurement.CalibrationTwoPaths

-- Kernel evaluation of the finished computations needs unfolding room;
-- this raises the elaborator's recursion budget only, adds no axiom.
set_option maxRecDepth 100000

-- The wall itself: the two mechanisms are NOT the same computation.
-- Any proposed collapse of the TWICE into one route asserts this
-- equality, and this equality is false.
theorem two_routes_distinct : direct_1to3 ≠ stepped_1to2to3 := by decide

-- The gap, pinned exactly: the routes differ by 204771701686 parts in
-- 1e18 — about 2e-7 in inverse-α units, real and nonzero.
theorem routes_gap_exact :
    stepped_1to2to3 - direct_1to3 = 204771701686 := by decide

-- The agreement, pinned exactly at the device's own resolution: the
-- leading nine digits coincide (both routes read 137.0112905…). This is
-- the honest form of "one number" — agreement below the count-3 floor,
-- never identity.
theorem routes_agree_nine_digits :
    direct_1to3 / 10 ^ 12 = stepped_1to2to3 / 10 ^ 12 := by decide

-- The direct route is the jar, to the digit — the frozen cold-build
-- value, re-decided here from the construction itself.
theorem direct_is_jar : direct_1to3 = 137011290548979455469 := by decide

-- The headline, in one statement: two mechanisms, one number at the
-- device's resolution, provably NOT one mechanism.
theorem twice_is_irreducibly_two :
    direct_1to3 ≠ stepped_1to2to3 ∧
    direct_1to3 / 10 ^ 12 = stepped_1to2to3 / 10 ^ 12 :=
  ⟨two_routes_distinct, routes_agree_nine_digits⟩

end Measurement.TwoPathsDistinct

#print axioms Measurement.TwoPathsDistinct.two_routes_distinct
#print axioms Measurement.TwoPathsDistinct.routes_gap_exact
#print axioms Measurement.TwoPathsDistinct.routes_agree_nine_digits
#print axioms Measurement.TwoPathsDistinct.direct_is_jar
#print axioms Measurement.TwoPathsDistinct.twice_is_irreducibly_two
