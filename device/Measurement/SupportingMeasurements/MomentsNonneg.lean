import Measurement.Episode30

/-! # MomentsNonneg — task 6, the (i) earn: Cauchy–Schwarz ASSERTED on the real moments.

DISCHARGES Episode30:164's marked-not-asserted gap, EXTERNALLY: Ep30's own MARK reads
"on GENUINE moment sums this is nonnegative by Cauchy–Schwarz … NOT provable for
arbitrary a,b,c, so it is marked, not asserted." Both chairs ruled the mark's
rationalization the exact true-but-unasserted failure mode: the real call-sites do not
pass arbitrary a,b,c — they pass genuine moments (Σx, Σx², Σx³ over the same triplet
values), and for THOSE the weighted Cauchy–Schwarz (Σx²)² = (Σ x^{3/2}·x^{1/2})² ≤
Σx³·Σx holds and is PROVEN here, per real site, at the real window.

THE REAL WINDOW, BY REFERENCE (Beastmaster's sharpening — the crux of
assert-on-real-input): the window below is `assayLower`/`assayUpper` — the SAME
definitions `cavendishChargeMassNormalization` (Ep30:225) and `cavendishMagneticNeedle`
(Ep31:115) reduce to, referenced not copied. Both live consumers run this one window; no
other window is live in the tree.

JAR + MARK HONESTY (Beastmaster's form): this is a NEW 16+ LEAF — zero edits to Ep30 or
any jar-cone file; the jar is untouched by construction and NO cold-cone verify is
needed for this earn. Episode30:164's MARK is therefore STALE-BUT-SAFE from the moment
this file lands (the claim IS now asserted — here); the mark's pointer-update, and the
doc non-sequitur correction Kodo flagged (Ep30:168 conflates "not provable for
arbitrary a,b,c" with "not provable"), RIDE THE NEXT Ep30 EDIT or the cold-window batch
— an Ep30 edit today would rehash the jar cone for a comment. Debt status: PROVEN (in
this leaf), not marked. -/

namespace Measurement.MomentsNonneg

open Measurement

/-! ## The three real call-sites (Ep30:213-215), asserted at the real window

`slipPointMoments weight squareSum cubeSum` computes `varianceNumerator :=
cubeSum * weight − square squareSum`; nonneg ⟺ `square squareSum ≤ cubeSum * weight`. -/

/-- CHARGE column: (Σx²)² ≤ Σx³ · Σx over the assay window — the real inputs of
`slipPointMoments charge chargeSquares chargeCubes`, by kernel computation. -/
theorem charge_moments_nonneg :
    square (chargeTripletSquareSum assayLower assayUpper)
      ≤ chargeTripletCubeSum assayLower assayUpper
          * chargeTripletValueSum assayLower assayUpper := by decide

/-- MASS column: same shape, the real inputs of `slipPointMoments mass massSquares
massCubes`. -/
theorem mass_moments_nonneg :
    square (massTripletSquareSum assayLower assayUpper)
      ≤ massTripletCubeSum assayLower assayUpper
          * massTripletValueSum assayLower assayUpper := by decide

/-- COMBINED column: the summed moments — the real inputs of
`slipPointMoments total totalSquares totalCubes`. -/
theorem combined_moments_nonneg :
    square (chargeTripletSquareSum assayLower assayUpper
              + massTripletSquareSum assayLower assayUpper)
      ≤ (chargeTripletCubeSum assayLower assayUpper
              + massTripletCubeSum assayLower assayUpper)
          * (chargeTripletValueSum assayLower assayUpper
              + massTripletValueSum assayLower assayUpper) := by decide

#print axioms charge_moments_nonneg
#print axioms mass_moments_nonneg
#print axioms combined_moments_nonneg

/-! ## The readouts are undistorted — the tie to the existing (ii) certificate

With the nonneg proven, Ep30's own on-domain certificate
(`slipPointVarianceNumeratorSigned_toNat`) applies at each real site: the Nat variance
numerator the report reads equals the true signed value exactly — no truncation occurred
at any live site. The (ii) totalization guards the off-domain case; the (i) earn shows
the live sites never leave the domain. -/

theorem charge_readout_undistorted :
    (slipPointVarianceNumeratorSigned
        (chargeTripletValueSum assayLower assayUpper)
        (chargeTripletSquareSum assayLower assayUpper)
        (chargeTripletCubeSum assayLower assayUpper)).toNat
      = chargeTripletCubeSum assayLower assayUpper
          * chargeTripletValueSum assayLower assayUpper
        - square (chargeTripletSquareSum assayLower assayUpper) :=
  slipPointVarianceNumeratorSigned_toNat _ _ _ charge_moments_nonneg

theorem mass_readout_undistorted :
    (slipPointVarianceNumeratorSigned
        (massTripletValueSum assayLower assayUpper)
        (massTripletSquareSum assayLower assayUpper)
        (massTripletCubeSum assayLower assayUpper)).toNat
      = massTripletCubeSum assayLower assayUpper
          * massTripletValueSum assayLower assayUpper
        - square (massTripletSquareSum assayLower assayUpper) :=
  slipPointVarianceNumeratorSigned_toNat _ _ _ mass_moments_nonneg

/-- COMBINED site — the third live site, so "no truncation at any live site" is proven
on the page at all three, not asserted at two. -/
theorem combined_readout_undistorted :
    (slipPointVarianceNumeratorSigned
        (chargeTripletValueSum assayLower assayUpper
          + massTripletValueSum assayLower assayUpper)
        (chargeTripletSquareSum assayLower assayUpper
          + massTripletSquareSum assayLower assayUpper)
        (chargeTripletCubeSum assayLower assayUpper
          + massTripletCubeSum assayLower assayUpper)).toNat
      = (chargeTripletCubeSum assayLower assayUpper
          + massTripletCubeSum assayLower assayUpper)
          * (chargeTripletValueSum assayLower assayUpper
              + massTripletValueSum assayLower assayUpper)
        - square (chargeTripletSquareSum assayLower assayUpper
              + massTripletSquareSum assayLower assayUpper) :=
  slipPointVarianceNumeratorSigned_toNat _ _ _ combined_moments_nonneg

#print axioms charge_readout_undistorted
#print axioms mass_readout_undistorted
#print axioms combined_readout_undistorted

#eval s!"C-S at the real window: charge {decide (square (chargeTripletSquareSum assayLower assayUpper) ≤ chargeTripletCubeSum assayLower assayUpper * chargeTripletValueSum assayLower assayUpper)} / mass {decide (square (massTripletSquareSum assayLower assayUpper) ≤ massTripletCubeSum assayLower assayUpper * massTripletValueSum assayLower assayUpper)} — proven, not marked"

end Measurement.MomentsNonneg
