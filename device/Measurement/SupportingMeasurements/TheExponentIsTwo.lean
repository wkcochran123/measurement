-- TheExponentIsTwo.lean
--
-- The counted mechanism behind the audit desk's three cards, stated as
-- kernel receipts on the device's OWN objects (Episode 10). Operator
-- directive 2026-08-21: "write the proof using the device. then write
-- the paper." This leaf is the proof; the paper exhibits it.
--
-- NOT-CLAIMED (load-bearing, per both chairs' fences 2026-08-21):
--   * No statement below mentions a magnetic dipole, a magnetic moment,
--     g-2, spin, or any physics name. The device counts a slip of two
--     and a squared separation; what a reader steeped in physics SEES in
--     that structure is the reader's, and the device does not lend its
--     kernel authority across that line. Resemblance is still a bridge.
--   * The device's own spin-adjacent object (the nowtrino, Episode 5)
--     stays behind its standing future-work fence; it appears in no
--     statement here.
--   * The exponent's ORIGIN -- that the slip law reads as the second
--     variation, hence inverse-square -- is Episode 10's stated model,
--     cited not re-derived. What THIS leaf certifies is the counted
--     structure: the separation is a performed count, the squaring is
--     really present, the cards are one number read three ways, the
--     crossing is taken with a proven square root, and the resulting
--     ratio agrees with the frozen record to the print's own floor --
--     agreement, never identity.

import Measurement.Episode10

namespace Measurement.TheExponentIsTwo

-- Kernel evaluation of the finished computations needs unfolding room;
-- this raises the elaborator's recursion budget only, adds no axiom.
set_option maxRecDepth 100000

-- ## The count is performed, not asserted
-- The separation is the length of the coproduct roster (addition earned
-- via Sum, per the standing rule); it lands on three.
theorem the_count_is_performed : theSeparation = 3 := by decide

-- The only input is the pair: the slip IS the two boxes.
theorem the_slip_is_the_pair : theObservedSlip = theTwoBoxes := rfl

-- ## The squaring is really present
-- The coupling is the slip times the separation to the SECOND power --
-- stated with the exponent as an exponent, so the claim is the type's.
theorem the_exponent_is_two :
    theCoupling = theObservedSlip * theSeparation ^ 2 := by decide

-- The exponent is exactly two: one power less or one power more misses
-- the coupling, in the device's own numbers.
theorem not_one_and_not_three :
    theCoupling ≠ theObservedSlip * theSeparation ^ 1 ∧
    theCoupling ≠ theObservedSlip * theSeparation ^ 3 := by decide

-- ## One number read three ways
-- The outer cards are the SAME coupling -- the structure is symmetric
-- about the count, and no third number enters.
theorem one_number_three_ways :
    cardC = cardR ∧ cardT = theCoupling / theTwoBoxes ^ 2 + 1 := by decide

-- The cards, laid: [18, 5, 18].
theorem the_cards : (cardC, cardT, cardR) = (18, 5, 18) := by decide

-- ## The crossing is taken with a proven root
-- The bracket comes from FloorSqrt's total-correctness theorem applied
-- at the audit's own argument -- not re-proved, INHERITED.
theorem the_crossing_is_bracketed :
    dStarScaled * dStarScaled ≤ cardC * alphaScale * alphaScale / cardT ∧
    cardC * alphaScale * alphaScale / cardT
      < (dStarScaled + 1) * (dStarScaled + 1) :=
  Measurement.FloorSqrt.floorSqrt_correct _

-- The crossing's value, pinned at the working scale.
theorem the_crossing_value : dStarScaled = 1897366596 := by decide

-- ## The reading, and its honest relation to the frozen record
-- The audit's ratio, pinned exactly as the build prints it.
theorem the_ratio_exact :
    invAlphaJar = (614746777104, 4486832980) := by decide

-- Agreement to the print's floor: the ratio's leading ten figures equal
-- the frozen record's leading ten figures. This is the strongest claim
-- a 1e9-scale dial can certify about a 1e18-scale record -- agreement
-- across every figure the dial can resolve, and NOT identity.
theorem agreement_to_the_floor :
    (dStarScaled * cardR * cardR) * 1000000000
        / ((dStarScaled - alphaScale) * cardT) / 100
      = 137011290548979455469 / 10 ^ 11 := by decide

-- Distinctness, kept in view so agreement is never oversold: at one
-- more digit of the frozen record, the two part company.
theorem and_not_identity :
    (dStarScaled * cardR * cardR) * 1000000000
        / ((dStarScaled - alphaScale) * cardT) / 10
      ≠ 137011290548979455469 / 10 ^ 10 := by decide

end Measurement.TheExponentIsTwo

#print axioms Measurement.TheExponentIsTwo.the_count_is_performed
#print axioms Measurement.TheExponentIsTwo.the_exponent_is_two
#print axioms Measurement.TheExponentIsTwo.not_one_and_not_three
#print axioms Measurement.TheExponentIsTwo.one_number_three_ways
#print axioms Measurement.TheExponentIsTwo.the_crossing_is_bracketed
#print axioms Measurement.TheExponentIsTwo.the_crossing_value
#print axioms Measurement.TheExponentIsTwo.the_ratio_exact
#print axioms Measurement.TheExponentIsTwo.agreement_to_the_floor
#print axioms Measurement.TheExponentIsTwo.and_not_identity
