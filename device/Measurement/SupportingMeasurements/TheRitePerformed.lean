-- TheRitePerformed.lean
--
-- Operator directive 2026-08-21: "Starting in episode 5, a mathematical
-- procedure is described in very clear detail. Perform the calculus rite
-- describes." This leaf PERFORMS it, in a new file, with sacred Episode 5
-- byte-untouched (BM's Fence 1). The rite, as Episode 5 states it:
-- arrive at the local law (.the_newton); object that it is not relative;
-- take the first variation of it (.the_gateaux OF .the_newton), pointed
-- at .einstein; and send the traveler around -- once through the
-- blackhole, landing one universe UP, twice through the whitehole,
-- returning to the same Box. The numeric half of the performance
-- (count, cross, read) closes at 1e18 scale with the proven root.
--
-- NOT-CLAIMED (BM's Fence 2, same wall as TheExponentIsTwo):
--   * "Spin-2" appears in Episode 5 as a name the text itself
--     immediately fences (DONT_WORRY_..._FUTURE_WORK). No statement
--     below uses it. What is proved is the COUNT: one traversal does
--     not return to the Box; two do. The representation-theory name
--     stays where Episode 5 put it -- behind the future-work fence.
--   * The closed form pinned below is the ideal value of the audit's
--     crossing map. Its relation to the frozen record is stated as
--     agreement-at-a-resolution and distinctness beyond it -- never
--     identity, and never a claim about a laboratory constant.

import Measurement.Episode10

namespace Measurement.TheRitePerformed

set_option maxRecDepth 100000

universe i

-- ## Part I: the first variation is taken (the Gateaux of the Newton)
-- Episode 5's UNIVERSAL instance really does wrap the local law in its
-- first variation: the .the_gateaux node CONTAINS the .the_newton node.
-- The calculus is performed by the type; this theorem reads it back.
theorem the_first_variation_is_taken
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon]
    [COMPARABLE Box Pigeon]
    [SOURCE Box Pigeon]
    [yet: WITNESSED Box Pigeon]
    [flying_spaghetti_monster: REAL Box Pigeon]
    (nowtrino_model: LOCAL Box Pigeon) :
    (PROBLEM_IS_THE_DIFFERENTIAL_EQUATION_IS_NOT_RELATIVE_BUT_IT_SHOULD_BE
        Box Pigeon nowtrino_model).the_train_of_thought.the_local_schedule.differential_equation
      = .the_gateaux yet.the_experiment Fact.Truth.truth nowtrino.fact.truth
          (.the_newton yet.the_experiment nowtrino.fact.truth) := rfl

-- The variation is pointed at Einstein: the direction to the destination.
theorem pointed_at_einstein
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon]
    [COMPARABLE Box Pigeon]
    [SOURCE Box Pigeon]
    [WITNESSED Box Pigeon]
    [REAL Box Pigeon]
    (nowtrino_model: LOCAL Box Pigeon) :
    (PROBLEM_IS_THE_DIFFERENTIAL_EQUATION_IS_NOT_RELATIVE_BUT_IT_SHOULD_BE
        Box Pigeon nowtrino_model).the_train_of_thought.the_direction_to_the_destination
      = .einstein nowtrino.fact := rfl

-- ## Part II: once around does not return; twice around does
-- The traversal, read off the instance: ONE trip is the blackhole and
-- its carrier is the LIFTED box -- one universe up, not the Box you
-- left from. TWO trips is the whitehole and its carrier is Box itself.
-- The count is the pair of these two theorems side by side.
theorem once_around_lands_one_universe_up
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon]
    [COMPARABLE Box Pigeon]
    [SOURCE Box Pigeon]
    [WITNESSED Box Pigeon]
    [REAL Box Pigeon]
    (nowtrino_model: LOCAL Box Pigeon) :
    (PROBLEM_IS_THE_DIFFERENTIAL_EQUATION_IS_NOT_RELATIVE_BUT_IT_SHOULD_BE
        Box Pigeon nowtrino_model).once_around
      = .blackhole nowtrino.fact.truth (ULift.{i+1} Box) (.einstein nowtrino.fact) := rfl

theorem twice_around_returns_to_the_same_box
    (Box: Type i)
    (Pigeon: CarrierProcess Box)
    [nowtrino: DISTINGUISHABLE Box Pigeon]
    [COMPARABLE Box Pigeon]
    [SOURCE Box Pigeon]
    [WITNESSED Box Pigeon]
    [REAL Box Pigeon]
    (nowtrino_model: LOCAL Box Pigeon) :
    (PROBLEM_IS_THE_DIFFERENTIAL_EQUATION_IS_NOT_RELATIVE_BUT_IT_SHOULD_BE
        Box Pigeon nowtrino_model).twice_around
      = .whitehole nowtrino.fact Box (.einstein nowtrino.fact) := rfl

-- ## Part III: the numeric half, closed at 1e18 with the proven root
-- Performing the count-cross-read by hand and rationalizing gives the
-- crossing map's ideal value in closed form:
--     1/alpha = 324 d* / (5 (d* - 1)),  d* = sqrt(18/5)
--             = 972 (6 + sqrt 10) / 65.
-- Here that closed form is pinned at 1e18 scale with the SAME proven
-- integer square root the audit uses -- no reals, nothing imported.
def sqrtTenScaled : Nat :=
  Measurement.FloorSqrt.floorSqrt (10 * 10 ^ 36)

theorem sqrt_ten_pinned : sqrtTenScaled = 3162277660168379331 := by decide

def closedFormScaled : Nat :=
  (5832 * 10 ^ 18 + 972 * sqrtTenScaled) / 65

-- The ideal reading at 1e18: seventeen figures of it are decided here.
theorem closed_form_pinned : closedFormScaled = 137011290548979457072 := by decide

-- Agreement with the frozen record through the SEVENTEENTH significant
-- figure -- and distinctness at the eighteenth. The frozen record is a
-- different computation (the deep readout); the closed form is the
-- crossing map's ideal. They meet to seventeen figures and provably
-- part company after, which is agreement, never identity.
theorem seventeen_figures_agree :
    closedFormScaled / 10 ^ 4 = 137011290548979455469 / 10 ^ 4 := by decide

theorem and_the_eighteenth_differs :
    closedFormScaled / 10 ^ 3 ≠ 137011290548979455469 / 10 ^ 3 := by decide

-- The audit's own 1e9 print sits under the same closed form to the
-- print's full resolution: its ratio truncates the same ideal.
theorem the_audit_reads_the_same_ideal :
    (dStarScaled * cardR * cardR) * 1000000000
        / ((dStarScaled - alphaScale) * cardT) / 100
      = closedFormScaled / 10 ^ 11 := by decide

end Measurement.TheRitePerformed

#print axioms Measurement.TheRitePerformed.the_first_variation_is_taken
#print axioms Measurement.TheRitePerformed.pointed_at_einstein
#print axioms Measurement.TheRitePerformed.once_around_lands_one_universe_up
#print axioms Measurement.TheRitePerformed.twice_around_returns_to_the_same_box
#print axioms Measurement.TheRitePerformed.sqrt_ten_pinned
#print axioms Measurement.TheRitePerformed.closed_form_pinned
#print axioms Measurement.TheRitePerformed.seventeen_figures_agree
#print axioms Measurement.TheRitePerformed.and_the_eighteenth_differs
#print axioms Measurement.TheRitePerformed.the_audit_reads_the_same_ideal
