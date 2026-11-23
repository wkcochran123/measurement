/-
The derivative, as Mathlib reads it, from the device's brackets.

Episode 13 has the residual's step exact: the slope by the step, and thirteen by the step squared, and nothing else; and
it has that the slope is the only linear part that leaves a multiple of the step squared.  Here the reals are handed in,
the step goes to nothing, and the bracket becomes Mathlib's derivative.  The exponential is its own derivative, and e is
the limit of one and one part in n, n times.  The device's turning, n and the quarter phase k times, is one and the
quarter turn by one part in n, k times; taken n times it goes to the exponential of the quarter turn.  Every statement
here bills choice, because Mathlib's reals do.
-/
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Measurement.Episode13

namespace Calibrate
open Filter Topology Asymptotics

noncomputable section

--| The residual, on the reals.
def theResidual (y : ℝ) : ℝ := 13 * y * y - 36 * y + 18

--| THE BRACKET.  The residual's step less the slope by the step is thirteen by the step squared, exactly.
theorem the_residuals_bracket (y h : ℝ) :
    theResidual (y + h) - theResidual y - h * (26 * y - 36) = 13 * h ^ 2 := by
  unfold theResidual; ring

--| THE DERIVATIVE, FROM THE BRACKET.  Thirteen by the step squared is small beside the step, so the slope is the derivative.
theorem the_slope_is_the_derivative (y : ℝ) : HasDerivAt theResidual (26 * y - 36) y := by
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  have e : (fun h => theResidual (y + h) - theResidual y - h • (26 * y - 36)) = fun h => 13 * h ^ 2 := by
    funext h; rw [smul_eq_mul]; exact the_residuals_bracket y h
  rw [e]
  exact (isLittleO_pow_id (by norm_num : 1 < 2)).const_mul_left 13

--| THE EXPONENTIAL IS ITS OWN DERIVATIVE.
theorem the_exponential_is_its_own_derivative (x : ℝ) : HasDerivAt Real.exp (Real.exp x) x := Real.hasDerivAt_exp x

--| e IS THE LIMIT OF ONE AND ONE PART IN n, n TIMES.
theorem e_is_the_limit_of_the_growing_steps :
    Tendsto (fun n : ℕ => (1 + 1 / (n : ℝ)) ^ n) atTop (𝓝 (Real.exp 1)) :=
  Real.tendsto_one_add_div_pow_exp 1

--| THE DEVICE'S TURNING, READ AS A COMPLEX NUMBER.
def asComplex (p : ℤ × ℤ) : ℂ := (p.1 : ℂ) + (p.2 : ℂ) * Complex.I

theorem the_gaussian_product_is_the_product (p q : ℤ × ℤ) :
    asComplex (Measurement.the_gaussian_product p q) = asComplex p * asComplex q := by
  unfold asComplex Measurement.the_gaussian_product
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

theorem the_turning_walk_is_a_power (n : ℤ) (k : ℕ) :
    asComplex (Measurement.the_phase_walk (Measurement.the_step_of_a_turn n) k) = ((n : ℂ) + Complex.I) ^ k := by
  induction k with
  | zero => simp [Measurement.the_phase_walk, asComplex]
  | succ k ih =>
    show asComplex (Measurement.the_gaussian_product _ _) = _
    rw [the_gaussian_product_is_the_product, ih, pow_succ]
    simp [asComplex, Measurement.the_step_of_a_turn]

--| THE TURNING GOES TO THE EXPONENTIAL OF THE QUARTER TURN.  n and the quarter phase, n times, over n to the n.
theorem the_turning_goes_to_the_exponential_of_the_quarter_turn :
    Tendsto (fun n : ℕ => asComplex (Measurement.the_phase_walk (Measurement.the_step_of_a_turn n) n) / (n : ℂ) ^ n)
      atTop (𝓝 (Complex.exp Complex.I)) := by
  have lim := Complex.tendsto_one_add_div_pow_exp Complex.I
  refine lim.congr' ?_
  filter_upwards [eventually_ne_atTop 0] with n hn
  rw [the_turning_walk_is_a_power, ← div_pow]
  congr 1
  have : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  field_simp
  push_cast
  ring

end
end Calibrate
