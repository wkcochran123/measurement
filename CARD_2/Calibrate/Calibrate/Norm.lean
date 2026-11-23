/-
The norm of the table, as Mathlib reads it.

Episode 13 walls the norm of the table in whole numbers: the weighed square of what the table gives is never past seven
hundred and fifty-six of what went in, and one pair passes seven hundred and fifty-five; in the surd pairs the norm is
reached.  Here the reals are handed in, and the norm is a number.

Weigh the two coins by eighteen and five, take the root of each weight, and the coins become the plane with its ordinary
length.  The table, carried across, is eighteen on the diagonal and the root of ninety off it, the same turned over.  Its
operator norm, Mathlib's `‖·‖` on continuous linear maps, is eighteen and the root of ninety.  So on the coins, for every
pair, the weighed square of what the table gives is never past the square of that, and the direction five and the root
reaches it.  That square lies between Episode 13's two walls.

The reals and their completion are Mathlib's.  They are handed in here and nowhere in the device.  Every statement here
bills `Classical.choice`, because Mathlib's reals do.
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Measurement.Episode13

namespace Calibrate
open Real

noncomputable section

--| The plane with its ordinary length.
abbrev ThePlane := EuclideanSpace ℝ (Fin 2)

--| The root of the round trip.
def theRoot : ℝ := √90

theorem theRoot_squared : theRoot * theRoot = 90 := Real.mul_self_sqrt (by norm_num)
theorem theRoot_nonneg : 0 ≤ theRoot := Real.sqrt_nonneg _
theorem theRoot_is_the_roots_of_the_weights : theRoot = √5 * √18 := by
  rw [theRoot, ← Real.sqrt_mul (by norm_num)]; norm_num

--| THE TABLE, CARRIED ACROSS.  Eighteen on the diagonal, the root of ninety off it: the same turned over.
def theCarriedTable : Matrix (Fin 2) (Fin 2) ℝ := !![18, theRoot; theRoot, 18]
def theOperator : ThePlane →L[ℝ] ThePlane := LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin theCarriedTable)

theorem theOperator_apply (x : ThePlane) :
    theOperator x 0 = 18 * x 0 + theRoot * x 1 ∧ theOperator x 1 = theRoot * x 0 + 18 * x 1 := by
  simp [theOperator, theCarriedTable, Matrix.toEuclideanLin_apply, dotProduct, Fin.sum_univ_two]

theorem theOperator_is_never_past (x : ThePlane) : ‖theOperator x‖ ≤ (18 + theRoot) * ‖x‖ := by
  have hx := EuclideanSpace.norm_sq_eq x
  have hT := EuclideanSpace.norm_sq_eq (theOperator x)
  simp only [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs] at hx hT
  obtain ⟨h0, h1⟩ := theOperator_apply x
  rw [h0, h1] at hT
  have hs := theRoot_squared; have hs0 := theRoot_nonneg
  have key : ‖theOperator x‖ ^ 2 ≤ ((18 + theRoot) * ‖x‖) ^ 2 := by
    rw [mul_pow, hT, hx]
    nlinarith [sq_nonneg (x 0 - x 1), mul_nonneg hs0 (sq_nonneg (x 0 - x 1))]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 key

--| THE OPERATOR NORM.  Never past eighteen and the root, and the direction one and one reaches it.
theorem the_operator_norm_of_the_table : ‖theOperator‖ = 18 + theRoot := by
  apply le_antisymm
  · exact ContinuousLinearMap.opNorm_le_bound _ (by have := theRoot_nonneg; linarith) theOperator_is_never_past
  · let e : ThePlane := WithLp.toLp 2 ![1, 1]
    have he : theOperator e = (18 + theRoot) • e := by
      ext i; fin_cases i <;> simp [e, theOperator, theCarriedTable, Matrix.toEuclideanLin_apply, add_comm]
    have hne : 0 < ‖e‖ := by
      rw [norm_pos_iff]; intro h
      have := congrArg (fun v : ThePlane => v 0) h
      simp [e] at this
    have := theOperator.le_opNorm e
    rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by have := theRoot_nonneg; linarith)] at this
    exact le_of_mul_le_mul_right this hne

--| ON THE COINS.  The weighed square, and the device's own table read on real coins.
def theWeighedSquare (v : Bool → ℝ) : ℝ := 18 * (v true * v true) + 5 * (v false * v false)
def theTableOnTheCoins (v : Bool → ℝ) : Bool → ℝ :=
  fun x => (Measurement.the_full_table x true : ℝ) * v true + (Measurement.the_full_table x false : ℝ) * v false

theorem theTableOnTheCoins_is_written (v : Bool → ℝ) :
    theTableOnTheCoins v true = 18 * v true + 5 * v false
      ∧ theTableOnTheCoins v false = 18 * v true + 18 * v false := by
  have e1 : Measurement.the_full_table true true = 18 := by decide
  have e2 : Measurement.the_full_table true false = 5 := by decide
  have e3 : Measurement.the_full_table false true = 18 := by decide
  have e4 : Measurement.the_full_table false false = 18 := by decide
  simp [theTableOnTheCoins, e1, e2, e3, e4]

--| The root of each weight takes the coins to the plane, and the weighed square to the length squared.
def toThePlane (v : Bool → ℝ) : ThePlane := WithLp.toLp 2 ![√18 * v true, √5 * v false]

theorem the_length_is_the_weighed_square (v : Bool → ℝ) : ‖toThePlane v‖ ^ 2 = theWeighedSquare v := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs, toThePlane, theWeighedSquare]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  have h18 : √18 * √18 = 18 := Real.mul_self_sqrt (by norm_num)
  have h5 : √5 * √5 = 5 := Real.mul_self_sqrt (by norm_num)
  nlinarith [h18, h5]

--| The table on the coins, carried to the plane, is the operator on the plane.
theorem the_table_carried_is_the_operator (v : Bool → ℝ) :
    toThePlane (theTableOnTheCoins v) = theOperator (toThePlane v) := by
  obtain ⟨t1, t2⟩ := theTableOnTheCoins_is_written v
  have h18 : √18 * √18 = 18 := Real.mul_self_sqrt (by norm_num)
  have h5 : √5 * √5 = 5 := Real.mul_self_sqrt (by norm_num)
  ext i; fin_cases i
  · simp only [toThePlane, t1, theOperator_apply, Fin.zero_eta, WithLp.ofLp_toLp, Matrix.cons_val_zero, Matrix.cons_val_one,
      theRoot_is_the_roots_of_the_weights]
    show √18 * (18 * v true + 5 * v false) = 18 * (√18 * v true) + √5 * √18 * (√5 * v false)
    linear_combination (-(√18 * v false)) * h5
  · simp only [toThePlane, t2, theOperator_apply, Fin.mk_one, WithLp.ofLp_toLp, Matrix.cons_val_zero, Matrix.cons_val_one,
      theRoot_is_the_roots_of_the_weights]
    show √5 * (18 * v true + 18 * v false) = √5 * √18 * (√18 * v true) + 18 * (√5 * v false)
    linear_combination (-(√5 * v true)) * h18

--| THE NORM ON THE COINS.  For every pair, the weighed square of what the device's table gives is never past the square of
--| the operator norm times the weighed square of what went in.
theorem the_table_on_the_coins_is_never_past (v : Bool → ℝ) :
    theWeighedSquare (theTableOnTheCoins v) ≤ ‖theOperator‖ ^ 2 * theWeighedSquare v := by
  rw [← the_length_is_the_weighed_square, ← the_length_is_the_weighed_square, the_table_carried_is_the_operator, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (theOperator.le_opNorm _) 2

--| And between Episode 13's walls: past seven hundred and fifty-five, not past seven hundred and fifty-six.
theorem the_norm_squared_is_between_the_walls : 755 < ‖theOperator‖ ^ 2 ∧ ‖theOperator‖ ^ 2 ≤ 756 := by
  rw [the_operator_norm_of_the_table]
  have hs := theRoot_squared; have hs0 := theRoot_nonneg
  constructor <;> nlinarith [sq_nonneg (theRoot - 341 / 36), sq_nonneg (theRoot - 342 / 36)]

end
end Calibrate
