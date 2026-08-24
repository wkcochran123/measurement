import Measurement.SupportingMeasurements.ConditionEntropy

/-! # SkeelCondition — the Skeel condition number of the ladder, exactly.

NAMING (operator, 2026-08-15 22:23): "this is the SKEEL condition number,
not the condition number." Robert Skeel's componentwise condition number,
cond(A) = ‖ |A⁻¹|·|A| ‖_∞ — row-scaling invariant, the conditioning of the
elementwise structure. ATTRIBUTION for the ledger: Robert D. Skeel
("Scaling for numerical stability in Gaussian elimination", JACM 1979);
carried here on instruments-not-authorities terms, with the operator's own
lineage on the record: Skeel taught the operator the Fréchet derivative.

WHAT IS PROVED (kernel, exact integers, per rung — no norms, no reals):
  * `inverse_verified` — the family's inverse is exhibited and CHECKED:
    A·B = I per rung (the candidate B is the unit upper-triangular of ones,
    which is exactly |A⁻¹| as well since its entries are 0/1).
  * `skeel_values` — the Skeel number ‖|A⁻¹||A|‖_∞ equals EXACTLY 2n−1 at
    every rung (max absolute row sum of |A⁻¹|·|A|, computed in integers).
  * `skeel_monotone_ladder` — it strictly increases along the refinement
    index: entropic in the device's bound-shaped sense.
  * `skeel_is_the_entropy_normalizer` — the identity that makes the
    operator's sentence LITERAL: the Skeel number equals the total diagonal
    energy t = Σᵢ‖A eᵢ‖² at every rung. Hence (header algebra, from
    EntropyLadder): H(n) = lg(Skeel) − (Skeel−1)/Skeel — THE ENTROPY OF THE
    SPECTRUM'S DISTRIBUTION IS A STRICTLY MONOTONE FUNCTION OF THE SKEEL
    CONDITION NUMBER. The conditioning is entropic, literally, with Skeel's
    object and Shannon's form joined by a kernel-checked identity.

THE THREE CONDITIONINGS, kept named apart (uncertified context, for
orientation): on this family the Skeel number is 2n−1 (linear, proven
here); the probe κ²-reading is 4n−3 (linear, ConditionEntropy); the
classical spectral κ² grows quadratically (≈113 at n=8, scipy context,
NOT certified, floor relation to the probe reading preserved). Three
different objects; the prose never floats a name across them.

NOT CLAIMED: the classical spectral condition number (uncertified gloss
only); any continuum object; any physical entropy. -/

namespace Measurement.WeakDiracGalerkin.SkeelCondition

open Measurement.WeakDiracGalerkin
open Measurement.WeakDiracGalerkin.ConditionEntropy

/-- The exhibited inverse: unit upper-triangular of ones — row i is
    eᵢ + eᵢ₊₁ + ⋯ + e_{n−1}. (Also equals |A⁻¹| entrywise: entries 0/1.) -/
def invRow (n i : Nat) : Vec :=
  (List.range n).map (fun j => if i ≤ j then (1 : Int) else 0)

def invRows (n : Nat) : List Vec :=
  (List.range n).map (invRow n)

/-- Matrix product row: (M·N) row i = [row i of M applied to columns of N],
    computed as matrixApply of N's transpose — here directly:
    entry (i,j) = Σₖ M[i][k]·N[k][j], via dotting M's row i with N's col j. -/
def col (rows : List Vec) (n j : Nat) : Vec :=
  rows.map (fun r => r.getD j 0)

def prodEntry (M N : List Vec) (n i j : Nat) : Int :=
  dot (M.getD i []) (col N n j)

def identityQ (M N : List Vec) (n : Nat) : Bool :=
  (List.range n).all (fun i =>
    (List.range n).all (fun j =>
      prodEntry M N n i j = (if i = j then 1 else 0)))

/-- The inverse is real: A·B = I at every checked rung, in exact integers. -/
theorem inverse_verified :
    identityQ (diracRowsN 2) (invRows 2) 2 = true ∧
    identityQ (diracRowsN 3) (invRows 3) 3 = true ∧
    identityQ (diracRowsN 4) (invRows 4) 4 = true ∧
    identityQ (diracRowsN 5) (invRows 5) 5 = true ∧
    identityQ (diracRowsN 6) (invRows 6) 6 = true ∧
    identityQ (diracRowsN 7) (invRows 7) 7 = true ∧
    identityQ (diracRowsN 8) (invRows 8) 8 = true := by decide

#print axioms inverse_verified

/-- |x| on Int. -/
def absI (x : Int) : Int := if x < 0 then -x else x

/-- Row i of |A⁻¹|·|A|, summed: Σⱼ |Σₖ |B[i][k]|·|A[k][j]|| — since all the
    entries of B are 0/1 and of A are 0/±1, the inner products are already
    nonnegative; we still take absolute values to compute Skeel's object
    literally. -/
def skeelRowSum (A B : List Vec) (n i : Nat) : Int :=
  ((List.range n).map (fun j =>
    absI ((List.range n).foldl (fun acc k =>
      acc + absI ((B.getD i []).getD k 0) * absI ((A.getD k []).getD j 0))
      0))).foldl (· + ·) 0

/-- Skeel number: the max row sum (∞-norm of |A⁻¹|·|A|). -/
def skeelNumber (n : Nat) : Int :=
  ((List.range n).map (fun i =>
    skeelRowSum (diracRowsN n) (invRows n) n i)).foldl max 0

/-- The Skeel condition number is exactly 2n−1 at every rung. -/
theorem skeel_values :
    skeelNumber 2 = 3 ∧ skeelNumber 3 = 5 ∧ skeelNumber 4 = 7 ∧
    skeelNumber 5 = 9 ∧ skeelNumber 6 = 11 ∧ skeelNumber 7 = 13 ∧
    skeelNumber 8 = 15 := by decide

#print axioms skeel_values

/-- Entropic growth of the Skeel conditioning: strictly increasing along the
    refinement index — a forward `<` that never turns around. -/
theorem skeel_monotone_ladder :
    skeelNumber 2 < skeelNumber 3 ∧ skeelNumber 3 < skeelNumber 4 ∧
    skeelNumber 4 < skeelNumber 5 ∧ skeelNumber 5 < skeelNumber 6 ∧
    skeelNumber 6 < skeelNumber 7 ∧ skeelNumber 7 < skeelNumber 8 := by decide

#print axioms skeel_monotone_ladder

/-- THE JOINT: the Skeel number equals the total diagonal energy at every
    rung — the exact normalizer of the entropy's distribution. With
    EntropyLadder's closed form H = lg t − (t−1)/t, this makes the entropy a
    strictly monotone function of the Skeel condition number: the
    conditioning is entropic, literally. -/
theorem skeel_is_the_entropy_normalizer :
    skeelNumber 2 = (diagEnergies 2).foldl (· + ·) 0 ∧
    skeelNumber 3 = (diagEnergies 3).foldl (· + ·) 0 ∧
    skeelNumber 4 = (diagEnergies 4).foldl (· + ·) 0 ∧
    skeelNumber 5 = (diagEnergies 5).foldl (· + ·) 0 ∧
    skeelNumber 6 = (diagEnergies 6).foldl (· + ·) 0 ∧
    skeelNumber 7 = (diagEnergies 7).foldl (· + ·) 0 ∧
    skeelNumber 8 = (diagEnergies 8).foldl (· + ·) 0 := by decide

#print axioms skeel_is_the_entropy_normalizer

/-! ## The parallelogram is Skeel's own (BM's area gate, answered on the
right object)

The Skeel product S = |A⁻¹|·|A| on this family is UPPER TRIANGULAR WITH
UNIT DIAGONAL — a unit-determinant SHEAR. det S = 1 (triangular, ones on
the diagonal), so S maps the unit cell to a parallelogram of area EXACTLY 1,
and the Skeel condition number ‖S‖_∞ reads how far that parallelogram is
sheared. "The condition number is an area-preserving shear's stretch, and it
makes a parallelogram" — kernel-exact, on Skeel's own object, no spectral
gloss anywhere: nothing created, everything stretched. -/

/-- Entry of the Skeel product S = |A⁻¹|·|A| (all inner terms nonnegative). -/
def skeelEntry (n i j : Nat) : Int :=
  (List.range n).foldl (fun acc k =>
    acc + absI (((invRows n).getD i []).getD k 0)
        * absI (((diracRowsN n).getD k []).getD j 0)) 0

/-- The Skeel product is a unit shear: ones on the diagonal, zeros below —
    hence det = 1 and the image of the unit cell is a parallelogram of area
    exactly 1, at every checked rung. -/
def unitShearQ (n : Nat) : Bool :=
  (List.range n).all (fun i =>
    skeelEntry n i i = 1 ∧
    (List.range n).all (fun j => decide (j < i) → skeelEntry n i j = 0))

theorem skeel_matrix_is_unit_shear :
    unitShearQ 2 = true ∧ unitShearQ 3 = true ∧ unitShearQ 4 = true ∧
    unitShearQ 5 = true ∧ unitShearQ 6 = true ∧ unitShearQ 7 = true ∧
    unitShearQ 8 = true := by decide

#print axioms skeel_matrix_is_unit_shear

end Measurement.WeakDiracGalerkin.SkeelCondition
