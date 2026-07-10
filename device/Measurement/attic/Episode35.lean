import Measurement.Episode34

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000
set_option allowUnsafeReducibility true

namespace Measurement

/-
__EPISODE 35__: _The Anchor Earns Its Keep_

Episode34 got coercivity the cheap way: the mass term `M` pinned every node, so
`K = M + S` was positive-definite before the boundary anchor did anything.

This episode drops the heartbeat mass.  The operator is now stiffness alone,

  K = S,

which is only positive *semi*-definite: on the unanchored chain the constant
mode `(t, t, t)` sits in the nullspace, `S (t,t,t) (t,t,t) = 0`.  Coercivity has
to come from somewhere else.

It comes from the boundary.  The carrier `AnchoredRung` builds in the
`.white_hole -> .load` Dirichlet pin: node `0` is fixed at `0` (the load node is
the anchor, `trace .load = 0`).  That pin turns the first edge term into `c1^2`,
which kills the constant mode and restores positive-definiteness.

Stated formally:
* `Rung3.stiffOnly` is `S` with no mass, and `unanchored_kernel_nontrivial`
  exhibits a nonzero element of its nullspace.
* `AnchoredRung` is the pinned carrier; `AnchoredRung.stiff` is `S` after the
  load anchor; `AnchoredRung.stiff_pd` proves the diagonal now detects zero.
* `anchoredFirstDerivativeModel` is Episode29's `FirstDerivativeNullspaceModel`:
  diagonal zero -> flat (constant) mode -> the load anchor kills it -> zero.
* `anchoredSPD : SPDGalerkinActivity` is the resulting SPD, with coercivity
  sourced entirely by `.white_hole -> .load`, not by mass.

Residue left:
This is still one fixed three-rung chain.  Episode36 proves the same coercivity
for a general finite stage graph (discrete Poincare).
-/

/-- Stiffness with no mass on the *unanchored* three rungs. -/
def Rung3.stiffOnly (x y : Rung3) : Int :=
  (x.c1 - x.c0) * (y.c1 - y.c0) + (x.c2 - x.c1) * (y.c2 - y.c1)

/-- Without the anchor, the constant mode `(1,1,1)` is a nonzero nullspace
element: stiffness alone is not coercive. -/
theorem unanchored_kernel_nontrivial :
    Rung3.stiffOnly ⟨1, 1, 1⟩ ⟨1, 1, 1⟩ = 0 ∧ (⟨1, 1, 1⟩ : Rung3) ≠ Rung3.zero := by
  refine ⟨by decide, by decide⟩

/-- The anchored carrier: node `0` is pinned to `0` by `.white_hole -> .load`,
so only the two free nodal values `c1, c2` remain. -/
structure AnchoredRung where
  c1 : Int
  c2 : Int
deriving DecidableEq

namespace AnchoredRung

def zero : AnchoredRung := ⟨0, 0⟩

def add (x y : AnchoredRung) : AnchoredRung := ⟨x.c1 + y.c1, x.c2 + y.c2⟩

def neg (x : AnchoredRung) : AnchoredRung := ⟨-x.c1, -x.c2⟩

def smul (k : Int) (x : AnchoredRung) : AnchoredRung := ⟨k * x.c1, k * x.c2⟩

/-- Stiffness after the anchor.  The first term `c1 * c1` is the edge from the
pinned load node `0` to node `1`; it exists only because node `0 = 0`. -/
def stiff (x y : AnchoredRung) : Int :=
  x.c1 * y.c1 + (x.c2 - x.c1) * (y.c2 - y.c1)

theorem stiff_symm (x y : AnchoredRung) : stiff x y = stiff y x := by
  simp only [stiff]; simp [Int.mul_comm]

theorem stiff_add_left (x y z : AnchoredRung) :
    stiff (add x y) z = stiff x z + stiff y z := by
  simp only [stiff, add, Int.add_mul, Int.sub_mul] <;> omega

theorem stiff_smul_left (k : Int) (x y : AnchoredRung) :
    stiff (smul k x) y = k * stiff x y := by
  simp only [stiff, smul, Int.sub_mul, Int.mul_sub, Int.mul_add, Int.mul_assoc] <;> omega

theorem stiff_zero_left (x : AnchoredRung) : stiff zero x = 0 := by
  simp [stiff, zero]

theorem stiff_nonneg (x : AnchoredRung) : 0 <= stiff x x := by
  simp only [stiff]
  have a1 := sqDiag_nonneg x.c1
  have a2 := sqDiag_nonneg (x.c2 - x.c1)
  omega

/-- The diagonal vanishing forces both edges flat: `c1 = 0` (the anchor edge)
and `c2 = c1` (the interior edge). -/
theorem stiff_diag_zero_edges (x : AnchoredRung) (h : stiff x x = 0) :
    x.c1 = 0 ∧ x.c2 = x.c1 := by
  simp only [stiff] at h
  have a1 := sqDiag_nonneg x.c1
  have a2 := sqDiag_nonneg (x.c2 - x.c1)
  have e1 : x.c1 * x.c1 = 0 := by omega
  have e2 : (x.c2 - x.c1) * (x.c2 - x.c1) = 0 := by omega
  have z1 : x.c1 = 0 := sqDiag_eq_zero e1
  have z2 : x.c2 - x.c1 = 0 := sqDiag_eq_zero e2
  exact ⟨z1, by omega⟩

/-- Coercivity, now sourced by the anchor: `K x x = 0 -> x = 0`. -/
theorem stiff_pd (x : AnchoredRung) (h : stiff x x = 0) : x = zero := by
  obtain ⟨z1, z2⟩ := stiff_diag_zero_edges x h
  have hc2 : x.c2 = 0 := by omega
  cases x; simp_all [zero]

end AnchoredRung

/-- `K = S` (no mass) as an Episode28 symmetric bilinear form on the anchored
carrier. -/
def anchoredForm : GalerkinBilinearForm where
  V := AnchoredRung
  zero := AnchoredRung.zero
  add := AnchoredRung.add
  neg := AnchoredRung.neg
  smul := AnchoredRung.smul
  a := AnchoredRung.stiff
  symmetric := AnchoredRung.stiff_symm
  add_left := AnchoredRung.stiff_add_left
  smul_left := AnchoredRung.stiff_smul_left
  zero_left := AnchoredRung.stiff_zero_left
  nonnegative_diagonal := AnchoredRung.stiff_nonneg

def anchoredNaturalBoundary : NaturalBoundary anchoredForm where
  boundary_terms_vanish := True
  boundary_terms_vanish_proof := trivial

/-- The load node traces to zero: this is the `.white_hole -> .load` pin. -/
def anchoredWhiteHoleLoadAnchor : WhiteHoleLoadAnchor anchoredForm where
  trace := fun _ => AnchoredRung.zero
  load_is_anchor := rfl
  source_to_load := True
  source_to_load_proof := trivial

/-- Episode29's first-derivative nullspace model, concretely realized: the
diagonal vanishing gives a flat mode, and the load anchor kills it. -/
def anchoredFirstDerivativeModel :
    FirstDerivativeNullspaceModel anchoredForm anchoredWhiteHoleLoadAnchor where
  ConstantMode := fun x => x.c1 = 0 ∧ x.c2 = x.c1
  diagonal_zero_implies_constant := by
    intro x h
    exact AnchoredRung.stiff_diag_zero_edges x h
  whiteHoleLoadAnchor_kills_constant := by
    intro x hConstant _hAnchor
    obtain ⟨z1, z2⟩ := hConstant
    have hc2 : x.c2 = 0 := by omega
    show x = AnchoredRung.zero
    cases x; simp_all [AnchoredRung.zero]

def anchoredFirstDerivativeActivity :
    FirstDerivativeAnchoredGalerkinActivity where
  form := anchoredForm
  natural := anchoredNaturalBoundary
  anchor := anchoredWhiteHoleLoadAnchor
  nullspaceModel := anchoredFirstDerivativeModel

/-- The SPD whose coercivity is carried by `.white_hole -> .load`, not by mass. -/
def anchoredSPD : SPDGalerkinActivity :=
  FirstDerivativeAnchoredGalerkinActivity.toSPDGalerkinActivity
    anchoredFirstDerivativeActivity

noncomputable def anchoredEnergySqCertificate :
    EnergySqCertificate anchoredSPD.form.V :=
  SPDGalerkinActivity.toEnergySqCertificate anchoredSPD

theorem anchored_energySq_zero_detector
    (x : anchoredSPD.form.V) :
    anchoredEnergySqCertificate.energySq x = 0 <->
      x = anchoredEnergySqCertificate.zero :=
  EnergySqCertificate.energySq_eq_zero_iff_eq_zero
    anchoredEnergySqCertificate
    x

end Measurement
