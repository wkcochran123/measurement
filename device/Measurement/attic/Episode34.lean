import Measurement.Episode33

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000
set_option allowUnsafeReducibility true

namespace Measurement

/-
__EPISODE 34__: _The First Real Stiffness_

Episode28 built the SPD Galerkin machine over a generic `GalerkinBilinearForm`,
but the only model ever exhibited was `truthGalerkinBilinearForm`: carrier
`Unit`, form `a = 0`, positive-definiteness vacuous.  The cathedral was wired to
a single point.

This episode installs the first genuinely finite-dimensional form: a concrete
three-rung path with nodal values `(c0, c1, c2)` and the assembled operator

  K = M + S

where `M` is the mass (diagonal / L^2) term and `S` is the stiffness (discrete
derivative-squared / graph-Laplacian) term over the two edges of the chain.

Stated formally:
* `Rung3` is the three-node carrier with componentwise `add`, `neg`, `smul`.
* `Rung3.mass`/`Rung3.stiff` are the two symmetric bilinear pieces, and
  `Rung3.aMS = mass + stiff` is `K`.
* `threeRungForm : GalerkinBilinearForm` discharges all five form axioms for `K`.
* `Rung3.aMS_pd` proves the diagonal detects zero: `K x x = 0 -> x = 0`.
* `threeRungSPD : SPDGalerkinActivity` packages it through Episode28's
  `naturalBoundary_whiteHoleLoadAnchor_implies_spd`.
* `threeRung_energy_nontrivial` exhibits a nonzero energy, so this is not the
  `Unit` toy.

Claimed by interpretation:
The compiler emits a real finite-element operator.  Here coercivity is carried
by the mass term `M`: even with the stiffness alone degenerate, `M` pins every
node.  The white-hole/load anchor is present in the package but does no work
yet.

Residue left:
The mass term is the cheap source of coercivity.  Episode35 drops it and forces
the `.white_hole -> .load` boundary anchor to carry the nullspace kill instead.
-/

theorem sqDiag_nonneg (t : Int) : 0 <= t * t := by
  rcases Int.le_total 0 t with h | h
  · exact Int.mul_nonneg h h
  · have h2 : 0 <= (-t) * (-t) := Int.mul_nonneg (by omega) (by omega)
    rwa [Int.neg_mul_neg] at h2

theorem sqDiag_eq_zero {t : Int} (h : t * t = 0) : t = 0 := by
  rcases Int.mul_eq_zero.mp h with h | h <;> exact h

structure Rung3 where
  c0 : Int
  c1 : Int
  c2 : Int
deriving DecidableEq

namespace Rung3

def zero : Rung3 := ⟨0, 0, 0⟩

def add (x y : Rung3) : Rung3 := ⟨x.c0 + y.c0, x.c1 + y.c1, x.c2 + y.c2⟩

def neg (x : Rung3) : Rung3 := ⟨-x.c0, -x.c1, -x.c2⟩

def smul (k : Int) (x : Rung3) : Rung3 := ⟨k * x.c0, k * x.c1, k * x.c2⟩

/-- Mass term `M`: the diagonal / L^2 inner product. -/
def mass (x y : Rung3) : Int :=
  x.c0 * y.c0 + x.c1 * y.c1 + x.c2 * y.c2

/-- Stiffness term `S`: the discrete derivative squared over the two edges. -/
def stiff (x y : Rung3) : Int :=
  (x.c1 - x.c0) * (y.c1 - y.c0) + (x.c2 - x.c1) * (y.c2 - y.c1)

/-- The assembled operator `K = M + S`. -/
def aMS (x y : Rung3) : Int := mass x y + stiff x y

theorem aMS_symm (x y : Rung3) : aMS x y = aMS y x := by
  simp only [aMS, mass, stiff]; simp [Int.mul_comm]

theorem aMS_add_left (x y z : Rung3) : aMS (add x y) z = aMS x z + aMS y z := by
  simp only [aMS, mass, stiff, add, Int.add_mul, Int.sub_mul] <;> omega

theorem aMS_smul_left (k : Int) (x y : Rung3) : aMS (smul k x) y = k * aMS x y := by
  simp only [aMS, mass, stiff, smul, Int.sub_mul, Int.mul_sub, Int.mul_add,
    Int.mul_assoc] <;> omega

theorem aMS_zero_left (x : Rung3) : aMS zero x = 0 := by
  simp [aMS, mass, stiff, zero]

theorem aMS_nonneg (x : Rung3) : 0 <= aMS x x := by
  simp only [aMS, mass, stiff]
  have a0 := sqDiag_nonneg x.c0
  have a1 := sqDiag_nonneg x.c1
  have a2 := sqDiag_nonneg x.c2
  have a3 := sqDiag_nonneg (x.c1 - x.c0)
  have a4 := sqDiag_nonneg (x.c2 - x.c1)
  omega

/-- Coercivity from the mass term: `K x x = 0` forces every node to zero. -/
theorem aMS_pd (x : Rung3) (h : aMS x x = 0) : x = zero := by
  simp only [aMS, mass, stiff] at h
  have a0 := sqDiag_nonneg x.c0
  have a1 := sqDiag_nonneg x.c1
  have a2 := sqDiag_nonneg x.c2
  have a3 := sqDiag_nonneg (x.c1 - x.c0)
  have a4 := sqDiag_nonneg (x.c2 - x.c1)
  have e0 : x.c0 * x.c0 = 0 := by omega
  have e1 : x.c1 * x.c1 = 0 := by omega
  have e2 : x.c2 * x.c2 = 0 := by omega
  have z0 : x.c0 = 0 := sqDiag_eq_zero e0
  have z1 : x.c1 = 0 := sqDiag_eq_zero e1
  have z2 : x.c2 = 0 := sqDiag_eq_zero e2
  cases x; simp_all [zero]

end Rung3

/-- `K = M + S` as an Episode28 symmetric bilinear form. -/
def threeRungForm : GalerkinBilinearForm where
  V := Rung3
  zero := Rung3.zero
  add := Rung3.add
  neg := Rung3.neg
  smul := Rung3.smul
  a := Rung3.aMS
  symmetric := Rung3.aMS_symm
  add_left := Rung3.aMS_add_left
  smul_left := Rung3.aMS_smul_left
  zero_left := Rung3.aMS_zero_left
  nonnegative_diagonal := Rung3.aMS_nonneg

def threeRungNaturalBoundary : NaturalBoundary threeRungForm where
  boundary_terms_vanish := True
  boundary_terms_vanish_proof := trivial

def threeRungWhiteHoleLoadAnchor : WhiteHoleLoadAnchor threeRungForm where
  trace := fun _ => Rung3.zero
  load_is_anchor := rfl
  source_to_load := True
  source_to_load_proof := trivial

def threeRungNullspaceKilled :
    NullspaceKilled
      threeRungForm
      threeRungNaturalBoundary
      threeRungWhiteHoleLoadAnchor where
  uses_natural_boundary := trivial
  uses_white_hole_load := trivial
  diagonal_zero_detects := by
    intro x h
    exact Rung3.aMS_pd x h

/-- The first nontrivial SPD Galerkin activity: `K = M + S` on three rungs. -/
def threeRungSPD : SPDGalerkinActivity :=
  SPDGalerkinActivity.naturalBoundary_whiteHoleLoadAnchor_implies_spd
    threeRungForm
    threeRungNaturalBoundary
    threeRungWhiteHoleLoadAnchor
    threeRungNullspaceKilled

noncomputable def threeRungEnergySqCertificate :
    EnergySqCertificate threeRungSPD.form.V :=
  SPDGalerkinActivity.toEnergySqCertificate threeRungSPD

/-- This is not the `Unit` toy: a single excited node carries energy `2`. -/
theorem threeRung_energy_nontrivial :
    threeRungForm.a ⟨1, 0, 0⟩ ⟨1, 0, 0⟩ = 2 := by
  decide

theorem threeRung_energySq_zero_detector
    (x : threeRungSPD.form.V) :
    threeRungEnergySqCertificate.energySq x = 0 <->
      x = threeRungEnergySqCertificate.zero :=
  EnergySqCertificate.energySq_eq_zero_iff_eq_zero
    threeRungEnergySqCertificate
    x

end Measurement
