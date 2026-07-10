import Measurement.Episode56

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000
set_option allowUnsafeReducibility true

namespace Measurement

/-
__EPISODE 57__: _Boundary Radiation, Finite Edition_

The paper's Theorem 3 is the target the whole lane points at: if the
geometric and gauge certificate families stand orthogonal in the induced
pairing, and that orthogonality rules out an interior mixed scalar
certificate in the unmodified apparatus, then the observable remainder
reads as the boundary residual.  This episode proves the finite edition,
with every hypothesis carried by a filed object.

The algebra is Clifford's, in shadow: Clifford multiplication remembers a
quadratic form through

  c(u)c(v) + c(v)c(u) = -2 <u,v>,

so the anticommutator's scalar part IS the pairing, rescaled.  If the
geometric and gauge representatives are orthogonal, the scalar cross-term
is zero -- and a nonzero interior mixed scalar certificate would have to
change at least one structure that made the statement true: the pairing,
the form, the representation, or the product.  Inside the unmodified
apparatus there is nothing to write it with.  `CliffordShadow` carries the
relation; `no_interior_scalar_mixed_of_orthogonal` is the obstruction, one
`rw` and one arithmetic step; Episode56's split supplies the orthogonality
by type.  Stated at its own size: at this instance the obstruction is the
arithmetic conditional `x = 0 -> -2x = 0` applied to a pairing that is
definitionally zero across sectors -- the load-bearing content is the
CONDITIONAL SHAPE, ready for a pairing where orthogonality costs
something; the predicate is not yet tied to the corpus's certificate
machinery (`IsC2Certified`), and that tie is the upgrade surface.

With the interior closed, the remainder has one place left to read:
the boundary.  `generatedBoundaryResidue` packages the generated program's
observable remainder -- the excitation channel's pair coupling -- as a
boundary flux against the terminal residual, and
`generated_boundary_flux_eq_terminal_residual` says they agree: -1, the
electron, read at the boundary because the interior refused it.
`boundary_radiation_finite` is the package: orthogonality, no interior
mixed certificate, flux equals residual -- the three clauses of Theorem 3,
each checked, at the finite level.  Honest shape note: the paper's target
is an IMPLICATION (orthogonality and no-interior as hypotheses forcing
flux = residual); what is filed here is clauses verified at the instance,
with only 1 => 2 a genuine implication.  The implication shape itself is
not yet formalized, and the paper must say so.

Stated formally:
* `CliffordShadow`, `cliffordOfSplit` -- the anticommutator shadow over
  any certificate split.
* `orthogonal_clifford_scalar_cross_zero`,
  `HasInteriorScalarMixedCertificate`,
  `no_interior_scalar_mixed_of_orthogonal` -- the conditional obstruction.
* `threeRung_no_interior_mixed_certificate` -- instantiated at the split:
  the three-rung apparatus has no interior mixed scalar certificate.
* `BoundaryResidueReading`, `generatedBoundaryResidue`,
  `generated_boundary_flux_eq_terminal_residual` -- the remainder reads at
  the boundary, and it reads the electron.
* `boundary_radiation_finite` -- Theorem 3's clauses, finite edition, one
  package; the implication shape stays a target.

Residue left (honest scope):
the orthogonality is supplied by the split's TYPE, not proven about a
continuum Sobolev pairing -- the continuum theorem remains the formal
target, behind the mathlib door, exactly as the paper states it.  The
obstruction is conditional, not a universal impossibility: change the
pairing, the form, the representation, or the product, and a mixed
certificate becomes writable -- that changed tuple is what "new physics"
means in this corpus.  And "boundary radiation" here is one signed unit
read at one boundary; Hawking keeps his own references.
-/

/-- The Clifford shadow: an anticommutator that remembers the pairing
through the scalar relation `anti = -2 * dot`. -/
structure CliffordShadow (H : Type) where
  dot : H -> H -> Int
  anti : H -> H -> Int
  relation : forall x y, anti x y = -2 * dot x y

/-- Every certificate split carries its Clifford shadow. -/
def cliffordOfSplit (S : FiniteCertificateSplit) : CliffordShadow S.H where
  dot := S.dotH
  anti := fun x y => -2 * S.dotH x y
  relation := fun _ _ => rfl

/-- Orthogonality kills the scalar cross-term. -/
theorem orthogonal_clifford_scalar_cross_zero
    {H : Type} (C : CliffordShadow H) {g q : H}
    (horth : C.dot g q = 0) :
    C.anti g q = 0 := by
  rw [C.relation, horth]
  omega

/-- An interior mixed scalar certificate: a nonzero scalar cross-term
between the geometric and gauge representatives. -/
def HasInteriorScalarMixedCertificate
    {H : Type} (C : CliffordShadow H) (g q : H) : Prop :=
  C.anti g q ≠ 0

/-- The conditional obstruction: orthogonal representatives admit no
interior mixed scalar certificate in the unmodified apparatus. -/
theorem no_interior_scalar_mixed_of_orthogonal
    {H : Type} (C : CliffordShadow H) {g q : H}
    (horth : C.dot g q = 0) :
    ¬ HasInteriorScalarMixedCertificate C g q :=
  fun h => h (orthogonal_clifford_scalar_cross_zero C horth)

/-- Instantiated at the split: the three-rung apparatus has no interior
mixed scalar certificate between its geometric witness and the electron. -/
theorem threeRung_no_interior_mixed_certificate :
    ¬ HasInteriorScalarMixedCertificate
        (cliffordOfSplit threeRungCertificateSplit)
        threeRungCertificateSplit.geometric
        threeRungCertificateSplit.gauge :=
  no_interior_scalar_mixed_of_orthogonal
    (cliffordOfSplit threeRungCertificateSplit)
    threeRungCertificateSplit.orthogonal

/-- A boundary residue reading: the generated program's observable
remainder, read as boundary flux against the terminal residual. -/
structure BoundaryResidueReading where
  boundaryFlux : Int
  terminalResidual : Int
  producedBy : GeometricProgram

/-- The generated boundary residue of a generated QED program: the
excitation channel's pair coupling, read at the boundary. -/
noncomputable def generatedBoundaryResidue
    {P : GeometricProgram} (Q : GeneratedQEDProgram P) :
    BoundaryResidueReading where
  boundaryFlux :=
    CubicGaugeVariation.mixedCubicCoupling
      Q.excitationAction Q.path Q.electronPair
  terminalResidual := electron
  producedBy := P

/-- The remainder reads at the boundary, and it reads the electron: the
terminal residual is THE ELECTRON (Episode52's filed object, not a
literal), and the generated flux equals it by `rfl` through the
generation. -/
theorem generated_boundary_flux_eq_terminal_residual :
    (generatedBoundaryResidue generatedThreeRungQEDProgram).boundaryFlux =
      (generatedBoundaryResidue generatedThreeRungQEDProgram).terminalResidual :=
  rfl

/-- THEOREM 3'S CLAUSES, FINITE EDITION: the geometric and gauge representatives are
orthogonal in the split pairing; that orthogonality leaves no interior
mixed scalar certificate in the unmodified apparatus; and the observable
remainder reads as the boundary residual -- the electron, -1. -/
theorem boundary_radiation_finite :
    threeRungCertificateSplit.dotH
        threeRungCertificateSplit.geometric
        threeRungCertificateSplit.gauge = 0 ∧
      ¬ HasInteriorScalarMixedCertificate
          (cliffordOfSplit threeRungCertificateSplit)
          threeRungCertificateSplit.geometric
          threeRungCertificateSplit.gauge ∧
        (generatedBoundaryResidue generatedThreeRungQEDProgram).boundaryFlux =
          (generatedBoundaryResidue generatedThreeRungQEDProgram).terminalResidual :=
  ⟨threeRungCertificateSplit.orthogonal,
    threeRung_no_interior_mixed_certificate,
    generated_boundary_flux_eq_terminal_residual⟩

/-
The standing record.
-/

-- Build-true `[propext, Quot.sound]` on the three obstruction theorems AND on
-- the two flux theorems -- all choice-FREE.  (Earlier audits expected
-- `Classical.choice` on the flux pair via the chair; the chair is noncomputable
-- but choice-free -- Quot/funext-borne, not the choice axiom.)
#print axioms orthogonal_clifford_scalar_cross_zero
#print axioms no_interior_scalar_mixed_of_orthogonal
#print axioms threeRung_no_interior_mixed_certificate
#print axioms generated_boundary_flux_eq_terminal_residual
#print axioms boundary_radiation_finite

end Measurement
