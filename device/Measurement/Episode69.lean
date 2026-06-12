import Measurement.Episode68

namespace Measurement

/-!
Episode 69 defines the continuum Clifford compatibility interface.

The finite Clifford obstruction from Episode57 becomes a door-facing rule:
if the Sobolev/Hilbert pairing is orthogonal, then the compatible Clifford
shadow admits no interior scalar mixed certificate.
-/

structure ContinuumCliffordCompatible (D : SobolevHilbertDoor) where
  hasInteriorScalarMixed : D.H -> D.H -> Prop
  noInteriorOfOrthogonal :
    forall x y,
      D.dotH x y = D.pairZero ->
        ¬ hasInteriorScalarMixed x y

def ContinuumInteriorScalarMixedCertificate
    {D : SobolevHilbertDoor}
    (C : ContinuumCliffordCompatible D)
    (G : GeometricSobolevCertificate D)
    (Q : GaugeSobolevCertificate D) : Prop :=
  C.hasInteriorScalarMixed G.vector Q.vector

theorem no_continuum_interior_scalar_mixed
    {D : SobolevHilbertDoor}
    {G : GeometricSobolevCertificate D}
    {Q : GaugeSobolevCertificate D}
    (C : ContinuumCliffordCompatible D)
    (horth : SobolevOrthogonal G Q) :
    ¬ ContinuumInteriorScalarMixedCertificate C G Q := by
  exact C.noInteriorOfOrthogonal G.vector Q.vector horth

def emptyContinuumCliffordCompatible
    (D : SobolevHilbertDoor) :
    ContinuumCliffordCompatible D where
  hasInteriorScalarMixed := fun _ _ => False
  noInteriorOfOrthogonal := by
    intro _x _y _horth hInterior
    exact hInterior

noncomputable def threeRungContinuumCliffordCompatible :
    ContinuumCliffordCompatible threeRungSobolevHilbertDoor :=
  emptyContinuumCliffordCompatible threeRungSobolevHilbertDoor

theorem threeRung_no_continuum_interior_scalar_mixed :
    ¬ ContinuumInteriorScalarMixedCertificate
      threeRungContinuumCliffordCompatible
      threeRungGeometricSobolevCertificate
      threeRungGaugeSobolevCertificate := by
  exact
    no_continuum_interior_scalar_mixed
      threeRungContinuumCliffordCompatible
      threeRung_sobolev_orthogonal

#print axioms no_continuum_interior_scalar_mixed
#print axioms emptyContinuumCliffordCompatible
#print axioms threeRungContinuumCliffordCompatible
#print axioms threeRung_no_continuum_interior_scalar_mixed

end Measurement
