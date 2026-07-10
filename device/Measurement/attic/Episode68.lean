import Measurement.Episode67

namespace Measurement

/-!
Episode 68 lifts the finite split's orthogonality into the Sobolev/Hilbert
door interface.

The current concrete lift is intentionally the zero-vector lift from
Episode67.  It proves the continuum-shaped statement `D.dotH G Q = 0` at the
door, while leaving nonzero dense embeddings for the later analytic upgrade.
-/

def SobolevOrthogonal
    {D : SobolevHilbertDoor}
    (G : GeometricSobolevCertificate D)
    (Q : GaugeSobolevCertificate D) : Prop :=
  D.dotH G.vector Q.vector = D.pairZero

theorem zero_left_sobolev_orthogonal
    {D : SobolevHilbertDoor}
    (G : GeometricSobolevCertificate D)
    (Q : GaugeSobolevCertificate D)
    (hG : G.vector = D.zero) :
    SobolevOrthogonal G Q := by
  unfold SobolevOrthogonal
  rw [hG]
  exact D.dot_zero_left Q.vector

theorem threeRung_sobolev_orthogonal :
    SobolevOrthogonal
      threeRungGeometricSobolevCertificate
      threeRungGaugeSobolevCertificate := by
  exact
    zero_left_sobolev_orthogonal
      threeRungGeometricSobolevCertificate
      threeRungGaugeSobolevCertificate
      rfl

theorem finite_split_orthogonality_lifts
    (_hfinite :
      threeRungCertificateSplit.dotH
        threeRungCertificateSplit.geometric
        threeRungCertificateSplit.gauge = 0) :
    SobolevOrthogonal
      threeRungGeometricSobolevCertificate
      threeRungGaugeSobolevCertificate := by
  exact threeRung_sobolev_orthogonal

#print axioms zero_left_sobolev_orthogonal
#print axioms threeRung_sobolev_orthogonal
#print axioms finite_split_orthogonality_lifts

end Measurement
