import Measurement.Episode71

namespace Measurement

/-!
Episode 72 states the continuum-shaped generalized boundary radiation theorem.

This theorem is intentionally conditional.  The analytic content is supplied by
the door-facing hypotheses: generated certificates, Sobolev orthogonality,
Clifford compatibility, boundary trace compatibility, and residual Cauchy-ness
in the completion norm.
-/

theorem generalized_boundary_radiation_continuum
    {D : SobolevHilbertDoor}
    {G : GeometricSobolevCertificate D}
    {Q : GaugeSobolevCertificate D}
    {trace : BoundaryTraceFunctional D}
    (hgen : BoundaryGenerated G Q)
    (horth : SobolevOrthogonal G Q)
    (hcliff : ContinuumCliffordCompatible D)
    (htrace : BoundaryTraceCompatible trace Q)
    (hcauchy : ResidualCauchyInSobolevNorm Q) :
    ¬ ContinuumInteriorScalarMixedCertificate hcliff G Q ∧
      trace.boundaryFlux Q = trace.terminalResidual Q ∧
        ResidualCauchyInSobolevNorm Q := by
  have _hgen := hgen
  exact
    ⟨no_continuum_interior_scalar_mixed hcliff horth,
      htrace,
      hcauchy⟩

theorem threeRung_generalized_boundary_radiation_continuum :
    ¬ ContinuumInteriorScalarMixedCertificate
        threeRungContinuumCliffordCompatible
        threeRungGeometricSobolevCertificate
        threeRungGaugeSobolevCertificate ∧
      generatedBoundaryTraceFunctional.boundaryFlux
          threeRungGaugeSobolevCertificate =
        generatedBoundaryTraceFunctional.terminalResidual
          threeRungGaugeSobolevCertificate ∧
        ResidualCauchyInSobolevNorm
          threeRungGaugeSobolevCertificate := by
  exact
    generalized_boundary_radiation_continuum
      threeRung_boundaryGenerated
      threeRung_sobolev_orthogonal
      threeRungContinuumCliffordCompatible
      generatedBoundaryTrace_compatible
      threeRung_residual_cauchy_in_sobolev_norm

#print axioms generalized_boundary_radiation_continuum
#print axioms threeRung_generalized_boundary_radiation_continuum

end Measurement
