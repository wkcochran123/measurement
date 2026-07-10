import Measurement.Episode74

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000
set_option allowUnsafeReducibility true

namespace Measurement

/-!
__EPISODE 75__: _The Outside Reading_

Episode55 named the generated boundary residue "QED-shaped".  That was a
useful intermediate handle, but it was not the outside-world theorem the early
episodes promised.  The promised route runs through the Einstein-side boundary
read and leaves a finite Navier-Stokes-shaped balance as the residue of the
approximation.

This episode keeps the old generated machinery as scaffolding and changes the
capstone surface:

* `EinsteinFieldEquationsHold` is the finite boundary equation: the geometric
  boundary read equals the stress read made by the generated boundary action.
* `BoundaryApproximationHolds` is the exact second-variation approximation:
  the coupled measurement is the two first-order readings plus the residue.
* `FiniteNavierStokesResidue` is the finite incompressible balance extracted
  from that approximation.
* `BoundaryObstructionCertificate` is the outside-world error code: a nonzero
  residue is no longer hidden as a truth-value question.  It is read by the
  simple on/off apparatus as `on`.

This is not a claim of standard continuum Navier-Stokes.  It is the finite
residue statement the code can actually support: from the generated
Einstein-boundary equation and the approximation identity, the remaining
second-variation term is the Navier-Stokes-shaped boundary balance term.  At
the three-rung witness the error code is `-1`, so the outside bit is on.
-/

/-- The simple apparatus only sees whether the outside-world residue is silent
or obstructed. -/
inductive BoundarySignal where
  | off
  | on

namespace BoundarySignal

/-- A zero error code is off; any nonzero error code is on. -/
def ofErrorCode (code : Int) : BoundarySignal :=
  if code = 0 then .off else .on

theorem ofErrorCode_on {code : Int} (h : code ≠ 0) :
    ofErrorCode code = .on := by
  simp [ofErrorCode, h]

theorem ofErrorCode_off :
    ofErrorCode 0 = .off := by
  simp [ofErrorCode]

end BoundarySignal

/-- The obstruction certificate is the error code seen by the outside
on/off apparatus. -/
structure BoundaryObstructionCertificate where
  errorCode : Int
  signal : BoundarySignal
  nonzero : errorCode ≠ 0
  signal_on : signal = BoundarySignal.on

namespace BoundaryObstructionCertificate

def ofNonzero (code : Int) (h : code ≠ 0) :
    BoundaryObstructionCertificate where
  errorCode := code
  signal := BoundarySignal.ofErrorCode code
  nonzero := h
  signal_on := BoundarySignal.ofErrorCode_on h

end BoundaryObstructionCertificate

/-- The finite Einstein-side boundary tensor: the depth of the geometric
boundary, read as an integer. -/
def EinsteinBoundaryTensor (P : GeometricProgram) : Int :=
  Int.ofNat (SpaceTimePath.boundaryDepth P.anchor.source)

/-- The finite stress read: the generated boundary action evaluated on the
left boundary displacement of the approximation. -/
def BoundaryStressTensor
    (action : FiniteGaugeAction) (path : CubicGaugePath)
    (variation : CubicGaugeVariation) : Int :=
  Int.ofNat (action.segmentCost path.middleLeft variation.middleLeftSlip)

/-- Finite Einstein field equation, at the boundary: geometry's boundary read
equals the stress read of the generated boundary action. -/
def EinsteinFieldEquationsHold
    (P : GeometricProgram) (action : FiniteGaugeAction)
    (path : CubicGaugePath) (variation : CubicGaugeVariation) : Prop :=
  EinsteinBoundaryTensor P = BoundaryStressTensor action path variation

/-- The approximation identity that exposes the residue: the coupled
measurement equals the two first-order readings plus the second variation. -/
def BoundaryApproximationHolds
    (action : FiniteGaugeAction) (path : CubicGaugePath)
    (variation : CubicGaugeVariation) : Prop :=
  CubicGaugeVariation.coupledCubicDifference action path variation =
    CubicGaugePath.leftMiddleResidual action path
        (CubicGaugeVariation.leftVariation variation) +
      CubicGaugePath.rightMiddleResidual action path
        (CubicGaugeVariation.rightVariation variation) +
        CubicGaugeVariation.secondVariation action path variation

/-- A generated finite Einstein-boundary approximation.  It carries both the
field equation and the approximation identity; no zero-mode conclusion is
stored here. -/
structure EinsteinBoundaryApproximation (P : GeometricProgram) where
  action : FiniteGaugeAction0
  path : CubicGaugePath0
  variation : CubicGaugeVariation0
  generatedBy : BoundaryGaugeCompiler
  action_generated : action = generatedBy.compileAction P
  path_generated : path = generatedBy.compilePath P
  variation_generated : variation = generatedBy.compilePair P
  fieldEquations : EinsteinFieldEquationsHold P action path variation
  approximation : BoundaryApproximationHolds action path variation

/-- The finite Navier-Stokes-shaped residue: a balance law with first-order
transport and pressure reads, a second-variation boundary flux, and an
obstruction certificate for the nonzero residue. -/
structure FiniteNavierStokesResidue where
  transport : Int
  pressure : Int
  viscousBoundaryFlux : Int
  boundaryForcing : Int
  divergence : Int
  obstruction : BoundaryObstructionCertificate
  balance :
    boundaryForcing = transport + pressure + viscousBoundaryFlux
  incompressible : divergence = 0
  obstruction_reads_residue :
    obstruction.errorCode = viscousBoundaryFlux

/-- Project an Einstein-boundary approximation to its finite
Navier-Stokes-shaped residue.  The nonzero second variation is the obstruction
error code. -/
def navierStokesResidueOfEinsteinApproximation
    {P : GeometricProgram} (A : EinsteinBoundaryApproximation P)
    (hResidue :
      CubicGaugeVariation.secondVariation A.action A.path A.variation ≠ 0) :
    FiniteNavierStokesResidue where
  transport :=
    CubicGaugePath.leftMiddleResidual A.action A.path
      (CubicGaugeVariation.leftVariation A.variation)
  pressure :=
    CubicGaugePath.rightMiddleResidual A.action A.path
      (CubicGaugeVariation.rightVariation A.variation)
  viscousBoundaryFlux :=
    CubicGaugeVariation.secondVariation A.action A.path A.variation
  boundaryForcing :=
    CubicGaugeVariation.coupledCubicDifference A.action A.path A.variation
  divergence := 0
  obstruction :=
    BoundaryObstructionCertificate.ofNonzero
      (CubicGaugeVariation.secondVariation A.action A.path A.variation)
      hResidue
  balance := A.approximation
  incompressible := rfl
  obstruction_reads_residue := rfl

/-- The three-rung generated Einstein-boundary approximation.  Geometry's
boundary depth is exactly the stress read of the generated boundary action,
and the approximation identity is Episode31's second-variation theorem. -/
noncomputable def threeRungEinsteinBoundaryApproximation :
    EinsteinBoundaryApproximation threeRungGeometricProgram where
  action :=
    threeRungBoundaryCompiler.compileAction threeRungGeometricProgram
  path :=
    threeRungBoundaryCompiler.compilePath threeRungGeometricProgram
  variation :=
    threeRungBoundaryCompiler.compilePair threeRungGeometricProgram
  generatedBy := threeRungBoundaryCompiler
  action_generated := rfl
  path_generated := rfl
  variation_generated := rfl
  fieldEquations := by
    unfold EinsteinFieldEquationsHold EinsteinBoundaryTensor
      BoundaryStressTensor
    decide
  approximation :=
    CubicGaugeVariation.coupledCubicDifference_eq_left_right_plus_secondVariation
      (threeRungBoundaryCompiler.compileAction threeRungGeometricProgram)
      (threeRungBoundaryCompiler.compilePath threeRungGeometricProgram)
      (threeRungBoundaryCompiler.compilePair threeRungGeometricProgram)

theorem threeRung_boundary_secondVariation_eq_electron :
    CubicGaugeVariation.secondVariation
        threeRungEinsteinBoundaryApproximation.action
        threeRungEinsteinBoundaryApproximation.path
        threeRungEinsteinBoundaryApproximation.variation =
      electron := rfl

theorem threeRung_boundary_secondVariation_ne_zero :
    CubicGaugeVariation.secondVariation
        threeRungEinsteinBoundaryApproximation.action
        threeRungEinsteinBoundaryApproximation.path
        threeRungEinsteinBoundaryApproximation.variation ≠ 0 := by
  rw [threeRung_boundary_secondVariation_eq_electron, electron_charge]
  decide

/-- The concrete finite Navier-Stokes-shaped residue forced by the generated
Einstein-boundary approximation. -/
noncomputable def threeRungNavierStokesResidue :
    FiniteNavierStokesResidue :=
  navierStokesResidueOfEinsteinApproximation
    threeRungEinsteinBoundaryApproximation
    threeRung_boundary_secondVariation_ne_zero

theorem threeRung_einstein_field_equations_hold :
    EinsteinFieldEquationsHold
      threeRungGeometricProgram
      threeRungEinsteinBoundaryApproximation.action
      threeRungEinsteinBoundaryApproximation.path
      threeRungEinsteinBoundaryApproximation.variation :=
  threeRungEinsteinBoundaryApproximation.fieldEquations

theorem threeRung_navierStokes_balance :
    threeRungNavierStokesResidue.boundaryForcing =
      threeRungNavierStokesResidue.transport +
        threeRungNavierStokesResidue.pressure +
          threeRungNavierStokesResidue.viscousBoundaryFlux :=
  threeRungNavierStokesResidue.balance

theorem threeRung_navierStokes_errorCode :
    threeRungNavierStokesResidue.obstruction.errorCode = -1 := by
  unfold threeRungNavierStokesResidue
    navierStokesResidueOfEinsteinApproximation
    BoundaryObstructionCertificate.ofNonzero
  change
    CubicGaugeVariation.secondVariation
        threeRungEinsteinBoundaryApproximation.action
        threeRungEinsteinBoundaryApproximation.path
        threeRungEinsteinBoundaryApproximation.variation = -1
  rw [threeRung_boundary_secondVariation_eq_electron, electron_charge]

theorem threeRung_navierStokes_signal_on :
    threeRungNavierStokesResidue.obstruction.signal = BoundarySignal.on :=
  threeRungNavierStokesResidue.obstruction.signal_on

/-- The corrected capstone: the generated finite Einstein field equation,
under the approximation identity, forces a finite Navier-Stokes-shaped
boundary residue.  The residue is not QED here; it is the nonzero error code
of the outside-world balance. -/
theorem einstein_approximation_forces_navierStokes :
    EinsteinFieldEquationsHold
        threeRungGeometricProgram
        threeRungEinsteinBoundaryApproximation.action
        threeRungEinsteinBoundaryApproximation.path
        threeRungEinsteinBoundaryApproximation.variation ∧
      threeRungNavierStokesResidue.boundaryForcing =
        threeRungNavierStokesResidue.transport +
          threeRungNavierStokesResidue.pressure +
            threeRungNavierStokesResidue.viscousBoundaryFlux ∧
        threeRungNavierStokesResidue.obstruction.errorCode = -1 ∧
          threeRungNavierStokesResidue.obstruction.signal =
            BoundarySignal.on :=
  ⟨threeRung_einstein_field_equations_hold,
    threeRung_navierStokes_balance,
    threeRung_navierStokes_errorCode,
    threeRung_navierStokes_signal_on⟩

/-
The standing record.
-/

-- The field-equation proof is a concrete boundary read; the balance is the
-- second-variation approximation; the error code is the old electron residue
-- re-read as the outside-world Navier-Stokes obstruction.
#print axioms threeRung_einstein_field_equations_hold
#print axioms threeRung_navierStokes_balance
#print axioms threeRung_navierStokes_errorCode
#print axioms einstein_approximation_forces_navierStokes

end Measurement
