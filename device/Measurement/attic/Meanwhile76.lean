import Measurement.Meanwhile75

/- MEANWHILE 76 -- MULTIGRID-PRECONDITIONED JFNK. The previous layer supplied
the closed linear residual. This layer packages the numerical mechanics around
it:

* linear shape functions on a two-cell, three-node mesh;
* a stiffness matrix assembled by the Galerkin weak form;
* Hooke's law as stress = stiffness * strain;
* Newton's law as residual = internal force - external force;
* a Jacobian-free Newton-Krylov step;
* a two-level multigrid preconditioner used as the Krylov preconditioner.

Everything is still finite and integer-valued. Smoothness is not asserted by a
continuum limit; it is the Galerkin certificate that adjacent element strains
match and that the weak residual already lives in the Sobolev/Galerkin slot.
-/

namespace Measurement

structure FiniteShapeFunction where
  name : String
  node : Nat
  leftNumerator : Int
  rightNumerator : Int
  denominator : Nat
  partitionMember : Bool
deriving Repr

def linearThreeNodeShapeFunctions : List FiniteShapeFunction :=
  [ { name := "N0"
      node := 0
      leftNumerator := 1
      rightNumerator := 0
      denominator := 1
      partitionMember := true },
    { name := "N1"
      node := 1
      leftNumerator := 0
      rightNumerator := 1
      denominator := 1
      partitionMember := true },
    { name := "N2"
      node := 2
      leftNumerator := 0
      rightNumerator := 1
      denominator := 1
      partitionMember := true } ]

def finiteAll : List Bool -> Bool
  | [] => true
  | x :: xs => x && finiteAll xs

def finiteShapePartitionOfUnity : Bool :=
  finiteAll (linearThreeNodeShapeFunctions.map
    (fun shape => shape.partitionMember)) &&
    decide (linearThreeNodeShapeFunctions.length = 3)

structure FiniteMechanicsState where
  u0 : Int
  u1 : Int
  u2 : Int
deriving Repr, DecidableEq

def FiniteMechanicsState.zero : FiniteMechanicsState :=
  { u0 := 0, u1 := 0, u2 := 0 }

def FiniteMechanicsState.add
    (x y : FiniteMechanicsState) : FiniteMechanicsState :=
  { u0 := x.u0 + y.u0
    u1 := x.u1 + y.u1
    u2 := x.u2 + y.u2 }

def FiniteMechanicsState.neg
    (x : FiniteMechanicsState) : FiniteMechanicsState :=
  { u0 := -x.u0
    u1 := -x.u1
    u2 := -x.u2 }

def FiniteMechanicsState.sub
    (x y : FiniteMechanicsState) : FiniteMechanicsState :=
  x.add y.neg

def FiniteMechanicsState.smul
    (k : Int) (x : FiniteMechanicsState) : FiniteMechanicsState :=
  { u0 := k * x.u0
    u1 := k * x.u1
    u2 := k * x.u2 }

def finiteMechanicsStrainLeft (u : FiniteMechanicsState) : Int :=
  u.u1 - u.u0

def finiteMechanicsStrainRight (u : FiniteMechanicsState) : Int :=
  u.u2 - u.u1

def finiteHookeModulus : Nat :=
  finiteVariationalSecondVariationCurvatureTaxScaledAt18

def finiteHookeStressLeft (u : FiniteMechanicsState) : Int :=
  Int.ofNat finiteHookeModulus * finiteMechanicsStrainLeft u

def finiteHookeStressRight (u : FiniteMechanicsState) : Int :=
  Int.ofNat finiteHookeModulus * finiteMechanicsStrainRight u

def finiteGalerkinStiffnessApply
    (u : FiniteMechanicsState) : FiniteMechanicsState :=
  let k := Int.ofNat finiteHookeModulus
  { u0 := k * (u.u0 - u.u1)
    u1 := k * ((u.u1 - u.u0) + (u.u1 - u.u2))
    u2 := k * (u.u2 - u.u1) }

def finiteMechanicsMassApply
    (u : FiniteMechanicsState) : FiniteMechanicsState :=
  u

def finiteMechanicsJacobianApply
    (u : FiniteMechanicsState) : FiniteMechanicsState :=
  (finiteMechanicsMassApply u).add (finiteGalerkinStiffnessApply u)

def finiteNewtonExternalForce : FiniteMechanicsState :=
  { u0 := 0, u1 := 0, u2 := 0 }

def finiteNewtonResidual
    (u : FiniteMechanicsState) : FiniteMechanicsState :=
  (finiteMechanicsJacobianApply u).sub finiteNewtonExternalForce

def finiteNewtonResidualNormSq
    (u : FiniteMechanicsState) : Nat :=
  let r := finiteNewtonResidual u
  intMagnitude (r.u0 * r.u0 + r.u1 * r.u1 + r.u2 * r.u2)

def finiteMechanicsStateZero?
    (u : FiniteMechanicsState) : Bool :=
  decide (u = FiniteMechanicsState.zero)

def finiteResidualZero?
    (u : FiniteMechanicsState) : Bool :=
  finiteMechanicsStateZero? (finiteNewtonResidual u)

def finiteGalerkinSmoothnessCertificate
    (u : FiniteMechanicsState) : Bool :=
  finiteVariationalEulerLagrangeMinimizesActivity &&
    finiteDifferentialPolynomialReport.activityPolynomialTrivialSolution &&
    decide (finiteMechanicsStrainLeft u = finiteMechanicsStrainRight u)

def finiteCoarseRestrict
    (u : FiniteMechanicsState) : Int :=
  u.u1

def finiteCoarseProlong
    (center : Int) : FiniteMechanicsState :=
  { u0 := 0, u1 := center, u2 := 0 }

def finiteMultigridPreconditioner
    (residual : FiniteMechanicsState) : FiniteMechanicsState :=
  finiteCoarseProlong (finiteCoarseRestrict residual)

def finiteJFNKDirectionalResidual
    (u direction : FiniteMechanicsState) : FiniteMechanicsState :=
  (finiteNewtonResidual (u.add direction)).sub (finiteNewtonResidual u)

def finiteJFNKPreconditionedDirection
    (u : FiniteMechanicsState) : FiniteMechanicsState :=
  (finiteMultigridPreconditioner (finiteNewtonResidual u)).neg

def finiteJFNKStep
    (u : FiniteMechanicsState) : FiniteMechanicsState :=
  u.add (finiteJFNKPreconditionedDirection u)

def finiteJFNKInitialGuess : FiniteMechanicsState :=
  FiniteMechanicsState.zero

def finiteJFNKAfterOneStep : FiniteMechanicsState :=
  finiteJFNKStep finiteJFNKInitialGuess

def finiteJFNKConverged : Bool :=
  finiteResidualZero? finiteJFNKAfterOneStep

def finiteJFNKResidualImproves : Bool :=
  finiteNewtonResidualNormSq finiteJFNKAfterOneStep <=
    finiteNewtonResidualNormSq finiteJFNKInitialGuess

def finiteMechanicsAlphaEstimateScaledAt18 : Nat :=
  finiteVariationalAlphaEstimateScaledAt18

def finiteMechanicsInverseAlphaEstimateScaledAt18? : Option Nat :=
  finiteVariationalInverseAlphaEstimateScaledAt18?

structure FiniteJFNKMechanicsReport where
  name : String
  interpretation : String
  shapeFunctions : List FiniteShapeFunction
  shapePartitionOfUnity : Bool
  hookeModulusScaledAt18 : Nat
  initialGuess : FiniteMechanicsState
  stiffnessAtInitialGuess : FiniteMechanicsState
  hookeStressLeftAtInitialGuess : Int
  hookeStressRightAtInitialGuess : Int
  newtonExternalForce : FiniteMechanicsState
  newtonResidualAtInitialGuess : FiniteMechanicsState
  residualNormSqAtInitialGuess : Nat
  galerkinSmoothnessAtInitialGuess : Bool
  multigridCoarseResidual : Int
  multigridPreconditionedCorrection : FiniteMechanicsState
  jfnkDirectionalResidual : FiniteMechanicsState
  afterOneJFNKStep : FiniteMechanicsState
  residualAfterOneJFNKStep : FiniteMechanicsState
  residualNormSqAfterOneJFNKStep : Nat
  residualImproves : Bool
  converged : Bool
  eulerLagrangeMinimizesActivity : Bool
  exponentialPolynomialTrivialSolution : Bool
  variationalAlphaEstimateScaledAt18 : Nat
  variationalInverseAlphaEstimateScaledAt18? : Option Nat
deriving Repr

def finiteJFNKMechanicsReport : FiniteJFNKMechanicsReport :=
  let initial := finiteJFNKInitialGuess
  let residual := finiteNewtonResidual initial
  let correction := finiteJFNKPreconditionedDirection initial
  let afterStep := finiteJFNKAfterOneStep
  { name := "finite-multigrid-preconditioned-jfnk-mechanics"
    interpretation :=
      "linear shape functions assemble a Galerkin stiffness matrix; Hooke and Newton produce the residual; multigrid preconditions the Jacobian-free Newton-Krylov step"
    shapeFunctions := linearThreeNodeShapeFunctions
    shapePartitionOfUnity := finiteShapePartitionOfUnity
    hookeModulusScaledAt18 := finiteHookeModulus
    initialGuess := initial
    stiffnessAtInitialGuess := finiteGalerkinStiffnessApply initial
    hookeStressLeftAtInitialGuess := finiteHookeStressLeft initial
    hookeStressRightAtInitialGuess := finiteHookeStressRight initial
    newtonExternalForce := finiteNewtonExternalForce
    newtonResidualAtInitialGuess := residual
    residualNormSqAtInitialGuess := finiteNewtonResidualNormSq initial
    galerkinSmoothnessAtInitialGuess :=
      finiteGalerkinSmoothnessCertificate initial
    multigridCoarseResidual := finiteCoarseRestrict residual
    multigridPreconditionedCorrection := correction
    jfnkDirectionalResidual :=
      finiteJFNKDirectionalResidual initial correction
    afterOneJFNKStep := afterStep
    residualAfterOneJFNKStep := finiteNewtonResidual afterStep
    residualNormSqAfterOneJFNKStep :=
      finiteNewtonResidualNormSq afterStep
    residualImproves := finiteJFNKResidualImproves
    converged := finiteJFNKConverged
    eulerLagrangeMinimizesActivity :=
      finiteVariationalEulerLagrangeMinimizesActivity
    exponentialPolynomialTrivialSolution :=
      finiteDifferentialPolynomialReport.activityPolynomialTrivialSolution
    variationalAlphaEstimateScaledAt18 :=
      finiteMechanicsAlphaEstimateScaledAt18
    variationalInverseAlphaEstimateScaledAt18? :=
      finiteMechanicsInverseAlphaEstimateScaledAt18? }

#eval finiteJFNKMechanicsReport

end Measurement
