import Measurement.Meanwhile74

/- MEANWHILE 75 -- EXPONENTIAL EIGENMODES. The variational layer needs a
cheap way to generate trivial solutions when the apparatus wants a closed
linear read. The analytic fact is familiar: `e^x` is an eigenfunction of the
derivative, so a differential polynomial `P(D)` acting on `e^x` collapses to
the ordinary scalar `P(1)`.

This file gives the finite certificate. We do not import real exponentials.
We record the one fact the device needs: an exponential mode has value `1`,
derivative read `1`, and eigenvalue `1`. Therefore any polynomial in the
derivative is evaluated by substituting `1` for `D`. If that scalar is zero,
the polynomial supplies a trivial residual for the variational problem.
-/

namespace Measurement

abbrev FiniteDifferentialPolynomial := List Int

def finitePolynomialEvalAtAux :
    FiniteDifferentialPolynomial -> Int -> Int -> Int
  | [], _, _ => 0
  | coefficient :: rest, eigenvalue, power =>
      coefficient * power +
        finitePolynomialEvalAtAux rest eigenvalue (power * eigenvalue)

def finitePolynomialEvalAt
    (polynomial : FiniteDifferentialPolynomial) (eigenvalue : Int) : Int :=
  finitePolynomialEvalAtAux polynomial eigenvalue 1

def finitePolynomialCoefficientSum
    (polynomial : FiniteDifferentialPolynomial) : Int :=
  finitePolynomialEvalAt polynomial 1

structure FiniteDerivativeEigenmode where
  name : String
  value : Int
  derivativeRead : Int
  eigenvalue : Int
  eigenfunctionCertificate : Bool
  interpretation : String
deriving Repr

def finiteExponentialEigenmode : FiniteDerivativeEigenmode :=
  { name := "finite-exp-mode"
    value := 1
    derivativeRead := 1
    eigenvalue := 1
    eigenfunctionCertificate := true
    interpretation :=
      "finite certificate for the analytic read D(e^x) = e^x" }

def finitePolynomialActsOnEigenmode
    (polynomial : FiniteDifferentialPolynomial)
    (mode : FiniteDerivativeEigenmode) : Int :=
  finitePolynomialEvalAt polynomial mode.eigenvalue * mode.value

def finitePolynomialKillsEigenmode
    (polynomial : FiniteDifferentialPolynomial)
    (mode : FiniteDerivativeEigenmode) : Bool :=
  decide (finitePolynomialActsOnEigenmode polynomial mode = 0)

def finiteFirstOrderTrivialPolynomial : FiniteDifferentialPolynomial :=
  [-1, 1]

def finiteSecondOrderTrivialPolynomial : FiniteDifferentialPolynomial :=
  [1, -2, 1]

def finiteActivityPolynomial : FiniteDifferentialPolynomial :=
  [Int.ofNat finiteVariationalActivityMagnitude,
    -Int.ofNat finiteVariationalFirstVariationResidualScaledAt18,
    Int.ofNat finiteVariationalSecondVariationCurvatureTaxScaledAt18,
    -Int.ofNat finiteVariationalSecondVariationCurvatureTaxScaledAt18]

def finiteActivityPolynomialIsTrivial : Bool :=
  finitePolynomialKillsEigenmode
    finiteActivityPolynomial finiteExponentialEigenmode

def finiteActivityPolynomialResidual : Int :=
  finitePolynomialActsOnEigenmode
    finiteActivityPolynomial finiteExponentialEigenmode

structure FiniteDifferentialPolynomialReport where
  name : String
  interpretation : String
  mode : FiniteDerivativeEigenmode
  derivativeEigenfunctionHolds : Bool
  firstOrderPolynomial : FiniteDifferentialPolynomial
  firstOrderPolynomialAtEigenvalue : Int
  firstOrderResidual : Int
  firstOrderTrivialSolution : Bool
  secondOrderPolynomial : FiniteDifferentialPolynomial
  secondOrderPolynomialAtEigenvalue : Int
  secondOrderResidual : Int
  secondOrderTrivialSolution : Bool
  activityPolynomial : FiniteDifferentialPolynomial
  activityPolynomialAtEigenvalue : Int
  activityPolynomialResidual : Int
  activityPolynomialTrivialSolution : Bool
  eulerLagrangeMinimizesActivity : Bool
  variationalAlphaEstimateScaledAt18 : Nat
  variationalInverseAlphaEstimateScaledAt18? : Option Nat
deriving Repr

def finiteDifferentialPolynomialReport :
    FiniteDifferentialPolynomialReport :=
  { name := "finite-differential-polynomial"
    interpretation :=
      "use the finite exponential eigenmode to collapse P(D) to P(1) and manufacture trivial residuals"
    mode := finiteExponentialEigenmode
    derivativeEigenfunctionHolds :=
      finiteExponentialEigenmode.eigenfunctionCertificate &&
        decide
          (finiteExponentialEigenmode.derivativeRead =
            finiteExponentialEigenmode.eigenvalue *
              finiteExponentialEigenmode.value)
    firstOrderPolynomial := finiteFirstOrderTrivialPolynomial
    firstOrderPolynomialAtEigenvalue :=
      finitePolynomialEvalAt finiteFirstOrderTrivialPolynomial
        finiteExponentialEigenmode.eigenvalue
    firstOrderResidual :=
      finitePolynomialActsOnEigenmode finiteFirstOrderTrivialPolynomial
        finiteExponentialEigenmode
    firstOrderTrivialSolution :=
      finitePolynomialKillsEigenmode finiteFirstOrderTrivialPolynomial
        finiteExponentialEigenmode
    secondOrderPolynomial := finiteSecondOrderTrivialPolynomial
    secondOrderPolynomialAtEigenvalue :=
      finitePolynomialEvalAt finiteSecondOrderTrivialPolynomial
        finiteExponentialEigenmode.eigenvalue
    secondOrderResidual :=
      finitePolynomialActsOnEigenmode finiteSecondOrderTrivialPolynomial
        finiteExponentialEigenmode
    secondOrderTrivialSolution :=
      finitePolynomialKillsEigenmode finiteSecondOrderTrivialPolynomial
        finiteExponentialEigenmode
    activityPolynomial := finiteActivityPolynomial
    activityPolynomialAtEigenvalue :=
      finitePolynomialEvalAt finiteActivityPolynomial
        finiteExponentialEigenmode.eigenvalue
    activityPolynomialResidual := finiteActivityPolynomialResidual
    activityPolynomialTrivialSolution := finiteActivityPolynomialIsTrivial
    eulerLagrangeMinimizesActivity :=
      finiteVariationalEulerLagrangeMinimizesActivity
    variationalAlphaEstimateScaledAt18 :=
      finiteVariationalAlphaEstimateScaledAt18
    variationalInverseAlphaEstimateScaledAt18? :=
      finiteVariationalInverseAlphaEstimateScaledAt18? }

#eval finiteDifferentialPolynomialReport

end Measurement
