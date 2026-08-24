/-!
Finite exact weak-form skeleton for Book II.

The analytic reading is:

* the Dirac face supplies the first-order rows;
* the universal tensor supplies the zeroth/tensor rows;
* the Sobolev rows express the norm in which the residual is tested;
* the first Frechet variation is the Sobolev-tested residual paired with a
  finite Galerkin test vector;
* an exact Galerkin residual gives the weak least-activity equation.

This is not a PDE library. It is the exact finite computation spine the
manuscript can point to without pretending that a continuum theorem has been
imported.
-/

namespace Measurement.WeakDiracGalerkin

abbrev Vec := List Int

def zeroLike : Vec -> Vec
  | [] => []
  | _ :: xs => 0 :: zeroLike xs

def add : Vec -> Vec -> Vec
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys => (x + y) :: add xs ys

def neg : Vec -> Vec
  | [] => []
  | x :: xs => (-x) :: neg xs

def sub (xs ys : Vec) : Vec :=
  add xs (neg ys)

def dot : Vec -> Vec -> Int
  | [], _ => 0
  | _, [] => 0
  | x :: xs, y :: ys => x * y + dot xs ys

def rowApply (row state : Vec) : Int :=
  dot row state

def matrixApply (rows : List Vec) (state : Vec) : Vec :=
  rows.map (fun row => rowApply row state)

theorem dot_zero_left_any :
    forall shape test : Vec, dot (zeroLike shape) test = 0 := by
  intro shape
  induction shape with
  | nil =>
      intro test
      cases test <;> rfl
  | cons _ xs ih =>
      intro test
      cases test with
      | nil => rfl
      | cons _ ys =>
          simp [zeroLike, dot, ih]

structure UniversalTensor where
  diracRows : List Vec
  tensorRows : List Vec
  sobolevRows : List Vec
  load : Vec
deriving Repr

def rawTensorResidual
    (U : UniversalTensor) (state : Vec) : Vec :=
  sub
    (add (matrixApply U.diracRows state)
      (matrixApply U.tensorRows state))
    U.load

def sobolevResidual
    (U : UniversalTensor) (state : Vec) : Vec :=
  matrixApply U.sobolevRows (rawTensorResidual U state)

def sobolevNormSq (U : UniversalTensor) (state : Vec) : Int :=
  let r := sobolevResidual U state
  dot r r

def firstFrechetVariation
    (U : UniversalTensor) (state test : Vec) : Int :=
  dot (sobolevResidual U state) test

def WeakLeastActivity
    (U : UniversalTensor) (state : Vec) : Prop :=
  forall test, firstFrechetVariation U state test = 0

def ExactGalerkin
    (U : UniversalTensor) (state : Vec) : Prop :=
  sobolevResidual U state = zeroLike (sobolevResidual U state)

theorem exactGalerkin_is_weakLeastActivity
    (U : UniversalTensor) (state : Vec)
    (h : ExactGalerkin U state) :
    WeakLeastActivity U state := by
  intro test
  unfold ExactGalerkin at h
  unfold firstFrechetVariation
  rw [h]
  exact dot_zero_left_any (sobolevResidual U state) test

structure GalerkinReport where
  state : Vec
  rawResidual : Vec
  sobolevResidual : Vec
  sobolevNormSq : Int
  frechetOnTests : List Int
deriving Repr

def report
    (U : UniversalTensor) (state : Vec) (tests : List Vec) :
    GalerkinReport :=
  { state := state
    rawResidual := rawTensorResidual U state
    sobolevResidual := sobolevResidual U state
    sobolevNormSq := sobolevNormSq U state
    frechetOnTests := tests.map (fun test =>
      firstFrechetVariation U state test) }

def diracToyTensor : UniversalTensor :=
  { diracRows :=
      [[1, -1],
       [1,  1]]
    tensorRows :=
      [[0, 0],
       [0, 0]]
    sobolevRows :=
      [[1, 0],
       [0, 1]]
    load :=
      [0, 2] }

def exactState : Vec :=
  [1, 1]

def basisTests : List Vec :=
  [[1, 0], [0, 1], [1, -1]]

def exactReport : GalerkinReport :=
  report diracToyTensor exactState basisTests

#eval exactReport

example : ExactGalerkin diracToyTensor exactState := by
  rfl

example : WeakLeastActivity diracToyTensor exactState :=
  exactGalerkin_is_weakLeastActivity diracToyTensor exactState (by rfl)

end Measurement.WeakDiracGalerkin
