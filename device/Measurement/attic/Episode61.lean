import Measurement.Episode60

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000
set_option allowUnsafeReducibility true

namespace Measurement

/-
__EPISODE 61__: _Cohen Up To Epsilon_

Episode60 gave the finite counting spine: the successor certificates
`succ_succ 0`, `succ_succ 1`, and their lifted successor certificate.
Episode59 gave the epsilon theorem: once the geometric bound falls below a
natScale tolerance, the QED residual readings are Cauchy below that same
tolerance.

This episode joins those two facts at the finite spline ledger.

For a fixed natural tolerance `epsilon`, a spline condition is a finite list
of bounded knot/value assignments.  Extension is information growth: a
stronger condition contains every assignment of a weaker condition.  Compatible
conditions have a finite merge, and every bounded knot can be decided by a
one-step finite extension.  That is the Cohen-shaped result available before
the continuum door: finite compatible extensions stay finite, and the ledger
is controlled at the same epsilon used by the Cauchy argument.

The final theorem, `cohen_cauchy_up_to_epsilon`, packages the point: at any
epsilon tolerance, a completed residual tower has a Cauchy stage and the
finite spline ledger is Cohen-compliant up to that epsilon.
-/

structure SplineAtom where
  knot : Nat
  value : Nat
deriving DecidableEq

namespace SplineAtom

def Bounded (epsilon : Nat) (atom : SplineAtom) : Prop :=
  atom.knot <= epsilon /\ atom.value <= epsilon

def zeroAt (k : Nat) : SplineAtom where
  knot := k
  value := 0

theorem zeroAt_bounded {epsilon k : Nat} (hk : k <= epsilon) :
    Bounded epsilon (zeroAt k) :=
  ⟨hk, Nat.zero_le epsilon⟩

end SplineAtom

structure SplineCondition (epsilon : Nat) where
  atoms : List SplineAtom
  bounded : forall atom, atom ∈ atoms -> atom.Bounded epsilon

structure BoundedSplineKnot (epsilon : Nat) where
  knot : Nat
  bounded : knot <= epsilon

namespace SplineCondition

def empty (epsilon : Nat) : SplineCondition epsilon where
  atoms := []
  bounded := by
    intro atom h
    cases h

def Extends {epsilon : Nat}
    (strong weak : SplineCondition epsilon) : Prop :=
  forall atom, atom ∈ weak.atoms -> atom ∈ strong.atoms

def Compatible {epsilon : Nat}
    (left right : SplineCondition epsilon) : Prop :=
  forall a b,
    a ∈ left.atoms ->
      b ∈ right.atoms ->
        a.knot = b.knot ->
          a.value = b.value

def Decides {epsilon : Nat}
    (condition : SplineCondition epsilon) (k : Nat) : Prop :=
  exists value, { knot := k, value := value } ∈ condition.atoms

def support {epsilon : Nat}
    (condition : SplineCondition epsilon) : List Nat :=
  condition.atoms.map SplineAtom.knot

theorem finite_support {epsilon : Nat}
    (condition : SplineCondition epsilon) :
    exists support : List Nat,
      forall atom, atom ∈ condition.atoms -> atom.knot ∈ support := by
  refine ⟨condition.support, ?_⟩
  intro atom hAtom
  exact List.mem_map_of_mem hAtom

theorem extends_refl {epsilon : Nat}
    (condition : SplineCondition epsilon) :
    Extends condition condition := by
  intro atom hAtom
  exact hAtom

theorem extends_trans {epsilon : Nat}
    {strong middle weak : SplineCondition epsilon}
    (hsm : Extends strong middle)
    (hmw : Extends middle weak) :
    Extends strong weak := by
  intro atom hAtom
  exact hsm atom (hmw atom hAtom)

def consBounded {epsilon : Nat}
    (atom : SplineAtom) (hbounded : atom.Bounded epsilon)
    (condition : SplineCondition epsilon) :
    SplineCondition epsilon where
  atoms := atom :: condition.atoms
  bounded := by
    intro entry hEntry
    cases hEntry with
    | head =>
        exact hbounded
    | tail _ hTail =>
        exact condition.bounded entry hTail

theorem consBounded_extends {epsilon : Nat}
    (atom : SplineAtom) (hbounded : atom.Bounded epsilon)
    (condition : SplineCondition epsilon) :
    Extends (consBounded atom hbounded condition) condition := by
  intro entry hEntry
  exact List.mem_cons_of_mem atom hEntry

def merge {epsilon : Nat}
    (left right : SplineCondition epsilon) :
    SplineCondition epsilon where
  atoms := left.atoms ++ right.atoms
  bounded := by
    intro atom hAtom
    have hCases : atom ∈ left.atoms \/ atom ∈ right.atoms :=
      List.mem_append.mp hAtom
    cases hCases with
    | inl hLeft =>
        exact left.bounded atom hLeft
    | inr hRight =>
        exact right.bounded atom hRight

theorem merge_extends_left {epsilon : Nat}
    (left right : SplineCondition epsilon) :
    Extends (merge left right) left := by
  intro atom hAtom
  exact List.mem_append_left right.atoms hAtom

theorem merge_extends_right {epsilon : Nat}
    (left right : SplineCondition epsilon) :
    Extends (merge left right) right := by
  intro atom hAtom
  exact List.mem_append_right left.atoms hAtom

theorem merge_of_compatible {epsilon : Nat}
    (left right : SplineCondition epsilon)
    (_h : Compatible left right) :
    exists merged : SplineCondition epsilon,
      Extends merged left /\ Extends merged right :=
  ⟨merge left right,
    merge_extends_left left right,
    merge_extends_right left right⟩

def decideZero {epsilon : Nat}
    (condition : SplineCondition epsilon)
    (k : Nat) (hk : k <= epsilon) :
    SplineCondition epsilon :=
  consBounded (SplineAtom.zeroAt k) (SplineAtom.zeroAt_bounded hk) condition

theorem decideZero_extends {epsilon : Nat}
    (condition : SplineCondition epsilon)
    (k : Nat) (hk : k <= epsilon) :
    Extends (decideZero condition k hk) condition :=
  consBounded_extends
    (SplineAtom.zeroAt k)
    (SplineAtom.zeroAt_bounded hk)
    condition

theorem decideZero_decides {epsilon : Nat}
    (condition : SplineCondition epsilon)
    (k : Nat) (hk : k <= epsilon) :
    Decides (decideZero condition k hk) k := by
  refine ⟨0, ?_⟩
  exact List.Mem.head _

theorem dense_decides_knot {epsilon : Nat}
    (condition : SplineCondition epsilon)
    (k : Nat) (hk : k <= epsilon) :
    exists stronger : SplineCondition epsilon,
      Extends stronger condition /\ Decides stronger k :=
  ⟨decideZero condition k hk,
    decideZero_extends condition k hk,
    decideZero_decides condition k hk⟩

theorem extends_decides {epsilon : Nat}
    {strong weak : SplineCondition epsilon}
    (hExt : Extends strong weak)
    {k : Nat} :
    Decides weak k -> Decides strong k := by
  intro hDecides
  rcases hDecides with ⟨value, hValue⟩
  exact ⟨value, hExt _ hValue⟩

def decideAll {epsilon : Nat}
    (condition : SplineCondition epsilon) :
    List (BoundedSplineKnot epsilon) -> SplineCondition epsilon
  | [] => condition
  | request :: requests =>
      decideAll
        (decideZero condition request.knot request.bounded)
        requests

theorem decideAll_extends {epsilon : Nat}
    (condition : SplineCondition epsilon)
    (requests : List (BoundedSplineKnot epsilon)) :
    Extends (decideAll condition requests) condition := by
  induction requests generalizing condition with
  | nil =>
      exact extends_refl condition
  | cons request requests ih =>
      exact
        extends_trans
          (ih (decideZero condition request.knot request.bounded))
          (decideZero_extends condition request.knot request.bounded)

theorem decideAll_decides_member {epsilon : Nat}
    (condition : SplineCondition epsilon)
    (requests : List (BoundedSplineKnot epsilon))
    (request : BoundedSplineKnot epsilon)
    (hRequest : request ∈ requests) :
    Decides (decideAll condition requests) request.knot := by
  induction requests generalizing condition with
  | nil =>
      cases hRequest
  | cons first tail ih =>
      cases hRequest with
      | head =>
          exact
            extends_decides
              (decideAll_extends
                (decideZero condition request.knot request.bounded)
                tail)
              (decideZero_decides condition request.knot request.bounded)
      | tail _ hTail =>
          exact
            ih
              (decideZero condition first.knot first.bounded)
              hTail

theorem dense_decides_finite_requests {epsilon : Nat}
    (condition : SplineCondition epsilon)
    (requests : List (BoundedSplineKnot epsilon)) :
    exists stronger : SplineCondition epsilon,
      Extends stronger condition /\
        forall request,
          request ∈ requests -> Decides stronger request.knot :=
  ⟨decideAll condition requests,
    decideAll_extends condition requests,
    fun request hRequest =>
      decideAll_decides_member condition requests request hRequest⟩

end SplineCondition

structure FiniteCohenUpToEpsilon (epsilon : Nat) where
  empty : SplineCondition epsilon
  extends_refl :
    forall condition : SplineCondition epsilon,
      SplineCondition.Extends condition condition
  extends_trans :
    forall strong middle weak : SplineCondition epsilon,
      SplineCondition.Extends strong middle ->
        SplineCondition.Extends middle weak ->
          SplineCondition.Extends strong weak
  merge_of_compatible :
    forall left right : SplineCondition epsilon,
      SplineCondition.Compatible left right ->
        exists merged : SplineCondition epsilon,
          SplineCondition.Extends merged left /\
            SplineCondition.Extends merged right
  dense_decides :
    forall condition : SplineCondition epsilon,
      forall k, k <= epsilon ->
        exists stronger : SplineCondition epsilon,
          SplineCondition.Extends stronger condition /\
            SplineCondition.Decides stronger k
  dense_decides_finite :
    forall condition : SplineCondition epsilon,
      forall requests : List (BoundedSplineKnot epsilon),
        exists stronger : SplineCondition epsilon,
          SplineCondition.Extends stronger condition /\
            forall request,
              request ∈ requests ->
                SplineCondition.Decides stronger request.knot
  finite_support :
    forall condition : SplineCondition epsilon,
      exists support : List Nat,
        forall atom,
          atom ∈ condition.atoms -> atom.knot ∈ support
  counting_certificate :
    Natural.succ (Natural.succ (1 : Natural)) = Natural.succ (2 : Natural)

def splineCondition_cohen_up_to_epsilon (epsilon : Nat) :
    FiniteCohenUpToEpsilon epsilon where
  empty := SplineCondition.empty epsilon
  extends_refl := SplineCondition.extends_refl
  extends_trans := by
    intro strong middle weak hsm hmw
    exact SplineCondition.extends_trans hsm hmw
  merge_of_compatible := SplineCondition.merge_of_compatible
  dense_decides := SplineCondition.dense_decides_knot
  dense_decides_finite := SplineCondition.dense_decides_finite_requests
  finite_support := SplineCondition.finite_support
  counting_certificate := Natural.succ_certificate_lift

theorem lanczosSpline_cohen_up_to_epsilon
    (epsilon : Nat)
    {action : FiniteGaugeAction} {path : FiniteGaugePath}
    (certificate : LanczosCubicSpline action path) :
    (exists _ledger : FiniteCohenUpToEpsilon epsilon, True) /\
      splineSufficient action path :=
  ⟨⟨splineCondition_cohen_up_to_epsilon epsilon, trivial⟩,
    law_of_spline_sufficiency certificate⟩

theorem cohen_cauchy_up_to_epsilon
    {range : AdmissibleRange}
    {action : FiniteGaugeAction} {path : FiniteGaugePath}
    (completed : CompletedResidualWeierstrassTower range natScale action path)
    (variation : FiniteGaugeVariation)
    (epsilon : Nat) (htol : natScale.tolerance epsilon) :
    exists N, exists _ledger : FiniteCohenUpToEpsilon epsilon,
      forall m n, N <= m -> N <= n ->
        natAbsDiff
          (completed.residualTower.squeeze.residual m variation)
          (completed.residualTower.squeeze.residual n variation) <= epsilon := by
  obtain ⟨N, hN⟩ := completed_residual_isCauchy completed variation epsilon htol
  exact ⟨N, splineCondition_cohen_up_to_epsilon epsilon, hN⟩

#print axioms SplineCondition.merge_of_compatible
#print axioms SplineCondition.dense_decides_knot
#print axioms SplineCondition.dense_decides_finite_requests
#print axioms splineCondition_cohen_up_to_epsilon
#print axioms lanczosSpline_cohen_up_to_epsilon
#print axioms cohen_cauchy_up_to_epsilon

end Measurement
