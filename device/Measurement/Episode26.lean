import Measurement.Episode25
import Measurement.Calibration.EKGBounded

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000
set_option allowUnsafeReducibility true

namespace Measurement

/-
__EPISODE 26__: _Three Measured Operations_

Episode25 made the next-candidate rule explicit: consume the available
candidate with the least heartbeat count.  This episode names the
measurement contract behind that selector.

There are three finite gauge operations being timed: load, transform, and
binary.  A candidate is measured by those three numbers.  The heartbeat
selector is the total measured cost.

Uniqueness is therefore not magic and not global.  It is local to a finite
elephant support: if the measured heartbeat total separates candidates on
that support, then any two heartbeat-minimal candidates are the same slip.
-/

inductive MeasuredGaugeOperation where
  | load
  | transform
  | binary

namespace MeasuredGaugeOperation

def all : List MeasuredGaugeOperation :=
  [.load, .transform, .binary]

theorem all_length : all.length = 3 :=
  rfl

end MeasuredGaugeOperation

structure ThreeOperationProfile where
  load : Nat
  transform : Nat
  binary : Nat

namespace ThreeOperationProfile

def totalHeartbeat (profile : ThreeOperationProfile) : Nat :=
  profile.load + profile.transform + profile.binary

end ThreeOperationProfile

structure ThreeOperationMeasurement where
  measure : MeasuredGaugeOperation -> Bullshit -> Nat

namespace ThreeOperationMeasurement

def profile
    (measurement : ThreeOperationMeasurement) (slip : Bullshit) :
    ThreeOperationProfile where
  load := measurement.measure .load slip
  transform := measurement.measure .transform slip
  binary := measurement.measure .binary slip

def heartbeat
    (measurement : ThreeOperationMeasurement) (slip : Bullshit) : Nat :=
  (measurement.profile slip).totalHeartbeat

def toHeartbeatSelector
    (measurement : ThreeOperationMeasurement) : HeartbeatSelector where
  heartbeat := measurement.heartbeat

def HeartbeatSeparatesOn
    (measurement : ThreeOperationMeasurement) (knots : SlipMultiset) :
    Prop :=
  forall leftSlip,
    leftSlip ∈ knots.entries ->
      forall rightSlip,
        rightSlip ∈ knots.entries ->
          measurement.heartbeat leftSlip =
            measurement.heartbeat rightSlip ->
              leftSlip = rightSlip

theorem fastestCandidate_unique
    {measurement : ThreeOperationMeasurement}
    {knots : SlipMultiset} {leftSlip rightSlip : Bullshit}
    (leftMinimal :
      SlipMultiset.HeartbeatMinimal
        measurement.toHeartbeatSelector
        knots
        leftSlip)
    (rightMinimal :
      SlipMultiset.HeartbeatMinimal
        measurement.toHeartbeatSelector
        knots
        rightSlip)
    (separates : measurement.HeartbeatSeparatesOn knots) :
    leftSlip = rightSlip := by
  have hLeftLe :
      measurement.heartbeat leftSlip <=
        measurement.heartbeat rightSlip :=
    leftMinimal.right rightSlip rightMinimal.left
  have hRightLe :
      measurement.heartbeat rightSlip <=
        measurement.heartbeat leftSlip :=
    rightMinimal.right leftSlip leftMinimal.left
  exact
    separates
      leftSlip
      leftMinimal.left
      rightSlip
      rightMinimal.left
      (Nat.le_antisymm hLeftLe hRightLe)

theorem fastestConsumes_same_slip
    {measurement : ThreeOperationMeasurement}
    {knots leftRemaining rightRemaining : SlipMultiset}
    {leftSlip rightSlip : Bullshit}
    (leftConsumes :
      SlipMultiset.FastestConsumes
        measurement.toHeartbeatSelector
        knots
        leftSlip
        leftRemaining)
    (rightConsumes :
      SlipMultiset.FastestConsumes
        measurement.toHeartbeatSelector
        knots
        rightSlip
        rightRemaining)
    (separates : measurement.HeartbeatSeparatesOn knots) :
    leftSlip = rightSlip :=
  ThreeOperationMeasurement.fastestCandidate_unique
    leftConsumes.fastest
    rightConsumes.fastest
    separates

end ThreeOperationMeasurement

structure ThreeOperationHeartbeatTrace
    (measurement : ThreeOperationMeasurement)
    (action : FiniteGaugeAction) (path : FiniteGaugePath) where
  trace :
    HeartbeatOrderedMultisetLanczosTrace
      measurement.toHeartbeatSelector
      action
      path
  separatesInitialSupport :
    measurement.HeartbeatSeparatesOn trace.knots

namespace ThreeOperationHeartbeatTrace

theorem eulerLagrange
    {measurement : ThreeOperationMeasurement}
    {action : FiniteGaugeAction} {path : FiniteGaugePath}
    (trace : ThreeOperationHeartbeatTrace measurement action path) :
    (DiscreteGaugeDerivative.fromAction action).eulerLagrange path :=
  trace.trace.eulerLagrange

theorem residue_eq_truth_zero
    {measurement : ThreeOperationMeasurement}
    {action : FiniteGaugeAction} {path : FiniteGaugePath}
    (trace : ThreeOperationHeartbeatTrace measurement action path) :
    (DiscreteGaugeDerivative.fromAction action).residue path =
      .zero Fact.Truth :=
  trace.trace.residue_eq_truth_zero

end ThreeOperationHeartbeatTrace

structure CubicThreeOperationApproximation
    (measurement : ThreeOperationMeasurement)
    (action : FiniteGaugeAction) (path : CubicGaugePath)
    (range : AdmissibleRange) where
  approximation :
    CubicHeartbeatPartitionedLanczosApproximation
      measurement.toHeartbeatSelector
      action
      path
      range
  leftSeparates :
    measurement.HeartbeatSeparatesOn
      approximation.support.leftElephant.candidates
  rightSeparates :
    measurement.HeartbeatSeparatesOn
      approximation.support.rightElephant.candidates

namespace CubicThreeOperationApproximation

theorem leftFastestCandidate_unique
    {measurement : ThreeOperationMeasurement}
    {action : FiniteGaugeAction} {path : CubicGaugePath}
    {range : AdmissibleRange}
    (approximation :
      CubicThreeOperationApproximation measurement action path range)
    {leftSlip rightSlip : Bullshit}
    (leftMinimal :
      SlipMultiset.HeartbeatMinimal
        measurement.toHeartbeatSelector
        approximation.approximation.support.leftElephant.candidates
        leftSlip)
    (rightMinimal :
      SlipMultiset.HeartbeatMinimal
        measurement.toHeartbeatSelector
        approximation.approximation.support.leftElephant.candidates
        rightSlip) :
    leftSlip = rightSlip :=
  ThreeOperationMeasurement.fastestCandidate_unique
    leftMinimal
    rightMinimal
    approximation.leftSeparates

theorem rightFastestCandidate_unique
    {measurement : ThreeOperationMeasurement}
    {action : FiniteGaugeAction} {path : CubicGaugePath}
    {range : AdmissibleRange}
    (approximation :
      CubicThreeOperationApproximation measurement action path range)
    {leftSlip rightSlip : Bullshit}
    (leftMinimal :
      SlipMultiset.HeartbeatMinimal
        measurement.toHeartbeatSelector
        approximation.approximation.support.rightElephant.candidates
        leftSlip)
    (rightMinimal :
      SlipMultiset.HeartbeatMinimal
        measurement.toHeartbeatSelector
        approximation.approximation.support.rightElephant.candidates
        rightSlip) :
    leftSlip = rightSlip :=
  ThreeOperationMeasurement.fastestCandidate_unique
    leftMinimal
    rightMinimal
    approximation.rightSeparates

theorem leftFastestConsumes_same_slip
    {measurement : ThreeOperationMeasurement}
    {action : FiniteGaugeAction} {path : CubicGaugePath}
    {range : AdmissibleRange}
    (approximation :
      CubicThreeOperationApproximation measurement action path range)
    {leftRemaining rightRemaining : SlipMultiset}
    {leftSlip rightSlip : Bullshit}
    (leftConsumes :
      SlipMultiset.FastestConsumes
        measurement.toHeartbeatSelector
        approximation.approximation.support.leftElephant.candidates
        leftSlip
        leftRemaining)
    (rightConsumes :
      SlipMultiset.FastestConsumes
        measurement.toHeartbeatSelector
        approximation.approximation.support.leftElephant.candidates
        rightSlip
        rightRemaining) :
    leftSlip = rightSlip :=
  ThreeOperationMeasurement.fastestConsumes_same_slip
    leftConsumes
    rightConsumes
    approximation.leftSeparates

theorem rightFastestConsumes_same_slip
    {measurement : ThreeOperationMeasurement}
    {action : FiniteGaugeAction} {path : CubicGaugePath}
    {range : AdmissibleRange}
    (approximation :
      CubicThreeOperationApproximation measurement action path range)
    {leftRemaining rightRemaining : SlipMultiset}
    {leftSlip rightSlip : Bullshit}
    (leftConsumes :
      SlipMultiset.FastestConsumes
        measurement.toHeartbeatSelector
        approximation.approximation.support.rightElephant.candidates
        leftSlip
        leftRemaining)
    (rightConsumes :
      SlipMultiset.FastestConsumes
        measurement.toHeartbeatSelector
        approximation.approximation.support.rightElephant.candidates
        rightSlip
        rightRemaining) :
    leftSlip = rightSlip :=
  ThreeOperationMeasurement.fastestConsumes_same_slip
    leftConsumes
    rightConsumes
    approximation.rightSeparates

theorem partitions_derive_two_middle_equations
    {measurement : ThreeOperationMeasurement}
    {action : FiniteGaugeAction} {path : CubicGaugePath}
    {range : AdmissibleRange}
    (approximation :
      CubicThreeOperationApproximation measurement action path range) :
    (forall variation,
      approximation.approximation.support.leftSupportedVariation variation ->
        path.leftMiddleResidual action variation = 0) /\
    (forall variation,
      approximation.approximation.support.rightSupportedVariation variation ->
        path.rightMiddleResidual action variation = 0) :=
  CubicHeartbeatPartitionedLanczosApproximation.partitions_derive_two_middle_equations_by_fastest_heartbeat
    approximation.approximation

theorem separated_fastest_candidates_derive_two_middle_equations
    {measurement : ThreeOperationMeasurement}
    {action : FiniteGaugeAction} {path : CubicGaugePath}
    {range : AdmissibleRange}
    (approximation :
      CubicThreeOperationApproximation measurement action path range)
    {leftA leftB rightA rightB : Bullshit}
    (leftMinimalA :
      SlipMultiset.HeartbeatMinimal
        measurement.toHeartbeatSelector
        approximation.approximation.support.leftElephant.candidates
        leftA)
    (leftMinimalB :
      SlipMultiset.HeartbeatMinimal
        measurement.toHeartbeatSelector
        approximation.approximation.support.leftElephant.candidates
        leftB)
    (rightMinimalA :
      SlipMultiset.HeartbeatMinimal
        measurement.toHeartbeatSelector
        approximation.approximation.support.rightElephant.candidates
        rightA)
    (rightMinimalB :
      SlipMultiset.HeartbeatMinimal
        measurement.toHeartbeatSelector
        approximation.approximation.support.rightElephant.candidates
        rightB) :
    leftA = leftB /\
      rightA = rightB /\
        ((forall variation,
          approximation.approximation.support.leftSupportedVariation variation ->
            path.leftMiddleResidual action variation = 0) /\
        (forall variation,
          approximation.approximation.support.rightSupportedVariation variation ->
            path.rightMiddleResidual action variation = 0)) :=
  ⟨approximation.leftFastestCandidate_unique leftMinimalA leftMinimalB,
    approximation.rightFastestCandidate_unique rightMinimalA rightMinimalB,
    approximation.partitions_derive_two_middle_equations⟩

end CubicThreeOperationApproximation

def truthThreeOperationMeasurement : ThreeOperationMeasurement where
  measure := fun _ _ => 0

theorem truthThreeOperation_has_three_operations :
    MeasuredGaugeOperation.all.length = 3 :=
  MeasuredGaugeOperation.all_length

theorem truthThreeOperationMeasurement_separates_singleton :
    truthThreeOperationMeasurement.HeartbeatSeparatesOn
      (SlipMultiset.singleton (.zero Fact.Truth)) := by
  intro leftSlip hLeft rightSlip hRight hEq
  simp [SlipMultiset.singleton] at hLeft hRight
  subst leftSlip
  subst rightSlip
  rfl

def ekgLoadSlip : Bullshit :=
  .zero Fact.Truth

def ekgTransformSlip : Bullshit :=
  .one
    Fact.Truth
    (.zero Fact.Truth)
    (.boot Fact.Truth Prop)
    (.boot Fact.Truth Prop)
    ekgLoadSlip

def ekgBinarySlip : Bullshit :=
  .rest
    Fact.Truth
    Fact.Truth
    Fact.Truth.truth
    (.zero Fact.Truth)
    (.zero Fact.Truth)
    (.zero Fact.Truth)
    (.boot Fact.Truth Prop)
    (.boot Fact.Truth Prop)
    ekgLoadSlip
    ekgTransformSlip

def ekgMeasuredSupport : SlipMultiset where
  entries := [ekgLoadSlip, ekgTransformSlip, ekgBinarySlip]

def ekgMeasuredOperationCost :
    MeasuredGaugeOperation -> Bullshit -> Nat
  | .load, _ => 1
  | .transform, .zero _ => 0
  | .transform, _ => 1
  | .binary, .rest _ _ _ _ _ _ _ _ _ _ => 1
  | .binary, _ => 0

def ekgThreeOperationMeasurement : ThreeOperationMeasurement where
  measure := ekgMeasuredOperationCost

theorem ekgLoadSlip_heartbeat :
    ekgThreeOperationMeasurement.heartbeat ekgLoadSlip = 1 := by
  rfl

theorem ekgTransformSlip_heartbeat :
    ekgThreeOperationMeasurement.heartbeat ekgTransformSlip = 2 := by
  rfl

theorem ekgBinarySlip_heartbeat :
    ekgThreeOperationMeasurement.heartbeat ekgBinarySlip = 3 := by
  rfl

theorem ekgThreeOperationMeasurement_separates_support :
    ekgThreeOperationMeasurement.HeartbeatSeparatesOn
      ekgMeasuredSupport := by
  intro leftSlip hLeft rightSlip hRight hEq
  simp [ekgMeasuredSupport, ekgLoadSlip, ekgTransformSlip, ekgBinarySlip]
    at hLeft hRight
  rcases hLeft with hLeft | hLeft | hLeft
  · subst leftSlip
    rcases hRight with hRight | hRight | hRight
    · subst rightSlip
      rfl
    · subst rightSlip
      simp [ThreeOperationMeasurement.heartbeat,
        ThreeOperationMeasurement.profile,
        ThreeOperationProfile.totalHeartbeat,
        ekgThreeOperationMeasurement,
        ekgMeasuredOperationCost] at hEq
    · subst rightSlip
      simp [ThreeOperationMeasurement.heartbeat,
        ThreeOperationMeasurement.profile,
        ThreeOperationProfile.totalHeartbeat,
        ekgThreeOperationMeasurement,
        ekgMeasuredOperationCost] at hEq
  · subst leftSlip
    rcases hRight with hRight | hRight | hRight
    · subst rightSlip
      simp [ThreeOperationMeasurement.heartbeat,
        ThreeOperationMeasurement.profile,
        ThreeOperationProfile.totalHeartbeat,
        ekgThreeOperationMeasurement,
        ekgMeasuredOperationCost] at hEq
    · subst rightSlip
      rfl
    · subst rightSlip
      simp [ThreeOperationMeasurement.heartbeat,
        ThreeOperationMeasurement.profile,
        ThreeOperationProfile.totalHeartbeat,
        ekgThreeOperationMeasurement,
        ekgMeasuredOperationCost] at hEq
  · subst leftSlip
    rcases hRight with hRight | hRight | hRight
    · subst rightSlip
      simp [ThreeOperationMeasurement.heartbeat,
        ThreeOperationMeasurement.profile,
        ThreeOperationProfile.totalHeartbeat,
        ekgThreeOperationMeasurement,
        ekgMeasuredOperationCost] at hEq
    · subst rightSlip
      simp [ThreeOperationMeasurement.heartbeat,
        ThreeOperationMeasurement.profile,
        ThreeOperationProfile.totalHeartbeat,
        ekgThreeOperationMeasurement,
        ekgMeasuredOperationCost] at hEq
    · subst rightSlip
      rfl

theorem ekgLoadSlip_fastest :
    SlipMultiset.HeartbeatMinimal
      ekgThreeOperationMeasurement.toHeartbeatSelector
      ekgMeasuredSupport
      ekgLoadSlip := by
  constructor
  · simp [ekgMeasuredSupport, ekgLoadSlip]
  · intro candidate h
    simp [ekgMeasuredSupport, ekgLoadSlip, ekgTransformSlip, ekgBinarySlip]
      at h
    rcases h with h | h | h
    · subst candidate
      exact Nat.le_refl _
    · subst candidate
      decide
    · subst candidate
      decide

theorem ekgFastestCandidate_eq_load
    {candidate : Bullshit}
    (minimal :
      SlipMultiset.HeartbeatMinimal
        ekgThreeOperationMeasurement.toHeartbeatSelector
        ekgMeasuredSupport
        candidate) :
    candidate = ekgLoadSlip :=
  Eq.symm <|
    ThreeOperationMeasurement.fastestCandidate_unique
      ekgLoadSlip_fastest
      minimal
      ekgThreeOperationMeasurement_separates_support

-- `ekg_probe` is an elaborator diagnostic. It asks Lean to elaborate the
-- following term under a heartbeat budget and logs whether the term outgrows
-- that budget. It does not store a proof, normalize the proposition, or turn
-- the measurement into a theorem.
--
-- Budget 7 is the smoke pulse. Budget 720 is the full one-clause pulse:
-- 9 fact positions * 8 three-bit assignments * 10 safety.
ekg_probe 7 =>
  ekgThreeOperationMeasurement.HeartbeatSeparatesOn ekgMeasuredSupport

ekg_probe 720 =>
  forall candidate,
    SlipMultiset.HeartbeatMinimal
      ekgThreeOperationMeasurement.toHeartbeatSelector
      ekgMeasuredSupport
      candidate ->
        candidate = ekgLoadSlip

end Measurement
