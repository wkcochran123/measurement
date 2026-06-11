import Measurement.Episode24

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000
set_option allowUnsafeReducibility true

namespace Measurement

/-
__EPISODE 25__: _Heartbeat Selection_

Episode24 derived the two middle-node Euler-Lagrange equations from
partitioned finite-elephant support.  The remaining choice policy is the
order in which a finite elephant's candidate multiset is consumed.

This episode makes that policy explicit: a heartbeat selector assigns a
cost to each candidate slip, and the iterator may consume only a
heartbeat-minimal candidate from the current multiset.  Thus the multiset
is still the finite support, while the heartbeat selector supplies the
semi-arbitrary but measurable ordering.
-/

structure HeartbeatSelector where
  heartbeat : Bullshit -> Nat

namespace SlipMultiset

def HeartbeatMinimal
    (selector : HeartbeatSelector) (knots : SlipMultiset)
    (slip : Bullshit) : Prop :=
  slip ∈ knots.entries /\
    forall candidate,
      candidate ∈ knots.entries ->
        selector.heartbeat slip <= selector.heartbeat candidate

structure FastestConsumes
    (selector : HeartbeatSelector) (knots : SlipMultiset)
    (slip : Bullshit) (remaining : SlipMultiset) : Prop where
  consumes : Consumes knots slip remaining
  fastest : HeartbeatMinimal selector knots slip

namespace HeartbeatMinimal

theorem singleton
    (selector : HeartbeatSelector) (slip : Bullshit) :
    HeartbeatMinimal selector (SlipMultiset.singleton slip) slip := by
  constructor
  · simp [SlipMultiset.singleton]
  · intro candidate h
    simp [SlipMultiset.singleton] at h
    subst candidate
    exact Nat.le_refl _

theorem exists_of_nonempty
    (selector : HeartbeatSelector) {knots : SlipMultiset}
    (hNonempty : knots.entries ≠ []) :
    exists slip,
      HeartbeatMinimal selector knots slip := by
  cases knots with
  | mk entries =>
      induction entries with
      | nil =>
          contradiction
      | cons head tail ih =>
          by_cases hTail : tail = []
          · subst tail
            exact
              ⟨head,
                by
                  constructor
                  · simp
                  · intro candidate hCandidate
                    simp at hCandidate
                    subst candidate
                    exact Nat.le_refl _⟩
          · rcases ih hTail with ⟨slip, hMinimal⟩
            by_cases hHead :
                selector.heartbeat head <= selector.heartbeat slip
            · exact
                ⟨head,
                  by
                    constructor
                    · simp
                    · intro candidate hCandidate
                      simp at hCandidate
                      rcases hCandidate with hCandidate | hCandidate
                      · subst candidate
                        exact Nat.le_refl _
                      · exact
                          Nat.le_trans
                            hHead
                            (hMinimal.right candidate hCandidate)⟩
            · exact
                ⟨slip,
                  by
                    constructor
                    · simp [hMinimal.left]
                    · intro candidate hCandidate
                      simp at hCandidate
                      rcases hCandidate with hCandidate | hCandidate
                      · subst candidate
                        exact Nat.le_of_lt (Nat.lt_of_not_ge hHead)
                      · exact hMinimal.right candidate hCandidate⟩

end HeartbeatMinimal

namespace FastestConsumes

def singleton
    (selector : HeartbeatSelector) (slip : Bullshit) :
    FastestConsumes
      selector
      (SlipMultiset.singleton slip)
      slip
      SlipMultiset.empty where
  consumes := Consumes.head slip []
  fastest := HeartbeatMinimal.singleton selector slip

theorem exists_of_nonempty
    (selector : HeartbeatSelector) {knots : SlipMultiset}
    (hNonempty : knots.entries ≠ []) :
    exists slip remaining,
      FastestConsumes selector knots slip remaining := by
  rcases HeartbeatMinimal.exists_of_nonempty selector hNonempty with
    ⟨slip, hMinimal⟩
  rcases Consumes.exists_of_mem hMinimal.left with
    ⟨remaining, consumes⟩
  exact
    ⟨slip, remaining,
      { consumes := consumes
        fastest := hMinimal }⟩

end FastestConsumes

end SlipMultiset

inductive HeartbeatLanczosIterates
    (selector : HeartbeatSelector) :
    SlipMultiset -> LanczosState -> LanczosState -> Prop where
  | done (state : LanczosState) :
      HeartbeatLanczosIterates selector SlipMultiset.empty state state
  | step
      {knots remaining : SlipMultiset}
      {state next terminal : LanczosState}
      {slip : Bullshit} :
      SlipMultiset.FastestConsumes selector knots slip remaining ->
      LanczosStep state next slip ->
      HeartbeatLanczosIterates selector remaining next terminal ->
      HeartbeatLanczosIterates selector knots state terminal

namespace HeartbeatLanczosIterates

theorem toLanczosIterates
    {selector : HeartbeatSelector}
    {knots : SlipMultiset} {initial terminal : LanczosState}
    (iterates :
      HeartbeatLanczosIterates selector knots initial terminal) :
    LanczosIterates knots initial terminal := by
  induction iterates with
  | done state =>
      exact LanczosIterates.done state
  | step fastestConsumes lanczosStep rest ih =>
      exact
        LanczosIterates.step
          fastestConsumes.consumes
          lanczosStep
          ih

end HeartbeatLanczosIterates

structure HeartbeatOrderedMultisetLanczosTrace
    (selector : HeartbeatSelector)
    (action : FiniteGaugeAction) (path : FiniteGaugePath) where
  knots : SlipMultiset
  initial : LanczosState
  terminal : LanczosState
  iterates : HeartbeatLanczosIterates selector knots initial terminal
  terminal_matches_cubic :
    forall variation,
      terminal.residual variation = cubicSplineResidual action path variation
  terminal_solved :
    forall variation,
      terminal.residual variation = 0
  terminal_solved_on :
    forall variation,
      variation.slip ∈ knots.entries ->
        terminal.residual variation = 0
  admits : action.admits path

namespace HeartbeatOrderedMultisetLanczosTrace

def toOrderedMultisetLanczosTrace
    {selector : HeartbeatSelector}
    {action : FiniteGaugeAction} {path : FiniteGaugePath}
    (trace : HeartbeatOrderedMultisetLanczosTrace selector action path) :
    OrderedMultisetLanczosTrace action path where
  knots := trace.knots
  initial := trace.initial
  terminal := trace.terminal
  iterates := trace.iterates.toLanczosIterates
  terminal_matches_cubic := trace.terminal_matches_cubic
  terminal_solved := trace.terminal_solved
  terminal_solved_on := trace.terminal_solved_on
  admits := trace.admits

def terminalResidual
    {selector : HeartbeatSelector}
    {action : FiniteGaugeAction} {path : FiniteGaugePath}
    (trace : HeartbeatOrderedMultisetLanczosTrace selector action path)
    (variation : FiniteGaugeVariation) : Int :=
  trace.terminal.residual variation

theorem terminalResidual_eq_zero
    {selector : HeartbeatSelector}
    {action : FiniteGaugeAction} {path : FiniteGaugePath}
    (trace : HeartbeatOrderedMultisetLanczosTrace selector action path)
    (variation : FiniteGaugeVariation) :
    trace.terminalResidual variation = 0 :=
  trace.terminal_solved variation

theorem terminalResidual_eq_zero_on
    {selector : HeartbeatSelector}
    {action : FiniteGaugeAction} {path : FiniteGaugePath}
    (trace : HeartbeatOrderedMultisetLanczosTrace selector action path)
    (variation : FiniteGaugeVariation)
    (h : variation.slip ∈ trace.knots.entries) :
    trace.terminalResidual variation = 0 :=
  trace.terminal_solved_on variation h

theorem eulerLagrange
    {selector : HeartbeatSelector}
    {action : FiniteGaugeAction} {path : FiniteGaugePath}
    (trace : HeartbeatOrderedMultisetLanczosTrace selector action path) :
    (DiscreteGaugeDerivative.fromAction action).eulerLagrange path :=
  trace.toOrderedMultisetLanczosTrace.eulerLagrange

theorem residue_eq_truth_zero
    {selector : HeartbeatSelector}
    {action : FiniteGaugeAction} {path : FiniteGaugePath}
    (trace : HeartbeatOrderedMultisetLanczosTrace selector action path) :
    (DiscreteGaugeDerivative.fromAction action).residue path =
      .zero Fact.Truth :=
  trace.toOrderedMultisetLanczosTrace.residue_eq_truth_zero

theorem fastest_heartbeat_order_sufficient
    {selector : HeartbeatSelector}
    {action : FiniteGaugeAction} {path : FiniteGaugePath}
    (trace : HeartbeatOrderedMultisetLanczosTrace selector action path) :
    Measurement.splineSufficient action path :=
  trace.toOrderedMultisetLanczosTrace.splineSufficient

end HeartbeatOrderedMultisetLanczosTrace

def heartbeatTraceFromLanczosCertificate
    (selector : HeartbeatSelector)
    {action : FiniteGaugeAction} {path : FiniteGaugePath}
    (certificate : LanczosCubicSpline action path) :
    HeartbeatOrderedMultisetLanczosTrace selector action path where
  knots := SlipMultiset.singleton path.slip
  initial := LanczosState.fromResidual certificate.tridiagonalResidual
  terminal := LanczosState.fromResidual certificate.tridiagonalResidual
  iterates :=
    HeartbeatLanczosIterates.step
      (SlipMultiset.FastestConsumes.singleton selector path.slip)
      (LanczosStep.identity certificate.tridiagonalResidual path.slip)
      (HeartbeatLanczosIterates.done
        (LanczosState.fromResidual certificate.tridiagonalResidual))
  terminal_matches_cubic := by
    intro variation
    exact certificate.lanczos_equals_cubic_residual variation
  terminal_solved := certificate.solved
  terminal_solved_on := by
    intro variation _h
    exact certificate.solved variation
  admits := certificate.admits

structure HeartbeatPartitionedLanczosApproximation
    (selector : HeartbeatSelector)
    (action : FiniteGaugeAction) (path : FiniteGaugePath)
    (range : AdmissibleRange) (elephant : FiniteElephant) where
  trace : HeartbeatOrderedMultisetLanczosTrace selector action path
  partitioned : ElephantRealPartition range elephant
  sobolevSpace : PartitionSobolevSpace partitioned.partition
  knots_match : trace.knots = elephant.candidates

namespace HeartbeatPartitionedLanczosApproximation

def toPartitionedLanczosApproximation
    {selector : HeartbeatSelector}
    {action : FiniteGaugeAction} {path : FiniteGaugePath}
    {range : AdmissibleRange} {elephant : FiniteElephant}
    (approximation :
      HeartbeatPartitionedLanczosApproximation
        selector action path range elephant) :
    PartitionedLanczosApproximation action path range elephant where
  trace := approximation.trace.toOrderedMultisetLanczosTrace
  partitioned := approximation.partitioned
  sobolevSpace := approximation.sobolevSpace
  knots_match := approximation.knots_match

theorem eulerLagrange
    {selector : HeartbeatSelector}
    {action : FiniteGaugeAction} {path : FiniteGaugePath}
    {range : AdmissibleRange} {elephant : FiniteElephant}
    (approximation :
      HeartbeatPartitionedLanczosApproximation
        selector action path range elephant) :
    (DiscreteGaugeDerivative.fromAction action).eulerLagrange path :=
  approximation.toPartitionedLanczosApproximation.eulerLagrange

theorem weakResidual_eq_zero
    {selector : HeartbeatSelector}
    {action : FiniteGaugeAction} {path : FiniteGaugePath}
    {range : AdmissibleRange} {elephant : FiniteElephant}
    (approximation :
      HeartbeatPartitionedLanczosApproximation
        selector action path range elephant)
    (test : FiniteGaugeVariation) :
    approximation.trace.terminalResidual test = 0 :=
  approximation.trace.terminalResidual_eq_zero test

theorem terminal_solved_on
    {selector : HeartbeatSelector}
    {action : FiniteGaugeAction} {path : FiniteGaugePath}
    {range : AdmissibleRange} {elephant : FiniteElephant}
    (approximation :
      HeartbeatPartitionedLanczosApproximation
        selector action path range elephant)
    (test : FiniteGaugeVariation)
    (h : test.slip ∈ elephant.candidates.entries) :
    approximation.trace.terminalResidual test = 0 :=
  approximation.trace.terminalResidual_eq_zero_on test
    (by
      simpa [approximation.knots_match] using h)

theorem weakResidual_eq_zero_on
    {selector : HeartbeatSelector}
    {action : FiniteGaugeAction} {path : FiniteGaugePath}
    {range : AdmissibleRange} {elephant : FiniteElephant}
    (approximation :
      HeartbeatPartitionedLanczosApproximation
        selector action path range elephant)
    (test : FiniteGaugeVariation)
    (h : test.slip ∈ elephant.candidates.entries) :
    approximation.trace.terminalResidual test = 0 :=
  approximation.terminal_solved_on test h

theorem spline_represents_supported_data
    {selector : HeartbeatSelector}
    {action : FiniteGaugeAction} {path : FiniteGaugePath}
    {range : AdmissibleRange} {elephant : FiniteElephant}
    (approximation :
      HeartbeatPartitionedLanczosApproximation
        selector action path range elephant)
    (test : FiniteGaugeVariation)
    (h : test.slip ∈ elephant.candidates.entries) :
    approximation.trace.terminalResidual test = 0 :=
  approximation.terminal_solved_on test h

theorem residue_eq_truth_zero
    {selector : HeartbeatSelector}
    {action : FiniteGaugeAction} {path : FiniteGaugePath}
    {range : AdmissibleRange} {elephant : FiniteElephant}
    (approximation :
      HeartbeatPartitionedLanczosApproximation
        selector action path range elephant) :
    (DiscreteGaugeDerivative.fromAction action).residue path =
      .zero Fact.Truth :=
  approximation.toPartitionedLanczosApproximation.residue_eq_truth_zero

end HeartbeatPartitionedLanczosApproximation

structure CubicHeartbeatPartitionedLanczosApproximation
    (selector : HeartbeatSelector)
    (action : FiniteGaugeAction) (path : CubicGaugePath)
    (range : AdmissibleRange) where
  support : CubicMiddleNodeSupport range path
  leftApproximation :
    HeartbeatPartitionedLanczosApproximation
      selector
      action
      path.leftFinitePath
      range
      support.leftElephant
  rightApproximation :
    HeartbeatPartitionedLanczosApproximation
      selector
      action
      path.rightFinitePath
      range
      support.rightElephant

namespace CubicHeartbeatPartitionedLanczosApproximation

def toCubicPartitionedLanczosApproximation
    {selector : HeartbeatSelector}
    {action : FiniteGaugeAction} {path : CubicGaugePath}
    {range : AdmissibleRange}
    (approximation :
      CubicHeartbeatPartitionedLanczosApproximation
        selector action path range) :
    CubicPartitionedLanczosApproximation action path range where
  support := approximation.support
  leftApproximation :=
    approximation.leftApproximation.toPartitionedLanczosApproximation
  rightApproximation :=
    approximation.rightApproximation.toPartitionedLanczosApproximation

theorem partitions_derive_two_middle_equations_by_fastest_heartbeat
    {selector : HeartbeatSelector}
    {action : FiniteGaugeAction} {path : CubicGaugePath}
    {range : AdmissibleRange}
    (approximation :
      CubicHeartbeatPartitionedLanczosApproximation
        selector action path range) :
    (forall variation,
      approximation.support.leftSupportedVariation variation ->
        path.leftMiddleResidual action variation = 0) /\
    (forall variation,
      approximation.support.rightSupportedVariation variation ->
        path.rightMiddleResidual action variation = 0) :=
  CubicPartitionedLanczosApproximation.partitions_derive_two_middle_equations
    approximation.toCubicPartitionedLanczosApproximation

end CubicHeartbeatPartitionedLanczosApproximation

def truthHeartbeatSelector : HeartbeatSelector where
  heartbeat := fun _ => 0

def truthHeartbeatTerminalTrace :
    HeartbeatOrderedMultisetLanczosTrace
      truthHeartbeatSelector
      truthTerminalAction
      truthTerminalPath :=
  heartbeatTraceFromLanczosCertificate
    truthHeartbeatSelector
    (closedFlatLanczosCertificate
      truthTerminalAction
      truthTerminalPath
      (truthTerminalAction_closedFlatAt truthTerminalPath))

def truthHeartbeatPartitionedLanczosApproximation :
    HeartbeatPartitionedLanczosApproximation
      truthHeartbeatSelector
      truthTerminalAction
      truthTerminalPath
      truthAdmissibleRange
      truthElephantSample where
  trace := truthHeartbeatTerminalTrace
  partitioned := truthElephantRealPartition
  sobolevSpace := truthPartitionSobolevSpace
  knots_match := rfl

theorem truthFastestHeartbeat_residue_eq_truth_zero :
    (DiscreteGaugeDerivative.fromAction truthTerminalAction).residue
      truthTerminalPath = .zero Fact.Truth :=
  truthHeartbeatTerminalTrace.residue_eq_truth_zero

end Measurement
