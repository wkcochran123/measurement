import Measurement.Episode20

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000
set_option allowUnsafeReducibility true

namespace Measurement

/-
__EPISODE 21__: _The Multiset Lanczos Iterator_

Episode20 named the Lanczos/cubic-spline agreement as a certificate.
This episode exposes the finite iterator that can produce such a
certificate.

The candidates form a finite multiset of slips.  The multiset is the
unordered field of admissible attempts; the Lanczos computation is an
ordered trace produced by repeatedly consuming one slip from that field.
Thus the bag and the execution order are separate objects.

The local theorem proved here is the order-stable support part: a completed
trace solves its terminal residual on the knots it represents.  A stronger
global solvedness field is still carried for the older residue-collapse
certificate; support-local claims below use the knot-local field.
-/

structure SlipMultiset where
  entries : List Bullshit

namespace SlipMultiset

def empty : SlipMultiset where
  entries := []

def singleton (slip : Bullshit) : SlipMultiset where
  entries := [slip]

def cons (slip : Bullshit) (knots : SlipMultiset) : SlipMultiset where
  entries := slip :: knots.entries

def length (knots : SlipMultiset) : Nat :=
  knots.entries.length

def variations (knots : SlipMultiset) : List FiniteGaugeVariation :=
  knots.entries.map fun slip => { slip := slip }

inductive Consumes : SlipMultiset -> Bullshit -> SlipMultiset -> Prop where
  | head (slip : Bullshit) (remaining : List Bullshit) :
      Consumes ⟨slip :: remaining⟩ slip ⟨remaining⟩
  | tail (head : Bullshit) {knots next : SlipMultiset} {slip : Bullshit} :
      Consumes knots slip next ->
      Consumes ⟨head :: knots.entries⟩ slip ⟨head :: next.entries⟩

namespace Consumes

theorem membership_selected
    {knots remaining : SlipMultiset} {slip : Bullshit}
    (consumes : Consumes knots slip remaining) :
    slip ∈ knots.entries := by
  induction consumes with
  | head slip remaining =>
      simp
  | tail head consumes ih =>
      simp [ih]

theorem length_decreases
    {knots remaining : SlipMultiset} {slip : Bullshit}
    (consumes : Consumes knots slip remaining) :
    remaining.length < knots.length := by
  induction consumes with
  | head slip remaining =>
      simp [SlipMultiset.length]
  | tail head consumes ih =>
      simp [SlipMultiset.length]
      exact ih

theorem remaining_members_were_members
    {knots remaining : SlipMultiset} {slip candidate : Bullshit}
    (consumes : Consumes knots slip remaining)
    (h : candidate ∈ remaining.entries) :
    candidate ∈ knots.entries := by
  induction consumes with
  | head slip remaining =>
      simp at h
      simp [h]
  | tail head consumes ih =>
      simp at h
      rcases h with h | h
      · simp [h]
      · exact List.Mem.tail head (ih h)

theorem exists_of_mem
    {knots : SlipMultiset} {slip : Bullshit}
    (h : slip ∈ knots.entries) :
    exists remaining,
      Consumes knots slip remaining := by
  cases knots with
  | mk entries =>
      induction entries with
      | nil =>
          cases h
      | cons head tail ih =>
          simp at h
          rcases h with hHead | hTail
          · subst head
            exact ⟨⟨tail⟩, Consumes.head slip tail⟩
          · rcases ih hTail with ⟨remaining, consumes⟩
            exact
              ⟨⟨head :: remaining.entries⟩,
                Consumes.tail head consumes⟩

end Consumes

theorem variations_mem_iff
    (knots : SlipMultiset) (variation : FiniteGaugeVariation) :
    variation ∈ knots.variations <->
      variation.slip ∈ knots.entries := by
  constructor
  · intro h
    simp [variations] at h
    rcases h with ⟨slip, hSlip, hEq⟩
    cases variation
    simp at hEq
    simpa [hEq] using hSlip
  · intro h
    cases variation
    simp [variations, h]

def sameSupport (left right : SlipMultiset) : Prop :=
  forall slip,
    slip ∈ left.entries <-> slip ∈ right.entries

theorem sameSupport_refl (knots : SlipMultiset) :
    knots.sameSupport knots := by
  intro slip
  exact Iff.rfl

theorem sameSupport_of_eq
    {left right : SlipMultiset}
    (h : left = right) :
    left.sameSupport right := by
  subst right
  exact sameSupport_refl left

end SlipMultiset

def cubicSplineBalancedOn
    (support : SlipMultiset)
    (action : FiniteGaugeAction) (path : FiniteGaugePath) : Prop :=
  action.admits path /\
    forall variation,
      variation.slip ∈ support.entries ->
        cubicSplineResidual action path variation = 0

theorem cubicSplineBalanced_balancedOn
    {action : FiniteGaugeAction} {path : FiniteGaugePath}
    {support : SlipMultiset}
    (h : cubicSplineBalanced action path) :
    cubicSplineBalancedOn support action path :=
  ⟨h.left,
    by
      intro variation _hSupport
      exact h.right variation⟩

structure TridiagonalStencil where
  lower : Int
  diagonal : Int
  upper : Int

structure LanczosWindow where
  previous : FiniteGaugeVariation -> Int
  current : FiniteGaugeVariation -> Int
  next : FiniteGaugeVariation -> Int

namespace TridiagonalStencil

def apply
    (stencil : TridiagonalStencil) (window : LanczosWindow)
    (variation : FiniteGaugeVariation) : Int :=
  stencil.lower * window.previous variation +
    stencil.diagonal * window.current variation +
      stencil.upper * window.next variation

end TridiagonalStencil

namespace LanczosWindow

def constant (residual : FiniteGaugeVariation -> Int) : LanczosWindow where
  previous := residual
  current := residual
  next := residual

end LanczosWindow

def identityTridiagonalStencil : TridiagonalStencil where
  lower := 0
  diagonal := 1
  upper := 0

structure LanczosState where
  residual : FiniteGaugeVariation -> Int
  window : LanczosWindow
  stencil : TridiagonalStencil

namespace LanczosState

def fromResidual (residual : FiniteGaugeVariation -> Int) : LanczosState where
  residual := residual
  window := LanczosWindow.constant residual
  stencil := identityTridiagonalStencil

end LanczosState

structure LanczosStep
    (state next : LanczosState) (slip : Bullshit) : Prop where
  law :
    forall variation,
      next.residual variation =
        state.stencil.apply state.window variation

namespace LanczosStep

theorem selected
    {state next : LanczosState} {slip : Bullshit}
    (step : LanczosStep state next slip) :
    next.residual { slip := slip } =
      state.stencil.apply state.window { slip := slip } :=
  step.law { slip := slip }

def identity
    (residual : FiniteGaugeVariation -> Int) (slip : Bullshit) :
    LanczosStep
      (LanczosState.fromResidual residual)
      (LanczosState.fromResidual residual)
      slip where
  law := by
    intro variation
    simp [LanczosState.fromResidual, TridiagonalStencil.apply,
      identityTridiagonalStencil, LanczosWindow.constant]

end LanczosStep

inductive LanczosIterates :
    SlipMultiset -> LanczosState -> LanczosState -> Prop where
  | done (state : LanczosState) :
      LanczosIterates SlipMultiset.empty state state
  | step
      {knots remaining : SlipMultiset}
      {state next terminal : LanczosState}
      {slip : Bullshit} :
      SlipMultiset.Consumes knots slip remaining ->
      LanczosStep state next slip ->
      LanczosIterates remaining next terminal ->
      LanczosIterates knots state terminal

structure OrderedMultisetLanczosTrace
    (action : FiniteGaugeAction) (path : FiniteGaugePath) where
  knots : SlipMultiset
  initial : LanczosState
  terminal : LanczosState
  iterates : LanczosIterates knots initial terminal
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

namespace OrderedMultisetLanczosTrace

def terminalResidual
    {action : FiniteGaugeAction} {path : FiniteGaugePath}
    (trace : OrderedMultisetLanczosTrace action path)
    (variation : FiniteGaugeVariation) : Int :=
  trace.terminal.residual variation

theorem terminalResidual_eq_zero
    {action : FiniteGaugeAction} {path : FiniteGaugePath}
    (trace : OrderedMultisetLanczosTrace action path)
    (variation : FiniteGaugeVariation) :
    trace.terminalResidual variation = 0 :=
  trace.terminal_solved variation

theorem terminalResidual_eq_zero_on
    {action : FiniteGaugeAction} {path : FiniteGaugePath}
    (trace : OrderedMultisetLanczosTrace action path)
    (variation : FiniteGaugeVariation)
    (h : variation.slip ∈ trace.knots.entries) :
    trace.terminalResidual variation = 0 :=
  trace.terminal_solved_on variation h

theorem terminalResidual_matches_cubic
    {action : FiniteGaugeAction} {path : FiniteGaugePath}
    (trace : OrderedMultisetLanczosTrace action path)
    (variation : FiniteGaugeVariation) :
    trace.terminalResidual variation =
      cubicSplineResidual action path variation :=
  trace.terminal_matches_cubic variation

theorem cubicSplineResidual_eq_zero_on
    {action : FiniteGaugeAction} {path : FiniteGaugePath}
    (trace : OrderedMultisetLanczosTrace action path)
    (variation : FiniteGaugeVariation)
    (h : variation.slip ∈ trace.knots.entries) :
    cubicSplineResidual action path variation = 0 := by
  exact Eq.trans
    (Eq.symm (trace.terminalResidual_matches_cubic variation))
    (trace.terminalResidual_eq_zero_on variation h)

theorem toCubicSplineBalancedOn
    {action : FiniteGaugeAction} {path : FiniteGaugePath}
    (trace : OrderedMultisetLanczosTrace action path) :
    cubicSplineBalancedOn trace.knots action path :=
  ⟨trace.admits,
    by
      intro variation h
      exact trace.cubicSplineResidual_eq_zero_on variation h⟩

def toLanczosCubicSpline
    {action : FiniteGaugeAction} {path : FiniteGaugePath}
    (trace : OrderedMultisetLanczosTrace action path) :
    LanczosCubicSpline action path where
  tridiagonalResidual := trace.terminal.residual
  splineResidual := cubicSplineResidual action path
  sameResidual := trace.terminal_matches_cubic
  solved := trace.terminal_solved
  matchesGauge := by
    intro variation
    rfl
  admits := trace.admits

theorem eulerLagrange
    {action : FiniteGaugeAction} {path : FiniteGaugePath}
    (trace : OrderedMultisetLanczosTrace action path) :
    (DiscreteGaugeDerivative.fromAction action).eulerLagrange path :=
  trace.toLanczosCubicSpline.eulerLagrange

theorem stationary
    {action : FiniteGaugeAction} {path : FiniteGaugePath}
    (trace : OrderedMultisetLanczosTrace action path) :
    (DiscreteGaugeDerivative.fromAction action).gauge.stationaryAt path :=
  trace.toLanczosCubicSpline.stationary

theorem splineSufficient
    {action : FiniteGaugeAction} {path : FiniteGaugePath}
    (trace : OrderedMultisetLanczosTrace action path) :
    Measurement.splineSufficient action path :=
  law_of_spline_sufficiency trace.toLanczosCubicSpline

theorem residue_eq_truth_zero
    {action : FiniteGaugeAction} {path : FiniteGaugePath}
    (trace : OrderedMultisetLanczosTrace action path) :
    (DiscreteGaugeDerivative.fromAction action).residue path =
      .zero Fact.Truth :=
  trace.toLanczosCubicSpline.residue_eq_truth_zero

theorem terminal_residue_for_any_iteration_order
    {action : FiniteGaugeAction} {path : FiniteGaugePath}
    (trace : OrderedMultisetLanczosTrace action path) :
    (DiscreteGaugeDerivative.fromAction action).residue path =
      .zero Fact.Truth :=
  trace.residue_eq_truth_zero

theorem terminal_residual_for_supported_variations
    {action : FiniteGaugeAction} {path : FiniteGaugePath}
    (trace : OrderedMultisetLanczosTrace action path)
    (variation : FiniteGaugeVariation)
    (h : variation.slip ∈ trace.knots.entries) :
    trace.terminalResidual variation = 0 :=
  trace.terminalResidual_eq_zero_on variation h

end OrderedMultisetLanczosTrace

def traceFromLanczosCertificate
    {action : FiniteGaugeAction} {path : FiniteGaugePath}
    (certificate : LanczosCubicSpline action path) :
    OrderedMultisetLanczosTrace action path where
  knots := SlipMultiset.singleton path.slip
  initial := LanczosState.fromResidual certificate.tridiagonalResidual
  terminal := LanczosState.fromResidual certificate.tridiagonalResidual
  iterates :=
    LanczosIterates.step
      (SlipMultiset.Consumes.head path.slip [])
      (LanczosStep.identity certificate.tridiagonalResidual path.slip)
      (LanczosIterates.done
        (LanczosState.fromResidual certificate.tridiagonalResidual))
  terminal_matches_cubic := by
    intro variation
    exact certificate.lanczos_equals_cubic_residual variation
  terminal_solved := certificate.solved
  terminal_solved_on := by
    intro variation _h
    exact certificate.solved variation
  admits := certificate.admits

def closedFlatOrderedMultisetLanczosTrace
    (action : FiniteGaugeAction) (path : FiniteGaugePath)
    (h : action.closedFlatAt path) :
    OrderedMultisetLanczosTrace action path :=
  traceFromLanczosCertificate
    (closedFlatLanczosCertificate action path h)

def truthTerminalTrace :
    OrderedMultisetLanczosTrace truthTerminalAction truthTerminalPath :=
  closedFlatOrderedMultisetLanczosTrace
    truthTerminalAction
    truthTerminalPath
    (truthTerminalAction_closedFlatAt truthTerminalPath)

theorem truthTerminalTrace_terminalResidual_eq_zero
    (variation : FiniteGaugeVariation) :
    truthTerminalTrace.terminalResidual variation = 0 :=
  truthTerminalTrace.terminalResidual_eq_zero variation

theorem truthTerminalTrace_residue_eq_truth_zero :
    (DiscreteGaugeDerivative.fromAction truthTerminalAction).residue
      truthTerminalPath = .zero Fact.Truth :=
  truthTerminal_residue_eq_truth_zero

end Measurement
