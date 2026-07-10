import Measurement.Episode44

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000
set_option allowUnsafeReducibility true

namespace Measurement

/-
__EPISODE 45__: _Weierstrass by Instantiation_

Episode27 left the convergence as an assumed certificate (`bound_tends_zero`).
But re-reading the scale shows there is no real-analysis door to open at all:

  structure ApproximationScale where
    Magnitude : Type
    zero : Magnitude
    le : Magnitude -> Magnitude -> Prop
    tolerance : Magnitude -> Prop
    le_trans : ...

No `ℝ`, no completeness, no sup-norm.  `TendsToZero` is order-theoretic: for
every admissible tolerance, the sequence is eventually within it.  The squeeze
is already proven for ANY such scale.  So "bringing in Weierstrass" is an
instantiation, not a cathedral.

This episode instantiates it.  The convergence the framework actually achieves
is not epsilon-approximation but *eventual exactness*: once refinement captures a
configuration, the residual is `0`, exactly (Episode27's
`stageTrace_solves_elephant_support`).  So the analytic Weierstrass bound is
replaced by a combinatorial fact: the refinement *exhausts* the countable knot
set, so every configuration's residual is eventually `0`, hence tends to zero.

Stated formally:
* `eventuallyZero_tendsToZero` -- the order-theoretic core: in any scale whose
  tolerances dominate zero, an eventually-zero sequence tends to zero.
* `natScale` -- a genuinely non-trivial scale (`Nat` with its real order, not
  `Unit`, not `le := True`); its tolerances include `0`, so `TendsToZero` here is
  eventual exactness.
* `sample_tendsToZero` -- a concrete run: the instantiation works, with no
  assumed bound.
* `tower_terminalResidual_tendsToZero` -- the discharge: given Episode27's
  residual tower and the combinatorial exhaustion hypothesis (every variation's
  slip is eventually supported), the terminal residual magnitude tends to zero
  *unconditionally* over `natScale`.  No `bound_tends_zero` assumed.

Residue left (honest scope):
This is the framework's order-theoretic Weierstrass -- eventual exactness via
exhaustion -- which is exactly what the spline-sufficiency law means here.  It is
NOT classical sup-norm density over `ℝ`, because the framework never instantiated
`ℝ`.  And the exhaustion hypothesis, though now combinatorial and explicit
(rather than an opaque analytic certificate), is still a hypothesis; constructing
a concrete exhausting tower from the rational enumeration is the next step.
-/

/-- A sequence is eventually exactly the scale's zero. -/
def EventuallyZero (s : ApproximationScale) (seq : Nat -> s.Magnitude) : Prop :=
  exists N, forall n, N <= n -> seq n = s.zero

/-- The order-theoretic Weierstrass core: in any scale whose tolerances all
dominate zero, an eventually-zero sequence tends to zero.  No reals, no sup-norm
-- just a transitive order and a notion of "small". -/
theorem eventuallyZero_tendsToZero (s : ApproximationScale)
    (h0 : forall epsilon, s.tolerance epsilon -> s.le s.zero epsilon)
    (seq : Nat -> s.Magnitude) (he : EventuallyZero s seq) :
    s.TendsToZero seq := by
  obtain ⟨N, hN⟩ := he
  intro epsilon hepsilon
  refine ⟨N, fun n hn => ?_⟩
  rw [hN n hn]
  exact h0 epsilon hepsilon

/-- A genuinely non-trivial approximation scale: `Nat` with its real order.  Not
`Unit`, not `le := True`.  Tolerances include `0`, so `TendsToZero` here is
eventual exactness -- stronger than epsilon-approximation, and exactly what the
discrete framework delivers. -/
def natScale : ApproximationScale where
  Magnitude := Nat
  zero := 0
  le := Nat.le
  tolerance := fun _ => True
  le_trans := fun h1 h2 => Nat.le_trans h1 h2

theorem natScale_zero_le :
    forall epsilon, natScale.tolerance epsilon -> natScale.le natScale.zero epsilon := by
  intro epsilon _
  exact Nat.zero_le epsilon

/-- A concrete run: a residual that becomes `0` from stage `1` on tends to zero
in `natScale` -- the instantiation works, with no assumed bound. -/
def sampleResidual : Nat -> Nat := fun n => if n = 0 then 1 else 0

theorem sample_eventuallyZero : EventuallyZero natScale sampleResidual := by
  refine ⟨1, fun n hn => ?_⟩
  have hne : n ≠ 0 := by omega
  show sampleResidual n = 0
  simp [sampleResidual, hne]

theorem sample_tendsToZero : natScale.TendsToZero sampleResidual :=
  eventuallyZero_tendsToZero natScale natScale_zero_le sampleResidual sample_eventuallyZero

/-- The discharge.  Given Episode27's residual tower over `natScale` and the
combinatorial exhaustion hypothesis -- every variation's slip is eventually in
the support -- the terminal residual magnitude tends to zero, *unconditionally*.
`bound_tends_zero` is no longer assumed; it is proven from exhaustion plus
`stageTrace_solves_elephant_support`.  This is the spline-sufficiency law made a
theorem: the residual does not approximate zero, it becomes zero, because
refinement runs out of distinguishable configurations to leave unsupported. -/
theorem tower_terminalResidual_tendsToZero
    {range : AdmissibleRange} {action : FiniteGaugeAction} {path : FiniteGaugePath}
    (completed : CompletedResidualWeierstrassTower range natScale action path)
    (hofzero : completed.residualTower.magnitude.ofInt 0 = natScale.zero)
    (variation : FiniteGaugeVariation)
    (hexhaust :
      exists N, forall n, N <= n ->
        variation.slip ∈
          (completed.completion.approximation.tower.stage n).candidates.entries) :
    natScale.TendsToZero
      (fun n =>
        completed.residualTower.magnitude.ofInt
          ((completed.residualTower.stageTrace n).terminalResidual variation)) := by
  apply eventuallyZero_tendsToZero natScale natScale_zero_le
  obtain ⟨N, hN⟩ := hexhaust
  refine ⟨N, fun n hn => ?_⟩
  have hres :
      (completed.residualTower.stageTrace n).terminalResidual variation = 0 :=
    CompletedResidualWeierstrassTower.stageTrace_solves_elephant_support
      completed n variation (hN n hn)
  simpa [hres] using hofzero

end Measurement
