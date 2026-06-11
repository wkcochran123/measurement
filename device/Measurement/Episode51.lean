import Measurement.Episode50

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000
set_option allowUnsafeReducibility true

namespace Measurement

/-
__EPISODE 51__: _The Fourth Telling of the Derivative_

The Frechet derivative has been told three times in this corpus.

Episode10 told it as STORY: `Variation`'s ladder `.newton -> .gateaux ->
.frechet`, with `BigRedDogProcess.transmute` adding the residue on the way
up.  Episode18 told it as STRUCTURE: `FrechetGauge`, a `linearPart` and a
`remainder`, and -- without saying the word -- an existence proof
(`fromAction_remainder_zero`: the gauge built from the action approximates
with remainder EXACTLY zero).  The Formalization told it as PRODUCTION:
`defaultFiniteGaugeClosure` (FiniteGaugeEquation.lean), the canonical
gateaux-to-frechet production rule, whose normal-form and determinism
theorems attach to `finiteGaugeEquation` one definition up.

This is the fourth telling, the final act: the THEOREM.

First, the reveal, and it is one `rfl` long: `cubicSplineResidual` -- the
residual that Episode20 named, Episode21 iterated, Episode27 squeezed,
Episode45 made eventually exact, and Episode50 drove to zero -- IS the
Frechet derivative.  `cubicSplineResidual action path v` and
`action.firstVariation path v` are the same term.  The tower was never
chasing an auxiliary quantity; it was driving the derivative of the action
to zero.  The finish line was crossed in Episode50; this episode reads the
name on the tape.

Second, the theorem the whole corpus has been rehearsing: the derivative
EXISTS (Episode18's gauge -- one gauge, all paths -- now filed as
`frechetDerivative_exists`) and is therefore UNIQUE
(`frechetDerivative_unique`: any gauge that approximates the action at a
path carries the same linear part AT THAT PATH -- uniqueness by exact
determination, which is what classical Frechet uniqueness degenerates to
when the remainder is identically zero).  Existence and uniqueness are
packaged in `frechetDerivative_existsUnique`.  The same uniqueness holds
slot by slot: `linearization_unique` pins the single-node linear part (the
order-one mirror of Episode31's `secondVariation_remainder_unique`), and
`cubic_left_slot_unique` / `cubic_right_slot_unique` pin the cubic
expansion's two first-order slots against their own one-coordinate
matching conditions (Episode24's difference identifications); Episode31
pins the second variation given the canonical first-order terms.  Each
slot is the unique solution of ITS OWN matching condition -- the bare
three-term sum does not determine its terms (shift a constant between left
and right and nothing complains), and the corpus does not pretend
otherwise.  The expansion does not approximate -- it terminates
(`taylor_terminates_at_order_two`).

Honest scope on the word "linear": there is no vector space of variations
here, so linearity of the linear part is not even stateable.  The slot
where linearity would sit is occupied by uniqueness -- which is the job
linearity does for the classical Frechet derivative anyway.  And the o(h)
condition is satisfied in the strongest form a remainder can manage:
identically zero, no norm required.  The continuum derivative behind
Episode38's square-root door remains a door.

The two showcase actions read out in derivative language exactly as
Episodes 48-50 staged them: the telescoping null Lagrangian has derivative
ZERO everywhere (`telescoping_derivative_zero` -- everything was a
critical point of it all along, which is why the tower accepted it), and
the discriminating action has nonzero derivative on every path
(`discriminating_derivative_nonzero` -- which is why no tag-covering
trace, hence no exhausting tower, can carry it: Episode48's
`discriminatingAction_no_tag_covering_trace`).
`frechet_crosses_the_finish_line` restates Episode50's unconditional
convergence with the name attached: the measured Frechet derivative of the
gauge action tends to zero along the produced tower.  And both directions
of the variational principle are now filed at the sequence level:
`flat_actions_cross_too` (every flat pair's derivative reading tends to
zero, not just the showcase), and
`nonzero_residual_fails_eventual_exactness` (a nonzero reading NEVER tends
to zero over `natScale` -- Episode50's header said "false, not unproven";
now there is a theorem to point at).

Stated formally:
* `cubicSplineResidual_eq_firstVariation` -- the reveal, by `rfl`; and
  `frechetDerivative`, the object named at last.
* `frechetDerivative_exists`, `FrechetGauge.approximates_linearPart_eq`,
  `frechetDerivative_unique`, `frechetDerivative_existsUnique` -- it
  exists, and therefore must be unique.
* `FiniteGaugeAction.IsLinearization`, `linearization_unique` -- order-one
  uniqueness, mirroring Episode31 at order two.
* `cubic_left_slot_unique`, `cubic_right_slot_unique` -- the cubic
  expansion's first-order slots, each pinned by its own matching condition.
* `taylor_terminates_at_order_two` -- the expansion is exact, slot by slot.
* `telescoping_derivative_zero`, `discriminating_derivative_nonzero` --
  the showcases, in derivative language.
* `frechet_crosses_the_finish_line`, `flat_actions_cross_too`,
  `nonzero_residual_fails_eventual_exactness` -- the limit, both
  directions, with the right name on it.

Residue left (honest scope):
at the sequence level, none: existence, uniqueness, and Taylor termination
hold for every action and path, and both directions of the limit are
filed.  One construction stays unfiled: the produced TOWER for an
arbitrary flat pair -- Episode50 built it for the showcase pair, and the
generalization is mechanical (Episode50's pattern with `telescopingAction`
abstracted), but mechanical is not filed.  What remains beyond the finite
level is behind the same door it has always been behind: Episode38's,
marked ℝ.
-/

/-- The reveal: the spline residual the tower has been squeezing since
Episode20 IS the Frechet derivative.  One `rfl`. -/
theorem cubicSplineResidual_eq_firstVariation
    (action : FiniteGaugeAction) (path : FiniteGaugePath)
    (variation : FiniteGaugeVariation) :
    cubicSplineResidual action path variation =
      action.firstVariation path variation := rfl

/-- The object, named at last: the canonical Frechet derivative of the
gauge action. -/
def frechetDerivative (action : FiniteGaugeAction) :
    FiniteGaugePath -> FiniteGaugeVariation -> Int :=
  action.firstVariation

/-- EXISTENCE: one gauge, all paths -- the gauge built from the action
approximates it everywhere, with remainder exactly zero.  Episode18 proved
this without filing it; filed. -/
theorem frechetDerivative_exists (action : FiniteGaugeAction) :
    exists gauge : FrechetGauge,
      gauge.action = action /\
        forall path variation, gauge.approximates path variation :=
  ⟨FrechetGauge.fromAction action, rfl,
    fun path variation =>
      FrechetGauge.fromAction_remainder_zero action path variation⟩

/-- The uniqueness engine: ANY gauge that approximates at a path carries
the first variation as its linear part.  The proof is the classical one --
two candidates matching the same difference must be equal -- in three
lines. -/
theorem FrechetGauge.approximates_linearPart_eq
    (gauge : FrechetGauge) (path : FiniteGaugePath)
    (happrox : forall variation, gauge.approximates path variation)
    (variation : FiniteGaugeVariation) :
    gauge.linearPart path variation =
      gauge.action.firstVariation path variation := by
  have h := happrox variation
  unfold FrechetGauge.approximates FrechetGauge.remainder
    FrechetGauge.variedValue FrechetGauge.value at h
  rw [gauge.action.firstVariation_eq_composedDifference path variation]
  omega

/-- UNIQUENESS: two gauges that approximate the same action at the same
path have the same linear part there.  It exists, therefore it is unique. -/
theorem frechetDerivative_unique
    (g1 g2 : FrechetGauge) (path : FiniteGaugePath)
    (haction : g1.action = g2.action)
    (h1 : forall variation, g1.approximates path variation)
    (h2 : forall variation, g2.approximates path variation) :
    forall variation,
      g1.linearPart path variation = g2.linearPart path variation := by
  intro variation
  rw [g1.approximates_linearPart_eq path h1 variation,
    g2.approximates_linearPart_eq path h2 variation, haction]

/-- Existence and uniqueness, packaged: there is a gauge approximating the
action at the path, and every other approximating gauge agrees with it on
the linear part. -/
theorem frechetDerivative_existsUnique
    (action : FiniteGaugeAction) (path : FiniteGaugePath) :
    exists gauge : FrechetGauge,
      (gauge.action = action /\
        forall variation, gauge.approximates path variation) /\
        forall other : FrechetGauge,
          other.action = action ->
            (forall variation, other.approximates path variation) ->
              forall variation,
                other.linearPart path variation =
                  gauge.linearPart path variation := by
  refine
    ⟨FrechetGauge.fromAction action,
      ⟨rfl,
        fun variation =>
          FrechetGauge.fromAction_remainder_zero action path variation⟩,
      ?_⟩
  intro other haction happrox variation
  rw [other.approximates_linearPart_eq path happrox variation, haction]
  rfl

/-- A linearization of the action at a path: anything that matches the
composed difference at every variation. -/
def FiniteGaugeAction.IsLinearization
    (action : FiniteGaugeAction) (path : FiniteGaugePath)
    (L : FiniteGaugeVariation -> Int) : Prop :=
  forall variation,
    Int.ofNat (action.composed (variation.apply path)) -
      Int.ofNat (action.composed path) = L variation

/-- Order-one uniqueness, mirroring Episode31's
`secondVariation_remainder_unique` at order two: every linearization IS the
first variation. -/
theorem FiniteGaugeAction.linearization_unique
    (action : FiniteGaugeAction) (path : FiniteGaugePath)
    (L : FiniteGaugeVariation -> Int)
    (hL : action.IsLinearization path L) :
    forall variation, L variation = action.firstVariation path variation := by
  intro variation
  have h := hL variation
  rw [action.firstVariation_eq_composedDifference path variation]
  omega

/-- The left slot's matching condition in the cubic expansion: the
one-coordinate cubic difference (Episode24). -/
def CubicGaugePath.IsLeftSlot
    (action : FiniteGaugeAction) (path : CubicGaugePath)
    (L : FiniteGaugeVariation -> Int) : Prop :=
  forall variation,
    CubicGaugePath.leftCubicDifference action path variation = L variation

/-- The right slot's matching condition in the cubic expansion. -/
def CubicGaugePath.IsRightSlot
    (action : FiniteGaugeAction) (path : CubicGaugePath)
    (L : FiniteGaugeVariation -> Int) : Prop :=
  forall variation,
    CubicGaugePath.rightCubicDifference action path variation = L variation

/-- The cubic expansion's left first-order slot is pinned by its own
matching condition: anything matching the one-coordinate difference IS the
canonical left residual, via Episode24's identification. -/
theorem cubic_left_slot_unique
    (action : FiniteGaugeAction) (path : CubicGaugePath)
    (L : FiniteGaugeVariation -> Int)
    (hL : CubicGaugePath.IsLeftSlot action path L) :
    forall variation,
      L variation =
        CubicGaugePath.leftMiddleResidual action path variation := by
  intro variation
  have h := hL variation
  rw [CubicGaugePath.leftCubicDifference_eq_leftMiddleResidual] at h
  exact h.symm

/-- The right slot, pinned the same way. -/
theorem cubic_right_slot_unique
    (action : FiniteGaugeAction) (path : CubicGaugePath)
    (L : FiniteGaugeVariation -> Int)
    (hL : CubicGaugePath.IsRightSlot action path L) :
    forall variation,
      L variation =
        CubicGaugePath.rightMiddleResidual action path variation := by
  intro variation
  have h := hL variation
  rw [CubicGaugePath.rightCubicDifference_eq_rightMiddleResidual] at h
  exact h.symm

/-- The discrete Taylor expansion terminates: the coupled cubic difference
is EXACTLY first-left + first-right + second, no remainder.  Episode31's
decomposition, restated as the closing of the calculus.  Each slot is
pinned by its own matching condition -- the left and right slots by
`cubic_left_slot_unique` / `cubic_right_slot_unique`, the second variation
by Episode31's `secondVariation_remainder_unique` GIVEN the canonical
first-order terms; the bare three-term sum does not determine its terms. -/
theorem taylor_terminates_at_order_two
    (action : FiniteGaugeAction) (path : CubicGaugePath)
    (variation : CubicGaugeVariation) :
    CubicGaugeVariation.coupledCubicDifference action path variation =
      CubicGaugePath.leftMiddleResidual
          action path (CubicGaugeVariation.leftVariation variation) +
        CubicGaugePath.rightMiddleResidual
          action path (CubicGaugeVariation.rightVariation variation) +
          CubicGaugeVariation.secondVariation action path variation :=
  CubicGaugeVariation.coupledCubicDifference_eq_left_right_plus_secondVariation
    action path variation

/-- The null Lagrangian in derivative language: the telescoping action's
Frechet derivative vanishes identically.  Everything was a critical point
of it all along -- which is why Episode50's tower accepted it. -/
theorem telescoping_derivative_zero
    (path : FiniteGaugePath) (variation : FiniteGaugeVariation) :
    telescopingAction.firstVariation path variation = 0 :=
  FrechetGauge.fromAction_stationaryAt_of_flatAt
    (telescoping_flatAt path) variation

/-- The obstruction in derivative language: the discriminating action has
nonzero Frechet derivative on EVERY path -- which is why no tag-covering
trace, hence no exhausting tower, can carry it (Episode48's
`discriminatingAction_no_tag_covering_trace`). -/
theorem discriminating_derivative_nonzero (path : FiniteGaugePath) :
    exists variation : FiniteGaugeVariation,
      discriminatingAction.firstVariation path variation ≠ 0 := by
  obtain ⟨s, _, hne⟩ := discriminatingAction_obstructed path
  exact ⟨{ slip := s }, hne⟩

/-- The finish line, with the name attached: Episode50's unconditional
convergence is, term for term, the statement that the measured Frechet
derivative of the gauge action tends to zero along the produced tower.
The sequence is constant at zero -- eventual exactness of the strongest
kind -- because the variational principle is not approximately solved but
solved. -/
theorem frechet_crosses_the_finish_line (variation : FiniteGaugeVariation) :
    natScale.TendsToZero
      (fun _ =>
        intActivityMagnitude
          (telescopingAction.firstVariation skeletonPath variation)) :=
  skeleton_unconditional_tendsToZero variation

/-- The finish line generalizes: for EVERY flat (action, path) pair -- not
just the showcase -- the measured derivative reading tends to zero. -/
theorem flat_actions_cross_too
    (action : FiniteGaugeAction) (path : FiniteGaugePath)
    (hflat : action.flatAt path) (variation : FiniteGaugeVariation) :
    natScale.TendsToZero
      (fun _ =>
        intActivityMagnitude (action.firstVariation path variation)) := by
  have h0 : action.firstVariation path variation = 0 :=
    FrechetGauge.fromAction_stationaryAt_of_flatAt hflat variation
  intro epsilon _
  refine ⟨0, fun n _ => ?_⟩
  show
    intActivityMagnitude (action.firstVariation path variation) <= epsilon
  rw [h0, intActivityMagnitude_zero]
  exact Nat.zero_le epsilon

/-- And the other direction, Episode50's header assertion filed as a
theorem: a nonzero residual reading NEVER tends to zero over `natScale`.
For an off-shell configuration, eventual exactness is false, not
unproven. -/
theorem nonzero_residual_fails_eventual_exactness
    (action : FiniteGaugeAction) (path : FiniteGaugePath)
    (variation : FiniteGaugeVariation)
    (hne : cubicSplineResidual action path variation ≠ 0) :
    ¬ natScale.TendsToZero
        (fun _ =>
          intActivityMagnitude
            (cubicSplineResidual action path variation)) := by
  intro h
  obtain ⟨stage, hstage⟩ := h natScale.zero trivial
  have hle := hstage stage (Nat.le_refl stage)
  have hzero :
      intActivityMagnitude (cubicSplineResidual action path variation) = 0 :=
    Nat.le_zero.mp hle
  exact hne (intActivityMagnitude_eq_zero hzero)

/-
The standing record, extending the audit.  Expected results inline.
-/

-- The derivative is read by the apparatus: zero for the null Lagrangian,
-- two for the obstructed action -- the same readings as Episode50, now in
-- derivative language, because they were always the same terms.
#eval intActivityMagnitude
  (telescopingAction.firstVariation skeletonPath { slip := node1 })
    -- expect: 0
#eval intActivityMagnitude
  (discriminatingAction.firstVariation skeletonPath { slip := node1 })
    -- expect: 2

-- The final act stays on the constructive side: expect NO
-- `Classical.choice` anywhere below.
#print axioms cubicSplineResidual_eq_firstVariation
#print axioms frechetDerivative_exists
#print axioms frechetDerivative_unique
#print axioms frechetDerivative_existsUnique
#print axioms FiniteGaugeAction.linearization_unique
#print axioms cubic_left_slot_unique
#print axioms cubic_right_slot_unique
#print axioms taylor_terminates_at_order_two
#print axioms telescoping_derivative_zero
#print axioms discriminating_derivative_nonzero
#print axioms frechet_crosses_the_finish_line
#print axioms flat_actions_cross_too
#print axioms nonzero_residual_fails_eventual_exactness

end Measurement
