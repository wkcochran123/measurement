import Measurement.Episode57

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000
set_option allowUnsafeReducibility true

namespace Measurement

/-
__EPISODE 58__: _The Flat Tower, Filed_

Episode51's honest-scope ledger left exactly one construction unfiled: the
produced tower for an arbitrary flat pair.  Episode50 built it for the
showcase pair only, and the closer said the generalization was "mechanical,
but mechanical is not filed."  Filed.

The construction is Episode50's with `telescopingAction` abstracted: for
ANY (action, path) with `action.flatAt path`, flatness makes the Frechet
derivative vanish (Episode18's `fromAction_stationaryAt_of_flatAt`, worn
here as `flat_residual_zero` through Episode51's reveal that the spline
residual IS the Frechet derivative), so every stage trace over the
skeleton slices carries an identically zero residual, the squeeze's bound
is PROVEN zero, and the completed tower exists with nothing assumed.

The naming discipline the paper lane requires (and Episode50 honored in
prose) is now in the names: a `FlatResidualTower` is a produced tower over
a flat pair -- telescoping/exhaustion machinery, with NO claim that the
action admits any path.  (The abbrev is naming discipline, enforced by the
constructor's `hflat` hypothesis rather than by the type itself.)  An `AdmittedC2Certificate` is Episode52's
`IsC2Certified`, whose first clause IS admissibility.  Flat towers and
admitted certificates are different channels; sliding from one to the
other is the cheat both Episode50 and the paper refuse.

Stated formally:
* `flat_residual_zero` -- flatness kills the residual at every variation.
* `FlatResidualTower` -- the named tower type: produced, flat, no admits
  claim.
* `flatStageTrace`, `flatSqueeze`, `flatPairCompleted` -- Episode50's
  construction over an arbitrary flat pair.
* `flatPair_unconditional_tendsToZero` -- the convergence, for every flat
  pair and every variation.
* `flatPairCompleted_exists` -- the existence form, Episode51's open door
  closed.
* `AdmittedC2Certificate` -- the certificate channel's honest name.

Residue left (honest scope):
the tower's stages still enumerate the rational skeleton; a flat pair
whose nodes live outside universe zero would need its own enumeration
(the construction pins to `Bullshit0` through `ratSlips`).  The completed
tower borrows `skeletonCompletion`'s Weierstrass witness -- sound, since
both sides of the domination are zero, but the flat pair's bound is
another action's; building the witness from `flatSqueeze` itself is the
tidier next pass.  And the two names are now load-bearing: nothing in
this episode lets a flat tower testify as an admitted law.
-/

/-- Flatness kills the residual at every variation: the cubic spline
residual IS the Frechet derivative (Episode51), and a flat pair's
derivative vanishes (Episode18). -/
theorem flat_residual_zero
    (action : FiniteGaugeAction) (path : FiniteGaugePath)
    (hflat : action.flatAt path) (variation : FiniteGaugeVariation) :
    cubicSplineResidual action path variation = 0 :=
  FrechetGauge.fromAction_stationaryAt_of_flatAt hflat variation

/-- The flat tower's honest name: a produced residual tower over a flat
pair.  Telescoping/exhaustion machinery; NO claim that the action admits
any path. -/
abbrev FlatResidualTower
    (action : FiniteGaugeAction) (path : FiniteGaugePath) :=
  CompletedResidualWeierstrassTower truthAdmissibleRange natScale action path

/-- The certificate channel's honest name: Episode52's C-squared
certificate, whose first clause is admissibility.  A flat tower is not
one of these. -/
abbrev AdmittedC2Certificate
    (action : FiniteGaugeAction) (path : CubicGaugePath) : Prop :=
  IsC2Certified action path

/-- Stage `n` of the flat tower: Episode50's stage trace with the action
abstracted.  The knot list is consumed completely; the terminal residual
is the (identically zero) cubic residual. -/
def flatStageTrace
    (action : FiniteGaugeAction) (path : FiniteGaugePath)
    (hflat : action.flatAt path) (n : Nat) :
    ApproximateLanczosTrace action path where
  knots := ⟨ratSlips n⟩
  initial := LanczosState.fromResidual (cubicSplineResidual action path)
  terminal := LanczosState.fromResidual (cubicSplineResidual action path)
  iterates := consumeAll (cubicSplineResidual action path) (ratSlips n)
  terminal_matches_cubic := fun _ => rfl
  terminal_solved_on := fun variation _ =>
    flat_residual_zero action path hflat variation

theorem flatStageTrace_terminalResidual
    (action : FiniteGaugeAction) (path : FiniteGaugePath)
    (hflat : action.flatAt path) (n : Nat)
    (variation : FiniteGaugeVariation) :
    (flatStageTrace action path hflat n).terminalResidual variation = 0 :=
  flat_residual_zero action path hflat variation

/-- The produced squeeze over a flat pair: `bound := residual`, both
identically zero, `bound_tends_zero` routed through Episode45's core. -/
def flatSqueeze
    (action : FiniteGaugeAction) (path : FiniteGaugePath)
    (hflat : action.flatAt path) :
    PointwiseSqueezedResidual natScale FiniteGaugeVariation where
  residual := fun n variation =>
    intActivityMagnitude
      ((flatStageTrace action path hflat n).terminalResidual variation)
  bound := fun n variation =>
    intActivityMagnitude
      ((flatStageTrace action path hflat n).terminalResidual variation)
  zero_le_residual := fun _ _ => Nat.zero_le _
  residual_le_bound := fun _ _ => Nat.le_refl _
  bound_tends_zero := fun variation =>
    eventuallyZero_tendsToZero natScale natScale_zero_le _
      ⟨0, fun n _ => by
        show
          intActivityMagnitude
            ((flatStageTrace action path hflat n).terminalResidual
              variation) = 0
        rw [flatStageTrace_terminalResidual action path hflat n variation,
          intActivityMagnitude_zero]⟩

/-- The produced tower for an arbitrary flat pair: Episode51's open door,
closed.  Every certificate field constructed; the stages are the skeleton
tower's. -/
def flatPairCompleted
    (action : FiniteGaugeAction) (path : FiniteGaugePath)
    (hflat : action.flatAt path) :
    FlatResidualTower action path where
  completion := skeletonCompletion
  residualTower :=
    { stageTrace := flatStageTrace action path hflat
      magnitude := skeletonMagnitude
      squeeze := flatSqueeze action path hflat
      residual_matches_terminal := fun _ _ => rfl }
  stage_matches_elephant := fun _ => rfl
  residualTower_le_weierstrass_bound := fun n variation => by
    show
      natScale.le
        (intActivityMagnitude
          ((flatStageTrace action path hflat n).terminalResidual variation))
        (skeletonSqueeze.bound n variation)
    rw [flatStageTrace_terminalResidual action path hflat n variation,
      intActivityMagnitude_zero]
    exact Nat.zero_le _

/-- The convergence, for every flat pair and every variation: produced,
not assumed. -/
theorem flatPair_unconditional_tendsToZero
    (action : FiniteGaugeAction) (path : FiniteGaugePath)
    (hflat : action.flatAt path) (variation : FiniteGaugeVariation) :
    natScale.TendsToZero
      (fun n =>
        (flatPairCompleted action path hflat).residualTower.magnitude.ofInt
          (((flatPairCompleted action path hflat).residualTower.stageTrace
              n).terminalResidual variation)) :=
  (flatPairCompleted action path hflat).terminalResidualMagnitude_tends_zero
    variation

/-- The existence form, as the paper lane's acceptance theorem states it:
for every flat pair there is a completed tower whose terminal residual
magnitude tends to zero at every variation. -/
theorem flatPairCompleted_exists
    (action : FiniteGaugeAction0) (path : FiniteGaugePath)
    (hflat : action.flatAt path) :
    exists completed :
      CompletedResidualWeierstrassTower.{0, 0, 0, 0, 0, 0, 0, 0}
        truthAdmissibleRange natScale action path,
      forall variation,
        natScale.TendsToZero
          (fun n =>
            completed.residualTower.magnitude.ofInt
              ((completed.residualTower.stageTrace n).terminalResidual
                variation)) :=
  ⟨flatPairCompleted action path hflat,
    flatPair_unconditional_tendsToZero action path hflat⟩

/-
The standing record.
-/

-- Episode51's ledger entry is closed: expect `[propext, Quot.sound]`,
-- choice-free -- the flat tower is on the production line, not in the
-- chair.
#print axioms flat_residual_zero
#print axioms flatPairCompleted_exists
#print axioms flatPair_unconditional_tendsToZero

end Measurement
