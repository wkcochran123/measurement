import Measurement.Episode49

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000
set_option allowUnsafeReducibility true

namespace Measurement

/-
__EPISODE 50__: _The Certificate Is Produced, Not Assumed_

The last bug from the review, and the deepest one.  Episode45's discharge
theorem consumes a `CompletedResidualWeierstrassTower`, and that structure
still CARRIES the analytic certificate: its squeeze's `bound_tends_zero`
field is assumed data, and Episode27's
`terminalResidualMagnitude_tends_zero` already derives the conclusion from it
with no exhaustion at all.  A theorem that consumes `completed` discharges
nothing; the certificate just sits in the hypothesis wearing a different hat.
The honest move is a CONSTRUCTOR: build the instance, and prove
`bound_tends_zero` from the combinatorics instead of assuming it.

This episode builds it.  Action: `telescopingAction` (Episode48 -- the
discriminating action refuses, and that refusal is now a theorem).  Tower:
`skeletonTower` (Episode49).  Each stage's trace consumes its whole knot list
by identity Lanczos steps -- the in-stage half of the counting argument,
finite descent down `Consumes` -- and its terminal residual IS the cubic
residual, which the null-Lagrangian theorem makes identically zero.  So the
squeeze's bound is PROVEN to tend to zero: `bound := residual`, and the
residual is exactly zero at every stage.  Eventual exactness of the strongest
kind, produced from structure, with nothing assumed anywhere in the instance.

Stated formally:
* `consumeAll` -- the generic in-stage iterator: any finite knot list is
  consumed completely, one identity step per entry.
* `skeletonCompleted` -- the concrete `CompletedResidualWeierstrassTower`
  over `natScale`, every certificate field constructed.
* `skeleton_unconditional_tendsToZero` -- the conclusion for EVERY variation,
  through Episode27's own flagship theorem, now with honest inputs.
* `skeleton_discharge_via_exhaustion` -- Episode45's theorem applied with
  `hexhaust` supplied by `skeletonTower_exhausts`: the per-slip pigeonhole
  route, N computed as `slipDepth variation.slip`.

The `#eval`/`#print axioms` record below extends Episode46's audit to the
new chain: every theorem below is expected choice-free.  And one more bug for
the record, found by RUNNING the audit instead of reading it: Episode46's
standing expectation that `rung3Inferred` lists `Classical.choice` is stale
-- the build reports `[propext, Quot.sound]`.  The boundary is a build
artifact, and artifacts get rebuilt.

Residue left (honest scope):
the covering framework only ever instantiates where the residual already
vanishes on the covered slips -- the forced-balance collapse the review
identified is real.  `telescopingAction` rides it because it is FLAT by
structure (`telescoping_flatAt`) with an identically zero residual, while
admitting NO path at all (`telescoping_not_admits`); Episode27's trace
dropped Episode21's `admits` field, and that dropped field is the door.  An
action with genuinely nonzero residual cannot ride this construction; for
it, eventual exactness is false, not unproven.  The discrete gauge equation
keeps its content.
-/

/-- The concrete path for the produced certificate: all nodes at the origin. -/
def skeletonPath : FiniteGaugePath where
  source := node0
  slip := node0
  target := node0

/-- The generic in-stage iterator: consume an entire knot list with identity
Lanczos steps, one entry at a time.  Finite descent down `Consumes` -- the
in-stage half of the counting argument, now a constructor instead of a
certificate. -/
def consumeAll (residual : FiniteGaugeVariation -> Int) :
    (entries : List Bullshit) ->
      LanczosIterates ⟨entries⟩
        (LanczosState.fromResidual residual)
        (LanczosState.fromResidual residual)
  | [] => LanczosIterates.done _
  | slip :: rest =>
      LanczosIterates.step
        (SlipMultiset.Consumes.head slip rest)
        (LanczosStep.identity residual slip)
        (consumeAll residual rest)

/-- Stage `n` of the produced residual tower: knots are the depth-`n` slice,
the terminal state is the cubic residual itself, and the whole knot list is
consumed. -/
def skeletonStageTrace (n : Nat) :
    ApproximateLanczosTrace telescopingAction skeletonPath where
  knots := ⟨ratSlips n⟩
  initial :=
    LanczosState.fromResidual
      (cubicSplineResidual telescopingAction skeletonPath)
  terminal :=
    LanczosState.fromResidual
      (cubicSplineResidual telescopingAction skeletonPath)
  iterates :=
    consumeAll (cubicSplineResidual telescopingAction skeletonPath) (ratSlips n)
  terminal_matches_cubic := fun _ => rfl
  terminal_solved_on := fun variation _ =>
    telescoping_residual_zero skeletonPath variation

theorem skeletonStageTrace_terminalResidual
    (n : Nat) (variation : FiniteGaugeVariation) :
    (skeletonStageTrace n).terminalResidual variation = 0 :=
  telescoping_residual_zero skeletonPath variation

/-- The magnitude is Episode28's activity magnitude: the apparatus reading. -/
def skeletonMagnitude : IntResidualMagnitude natScale where
  ofInt := intActivityMagnitude

/-- The produced squeeze: `bound := residual`, and `bound_tends_zero` is a
THEOREM, routed through Episode45's own order-theoretic core
(`eventuallyZero_tendsToZero`) -- the null Lagrangian makes every stage's
reading exactly zero.  Nothing here is assumed. -/
def skeletonSqueeze :
    PointwiseSqueezedResidual natScale FiniteGaugeVariation where
  residual := fun n variation =>
    intActivityMagnitude ((skeletonStageTrace n).terminalResidual variation)
  bound := fun n variation =>
    intActivityMagnitude ((skeletonStageTrace n).terminalResidual variation)
  zero_le_residual := fun _ _ => Nat.zero_le _
  residual_le_bound := fun _ _ => Nat.le_refl _
  bound_tends_zero := fun variation =>
    eventuallyZero_tendsToZero natScale natScale_zero_le _
      ⟨0, fun n _ => by
        show
          intActivityMagnitude
            ((skeletonStageTrace n).terminalResidual variation) = 0
        rw [skeletonStageTrace_terminalResidual n variation,
          intActivityMagnitude_zero]⟩

/-- The produced residual tower over `natScale`. -/
def skeletonResidualTower :
    ResidualTowerRealizesLanczos natScale telescopingAction skeletonPath where
  stageTrace := skeletonStageTrace
  magnitude := skeletonMagnitude
  squeeze := skeletonSqueeze
  residual_matches_terminal := fun _ _ => rfl

/-- The produced Weierstrass witness: the same squeeze, so the bound the
completion certifies is the bound the tower proves. -/
def skeletonWeierstrassTower :
    WeierstrassFiniteElephantTower truthAdmissibleRange natScale where
  tower := skeletonTower
  work := truthPolynomialWorkSchedule
  witness := { basis := .bspline, squeeze := skeletonSqueeze }

/-- The produced completion: the approximant sits at `node0`, which every
stage contains. -/
def skeletonCompletion :
    CompletedWeierstrassFiniteElephantTower truthAdmissibleRange natScale where
  approximation := skeletonWeierstrassTower
  limit := node0
  approximant := fun _ => node0
  approximant_in_stage := fun n => Or.inr (node0_mem_ratSlips n)
  converges := fun approximant limit => forall n, approximant n = limit
  converges_to_limit := fun _ => rfl

/-- The produced certificate: a concrete `CompletedResidualWeierstrassTower`
in which every field that Episode27 took as assumed data is constructed and
proven.  This is the constructor the review asked for. -/
def skeletonCompleted :
    CompletedResidualWeierstrassTower
      truthAdmissibleRange natScale telescopingAction skeletonPath where
  completion := skeletonCompletion
  residualTower := skeletonResidualTower
  stage_matches_elephant := fun _ => rfl
  residualTower_le_weierstrass_bound := fun _ _ => Nat.le_refl _

/-- The unconditional conclusion, for EVERY variation, through Episode27's
own flagship theorem -- now with honest inputs: the squeeze it consumes was
produced above, not assumed. -/
theorem skeleton_unconditional_tendsToZero
    (variation : FiniteGaugeVariation) :
    natScale.TendsToZero
      (fun n =>
        skeletonCompleted.residualTower.magnitude.ofInt
          ((skeletonCompleted.residualTower.stageTrace n).terminalResidual
            variation)) :=
  skeletonCompleted.terminalResidualMagnitude_tends_zero variation

/-- Episode45's discharge theorem, applied: `hexhaust` is supplied by
`skeletonTower_exhausts`, the per-slip pigeonhole route, with
`N = slipDepth variation.slip` computed from the term.  The hypothesis that
was a residue is now a theorem.  Honest accounting: at THIS (action, path)
the conclusion is subsumed by `skeleton_unconditional_tendsToZero` above,
because the residual is structurally zero -- the exhaustion route is
demonstrated here, not load-bearing. -/
theorem skeleton_discharge_via_exhaustion
    (variation : FiniteGaugeVariation) (h : IsSkeleton variation.slip) :
    natScale.TendsToZero
      (fun n =>
        skeletonCompleted.residualTower.magnitude.ofInt
          ((skeletonCompleted.residualTower.stageTrace n).terminalResidual
            variation)) :=
  tower_terminalResidual_tendsToZero
    skeletonCompleted
    intActivityMagnitude_zero
    variation
    (skeletonTower_exhausts variation h)

/-
The standing record, extending Episode46's audit.  Expected results inline.
-/

-- The enumeration runs and counts: depth reads back, slices are complete
-- (entry counts include multiplicity).
#eval slipDepth (iterOne 5)      -- expect: 5
#eval (ratSlips 0).length        -- expect: 1
#eval (ratSlips 1).length        -- expect: 3
#eval (ratSlips 2).length        -- expect: 15

-- The integrator reads the two actions at a covering representative: the
-- null Lagrangian reads 0, the obstructed action reads 2 -- the same `2`
-- as Episode44's kicked path, now understood as the obstruction.
#eval intActivityMagnitude
  (cubicSplineResidual telescopingAction skeletonPath { slip := node1 })
    -- expect: 0
#eval intActivityMagnitude
  (cubicSplineResidual discriminatingAction skeletonPath { slip := node1 })
    -- expect: 2

-- Extending Episode46's audit: expect NO `Classical.choice` anywhere below.
#print axioms finite_entries_miss_a_slip
#print axioms discriminatingAction_no_covering_trace
#print axioms discriminatingAction_no_tag_covering_trace
#print axioms tag_covering_residual
#print axioms skeletonTower_exhausts
#print axioms skeleton_unconditional_tendsToZero
#print axioms skeleton_discharge_via_exhaustion

end Measurement
