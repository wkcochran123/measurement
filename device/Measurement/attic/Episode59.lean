import Measurement.Episode58

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000
set_option allowUnsafeReducibility true

namespace Measurement

/-
__EPISODE 59__: _Cauchy Convergence of QED as the ε of GR Goes to Zero_

Episode1 built a `CauchyProcess` fifty-eight episodes before anything could
run it, and said why: "We now have the pieces of a residue, an origin and a
limit away from that origin."  This is the episode that runs it.  Finally.

The two programs are split by type (Episode56) and coupled through exactly
one thing: the bound.  `CompletedResidualWeierstrassTower` carries the
coupling as a field -- `residualTower_le_weierstrass_bound` pins the
QED-side residual reading UNDER the geometric completion's Weierstrass
bound -- and since Episode50 that bound is produced, not assumed.  The
geometric bound is the ε of GR: the tolerance the geometric refinement
grants the gauge reading at each stage.  And it tends to zero.

So the QED reading has no choice.  `completed_residual_isCauchy` is the
general theorem: for ANY completed tower over the `natScale`, the residual
sequence is Cauchy -- for every tolerance there is a stage past which any
two readings differ by less -- because both readings sit under a GR ε that
has already gone to zero.  The proof is the squeeze run twice: two stages,
two bounds, one `natAbsDiff`, `omega`.  Convergence comes with it: the
limit is the on-shell zero (Episode50's unconditional theorem), so the
package `qed_cauchy_convergence_as_gr_epsilon_vanishes` states all three
clauses at the generated program's tower -- the GR ε tends to zero, the
QED readings are Cauchy, and they converge to the on-shell reading.
`flatPair_qed_isCauchy` says the same for every flat pair through
Episode58's tower.

What this is, honestly: the discrete completion of the corpus's oldest
promise.  The residue was an origin and a limit; the origin is the
on-shell zero, the limit exists because the readings are eventually
exactly there (Episode45's eventual exactness is the strongest Cauchy
behavior a sequence can have), and the distance that shrinks is GR's to
spend.  QED converges because geometry's tolerance does.

Stated formally:
* `IsCauchyNat` -- Cauchy over the natScale, distances by `natAbsDiff`
  (Episode33's middle-reading metric, now doing analysis).
* `completed_residual_isCauchy` -- the general theorem: every completed
  tower's QED residual sequence is Cauchy under the vanishing GR ε.
* `qed_cauchy_convergence_as_gr_epsilon_vanishes` -- the finale package at
  the generated program's tower: ε of GR to zero, QED Cauchy, QED
  convergent to on-shell zero.
* `flatPair_qed_isCauchy` -- the same for every flat pair (Episode58).

Residue left (honest scope):
ε here is the `natScale` tolerance carried by the PRODUCED geometric
Weierstrass bound -- finite and order-theoretic, not a continuum metric;
Cauchy COMPLETENESS (the limit existing in a completed space) is
Episode38's door and stays a door.  Episode1's `CauchyProcess` and the
RESIDUE gate keep their Limit-typed fields; this episode is their finite
shadow running, not their analytic discharge.  And the convergence is
eventual exactness -- the strongest form, and also the cheapest joke: the
sequence converges because it stopped moving.
-/

/-- Cauchy over the natScale: for every tolerance there is a stage past
which any two readings differ by at most it.  Distances by Episode33's
`natAbsDiff`. -/
def IsCauchyNat (seq : Nat -> Nat) : Prop :=
  forall epsilon, natScale.tolerance epsilon ->
    exists N, forall m n, N <= m -> N <= n ->
      natAbsDiff (seq m) (seq n) <= epsilon

/-- THE GENERAL THEOREM: for any completed tower over the natScale, the
QED-side residual sequence is Cauchy, because every reading sits under the
geometric completion's Weierstrass bound -- the ε of GR -- and that bound
tends to zero.  The squeeze, run twice. -/
theorem completed_residual_isCauchy
    {range : AdmissibleRange}
    {action : FiniteGaugeAction} {path : FiniteGaugePath}
    (completed : CompletedResidualWeierstrassTower range natScale action path)
    (variation : FiniteGaugeVariation) :
    IsCauchyNat
      (fun n => completed.residualTower.squeeze.residual n variation) := by
  intro epsilon htol
  obtain ⟨N, hN⟩ :=
    completed.completion.approximation.witness.squeeze.bound_tends_zero
      variation epsilon htol
  refine ⟨N, fun m n hm hn => ?_⟩
  have h1 :
      Nat.le
        (completed.residualTower.squeeze.residual m variation)
        (completed.completion.approximation.witness.squeeze.bound
          m variation) :=
    completed.residualTower_le_weierstrass_bound m variation
  have h2 :
      Nat.le
        (completed.residualTower.squeeze.residual n variation)
        (completed.completion.approximation.witness.squeeze.bound
          n variation) :=
    completed.residualTower_le_weierstrass_bound n variation
  have h3 :
      Nat.le
        (completed.completion.approximation.witness.squeeze.bound
          m variation)
        epsilon :=
    hN m hm
  have h4 :
      Nat.le
        (completed.completion.approximation.witness.squeeze.bound
          n variation)
        epsilon :=
    hN n hn
  show
    natAbsDiff
      (completed.residualTower.squeeze.residual m variation)
      (completed.residualTower.squeeze.residual n variation) <= epsilon
  unfold natAbsDiff
  split
  · exact Nat.le_trans (Nat.sub_le _ _) (Nat.le_trans h2 h4)
  · exact Nat.le_trans (Nat.sub_le _ _) (Nat.le_trans h1 h3)

/-- THE FINALE: at the generated program's produced tower, the ε of GR
tends to zero, the QED readings are Cauchy, and they converge to the
on-shell zero.  Cauchy convergence of QED as the ε of GR goes to zero. -/
theorem qed_cauchy_convergence_as_gr_epsilon_vanishes
    (variation : FiniteGaugeVariation) :
    natScale.TendsToZero
        (fun n =>
          skeletonCompleted.completion.approximation.witness.squeeze.bound
            n variation) ∧
      IsCauchyNat
          (fun n =>
            skeletonCompleted.residualTower.squeeze.residual n variation) ∧
        natScale.TendsToZero
          (fun n =>
            skeletonCompleted.residualTower.magnitude.ofInt
              ((skeletonCompleted.residualTower.stageTrace n).terminalResidual
                variation)) :=
  ⟨skeletonCompleted.completion.approximation.witness.squeeze.bound_tends_zero
      variation,
    completed_residual_isCauchy skeletonCompleted variation,
    skeleton_unconditional_tendsToZero variation⟩

/-- And for every flat pair, through Episode58's tower: the flat QED
readings are Cauchy under the same vanishing ε. -/
theorem flatPair_qed_isCauchy
    (action : FiniteGaugeAction) (path : FiniteGaugePath)
    (hflat : action.flatAt path) (variation : FiniteGaugeVariation) :
    IsCauchyNat
      (fun n =>
        (flatPairCompleted action path hflat).residualTower.squeeze.residual
          n variation) :=
  completed_residual_isCauchy (flatPairCompleted action path hflat) variation

/-
The standing record.
-/

-- Expect NO axioms at all on the general theorem -- the Cauchy argument
-- is pure construction, the cleanest record in the corpus -- and
-- `[propext, Quot.sound]` on the finale package and the flat instance.
-- No chair anywhere: GR's ε reaches QED through the produced bound, and
-- the production line carries it the whole way.
#print axioms completed_residual_isCauchy
#print axioms qed_cauchy_convergence_as_gr_epsilon_vanishes
#print axioms flatPair_qed_isCauchy

end Measurement
