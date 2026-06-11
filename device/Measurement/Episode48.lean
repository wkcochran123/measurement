import Measurement.Episode47

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000
set_option allowUnsafeReducibility true

namespace Measurement

/-
__EPISODE 48__: _Three Holes Are Enough, and One Action Refuses_

Episode47 proved the negative pigeonhole: infinitely many slip-pigeons, one
finite list of holes, so literal support can never be uniform.  This episode
proves the positive pigeonhole, and it lands on the other side of the same
counting: the residual does not see the slip -- it sees the slip only through
two segment costs.  When the cost factors through `tag` (Episode44), the
infinite pigeon family maps into THREE holes, and three representatives carry
every variation.  Countably many pigeons, three holes, congruence transfers
the zero from the hole to every pigeon inside it.

Stated formally:
* `cubicSplineResidual_congr` -- the kernel lemma: cost-indistinguishable
  slips have equal residuals.  The slip enters the Euler-Lagrange residual at
  exactly two cost positions; nothing else of it survives.
* `FiniteGaugeAction.FactorsThroughTag` and `cubicSplineResidual_tag_congr`
  -- the three-hole quotient for tag-factoring actions.
* `tag_covering_residual` -- the payoff: solve the residual on `node0`,
  `node1`, `node2` and you have solved it on EVERY variation.  The uniform N
  that Episode47 proved impossible literally is recovered up to congruence.

And the bug report, filed as a theorem.  The review found that Episode44's
`discriminatingAction` -- the only nontrivial action in the corpus -- can
never inhabit a covering trace: with `a = tag source` and `c = tag target`,
the map `x ↦ [a≠x] + [x≠c]` over the three tags takes values `{0,2}` or
`{1,1,2}`, never constant, so the residual cannot vanish on all three
representatives at once.  `kickedGaugeReading = 2` was the standing witness
all along.  `discriminatingAction_obstructed` states it for every path, with
a `decide` over `Fin 3` as the entire arithmetic content;
`discriminatingAction_no_covering_trace` is the corollary that no
`ApproximateLanczosTrace` over it can carry tag-covering knots.

The repair is `telescopingAction`: cost `tag x + (2 - tag y)`.  The two
segment costs telescope -- `cost(s,t) + cost(t,g)` is constant in `t` -- so
the Euler-Lagrange residual vanishes identically, for every path and every
variation: a discrete null Lagrangian.  Nontrivial cost, structurally zero
residual, and the whole thing computes.

Residue left (honest scope):
the covering representatives exist and transfer, but no concrete exhausting
tower has been built yet.  That is Episode49.
-/

/-- The kernel lemma: the cubic/Frechet residual sees the slip only through
`segmentCost source ·` and `segmentCost · target`.  Slips the cost cannot
distinguish have equal residuals. -/
theorem cubicSplineResidual_congr
    (action : FiniteGaugeAction) (path : FiniteGaugePath) {s t : Bullshit}
    (hleft :
      action.segmentCost path.source s = action.segmentCost path.source t)
    (hright :
      action.segmentCost s path.target = action.segmentCost t path.target) :
    cubicSplineResidual action path { slip := s } =
      cubicSplineResidual action path { slip := t } := by
  simp only [cubicSplineResidual, DiscreteGaugeDerivative.eulerLagrangeResidual,
    DiscreteGaugeDerivative.fromAction, FiniteGaugeAction.leftVariation,
    FiniteGaugeAction.rightVariation]
  rw [hleft, hright]

/-- An action factors through the tag quotient when tag-equal slips are
cost-indistinguishable on both sides. -/
def FiniteGaugeAction.FactorsThroughTag (action : FiniteGaugeAction0) : Prop :=
  forall s t : Bullshit0, tag s = tag t ->
    (forall x : Bullshit0, action.segmentCost x s = action.segmentCost x t) /\
      (forall x : Bullshit0, action.segmentCost s x = action.segmentCost t x)

/-- The three-hole congruence: for a tag-factoring action, tag-equal slips
have equal residuals. -/
theorem cubicSplineResidual_tag_congr
    {action : FiniteGaugeAction0} (hfac : action.FactorsThroughTag)
    (path : FiniteGaugePath) {s t : Bullshit0} (htag : tag s = tag t) :
    cubicSplineResidual action path { slip := s } =
      cubicSplineResidual action path { slip := t } :=
  cubicSplineResidual_congr action path
    ((hfac s t htag).left path.source)
    ((hfac s t htag).right path.target)

theorem tag_lt_three : forall s : Bullshit0, tag s < 3 := by
  intro s
  cases s <;> (simp only [tag]; omega)

/-- The third representative: the skeleton `.rest` over the fixed atoms. -/
def node2 : Bullshit0 :=
  .rest Fact.Truth Fact.Truth True
    (Number.zero Fact.Truth) (Number.zero Fact.Truth) (Number.zero Fact.Truth)
    (CompilerTape.boot Fact.Truth (Unit : Type))
    (CompilerTape.boot Fact.Truth (Unit : Type))
    node0 node0

/-- One representative per hole. -/
def tagRep (x : Fin 3) : Bullshit0 :=
  if x.val = 0 then node0 else if x.val = 1 then node1 else node2

theorem tag_tagRep : forall x : Fin 3, tag (tagRep x) = x.val := by decide

theorem tagRep_mem (x : Fin 3) : tagRep x ∈ [node0, node1, node2] := by
  rcases x with ⟨n, hn⟩
  rcases n with _ | _ | _ | m
  · exact List.Mem.head _
  · exact List.Mem.tail _ (List.Mem.head _)
  · exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
  · exact absurd hn (by omega)

/-- The positive pigeonhole, as a transfer theorem: countably many slips fall
into three tag holes, the residual is constant on each hole, so solving the
three representatives solves every variation.  This is the uniform N that
literal membership (Episode47) can never provide. -/
theorem tag_covering_residual
    {action : FiniteGaugeAction0} (hfac : action.FactorsThroughTag)
    (path : FiniteGaugePath)
    (hsolved :
      forall rep : Bullshit0, rep ∈ [node0, node1, node2] ->
        cubicSplineResidual action path { slip := rep } = 0) :
    forall variation : FiniteGaugeVariation,
      cubicSplineResidual action path variation = 0 := by
  intro variation
  have hv : variation = { slip := variation.slip } := rfl
  have hcongr :
      cubicSplineResidual action path { slip := variation.slip } =
        cubicSplineResidual action path
          { slip := tagRep ⟨tag variation.slip, tag_lt_three variation.slip⟩ } :=
    cubicSplineResidual_tag_congr hfac path
      (tag_tagRep ⟨tag variation.slip, tag_lt_three variation.slip⟩).symm
  rw [hv, hcongr]
  exact hsolved _ (tagRep_mem _)

/-
The bug report.  `discriminatingAction` refuses the covering: the arithmetic
core is one `decide` over `Fin 3`.
-/

theorem discriminating_core :
    forall a b c : Fin 3, exists x : Fin 3,
      (Int.ofNat (if a.val = x.val then 0 else 1) -
          Int.ofNat (if a.val = b.val then 0 else 1)) +
        (Int.ofNat (if x.val = c.val then 0 else 1) -
          Int.ofNat (if b.val = c.val then 0 else 1)) ≠ 0 := by
  decide

/-- For EVERY path, some tag representative has nonzero residual under
`discriminatingAction`.  The obstruction is total: it does not depend on the
path's configuration. -/
theorem discriminatingAction_obstructed (path : FiniteGaugePath) :
    exists s : Bullshit0, s ∈ [node0, node1, node2] /\
      cubicSplineResidual discriminatingAction path { slip := s } ≠ 0 := by
  obtain ⟨x, hx⟩ :=
    discriminating_core
      ⟨tag path.source, tag_lt_three path.source⟩
      ⟨tag path.slip, tag_lt_three path.slip⟩
      ⟨tag path.target, tag_lt_three path.target⟩
  refine ⟨tagRep x, tagRep_mem x, ?_⟩
  have hformula :
      cubicSplineResidual discriminatingAction path { slip := tagRep x } =
        (Int.ofNat (if tag path.source = tag (tagRep x) then 0 else 1) -
            Int.ofNat (if tag path.source = tag path.slip then 0 else 1)) +
          (Int.ofNat (if tag (tagRep x) = tag path.target then 0 else 1) -
            Int.ofNat (if tag path.slip = tag path.target then 0 else 1)) := rfl
  rw [hformula, tag_tagRep x]
  exact hx

/-- No `ApproximateLanczosTrace` over `discriminatingAction` carries
tag-covering knots: `terminal_matches_cubic` plus `terminal_solved_on` would
force the residual to vanish on all three representatives, which
`discriminatingAction_obstructed` forbids.  The honest ceiling on Episode45's
header promise, filed as a theorem. -/
theorem discriminatingAction_no_covering_trace
    (path : FiniteGaugePath)
    (trace : ApproximateLanczosTrace discriminatingAction path) :
    ¬ forall rep : Bullshit0, rep ∈ [node0, node1, node2] ->
        rep ∈ trace.knots.entries := by
  intro hcov
  obtain ⟨s, hmem, hne⟩ := discriminatingAction_obstructed path
  exact hne
    ((trace.terminal_matches_cubic { slip := s }).symm.trans
      (trace.terminal_solved_on { slip := s } (hcov s hmem)))

/-
The repair: a tag-factoring action whose residual is structurally zero.
-/

/-- The telescoping action: `cost x y = tag x + (2 - tag y)`.  The two
segment costs around any middle node telescope, so the residual is a discrete
null Lagrangian -- identically zero, for every path and every variation. -/
def telescopingAction : FiniteGaugeAction0 :=
  { segmentCost := fun x y => tag x + (2 - tag y) }

theorem telescoping_factorsThroughTag :
    telescopingAction.FactorsThroughTag := by
  intro s t htag
  refine ⟨fun x => ?_, fun x => ?_⟩
  · show tag x + (2 - tag s) = tag x + (2 - tag t)
    rw [htag]
  · show tag s + (2 - tag x) = tag t + (2 - tag x)
    rw [htag]

/-- The discrete null Lagrangian: the telescoping residual vanishes for every
path and every variation, structurally. -/
theorem telescoping_residual_zero
    (path : FiniteGaugePath) (variation : FiniteGaugeVariation) :
    cubicSplineResidual telescopingAction path variation = 0 := by
  have hv := tag_lt_three variation.slip
  have hp := tag_lt_three path.slip
  show
    (Int.ofNat (tag path.source + (2 - tag variation.slip)) -
        Int.ofNat (tag path.source + (2 - tag path.slip))) +
      (Int.ofNat (tag variation.slip + (2 - tag path.target)) -
        Int.ofNat (tag path.slip + (2 - tag path.target))) = 0
  simp only [Int.ofNat_eq_natCast, Int.natCast_add]
  omega

end Measurement
