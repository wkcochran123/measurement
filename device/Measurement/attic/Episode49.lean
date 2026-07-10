import Measurement.Episode48

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000
set_option allowUnsafeReducibility true

namespace Measurement

/-
__EPISODE 49__: _The Rational Skeleton, Enumerated by Depth_

Episode45's header said "the rational enumeration" and waved at all of
`Bullshit`.  The review caught the bug: `.rest` carries a raw `Prop` and the
tapes carry `Type`-level data, so the full type has no enumeration -- not
constructively, not classically.  Any Nat-indexed tower of finite lists holds
countably many slips, full stop.  What CAN be enumerated is the rational
skeleton: the closure of `node0` under the skeleton constructors over the
fixed atoms.  That subfamily is the honest content of the promise, and this
episode delivers it.

The review also caught a second bug, in the obvious grading.  Grading slices
by size-sum makes `rest zero zero` (size 3) land in the alleged size-2 slice
and the counting lemma is false as stated.  The repair is DEPTH -- `max` of
children plus one -- under which the slices are complete: every skeleton term
of depth `d` appears by stage `d`, by structural induction, with no counting
debt on the membership side.  (The stage lists count with multiplicity --
stage 2 holds 15 entries, 13 distinct -- which is harmless: `hexhaust` asks
for membership, not measure.)

The tower is cumulative: stage `n+1` is stage `n` plus one `skeletonOne`
image and one `skeletonRest` product.  Cumulativity matters more than it
looks: `contains_refines` as recorded in Episode27 preserves only the
disjunction `body ∨ entries`, which is too weak to persist entries-membership
-- exactly what `hexhaust` demands.  The concrete tower carries genuine
entries-monotonicity (`ratSlips_mono`), the stronger thing, for free.

Stated formally:
* `ratSlips_complete` -- every skeleton slip appears at stage `slipDepth s`:
  the positive enumeration, with N computable from the term.
* `ratSlips_mono` -- once in, never out.
* `skeletonTower` -- the concrete `FiniteElephantTower`.
* `skeletonTower_exhausts` -- Episode45's `hexhaust`, now a THEOREM for every
  skeleton variation, with `N := slipDepth variation.slip`.
* `skeletonTower_no_single_stage` -- and per Episode47, still no single stage
  does it uniformly; the quantifier order survives the construction.
* `skeletonStage_covers_tagReps`, `discriminatingAction_no_skeleton_knots`
  -- stage 1 already covers all three tag holes, so Episode48's refusal
  applies from the first refinement onward: no trace over the discriminating
  action can take any skeleton stage past the zeroth as its knots.  The
  bridge is a theorem, not a header sentence.

Residue left (honest scope):
the tower is enumeration; it is not yet wired into a completed residual
tower.  Episode50 produces that certificate instead of assuming it.
-/

/-- The skeleton `.rest` constructor over the fixed atoms.  Applying it to
`node0` twice reproduces Episode48's `node2` exactly. -/
def skeletonRest (b1 b2 : Bullshit0) : Bullshit0 :=
  .rest Fact.Truth Fact.Truth True
    (Number.zero Fact.Truth) (Number.zero Fact.Truth) (Number.zero Fact.Truth)
    (CompilerTape.boot Fact.Truth (Unit : Type))
    (CompilerTape.boot Fact.Truth (Unit : Type))
    b1 b2

theorem skeletonRest_node0_eq_node2 : skeletonRest node0 node0 = node2 := rfl

/-- The rational skeleton: the closure of `node0` under the skeleton
constructors.  This is the countable family the enumeration honestly covers. -/
inductive IsSkeleton : Bullshit0 -> Prop where
  | base : IsSkeleton node0
  | one {b : Bullshit0} : IsSkeleton b -> IsSkeleton (skeletonOne b)
  | rest {b1 b2 : Bullshit0} :
      IsSkeleton b1 -> IsSkeleton b2 -> IsSkeleton (skeletonRest b1 b2)

/-- The grading that makes the slices exact: depth, not size-sum. -/
def slipDepth : Bullshit0 -> Nat
  | .zero _ => 0
  | .one _ _ _ _ b => slipDepth b + 1
  | .rest _ _ _ _ _ _ _ _ b1 b2 => max (slipDepth b1) (slipDepth b2) + 1

theorem slipDepth_skeletonOne (b : Bullshit0) :
    slipDepth (skeletonOne b) = slipDepth b + 1 := rfl

theorem slipDepth_skeletonRest (b1 b2 : Bullshit0) :
    slipDepth (skeletonRest b1 b2) =
      max (slipDepth b1) (slipDepth b2) + 1 := rfl

/-- All `skeletonRest` combinations of two finite lists. -/
def restPairs : List Bullshit0 -> List Bullshit0 -> List Bullshit0
  | [], _ => []
  | b :: rest, others => others.map (skeletonRest b) ++ restPairs rest others

theorem mem_restPairs {b1 b2 : Bullshit0} {left right : List Bullshit0}
    (h1 : b1 ∈ left) (h2 : b2 ∈ right) :
    skeletonRest b1 b2 ∈ restPairs left right := by
  induction h1 with
  | head rest =>
      exact List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨b2, h2, rfl⟩))
  | tail hd _ ih =>
      exact List.mem_append.mpr (Or.inr ih)

/-- The depth-graded cumulative enumeration of the rational skeleton. -/
def ratSlips : Nat -> List Bullshit0
  | 0 => [node0]
  | n + 1 =>
      ratSlips n ++
        ((ratSlips n).map skeletonOne ++ restPairs (ratSlips n) (ratSlips n))

/-- Once in, never out (single step). -/
theorem ratSlips_mono_succ {s : Bullshit0} {n : Nat}
    (h : s ∈ ratSlips n) : s ∈ ratSlips (n + 1) :=
  List.mem_append.mpr (Or.inl h)

/-- Once in, never out: genuine entries-monotonicity, strictly stronger than
the recorded `contains_refines` disjunction. -/
theorem ratSlips_mono {s : Bullshit0} {m n : Nat}
    (hmn : m <= n) (h : s ∈ ratSlips m) : s ∈ ratSlips n := by
  induction n with
  | zero =>
      have hm : m = 0 := by omega
      subst hm
      exact h
  | succ n ih =>
      by_cases hm : m = n + 1
      · subst hm
        exact h
      · have hle : m <= n := by omega
        exact ratSlips_mono_succ (ih hle)

theorem node0_mem_ratSlips : forall n, node0 ∈ ratSlips n
  | 0 => List.Mem.head _
  | n + 1 => ratSlips_mono_succ (node0_mem_ratSlips n)

/-- The enumeration is complete on the skeleton, and the stage is computable
from the term: every skeleton slip appears at stage `slipDepth s`. -/
theorem ratSlips_complete {s : Bullshit0} (h : IsSkeleton s) :
    s ∈ ratSlips (slipDepth s) := by
  induction h with
  | base =>
      exact List.Mem.head _
  | one hb ih =>
      rw [slipDepth_skeletonOne]
      exact List.mem_append.mpr
        (Or.inr (List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨_, ih, rfl⟩))))
  | rest hb1 hb2 ih1 ih2 =>
      rw [slipDepth_skeletonRest]
      refine List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr ?_)))
      exact mem_restPairs
        (ratSlips_mono (Nat.le_max_left _ _) ih1)
        (ratSlips_mono (Nat.le_max_right _ _) ih2)

/-- Stage 1 already holds the second tag representative. -/
theorem node1_mem_ratSlips_one : node1 ∈ ratSlips 1 := by
  rw [← skeletonOne_node0_eq_node1]
  exact List.mem_append.mpr
    (Or.inr (List.mem_append.mpr
      (Or.inl (List.mem_map.mpr ⟨node0, List.Mem.head _, rfl⟩))))

/-- Stage 1 already holds the third tag representative. -/
theorem node2_mem_ratSlips_one : node2 ∈ ratSlips 1 := by
  rw [← skeletonRest_node0_eq_node2]
  exact List.mem_append.mpr
    (Or.inr (List.mem_append.mpr
      (Or.inr (mem_restPairs (List.Mem.head _) (List.Mem.head _)))))

/-- From stage 1 onward, every stage literally holds all three tag
representatives -- Episode48's covering, supplied by the enumeration. -/
theorem skeletonStage_covers_tagReps {n : Nat} (hn : 1 <= n) :
    forall rep : Bullshit0, rep ∈ [node0, node1, node2] ->
      rep ∈ ratSlips n := by
  intro rep hrep
  cases hrep with
  | head =>
      exact node0_mem_ratSlips n
  | tail _ h1 =>
      cases h1 with
      | head =>
          exact ratSlips_mono hn node1_mem_ratSlips_one
      | tail _ h2 =>
          cases h2 with
          | head =>
              exact ratSlips_mono hn node2_mem_ratSlips_one
          | tail _ h3 =>
              cases h3

/-- The bridge from Episode48, filed as a theorem: no trace over the
discriminating action can take any skeleton stage past the zeroth as its
knots -- the stage covers the three representatives, and the covering is
refused. -/
theorem discriminatingAction_no_skeleton_knots
    (path : FiniteGaugePath) {n : Nat} (hn : 1 <= n)
    (trace : ApproximateLanczosTrace discriminatingAction path)
    (hk : trace.knots = ⟨ratSlips n⟩) : False := by
  apply discriminatingAction_no_covering_trace path trace
  intro rep hrep
  rw [hk]
  exact skeletonStage_covers_tagReps hn rep hrep

/-- The concrete elephant at stage `n`: body `node0`, candidates the
depth-`n` slice of the skeleton. -/
def skeletonElephant (n : Nat) : FiniteElephant where
  body := node0
  candidates := ⟨ratSlips n⟩

/-- The concrete exhausting tower Episode45 asked for, on the family that can
actually be exhausted. -/
def skeletonTower : FiniteElephantTower truthAdmissibleRange where
  stage := skeletonElephant
  stage_inRange := by
    intro n
    exact ⟨trivial, fun _ _ => trivial⟩
  contains_refines := fun n slip h =>
    h.elim
      (fun hb => Or.inl hb)
      (fun hm => Or.inr (ratSlips_mono_succ hm))

/-- Episode45's `hexhaust`, discharged: for every skeleton variation there is
a stage -- computably, `slipDepth variation.slip` -- from which the slip is
literally supported forever. -/
theorem skeletonTower_exhausts
    (variation : FiniteGaugeVariation) (h : IsSkeleton variation.slip) :
    exists N, forall n, N <= n ->
      variation.slip ∈ (skeletonTower.stage n).candidates.entries :=
  ⟨slipDepth variation.slip,
    fun _ hn => ratSlips_mono hn (ratSlips_complete h)⟩

/-- And per Episode47, the quantifier order survives the construction: no
single stage of THIS tower supports every variation either. -/
theorem skeletonTower_no_single_stage (N : Nat) :
    ¬ forall variation : FiniteGaugeVariation,
        variation.slip ∈ (skeletonTower.stage N).candidates.entries :=
  no_uniform_support (ratSlips N)

end Measurement
