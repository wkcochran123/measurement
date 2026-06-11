import Measurement.Episode46

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000
set_option allowUnsafeReducibility true

namespace Measurement

/-
__EPISODE 47__: _The Quantifier Is Forced_

Episode45 left one residue: the exhaustion hypothesis.  Its header promised
"the rational enumeration" as the next step.  An adversarial review of that
promise found a bug in the prose, and this episode files the bug report as
theorems.

The hypothesis `hexhaust` is quantified per-variation:

  forall variation, EXISTS N, forall n >= N, variation.slip ∈ stage-n support

That quantifier order is not a stylistic choice.  It is forced, and the
forcing argument is the pigeonhole principle in its escape form: a stage's
support is one finite list, and the slips are an infinite family, so every
finite list misses a slip.  More pigeons than holes; some pigeon stands
outside.  Hence no single stage -- and no uniform N -- can ever support every
variation literally, and `EXISTS N, forall variation` is unprovable for any
tower whatsoever.  The per-slip form is the only form there is.

The infinite family of pigeons is built honestly: iterate the skeleton `.one`
constructor over the fixed atoms (`Fact.Truth`, `Number.zero Fact.Truth`, the
boot tape).  A spine-depth measure separates the iterates -- `oneDepth` reads
the iteration count back off the term -- so the family is injective, and the
escape witness for a list `l` is computable: the iterate at depth
`maxOneDepth l + 1`, one deeper than anything `l` holds.

Stated formally:
* `iterOne_injective` -- the pigeons are pairwise distinct.
* `finite_entries_miss_a_slip` -- THE PIGEONHOLE: every finite list of slips
  misses one, with a computable witness.
* `no_uniform_support` -- no finite stage supports all variations; the
  uniform-N strengthening of `hexhaust` is dead on arrival.

Residue left (honest scope):
the pigeonhole here is the negative half.  It dictates the logical form of
the discharge but discharges nothing itself.  The positive half -- which
slips CAN be exhausted, and by which concrete tower -- is Episodes 48 and 49.
-/

/-- The skeleton `.one` constructor over the fixed atoms.  Applying it to
`node0` reproduces Episode44's `node1` exactly. -/
def skeletonOne (b : Bullshit0) : Bullshit0 :=
  .one Fact.Truth (Number.zero Fact.Truth)
    (CompilerTape.boot Fact.Truth (Unit : Type))
    (CompilerTape.boot Fact.Truth (Unit : Type))
    b

theorem skeletonOne_node0_eq_node1 : skeletonOne node0 = node1 := rfl

/-- The pigeons: the n-fold `.one` spine over `node0`. -/
def iterOne : Nat -> Bullshit0
  | 0 => node0
  | n + 1 => skeletonOne (iterOne n)

/-- The separating measure: read the `.one` spine length back off the term. -/
def oneDepth : Bullshit0 -> Nat
  | .zero _ => 0
  | .one _ _ _ _ b => oneDepth b + 1
  | .rest _ _ _ _ _ _ _ _ _ _ => 0

theorem oneDepth_iterOne : forall n, oneDepth (iterOne n) = n
  | 0 => rfl
  | n + 1 => by
      simp [iterOne, skeletonOne, oneDepth, oneDepth_iterOne n]

/-- The pigeons are pairwise distinct: `oneDepth` inverts `iterOne`. -/
theorem iterOne_injective {m n : Nat} (h : iterOne m = iterOne n) : m = n := by
  have hm := oneDepth_iterOne m
  rw [h, oneDepth_iterOne n] at hm
  exact hm.symm

/-- The deepest spine a finite list holds. -/
def maxOneDepth : List Bullshit0 -> Nat
  | [] => 0
  | b :: rest => max (oneDepth b) (maxOneDepth rest)

theorem oneDepth_le_maxOneDepth {b : Bullshit0} {entries : List Bullshit0}
    (h : b ∈ entries) : oneDepth b <= maxOneDepth entries := by
  induction h with
  | head rest =>
      exact Nat.le_max_left _ _
  | tail hd _ ih =>
      exact Nat.le_trans ih (Nat.le_max_right _ _)

/-- THE PIGEONHOLE, escape form: any finite list of slips misses a slip, and
the witness is computable -- the spine one deeper than anything listed. -/
theorem finite_entries_miss_a_slip (entries : List Bullshit0) :
    exists slip : Bullshit0, ¬ slip ∈ entries := by
  refine ⟨iterOne (maxOneDepth entries + 1), fun hmem => ?_⟩
  have hle := oneDepth_le_maxOneDepth hmem
  rw [oneDepth_iterOne] at hle
  omega

/-- No finite stage supports every variation literally: the uniform-N form of
Episode45's `hexhaust` is unprovable for any tower.  The per-variation
quantifier order is forced. -/
theorem no_uniform_support (entries : List Bullshit0) :
    ¬ forall variation : FiniteGaugeVariation,
        variation.slip ∈ entries := by
  intro hall
  obtain ⟨slip, hmiss⟩ := finite_entries_miss_a_slip entries
  exact hmiss (hall { slip := slip })

end Measurement
