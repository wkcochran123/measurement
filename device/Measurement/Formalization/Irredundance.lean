import Measurement.Formalization.Cost
import Measurement.Formalization.Herbrand

/-!
# Irredundance — serial production version (replacing the Boolean version)

The previous draft argued profile-level irredundance: each bit of `Bool^36`
can be flipped. Per the second review that claim is true but does not
characterize the project's actual content.

The correct irredundance claim is about the **serial production grammar**:
no production / stage transition can be removed without losing derivability
of `.inferred`, increasing the minimum cost of reaching `.inferred`, or
forcing the missing information to be carried by another production.

## Three levels (Codex's note)

* **Level 1 — Derivability**: removing a production breaks derivability of
  `.inferred` from `.fact`.

* **Level 2 — Cost**: even when an alternate derivation exists, removing a
  production strictly increases the minimum cost to reach `.inferred`.

* **Level 3 — Hidden cost**: if derivability and cost are both preserved
  when a production is removed, then equivalent information must have been
  moved into another production.

For the strictly serial grammar (one successor per stage) Level 1 is
trivial — removing any step disconnects the chain. Levels 2 and 3 become
load-bearing only when alternate productions are added to the grammar.

## Contents

- `StepSet` — a subset of production steps.
- `allSteps` — every step.
- `removeStep` — pointwise removal of a single production from a step set.
- `DerivableWith` — whether a step set permits a derivation of stage `s`.
- `Derivation.lift` — lift a `Derivation` to a `DerivationWith allSteps`.
- `reachesInferred_allSteps` — `.inferred` is reachable under `allSteps`.
- `ProductionNecessary` — Level 1 irredundance for a single production.
- `derivationWith_rank_lt_removed` — the key invariant: removing a step
  bounds all reachable stages below the target stage's rank.
- `allProductions_necessary` — every production is Level 1 necessary,
  **proved** via the rank-bound invariant.

The cost-level statement (Level 2) is documented as future work in a
docstring section near the end of this file; no theorem in this file
asserts a Level 2 result. Level 2 belongs to `Search.lean`.
-/

namespace Measurement.Formalization

/-! ## Step sets -/

/-- A step set: which production transitions are admissible. -/
abbrev StepSet := (s t : Stage) → Bool

/-- The set containing every step. -/
def allSteps : StepSet := fun _ _ => true

/-- The step set `R` minus the production `s → t`. -/
def removeStep (R : StepSet) (s₀ t₀ : Stage) : StepSet :=
  fun s t => if s = s₀ ∧ t = t₀ then false else R s t

/-! ## Derivability under a step set -/

/-- A derivation of `s` permitted by step set `R`: same as `Derivation`,
but each step must be allowed by `R`. -/
inductive DerivationWith (R : StepSet) : Stage → Type
  | fact : DerivationWith R .fact
  | step {s t : Stage}
      (hStep : Step s t)
      (hAllow : R s t = true)
      (d : DerivationWith R s) :
      DerivationWith R t

/-- `R` derives `s` iff there is some `DerivationWith R s`. -/
def DerivableWith (R : StepSet) (s : Stage) : Prop :=
  Nonempty (DerivationWith R s)

/-- Every step is permitted by `allSteps`. -/
@[simp] theorem allSteps_true (s t : Stage) : allSteps s t = true := rfl

/-- Lift any `Derivation s` to a `DerivationWith allSteps s` — every step is
trivially allowed under the full step set. -/
def Derivation.lift {s : Stage} : Derivation s → DerivationWith allSteps s
  | .fact      => .fact
  | .step h d  => .step h (allSteps_true _ _) d.lift

/-- The canonical derivation under the full step set. -/
def derivationWith_inferred : DerivationWith allSteps .inferred :=
  derivation_inferred.lift

/-- The full step set reaches `.inferred`. The reachability witness used by
`allProductions_necessary` and `cascade_level1_minimal`. -/
theorem reachesInferred_allSteps : DerivableWith allSteps .inferred :=
  ⟨derivationWith_inferred⟩

/-! ## Level 1: derivability irredundance

A production `s₀ → t₀` is Level 1 necessary iff:

1. with all steps, `.inferred` is derivable, AND
2. with that production removed, `.inferred` is no longer derivable.
-/

/-- Level 1 irredundance for a single production. -/
def ProductionNecessary (s₀ t₀ : Stage) (_h : Step s₀ t₀) : Prop :=
  DerivableWith allSteps .inferred ∧
  ¬ DerivableWith (removeStep allSteps s₀ t₀) .inferred

/-! ### Key invariant: under a removed step, derivations are rank-bounded

Under `removeStep allSteps s₀ t₀`, every reachable stage has rank strictly
below `Stage.rank t₀`. Proof by induction on `DerivationWith`. The base
case (`.fact`) uses `Step.target_rank_pos` to show `0 < Stage.rank t₀`. The
step case argues: the new stage's rank is one more than its source's;
if it equalled `Stage.rank t₀`, then by `Stage.rank_injective` the stage IS
`t₀`, and by `Step.prev_eq` the source is `s₀`, which makes the step
exactly `s₀ → t₀` — but that step is forbidden by `removeStep`. -/
theorem derivationWith_rank_lt_removed
    {s₀ t₀ : Stage} (h₀ : Step s₀ t₀) :
    ∀ {u : Stage}, DerivationWith (removeStep allSteps s₀ t₀) u →
      Stage.rank u < Stage.rank t₀ := by
  intro u d
  induction d with
  | fact =>
      exact Step.target_rank_pos h₀
  | @step s_src t_src h_step hAllow _ ih =>
      have hr : Stage.rank t_src = Stage.rank s_src + 1 := Step.rank_succ h_step
      by_cases h_eq_rank : Stage.rank t_src = Stage.rank t₀
      · exfalso
        have h_eq : t_src = t₀ := Stage.rank_injective h_eq_rank
        have h_prev_u : Stage.prev t_src = some s_src := Step.prev_eq h_step
        have h_prev_t : Stage.prev t₀ = some s₀ := Step.prev_eq h₀
        rw [h_eq] at h_prev_u
        -- After rw: h_prev_u : Stage.prev t₀ = some s_src
        --           h_prev_t : Stage.prev t₀ = some s₀
        -- Chain (some s_src = Stage.prev t₀) ⋅ (Stage.prev t₀ = some s₀)
        have h_some_eq : some s_src = some s₀ := h_prev_u.symm.trans h_prev_t
        have h_eq_s : s_src = s₀ := Option.some.inj h_some_eq
        rw [h_eq, h_eq_s] at hAllow
        simp [removeStep] at hAllow
      · omega

/-- **Stage 5 (level 1):** every production in the serial chain is
necessary. Removing any single `Stage.next`-witnessed step disconnects the
derivation from `.fact` to `.inferred`.

Proof: `derivationWith_rank_lt_removed` shows that under
`removeStep allSteps s₀ t₀`, every reachable stage has rank strictly less
than `Stage.rank t₀`. In particular, `.inferred` (rank 36) is unreachable
unless `Stage.rank t₀ > 36`, but `Stage.rank_le_inferred` gives
`Stage.rank t₀ ≤ 36`. Contradiction.

The predecessor lemma here is `Step.prev_eq` (not `Step.unique`, which is
successor uniqueness). The rank-injectivity lemma is `Stage.rank_injective`.
The reachability witness uses `reachesInferred_allSteps`
(`DerivableWith allSteps .inferred`), not the bare
`inferred_derivable : Nonempty (Derivation .inferred)`. -/
theorem allProductions_necessary :
    ∀ s₀ t₀ : Stage, ∀ h : Step s₀ t₀, ProductionNecessary s₀ t₀ h := by
  intro s₀ t₀ hStep
  refine ⟨reachesInferred_allSteps, ?_⟩
  rintro ⟨d⟩
  have hrank : Stage.rank .inferred < Stage.rank t₀ :=
    derivationWith_rank_lt_removed hStep d
  have hle : Stage.rank t₀ ≤ Stage.rank .inferred := Stage.rank_le_inferred t₀
  omega

/-! ## Level 2 cost irredundance — shape theorem only

This section *only states the shape* of Level 2 cost irredundance. The
substantive content — a real `minCost` over an enumerable search space —
belongs in `Search.lean` (next file). Until that file exists, no
non-trivial Level 2 statement should be asserted.

The shape we are aiming at:

> For each production `s₀ → t₀` in the chain, the minimum cost of reaching
> `.inferred` from `.fact` under `allSteps` is strictly less than the
> minimum cost under `removeStep allSteps s₀ t₀`. (In the strictly serial
> grammar this is equivalent to Level 1: removing a production prevents
> reaching `.inferred` at all, so the "increased cost" is `+∞`.)

When `Search.lean` provides a non-vacuous `minCost`, this section will
contain `ProductionCostNecessary` and `allProductions_cost_necessary`. Until
then, we leave only this docstring as a placeholder.
-/

end Measurement.Formalization
