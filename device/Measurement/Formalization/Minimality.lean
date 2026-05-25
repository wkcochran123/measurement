import Measurement.Formalization.Irredundance

/-!
# Minimality — Level 1 (serial-grammar)

**Scope of this file.** This file states and proves the Level-1 minimality
wrapper: the 36-gate serial grammar derives `.inferred` from `.fact`, and
each individual production is necessary for that derivation. The wrapper
does NOT yet prove cost-sortedness, Level 2 cost irredundance, or Level 3
hidden-evidence irredundance. Those are deferred to `Search.lean` and
later files.

To avoid promising more than the proofs deliver, the wrapper is named
`Level1MinimalSerialGrammar`, not `MinimalSearchGrammar`.

## Basis-Gauge Thesis status

The Level 1 portion of the Basis-Gauge Thesis is now proved:

> The 36 gates form a serial grammar from `.fact` to `.inferred`, and no
> production can be removed without losing derivability of `.inferred`.

Levels 2 (cost irredundance) and 3 (hidden-evidence irredundance) remain
future work. The full Basis-Gauge Thesis combines all three levels and
sits at the top of a layered theorem stack.
-/

namespace Measurement.Formalization

/-- A serial production grammar that satisfies the Level 1 minimality
property: it reaches the target stage, and each production is necessary
for that derivation. (Levels 2 and 3 — cost and hidden-evidence — are
not yet claimed here.) -/
structure Level1MinimalSerialGrammar where
  reachesInferred : DerivableWith allSteps .inferred
  irredundant : ∀ s₀ t₀ : Stage, ∀ h : Step s₀ t₀,
    ProductionNecessary s₀ t₀ h

/-- The serial cascade satisfies the Level 1 minimality wrapper:
derivability of `.inferred` plus per-production necessity.

Reuses `reachesInferred_allSteps` and `derivationWith_inferred` from
`Irredundance.lean` — no duplicate definitions. -/
theorem cascade_level1_minimal : Level1MinimalSerialGrammar where
  reachesInferred := reachesInferred_allSteps
  irredundant := allProductions_necessary

end Measurement.Formalization
