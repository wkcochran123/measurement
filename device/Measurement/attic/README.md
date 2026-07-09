# attic/ — the codebase's antimatter budget (quarantine, never delete)

*Task `instrument`, Phase 0a. Below-floor decls `git mv`'d here (SPEC §4). Quarantined, not deleted —
add back adiabatically, one above-floor rung at a time, if a later phase needs them. Nothing here is
imported by the active tree.*

## Quarantined (Turn 77 #1 — dead by the operator's criterion)
- `ProfileToy.lean` — the sidelined `Bool^36` toy model; its own docstring says "not the main formalization",
  "Do not cite the theorems in this file". Dead leaf (imported by nothing). Was `Formalization/ProfileToy.lean`.
- `Formalization_aggregator.lean` — the import-only orphan aggregator (`Measurement.Formalization`); "no new
  theorems/definitions", not imported by the root. Was `Formalization.lean`.
- `Agent.lean` — thin re-export aggregator (0 own decls); nothing imports it (everything imports
  `Agent.Positron` directly, which STAYS in the active tree).
- `Basic.lean` — the lake-generated placeholder `def hello := "world"`.
- `Episode93.lean` — all decls are `def : Prop` (`did_this_distinguish?`, `youTheReader_asked`, …); no theorem,
  `#eval`, or proof term — registers no distinction. Leaf.

## NOT atticked — repaired instead (CHOICE, deviation from Turn 77 #3, justified)
- `Formalization/FiniteGaugeEquation.lean` — Turn 77 said attic-for-now. But it's imported by `Bridge → QED →
  Example` (a real off-α-path track), so atticking cascade-breaks 5 files — a hard cut the SPEC §5 anti-Gibbs
  principle warns against. Its break was the SAME sacred-signature drift as Epiphany (`LOCAL` missing its
  explicit `(real: REAL)` arg). **Repaired in place (4 lines), keeping the whole QED track green.** Smooth
  repair over hard cut.

## Repaired in place (α-critical-path unblock — NOT atticked)
- `Formalization/Epiphany.lean:340/352` — `FullCascadeObject` binders under-applied `LOCAL`/`MEASURED` against
  their sacred signatures (which now take an explicit `(real/imaginary: REAL)`). Fixed 2 binders → the whole
  ℕ-cost spine (`Grammar`/`Cost`/`Search`, incl. `derivation_cost_eq_rank`, `inferred_cost=36`) reopened,
  axiom-clean. `FullCascadeObject`/`truthObject` stay in Epiphany (above-floor: the canonical truth cascade).

Net: the entire Formalization branch went from 100% broken to 100% building with **6 lines of repair and zero
cascade cuts**.
