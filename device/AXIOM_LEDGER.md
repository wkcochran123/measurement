# Episode Axiom Ledger — `device/Measurement/Episode1..81`

In-order reading of the Lean development, recording each episode's theorems with
the axioms they depend on.

> **Status: READ-DERIVED, pending build.** `#print axioms` was **not** run (Lean
> build in progress, per operator). Every axiom attribution below is derived from
> (a) static reading of proof terms, (b) the two taint rules below, and (c) the
> author's own in-source `#print axioms` audit annotations (Ep46, 50, 52–59, 73,
> 81). When the build lands, confirm against the `#print axioms` blocks the source
> already contains. Lines flagged **[PENDING BUILD]** are the only ones the source
> does not already pin.

---

## 0. The complete axiom inventory (entire 81-episode development)

There are **exactly four** axioms anywhere in the closure, and **no `sorry`**:

| # | axiom | kind | where it enters | reach |
|---|---|---|---|---|
| 1 | `propext` | Lean foundational (ambient) | Prop-level theorems | most theorems |
| 2 | `Quot.sound` | Lean foundational (ambient) | quotient/typeclass machinery | most theorems |
| 3 | `eulerLagrangeOracle` | **the one custom `axiom`** (Ep19:109) | declared Ep19 | ~20 theorems, Ep19–26 only |
| 4 | `Classical.choice` | Lean classical (ambient) — **never called directly** | inherited from scaffolding | Ep52 onward, specific theorems |

- A theorem's "axioms" is therefore drawn from `{propext, Quot.sound}` plus,
  *for a minority*, `eulerLagrangeOracle` and/or `Classical.choice`.
- Purely arithmetic theorems over `Nat`/`Int` closed by `rfl`/`decide`/`omega`
  depend on **no axioms at all** (the author records several such, e.g. Ep73).
- **No `Classical.` call appears in any episode body** — every `Classical.*`
  token in the corpus is in a comment. Choice is inherited structurally, not invoked.

### The one custom axiom (Ep19)

```lean
/-- ... This is the axiom of choice in its physical form: the law of motion is
the one query nature answers that the machine cannot. -/
axiom eulerLagrangeOracle
    (derivative : DiscreteGaugeDerivative) (path : FiniteGaugePath) :
    Decidable (derivative.eulerLagrange path)
```

It is consumed **only** by `noncomputable def residue` (Ep19), which uses it as the
`Decidable` instance behind an `if derivative.totalResidualVanished path then …`.

## 1. The two taint rules

- **Oracle rule.** A theorem depends on `eulerLagrangeOracle` **iff** its proof
  term touches `residue` (the `*_residue_eq_truth_zero` family). Theorems about the
  `eulerLagrange` predicate or the `eulerLagrangeResidual : Int` are constructive
  and oracle-free. Oracle reach = Ep19–26.
- **Choice rule.** A theorem depends on `Classical.choice` **iff** its closure
  touches one of two scaffolding roots:
  - **the chair** `truthLocal` (Ep16 instance; `noncomputable`, classical via
    `SAME`'s `Classical.propDecidable`), used in Ep52 (`the_stack_produces_it`),
    Ep56 (the door), Ep81 (the chair);
  - **the geometric program** rooted in Ep28's `x = zero` case-split, when consumed
    by the noncomputable three-rung generated program (Ep53–55, Ep57 flux theorems).
  Ep28's own theorems are choice-free; choice surfaces only when the program is
  generated through the noncomputable chair.

---

## 2. In-order ledger

### Ep1–15 — scaffolding (no theorems)

Pure type tower; **zero theorems, zero axioms beyond Lean defaults**. Each episode
adds a `structure`/`class` pair; Ep8 wires the instance chain
(`STEP_1 → … → ACOLYTE_PROPAGANDA`); Ep15 tops out at `class INFERRED` with
`noncomputable def SAME` (`Fact.SAME`, choice-free in itself).

Defines: `Fact, Number, Natural, Rational, Sequence, Limit, Sample` and the class
tower `CarrierProcess → DISTINGUISHABLE → COUNTABLE → ENCODED → CauchyProcess →
RESIDUE → BINARY → … → MEASURED → COMPILED → TrueOutput → INFERRED`.

### Ep16 — first theorem (`propext`)

- `true_eq_false : Subsingleton Fact.Truth.truth = Subsingleton (¬ Fact.Truth.truth)`
  — proof `apply propext; exact ⟨…, …⟩`. **Axioms: `propext` (+ ambient `Quot.sound`).**
  (Top-of-file comment documents that `Classical.em`-using instances were *removed*
  to stay choice-free.) Also instantiates the whole `truth*` instance tower at `Prop`.

### Ep17 — finite gauge stationarity (clean)

`FiniteGaugePath`/`FiniteGaugeAction`; `direct/composed/admits/stationaryAt/flatAt/
closedFlatAt/reducibleSlip`.
- `flatAt_stationaryAt`, `closedFlatAt_admits`, `closedFlatAt_flatAt`,
  `closedFlatAt_reducibleSlip`, `reducibleSlip_admits`, `reducibleSlip_stationary`.
- **All constructive over `Nat` (`.left/.right`, `Nat.le_refl`). No axioms.**

### Ep18 — Frechet approximation (clean)

- `apply_identity`, `firstVariation_eq_composedDifference`, `fromAction_remainder_zero`,
  `fromAction_stationaryAt_of_flatAt`, `stationaryAt_zero`.
- **All `rfl`/`simp`/`omega`/`rw` over `Int`/`Nat`. No axioms** (`omega` is choice-free).

### Ep19 — Euler–Lagrange + THE ORACLE

Declares `axiom eulerLagrangeOracle`; `noncomputable def residue` consumes it.

- **Oracle-dependent (touch `residue`):**
  `totalResidualVanished_residue_eq_truth_zero`,
  `eulerLagrange_residue_eq_truth_zero`,
  `stationary_residue_eq_truth_zero`,
  `fromAction_closedFlatAt_residue_eq_truth_zero`
  → **`eulerLagrangeOracle` (+ ambient).**
- **Clean (predicate-level, no `residue`):**
  `residualVanished_iff_eulerLagrange` (`Iff.rfl`),
  `totalResidual_eq_zero_of_totalResidualVanished`,
  `totalResidualVanished_iff_directResidual_eq_zero_and_eulerLagrange`,
  `fromAction_directResidual_eq_zero_of_admits`,
  `stationary_implies_eulerLagrange`, `eulerLagrange_implies_stationary`,
  `stationary_iff_eulerLagrange`, `fromAction_closedFlatAt_totalResidualVanished`.

### Ep20–26 — cubic spline / Lanczos / partitions (oracle only via the `residue` family)

The **only** oracle-carrying theorems are the `*_residue_eq_truth_zero` family; all
other theorems (about `eulerLagrange`, `eulerLagrangeResidual`, weak residuals,
support, multisets) are constructive/clean.

| Ep | oracle-dependent theorems (`eulerLagrangeOracle` + ambient) |
|---|---|
| 20 | `cubicSplineBalanced_residue_eq_truth_zero`, `cubicSplineClosed_residue_eq_truth_zero`, `residue_eq_truth_zero`, `law_of_spline_sufficiency`, `truthTerminal_residue_eq_truth_zero` |
| 21 | `residue_eq_truth_zero`, `terminal_residue_for_any_iteration_order`, `truthTerminalTrace_residue_eq_truth_zero` |
| 22 | `residue_eq_truth_zero`, `truthPartitionedLanczos_residue_eq_truth_zero` |
| 23 | `residue_eq_truth_zero`, `truthRealizedPartitionedFunction_residue_eq_truth_zero` |
| 24 | *(none — all touch `eulerLagrangeResidual : Int`, constructive; clean)* |
| 25 | `residue_eq_truth_zero` (×2), `truthFastestHeartbeat_residue_eq_truth_zero` |
| 26 | `residue_eq_truth_zero` |

Everything else in Ep20–26: **`{propext, Quot.sound}` ambient, no oracle, no choice.**

### Ep27 — Weierstrass/squeeze convergence (clean)

`residual_tends_zero`/`terminalResidualMagnitude_tends_zero`/… — **"residual," not the
oracle `residue."** No `residue` touch → **no oracle; clean.** Oracle reach ends at Ep26.

### Ep28 — Sobolev activity / SPD certificate (clean; second choice ROOT, not yet a leak)

`ActivityGaugeCertificate`, `GalerkinBilinearForm`, `SPDGalerkinActivity`;
`energySq x = 0 ↔ x = zero`, coercivity `x ≠ zero → 0 < a x x`, nullspace killing.
Its `x = zero` case-splits are the **second geometric choice root**, but Ep28's own
theorems are **choice-free** (per Ep50/51 audits); choice surfaces only when the
geometric program is generated noncomputably in Ep53+.

### Ep29–45, 47–49 — clean-math core (no oracle, no choice)

Theorems are `{propext, Quot.sound}` ambient (many are `decide`/`omega`/`rfl`-clean
with no axioms). Notable: **Ep31** `secondVariation_remainder_unique` (single
invariant); **Ep40** the example→def conversion target (defs, 0 theorems);
**Ep44** the kicked path reads 2; **Ep45** Weierstrass-by-instantiation.

### Ep46 — AUDIT episode (no theorems)

`#eval`/`#print axioms` record. Documents: constructive rungs (`gaugeReading`,
`rung3Numeric`, `rung3Comparable`, `sample_tendsToZero`) are choice-free; the needle
`rung3Inferred` was *historically* reached through `SAME`'s classical diagonal.

### Ep48–49 — discriminating action / skeleton tower (clean)

`telescoping_*`, `discriminating_*`, skeleton tower data. Choice-free.

### Ep50 — AUDIT + produced certificate (clean) — **needle correction**

Records the key correction: **"Episode46's standing expectation that `rung3Inferred`
lists `Classical.choice` is stale — the build reports `[propext, Quot.sound]`."** Own
theorems `skeletonStageTrace_terminalResidual`, `skeleton_unconditional_tendsToZero`,
`skeleton_discharge_via_exhaustion`, and the audited Ep48–50 theorems: **all
choice-free `{propext, Quot.sound}`.**

### Ep51 — Frechet uniqueness / Taylor terminates (clean, documented)

Audited: `cubicSplineResidual_eq_firstVariation`, `frechetDerivative_exists/_unique/
_existsUnique`, `linearization_unique`, `cubic_left/right_slot_unique`,
`taylor_terminates_at_order_two`, `telescoping_derivative_zero`,
`discriminating_derivative_nonzero`, `frechet_crosses_the_finish_line`,
`flat_actions_cross_too`, `nonzero_residual_fails_eventual_exactness`.
**Documented choice-free `{propext, Quot.sound}`.** (Ep1–51 are choice-free.)

### Ep52 — Pair Production = CHOICE FRONTIER (documented split)

`electron = -1`, the second-variation residue. Author's audit:
- **`Classical.choice`** (`[propext, Classical.choice, Quot.sound]`) — **only**
  `the_stack_produces_it` (inherited from the chair `truthLocal`, *not* the electron);
  by extension `electronVariation` / `electronVariation_normal_form` (seated under the
  chair, `noncomputable`).
- **Clean `[propext, Quot.sound]`** — the production line:
  `electron_charge`, `positron_charge`, `same_pair_charge`,
  `mixedCoupling_needs_the_pair_left/right`,
  `residue_is_the_difference_between_story_and_measurement`, `strain_iff_residue`,
  `electron_strain_is_real`, `electron_strain_iff_charge`, `pair_moved`,
  `linear_story_fails`, `electron_is_the_secondVariation`, `vacuum_is_empty`,
  `certificate_is_C2`, `hilberts_sixth_on_the_vacuum`.

### Ep53 — geometric program detects invariant (documented CHOICE)

**`[propext, Classical.choice, Quot.sound]` on all three** — geometric side inherits
choice from Ep28: `GeometricProgram.invariant_zero_detects`,
`threeRungGeometricProgram_invariant_zero_detects`,
`threeRungGeometricProgram_source_is_white_hole`.

### Ep54 — compiled action produces the electron (documented CHOICE)

**`[propext, Classical.choice, Quot.sound]`** (geometric):
`threeRungCompiler_generates_discriminatingAction`,
`threeRung_vacuum_compiles_to_zero_action`, `compiled_action_produces_the_electron`.

### Ep55 — geometry generates QED program (documented CHOICE)

**`[propext, Classical.choice, Quot.sound]`** (the generated program):
`generatedThreeRungQEDProgram`, `geometric_program_generates_qed_program`.

### Ep56 — pairing door / certificate split (documented CHOICE — the door = chair)

**`[propext, Classical.choice, Quot.sound]`** (the door, the chair):
`threeRungPairingDoor_dot_zero_left`, `threeRungCertificateSplit_sectors_nontrivial`.

### Ep57 — boundary radiation, finite (documented MIXED)

- **Clean `[propext, Quot.sound]`** — the three obstruction theorems:
  `orthogonal_clifford_scalar_cross_zero`, `no_interior_scalar_mixed_of_orthogonal`,
  `threeRung_no_interior_mixed_certificate`.
- **`[propext, Classical.choice, Quot.sound]`** — the two flux theorems:
  `generated_boundary_flux_eq_terminal_residual`, `boundary_radiation_finite`.

### Ep58 — flat tower (documented CLEAN)

**`[propext, Quot.sound]`, choice-free** ("flat tower is on the production line"):
`flat_residual_zero`, `flatPairCompleted_exists`, `flatPair_unconditional_tendsToZero`.

### Ep59 — QED Cauchy convergence (documented CLEAN / NO AXIOMS)

- **NO axioms at all** on the general theorem (`completed_residual_isCauchy` — pure
  Cauchy argument).
- **`[propext, Quot.sound]`** on `qed_cauchy_convergence_as_gr_epsilon_vanishes`,
  `flatPair_qed_isCauchy`.

### Ep60–72, 74–80 — Cohen/Sobolev/continuum + capstone machinery **[PENDING BUILD]**

These have `#print axioms` targets but **no inline expected-axiom annotation** — the
running build settles them. Structural inference: those built purely on the
arithmetic/Cohen/flat production line are **expected clean `{propext, Quot.sound}`**;
any routed through the noncomputable three-rung *generated/geometric* program may
inherit **`Classical.choice`** (the Ep28 root). Confirm via `#print axioms` on build.

- **Ep60** Counting to three: `successorNumber_eq_zero_succ_succ`, `canonical_ofNat`,
  `induction_on_canonical/_ofNat`, `succ_succ`, `succ_one_eq_two`, `succ_two_eq_three`,
  `succ_certificate_lift`, `one_add_one_eq_two`, `one_add_two_eq_three`,
  `one_add_one_add_one_eq_three`. *(expected clean / no-axiom arithmetic).*
- **Ep61** Cohen up to epsilon: `SplineCondition.merge_of_compatible`,
  `…dense_decides_knot`, `…dense_decides_finite_requests`,
  `splineCondition_cohen_up_to_epsilon`, `lanczosSpline_cohen_up_to_epsilon`,
  `cohen_cauchy_up_to_epsilon`.
- **Ep62** `…sameAtoms_of_extends_both`, `…merge_extensional_comm`,
  `splineCondition_extensional_order`, `splineCondition_order_up_to_extensionality`.
- **Ep63** `SplineAtom.code_witness`, `splineAtomListCode_witness`,
  `SplineCondition.code_witness`, `splineCondition_conditions_countable`,
  `finiteCohen_ledger_has_nat_code`, `finiteCohen_countable_up_to_epsilon`.
- **Ep64** `splineCondition_finiteCohenCompliant`, `lanczosSpline_cohen_compliant`,
  `finiteCohen_boundary_radiation_closeout`, `finiteGauge_successor_commutator_residue`
  (+`_theorem`/`_from_count`), `finiteCohen_gauge_residue_closeout`.
- **Ep65** `SobolevHilbertDoor.norm_zero(_detects)`, `threeRungSobolevHilbertDoor`,
  `zeroFiniteCohenPreHilbertSkeleton`, `threeRungHilbertCompletionArc`,
  `hilbertCompletionArc_setup`, `…has_completion_token`, `…retains_finite_residue`.
- **Ep66** `separablePreHilbertSkeletonOfFinite`, `separableSkeleton_condition_coded`,
  `finiteResidualMapsIntoCompletion(_retains_residue)`,
  `threeRung_completion_maps_finite_residue`.
- **Ep67** `threeRungGeometricSobolevCertificate`, `threeRungGaugeSobolevCertificate`,
  `threeRung_boundaryGenerated`, `threeRungContinuumCertificatePair`.
- **Ep68** `zero_left_sobolev_orthogonal`, `threeRung_sobolev_orthogonal`,
  `finite_split_orthogonality_lifts`.
- **Ep69** `no_continuum_interior_scalar_mixed`, `emptyContinuumCliffordCompatible`,
  `threeRungContinuumCliffordCompatible`, `threeRung_no_continuum_interior_scalar_mixed`.
- **Ep70** `generatedBoundaryTraceFunctional`, `generatedBoundaryTrace_compatible`,
  `boundaryTrace_agrees_with_terminal_residual`.
- **Ep71** `threeRungResidualCauchyWitness`, `threeRung_residual_cauchy_in_sobolev_norm`,
  `threeRungCauchyLiftThroughCompletion`.
- **Ep72** `generalized_boundary_radiation_continuum`,
  `threeRung_generalized_boundary_radiation_continuum`.
- **Ep73** Orientation as measurement — **DOCUMENTED**:
  `orientationReading_electron/_positron`, `orientation_readings_cancel`,
  `ConventionAnchor.anchoredReading`, `sample_electron_count`, `sample_positron_count`,
  `sample_electron_dominates`, `sampleAnchor`, `sample_anchoredReading`
  → **NO axioms**; `dominant_unique`, `anchor_unique` → **`[propext, Quot.sound]`**.
- **Ep74** `threeRung_resolved_add_unresolved_eq_whole`,
  `reciprocalAccounting_truth_parity_surface`,
  `threeRung_reciprocal_residue_certificate`, `threeRung_preHilbert_reciprocal_energy`,
  `episode74_reciprocal_accounting_package`.
- **Ep75** The Outside Reading: `threeRung_einstein_field_equations_hold`,
  `threeRung_navierStokes_balance`, `threeRung_navierStokes_errorCode`,
  `einstein_approximation_forces_navierStokes`.
- **Ep76** `DISTINGUISHED_GODEL_SENTENCE`,
  `distinguished_godel_sentence_reads_obstruction`.
- **Ep77** `secondGodelIndex_is_succ_succ`, `SECOND_DISTINGUISHED_GODEL_SENTENCE`,
  `second_distinguished_godel_sentence_reads_obstruction`.
- **Ep78** `BoundarySignal.on_ne_off`, `Fact_FALSE_is_zero_strain_residue`,
  `Distinguished.falseRead_zero_strain`, `Distinguished.truthBit_neq_false`,
  `Distinguished.true_neq_false`, `distinguished_sequence_true_neq_false`.
- **Ep79** `truthBinaryToInferredTower`, `finalGodelTarget_is_inferred`,
  `FINAL_INFERRED_CLOSE`, `inferred_closed_for_the_last_time`.
- **Ep80** How Much Do You Want? — note: built to **avoid** "the undecidable case
  split that would otherwise call for choice." `ExplanationChange.none_liftSignal_off`,
  `BoundarySignal.deMorgan_meet/_join`, `prop_deMorgan_not_or/_and`,
  `formal_theorem_authorizes_more`, `inferredCloseInvariant_holds`,
  `HOW_MUCH_DO_YOU_WANT`, `requested_depth_projection_receipt`,
  `how_much_do_you_want_continue_if_new_boundary`,
  `duh_we_made_binary_how_much_do_you_want`.

### Ep81 — capstone "the chair" (documented CHOICE)

**"Expect the chair — `[propext, Classical.choice, Quot.sound]`."**
`measurementBit_on`, `distinguished_distinguishable`, `binary_is_enough`.

---

## 3. Summary

- **Total axioms in the whole development: 4** (`propext`, `Quot.sound`,
  `eulerLagrangeOracle`, `Classical.choice`). **No `sorry`.**
- **`eulerLagrangeOracle`** (the one custom axiom): ~20 `*_residue_eq_truth_zero`
  theorems, **Ep19–26 only**.
- **`Classical.choice`** (never called; inherited): the chair (Ep52
  `the_stack_produces_it`, Ep56 door, Ep81 chair) and the noncomputable geometric
  program (Ep53–55, Ep57 flux). Ep1–51 are choice-free.
- **Everything else: `{propext, Quot.sound}`**, with many `Nat`/`Int` theorems
  depending on **no axioms at all**.
- **[PENDING BUILD]:** Ep60–72, 74–80 lack inline expected-axiom annotations; the
  running `#print axioms` build is the authority for their choice-vs-clean split.
