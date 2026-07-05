# Episode Axiom Ledger — `device/Measurement/Episode1..81`

In-order reading of the Lean development, recording each episode's theorems with
the axioms they depend on.

> **Status: BUILD-CONFIRMED (fidelity A.12, 2026-07-05).** `#print axioms` HAS now
> been run per-decl (`lake env lean`). It **OVERTURNS** the read-derived
> `Classical.choice` attributions below: **the corpus is choice-free end to end.**
> Every decl once tagged "documented CHOICE" (the chair Ep52/56/81, the geometric
> program Ep53–55, the Ep57 flux) builds `[propext, Quot.sound]`. Root cause of the
> error: the read-derived "Choice rule" conflated `noncomputable` with
> `Classical.choice` — the chair `truthLocal` is a `noncomputable instance` yet
> `[propext, Quot.sound]` (noncomputable is Quot/funext-borne, NOT the choice axiom).
> The ONLY `Classical.choice` in any footprint is `band_covers` (Ep92), and it is a
> `by omega` TACTIC artifact — the same statement proved by hand is axiom-free `[]`.
> Sections below are corrected in place; the per-episode "documented CHOICE" tags are
> superseded and marked. The build (`#print axioms`), not this prose, is the count.

---

## 0. The complete axiom inventory (entire 81-episode development)

There are **exactly four** axioms anywhere in the closure, and **no `sorry`**:

| # | axiom | kind | where it enters | reach |
|---|---|---|---|---|
| 1 | `propext` | Lean foundational (ambient) | Prop-level theorems | most theorems |
| 2 | `Quot.sound` | Lean foundational (ambient) | quotient/typeclass machinery | most theorems |
| 3 | `eulerLagrangeOracle` | **the one custom `axiom`** (Ep19:109) | declared Ep19 | ~20 theorems, Ep19–26 only |
| 4 | `Classical.choice` | **BUILD: absent as a genuine dependency** (was: "Lean classical, inherited") | ~~inherited from scaffolding~~ | **NONE in the math; sole footprint occurrence = `band_covers` (Ep92) `omega` tactic artifact, hand-proof axiom-free** |

- A theorem's "axioms" is therefore drawn from `{propext, Quot.sound}` plus,
  *for a minority* (Ep19–26), `eulerLagrangeOracle`. No theorem depends on
  `Classical.choice` (build-confirmed; see the status banner and the retracted
  Choice rule).
- Purely arithmetic theorems over `Nat`/`Int` closed by `rfl`/`decide`/`omega`
  depend on **no axioms at all** (the author records several such, e.g. Ep73).
- **No `Classical.` call appears in any episode body**, and — build-confirmed — no
  decl inherits it either: every `Classical.*` token in the corpus is in a comment,
  and the build carries none into the math. (The one footprint occurrence,
  `band_covers`, is an `omega` tactic artifact, not an inheritance.)

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
- **Choice rule — RETRACTED (build-falsified, fidelity A.12).** This read-derived
  rule predicted `Classical.choice` wherever a proof touched "the chair" `truthLocal`
  or the noncomputable geometric program. The BUILD refutes it: `truthLocal` is
  `[propext, Quot.sound]` (noncomputable ≠ classical; no `Classical.propDecidable`
  survives in the built corpus), and every decl it named — Ep52 `the_stack_produces_it`,
  Ep56 the door, Ep81 the chair, Ep53–55 geometric, Ep57 flux — is
  `[propext, Quot.sound]`, choice-free. There is no choice-taint root. The corpus
  carries no `Classical.choice` except the `band_covers` (Ep92) `omega` artifact.

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

### Ep52 — Pair Production (build: NO choice frontier — corrected)

`electron = -1`, the second-variation residue. Build-corrected (was "CHOICE FRONTIER"):
- **`the_stack_produces_it` is `[propext, Quot.sound]`, choice-FREE** (build). The
  read-derived audit tagged it `Classical.choice` "inherited from the chair
  `truthLocal`"; the build shows the chair itself choice-free (noncomputable, not
  classical), so nothing is inherited. `electronVariation` /
  `electronVariation_normal_form` are noncomputable but likewise choice-free.
- **Clean `[propext, Quot.sound]`** — the production line:
  `electron_charge`, `positron_charge`, `same_pair_charge`,
  `mixedCoupling_needs_the_pair_left/right`,
  `residue_is_the_difference_between_story_and_measurement`, `strain_iff_residue`,
  `electron_strain_is_real`, `electron_strain_iff_charge`, `pair_moved`,
  `linear_story_fails`, `electron_is_the_secondVariation`, `vacuum_is_empty`,
  `certificate_is_C2`, `hilberts_sixth_on_the_vacuum`.

### Ep53 — geometric program detects invariant (build: CLEAN — corrected)

**`[propext, Quot.sound]` on all three, choice-FREE** (build; was "documented CHOICE").
The read-derived "inherits choice from Ep28" is falsified — the geometric side is
noncomputable but choice-free: `GeometricProgram.invariant_zero_detects`,
`threeRungGeometricProgram_invariant_zero_detects`,
`threeRungGeometricProgram_source_is_white_hole`.

### Ep54 — compiled action produces the electron (build: CLEAN — corrected)

**`[propext, Quot.sound]`, choice-FREE** (build; was "documented CHOICE"):
`threeRungCompiler_generates_discriminatingAction`,
`threeRung_vacuum_compiles_to_zero_action`, `compiled_action_produces_the_electron`.

### Ep55 — geometry generates QED program (build: CLEAN — corrected)

**`[propext, Quot.sound]`, choice-FREE** (build; was "documented CHOICE"):
`generatedThreeRungQEDProgram`, `geometric_program_generates_qed_program`.

### Ep56 — pairing door / certificate split (build: CLEAN — corrected)

**`[propext, Quot.sound]`, choice-FREE** (build; was "documented CHOICE — the door =
chair"). The door/chair is noncomputable but choice-free:
`threeRungPairingDoor_dot_zero_left`, `threeRungCertificateSplit_sectors_nontrivial`.

### Ep57 — boundary radiation, finite (build: CLEAN throughout — corrected)

Both groups are `[propext, Quot.sound]`, choice-FREE (build; was "MIXED"):
- the three obstruction theorems: `orthogonal_clifford_scalar_cross_zero`,
  `no_interior_scalar_mixed_of_orthogonal`, `threeRung_no_interior_mixed_certificate`;
- the two flux theorems (read-derived tagged CHOICE via the chair — falsified):
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
arithmetic/Cohen/flat production line are **clean `{propext, Quot.sound}`**. The
read-derived worry that decls routed through the noncomputable generated/geometric
program "may inherit `Classical.choice`" is **void** — A.12 build-verified that root
(chair + geometric program) is itself choice-free. Spot-checks here — Ep64
`finiteGauge_successor_commutator_residue_theorem`, Ep75
`threeRung_boundary_secondVariation_eq_electron`, and the QED capstone (`[propext]`) —
are choice-free. A full per-decl `#print axioms` sweep of Ep60–80 stays the authority
for the remainder.

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

### Ep81 — capstone "the chair" (build: CLEAN — corrected)

**Build `[propext, Quot.sound]`, choice-FREE** (was "Expect the chair —
`[propext, Classical.choice, Quot.sound]`"; the chair is noncomputable, not classical):
`measurementBit_on`, `distinguished_distinguishable`, `binary_is_enough`.

---

## 3. Summary

- **Total axioms in the math: 3** (`propext`, `Quot.sound`, `eulerLagrangeOracle`).
  **No `sorry`.** `Classical.choice` appears in NO math footprint; it surfaces only
  as a `by omega` tactic artifact in `band_covers` (Ep92), which the hand-proof shows
  eliminable (axiom-free `[]`).
- **`eulerLagrangeOracle`** (the one custom axiom): ~20 `*_residue_eq_truth_zero`
  theorems, **Ep19–26 only**.
- **`Classical.choice`** — build-confirmed ABSENT as a genuine dependency. The
  read-derived attributions (the chair Ep52/56/81, the geometric program Ep53–55,
  Ep57 flux) are all `[propext, Quot.sound]` in the build. The corpus is choice-free
  end to end; the sole footprint occurrence is `band_covers` (Ep92), a `by omega`
  tactic artifact (hand-proof axiom-free). Ep1–81 are choice-free.
- **Everything else: `{propext, Quot.sound}`**, with many `Nat`/`Int` theorems
  depending on **no axioms at all**.
- **[choice-root void; sweep partial]:** Ep60–72, 74–80 lacked inline annotations.
  The `Classical.choice` worry for them is void (A.12 verified the chair/geometric
  root is choice-free); spot-checks (Ep64, Ep75, the QED capstone `[propext]`) are
  clean. A full per-decl `#print axioms` sweep remains the authority for the rest.
