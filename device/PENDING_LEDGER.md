# PENDING LEDGER — what device/Measurement demonstrates vs merely builds

## Preamble — the distinction

This corpus **builds**: the whole 93-episode tower typechecks under Lean's kernel. The question this ledger answers is narrower and harder — for each named claim, does the development **demonstrate** it (the named theorem is meaningful and the proof genuinely establishes that meaning) or does it merely **build** it (the term typechecks, but the content is assumed, vacuous, definitional, or much smaller than the name)?

**Bottom line.** There is **no `sorry`** anywhere. There are **exactly four axioms** in the entire closure:

- `propext`, `Quot.sound` — Lean-foundational (ambient); under nearly everything.
- `eulerLagrangeOracle` — **the one custom axiom** (Episode19.lean:109). It is the Decidable instance behind the noncomputable `residue`, so every "the residue collapses to truth-zero / splineSufficient / law_of_spline_sufficiency" theorem **assumes** its headline via this oracle rather than proving it. Reach: ~20 theorems, **Ep19–26 only**.
- `Classical.choice` — ambient classical, **never called directly** (every `Classical.*` token in the corpus is in a comment). It is inherited *structurally* from the noncomputable "chair"/geometric program (root: Ep28 positive-definiteness-by-contradiction, and Ep16/Ep52 `truthLocal`). Reach: specific theorems from **Ep52 onward**.

So the **load-bearing assumption** is the custom `eulerLagrangeOracle`: it is the only non-foundational, non-ambient thing the development takes on faith, and it sits directly under the central "stationarity/Euler–Lagrange detection" storyline.

A theorem can be honest yet narrow: the recurring pattern is **NAME_VS_CONTENT** — grand physics/metamath names (electron, positron, Einstein/Navier–Stokes, Hilbert's sixth, Gödel sentence, Yang–Mills, Cohen forcing) sitting over tiny finite `decide`/`rfl`/`omega` facts. These build and are often correctly proved; they just demonstrate far less than they evoke.

---

## PENDING

### AXIOM_CARRIED — the headline rests on an assumption, not a proof

**The custom oracle (load-bearing) — Ep19–26.** Every theorem terminating in the noncomputable `residue` (whose Decidable instance *is* `eulerLagrangeOracle`):

- `Ep19 totalResidualVanished_residue_eq_truth_zero` — `simp [residue, h]`; the "detection collapses to truth-zero" is assumed via the oracle.
- `Ep19 eulerLagrange_residue_eq_truth_zero` — routes through the above; "EL closes the residue" is oracle-borne.
- `Ep19 stationary_residue_eq_truth_zero` — feeds stationary→EL into the oracle-backed collapse.
- `Ep19 fromAction_closedFlatAt_residue_eq_truth_zero` — flagship "closed-flat ⇒ residue truth-zero"; final equality through the oracle.
- `Ep20 cubicSplineBalanced_residue_eq_truth_zero` / `cubicSplineClosed_residue_eq_truth_zero` — balanced/closed certificates routed into the oracle collapse.
- `Ep20 LanczosCubicSpline.residue_eq_truth_zero` — funnels the certificate into the oracle.
- `Ep20 law_of_spline_sufficiency` — `splineSufficient` is *defined* as `residue = .zero Fact.Truth`; this "law" is exactly the oracle if-branch under a grander name (also NAME_VS_CONTENT).
- `Ep21 OrderedMultisetLanczosTrace.splineSufficient` / `residue_eq_truth_zero` — oracle-backed via `toLanczosCubicSpline`.
- `Ep21 OrderedMultisetLanczosTrace.terminal_residue_for_any_iteration_order` — identical body to `residue_eq_truth_zero`; "any iteration order" is not proved (order-independence never shown), just re-aliased, and stays oracle-borne.
- `Ep22 PartitionedLanczosApproximation.residue_eq_truth_zero` — delegates to the trace's oracle collapse.
- `Ep23 RealizedPartitionedLanczosApproximation.residue_eq_truth_zero` — delegates to the approximation's oracle collapse.
- `Ep25 HeartbeatOrderedMultisetLanczosTrace.residue_eq_truth_zero` — oracle-backed collapse.
- `Ep25 HeartbeatOrderedMultisetLanczosTrace.fastest_heartbeat_order_sufficient` — `splineSufficient` (= oracle) under a name implying the fastest-order *policy* matters; the policy is not load-bearing in the proof, the oracle is.
- `Ep26 ThreeOperationHeartbeatTrace.residue_eq_truth_zero` — oracle collapse via the carried trace.

**The inherited chair — `Classical.choice`, Ep52 onward (never directly invoked).**

- `Ep52 the_stack_produces_it` — the one Ep52 theorem the ledger pins as reporting `[propext, Classical.choice, Quot.sound]`; `rfl` content, choice inherited from `truthLocal`.
- `Ep52 electronVariation` / `electronVariation_normal_form` — noncomputable, seated under the `truthLocal` (Ep16) chair, which is classical (`Classical.propDecidable`); placement defs, load-bearing-noncomputable via the chair.
- `Ep53 GeometricProgram.invariant_zero_detects` / `threeRungGeometricProgram_invariant_zero_detects` / `..._source_is_white_hole` — coercivity content is genuine but rests on the choice-carrying noncomputable kernel/door (Ep28 PD-by-contradiction); "white hole over spacetime" is a constructor label, not GR.
- `Ep55 generatedThreeRungQEDProgram` / `geometric_program_generates_qed_program` — the "generation" carrier; `[propext, Classical.choice, Quot.sound]` via the geometric chair. (NAME_VS_CONTENT too: proves one fixed compiler reads −1 at one boundary.)
- `Ep56 threeRungPairingDoor_dot_zero_left` — `form.zero_left` worn as a door field; closure choice-carried via the noncomputable door.
- `Ep57 generated_boundary_flux_eq_terminal_residual` — `rfl`, but both sides reduce through `generatedThreeRungQEDProgram`; `boundaryFlux`/`terminalResidual` are both *defined* as `electron`, so "the boundary reads the electron" is a definitional identity carrying choice.
- `Ep64 finiteCohen_boundary_radiation_closeout` — load-bearing half is Ep57 `boundary_radiation_finite` (`[propext, Classical.choice, Quot.sound]`); left conjunct is vacuous `(∃ _ledger, True)`.
- `Ep65 threeRungHilbertCompletionArc` / `hilbertCompletionArc_retains_finite_residue` — built on the noncomputable chair-rooted door; "Hilbert completion" is a carried Prop token, residue is re-exported Ep52/55 content.
- `Ep66 finiteResidualMapsIntoCompletion` / `threeRung_completion_maps_finite_residue` — record assembly over the chair; only nonvacuous content is the carried (mixedCubicCoupling = −1) residue.
- `Ep76 DISTINGUISHED_GODEL_SENTENCE` / `Ep77 SECOND_DISTINGUISHED_GODEL_SENTENCE` / `Ep79 FINAL_INFERRED_CLOSE` / `Ep80 inferredCloseInvariant_holds` / `Ep81 measurementBit_on`, `binary_is_enough`, `distinguished_distinguishable` — carry `Classical.choice` structurally through the noncomputable DISTINGUISHED chair. (Most of these are *also* NAME_VS_CONTENT/FORCED, listed below; the choice dependency is inherited scaffolding, not a load-bearing assumption about the physics claimed.)

### FORCED_SUSPECT — a coupling asserted by fiat rather than derived

- `Ep56 threeRungCertificateSplit` — `orthogonal := rfl` because `splitDot` makes **every** cross-sector pair 0 by definition (sum type, no cross-sector addition). The author's own comment admits the representatives are "decorative" and orthogonality is "MADE zero, not proven." The physics name (geometric vs gauge certificate families orthogonal) is asserted by type fiat.
- `Ep61 cohen_cauchy_up_to_epsilon` — bolts the *genuine* Cauchy stage (`completed_residual_isCauchy`) to an existentially-discarded `FiniteCohenUpToEpsilon` ledger `(∃ _ledger, …)` that contributes nothing to the conclusion. The "cohen" factor is inert padding; the joint name asserts a Cohen+Cauchy coupling the proof never couples. Locally builds, globally misleading.
- `Ep81 qed_perp_gr` — `dotH geometric gauge = 0` via `threeRungCertificateSplit.orthogonal := rfl`. Ep56 itself states the orthogonality is "by construction" and the representatives "decorative." The zero is asserted by the def of `dotH` on the split, not a discovered perpendicularity — "QED perpendicular to GR" is coupling-by-fiat.
- `Ep54 threeRungCompiler_generates_discriminatingAction` — *borderline FORCED.* `rfl` that `boundaryReadAction == discriminatingAction` because `boundaryDepth source` evaluates to 1, lining up with the if-tag-then-0-else-1 form. A true `rfl`, but the "GR boundary compiles the gauge action" generation is a definitional coincidence arranged so a constant 1 lines up; the compiler/generation framing far exceeds "the depth happens to be 1."

*(Note: GOALS.md flags one further forced coupling — `TheEchoChamberMazeSolution` → `native_antimatter_is_zero` — but that lives in `device/Experiments/`, outside `device/Measurement/`. The target theorem `Ep85 native_antimatter_is_zero` is itself an honest count.)*

### NAME_VS_CONTENT — honest (often) but vastly smaller than the name

**Particle physics over Kronecker-delta arithmetic (Ep52, 82–88).**
- `Ep52 electron_charge` — "electron = −1" is `decide` over a 4-term sum of 0/1 tag-indicators.
- `Ep52 same_pair_charge` (−2), `positron_charge` (+1) — finite sums; "charge" is a label.
- `Ep52 linear_story_fails` — `decide` that a 4-term integer is nonzero.
- `Ep82 electron_relVel_eq_electron`, `split_cancels` — "matter/antimatter cancel" is a definitional sign flip over two Ints (positron defined as negation by fiat; file admits this).
- `Ep83 no_positron_over_flatPath`, `electron_over_flatPath`, `positron_over_tiltedPath`, `baseline_relative_flip`, `apparatus_resolves_at_most_three` — `decide`/`omega` over a fixed 3-pair event list; the last is the tag<3 pigeonhole on a 3-constructor type, not a physical bound on resolvable electrons.
- `Ep84 holonomy_open_is_trivial`, `holonomy_loop_is_charged`, `detects_positron_over_tilt`, `no_positron_over_flat`, `detection_is_frame_relative` — single hardcoded-pair sign lookups dressed as gauge holonomy / frame-relativity.
- `Ep85 native_antimatter_is_zero`, `native_matter_is_present`, `antimatter_needs_asymmetry`, `the_split_counted` — `decide` tallies over two hand-built event lists; "PREDICTION: native baseline forbids antimatter" is a count over one trial.
- `Ep86 pair_distance_is_one`, `pair_closeness_is_thirtyfive`, `pair_is_not_electron` / `Ep87 pair_cranks_once`, `pair_funges_thirtyfive` / `Ep88 matter_off_the_gauge`, `antimatter_off_the_gauge` / `Ep90 superconducting_pair_admits_one_positron` — popcounts of a `superconductingPair` wired to flip exactly one of 36 gates, so 1 and 35/36 are definitional.

**Analysis / Hilbert / Cohen over finite structures (Ep27, 38, 50–51, 61, 63–64).**
- `Ep27 WeierstrassFiniteElephantTower.residual_tends_zero` / `CompletedWeierstrassFiniteElephantTower.residual_tends_zero` / `BasisApproximationWitness…` — "Weierstrass/B-spline/FFT" labels over the abstract squeeze; no approximation theorem proved (file concedes this), bound→0 is an assumed field.
- `Ep38 natNormSqShadow`, `HilbertCompletionDoor`, `threeRungHilbertDoor` — only inhabitant of `RealScaleField` is `sqrt := id` over `Nat`; `completionAvailable` is a `True` token. Finite Nat-energy norm wearing the Hilbert name.
- `Ep50 skeleton_unconditional_tendsToZero` / `Ep51 frechet_crosses_the_finish_line` — real proofs, but the sequence is *constant zero* (telescoping residual ≡ 0), so `TendsToZero` is trivially met; nothing is being approximated.
- `Ep51 nonzero_residual_fails_eventual_exactness` is genuine (kept under DEMONSTRATED); the "fourth telling / reveal" framing around `cubicSplineResidual_eq_firstVariation` is a one-line def-unfold (kept under VACUOUS).
- `Ep61 splineCondition_cohen_up_to_epsilon` — finite poset of ≤ε-bounded knot/value lists with density for bounded knots; `counting_certificate` is literally Ep60's `succ_certificate_lift`. No genericity, model, or independence.
- `Ep63 splineCondition_conditions_countable` — `NatEnumerable` whose `every_entry_has_code` is the vacuous `x = x` witness; proves only a (non-injective) Nat-valued code exists. Real countability (injectivity) never claimed.
- `Ep64 lanczosSpline_cohen_compliant`, `finiteGauge_successor_commutator_residue`, `finiteCohen_gauge_residue_closeout` — grand Cohen/gauge-commutator names over `(∃ _, True)` padding plus carried Ep52/55 charge facts; no commutator computed.

**Standard Model / cosmology / GR decorations (Ep31, 38–39, 41, 43–44, 54).**
- `Ep31 secondVariation_eq_mixedCubicCoupling`, `secondVariationVanished_iff_mixedCouplingSolved` — `rfl`/tautological renames of the Ep24 mixed-coupling Int as "the second variation / Hessian."
- `Ep39 UniverseKernel`, `threeRungUniverse` — "Universe kernel"/Standard-Model framing over inert enums (Color=3, Flavor=6, QPhase=2) with no group action; fixed tags red/up/plus.
- `Ep41 metaphysical_is_relative`, `groundInvariant_physical` — "physical" means realized by `AllApparatus := fun _ => True`, the unconstrained ceiling the file itself flags as non-physical.
- `Ep43 first_record_in_apparatus_vocabulary` — recasts the first record into apparatus vocabulary, but the metaphysical half is the vacuous empty-class branch (below).
- `Ep44 IsGaugeSolution` — names `coupledCubicDifference = 0` the "discrete gauge / Yang–Mills equation"; the episode's own "what this is NOT" admits no continuum, no mass gap, no SU(N).
- `Ep45 natScale` — sold as escaping `le := True`; order `Nat.le` is real, but `tolerance := fun _ => True`, so the "small/tolerance" half is still the placeholder.
- `Ep54 SpaceTimePath.boundaryDepth`, `threeRung_boundaryCharge_one`, `threeRung_interiorCharge_zero`, `compiled_action_produces_the_electron` — Nat constructor-counts under "charge" names; the last is Ep52's −1 plumbed through a `rfl`.

**Millennium-problem / Gödel capstones (Ep22, 48–49, 75–77, 79–80).**
- `Ep22 spline_represents_supported_data` — "spline represents data" re-reads `terminal_solved_on`; no interpolation proved.
- `Ep48 tag_covering_residual` / `Ep49 skeletonStage_covers_tagReps` — honest, but the content is a 3-element tag-quotient cover, far smaller than the prose's "countably many slips."
- `Ep52 certificate_is_C2`, `hilberts_sixth_on_the_vacuum` — `IsC2Certified` is a 3-clause finite predicate, not classical C²; "Hilbert's sixth problem" certifies a trivial predicate on the zero-cost action — the starkest name gap in the batch.
- `Ep75 threeRung_einstein_field_equations_hold` (`Int.ofNat 1 = Int.ofNat 1` by `decide`), `threeRung_navierStokes_balance` (renamed Ep31 second-variation identity), `threeRung_navierStokes_errorCode` (= Ep52 −1), `einstein_approximation_forces_navierStokes` (their conjunction).
- `Ep76/77 distinguished_navierStokes_errorCode`, `distinguished_godel_sentence_reads_obstruction`, `second_distinguished_godel_sentence_reads_obstruction` — finite obstruction-read receipts under Gödel/physics names; nothing of incompleteness proved.
- `Ep79 inferred_closed_for_the_last_time` / `Ep80 inferredCloseInvariant_holds` — bundles of definitional self-equalities + the same −1 read under a "final inferred close" name.

**Local algebra renamed as physics (Ep82).**
- `Ep82 electron_relVel_eq_electron` (also above) — "the relative velocity IS the electron" names a one-integer identity.

### VACUOUS_TRIVIAL — true, but only because the witness/structure is degenerate

**Carried-field re-exposure (a theorem that returns a structure field it was handed).** `Ep20 LanczosCubicSpline.residual_zero`, `lanczos_equals_cubic_residual`; `Ep21 LanczosStep.selected`, `LanczosStep.identity`, `OrderedMultisetLanczosTrace.terminalResidual_eq_zero(_on)`, `terminalResidual_matches_cubic`, `terminal_residual_for_supported_variations`; `Ep22 weakResidual_eq_zero(_on)`, `trace_knots_sameSupport_elephant`; `Ep23 RealizedPartitionedLanczosApproximation.weakResidual_eq_zero`; `Ep24 left/right_partition_supports_middle_node`; `Ep25 HeartbeatOrderedMultisetLanczosTrace.terminalResidual_eq_zero(_on)` and the forgetful `.toOrderedMultisetLanczosTrace`; `Ep27 ApproximateLanczosTrace.terminalResidual_matches_cubic`, `…_eq_zero_on`, `PointwiseSqueezedResidual.residual_squeezed_between_zero_and_bound`, `ResidualTowerRealizesLanczos.stage_terminalResidual_eq_zero_on`, `residual_matches_terminal_on`, `FiniteElephantTower.contains_refines'`, `CompletedResidualWeierstrassTower.stage_knots_match_elephant`. (Honest engineering glue; assumption re-read, not derived.)

**Degenerate truth/Unit witnesses (everything forced to 0/()/True).** `Ep20 truthTerminalAction_closedFlatAt`, `truthTerminal_residue_eq_truth_zero`; `Ep21 truthTerminalTrace_*`; `Ep22 truthElephantSample_inRange`, `truthPartitionedLanczos_*`; `Ep23 truthRealizedPartitionedFunction_*`; `Ep24 truthCubicPartitionedEulerLagrange`, `truthCubicPartitions_derive_two_middle_equations`; `Ep25 truthFastestHeartbeat_residue_eq_truth_zero`; `Ep26 truthThreeOperation_has_three_operations`, `truthThreeOperationMeasurement_separates_singleton`; `Ep27 truthCompletedWeierstrass_*`, `truthCompletedResidualWeierstrass_pipeline`; `Ep28 truthEnergySq_zero_detector`, `truthGalerkinBilinearForm`, `truthSPDGalerkinActivity`; `Ep29 truthFirstDerivative_energySq_zero_detector`; `Ep30 truthLoadedBoundaryEvaluation`, `truthBoundaryEvaluated_energySq_zero_detector`. The "energy detector / boundary actually evaluates / cathedral" runs on a one-point space with `a = 0` (Ep34's own comment: "cathedral wired to a single point").

**Reflexivity/proof-irrelevance dressed as content (Ep32–33).** `Ep32 coupledZeroByMixed_eq_coupledZeroBySecondVariation` (`Subsingleton.elim`), `proofTiming_equivalent_or_distinguishable` (Nat total-order dichotomy); `Ep33 middle_exists/_unique`, `middle_changed_implies_endpoint_changed`, `endpoints_true_middle_true`, `CompiledMiddle.*`, `timingMiddle_*`, `currentTimingMiddle_*` — `⟨x, rfl⟩` existence/uniqueness and generic congruence-contrapositives in costume.

**Overridden-True class towers (Ep40, 41, 43).** `Ep40 rung3Distinguishable`, `rung3Comparable`, `rung3Inferred`, `rung3Carrier_isNumeric`, `rung3Carrier_isGungan` — fire only because every class predicate was overridden to `True` and every datum is `Fact.Truth` (Ep42 prologue concedes it). `Ep41 even_reading_is_funge_balance` (an iff that is one `rw`), `allApparatus_realizes_every_invariant` (true by construction over `fun _ => True`). `Ep43 anchored_nullMode_metaphysical` — the class is provably *empty*, so "metaphysical" holds vacuously (no-apparatus-exists branch in Ep41 vocabulary).

**Existence/inhabitation wrappers `(∃ _x, True)` and `x = x` codes.** `Ep51 cubicSplineResidual_eq_firstVariation` (def-unfold `rfl`); `Ep52 electron_is_the_secondVariation`, `electron_strain_is_real`; `Ep61 lanczosSpline_cohen_up_to_epsilon`, `merge_of_compatible` (ignores its compatibility hypothesis); `Ep62 splineCondition_order_up_to_extensionality`; `Ep63 SplineAtom.code_witness`, `splineAtomListCode_witness`, `SplineCondition.code_witness`, `finiteCohen_ledger_has_nat_code`, `finiteCohen_countable_up_to_epsilon`; `Ep65 hilbertCompletionArc_setup`, `hilbertCompletionArc_has_completion_token`, `SobolevHilbertDoor.dot_zero_left`, `zeroFiniteCohenPreHilbertSkeleton`; `Ep66 separablePreHilbertSkeletonOfFinite` (`dense := True`), `finiteResidualMapsIntoCompletion_retains_residue`; `Ep74 reciprocalAccounting_truth_parity_surface`, `threeRung_reciprocal_residue_certificate`, `threeRung_preHilbert_reciprocal_energy`, `episode74_reciprocal_accounting_package`.

**Zero-vector / constantly-False continuum lifts (Ep67–72).** The entire Sobolev/Hilbert/Clifford continuum arc: `Ep67 threeRung_boundaryGenerated`; `Ep68 zero_left_sobolev_orthogonal`, `threeRung_sobolev_orthogonal`, `finite_split_orthogonality_lifts` (ignores its `_hfinite` hypothesis); `Ep69 no_continuum_interior_scalar_mixed`, `threeRung_no_continuum_interior_scalar_mixed` (predicate ≡ `False`, so "no mixed certificate" = ¬False); `Ep70 generatedBoundaryTrace_compatible`, `boundaryTrace_agrees_with_terminal_residual` (equality of two `rfl`-equal constants); `Ep71 threeRung_residual_cauchy_in_sobolev_norm` (`cauchyToken := True`, sequence ≡ zero); `Ep72 generalized_boundary_radiation_continuum`, `threeRung_generalized_boundary_radiation_continuum` (¬False ∧ const=const ∧ True). Files admit they install zero-vector lifts and `True` tokens "because no real normed-space library is imported." Also `Ep57 threeRung_no_interior_mixed_certificate` — true because the cross pairing was MADE zero by the Ep56 sum-type, an artifact not a resisted impossibility.

**Definitional Gödel/receipt `rfl`s (Ep76–80).** `Ep76/77/79 *_says_internal_order`, `*_encoded_by_*`, `finalGodelTarget_is_inferred`, `finalGodelSource_is_previous_target`, `truthBinaryToInferredTower_starts/_closes` — a field equals its own definition; the `Closure.le` order is never shown to hold. `Ep78 Fact_FALSE_is_zero_strain_residue`, `Distinguished.falseRead_zero_strain` (discards its hypothesis). `Ep80 requested_depth_projection_receipt`, `how_much_do_you_want_continue_if_new_boundary`, `duh_we_made_binary_how_much_do_you_want` — field extraction from constructed structs.

**Electron-vs-itself reflexivity (Ep86–88, 90).** `Ep86 electron_is_trivial_distance`, `electron_reads_electron`; `Ep87 electron_never_cranks`, `electron_is_all_funge`; `Ep88 native_pure_matter_off_the_gauge`; `Ep90 native_pair_pure_matter` — Hamming distance / crank count of the all-true vector against itself is 0, or its funge count equals the list length, by construction.

**Other.** `Ep19 residualVanished_iff_eulerLagrange` (`Iff.rfl`, def-unfold); `Ep21 SlipMultiset.sameSupport_refl/_of_eq`; `Ep24 partitions_and_mixed_derive_coupledSolved` (premise "∀ variation, in the finite candidate list" is effectively unsatisfiable for a finite multiset); `Ep28 diagonal_zero_detects_of_positive_definite` ("positive_definite" in the name does no work); `Ep41 even_reading_is_funge_balance`; `Ep46` (no theorem — `#eval`/`#print axioms` audit only); `Ep48 telescoping_covering_route` (showcase wrapper, docstring admits it adds nothing); `Ep50 skeleton_discharge_via_exhaustion` (own docstring: pigeonhole route "not load-bearing"); `Ep60 successorNumber_eq_zero_succ_succ`, `succ_succ`, `one_add_one_eq_two`, `one_add_two_eq_three`, `one_add_one_add_one_eq_three` (def-unfold `rfl`, author concedes "definitional"); `Ep89` (only anonymous `example`s, no named theorem); `Ep93 youTheReader_asked` and `did_this_*?` (four `def … : Prop` — class-method conjunctions asserted but never proved; the heavy reader tower demonstrates nothing).

---

## DEMONSTRATED (genuine) — the clean core, characterized by range

The honest, non-vacuous, correctly-named, mostly axiom-free results cluster as follows. (Trivial-but-honest arithmetic/projection lemmas — conjunct extractions, `rfl` identities whose names match exactly, numeral facts over the custom `Natural` — are not individually listed; they are real but minor.)

- **Ep1–14 — no claims.** Pure type tower: order-relation `def`s and `.default` instance-builders. No theorem, axiom, `sorry`, or choice. Nothing to demonstrate or doubt; this is the scaffolding Ep16+ sits on.
- **Ep17–18 — the gauge-variation core.** `FiniteGaugeAction` flatness→stationarity implications and the Fréchet-remainder algebra (`firstVariation_eq_composedDifference`, `fromAction_remainder_zero`, `fromAction_stationaryAt_of_flatAt`). Clean, generic, `omega`/`simp`-closed, axiom-free. The genuine analytic spine the later episodes lean on.
- **Ep19 (predicate layer), 24–26 — finite discrete-variational mathematics.** The discrete Euler–Lagrange ⇔ stationarity equivalence (`stationary_iff_eulerLagrange`, `Eq.trans` over a decomposition), the cubic finite-difference identities and the honest left+right+mixed coupling decomposition (`coupledCubicDifference_eq_left_right_plus_mixed`, mixed term kept explicit), heartbeat-minimal existence and local separation/uniqueness including a real 3-element EKG case-bash with distinct heartbeat totals. The substantive combinatorial/arithmetic content of the spline tower (everything *except* the oracle-backed `residue` collapses).
- **Ep27 — the squeeze theorem.** `ApproximationScale.tendsToZero_mono` and its transports (`PointwiseSqueezedResidual.residual_tends_zero`, the `CompletedResidualWeierstrassTower` squeeze chain). Real, abstract, axiom-free. (Convergence rests on assumed bound→0 *fields*, and "Weierstrass" decorates them — but the bounding step actually invoked is proved.)
- **Ep28–30 (generic plumbing) + 34–36 — the SPD/coercivity core.** The abstract bilinear-form algebra and certificate conversions are real plumbing (though every *exhibited model* there is the Unit `a=0` toy). The genuine finite-dimensional content lands in Ep34–36: the real `K = M+S` and anchored `K = S` Int forms, honest coercivity (`Rung3.aMS_pd`, `AnchoredRung.stiff_pd`), the non-triviality certificate (`threeRung_energy_nontrivial = 2`), and the discrete-Poincaré theorem `chain_poincare` (induction over chain length). This is where scaffolding becomes non-vacuous mathematics.
- **Ep37, 41–42, 44–45 — operator-substitution, parity, the first real record.** Operator-substitution energy collapses (conditional on a supplied matching certificate, honestly so); the parity obstruction (`odd_is_obstructed`, `funges_and_cranks_partition`); **Ep42's first record** — a genuine present/absent boundary sourced from proven coercivity (`anchored_has_no_null_mode` + `unanchored_has_null_mode`), the strongest result in its range; the Ep44 integrator runs (`concrete_runs` reads 0 and 2 by `decide`, `reading_is_EL_plus_coupling` a real Int identity); and `eventuallyZero_tendsToZero` plus `tower_terminalResidual_tendsToZero` (conditionality stated).
- **Ep47–51 — the pigeonhole/enumeration arc and finite Fréchet/Taylor algebra.** `iterOne_injective`, `finite_entries_miss_a_slip`, `no_uniform_support`, `ratSlips_complete`, `skeletonTower_exhausts`; the Fréchet existence/uniqueness and `taylor_terminates_at_order_two`, `nonzero_residual_fails_eventual_exactness`. Real `omega`/`decide`/induction. Ep50's `skeletonCompleted` honestly converts an assumed bound→0 into a proof (the convergence then trivializes only because the residual is structurally zero — flagged above).
- **Ep52 (algebra half), 56–60 — the analytic spine and finite combinatorics.** `residue_is_the_difference_between_story_and_measurement`, `strain_iff_residue` (real Int equivalences); `threeRungCertificateSplit_sectors_nontrivial` (`decide`: 2 and 1); the two general Clifford-shadow obstruction lemmas (`orthogonal_clifford_scalar_cross_zero`, `no_interior_scalar_mixed_of_orthogonal`); the flat-tower delegations (`flat_residual_zero`, `flatPair_unconditional_tendsToZero`, `flatPairCompleted_exists`) with satisfiable hypotheses; **`completed_residual_isCauchy`** (Ep59) — the standout, a genuine axiom-free Cauchy proof by a double squeeze; the `Natural` induction principles (`canonical_ofNat`, `induction_on_canonical`).
- **Ep61–62, 64–66 (coding) — finite-Cohen density and order lemmas.** `dense_decides_knot`, `dense_decides_finite_requests`, the extensional partial-order record (`splineCondition_extensional_order`), `separableSkeleton_condition_coded`, and the genuinely-proved bundle components of `splineCondition_finiteCohenCompliant` / `finiteGauge_successor_commutator_residue_theorem` (which honestly projects the real mixedCubicCoupling = −1 and `IsC2Certified` facts). Honest finite combinatorics under set-theory/gauge branding.
- **Ep73, 78, 80 — EKG uniqueness and small constructive logic.** `dominant_unique` (case-split + `omega`) and the concrete `decide` electron/positron counts; `BoundarySignal.on_ne_off`, `Distinguished.true_neq_false` (real finite separation); constructive De Morgan over props and the 2×2 Boolean carrier, and the `[Decidable P]`-gated `¬(P∧Q)` that deliberately avoids choice; the `liftSignal` case lemmas.
- **Ep82–83, 87–88, 90–92 — coupling bridges, tag pigeonhole, finite partitions.** `routes_same_invariant`, `pairRelVel_eq_secondVariation` (the Ep31-coupling bridges); the located `Quot.sound` collapses (`relvel_routes_agree`, `electron_routes_agree` — ambient `Quot.sound` only, not the custom oracle or choice); `four_tags_collide`; the finite gate partitions (35 + 1 = 36); the abstract strict-order lemmas (Ep91); and `band_covers` (Ep92 Nat trichotomy).

---

## Coverage caveat

This is a **static read of the source**, not a `#print axioms` run on each declaration. The axiom attributions for the chair-inherited `Classical.choice` items (Ep52–81) lean on `device/AXIOM_LEDGER.md`'s annotations plus the corpus's own inline `#print axioms` expectations rather than fresh kernel output, and the ledger itself flags **Ep60–72, 74–80 as `[PENDING BUILD]` — lacking inline expected-axiom annotations**. Confidence is therefore **lower** specifically on:

- *Exactly which* Ep52+ theorems carry `Classical.choice` vs. close clean `[propext, Quot.sound]`. The chair-inheritance is structural, so the boundary between "carries choice" and "doesn't" within a file is the most likely place a static read is off. (Ep50 already recorded that the earlier expectation of `rung3Inferred` carrying choice was **stale** — it built `[propext, Quot.sound]` — which is precisely the kind of drift only a real audit catches.)
- The Ep64–72 continuum arc, where "vacuous" vs. "axiom-carried" depends on whether a given field reduces through `generatedThreeRungQEDProgram`/the noncomputable door; assigned by structural reasoning, not verified per-decl.

What is **high-confidence** and source-verified: no `sorry`; exactly four axioms; `eulerLagrangeOracle` declared at Episode19.lean:109, reaching only Ep19–26; `decide` (not `native_decide`, which would add `ofReduceBool`); and that every `Classical.*` token in episode bodies is in a comment, so choice is inherited, never directly invoked.