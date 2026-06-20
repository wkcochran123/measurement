# Feedback v2 on `device/Experiments/*/Experiment{1,2,3}.lean`

Re-review after the suite grew from 136 files to **408** (Experiment1/2/3 per effect). Method: full grep over all 408 files for the systemic claims, a per-effect tag-vs-`description.md` audit across **all 136** effects, an adversarial verification pass on every flagged mis-tag, and a harness/design analysis of `Common/Basic.lean`. Supersedes `FEEDBACK.md` (v1); v1's structure is still the baseline this checks against.

## 0. Net verdict

v2 took the v1 review seriously **in spirit** and added one genuinely valuable artifact, but did not fix the core problem. The single best thing v2 did: it now **machine-proves its own central weakness** — `exported_claim_is_constant` certifies in Lean that the exported claim discards its `Setup`. That is honest. But it **documents** the v1 vacuity instead of **removing** it.

**The two issues that mattered most in v1 are both still open**, and both fixes are small and mechanically unblocked:
1. **0 of 408 files import the real device.** The suite still tests a 3-`Nat` toy harness, never `Measurement.lean`.
2. **The tag is still a sticker, not a fence.** v2 stapled a *second* author-chosen sticker (`modelKind`) next to the first (`tag`) and checked them against each other — neither is tied to what the file actually proves.

Net: **3× the files, ≈1.05× the proved content**, plus one honest disclosure. Still clean (0 `sorry`/`admit`/`native_decide`/`axiom` across all 408). `CompactDiscEncoding` remains the one correct template.

## 1. What genuinely improved since v1 (credit where due)

- **Self-disclosure of the defect.** `exported_claim_is_constant (left right) : experiment.claim left = experiment.claim right := by rfl` (`CompactDiscEncoding/Experiment2.lean:49`) certifies the exported claim ignores its input. Proving your own critique beats hiding it.
- **Uniform audit discipline across all 136.** Experiment2 adds the same three things everywhere: a tag↔modelKind consistency check, a `(setup)`-quantified lemma *shape*, and the constant-claim disclosure. Uniformity means a real fix can be templated once and propagated.
- **Still no proof debt.** 0 `sorry`/`admit`/`native_decide`/`axiom` re-confirmed across 408 files.
- **Chaitin's v1 over-claim was removed** and the `allowsModelKind` table (`Basic.lean:130-139`) gives a principled vocabulary of claim ceilings — the scaffolding for a real fence now exists, just unwired.

## 2. What is still broken (with the receipts)

- **#1 from v1 — 0/408 import `Measurement.*`.** Re-confirmed by grep. The suite tests `CountSetup` (3 Nats), never the device. Mechanically trivial to start: `Measurement.lean` already imports `Episode81/82/83`, and `lakefile.toml` builds the `Experiments` lib with `srcDir='.'` alongside `Measurement` — so `import Measurement.Episode81` from an Experiment resolves with **no build-graph change**.
- **Tag ≠ fence.** `claimStatement output := ModelKind.holds modelKind output` uses the **author's** `modelKind`; `tag_allows_modelKind` only checks `allowsModelKind tag modelKind` (label-vs-label). **Verified:** retagging `TheHeisenbergEffect` from `finiteLedgerModel` to `standardMathlibTheorem` still compiles, because the table admits `(standardMathlibTheorem, preserves)`. A wrong-but-table-consistent tag passes.
- **`claim_holds := by decide` on frozen literals (136/136).** Never universal. The `blocks`/`inadmissibilityNoGo` "no-go" tier proves a single favorable triple, not `∀ s, P s → ¬ holds` — the weakest possible form of a no-go.
- **The Exp2 "quantified" lemma is gutted in 123 of 136 effects.** It takes the only substantive inequality as a *hypothesis* and closes with `And.intro … rfl` (e.g. `CompactDiscEncoding/Experiment2.lean:31-35` assumes `coarseCount <= fineCount` then returns it). It quantifies over `setup` but proves nothing about `run`; it cannot fail.
- **27/136 files prove literally `True`** (`physicalClaimLabelOnly` + `ModelKind.holds labelsOnly _ = True`, `Basic.lean:173`).
- **Exp3 buys ≈nothing.** `longPath := auditedExperiment.run defaultSetup` is definitionally `shortPath` (`auditedExperiment := experiment`), so every `_agree` theorem is `rfl` over one shared definition. No second independent path → detects no drift.
- **Advertised-but-dead modeling vocabulary.** `Holonomy`, `Projection/sameShadow`, `Boundary/compatible`, `Channel`, `Refinement/pushLedger`, `CausalOrder`, `Ledger.append/map/empty`, `count_append/count_map/count_empty`, `Counting.boundedBy*` — **0 uses across 408 files.** `standardMathlibTheorem` — **0 uses** (dead 5th tag). The harness implies far more is modeled than the 3-`Nat` reality delivers.

## 3. Tag-honesty audit — the new finding (17/136 tag-polarity issues)

Tag distribution: `finiteLedgerModel` 70 · `physicalClaimLabelOnly` 27 · `smoothShadowAnalogy` 26 · `inadmissibilityNoGo` 13 · `standardMathlibTheorem` 0.

A per-effect audit of all 136 tags against their `description.md` found **17 effects where the tag's proposition has different (often opposite) truth conditions than the phenomenon described.** An adversarial verifier (instructed to defend the status quo and default to "defensible") hard-confirmed **2**; the rest are real but judgment-call-severity given the deliberately coarse 5-tag vocabulary. They cluster into five patterns — the first is the serious one (the encoded claim is the logical *negation* of the source):

**A. Impossibility encoded as success** (no-go → `finiteLedgerModel`/`preserves`/`transports`, which asserts the thing *succeeds*):
- **`TheAndersonEffect`** ✅confirmed — source says "no admissible global extension exists"; encoded as `preserves` (`required ≤ accessible`, i.e. extension *succeeds*). Exact negation. Sibling no-gos `TheHaltEffect`/`TheLimitationOfIndexing` already use the right shape (`blocks`/`inadmissibilityNoGo`).
- **`TheHallEinsteinPodolskyRosenEffect`** ✅confirmed — Bell/EPR + Monty-Hall *non-existence of a joint event* encoded as a `preserves` success.
- `TheSchrodingerYoungEffect`, `TheJupyterEffect` ("it halts"), `TheQuicksandEffect` ("fails to generate a new event"), `SpookyActionAtADistance` (order-independence ≠ count inequality), `TheAmdahlEffect` (`S_max=1/(1−p)` no-go tagged benign).

**B. Undecidability/uncomputability flattened to a finite decidable count:**
- `TheCantorGodelCohenEffect` (CH independence → `2 ≤ 3 by decide`), `TheParetoEffect` (Kolmogorov incompressibility, uncomputable → finite count).

**C. A real stated bound softened to a do-nothing label** (`physicalClaimLabelOnly`, proves `True`):
- `TheChaitinEffect` — **over-corrected from v1**: it *was* over-claiming (`inadmissibilityNoGo`); the retag to `physicalClaimLabelOnly` now *under*-claims, softening the strongest uncomputability result to a label. `TheTHooftSusskindEffect` — a holographic bound `N(Ω) ≤ f(|∂|)` softened to `True` when an inequality was available.

**D. Continuum/smooth analogy tagged `finiteLedgerModel`** (should be `smoothShadowAnalogy`):
- `TheInverseSquareEffect` (its own description: "the smooth shadow of the combinatorial growth … " + `4πr²`), `TheGibbsPreservationEffect` (Fourier/continuum-completion overshoot).

**E. Other:** `TheStoichiometryEffect` (integer-program solvability = a standard decidable theorem → should be `standardMathlibTheorem`, the dead tag); `TheLimitationOfIndexing` (monotonicity `ΔS ≥ 0` mis-modeled as a `blocks` no-go); `TheVonNeumannTrefethenEffect` (statistical survivorship mislabeled as a crisp finite no-go).

This pattern is exactly why recommendation #2 matters: today the polarity of `claimStatement` is the *author's* free choice (`modelKind`), so an impossibility and a success are equally easy to "prove green."

## 4. Prioritized recommendations

**1 — Couple at least one test to the real device.** From one `Experiment1`, `import Measurement.Episode83` and prove `claim_holds : claim.statement := by exact Measurement.Episode83.<provedLemma>`, choosing an effect whose `description.md` matches what the Episode formalizes (e.g. charge-sign / baseline-relative matter for Ep83). Now a `sorry`/regression in the Episode breaks *this* file's build. Minimum that converts a green light into real regression coverage; the lib already builds alongside `Measurement`, so no build-graph change.

**2 — Make the tag derive the obligation (turn the sticker into a fence).** Add `def ClaimTag.requiredModelKind : ClaimTag → ModelKind` to `Common/Basic.lean` (finiteLedgerModel⇒preserves, inadmissibilityNoGo⇒blocks, physicalClaimLabelOnly⇒labelsOnly, smoothShadowAnalogy⇒projects, standardMathlibTheorem⇒preserves). Redefine each file's `claimStatement` as `ModelKind.holds (ClaimTag.requiredModelKind claim.tag) output` — **tag-derived, not the author's `modelKind`.** Then flipping a `blocks` no-go to `preserves`, or the Anderson/HEPR inversions in §3, becomes a **compile error**: the inequality `claim_holds := by decide` must satisfy changes with the tag. One `Basic.lean` def + a one-line edit per file.

**3 — Replace the frozen-literal `by decide` with a `(setup)`-quantified obligation that can fail.** `theorem claim_holds : ∀ s, P s → ModelKind.holds (requiredModelKind claim.tag) (run s)`. For the `blocks`/`inadmissibilityNoGo` tier prove a **universal** impossibility `∀ s, P s → ¬ holds`, not one favorable triple.

**4 — Un-gut the quantified lemma (123/136 are circular) and wire in the one real lemma.** Make `claimStatement_holds_when_…` **prove** its inequality from `run`'s definition instead of assuming it. In CDE, replace `mergedLedger := setup.fineLedger` (`Experiment1.lean:76`) with a real `Refinement.pushLedger` reconciliation so `coarseCount ≤ fineCount` is a theorem, and reference `Reader.belowThresholdInvisible` (`Experiment1.lean:32`, the suite's *one* genuinely falsifiable lemma) inside `claim` so it stops being orphaned.

**5 — Fix the 17 tag-polarity issues from §3.** Apply the §A inversions first (Anderson, HEPR → `inadmissibilityNoGo`/`blocks`); retag the §D continuum cases to `smoothShadowAnalogy`; give §C its real inequality back; use the dead `standardMathlibTheorem` tag for `TheStoichiometryEffect`. After #2 lands these become enforceable rather than convention.

**6 — Resolve the dead-vocabulary mismatch.** Either **wire in** `Common/Basic.lean`'s structures per the family table (below), or **prune** them plus the dead `standardMathlibTheorem` tag and the unused `Ledger`/`Counting` API. Shipping them unused oversells the harness.

**7 — Replace or delete Exp3.** The "long path" is the short path wearing a wrapper (every `_agree` is `rfl`). Either compute the long path *independently* (a second route, proven equal — then it can detect drift) or delete it; a funge over one shared definition triples the file count for nothing.

## 5. Domain-modeling examples (copy `CompactDiscEncoding`'s shape: effect type + falsifiable lemma + content-bearing claim)

- **Conservation of Energy / Gauss / Maxwell's Demon** → `Ledger.count_append : (append l r).count = l.count + r.count` as the continuity law "what leaves here = what enters there" (currently `TheConservationOfEnergy` is a `labelsOnly` file proving `True` while its exact conservation lemma sits unused).
- **Aharonov–Bohm / Yang–Mills / Sagnac / MinimizingVariations** → `Holonomy`: `residue (transportAround …) ≠ 0` while a local `Projection.sameShadow` agrees (nonzero loop residue, locally-trivial shadow). For stationarity, residue `= 0`.
- **Bell–Aspect / Entanglement / HEPR / Hawking horizon** → `Boundary.compatible` (`restrict left = restrict right`) as the shared-boundary constraint two ledgers must agree on; the no-go is its *failure*.
- **Shadow Tomography / Butterfly / Gibbs / Precision / CD** → `Projection.sameShadow` + `Refinement.pushLedger`: two states with equal shadow but a refinement that distinguishes them.
- **LiDAR / time-dilation effects** → two `Ledger`s with a `Ledger.count` comparison ("A's notebook has more events than B's"), not 3 undifferentiated Nats.
- **Heisenberg-as-tradeoff** → `ModelKind.blocks` proven **universally**: `∀ s, P s → accessible < required`.

---
**One line:** v2 is honest about its vacuity (it now machine-proves the exported claim ignores its input) but did not remove it — 0/408 tests touch the real device, the tag still doesn't bound proved content, 123/136 "quantified" lemmas assume their conclusion, and 17/136 tags encode a different (sometimes opposite) proposition than described — and the two fixes that matter (couple one test to `Measurement`, make the tag *derive* the obligation) are both small and unblocked.
