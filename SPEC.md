# SPEC — The Measurement Instrument: a Repeatable Calibration Verifier and its Four Gauges

*Master spec, acting operator, 2026-07-09. This is the single mandate. **Clear the decks:** all prior task work
(Vol 2 codas, the fidelity lane, the old abstract vol1-alpha turns) is SUPERSEDED. Kodo and Podo start fresh
from this document. Governed by `SACRED_TEXTS.md` (the constitution) and detailed by the supporting docs in §9.
Grade off the build.*

---

## 1. The thesis (one breath)
The device is a **highly repeatable experiment** — deterministic computation, so every run returns the identical
reading bit-for-bit, against a frozen standard. Its **final API is a calibration verifier**:
`verify(claimed) → { verified?, residual }`. But **a reading is meaningless without gauges to read it by.** A
number with no gauge is noise. So the deliverable is the instrument **and its four gauges** — and the four gauges
are **four books.** Instrument + gauges = the product. That is the whole project.

## 2. The instrument (the API — the product surface)
- **`verify(claimed_calibration) → { verified?, residual : above/below floor }`.** Input a claimed calibration
  (the device's α, a user's claimed cost, anyone's number); run the repeatable experiment; return verified +
  the residual, everything below the floor cut into antimatter (unclaimable).
- **Engine, already built:** `Calibration.EKG.outgrown?` (LeanCalibration) — reading vs `reference +
  measuredFloor` → verified-or-not, floored at `TRUE=TRUE` (`Fact.Truth.decTruth`). `verify` is the clean wrapper.
- **Repeatability is the honesty.** A crank result isn't repeatable by others; a real calibration is. The user
  doesn't trust our claim — they re-run and verify. This is the preface's "builds a machine and asks you to
  check it" made runnable; the API is the checking, the witness verifies.
- **Repeatability scope (honest):** EXACT per Lean-version/setup (deterministic); calibration-stable across
  setups (self-reference to the `TRUE=TRUE` floor + ratio-read carry the invariance the absolute count can't).
- **α is the flagship INSTANCE of the API, not the API.** The fold probe is one calibration `verify` checks.

## 3. The four gauges (the four books — necessary to understand the reading)
Three registers that share **no vocabulary** (a null basis — agreement across them can't be a shared-word
artifact) + the code itself. Vols 1–3 define and use `tange`/`funge`; Vol 4 drops the words and carries the
distinction as **citation texture** (cited-generously = funge/standard; uncited = tange/novel = pay attention).

| Gauge | Book | Register | Rule |
|---|---|---|---|
| 1 — Mathematical | **Vol 1 · Measurement** | the math explanation | construction from the first difference; **defines** tange/funge (math-without-math); names the electron; the α apex |
| 2 — Physical | **Vol 2 · Experimentation** | physics without computation | the experiments, the constants, the courtroom; physics as physics |
| 3 — Computational | **Vol 3 · The Compiler** | computation without physics | the self-hosting compiler; the code as pure computation |
| 4 — The Reading | **Vol 4 · Scientific Computation** | the code walk + all three unified | **no** tange/funge (citation texture instead); maximally generous citation; the user guide to the instrument |

The gauges convert a reading into understanding. Ship the instrument without them and you've shipped a number
nobody can interpret.

## 4. The technical pipeline (the fresh build — strict order)
- **PHASE 0a — TRIM to the above-floor core.** You can't register a command below the antimatter floor; below-floor
  code is an aliasing mode = the resonance source. QUARANTINE (not delete) below-floor decls to
  `device/Measurement/attic/` (= the codebase's antimatter budget); the **effort-sort of the above-floor core lays
  the zero and the naturals.** 16+ ONLY. Restore-point branch first; **INVENTORY first, acting operator reviews
  before any cut.** Criterion: ABOVE = builds AND registers a real distinction (computes / proves / used
  downstream); BELOW = sketched / stub / promissory / dead. (Charter `bm-trim-to-floor`.) Test for free: residual
  survives the trim = REAL; vanishes = it was sub-floor noise faking convergence.
- **PHASE 0b — THE CONNECTION THEOREM (closes the bridge to ℕ).** Prove `Formalization.Cost.rank ≡ EKG
  heartbeat / 1000, above the floor` — welds the structural ℕ (rank; `Step.rank_succ` + `derivation_cost_eq_rank`
  are ~90% there) to the physical, boot-calibrated effort (LeanCalibration's gauge map already defines the ×1000).
  Cost.lean itself flags this theorem as owed. **In MY territory (Formalization reads LeanCalibration); NO gate.**
  Grounds the ratio as a genuine ratio of naturals.
- **PHASE 0c — THE FOLD PROBE (α = the flagship reading).** `step : Number → Number` = `spin` (Number→Bullshit,
  Meanwhile18) then read back = one baker/(−i)² fold = one connection application. Calibrate on `TRUE=TRUE`
  (already done at boot — READ it, don't rebuild). Run under `withHeartbeats`; truncate at ε; sub-floor tail →
  antimatter. Search up the universe levels; report α / antimatter / ε per level. (Design: `alpha_fold_probe_design.md`.)
- **PHASE 1 — THE `verify` API.** Wrap `outgrown?` as `verify(claimed) → { verified?, residual }`. α becomes the
  first calibration the API verifies. This is the product surface.
- **PHASE 2 — THE FOUR GAUGES.** Write / re-aim the four books as the four gauges of the reading. Vol 4 is new
  (the reading gauge, `scientific_computation/vol4_spec.md`); Vols 1–3 re-aimed as the math / physics / computation
  gauges around the α reading they interpret.

## 5. The fences (honesty — non-negotiable, all required)
- **Predicted, not fit.** Fix the gauge before the reading; fishing the codebase for a ratio near 137 is the
  cardinal sin. Frozen target α⁻¹ = 137.035999206 (NOT 137).
- **Blind.** Calibrate on `TRUE=TRUE` first; read α as a difference from the blank; target out of the fold defn.
- **Two-sided floor.** UPPER: **`OUTPUT ≤ Bullshit` is the device's NATIVE output**, not an imposed check —
  `outgrown?` returns exactly its truth, so `verify` *exposes* the device's own boundedness rather than bolting a
  fence on. The device cannot emit an unbounded claim: its output is either `OUTPUT ≤ Bullshit` (verified, under
  budget) or `outgrown` (the fit-signal fired — log the budget you'd have had to grant). The honesty is in the
  output TYPE (the sayable bounded by the showable — the funge output capped by the tange corridor above it), not
  in a discipline we promise. LOWER: truncate at ε; tail → antimatter; `antimatter ≤ ε` (excess = hiding an
  above-floor discrepancy). Keep OUTPUT (the reading) and Bullshit (the budget/corridor) SEPARATE (Cost.lean mandate).
- **ρ ≈ ½ lockstep with ε.** Residual must halve WITH the floor; slower = missing connection, faster = over-read.
- **Pre-registration + full run-log.** Every gauge variant + reading, in order — not the flattering run.
- **Grade off the build.** No prose claims a number until a Lean `#eval`/theorem carries it. Two honest landings
  (FULL / STRUCTURAL); a STRUCTURAL / push-back reading honestly logged IS a real result. The number is unknown
  until read.

## 6. The boundaries (sacred + gate)
- **Episodes 1–15 = SACRED, frozen, read-only** (`SACRED_TEXTS.md`). Own 16+. Renaming a sacred name = a **2+ day
  recompile** — hoard and batch. **The first time any work needs to change a sacred text, STOP and escalate to the
  operator for review.** Kodo's gate rejects/HOLDs any sacred-editing turn.
- **`Calibration/LeanCalibration.lean` = sacred-in-spirit** (the frozen calibration standard, upstream). READ it;
  do not touch it. `Calibration/EKGBounded.lean` is a downstream tool (mine).
- **Builds:** TARGET build only, never bare `lake` (QPhase two-root clash); do not touch the uncommitted
  `Measurement.lean`.

## 7. Roles + sequence
- **Kodo gates** each step against §5 and the grade table; **Podo builds** in 16+ and writes the gauges.
- **Acting operator (me)** owns the trim criterion, reviews the inventory before any cut, adjudicates the reading,
  and holds the sacred gate.
- **Sequence:** 0a trim → 0b connection theorem → 0c fold probe → 1 verify API → 2 the four gauges. Each phase
  gates the next; the number is only read after the core is clean and the bridge is closed.

## 8. The grade discipline
Grade off `#print`, never the frame. Every claim is one of: **BUILT** (carried by the build), **CONJECTURE the
probe TESTS** (fold = connection = holonomy; deficit = α; measure-preserving + hyperbolic), or **DESIGN
CONVENTION** (antimatter ≤ ε; blank calibration; the four-gauge mapping). The four gauges are the FRAME until the
build carries them — written as the interpretation of what the build DOES, never as theorems wearing prose.

## 9. Supporting docs (detail under this master)
- `SACRED_TEXTS.md` — the constitution (the boundary + the gate).
- `books/expository_monograph/alpha_target_and_acceptance.md` — the frozen target + non-crank bar.
- `books/expository_monograph/alpha_fold_probe_design.md` — the fold probe + the verify API + the four explanations.
- `books/scientific_computation/vol4_spec.md` — Vol 4 = the reading gauge (no words, citation texture).
