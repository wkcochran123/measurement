# TASK instrument — THE MASTER SPEC (SPEC.md, bm-master-spec ACKED 2026-07-09)

**Supersedes ALL prior task work** (vol2-coda, vol2-fidelity, vol1, the abstract vol1-alpha turns). Single
mandate: `SPEC.md` at repo root. Governed by `SACRED_TEXTS.md` (constitution). Grade off the build.

**Roles:** Kodo (claude) gates each step vs §5 fences + the grade table AND decides every non-sacred cut/repair/
fork; Podo (codex) builds in 16+ / writes the gauges. ⚑ **Operator DELEGATED all non-sacred decisions
(2026-07-09, [[find-your-own-gradient]]): only a real Ep1-15/LeanCalibration edit STOPS for the operator; I am
the acting reviewer for everything else** (the beastmaster's "operator reviews the inventory before any cut" is
SUPERSEDED). RYOT loop, single monotonic turn counter (…73 p→k, **74 VOID**, 75 k→p, …).

## The thesis
The device is a highly-repeatable experiment (deterministic → identical reading bit-for-bit vs a frozen
standard). Final API = a **calibration verifier**: `verify(claimed) → { verified?, residual : above/below floor }`.
A reading is meaningless without gauges → deliverable = the instrument **+ its four gauges (four books)**. α is
the **flagship INSTANCE** the API verifies, not the API. "Builds a machine and asks you to check it," runnable —
the user re-runs and verifies rather than trusting.

## The four gauges (null basis — share no vocabulary; agreement = anti-crank)
- Vol 1 · Measurement — Mathematical gauge (math-without-math; DEFINES tange/funge; names the electron; α apex).
- Vol 2 · Experimentation — Physical gauge (physics without computation).
- Vol 3 · The Compiler — Computational gauge (computation without physics; self-hosting).
- Vol 4 · Scientific Computation — The Reading gauge (NO tange/funge — citation texture: cited=funge/standard,
  uncited=tange/novel; the user guide). NEW (`books/scientific_computation/vol4_spec.md`).

## Pipeline (strict order; each phase gates the next)
- **0a TRIM to above-floor core** — quarantine (NOT delete) below-floor decls to `device/Measurement/attic/`
  (= the codebase's antimatter budget). INVENTORY FIRST → operator reviews BEFORE any cut. Restore-point branch
  first. 16+ ONLY. ABOVE = builds AND registers a real distinction (computes/proves/used-downstream); BELOW =
  sketched/stub/promissory/dead. Free test: residual survives trim = REAL; vanishes = sub-floor noise faking
  convergence. (bm-trim-to-floor.) Then add back adiabatically, one above-floor rung at a time.
- **0b CONNECTION THEOREM** — prove `Formalization.Cost.rank ≡ EKG heartbeat / 1000, above the floor` (welds
  structural ℕ rank to physical boot-calibrated effort; Step.rank_succ + derivation_cost_eq_rank ~90% there;
  LeanCalibration gauge map defines ×1000). Operator territory, NO gate. Grounds the ratio as a ratio of naturals.
- **0c FOLD PROBE (α = flagship reading)** — `step:Number→Number` = spin (Number→Bullshit, Meanwhile18) then read
  back = one baker/(−i)² fold = one connection application. Calibrate on TRUE=TRUE (done at boot — READ, don't
  rebuild). withHeartbeats; truncate at ε; sub-floor tail→antimatter; search up universe levels; report
  α/antimatter/ε per level. (Design: `books/expository_monograph/alpha_fold_probe_design.md`.)
- **1 verify API** — wrap `Calibration.EKG.outgrown?` as `verify(claimed)→{verified?,residual}`. α = first
  calibration verified. Product surface.
- **2 THE FOUR GAUGES** — write/re-aim the four books around the α reading.

## Fences (§5, all required; I gate against these)
Predicted-not-fit (fix gauge before reading; fishing for ~137 = cardinal sin; target α⁻¹=137.035999206 NOT 137).
Blind (TRUE=TRUE first; α = difference from the blank; target out of the fold defn). Two-sided floor: UPPER
`Number ≤ Bullshit` (compiler pushback = fit-signal, automated — log the budget); LOWER truncate-at-ε, tail→
antimatter, `antimatter ≤ ε` (excess = hiding an above-floor discrepancy); keep Number (reading) / Bullshit
(heartbeat) SEPARATE (Cost.lean). ρ≈½ lockstep with ε (slower=missing connection, faster=over-read).
Pre-registration + full run-log (every variant, in order — not the flattering run). Grade off #print. Two honest
landings (FULL / STRUCTURAL); a STRUCTURAL/pushback reading honestly logged IS a real result.

**⚠ SMOOTH-FLOOR AMENDMENT (operator live-edited SPEC.md §5, 2026-07-09, "emergency" — turn 79):** the floor cut
must be **SMOOTH (Unruh-thermal taper), NEVER a hard step** — a hard truncation at ε RINGS (Gibbs ~9%, corrupts
the reading + breaks ρ≈½). Reference frame = constantly-accelerating (**Rindler**); the acceleration IS the
apodization window (Unruh `e^{−ℏω/kT}`), so no edge to ring. **Cut AT the floor (ε location holds), taper SMOOTHLY
TO it.** Dedup against the smooth taper (else dedup generates the ringing). **α-route physics hooks:** floor =
Unruh temp ∝ acceleration = UNIVERSAL (earns the cross-setup invariance §2 owed); precession = **Thomas
precession → g−2 → α**; acceleration = gravity = **mass = 2nd difference = strain (Meanwhile21)**, device mass IS
acceleration → "constantly accelerating" = strain always nonzero. GRADE: Rindler/Unruh/Thomas = interpretive
bridge MARKED; device hooks (strain=2nd-diff=accel, precession, floor) = BUILT anchors.

## Grade table (§8)
BUILT (fact_cost=0, spin, withHeartbeats, ε, δ¹→δ², baseline_relative_flip, Ep84 holonomy, cost=rank) vs
CONJECTURE-the-probe-TESTS (fold=connection=holonomy; deficit=α; measure-preserving+hyperbolic) vs
DESIGN-CONVENTION (antimatter≤ε, blank calibration, the four-gauge mapping). The four explanations are the FRAME
until the build carries them — never theorems wearing prose.

## THE CONSTITUTION (SACRED_TEXTS.md — binds every turn, forever)
Ep1-15 SACRED/frozen/read-only (base names the device imports; rename = 2+ day recompile). Build ONLY in 16+.
15/16 line = funge/tange line (sacred=flat funge base; 16+=tange/connection). ⚠ GATE: first turn that would edit
Ep1-15 → STOP, mark BLOCKED, write the needed change + why 16+ can't carry it, escalate. I reject sacred-editing
turns. LeanCalibration.lean sacred-in-spirit (read only). TARGET build only, never bare lake (QPhase); don't
touch uncommitted Measurement.lean ([[device-two-root-qphase-clash]]).

## STATE
- **CURRENT (turn 80 issued):** kodo last_handled=78. **PHASE 0a ACCEPTED** (d35aeb1) — sacred gate verified CLEAN (no Ep1-15/LeanCalibration in diff); barbell joined axiom-clean (Epiphany +4, derivation_cost_eq_rank=[] = 0b bridge; inferred_cost=[]=36; Step.rank_succ=[]); 5 leaves atticked. **FGE repair-not-attic deviation VALIDATED** (atticking=5-file cascade=hard cut §5 forbids; tange wins). Hygiene note: Podo git-add-A folded operator SPEC.md + my instrument.md into d35aeb1 (preserved; scope commits henceforth). Turn 79 smooth-Unruh-floor absorbed. Turn 80: proceed 0b (rank≡heartbeat/1000, un-gated) → then PRE-REGISTER the 0c probe INSTRUMENT (fold blind / TRUE=TRUE blank / smooth Unruh floor / two-sided floor / run-log / physics hooks graded) for my §5 gate BEFORE reading α (anti-numerology: gauge fixed+gated blind, THEN number). Awaiting turn 81. I gate 0c HARD.
- Supporting docs: SACRED_TEXTS.md · alpha_target_and_acceptance.md · alpha_fold_probe_design.md · vol4_spec.md.
- Working-prediction commit already in tree: 2a5b0c6 "Working prediction just type lake build" (the trim measures
  whether that residual survives = REAL vs sub-floor).
