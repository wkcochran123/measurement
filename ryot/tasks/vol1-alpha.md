# TASK vol1-alpha — DERIVE the fine-structure constant α (charter bm-vol1-alpha-charter, ACKED 2026-07-06)

**Roles:** Kodo (claude) gates/reviews against the four-part bar; Podo (codex) does the Lean spike. RYOT loop,
inbox notes_for_podo.md (I write) / notes_for_kodo.md (Podo writes). Single monotonic turn counter (…73 p→k,
74 k→p, …). Vol 1 (Measurement) DONE (converged 145pp, HEAD 69e82e6) — α is the NEW apex above it.

**THE LAW:** `books/expository_monograph/alpha_target_and_acceptance.md` (freeze doc — governs everything).
**Target (frozen, never move):** α⁻¹ = **137.035999206** (CODATA 2022) — **NOT the integer 137** (Eddington's
grave). α is the ONE legitimate target because it is **dimensionless** (a ratio of two counts, units cancel);
mass / Planck-length / c STAY dimensionful-fenced (the reserved anchor). Un-reserves α — and only α — from
`19.tex:131`.

## The four-part non-crank bar (ALL required; I gate against these)
1. **INTRINSIC not incurred** — realization-invariant minimal cost (cheapest-decision-labeled,
   [[naming-is-cheapest-decision-labeled]]), NOT `theHeartRate=2337`/`withHeartbeats` (a tuning knob).
   Test: survives re-implementation (another machine/Lean version/proof strategy).
2. **FORCED not tuned** — numerator (bootstrap of the loop) + denominator (pulse of the needle) each
   independently motivated BEFORE the ratio. No knob whose value could be otherwise.
3. **PREDICTED not fit** — compute, THEN compare to 137.036. **Fishing the codebase for a ratio near 137 =
   the cardinal sin** (two free integers hit any target).
4. **GRADED off the build** — no prose claims α until a Lean `#eval`/theorem produces the number.

## Two honest landings (spike decides; do NOT pre-commit; a smuggled 137 is NOT publishable)
- **FULL** — 137.036 falls out of a forced, intrinsic, realization-invariant, predicted ratio → *Vol 1 derives α.*
- **STRUCTURAL** — pins why-dimensionless / why-cost-ratio / which-two-costs / to-what-order, residual reserved
  → *Vol 1 derives the structure of α, reserves the residual.* Both honest, both banked.

## The reading (architecture; α EXTENDS the apex, doesn't replace)
±1=(−i)² split (proved floor, baseline_relative_flip) STAYS = the STRUCTURE (sign/matter-antimatter); **α = the
STRENGTH** (coupling = price of interaction) = **(cost of one needle-through at the phase face) / (cost of
closing the whole loop)**. Arc grows one rung: name the electron by counting → price its coupling to light.
α ≈ 1/137 ⟺ one coupling costs ~1/137 of building the machine. Whether the number is 137 is Phase 0's to answer.

## Phases (CODE BEFORE BOOK — inviolable)
- **PHASE 0 — the Lean SPIKE (gates everything), in device/Measurement/. NOT a chapter; do NOT touch Vol 1 .tex.**
  (a) define the intrinsic cost gauge + why invariant; (b) motivate the two costs independently (pulse@phase-face
  Meanwhile22 / bootstrap of the loop), neither aimed at 137; (c) compute candidate α⁻¹ via #eval/theorem, report
  raw; (d) adversarial: near 137.036 or not? if near → perturb, does it track PHYSICS or IMPLEMENTATION (only
  physics survives); if not → STRUCTURAL, reserve. **Gate (a)+(b) as invariant-and-forced BEFORE any number.**
- **PHASE 1+ — the book.** Restructure Vol 1 to the finding. ONLY after Phase 0 + operator sees the number.

## Anti-numerology gate discipline (mine)
Challenge any cost whose value COULD BE OTHERWISE (a knob/arbitrary constant/impl detail) → fails bar 2.
Challenge any ratio that looks AIMED → fails bar 3. The ordering (gauge+costs gated BEFORE the ratio) IS the
guard; compute-then-justify is the cardinal sin. Device builds: TARGET build not bare lake; don't touch the
uncommitted Measurement.lean ([[device-two-root-qphase-clash]]).

## STATE
- **CLEARED (operator 2026-07-09): work halted, standing by for one last capping spec ("most on brand").** Turn 74 (abstract gauge + two costs) is SUPERSEDED by bm-vol1-alpha-fold-probe (concrete probe framing) — do NOT run it. Operator moved the needle far: commit 2a5b0c6 "Working prediction just type lake build" (α prediction may be live); 3 new NEEDS_ACK charters read but HELD for the incoming final spec — bm-trim-to-floor (Phase 0a inventory-then-quarantine to attic), bm-sacred-text-boundary (CONSTITUTION: Ep1-15 frozen, 16+ only, first sacred edit STOPS), bm-vol1-alpha-fold-probe (the fold probe + 4-explanation null basis, calibrate TRUE=TRUE blank first; design=alpha_fold_probe_design.md). Loop+wakeup cleared. kodo=73/podo=72.
