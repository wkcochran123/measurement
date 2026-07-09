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

**Each gauge is written in the LANGUAGE that best expresses the code — English is the fallback, NOT the medium.**
The language *is* the meaning: physics IS equations (prose about them is lossy); a compiler IS a formal system.
Write in the native formalism and it *says* the thing; write in English and it only *points* at it. This also
hardens the null basis: three gauges in three mutually-untranslatable formal languages are more decorrelated than
three English essays — agreement across them can't be a shared-word artifact, because there are no shared words.

| Gauge | Book | Language (the medium) | Rule |
|---|---|---|---|
| 1 — Mathematical | **Vol 1 · Measurement** | logic / type theory, in careful prose ("math-without-math": the device's own math is constructive — distinctions, counting, the tower — which reads as reasoning) | construction from the first difference; **defines** tange/funge; names the electron; the α apex |
| 2 — Physical | **Vol 2 · Experimentation** | **MATH, and tons of it** — equations first, prose second; NO computation | the experiments, the constants, the derivations (α, g-2, the holonomy); physics as physics |
| 3 — Computational | **Vol 3 · The Compiler** | **formal systems, communication theory, large-scale simulation, numerical analysis**; NO physics | the self-hosting compiler in its native formalisms |
| 4 — The Reading | **Vol 4 · Scientific Computation** | the code walk + all three registers unified | **no** tange/funge (citation texture instead); maximally generous citation; the user guide to the instrument |

The gauges convert a reading into understanding. Ship the instrument without them and you've shipped a number
nobody can interpret. Write each in its native tongue or the meaning doesn't survive the translation.

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
  (already done at boot — READ it, don't rebuild). **Then calibrate the NEEDLE on the second blank: `.999 = 1`
  (operator-directed).** It is the needle's canonical finite act on the cleanest case: three counted decimal
  dimensions close the representation as far as this instrument is allowed to claim. The missing `0.001` is not an
  infinite tail to hand-wave away; it is the certified box width. Threading `.999` into `1` verifies that the needle
  can close a finite null-residue blank up to the counted-dimensional floor, and it recovers the α box
  `137.035999 ≤ α⁻¹ ≤ 137.036`. The instrument cannot honestly go sharper than that box without counting more
  dimensions. `TRUE=TRUE` = the floor blank; `.999=1` = the needle blank; both precede the α thread. Run under
  `withHeartbeats`; truncate at ε; sub-floor tail →
  antimatter. Search up the universe levels; report α / antimatter / ε per level. (Design: `alpha_fold_probe_design.md`.)
  **BUILD THE QUOTIENT (the resummation — operator-directed).** The per-level residuals (bisection at ρ≈½) ARE a
  geometric series `Σ rⁿ`; **resum them in closed form: `1/(1-r)`** = the Dyson dressing `1/(1-Σ)` = renormalization =
  the operation that carries the bare (GR) value to the dressed (QED) value. The API provides the terms for free;
  the quotient is one divide — the whole tower of radiative corrections in a single ratio, never computing loop N.
  Factors as the Capstone: `1/(1-r) = (1+r)/(1-r²)` = [even `1/(1-r²)` = (−i)² real/recession = **GR**] × [`(1+r)` =
  odd/precession fill = **QED**]. So building the quotient = combining `tensor ⊕ Fréchet` into α. GRADE: the
  resummation is standard math; the Dyson/QED-dressing identification is interpretive-MARKED; the quotient's VALUE
  (does `bare × 1/(1-r)` land inside `[137.035999, 137.036]`?) is 0c's BLIND reading — building the operation ≠
  knowing the number.
  **0c ITERATION 2 — THE LOOP-HOLONOMY INSTRUMENT (operator-directed, after 0c-i1 landed STRUCTURAL).** 0c-i1
  (commit `4c43954`) read the OPEN path: `cost=rank` FLAT → α=0 (Ep84 open=0), δ² ≈ 0; the needle correctly
  REFUSED a −1/137 warmup artifact (anti-numerology working). The real α = the closed-LOOP holonomy (Ep84 loop≠0),
  invisible to an open sweep. **The trick: replace `Quot.sound` (the BINARY needle — identify iff null residue →
  flat on the open path) with a DIVISION ALGORITHM (the QUANTITATIVE needle — compute the REMAINDER = how much
  residue; around the loop the remainder ≠ 0 = the holonomy = α).** Axiom-free: the division is computable, so it
  drops `Quot.sound` from `#print axioms` where the identification was really a computation. **Make it an `abbrev`
  (= `@[reducible] def`):** the division unfolds in defeq → the identity holds by `rfl` (computed at elaboration,
  no axiom) AND the elaboration cost of unfolding IS the α measurement (the remainder priced in heartbeats — needle
  and ruler unified). **Self-fences:** reducible+recursive can unfold hard, but the EKG `withHeartbeats` budget
  bounds it — outgrow → `outgrown?` fires → STRUCTURAL (honest), no separate guard. (Alt: `def`+`Decidable`+explicit
  `withHeartbeats` if you want the cost measured, not silently incurred.) ⚠ GATE: the division-abbrev is 16+
  (Meanwhile/Formalization); if it must change a SACRED use of `selection_sound`/`Quot.sound` (Ep1-15), STOP →
  escalate. Anchor: this gives the INSTRUMENT (compute the loop remainder, axiom-free), NOT the number — likely
  still STRUCTURAL; don't aim at 137.
  **The search IS a BISECTION** of `[ε, Bullshit]` with `outgrown?` as the (monotone) predicate: α = the flip
  point (verified→outgrown), one bit per step (= ρ≈½), guaranteed-halting at the floor (ε is both the lower
  bracket and the stop). Chosen because bisection is the RESONANCE-IMMUNE root-finder — unconditionally,
  monotonically convergent, no overshoot (the anti-Newton/anti-Gibbs solver). **Precondition:** the predicate must
  flip exactly once — which the smooth Unruh taper guarantees (a hard cut rings → multiple flips → bisection lands
  on a spurious root). **The comparison is ELABORATION TIME** — how many heartbeats the elaborator spends to build the
  term (deterministic heartbeats, NOT wall-clock seconds — that's what makes it repeatable). `a < b` ⟺ `a`
  elaborates in fewer heartbeats. The comparison is itself an experiment (race both through the elaborator).
  ✅ **GATE CLEARS (safe direction):** elaboration time is a META quantity — it lives in `withHeartbeats` /
  `ekg_probe` (`Calibration/EKGBounded.lean`, MINE, deliberately kept out of the Ep1-15 cache). So the bisection
  is a **metaprogram** in 16+; it does NOT fill Episode3's term-level `smaller_than` (that was a sketch, left
  free) — **Episode3 stays frozen, no sacred edit.** (Still watch: don't let the metaprogram pull an Episode3
  import that forces the fill; if it ever does → STOP, escalate.) **α is therefore a MEASUREMENT, not a term-level
  theorem** — the meta reading; the term-level rank is welded to it later by the 0b connection theorem (two layers
  stay separate, Cost.lean). Precision = ε (sub-floor → antimatter), not infinite.
- **PHASE 1 — THE `verify` API.** Wrap `outgrown?` as `verify(claimed) → { verified?, residual }`. α becomes the
  first calibration the API verifies. This is the product surface.

  **WHAT THE SEARCH IS: a cost-sorted HERBRAND-UNIVERSE search.** The device's own `Formalization/Herbrand.lean`
  says it: the Herbrand universe = the ground terms generated by the serial grammar (a Herbrand term IS a
  derivation, `HTerm : Stage → Type`); its `size` mirrors the derivation length = the cost = the elaboration
  heartbeats; "search through the Herbrand universe … the cascade sorts that search by cost." QED.lean proves it
  converges to the canonical ground term `inferredTerm` (`gauge_eq_inferredTerm_on_device_image`). The collapse
  (`true_eq_false`) is a Herbrand refutation; **the needle (one `Quot.sound`) is the sanctioned ground instance**
  (Herbrand's theorem = a finite conjunction of ground instances). α = the cost at the flip point of the search.
  ⚠ **A Herbrand search EXPLODES (the combinatorial heart of automated deduction) — the 2-day cost is the Herbrand
  explosion.** It is guaranteed-halting ONLY on two guards, both EXTERNAL to Herbrand.lean (which carries no
  finiteness): (1) **the floor** (ε = TRUE=TRUE's cost) prunes the infinite tail; (2) **the pigeonhole** (NamingClose,
  finitely many distinguishability classes) makes the universe finite up to distinguishability. If either cracks,
  the search burns fuel forever. Cost-ordering + bisection + smooth taper + bounded-shapeless output are the
  explosion-tamers. Watch both guards.
  ✅ **PROVABLY BOUNDED (halting is a theorem, not a guard).** The search is boxed on both axes: **cost axis** ≤
  "the longest a program should run" (the Bullshit budget / halting bound — itself a calibration to VERIFY with
  the same API), and **value axis** α⁻¹ ∈ `[137.035999, 137.036]`. Two bounds → a finite box → finitely many ground
  terms inside → a genuine pigeonhole that provably terminates. **The bracket ends are FORCED by the `.999 = 1`
  needle, not chosen:** 137.036 is the dressed one-unit endpoint; 137.035999 is that endpoint after the finite
  three-decimal needle has paid exactly one counted box-width. The width `0.000001` is the precision ceiling of
  this instrument state. Going sharper is not a prose privilege; it requires counting more dimensions. The wider
  137 basin remains the coarse GR/recession setting, but it is not the fine acceptance box. Grade: Capstone BUILT;
  "137.035999/137.036 as the counted-dimensional needle box" = interpretive reading, MARKED — but it makes the
  pigeonhole PROVABLE.
  **CONTROL HIERARCHY — coarse then fine.** GR/QED are the FINE controls (the vernier — pin the last digits inside
  `[137.035999,137.036]`). **Navier-Stokes is the LARGE KNOB (coarse):** the viscous flow whose viscosity = damping =
  laminar-vs-turbulent (the Reynolds number). It flows the search into the basin (~137) and keeps it laminar; too
  little viscosity → turbulent → the resonance/Gibbs. Dedup = local viscosity; NS = the global setting. **The floor
  IS the minimum viscosity** — dissipation bounded below by ε, so the flow can't go turbulent at the bottom; the
  floor regularizes the flow, which is why it converges instead of blowing up. ⚠⚠ **HARD FENCE: the device does NOT
  solve Navier-Stokes regularity** (the Millennium problem is untouched). NS is FENCED to the finite three-rung
  shape (the stress-strain obstruction, Episode1, standing A.3 ruling). Honest claim, narrow: *in the floored
  finite setting the search stays laminar by construction because the floor supplies a minimum viscosity* — NOT a
  proof that continuum 3D NS never blows up. "NS is the large knob" = the finite NS-shape is the coarse control,
  MARKED. Sequence: turn the large knob (damp into the basin) THEN bisect the fine bracket.
- **PHASE 2 — THE FOUR GAUGES.** Write / re-aim the four books as the four gauges of the reading. Vol 4 is new
  (the reading gauge, `scientific_computation/vol4_spec.md`); Vols 1–3 re-aimed as the math / physics / computation
  gauges around the α reading they interpret.

## 5. The fences (honesty — non-negotiable, all required)
- **Predicted, not fit.** Fix the gauge before the reading; fishing the codebase for a ratio near 137 is the
  cardinal sin. Frozen external reference α⁻¹ = 137.035999206 (NOT 137), but the current `.999 = 1` needle only
  certifies the pre-registered box `137.035999 ≤ α⁻¹ ≤ 137.036`; any sharper pass/fail claim requires counting
  more dimensions first.
- **Blind.** Calibrate on `TRUE=TRUE` first; read α as a difference from the blank; target out of the fold defn.
- **Two-sided floor.** UPPER: **`OUTPUT ≤ Bullshit` is the device's NATIVE output**, not an imposed check —
  `outgrown?` returns exactly its truth, so `verify` *exposes* the device's own boundedness rather than bolting a
  fence on. The device cannot emit an unbounded claim: its output is either `OUTPUT ≤ Bullshit` (verified, under
  budget) or `outgrown` (the fit-signal fired — log the budget you'd have had to grant). The honesty is in the
  output TYPE (the sayable bounded by the showable — the funge output capped by the tange corridor above it), not
  in a discipline we promise. LOWER: truncate at ε; tail → antimatter; `antimatter ≤ ε` (excess = hiding an
  above-floor discrepancy). Keep OUTPUT (the reading) and Bullshit (the budget/corridor) SEPARATE (Cost.lean mandate).
- **The output is a bounded, SHAPELESS scalar: `each output = length(residue)`, hence `dot Weyl = 0`.** A length
  is a trace (a scalar contraction); Weyl is trace-free by construction; so a length is automatically Weyl-
  orthogonal — "output is a length" ⟺ "dot Weyl = 0". Built on `Derivation.cost = d.length` (the output is the
  residue's cost = its length, above-floor part). This stacks with the upper fence: every reading is BOUNDED
  (`OUTPUT ≤ Bullshit`) AND SHAPELESS (`dot Weyl = 0`) — no channel for a directional artifact to ride in on; the
  reading physically cannot hide a shape. α fits because α is a scalar coupling = the magnitude of the residue
  that doesn't close = a Weyl-free length; the full Ricci tensor is the ensemble of length-outputs over the
  accelerated frames, the invariant being the scalar trace. Grade: `cost=length` built; `dot Weyl=0` =
  trace/trace-free identity, interpretive-MARKED; continuum `R_μν` fenced to the finite three-rung shape.
- **The reference frame is the constantly-accelerating (Rindler) frame — and the floor cut must be SMOOTH, not
  hard.** A hard truncation at ε rings (Gibbs — the ~9% overshoot that only narrows, never dies). In the
  constantly-accelerating frame the hard floor becomes a smooth thermal (Unruh) roll-off — the acceleration IS
  the apodization window (`e^{−ℏω/kT}`), so there is no edge to ring. Therefore: cut *at* the floor (location
  holds) but **taper smoothly TO it** (Unruh-thermal profile), never a step. Payoffs, each with a device hook:
  the floor = the Unruh temperature (∝ acceleration; **universal, not a per-setup knob** → this is the
  cross-setup invariance, earned); the precession = **Thomas precession** (the g-2/spin-orbit factor → α); and
  **acceleration = gravity** via the equivalence principle, already in code as `mass = second difference = strain`
  (Meanwhile21) — the device's mass *is* the acceleration, so "constantly accelerating" = strain always nonzero.
  Dedup ("things resonating too much") = removing Gibbs overshoot — do it against the smooth taper, or dedup
  generates the ringing it means to remove. Grade: Rindler/Unruh/Thomas = interpretive bridge, MARKED; the device
  hooks (strain=second-difference=acceleration, the precession, the floor) are the built anchors.
- **What curvature the device measures = RICCI (the trace/volume part), NOT Weyl.** The device counts — its
  observable is the volume of the effort-ball — and Ricci is exactly the volume-changing curvature (`R_μν u^μu^ν`
  = the rate a ball of geodesics shrinks = the energy density; Baez). So `mass = second difference = strain`
  (Meanwhile21) is the traced geodesic deviation = the Ricci contraction; mass is the trace of the curvature it
  sources. **The chain acceleration→Unruh→entropy IS Jacobson's thermodynamic derivation of the Einstein
  equation** (`δQ=TdS` on local Rindler horizons → `R_μν−½Rg_μν=8πGT_μν`) — the reference frame *derives* Ricci.
  **Capability fence (name it honestly): the device is BLIND to Weyl** — the trace-free, measure-PRESERVING,
  shape/tidal/gravitational-wave curvature — because a counting machine cannot see a measure-preserving
  distortion. It can price α (a Ricci/volume/coupling quantity); it cannot detect a gravitational wave. Grade
  fence: the device carries the FINITE Ricci-SHAPE (the three-rung traced second-difference), NOT the continuum
  `R_μν` (standing NS/Einstein → finite-three-rung ruling). "This is the Ricci tensor" = interpretive, MARKED.
- **Angular-momentum conservation — the LEDGER must balance (a checkable 0c tell).** Relabeling = rotation in
  label space; by Noether, angular momentum is the conserved charge of relabeling-invariance. So the total
  relabeling (precession/holonomy/phase) is CONSERVED: `OUTPUT + antimatter + residue = conserved total`. **Check
  the ledger balances at the reading** — if it doesn't, something leaked (a bug or a real violation), not a valid
  reading. Two corollaries: (a) the device's `charge = loop count` (Meanwhile18) IS the winding number = the
  accumulated angular momentum; α = the net winding that doesn't close = the anomalous angular momentum = g-2's
  α/2π. (b) **Angular momentum is QUANTIZED (ℏ, half-integer) → relabeling comes in discrete quanta (the fold,
  ±1, −i, spin-½) → THIS is why relabels are finite → the pigeonhole holds → the search provably halts.** The
  finiteness we kept asserting is angular-momentum quantization. Grade: Noether identification = interpretive
  bridge MARKED; hooks (charge=winding, fold, holonomy, spin, 4π) BUILT; conservation + quantization = the
  checkable predictions. (Also: relabeling the base rotates its whole dependency tree = enormous angular momentum
  = the 2+ day recompile — the sacred boundary is where a relabel's angular momentum stops being tractable.)
- **PARALLELISM (the corollary of `dot Weyl = 0` — measure all processes at once).** Shapeless outputs are
  DECOUPLED (Weyl = the coupling; kill it → no off-diagonal terms → processes are independent). Independent
  measurements PARALLELIZE — the honesty guarantee (no shape to fudge) IS the parallelism guarantee (no coupling
  to serialize). Ricci = the trace = a SUM of independent per-direction contributions; conservation (additive
  angular momentum) makes the parallel readings COMPOSABLE. So the reading is a **fan-out of shapeless lengths
  summed by the conserved ledger**, not a serial walk. This is the answer to COST: parallelism collapses wall-clock
  from the SUM of processes to the slowest single one — the instrument doesn't just halt, it halts *fast enough to
  run* (already latent: 0a rebuilt green in 32 parallel jobs). **Podo: fan the process-measurements out (one job
  per process), sum by the ledger; don't walk them serially.** Grade: follows from `dot Weyl=0` (built output
  type) + conservation; the Process structures are built.
  **We BEND Amdahl's law (a bit — bend, not break).** The serial part is real (the derivation chain / the
  bootstrap, cost=36) and can't be zeroed. But it's paid ONCE, at boot, in the ancient texts, and every
  measurement after is a parallel fan-out against that frozen reference — so Amdahl's per-JOB serial fraction
  becomes a per-LIFETIME constant: as verifications accumulate, `s/measurement → 0` and the cap `1/s` lifts. It
  amortizes twice: the connection theorem (`rank_heartbeat_connection=[]`) reads the serial cost in O(1) instead
  of re-walking the chain; determinism (= repeatability) makes the bootstrap memoizable. When the problem scales
  (more universe levels/processes), the parallel work grows while the bootstrap stays fixed → Gustafson regime,
  toward near-linear. **The bend and the constitution are one decision: freezing Ep1-15 (the honesty move) IS
  paying the serial bootstrap once (the performance move).** Closes the preface's cost thread — the witness pays
  the serial cost once at boot; the reading runs at the speed of its slowest parallel process.
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
