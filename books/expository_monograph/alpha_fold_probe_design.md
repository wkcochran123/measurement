# The α Fold Probe — the Instrument, Four Explanations, and the Fences

*Beastmaster synthesis, 2026-07-09. Consolidates the operator↔beastmaster working session into a buildable
Phase-0 spike for task `vol1-alpha`. Governed by [alpha_target_and_acceptance.md] (the freeze doc / the law);
this doc is the concrete instrument + the four-frame write-up. **Grade off the build, never off the frame.***

## The object (ONE thing, built once, read many ways)
The **fold probe**. One operator, iterated around the loop:

- `step : Number → Number` = **relabel then read back**: apply `spin` (`Number → Bullshit`, Meanwhile18 —
  the value relabeled into the corridor) then read the class back to `Number`. This is one baker step / one
  `(−i)²` squaring on the label = one application of the connection.
- **Calibrate on the blank FIRST.** Run `step` on `TRUE=TRUE` (`Fact.Truth`, Episode1:96; `fact_cost = 0`).
  The tautology is the stationary point (δ¹ = 0), so it returns to itself — and the machine reads its OWN
  pulse, precession, and residual off how it returns. This fixes the instrument's zero. α is then read as a
  **difference from the calibrated blank**, never from the air. (g−2 protocol: measure the trivial return,
  then the anomalous precession.)
- **Run under `withHeartbeats`** (the budget — the Bullshit; cf. `theHeartRate`, Meanwhile22).
- **Truncate at the machine-ε floor** (`1/2^n` at universe level n — Episode1:1045, Episode3:420). The
  sub-floor tail is routed to the **antimatter budget** — it is what the machine can't resolve, our
  ignorance, not its measurement.
- **Search up the universe levels** (each level = a fidelity rung). Report THREE numbers per level: the α
  candidate (to the floor), the antimatter budget (the ε tail), and ε itself.

## The four explanations (the deliverable rendering — a NULL BASIS *by register*)
NOT four math frames. FOUR renderings of the ONE result — three of them each **stripped of two registers so
they share NO vocabulary** (maximal decorrelation; agreement can't be a shared-word artifact), plus the literal
code. Each must stand alone and point at the build; none may borrow another's status.

1. **The mathematical explanation that uses no math.** The structure — connection/curvature, pigeonhole
   deficit, second variation, fold-entropy — in pure intuition. No symbols, no equations.
2. **The physical explanation that uses no computation.** The physics — spin as the first distinction,
   precession/g−2, α as the coupling, matter/antimatter — as physics. No code, no algorithm.
3. **The computational explanation that uses no physics.** The code's logic — the fold `spin:Number→Bullshit`,
   the cost gauge, calibrate-on-`TRUE=TRUE`, the ε floor — as pure computation. No physical claims.
4. **A step-by-step walk-through of the code.** The literal Lean.

The three single-register explanations share no words; their agreement **plus the code** is the anti-crank
evidence — the Richardson null-basis made the deliverable, and the Vol 4 template (see `scientific_computation/`).

### The CONTENT (the four frames) — recurs, translated, across explanations 1–3; not itself an explanation
- **Christoffel / connection.** α is the connection coefficient — the relabeling everything real must survive.
  `cost = rank` is FLAT (Search.lean) = zero connection = α=0 built in (serializing gauge-fixed A=0 on the tree).
  The fold restores it; antisymmetric part = curvature/bracket; loop holonomy (Ep84: open=0, loop≠0) = the part
  the gauge can't kill = realization-invariant = α. Recession=radial/rank (funge); precession=angular/holonomy
  (tange).
- **Pigeonhole / matching.** α = the deficit of the pigeon↔hole assignment. Holes = the 36-step rank ladder;
  pigeons = the classes (more classes than steps). Serial path = partial matching; off-path classes = unassigned
  pigeons, holonomy slot = unassigned hole. Line up under the FORCED holonomy sign (unique). Hall deficiency = α.
- **Baker / mod / aliasing.** z→z² = angle-doubling = baker's expanding factor = aliasing; one squaring = `(−i)²`.
  KS entropy = **log 2 per fold** = the uncounted bits, in the FOLD (mod) not the STRETCH (rank).
  Measure-preserving → metric-compatible; hyperbolic → curvature. ρ ≈ ½ per level. Fourth label forced too fast
  = counter-rotating resonance = false convergence.
- **TRUE=TRUE / δ².** The tautology is 0 bits *in value* (stationary point, δ¹=0, `fact_cost=0`); its info is in
  **δ²** = curvature = box 1 = the electron (NamingClose). Three channels: pulse (Number), phase (holonomy/α),
  residual (ε/antimatter). One honest bit = distance from `true_eq_false` = ±1 sign = spin. Run the blank.

## The fences (honesty — ALL required; the compiler enforces the first)
- **Upper (automated): `Number ≤ Bullshit`.** The relabeling makes the elaborator push back. If tuning needs
  more than the budget, the compiler times out — the fit-signal fires itself. Log the budget you'd have had
  to grant.
- **Lower: truncate at ε; sub-floor tail → antimatter; `antimatter ≤ ε`.** Below the floor the machine can't
  tell a difference though we can (because we know 137.036) — that is leaking the target below resolution.
  Quarantine it. Antimatter **>** ε = hiding an above-floor discrepancy = fitting.
- **Keep Number (structural reading) and Bullshit (heartbeat budget) SEPARATE** — Cost.lean's own mandate.
  α is read off the deficit, never off the heartbeat (heartbeat = implementation-dependent = the fence, not
  the reading).
- **Blind: calibrate on `TRUE=TRUE` first; α = difference from the blank; target out of sight in the fold.**
- **ρ ≈ ½ lockstep with ε.** Residual must halve WITH the floor (residual ≈ ε per level). Slower → a real
  above-floor discrepancy (go build the connection, don't add antimatter). Faster → over-reading (smuggling).
  Honest signature: residual ≈ floor, both halving.
- **Pre-registration + run-log.** Fix the fold before the reading; log every level's three numbers, in order.

## The deliverable is an API, not a paper (operator, 2026-07-09)
The device is a **highly repeatable experiment** — deterministic computation, so every run returns the identical
reading bit-for-bit (repeatable EXACTLY, not within error bars; stronger than any lab), against a frozen standard.
**The final API is: help the user VERIFY a calibration.** Not "here is α" — a reusable, trust-minimizing verifier
the user re-runs to check any claimed calibration themselves. Repeatability IS the honesty (a crank result isn't
repeatable by others; a real calibration is). This is the preface's "builds a machine and asks you to check it"
made runnable — the API is the checking; the witness verifies.

- **API surface:** `verify(claimed_calibration) → { verified?, residual : above/below floor }`. Input a claimed
  calibration (the device's α, a user's claimed cost, anyone's number); run the repeatable experiment; return
  verified + the residual, everything below the floor cut into antimatter (unc'laimable).
- **Engine (already built):** `Calibration.EKG.outgrown?` (LeanCalibration) — reading vs `reference +
  measuredFloor` → verified-or-not, floored at `TRUE=TRUE` (`Fact.Truth.decTruth`). `verify` is the clean wrapper.
- **α is the flagship INSTANCE of the API, not the API.** The fold probe is one calibration the API verifies.
- **Repeatability scope (honest):** EXACT per Lean-version/setup (deterministic); calibration-stable across
  setups (self-reference to the `TRUE=TRUE` floor + ratio-read carry the invariance the absolute count can't).

## The deliverable
1. **A working Lean verifier** — builds (TARGET build, not bare `lake`; QPhase two-root clash — do NOT touch the
   uncommitted `Measurement.lean`) and exposes `verify` over `outgrown?`; reads the three numbers per level and
   returns verified + residual for a claimed calibration. The probe is an instance of it.
2. **Four explanations** — the API's manual: each frame written up, standing independently, an account of what
   the verifier *does*. (Vol 4 = the user guide: here are the calibrations, verify them yourself, repeatably.)

## The grade (grade off the build, never the frame)
- **BUILT** (verify off `#print`): `fact_cost = 0`, `spin : Number → Bullshit`, `theHeartRate`/`withHeartbeats`,
  ε = `1/2^n`, δ¹→δ² (NamingClose, `the_naming`), `baseline_relative_flip` (±1), Episode84 holonomy
  (open = 0 / loop ≠ 0), `derivation_cost_eq_rank` (flat).
- **CONJECTURE the probe TESTS** (NOT claimed until the build carries them): fold = connection = Episode84
  holonomy; deficit = α; fold is measure-preserving + hyperbolic (log 2).
- **DESIGN CONVENTION** (honest scaffolding, marked): `antimatter ≤ ε`; `TRUE=TRUE`-as-blank calibration;
  the four-frame mapping.
- **The NUMBER is unknown until read.** Two honest landings stand (FULL / STRUCTURAL). A STRUCTURAL/push-back
  reading, honestly logged, is a real result.

Related: [[vol1-derive-alpha]], [[naming-is-cheapest-decision-labeled]], [[grade-axioms-off-the-build]],
[[the-naming-pigeonhole]], [[covariant-contravariant-is-funge-tange]], [[device-two-root-qphase-clash]].
