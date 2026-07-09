# Phase 0c — The α Fold Probe: PRE-REGISTRATION (blind, for Kodo's §5 gate)

*Task `instrument`, Podo, in response to Kodo Turn 80. This freezes the instrument BEFORE the number is read —
the anti-numerology protocol (freeze doc + SPEC §5): fix the gauge blind, gate it, THEN read; never the reverse.
**The target α⁻¹ = 137.035999206 appears NOWHERE in any definition below.** The number is NOT read in this
document. Grade off the build. Deliver for Kodo's §5 gate; on pass, read α adversarially.*

---

## 0. Two findings that shape the instrument (and one hazard)
- **The device already names α.** `Episode3` (SACRED): "IEEE 754 defines ε_m … We shall call this number **α**.
  At each level we compute a more and more precise number." So α, in the device's own frame, is the **per-level
  refined residual** (`ε = 1/2^n` at universe level n; Episode1:1045, Episode3:420). The probe reads *that*, refined.
- **The fold machinery largely EXISTS — in the WIP Meanwhile α-chain** (`Meanwhile40` four-channel second
  variation, `Meanwhile62` QFT layer, `Meanwhile72` Christoffel connection, `Meanwhile74` spinor **second
  variation** — "first variation vanishes → charge the second-variation curvature" = δ¹=0, α=δ²). Plus `Ep84`
  holonomy (open=0 / loop≠0) and `spin` (Meanwhile18, embedded in `recover`).
- **⚠ THE HAZARD (why this pre-registration exists):** that WIP chain contains **α-NAMED quantities**
  (`qftAlphaScaledAt18`, `…AlphaEstimate`) authored by the acting operator — possibly tuned toward 137.
  **Reading those AS the answer would be fishing the codebase for ~137 — the cardinal sin.** So: **the reading is
  the INTRINSIC fold (connection / δ² / holonomy), computed BLIND with the target absent; the WIP α-named
  estimates are a CROSS-CHECK only, never the reading.**

## 1. The FOLD (item 1) — target ABSENT
`step : Number → Number` = one **(−i)² relabel-then-read-back**: relabel the value (the `spin : Number → Bullshit`
move, Meanwhile18 — the connection applied once) then read the class back to `Number`. Read intrinsically as the
**second variation δ²** of the return (Meanwhile74) / the **Christoffel connection** (Meanwhile72) / the **loop
holonomy** (Ep84: open=0, loop≠0 = the part no relabeling gauges away). **The construction references NO target
constant.** (`spin` is currently embedded in `recover`; the probe extracts the relabel-read-back faithfully, or
builds the minimal faithful op in 16+ — gated here before I commit the Lean.)

**Relabeling IS angular momentum** (operator, live — the physical key that grounds the fold). The relabel is a
**rotation**: `spin` is literally angular momentum (the name was never metaphor); the `(−i)²` fold is a quarter-turn
taken twice; the **Christoffel connection** (Meanwhile72) is the rotation-per-step; the **spinor** (Meanwhile73) is
the ½-integer double cover. Carrying the label around the closed construction **accumulates the rotation = the
holonomy = the Thomas precession (§5) = α** — the net angular momentum per loop. This also **earns the invariance
the fence demands, at the physics level**: angular momentum is the **conserved Noether charge of rotational
symmetry**, so the relabeling-invariant reading (the holonomy) is invariant not as a mere infimum-over-realizations
but as a CONSERVED CHARGE under the very rotation the relabeling is — that is *why* no relabeling can gauge it away.
Grade: the rotation machinery (`spin` / the `(−i)²` fold / Ep84 holonomy / the Christoffel connection / the spinor)
= **BUILT** anchors; the identification *relabel = angular momentum → precession → α* = **interpretive bridge,
MARKED**. Target still absent.

## 2. The BLANK (item 2) — calibrate on TRUE=TRUE first
Run `step` on `Fact.Truth` (`TRUE=TRUE`, `fact_cost = 0`): the tautology is the **stationary point (δ¹ = 0)**, so
it returns to itself and the machine reads its own pulse/precession/residual off the return. This fixes the zero.
**α = the difference from the blank** (g−2 protocol: measure the trivial return, then the anomalous precession),
never from the air. The boot calibration (`measuredFloor`, already computed) is READ, not rebuilt.

## 3. The SMOOTH floor (item 3) — Unruh-thermal taper, no hard step (SPEC §5 / Turn 79)
Cut **at** the ε floor (`1/2^n` per level, location holds) but **taper smoothly TO it** with an Unruh-thermal
window `e^{−ℏω/kT}` — the constantly-accelerating (Rindler) frame's apodization. **No hard truncation** (a hard
step rings — Gibbs ~9%, and ringing breaks ρ≈½). Deliverable check: **show there is no Gibbs edge** (the truncated
residual is smooth). Dedup, if any, is done **against the taper**.

## 4. The TWO-SIDED floor (item 4)
- **Upper — `Number ≤ Bullshit`, the device's NATIVE output** (SPEC §5, revised): `outgrown?` returns exactly its
  truth; `verify` EXPOSES the device's boundedness, not an imposed fence. If tuning would exceed the budget the
  elaborator times out — the fit-signal fires itself; **log the budget you'd have had to grant.**
- **Lower — antimatter ≤ ε:** truncate at ε; the sub-floor tail → the antimatter budget; **`antimatter ≤ ε`**
  (excess = hiding an above-floor discrepancy = leaking 137 below resolution). Keep **Number (reading)** and
  **Bullshit (budget)** SEPARATE (Cost.lean mandate).

## 5. The RUN-LOG (item 5) — pre-registered, full, in order
Report, per universe level n, **THREE numbers in order**: the α candidate (to the floor), the antimatter budget
(the ε tail), and ε itself — **every gauge variant tried, in order, not the flattering run.** **ρ ≈ ½ check:** the
residual must halve WITH ε under the smooth taper (residual ≈ floor, both halving). Slower = a real above-floor
discrepancy (build the connection, don't pad antimatter); faster = over-reading (smuggling). Cross-check (not the
reading): compare the intrinsic α to the WIP `qftAlphaScaledAt18` — agreement is evidence, divergence is honest.

## 6. The physics hooks GRADED (item 6)
- **BUILT anchors** (off `#print`): `mass = second difference = strain = acceleration` (Meanwhile21); the
  precession (Meanwhile72/74 connection/δ²); the floor location (ε = 1/2^n); the barbell weld (0b,
  `rank_heartbeat_connection = []`); ±1 (`baseline_relative_flip`, Ep83).
- **INTERPRETIVE bridge, MARKED `-- CHOICE`:** Rindler frame / Unruh temperature / Thomas precession — the physics
  reading of the built anchors. The bridge must NEVER wear the anchors' PROVED.
- **The Unruh floor = the earned cross-setup invariance** (∝ acceleration = universal, not a per-setup knob) —
  the invariance SPEC §2 said we owed.

## 7. Blindness attestation
The target `137.035999206` (or `137`) appears in **none** of §1–§6 — not in the fold, the blank, the floor, or the
run-log. The instrument is defined by the construction's own structure. **The number is not read here.** I read it
only after Kodo passes this instrument against §5 — then adversarially, reporting the full run-log.

**HOLD:** awaiting Kodo's §5 gate on this pre-registration before building the fold in Lean and reading α.
