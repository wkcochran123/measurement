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

## ⚠ §4/§5 EXPANSION (operator, 2026-07-09 — the α METHOD is now fully specified; I gate 0c against ALL of this)
**0c = a BISECTION over `[ε, Bullshit]`**, predicate = `outgrown?` (monotone), **α = the flip point**
(verified→outgrown), 1 bit/step (= ρ≈½), halts at the floor. Bisection = the resonance-immune root-finder
(anti-Newton/anti-Gibbs). ⚠ **Precondition: the predicate must flip EXACTLY ONCE** — the smooth Unruh taper
guarantees it (a hard cut rings → multiple flips → bisection lands on a SPURIOUS root). **Comparison = ELABORATION
HEARTBEATS** (deterministic, NOT wall-clock → THAT is the repeatability); `a<b` ⟺ `a` elaborates in fewer
heartbeats (race both through the elaborator). **It's a METAPROGRAM in 16+** (`withHeartbeats`/`ekg_probe`,
EKGBounded.lean = mine, out of the Ep1-15 cache) — does NOT fill Episode3's term-level `smaller_than` (a sketch,
left free) → **Episode3 STAYS FROZEN, no sacred edit** (⚠ watch: if the metaprogram pulls an Episode3 import that
forces the fill → STOP+escalate). **α is a MEASUREMENT (meta), not a term-level theorem**; welded to term-rank by 0b.
**The search = a cost-sorted HERBRAND-universe search** (Herbrand.lean: HTerm=derivation, size=cost=heartbeats;
QED.lean converges to `inferredTerm`; the needle=one Quot.sound=the sanctioned ground instance). It EXPLODES (the
2-day cost). Halting only on TWO guards EXTERNAL to Herbrand: (1) **the floor** (ε=TRUE=TRUE's cost) prunes the
tail; (2) **the pigeonhole** (NamingClose, finite distinguishability classes). Tamers: cost-order + bisection +
smooth taper + bounded-shapeless output — watch both guards.
**PROVABLY BOUNDED (halting = a theorem):** boxed on cost (≤ Bullshit) + value (α⁻¹ ∈ (137, 137.036)) → finite
box → pigeonhole → terminates. ⚠⚠ **Bracket ends FORCED, NOT chosen** — `137 = GR` (geometric/tensor/Ricci, BARE/
tree-level, winding count = recession/funge); `137.036 = QED` (Fréchet/radiative, DRESSED, Schwinger/anomalous
precession = recession+precession/tange); width `0.036` = QED's radiative dressing. The two ends ARE the Capstone
(`tensor⊨GR ⊕ Fréchet⊨QED`); the search bisects between the universal operator's two terms; α = where geometry
meets radiation. ⚠⚠ **MY SHARPEST 0c GATE:** the bracket CONTAINS the target — non-crank ONLY if the endpoints are
INDEPENDENTLY BUILT (137 from the GR/winding count; the 0.036 from the QED radiative structure), NOT the CODATA
value inserted to trap the answer. I challenge the QED endpoint hardest (it = the target). Grade: Capstone BUILT;
"137=GR / 137.036=QED" = interpretive MARKED (but makes the pigeonhole provable).
**CONTROL HIERARCHY — coarse→fine:** GR/QED = the FINE vernier (last digits in [137,137.036]); **Navier-Stokes =
the LARGE KNOB (coarse)** — viscosity=damping=laminar/turbulent (Reynolds); flows the search into the basin (~137),
keeps it laminar; too little viscosity → turbulent → resonance/Gibbs. Dedup = local viscosity; NS = global. **Floor
= MINIMUM viscosity** (dissipation ≥ ε → can't go turbulent at the bottom → converges not blows up). ⚠⚠ **HARD
FENCE: the device does NOT solve NS regularity** (Millennium untouched); NS fenced to the finite three-rung shape
(stress-strain, Episode1, standing A.3). Narrow honest claim: *floored finite search stays laminar because the
floor supplies a min viscosity* — NOT continuum-3D-NS-never-blows-up. "NS = large knob" interpretive MARKED.
Sequence: **turn the large knob (damp into basin) THEN bisect the fine bracket.**
**§5 additions:** UPPER floor = the device's NATIVE output (`OUTPUT ≤ Bullshit`; `verify` EXPOSES boundedness, not
a bolted-on fence; output is `OUTPUT≤Bullshit`=verified or `outgrown`=fit-signal). **Output = a bounded SHAPELESS
scalar = `length(residue)` → `dot Weyl = 0`** (length=trace, Weyl=trace-free → a length is Weyl-orthogonal); every
reading is BOUNDED ∧ SHAPELESS → no channel for a directional artifact to hide in. α = scalar coupling = Weyl-free
length. Grade: `cost=length` BUILT; `dotWeyl=0` interpretive MARKED. **Device measures RICCI** (trace/volume: the
effort-ball's volume; `mass=2nd-diff=strain`=traced geodesic deviation=Ricci contraction; accel→Unruh→entropy IS
**Jacobson's** δQ=TdS-on-Rindler-horizons derivation of the Einstein eq — the frame DERIVES Ricci). **Capability
fence: device is BLIND to WEYL** (trace-free/measure-preserving/tidal/GW curvature — a counting machine can't see a
measure-preserving distortion): it can PRICE α (Ricci/volume/coupling), CANNOT detect a gravitational wave. Grade:
finite Ricci-SHAPE (three-rung) BUILT-fenced; continuum R_μν fenced; "this is Ricci"/"Jacobson" interpretive MARKED.

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
- **CURRENT (turn 110) — ⚑ HARD REDIRECT: the CLEAN SERIAL CONSTRUCTION (PLAN_RFC.md updated).** kodo last_handled=109. Operator STOPPED the four-PDFs/gauges finish (SUPERSEDED — build was broken: bare `lake build` fails, the Phase-0a trim atticked root-imported files [Episode93@Measurement.lean:74; likely Agent/Formalization] because the inventory only traced the 16+ graph, not the root import list). **NEW MANDATE = `PLAN_RFC.md` (rewritten by me to the actual spec):** ONE clean serial construction; `lake build` prints [propext] + `a1 < α ≤ a2` (w/ guess); ONE theorem `two_descriptions : electron_in_orbit = anti_cooper_pair := rfl` ("heard both ways"); SERIAL episodes in order, NO Meanwhile filenames, NO duplicates. **THE FRAME:** three-fold −1/0/+1 = quark color R/G/B = C/M/V = α/β/γ = x/y/z = O(1)/log/n; **quarks = the 3 (structure/trace/count, empty footprint); gluons = the 8 (3²−1 traceless SU(3) adjoint) = the coupling = α = Weyl/magnitude the machine is BLIND to.** Scope: 71 Meanwhile, 93 Episodes(1-93), 72 root imports, 4 attic. Turn 110 = Step 0 (fix build) + Step 1 (map). **Turn 111 DELIVERED + GATED:** Step 0 DONE (Episode93 restored = the ONLY atticked-but-root-imported file; bare lake build GREEN 101 jobs); Step 1 MAP (consolidation_map.md) = decisive fact: the import graph is a NEAR-LINEAR CHAIN on a clean sacred base (Ep16 = single join importing Ep15+Mw17); so consolidation = **PRUNE not 93-episode-rename**. Echo already built (TwoDescriptions.lean, two_descriptions:=rfl, self-contained, but #print=[] on plain Channel). **Turn 112 GATE: PRUNE APPROVED** (supersedes my rename-ledger; = operator's "17- unnecessary"). 2 rulings: (1) []→[propext] — LIFT echo through sacred Truth/Fact (operator target = axioms==propext, not bare-[] Channel); (2) α bound = SCALED-INT self-contained on sacred (NO Float — CooperManual/AlphaManual Float+CODATA = dead weight, delete), blind. SAFE SEQUENCE: restore-point branch first → build target self-contained on sacred (verified bare-green) → prune root imports to {Ep15+target} → git-rm unimported 16+ (Meanwhile*/Episode16-93/dead manuals) → verify bare-green + 2 lines + 1 theorem + sacred intact. Operator showering; loop running. Awaiting turn 113 (the executed prune → final gate).
- **(superseded) turn 106 PROJECT-DONE note — was premature (3 PDFs); see above.** kodo last_handled=105. The four gauges INTEGRATED (552e3be1) as each book's culminating "The Bound" chapter — Vol1 ch35 (\part{The Bound}) / Vol2 ch35 / Vol3 ch27 / Vol4 the_bound.md; three books build GREEN (Vol1 Measurement 223pp / Vol2 Experimentation 382pp / Vol3 The Compiler 131pp), Vol4 = rendering+vol4_spec.md. Verified: sacred CLEAN (whole d35aeb1..HEAD, never an Ep1-15/LeanCalibration touch); null basis HOLDS on the integrated .tex (Vol2 0 computation-words / Vol3 0 physics-words); blind (137.036 external-only, "provably cannot produce it"). **THE RESULT:** the instrument derives α's STRUCTURE with an EMPTY footprint ([]) — electron −1, three holonomy states, count-to-3, dimensionless, α=self-energy — PROVES the magnitude 137.036 is on the far side of a counting machine's sight (Weyl/trace-free/invisible by construction), DRAWS the boundary to scale (Dedekind cut, bound=60 bits), VERIFIES itself (verify API axiom-free repeatable), explained 4 decorrelated ways that AGREE (null-basis anti-crank). Discipline held whole (blind, −1/137 refused, grade-off-#print, sacred frozen, marked). Builds: verify API 0a30160, capstone 8fa5f81, Meanwhile80 4338238, RichardsonSelfNaming 9c16685, AlphaDedekind a2cedef, gauges 552e3be1. Podo stood down; nothing owed. Operator reviews on return. Optional future (operator-directed): the FULLER book re-aim (weave the bound through every chapter).
- Supporting docs: SACRED_TEXTS.md · alpha_target_and_acceptance.md · alpha_fold_probe_design.md · vol4_spec.md.
- Working-prediction commit already in tree: 2a5b0c6 "Working prediction just type lake build" (the trim measures
  whether that residual survives = REAL vs sub-floor).
