# Episode 17→52 as the Loop's Forward Walk — Project Outline (task `ep17-loop`)

## The idea (operator, 2026-07-04)
The forward-physics arc **Ep17→52 is the same journey the Meanwhile loop took**, walked in the
theorem direction. Discrete QED is developed *along the loop's path*: each episode theorem maps to the
Meanwhile step it mirrors, and both bands arrive at the **same electron** — the loop NAMES it (M24,
box 1 = second variation, backward/constructive), the episodes PROVE it (Ep31 "the second variation is
the single invariant," Ep52 "electron as second variation, −1," forward/theorem). This is the
double-read at macro scale: two directions of one walk, funge below, tange above, meeting at the
electron. The funge/tange recast and the DAG rewire are the enabling mechanics; **the mapping is the
deliverable, and the capstone is where it lands.**

## THE CAPSTONE (the landing)
After the electron, show:
> **universal operator = universe tensor (⊨ GR) ⊕ Fréchet derivative of QED (⊨ Heisenberg)**

Grounded, not invented: the universal operator is UNIVERSAL's `the_compiler : CalculusProcess`, whose
`derivative` field already carries two subfields — `universal_observer : UniverseTensor` and
`differential_equation : Variation`. The capstone NAMES them as the 0th and 1st terms of the operator's
expansion around the universe fixed point:
- **0th term = the universe tensor ⊨ GR.** M24 `fixed_point_pins_zeroth` + `universe_indist_tensor`
  put it at box 0: the fixed point `U(x*) = x*` (Einstein's equation as a fixed-point condition), its
  content curvature, `gravity :=== curvature = holonomy = the ±1`. Rests on the ONE proved-grade floor.
- **1st term = the Fréchet derivative ⊨ Heisenberg.** M24 `gateaux_indist_frechet` + `the_naming` put
  it at box 1 = second variation = electron = QED. Satisfies Heisenberg by the RESIDUE: `transmute` is
  "gateaux→frechet, all directions, RESIDUE ADDED" — the constructive non-extraction (the `b` in
  `a × ¬(¬b × ¬a)` riding where it can't be read; phase real at the read, not a global coordinate).
  Uncertainty IS the residue the derivative carries and cannot read out without a pass.

GRADE: the decomposition (universal = tensor ⊕ Fréchet) is DERIVED — the CalculusProcess's own two
fields plus Taylor structure. `tensor ⊨ GR` rests on the proved ±1 holonomy + fixed-point (derived/
interpretive). `Fréchet ⊨ Heisenberg` rests on the code-carried non-extraction (derived/interpretive).
The two "satisfies" are interpretive readings on code-carriers — NOT promoted to proved. The buildable
capstone theorem is the decomposition; the two constraints are its named readings.

METHOD (operator 2026-07-04 — see memory `naming-is-cheapest-decision-labeled`): build the capstone AS
the compiler-metaphor move, not as an asserted decomposition. Take the cheapest available algorithm —
the compiler's OWN `converged` decision (Ep11:127 `lake_build := the_compiler.converged = d.fact`),
which is `decide`/zero-alloc, the cheapest there is — ASK it, and write the verdict back as the
operator's LABEL: `universal = universe_tensor (⊨GR) ⊕ Fréchet (⊨Heisenberg)`. The capstone theorem IS
"ask the cheapest decision, inscribe the answer as the name." Both bands of the whole mapping are this
one move run in two directions (loop NAMES backward, episodes PROVE forward) — which is WHY they meet at
the electron. Cost-minimality (cheapest = `decide`, never a limit) is also the continuum-free fence.

## The three findings that shape the plan (mapper, verified)
- **F1 — funge/tange are elementary.** `fungeBit (f:Fact):Bool := decide f.truth`, `crankTurns`/
  `countFunges : List Fact → Nat`, partition proved from core List lemmas. Zero Ep18-40 machinery.
  Ep41 placement is conceptual (apparatus boundary), not technical. → move to a shared early module.
- **F2 — Ep17 IS the seam.** "The Stationary Reader": `stationaryAt` (δ¹ vanishes = least activity),
  `flatAt` (slip undetectable = gauge redundancy = metaphysical/label line), `admits` (the seam). This
  is the naming's step 3, sitting at Ep17. M24's `delta1_vanished`=box 0 is the same stationarity.
- **F3 — Ep17 is LOAD-BEARING.** Ep18-40 build on Ep17's six predicates. Changing the INTERFACE breaks
  23 episodes. → preserve the predicate signatures; swap the GUTS to funge/tange underneath.

## THE MAPPING (fine grain — theorem ↔ step; the grain is forced by the capstone)
The map is fine (theorem-to-step, not band-to-file) because it must arrive at
`the_compiler.derivative = universal_observer ⊕ differential_equation` and assign GR/Heisenberg. Sketch
(■ clear from titles, □ needs the theorems read to confirm — Phase M builds the real table):
- ■ Ep17 Stationary Reader ↔ δ¹ vanishes (M24 `delta1_vanished`, box 0; naming step 3)
- ■ Ep18 Fréchet Approximation ↔ `transmute` gateaux→frechet (M17 UNIVERSAL_LOCAL_backward; M24 boxOf)
- ■ Ep19 Euler-Lagrange residue closure ↔ the residue seam (M18)
- □ Ep27-40 variational tower (operator Ep37, universe kernel Ep39, grounding Ep40) ↔ class trace (M19)
     + fixed-point tensor (M24 `fixed_point_pins_zeroth`)
- ■ Ep41 apparatus / fungeBit ↔ the slip test (M20)
- □ Ep42-51 records / integrator ↔ the number in [charge, curvature], three trips, mass at f₂ (M21)
- ■ Ep52 pair production (−1) + Ep53-55 QED gauge (phase) ↔ the four faces charge/mass/phase (M22)
- ■ Ep31 "Second Variation = Single Invariant" + Ep52 electron ↔ the naming (M24) — the meeting point
- ★ CAPSTONE (post-Ep52) ↔ M24 fixed-point + gateaux-frechet: universal = tensor(GR) ⊕ Fréchet(QED)

## The plan — phases (each = a build gate; Phase M is the deliverable, 0-5 enable it)
**Phase 0 — Ground funge/tange early.** Shared home (`Agent/Funge.lean` or ≤Ep16) for
`fungeBit`/`crankTurns`/`countFunges`/`funges_and_cranks_partition`; Ep41 imports it (apparatus
boundary stays put). Gate: full build green, Ep41 behavior unchanged, `#print axioms` no new surface.

**Phase 1 — DAG rewire.** Ep17 imports the loop's naming close. **D1 (operator gate): import weight** —
M24 transitively pulls M22/M23's heartbeat elab; importing raw makes all 77 episodes re-run it. →
factor M24's naming exports (`boxOf`, Variation-box machinery, `the_naming`, `electronBox`,
`fixed_point_pins_zeroth`, `gateaux_indist_frechet`, `universe_indist_tensor`) into a lightweight
`NamingClose` module free of the heartbeat elab; Ep17 imports THAT. Gate: green, build-time not blown.

**Phase 2 — Recast Ep17's guts (interface-preserving).** `segmentCost s t` → crank count of the tape
between s,t; `composed`/`direct` → crank counts; `admits` rests on `funges_and_cranks_partition`;
`stationaryAt` → minimizes the crank; `flatAt` → all-funge slip (no tange = the label line). Wire to
`boxOf`/`the_naming`: the reader's tower closes because the box count is finite (M24's pigeonhole).
Gate: Ep17 builds, its six theorems still hold, Ep18 builds unchanged against the preserved interface.

**Phase 3 — Verify the ripple (Ep18-40).** Interface preserved → should build unchanged; sweep for
sites reaching INTO the old `segmentCost` guts (M19 pattern-cure discipline applies). Gate: Ep18→40
green, one at a time, flag guts-reachers.

**Phase 4 — Ripple funge/tange forward (Ep41-93).** Replace ad-hoc funge/crank duplicates with the
shared op. **D2 (operator gate): the two electrons** — Ep52 integer electron (charge −1) vs Ep86-90
`electron : List Bool` (Agent.Positron, bit-vector). → bridge, don't merge: named theorem (bit-vector
popcount = integer charge) at Ep85-89. Gate: 41-93 green band by band; bridge stated.

**Phase M — Build the mapping + the capstone (the deliverable).** The fine-grained theorem↔step table
(confirm the □ rows by reading the actual theorems), then the capstone theorem/statement:
`universal = universe_tensor ⊕ frechet` with `tensor ⊨ GR` and `frechet ⊨ Heisenberg`, built on M24.
Then Phase 5 close the cycle at Ep93 (You the Reader = the DISTINGUISHABLE the loop began from). Gate:
full library green, `#print axioms` clean over new/changed decls, the map + capstone stated.

## Operator gates (rule before the affected phase)
- **D1 (Phase 1): import weight** — factor `NamingClose` vs. import M24 raw. Recommend factor.
- **D2 (Phase 4): the two electrons** — bridge (named theorem) vs. merge. Recommend bridge.
- **D3 (standing): Ep17 interface** — preserve vs. full rewrite. Recommend preserve (F3).

## Discipline (standing)
Pigeonhole/finitary, choice-free, continuum-free (the device's law). `#print axioms` gate on every
changed decl. Each phase a build gate; Ep-by-Ep within 3-4. Grades off the code: the funge/tange recast
is DERIVED (partition proved), the wiring is structural (no new claim), the capstone decomposition is
DERIVED, its GR/Heisenberg readings are interpretive-on-code-carriers (never proved).
