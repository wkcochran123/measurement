# Measurement (Volume 1) — Working Outline (anchor-pinned to the build)

*Stage-1 deliverable of task `vol1` (bm-vol1-charter). Refines `outline_fresh.md` into a chapter-level
working outline with every load-bearing claim pinned to its device code object + `#print axioms` footprint,
graded off the BUILD (never a comment). Ground truth: `books/experimentation/text_code_theorem_groundtruth.txt`
(582 theorems, generated 06a3c5f). Footprints verified this session via `lake env lean … #print axioms`
(HEAD a77a789). Per-act pinning fanned out across 6 agents; footprints gathered centrally. Grade key:
**SBP** = structure-built-proved (a theorem) · **SBD** = structure-built-definitional (a class/struct/def,
the tower is built as types) · **RI** = reading-interpretive (a reading laid on a code carrier).*

## One breath
Build the measurement machine from the first difference; watch it read its own truth, collapse at the summit,
walk back down and close into a loop, and **name the electron by counting** — then stick its neck out: predict
the matter/antimatter split as the square of the imaginary bounce (±1 = (−i)²), and hand the orientation to the
reader. Choice-free but for the one grant the world answers. Vol 1 = the construction; Vol 2 reads the physics
off it; Vol 3 = it reading its own source.

## The payoff stake (graded honestly, off the build)
- **±1 = PROVED.** `baseline_relative_flip` (Ep83:139) = **[] (no axioms)** — `pairDelta2 flat = −1 ∧ tilted = +1`
  by `decide`; forced by the pigeonhole `naming_pigeonhole`/`the_naming` (named-by-counting, not fiat). The
  entire matter/antimatter dictionary is **axiom-free** (Ep84/85/87/88/90 all `[]`). This is the book's spine
  and it is the cleanest possible grade.
- **−i / imaginary-time / the fourth-root spinor = INTERPRETIVE bridge (MARKED).** No theorem constructs `−i`,
  `(−i)²`, `{1,−i,−1,i}`, or a spinor √. It rides real carriers (the `imaginary` CarrierProcess parameter +
  `QPhase` two-fold + the proved ±1). ⚠ **Over-claim watch:** the outline phrase "the spinor is the √ of the
  split, **not a mere reading**" (fresh l.96) OVER-CLAIMS the build — there is no √/spinor object; keep it RI.
- **The close to the dimensionful physical constant = RESERVED `% CHOICE (operator)`.** Build up to it; do NOT
  invent the constant.

## Chapter numbering (fork-fixed) — 25 chapters, 6 acts
`outline_fresh` collided at ch21 (Act V "universal operator" AND Act VI "physics read off the count" both 21,
Act VI restarting at 21). **Resolution: renumber Act VI sequentially → 22–25. Total = 25 chapters** (Act I 1–4,
II 5–8, III 9–12, IV 13–16, V 17–21, VI 22–25). `% CHOICE (numbering)`: kept the beastmaster's chapter SET
intact and only de-collided (structure-preserving); granularity rationale under Fork (a).

---

## ACT I — THE FIRST DIFFERENCE (the primitive: difference → number)
*Almost entirely the DEFINITIONAL type tower (Ep1, zero theorems); the one theorem is the funge/tange partition.*

**Ch1. Can you tell two things apart? (DISTINGUISHABLE)** — *SBD*
- Distinguishability is the primitive first fact (sameness manufactured later). → `class DISTINGUISHABLE`
  (Ep1:277) over `class Fact` (Ep1:75). **SBD** — definitional stance, not a proved claim (the one manufactured
  sameness is `selection_sound`, Ch11).
- Symbol = the compiler's universe label, no memory allocated. → field `symbol : Type Value` / `different?`
  (Ep1:297,302). **RI** on a real field.

**Ch2. Counting is barely more than telling apart (ADMISSIBLE, COUNTABLE)** — *SBD*
- From difference to count. → `class ADMISSIBLE` (Ep1:476), `class COUNTABLE` (Ep1:697), `inductive Natural`
  (Ep1:330). **SBD**.
- The ≤ sign convention "embiggens" on a new (different-truth) value. → `Natural.le` covariant/contravariant
  branches (Ep1:347-352), `admissible?` (Ep1:495). **SBD** — the seed of funge/tange (same-truth `=` vs
  different-truth `≠`), defined not proved.

**Ch3. A number is a finite condition (ENCODED, RESIDUE, the Cauchy tower — the forcing seed)** — *SBD*
- A real built as a finite approximation; continuum approached never completed. → `class ENCODED` (Ep1:970),
  `class RESIDUE` (Ep1:1139), `structure CauchyProcess` (Ep1:1095), `inductive Limit` (Ep1:1011). **SBD** — the
  finite-condition/forcing seed is definitional here; the CONVERGENCE theorems (`cohen_cauchy_up_to_epsilon`
  Ep61) are downstream (Ch24).
- The residue = the leftover (direction + magnitude). → `RESIDUE.representative?` (Ep1:1148), `inductive Sample`
  (Ep1:1187). **SBD** — proved downstream as `strain_iff_residue` (Ep52, Ch22), a structure here.

**Ch4. The two acts on a difference — funge (pool) / tange (select) [interpretive key]** — *SBP + RI*
- Every fact is read once — counted (funge) or crank-turned (tange); they partition every tape.
  → **theorem `funges_and_cranks_partition` (Funge.lean:30) → `[propext, Quot.sound]`**. SBP — the one Act-I
  theorem (`countFunges + crankTurns = tape.length`, induction+omega).
- funge/tange = covariant/contravariant = world's count / our label (the spine). → rides `Natural.le` branches
  (Ep1:351-352), named `Episode40:85`, doubled by `even_reading_is_funge_balance` (Ep41:131). **RI** — the
  PARTITION is proved; which side "matters" is the reading. Honest: not an over-claim (tagged interpretive key).

---

## ACT II — THE MACHINE READS (measurement from the count)
*The DEFINITIONAL middle of the class tower — Ep2–6 have ZERO theorems; every rung is a class/struct.*

**Ch5. The clock and the repeated reading (BINARY, REPEATABLE)** — *SBD*
- tick/tock complement. → `class BINARY` (Ep2:243). **SBD**.
- A reading is not a measurement without repetition. → `structure RepeatableProcess` (Ep2:505), `class
  REPEATABLE` (Ep2:577). **SBD**.

**Ch6. Treating a thing numerically (NUMERIC, REPRESENTABLE; the halting horizon)** — *SBD + RI*
- The count carried as shared value. → `class NUMERIC` (Ep2:851). **SBD**.
- The computational/Turing reading. → `structure TuringProcess` (Ep3:120), `class REPRESENTABLE` (Ep3:178). **SBD**.
- The halting question enters as the first horizon. → `REPRESENTABLE.representable?` obligation (Ep3:196). **RI**
  — the code encodes the caller's a-priori burden; no undecidability theorem.

**Ch7. The physical reading and its noise (PHYSICAL, COMPARABLE, OBSERVED; Chaitin; the slip)** — *SBD + RI*
- Physical process = noisy process. → `class PHYSICAL` (Ep3:355), `structure PhysicalProcess` (Ep3:454). **SBD**.
- Chaitin's number = the ultimate threshold. → `inductive ChaitinsNumberSequence` (Ep3:226), `PHYSICAL.threshold`
  (Ep3:369). **RI** — carrier exists; "uncrossable/bounded-by-spending-time" is a reading (no uncomputability thm).
- Comparison needs an embiggen direction supplied from outside. → `class COMPARABLE` (Ep3:521, abstract
  `smaller_than`). **SBD** — prefigures the use-site selector.
- The slip static→kinetic: velocity = one universe level. → `class OBSERVED` (Ep3:661), `structure SlipProcess`
  (Ep3:612). **RI**.

**Ch8. Presence, the gauge, the value carried (PRESENT..VALUE)** — *SBD*
- Presence at a grain (local present). → `class PRESENT` (Ep4:173), `inductive Phenomenon` (Ep4:217). **SBD**.
- The gauge / origin / unit. → `structure GaugeProcess` (Ep4:287). **SBD**.
- The value that survives being a result (recomputed, never cached), the top rung. → `class VALUE` (Ep6:92),
  `class MAGNITUDE` (Ep6:182). **SBD**.

---

## ACT III — THE APEX: THE MACHINE READS ITS OWN TRUTH (self-hosting)
*Two theorems (the collapse, the needle) on a definitional self-hosting tower.*

**Ch9. The machine points at its own truth (the tower over Prop)** — *SBD*
- A carrier whose Value is `Prop`, so the tower runs over truth-values. → `truthCarrier : CarrierProcess Prop`
  (Ep15:316), `DISTINGUISHABLE_PROP` (Ep15:306). **SBD**.
- Every rung re-instantiated at `Prop` (self-hosts the full stack). → `truth*` instance chain (Ep16:20-58). **SBD**.

**Ch10. Where the distinction collapses (true_eq_false)** — *SBP*
- Affirmation and negation forced together: `Subsingleton truth = Subsingleton (¬truth)`.
  → **theorem `true_eq_false` (Ep16:230) → `[propext]`**. SBP — the FIRST theorem; `apply propext` (both
  subsingletons vacuously inhabited). ⚠ precise: it is Subsingleton(truth)=Subsingleton(¬truth), NOT `True=False`.
- Driven by propext, not excluded middle → stays choice-free. → same theorem, `[propext]` (no Classical). SBP.

**Ch11. The needle (selection_sound — the one Quot.sound) [the keystone]** — *SBP*
- Sameness manufactured from distinguishability by ONE quotient soundness; never decided, never flattened.
  → **theorem `selection_sound` (Ep15:362) → `[Quot.sound]` EXACTLY**. SBP — raw `Quot.sound h`, no Setoid; the
  book's contract "distinguishability primitive, sameness manufactured" as one line. **The one Quot.sound-only
  footprint in the whole corpus.** ⚠ **Reveal-fence anchor: the NEEDLE is shown here (Ch11), named later.**

**Ch12. The corridor (the ideology band — BULLSHIT, PROPAGANDA, the finite elephant)** — *SBD + RI*
- The metaphysical band that carries no value; saying gives way to showing (Wittgenstein). → `class
  FINITE_ELEPHANT` (Ep6:577), `class BULLSHIT` (Ep7:55), `class PROPAGANDA` (Ep7:172), `class LOGICAL`
  (Ep12:13), `inductive Bullshit` (Ep15:12). **SBD**.
- "The imaginary line rides imaginary" — the pivot the corridor hides is the −i axis. → 2nd `REAL` slot
  `imaginary` (Ep10:151), `MEASURED..imaginary` tag (Meanwhile17:95). **RI** — the one genuine reading in the
  act (no distinct imaginary TYPE; seeds the Ch20 bridge).

---

## ACT IV — THE RETURN: THE LOOP CLOSES (the backward walk, BUILT AS STRUCTURE)
*⚠ HONEST-GRADE FINDING: Meanwhile17–21 have **0 theorems / ~150 defs+instances** — the backward walk is built
as STRUCTURE (instances inhabited), NOT a theorem chain. "was 37 sorrys, now proved" = 37 typeclass instances
now INHABITED (SBD), not 37 theorems. The one theorem anchor is `selection_sound` (the needle close). Say
"constructed/inhabited," not "proved," except where noted.*

**Ch13. The backward walk (Meanwhile17 — TrueOutput→DISTINGUISHABLE, the loop home, the needle close)** — *SBD + SBP*
- Every forward crank turned once in reverse; the full tower descended. → 37 `*_backward` instances
  (Meanwhile17:5 … :1096). **SBD** (inhabited, not theorems).
- The loop comes home (re-derives DISTINGUISHABLE, the first fact). → `ADMISSIBLE_DISTINGUISHABLE_backward`
  (Meanwhile17:1096). **SBD**.
- The needle close: what returns is SAME truth, decided by the one Quot.sound (Fact.SAME).
  → **theorem `selection_sound` (Ep15:362) → `[Quot.sound]`**, via `Fact.SAME` (Ep15:369) + the M17 close
  (Meanwhile17:1139-1155). **SBP** — Act IV's one genuine theorem anchor.
- The dead arm (isFalse→isTrue) is carried but never taken. → `dec_distinct` match (Meanwhile17:1158). **SBD**.

**Ch14. The seam (Meanwhile18 — pass n seeds pass n+1; charge = the loop count)** — *SBD + RI*
- Every class re-instantiated from a completed loop's residue. → ~21 `*_residue` instances (Meanwhile18:29 …
  :1662). **SBD**.
- Charge = the loop count (billed the turns). → `TrueOutput_number` instance, `stress := charge`, `spin charge`
  (Meanwhile18:1792,1849). **SBD** — definitionally true by construction (a noncomputable instance, not a theorem).
- The tape only appends (the revolution ledger). → `TrueOutput_number` tape/spin (Meanwhile18:1849-1876). **RI**
  — a design invariant (law 5), not a proved object.

**Ch15. The trace and the slip (Meanwhile19–20 — the class trace, the slip test, the world's carrier)** — *SBD + RI*
- The class trace (the second tape, one cell per class). → `class TRACED` + ~36 `TRACED_*` (Meanwhile19:11+). **SBD**.
- The slip test: execute up the ladder; the register is internal, never on the tape. → `class EXECUTED_TRACE`
  (Meanwhile20:12), `seamExit : SlipVerdict` (Meanwhile20:569). **SBD** — slip decided by the pair's own decTruths
  (Classical-free).
- The carrier is the world's selector (report, don't force). → `EXECUTED_TRACE.register_value` + `seamExit`
  (Meanwhile20:12,583). **RI** — a design stance (tange/funge, law 6), not proved.

**Ch16. The number in [charge, curvature] (Meanwhile21 — three trips; mass = second difference = strain)** — *SBD + SBP(anon)*
- Three trips f0/f1/f2 (null / threshold / response). → `trip0/trip1/trip2`, `strainRead` (Meanwhile21 defs). **SBD**.
- ⚠ **UNPINNED (proved-but-anonymous):** trip1 head = `.one`, trip2 head = `.rest` (mass surfaces at f2). →
  three anonymous `example`s (`rfl` / `simp;cases;trivial`) in Meanwhile21 → footprint `[propext, Quot.sound]`.
  **SBP but unpinned=true** — the proof obligations genuinely discharge, but they are `example`s, not named
  theorems, so there is no citeable name. `-- CHOICE (unpinned-16)`: **recommend converting these to named
  theorems** (`mass_surfaces_at_f2` etc.) so the payoff is citeable; flagged for the operator/code lane.
- Mass = second difference = strain; inertial-response = gravitational-strain (equivalence principle, code-carried).
  → `theNumber` `upper := strainRead …` (Meanwhile21), `BracketedNumber`. **SBD** — a definitional identification
  (the .rest slot read twice); the .rest-surfacing is the anon `example` above. NOT a named equivalence-principle
  theorem.
- The number built in the bracket [charge, curvature]. → `structure BracketedNumber`, `theNumber` (Meanwhile21). **SBD**.

---

## ACT V — THE NAMING & THE PREDICTED SPLIT (the electron named; the neck stuck out)

**Ch17. The four faces (Meanwhile22 — one number, four faces, three costs)** — *SBP + SBD + RI*
- One number read four ways at three costs; the recovery closes exactly. → **theorem `recover_theNumber`
  (Meanwhile22:49) → `[propext, Quot.sound]`**. SBP (rfl; proves the recovery closes).
- charge/mass faces = free projections (n.lower / n.upper). → `chargeRead`/`massRead`/`recover`
  (Meanwhile22:25,27,39). **SBD**.
- The phase face = a DECISION (matches the fact's decidability) — the QPhase two-fold ±. → `inductive QPhase`
  (Meanwhile22:14), `phaseRead` (Meanwhile22:29). **SBD** — the ± content is definitional (rfl equates the face
  with itself, not a proved sign).
- The PHASE face IS the −i direction. → `QPhase` + `imaginary` carrier (Meanwhile22:14,70). **RI** — no complex
  value in code; seeds Ch20.

**Ch18. The cost of the needle (the heartbeat — the elaboration pulse; binding energy) [measured]** — *RI (mostly)*
- The needle's fourth face realized as a MEASUREMENT (a real, reproducible elaboration pulse). → elab command
  `register_heart_rate` → `theHeartRate : Nat` (Meanwhile22:126,134), `#eval` (Meanwhile22:140). **RI** — `[measured]`,
  no theorem (a generated Nat, no proposition/footprint). Honestly graded.
- ⚠ **UNPINNED:** "binding energy — the whole lighter than its parts." → **no code object** (unpinned=true);
  closest is `theHeartRate` (the pulse = the cost). `-- CHOICE (fork-b, unpinned-18)`: see Fork (b) — this
  chapter is the weakest/most self-referential in Vol 1; **kept thin here (my guess); flagged for Kodo to
  re-rule to Vol 3.**

**Ch19. Named by counting, not fiat (NamingClose — the pigeonhole) [the naming]** — *SBP*
- Finiteness FORCES the electron: δ² forced into box 1 (the electron), no other. → **theorem `the_naming`
  (NamingClose:266) → `[propext, Quot.sound]`**, via `finiteness_forces_electron` (NamingClose:251, `[propext]`)
  + `recovered_ne_value` (NamingClose:256). SBP — the type-level (distinguishability-CLASS) box identity;
  "electron" (charge −1) is the READING of box 1.
- The pigeonhole: an infinite tower over a finite representation must wrap (the loop's WHY). → **`naming_pigeonhole`
  (NamingClose:60) → `[propext, Quot.sound]`**, `naming_tower_wraps` (NamingClose:85, `[propext, Quot.sound]`),
  `boxCount_is_two` (NamingClose:91, `[] no axioms`). SBP — native Fin/omega, no Mathlib/Classical.
- box 1 (electron) ≠ box 0 (value); box 0 pinned by the fixed point. → `fixed_point_pins_zeroth` (NamingClose:202,
  `[propext]`), `recovered_ne_value` (NamingClose:256). SBP.
- The two indistinguishability premises hold. → `gateaux_indist_frechet` (NamingClose:104, `[propext]`),
  `universe_indist_tensor` (NamingClose:126), `naming_collision` (NamingClose:173, `[propext, Quot.sound]`),
  `anticheat_reduced_ne_sameS` (NamingClose:180). SBP.
- The selected collision is an instance of the generically forced wrap. → `selected_wrap_is_instance`
  (NamingClose:223), `generic_wrap_exists` (NamingClose:230), `cubic_linearizes` (NamingClose:279,
  `[propext, Quot.sound]`). SBP.
- ⚠ Note: `Meanwhile24` is EMPTY (0/0) — the naming lives in `NamingClose.lean`, not Meanwhile24. Corrected pin.
- **Aside (folded from the deferred heartbeat):** naming the electron cost a real, measured elaboration pulse
  (`register_heart_rate`/`theHeartRate`, Meanwhile22) — the machine paid to force its needle.
- ⚠ **Reveal-fence anchor: the naming is NAMED here (Ch19); mechanism (needle) was Ch11.**

**Ch20. The imaginary bounce — the predicted split (Ep83 baseline flip + the imaginary carrier)** — *SBP + RI*
- The split IS the SIGN of the per-pair δ²; ±1 proved on the single floor (electron −1 flat, positron +1 tilted).
  → **theorem `baseline_relative_flip` (Ep83:139) → `[] (no axioms)`**, `electron_over_flatPath`/
  `positron_over_tiltedPath` (Ep83:130,134). SBP — **the ONE proved ±1 floor the prediction is forced from.**
- The apparatus resolves AT MOST THREE tags (the pigeonhole from inside). → `apparatus_resolves_at_most_three`
  (Ep83:163) → `[propext, Quot.sound]`, `four_tags_collide` (Ep83:151, `[propext, Quot.sound]`). SBP.
- Measurement framing = the invariant: whole−parts relvel = δ². → `pairRelVel_eq_secondVariation` (Ep83:78)
  → expected ≤`[propext]` (axiom-free/omega; decl in an inner scope — verify exact name at lock). SBP.
- The `imaginary` carrier IS the −i axis; at crossed 90° the amplitude bounces ×(−i) (Malus/de Broglie). →
  rides the `imaginary` CarrierProcess parameter (Meanwhile21:223 / Meanwhile22:70). **RI** — no ×(−i) rotation
  in code; a Vol-2 reframe.
- ±1 = (−i)²; the four-fold {1,−i,−1,i} is the spinor 4π; the split is Vol 1's predicted constant. → rides
  `baseline_relative_flip` + `QPhase`. **RI**. ⚠ **Over-claim watch:** "the spinor is the √ of the split, not a
  mere reading" OVER-CLAIMS — no √/spinor object; keep RI. Orientation handed to the reader; the physical
  constant is RESERVED `% CHOICE (operator)`.

**Ch21. The universal operator (the capstone — tensor ⊕ Fréchet)** — *SBP + RI*
- The universal operator decomposes into exactly two terms (0th = universe tensor / box 0 ⊕ 1st = Fréchet δ² /
  box 1), two distinct classes. → **theorem `the_capstone` (Capstone:49) → `[propext, Quot.sound]`**,
  `capstone_zeroth_is_tensor` (Capstone:37, `[propext]`), `capstone_first_is_frechet` (Capstone:42,
  `[propext, Quot.sound]`). SBP — a DERIVED decomposition.
- The two leading terms exhaust the count (non-degenerate). → `capstone_two_terms_exhaust_the_count` (Capstone:58)
  → `[propext]`. SBP.
- The Fréchet 1st term IS the produced electron. → `capstone_first_is_frechet` + `the_stack_produces_it`
  (Ep52:294), `electronVariation_normal_form` (Ep52:282). SBP (`[propext, Quot.sound]`; electronVariation
  noncomputable but choice-free).
- 0th ⊨ GR, 1st ⊨ Heisenberg (GR on the ±1 holonomy; Heisenberg on the −i residue). → rides the capstone
  theorems. **RI** — ⚠ the Capstone docstring itself says "NEVER a proved unification"; keep the two ⊨ readings
  interpretive-on-code-carriers.

---

## ACT VI — THE READER (the loop handed over)
*The code is AHEAD of the prose here — the dictionary is theorem-dense and almost entirely AXIOM-FREE.*

**Ch22. The physics read off the count — the graded dictionary** *(outline collision "21" → 22)* — *SBP + RI*
- charge = the loop count; funges/cranks partition the whole gauge. → **`funges_and_cranks_partition` (Funge:30,
  `[propext, Quot.sound]`)**, `gauge_funge_crank_partition` (Ep87:35, `[]`), `electron_never_cranks` (Ep87:26,
  `[]`), `pair_cranks_once` (Ep87:31, `[]`). SBP.
- gravity = curvature = holonomy = ±1 (signed loop residue; 0 on open paths; frame-relative). → **`holonomy_loop_is_charged`
  (Ep84:66, `[] no axioms`)**, `holonomy_open_is_trivial` (Ep84:60, `[]`), `detection_is_frame_relative`
  (Ep84:87, `[]`), `baseline_relative_flip` (Ep83:139, `[]`). SBP. The WORD "gravity/curvature" is the graded
  reading on a real holonomy theorem (Ep84 header fences: MEASURED not derived, no real Aharonov-Bohm/QED).
- gauge = the label lines (35 gates funge/matter, 1 tanges/antimatter at MAGNITUDE; the tally closes). →
  `matter_off_the_gauge` (Ep88:22, `[]`), `antimatter_off_the_gauge` (Ep88:27, `[]`), `split_tallies_the_gauge`
  (Ep88:36, `[]`), `gauge_closes` (Ep90:31, `[]`), `superconducting_pair_admits_one_positron` (Ep90:21, `[]`). SBP.
- the split is counted: native baseline reads 0 antimatter, nonzero matter (pure matter); antimatter only once
  tilted. → `the_split_counted` (Ep85:59, `[]`), `native_antimatter_is_zero` (Ep85:47, `[]`),
  `antimatter_needs_asymmetry` (Ep85:54, `[]`). SBP — ⚠ a CONDITIONAL falsifiable count over the trial (Ep85
  header: does NOT derive baryogenesis/CP/Sakharov; "MEASURED, not derived"; one positron over the symmetric
  trial breaks it). Say "the prediction is proved" ONLY at this count-over-the-trial ceiling.
- mass = second difference = strain (strain real iff charge). → `strain_iff_residue` (Ep52:212,
  `[propext, Quot.sound]`), `electron_strain_iff_charge` (Ep52:262). SBP — ⚠ real object but UPSTREAM (Ep52,
  Act IV/V), re-cited into the VI dictionary.
- confinement = color/flavor = whereof one cannot speak (saying/showing = funge/tange). → rides `fungeBit`
  (Funge:19) + the corridor band. **RI** — the one dictionary entry with no theorem of its own (graded).

**Ch23. Choice-free but for the one grant** *(outline "22" → 23)* — *RI(footprint) + SBP + SBD*
- The build is `[propext, Quot.sound]` end to end (choice-free), verified off `#print axioms`. → a claim ABOUT
  the footprint (the corpus), `AXIOM_LEDGER §0/§3` build-confirmed. **RI** — its truth is the footprint. ⚠ **ONE
  exception:** `band_covers` (Ep92, Ch25) carries `Classical.choice` as an `omega` TACTIC artifact (hand-proof
  axiom-free) — the "choice-free" banner needs an asterisk on that single decl. `% CHOICE (band-omega)`.
- The one needle: exactly one sanctioned `Quot.sound`. → **`selection_sound` (Ep15:362) → `[Quot.sound]`**. SBP.
- The one grant: the oracle = the law of motion = the axiom of choice in physical form. → **`axiom
  eulerLagrangeOracle` (Ep19:109)**, consumed by `noncomputable def residue`. **SBD** — a declared axiom, not a
  theorem; the AC=oracle is the author's reading. Reach = Ep19–26 residue family ONLY; the Act-VI dictionary
  theorems do NOT touch it (they are axiom-free/`[propext,Quot.sound]`).

**Ch24. The construction is forcing** *(outline "23" → 24)* — *SBD + SBP + RI*
- Cohen: finite conditions ordered by extension with a dense-decides property (the forcing signature). →
  `structure FiniteCohenUpToEpsilon` + `dense_decides` (Ep61:266,282), `splineCondition_cohen_up_to_epsilon`
  (Ep61:304). **SBD** — the forcing POSET, built as a structure.
- The finite analogue is PROVED (Cauchy up to ε over a countable Cohen ledger). → **`cohen_cauchy_up_to_epsilon`
  (Ep61:326) → `[propext, Quot.sound]`**, `finiteCohen_countable_up_to_epsilon` (Ep63:66, `[propext, Quot.sound]`),
  `finiteCohen_boundary_radiation_closeout`/`_gauge_residue_closeout` (Ep64:34,86). SBP.
- The construction recognizes itself as the forcing it has been (the REVEAL); literal set-theoretic forcing NAMED,
  not claimed. → rides the FiniteCohen structure. **RI** — no generic-filter/independence theorem; a finite,
  ε-bounded, countable analogue. ⚠ **Reveal-fence anchor: forcing NAMED here (Ch24); the body stays silent on
  "axiom of choice" until this chapter.**

**Ch25. The reader is the final apparatus** *(outline "24" → 25; the close)* — *SBP + SBD + RI*
- The band/MAGNITUDE gate covers everything (floor/ceiling squeeze read as a COVERING). → **theorem `band_covers`
  (Ep92:53) → `[propext, Classical.choice, Quot.sound]`** ⚠. SBP — proves COVERAGE by `∨` (omega), NOT
  exclusivity; docstring already softened "trichotomy"→"covers" (A.8). ⚠⚠ **the SOLE decl in the corpus carrying
  `Classical.choice` — an `omega` tactic artifact (hand-proof axiom-free); flag on every "choice-free" claim.**
- You-the-reader is asked each class's own question (AtreyuProcess, the tanging question at MAGNITUDE). →
  `youTheReader_asked`/`did_this_whelm?`/`did_this_distinguish?`/`did_this_rise?` (Ep93:65,54,48,59 — **all
  defs; Ep93 = 0 theorems**). **SBD** — Prop-valued questions, never DECIDED (confirms A.9: the reader = the
  predicates it exposes).
- ⚠ **UNPINNED (the honest gap):** "the reader is the final apparatus the construction can address but not build;
  Q.E.D. as gerundive." → **no code object** (unpinned=true); the design stance/close. BUT the orientation-handed-
  over half IS pinned: `detection_is_frame_relative` (Ep84:87) + `baseline_relative_flip` (Ep83:139) prove WHICH
  sign is "matter" is the reader's frame, not the construction's. `% CHOICE (operator)` — the close + the
  physical constant are the operator's.

---

## The 3 refinement-note forks — resolved (tange→guess→MARK)

**(a) Act II granularity — 4 chapters vs 5–6. → KEEP 4. `% CHOICE (fork-a)`.**
Deciding characteristic (tange): does the extra split carry a *build-real* distinction? NO — Act II is
DEFINITIONAL end to end (Ep2–6 have **zero theorems**), so there is no theorem-cluster forcing a chapter
boundary; granularity here is a narrative dial, not a build-forced one. The 4 chapters are coherent concept
groups (clock/repeat · numeric/Turing · physical/Chaitin/slip · presence/gauge/value). The tange's characteristic
(a real extra distinction) is not real → the funge (keep 4, bag the classes by concept) wins. **Kept 4.**

**(b) Heartbeat (ch18) + capstone (ch21) — Vol 1 or Vol 3? → capstone Vol 1; heartbeat Vol 1 (thin), FLAGGED.
`% CHOICE (fork-b)`.** Series division: Vol 1 = the construction; Vol 3 = it reading its own source.
- **Capstone → Vol 1 (Act V ch21 peak).** It is the construction's built SUMMIT (`the_capstone`,
  `[propext, Quot.sound]`, a proved box-decomposition ARTIFACT). Double-ownership check: the Vol-2
  capstone-rethread (fidelity B.1) was SKIPPED for the Vol-2 PDF, so the capstone is NOT in shipped Vol 2 → no
  conflict. The two ⊨ readings stay interpretive (the docstring forbids "proved unification"). **Confirmed Kodo's
  lean.**
- **Heartbeat → kept thin in Vol 1 (ch18), but this is the ONE fork I'd accept you re-ruling to Vol 3.** It is
  the weakest chapter (0 theorems, `[measured]`, 1 genuinely-unpinned claim — the binding energy). Argument for
  Vol 1: it is the "cost of forcing the needle" beat the naming story wants, and it is a construction-cost fact,
  not the deep reflexive self-source-reading that defines Vol 3. Argument for Vol 3: a reflexive self-measurement
  (the elaborator timing itself) is exactly "it reading its own source." **My guess: keep thin in Vol 1 (or fold
  the one real point — the measured elaboration pulse — into Ch19 as an aside, dropping ch18 → 24 chapters).
  Flagging for your rule: KEEP-as-ch18 (25 ch) vs DEFER-to-Vol-3 (fold the aside, 24 ch).**

**(c) Double-read reveal fence — preserved. `% CHOICE (fork-c)`.** Mechanism shown before it is named:
**needle at Ch11** (`selection_sound` shown) → **naming at Ch19** (the electron named) → **forcing named only at
Ch24** (the last act), and **the body stays silent on "axiom of choice" until Ch24**. The renumber preserves the
ordering (11 < 19 < 24, all mechanism-before-name). Fence chapter numbers MARKED at Ch11 / Ch19 / Ch24.

## Series-preface seam (Stage-3, flagged not authored)
The series naming-preface already exists (`books/experimentation/latex/chapters/00-series-preface.tex`, authored
for Vol 2; it prepends for the WHOLE series: Zermelo→Frege→Wittgenstein→Cohen→the instrument, poses the question,
withholds the resolution). Vol 1 will also carry its own Oracle-of-Free-Will preface. **Seam: series-then-volume,
PREPEND-not-replace** (identical to Vol 2's `\input{00-series-preface}` then `\input{00-preface}`). Tange: the
series preface is shared front matter, not re-authored per volume; only Vol 1's own Oracle preface is new. Stage-3
work; flagged here.

## Pin tally
- **~80 load-bearing claims pinned across 25 chapters.**
- **Theorem-backed (SBP):** ~34 (incl. the load-bearing spine — `funges_and_cranks_partition`, `true_eq_false`,
  `selection_sound`, `the_naming`+pigeonhole family, `baseline_relative_flip`, `the_capstone`+family, the entire
  axiom-free Ep84/85/87/88/90 dictionary, `cohen_cauchy_up_to_epsilon`, `band_covers`).
- **Definitional (SBD):** ~30 (the Ep1–6 type tower, the truthCarrier self-hosting, the Meanwhile17–21 backward
  walk, the FiniteCohen poset, `eulerLagrangeOracle`, the Ep93 reader defs).
- **Reading (RI):** ~16 (funge/tange valuation, halting/Chaitin/slip, the −i/imaginary-time/spinor bridge, the
  two ⊨ capstone readings, confinement, the choice-free footprint claim, the close).
- **Genuinely UNPINNED: 3** — (16) trip2 acceptance = proved-but-anonymous `example`s (recommend naming them);
  (18) binding energy = no code object; (25) "reader is the final apparatus / Q.E.D. gerundive" = the honest
  design stance (its orientation-handed-over half IS pinned). All three are expected/honest (code ahead of prose,
  or the deliberate close).

## Escalations for Kodo (rather than guess)
1. **Fork (b) heartbeat placement** — my guess is keep-thin-in-Vol-1; I'd accept a defer-to-Vol-3 rule (→ 24
   chapters). The one placement worth your call.
2. **Ch16 anonymous `example`s** — recommend a small CODE task to convert the trip1/trip2 acceptance `example`s
   into named theorems (`mass_surfaces_at_f2`) so the mass=second-difference payoff is citeable. Your call whether
   that's in-scope for vol1 or a separate code unit.
3. **`band_covers` `Classical.choice` omega artifact** — the one asterisk on "choice-free." Leave as-is (noted) or
   swap `omega`→a hand proof (a tiny code fix) to make the corpus footprint uniformly `[propext, Quot.sound]`.
