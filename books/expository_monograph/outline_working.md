# Measurement (Volume 1) — Working Outline (anchor-pinned to the build)

*Stage-1 deliverable of task `vol1` (bm-vol1-charter), UPDATED per Kodo turn 50 (E1/E2/E3 ruled). Refines
`outline_fresh.md` into a chapter-level working outline with every load-bearing claim pinned to its device code
object + `#print axioms` footprint, graded off the BUILD (never a comment). Ground truth:
`books/experimentation/text_code_theorem_groundtruth.txt` (582 theorems, generated 06a3c5f). Footprints verified
this session via `lake env lean … #print axioms`. Grade key: **SBP** = structure-built-proved (a theorem) ·
**SBD** = structure-built-definitional (a class/struct/def — the tower is built as types) · **RI** =
reading-interpretive (a reading laid on a code carrier).*

## One breath
Build the measurement machine from the first difference; watch it read its own truth, collapse at the summit,
walk back down and close into a loop, and **name the electron by counting** — then stick its neck out: predict
the matter/antimatter split as the square of the imaginary bounce (±1 = (−i)²), and hand the orientation to the
reader. Choice-free but for the one grant the world answers. Vol 1 = the construction; Vol 2 reads the physics
off it; Vol 3 = it reading its own source.

## The payoff stake (graded honestly, off the build)
- **±1 = PROVED.** `baseline_relative_flip` (Ep83:139) = **[] (no axioms)** — `pairDelta2 flat = −1 ∧ tilted = +1`
  by `decide`; forced by the pigeonhole `naming_pigeonhole`/`the_naming` (named-by-counting, not fiat). The
  entire matter/antimatter dictionary is **axiom-free** (Ep84/85/87/88/90 all `[]`). This is the book's spine and
  the cleanest possible grade.
- **−i / imaginary-time / the fourth-root spinor = INTERPRETIVE bridge (MARKED).** No theorem constructs `−i`,
  `(−i)²`, `{1,−i,−1,i}`, or a spinor √. It rides real carriers (the `imaginary` CarrierProcess parameter +
  `QPhase` two-fold + the proved ±1). ⚠ **Over-claim watch:** the outline phrase "the spinor is the √ of the
  split, **not a mere reading**" (fresh l.96) OVER-CLAIMS the build — there is no √/spinor object; keep it RI.
- **The close to the dimensionful physical constant = RESERVED `% CHOICE (operator)`.** Build up to it; do NOT
  invent the constant.
- **Choice-free banner, scoped honestly (`% CHOICE (vol1-E3)`).** The construction's **spine** is
  `[propext, Quot.sound]` + the one declared oracle (`eulerLagrangeOracle`, Ep19). The SOLE `Classical.choice`
  in the corpus is `band_covers` (Ep92) — an `omega`-tactic artifact (hand-provable away), a peripheral coverage
  lemma OFF the spine. So "choice-free but for the one grant" is true of the spine; asterisk the one omega
  artifact honestly (Ch22/Ch24), do not let the banner over-claim on that decl.

## Chapter numbering (forks fixed) — 24 chapters, 6 acts (4 per act)
`outline_fresh` collided at ch21. **Resolution (`% CHOICE (numbering)` + `% CHOICE (vol1-E1)`):** de-collide AND
defer the heartbeat/elaboration-cost chapter to Vol 3 (E1) → **24 chapters, a clean 4 per act**: Act I 1–4, II
5–8, III 9–12, IV 13–16, V 17–20, VI 21–24.

---

## ACT I — THE FIRST DIFFERENCE (the primitive: difference → number)
*Almost entirely the DEFINITIONAL type tower (Ep1, zero theorems); the one theorem is the funge/tange partition.*

**Ch1. Can you tell two things apart? (DISTINGUISHABLE)** — *SBD*
- Distinguishability is the primitive first fact (sameness manufactured later). → `class DISTINGUISHABLE`
  (Ep1:277) over `class Fact` (Ep1:75). **SBD** — a definitional stance, not a proved claim (the one manufactured
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
  Ep61) are downstream (Ch23).
- The residue = the leftover (direction + magnitude). → `RESIDUE.representative?` (Ep1:1148), `inductive Sample`
  (Ep1:1187). **SBD** — proved downstream as `strain_iff_residue` (Ep52, Ch21), a structure here.

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
  act (no distinct imaginary TYPE; seeds the Ch19 bridge).

---

## ACT IV — THE RETURN: THE LOOP CLOSES (the backward walk, BUILT AS STRUCTURE)
*⚠ HONEST-GRADE FINDING: Meanwhile17–21 are STRUCTURE — ~150 defs/instances, and (after E2) exactly ONE named
theorem, `mass_surfaces_at_f2` (Meanwhile21), plus the `selection_sound` anchor at the needle close. "was 37
sorrys, now proved" = 37 typeclass instances now INHABITED (SBD), not 37 theorems. Say "constructed/inhabited,"
not "proved," for the backward walk.*

**Ch13. The backward walk (Meanwhile17 — TrueOutput→DISTINGUISHABLE, the loop home, the needle close)** — *SBD + SBP*
- Every forward crank turned once in reverse; the full tower descended. → 37 `*_backward` instances
  (Meanwhile17:5 … :1096). **SBD** (inhabited, not theorems).
- The loop comes home (re-derives DISTINGUISHABLE, the first fact). → `ADMISSIBLE_DISTINGUISHABLE_backward`
  (Meanwhile17:1096). **SBD**.
- The needle close: what returns is SAME truth, decided by the one Quot.sound (Fact.SAME).
  → **theorem `selection_sound` (Ep15:362) → `[Quot.sound]`**, via `Fact.SAME` (Ep15:369) + the M17 close
  (Meanwhile17:1139-1155). **SBP** — Act IV's needle anchor.
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

**Ch16. The number in [charge, curvature] (Meanwhile21 — three trips; mass = second difference = strain)** — *SBP + SBD*
- Three trips f0/f1/f2 (null / threshold / response). → `trip0/trip1/trip2`, `strainRead` (Meanwhile21 defs). **SBD**.
- **Mass surfaces at f2: the reading-head climbs into `.rest`, the strain-bearing constructor — mass IS the second
  difference. → theorem `mass_surfaces_at_f2` (Meanwhile21:354, NAMED per E2) → `[propext, Quot.sound]`. SBP** —
  the load-bearing mass=second-difference payoff, now citeable (was an anonymous acceptance `example`; target
  build green, footprint unchanged). (trip1's `.one` threshold head stays an anonymous `rfl` example — not
  load-bearing, left as-is.)
- Mass = second difference = strain; inertial-response = gravitational-strain (equivalence principle, code-carried).
  → `theNumber` `upper := strainRead …` (Meanwhile21), `BracketedNumber`. **SBD** — a definitional identification
  (the `.rest` slot read twice); the `.rest`-surfacing is `mass_surfaces_at_f2` (above). NOT a named
  equivalence-principle theorem — that identity is definitional (strainRead reused).
- The number built in the bracket [charge, curvature]. → `structure BracketedNumber`, `theNumber` (Meanwhile21). **SBD**.

---

## ACT V — THE NAMING & THE PREDICTED SPLIT (the electron named; the neck stuck out)
*(The heartbeat/elaboration-cost chapter was DEFERRED to Vol 3 — E1; Act V is now four chapters.)*

**Ch17. The four faces (Meanwhile22 — one number, four faces, three costs)** — *SBP + SBD + RI*
- One number read four ways at three costs; the recovery closes exactly. → **theorem `recover_theNumber`
  (Meanwhile22:49) → `[propext, Quot.sound]`**. SBP (rfl; proves the recovery closes).
- charge/mass faces = free projections (n.lower / n.upper). → `chargeRead`/`massRead`/`recover`
  (Meanwhile22:25,27,39). **SBD**.
- The phase face = a DECISION (matches the fact's decidability) — the QPhase two-fold ±. → `inductive QPhase`
  (Meanwhile22:14), `phaseRead` (Meanwhile22:29). **SBD** — the ± content is definitional (rfl equates the face
  with itself, not a proved sign).
- The PHASE face IS the −i direction. → `QPhase` + `imaginary` carrier (Meanwhile22:14,70). **RI** — no complex
  value in code; seeds Ch19.

**Ch18. Named by counting, not fiat (NamingClose — the pigeonhole) [the naming]** — *SBP*
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
- ⚠ **Reveal-fence anchor: the naming is NAMED here (Ch18); mechanism (needle) was Ch11.**

**Ch19. The imaginary bounce — the predicted split (Ep83 baseline flip + the imaginary carrier)** — *SBP + RI*
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

**Ch20. The universal operator (the capstone — tensor ⊕ Fréchet)** — *SBP + RI*
- The universal operator decomposes into exactly two terms (0th = universe tensor / box 0 ⊕ 1st = Fréchet δ² /
  box 1), two distinct classes. → **theorem `the_capstone` (Capstone:49) → `[propext, Quot.sound]`**,
  `capstone_zeroth_is_tensor` (Capstone:37, `[propext]`), `capstone_first_is_frechet` (Capstone:42,
  `[propext, Quot.sound]`). SBP — a DERIVED decomposition. (Capstone → Vol 1's Act-V peak per E1: built artifact,
  the Vol-2 rethread was skipped → no double-ownership.)
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

**Ch21. The physics read off the count — the graded dictionary** — *SBP + RI*
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

**Ch22. Choice-free but for the one grant** — *RI(footprint) + SBP + SBD*
- The build's SPINE is `[propext, Quot.sound]` end to end (choice-free), verified off `#print axioms`. → a claim
  ABOUT the footprint; `AXIOM_LEDGER §0/§3` build-confirmed. **RI** — its truth is the footprint. ⚠ **`% CHOICE
  (vol1-E3)`: scope the banner to the SPINE.** The ONE exception is `band_covers` (Ep92, Ch24) — `Classical.choice`
  as an `omega` TACTIC artifact (hand-provable away), a peripheral coverage lemma off the spine. Asterisk it
  honestly; the spine's choice-freeness stands.
- The one needle: exactly one sanctioned `Quot.sound`. → **`selection_sound` (Ep15:362) → `[Quot.sound]`**. SBP.
- The one grant: the oracle = the law of motion = the axiom of choice in physical form. → **`axiom
  eulerLagrangeOracle` (Ep19:109)**, consumed by `noncomputable def residue`. **SBD** — a declared axiom, not a
  theorem; the AC=oracle is the author's reading. Reach = Ep19–26 residue family ONLY; the Act-VI dictionary
  theorems do NOT touch it (they are axiom-free/`[propext,Quot.sound]`).

**Ch23. The construction is forcing** — *SBD + SBP + RI*
- Cohen: finite conditions ordered by extension with a dense-decides property (the forcing signature). →
  `structure FiniteCohenUpToEpsilon` + `dense_decides` (Ep61:266,282), `splineCondition_cohen_up_to_epsilon`
  (Ep61:304). **SBD** — the forcing POSET, built as a structure.
- The finite analogue is PROVED (Cauchy up to ε over a countable Cohen ledger). → **`cohen_cauchy_up_to_epsilon`
  (Ep61:326) → `[propext, Quot.sound]`**, `finiteCohen_countable_up_to_epsilon` (Ep63:66, `[propext, Quot.sound]`),
  `finiteCohen_boundary_radiation_closeout`/`_gauge_residue_closeout` (Ep64:34,86). SBP.
- The construction recognizes itself as the forcing it has been (the REVEAL); literal set-theoretic forcing NAMED,
  not claimed. → rides the FiniteCohen structure. **RI** — no generic-filter/independence theorem; a finite,
  ε-bounded, countable analogue. ⚠ **Reveal-fence anchor: forcing NAMED here (Ch23); the body stays silent on
  "axiom of choice" until this chapter.**

**Ch24. The reader is the final apparatus (the close)** — *SBP + SBD + RI*
- The band/MAGNITUDE gate covers everything (floor/ceiling squeeze read as a COVERING). → **theorem `band_covers`
  (Ep92:53) → `[propext, Classical.choice, Quot.sound]`** ⚠. SBP — proves COVERAGE by `∨` (omega), NOT
  exclusivity; docstring already softened "trichotomy"→"covers" (A.8). ⚠⚠ **the SOLE decl in the corpus carrying
  `Classical.choice` — an `omega` tactic artifact (hand-proof axiom-free), off the spine. `% CHOICE (vol1-E3)`:
  the choice-free banner is scoped to the spine; note this asterisk. Optional Stage-3 stretch: swap `omega`→hand
  proof for a uniform `[propext, Quot.sound]` corpus (deferred; must not block).**
- You-the-reader is asked each class's own question (AtreyuProcess, the tanging question at MAGNITUDE). →
  `youTheReader_asked`/`did_this_whelm?`/`did_this_distinguish?`/`did_this_rise?` (Ep93:65,54,48,59 — **all
  defs; Ep93 = 0 theorems**). **SBD** — Prop-valued questions, never DECIDED (confirms A.9: the reader = the
  predicates it exposes).
- ⚠ **UNPINNED (the honest gap — the one that remains):** "the reader is the final apparatus the construction can
  address but not build; Q.E.D. as gerundive." → **no code object** (unpinned=true); the design stance/close. BUT
  the orientation-handed-over half IS pinned: `detection_is_frame_relative` (Ep84:87) + `baseline_relative_flip`
  (Ep83:139) prove WHICH sign is "matter" is the reader's frame, not the construction's. `% CHOICE (operator)` —
  the close + the physical constant are the operator's.

---

## The 3 refinement-note forks — RULED (Kodo turn 50; each MARKED)

**(a) Act II granularity → KEEP 4. `% CHOICE (fork-a)`.** Act II is DEFINITIONAL end to end (Ep2–6 = **zero
theorems**); no theorem-cluster forces a chapter boundary; the 4 chapters are coherent concept groups
(clock/repeat · numeric/Turing · physical/Chaitin/slip · presence/gauge/value). The tange's characteristic (a
real extra distinction) is not real → the funge (keep 4) wins.

**(b) Heartbeat + capstone → capstone Vol 1, heartbeat DEFERRED to Vol 3. `% CHOICE (vol1-E1)` (Kodo-ruled).**
- **Capstone → Vol 1 (Act V Ch20 peak).** Built SUMMIT (`the_capstone`, `[propext, Quot.sound]`, a proved
  box-decomposition ARTIFACT). The Vol-2 capstone-rethread (fidelity B.1) was SKIPPED → not in shipped Vol 2 → no
  double-ownership. The two ⊨ readings stay interpretive.
- **Heartbeat → DEFERRED to Vol 3.** "The proof costs electricity/money" = the machine running its OWN SOURCE =
  Vol 3's subject. It was the weakest chapter (0 theorems, `[measured]`, an unpinned claim). Vol 2's codas already
  seed "charge = what you're billed," so Vol 1 doesn't need it. Its one candidate Vol-1 residue — binding energy
  ("the whole lighter than its parts") — has **no code object (unpinned)**, so per E1 it is **DROPPED** (not given
  a build claim it cannot back), not folded. Result: clean 4-per-act, 24 chapters.

**(c) Double-read reveal fence — PRESERVED. `% CHOICE (fork-c)`.** Mechanism shown before named:
**needle at Ch11** (`selection_sound` shown) → **naming at Ch18** (the electron named) → **forcing named only at
Ch23** (the last act), and **the body stays silent on "axiom of choice" until Ch23**. The renumber preserves the
ordering (11 < 18 < 23, all mechanism-before-name). Fence chapter numbers MARKED at Ch11 / Ch18 / Ch23.

## Series-preface seam (Stage-3, flagged not authored)
The series naming-preface already exists (`books/experimentation/latex/chapters/00-series-preface.tex`, authored
for Vol 2; it prepends for the WHOLE series). Vol 1 will also carry its own Oracle-of-Free-Will preface. **Seam:
series-then-volume, PREPEND-not-replace** (identical to Vol 2's `\input{00-series-preface}` then
`\input{00-preface}`). The series preface is shared front matter, not re-authored per volume; only Vol 1's own
Oracle preface is new. Stage-3 work; flagged.

## Pin tally (post E2)
- **~75 load-bearing claims pinned across 24 chapters.**
- **Theorem-backed (SBP):** ~35 (the spine — `funges_and_cranks_partition`, `true_eq_false`, `selection_sound`,
  `the_naming`+pigeonhole family, `mass_surfaces_at_f2` [NEW, E2], `baseline_relative_flip`, `the_capstone`+family,
  the entire axiom-free Ep84/85/87/88/90 dictionary, `cohen_cauchy_up_to_epsilon`, `band_covers`).
- **Definitional (SBD):** ~28 (the Ep1–6 type tower, the truthCarrier self-hosting, the Meanwhile17–21 backward
  walk, the FiniteCohen poset, `eulerLagrangeOracle`, the Ep93 reader defs).
- **Reading (RI):** ~15 (funge/tange valuation, halting/Chaitin/slip, the −i/imaginary-time/spinor bridge, the
  two ⊨ capstone readings, confinement, the choice-free footprint claim, the close).
- **Genuinely UNPINNED: 1** — (Ch24) "the reader is the final apparatus / Q.E.D. gerundive" = the honest design
  close (its orientation-handed-over half IS pinned). *(The two prior unpinned resolved: ch16 → NAMED
  `mass_surfaces_at_f2` (E2); ch18 binding-energy → deferred to Vol 3 with the heartbeat (E1).)*

## Status
Stage 1 CONVERGED as updated: 24 chapters, every load-bearing claim anchor-pinned + graded off the build; E1
(heartbeat→Vol 3, binding-energy dropped), E2 (`mass_surfaces_at_f2` named + verified), E3 (choice-free banner
scoped to the spine) all applied. Ready for Stage 2 (the budget → `outline_budget_vol1.md`).
