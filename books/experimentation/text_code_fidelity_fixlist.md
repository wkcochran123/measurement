# Text↔Code Fidelity — Integrated Fix List (post-triangulation)

*2026-07-05. The extrapolant of three bases: my read, the differently-trained auditor's read, and the
BUILD (`#print axioms`, the tie-breaker). Signal is clean. This is the improved work product. Standing
discipline learned here: **grade axioms off the build, never off a code comment** (a comment is a label
that drifts; the build is the count).*

## A. CLEAR FIXES → Kodo/Podo fidelity lane (fires AFTER the coda pass converges + is committed)
Each is a gated unit. Most are fences/re-anchors/softens — the honest-under-claim direction held.

1. **Cohen forcing → the finite analogue.** Prose must claim only finite `CohenUpToEpsilon`, not literal
   set-theoretic forcing; name it only at the reveal (Ch29). [converged: mine #12 + D-006]
2. **Electron = second variation: re-anchor + "model, not lab."** Re-anchor stale `SECOND_VARIATION` /
   `ELECTRON_MODEL` to `the_naming` (NamingClose) / `threeRung_boundary_secondVariation_eq_electron`
   (Ep75); keep the reached-for fence where designed; say model electron, not lab electron.
   [converged: mine #4/#8 + D-002/D-003/D-012]
3. **NS / Einstein → fence to the finite three-rung shape.** Claim only the finite boundary/residue/
   obstruction shape; fence the literal-continuum NS/Einstein language. [converged: mine #5 + D-011]
4. **Commutator → same finite fence.** `finiteGauge_successor_commutator_residue_theorem` (Ep64) proves
   the FINITE commutator residue; fence the literal `[x,p]=iℏ` continuum. [resolved ⚠#3]
5. **Spinor → a reading, not a separate proof.** No spinor/2π theorem; it reads the general ±1
   (`baseline_relative_flip`), coda-only. Frame as a reading. [resolved ⚠#4]
6. **Bell `|S|≤2` → soften to the qualitative locality no-go.** No CHSH theorem in `Measurement/`; only a
   qualitative Experiments exemplar. Say the no-go is proved; the number and 2√2 are name-only/
   experimental. [mine #1]
7. **Baryon asymmetry → retreat to native-baseline / sign-convention.** Ep82/83 explicitly disclaim
   baryogenesis/CP/Sakharov/SM. [D-005]
8. **Band "complete/trichotomy" → "covers."** `band_covers` proves coverage by disjunction, not
   exclusivity. [D-007] (or build exclusivity — see B.4)
9. **Reader "asked every question / final apparatus" → the predicates it exposes.** Ep93 has three
   predicates + a conjunction, not reader performance. [D-008]
10. **Color/flavor confinement → interpretive (saying/showing), not proved.** Data fields + phase facts,
    no confinement theorem; the unreadability is the interpretation. [D-010]
11. **Meanwhile17 doc → the built (no-sorry) state.** Vol 1 outline/study describe the old 37-sorry
    state; Meanwhile17 builds clean. [D-001] (Vol 1 docs)
12. **D-004 comment-sweep (CODE).** Correct every stale "expect/reports `Classical.choice`" comment
    (Ep46/50/52/53/54–57/81–82) to the build-true footprint. Build-verify each file first. The build is
    choice-free (`[propext, Quot.sound]` / no-axioms across the core); the one real axiom is the declared
    `eulerLagrangeOracle`, NOT `Classical.choice`. [List-3 resolution]

## B. OPERATOR SIGN-OFF (you + beastmaster) — genuine forks, NOT auto-queued
1. **Capstone rethread (Vol 2, structural).** `the_capstone` is built (Capstone.lean) → Parts IV+V can be
   re-rooted as the two leading terms. Big doc restructure + interpretive-grade discipline. Operator call.
2. **Flavor / "at most three" promote.** `apparatus_resolves_at_most_three` (Ep83) is proved — but verify
   scope (generation-count claim vs narrower tag result) before promoting the conjecture.
3. **Ep93 ↔ Ep92 integration (CODE).** Ep93 calls the old `whelmed?`; wire it to Ep92's band (code) or
   fence the claim (doc). Build-or-retreat.
4. **Band exclusivity.** Want the trichotomy? Build pairwise-exclusivity (code); else soften (A.8).

### Section B decisions (fidelity lane, tange→guess→MARK; Podo turn 40, Kodo-gated turn 40)
- **B.1 (capstone rethread) — SKIP for the PDF; DEFERRED.** `% CHOICE (B.1)`: the book is coda-complete +
  coherent (354pp, builds, the whole arc lands to the Ch30 verdict). Re-rooting Parts IV+V around the built
  `Capstone.lean` as the two leading terms is a STRUCTURAL enhancement, NOT a coherence requirement — deferred to
  a future structural pass. No book edit. (No incoherence found that the rethread would fix.)
- **B.2 (flavor / "at most three" promote) — NO PROMOTION; keep interpretive.** `-- CHOICE (B.2)`: Ep83
  `apparatus_resolves_at_most_three` proves the NARROWER tag-resolution result — `¬ ∃ a b c d, [tags pairwise
  distinct]` via `tag_lt_three` (pigeonhole: at most three distinct tags) — NOT the physics generation-count
  ("exactly/at most three generations"). The book makes NO "three generations / at most three families" claim
  (grep-clean). So nothing to promote and nothing to fence: generation-count stays interpretive/conjectural,
  exactly as the code's scope warrants. No edit.
- **B.3 (Ep93 ↔ Ep92 integration) — DEFER; off the Vol2-PDF path.** `-- CHOICE (B.3)`: Ep93's `did_this_whelm?`
  calls `length.whelmed?` (the Ep6 class interface), not Ep92's band `Reader.whelmed?`. NO book prose depends on
  Ep93/Ep92 or the `whelmed?` wiring (grep-clean of the chapters). Device-internal fork with no PDF impact — the
  claim is fenced by A.9 (Ep93 = the three predicates + conjunction it exposes) and the wiring is deferred. Build
  the wire-to-Ep92 only if something later needs it.
- **B.4 (band exclusivity) — DONE via A.8** (softened to coverage; disjointness true-but-unbuilt noted, Ep92
  docstring, commit 1599767).

## C. RESOLVED — NO ACTION (backed / aligned; my false-positive gaps, banked)
- #2 shell zero-force → `threeRung_interiorCharge_zero` (Ep54). Backed.
- #9 five loop residues → readings of one ±1 holonomy; fine as framed.
- #10 positron iff, #11 NS-fence-holds, #12 forcing-at-Ch29 → backed/aligned.

## D. WHERE I WAS WRONG (the yield of the different basis + the build)
1. **D-004 choice-free** — carried it unverified, then mis-adjudicated the auditor's flag to a doc-fence
   trusting the *comment* over the *build*. Build: choice-free is true; comments lie; fix is code (A.12).
2. **#5 Einstein** — graded "promote the doc" when the correct call is "fence to the finite shape" (A.3).
3. **#2 shell** — flagged as a ⚠gap; `threeRung_interiorCharge_zero` backs it. Kernel miss.
4. **#3 commutator** — flagged as a ⚠gap; `finiteGauge_successor_commutator_residue_theorem` backs it.
   Kernel miss.
(Mirror: **D-003** is where the AUDITOR was wrong — it missed `the_naming`; folded into A.2.)
