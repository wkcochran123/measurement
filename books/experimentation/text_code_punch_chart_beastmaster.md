# Text vs. Code — Beastmaster's Committed Grading (the first Richardson point)

*2026-07-05, committed BEFORE seeing the differently-trained auditor's read, so the two points are
independent. Low-confidence rows are marked `LOW` — those are MY likely null-space spots, where the
other basis matters most. Ambiguous gaps (my read finds no clean code backing AND it is not a
self-fence) are marked `⚠GAP` — the frontier the last turn named: build-code-or-retreat-book, immediate.
Grades against the 582-theorem ground truth (`text_code_theorem_groundtruth.txt`), not the drifted agent
ledgers.*

## Method note
Self-fencing claims (NAME-ONLY / SMOOTH-SHADOW / NO-GO / FINITE-COUNT that do not assert device proof)
are `NONE`-by-construction — they claim no code backing. I grade the DEVICE-LEVEL claims (prose says
"proved" / "a finite theorem" / "derived") against the theorem list, plus the fences and the lags. That
is the comparison surface where disagreement and gaps live.

## The committed rows

| # | Ch(.tex) | Claim | My grade of code backing | Code theorem / NONE | Delta | Conf | My call |
|---|----------|-------|--------------------------|---------------------|-------|------|---------|
| 1 | 14 | Bell local bound `\|S\|≤2` "proved (counting no-go)" | **NO device theorem**; only Experiments qualitative no-go | NONE (Measurement/) | **OVER** | high | fix-doc (soften) or fix-code (build CHSH) |
| 2 | 08 | shell interior zero-force "exactly, proved (symmetry)" | unclear if device-proved or a prose math fact | ? (none found) | **⚠GAP** | LOW | build-or-retreat — verify |
| 3 | 13 | Heisenberg commutator "[x,p], proved (foundational)" | unclear the commutator is a code theorem vs prose | ? | **⚠GAP** | LOW | build-or-retreat — verify |
| 4 | 17 | Dirac/spinor `±1` "proved (finite theorem)" | memory says spinor coda-only; book may grade proved | ? (baseline_relative_flip is ±1 general) | **⚠GAP** | LOW | verify: is spinor a separate proof or a reading? |
| 5 | 21 | gravity = curvature "name-only" | code PROVES Einstein field eqns (three-rung) | threeRung_einstein_field_equations_hold (Ep75) | **LAG** | high | fix-doc (may promote) / keep floor — my call |
| 6 | ~19/30 | 3-up/3-down flavor "conjectured / not claimed" | code proves "at most three" | apparatus_resolves_at_most_three (Ep83) | **LAG** | med | fix-doc (promote, verify scope) |
| 7 | ~IV–V | GR+QED unification "not claimed" | code built the capstone | the_capstone (Capstone.lean) | **LAG** | high | fix-doc (rethread due, interpretive grade) |
| 8 | 17/18/30 | electron "named, not built" | code PROVES electron=second-variation, bridge | the_naming, threeRung_boundary_secondVariation_eq_electron, two_electrons_are_one_particle | **LAG (designed fence)** | high | keep — but Ch29 reveal can now land the built naming |
| 9 | 05/15/17/20/30 | five "proved loop residues" | one ±1-holonomy mechanism read across contexts | baseline_relative_flip, threeRung_boundaryCharge_one | **SOFT** | high | keep if framed as readings; fix-doc if any claims a separate proof |
| 10 | 18 | positron coincidence iff, converses | backed | detects_positron_over_tilt, no_positron_over_flat | NONE | high | keep |
| 11 | 11/22 | Navier–Stokes fenced unsolved | code NS is finite balance, not a solution | threeRung_navierStokes_balance (Ep75) | NONE (fence holds) | med | keep — confirm prose never reads it "solved" |
| 12 | 28/29 | forcing named; body silent on "axiom of choice" | forcing at 29.tex:138; finite-Cohen backed | cohen_cauchy_up_to_epsilon (Ep61) | NONE | high | keep (Ch29 confirmed) |
| — | meta | agent chapter NUMBERS drift (e.g. Cantor–Gödel–Cohen graded "Ch28"; it is 29.tex) | — | — | **process** | high | trust .tex filenames, not ledger numbers |

## My flagged frontier (⚠GAP — address immediately, don't defer)
- **Row 1 (Ch14 Bell)** — the one I'm CONFIDENT is an over-claim. Fork: soften the grade, or build a CHSH
  theorem. My call: fix-doc.
- **Rows 2–4 (Ch08 shell / Ch13 commutator / Ch17 spinor)** — the three I'm NOT confident on. My read
  finds no clean device theorem behind a "proved" grade, but my confidence is LOW — this is precisely
  where my null basis may be blind (a theorem I couldn't map, or a prose "provable" I misread as a device
  claim). **These are the rows I most need the differently-trained read to arbitrate.** If it also finds
  no backing → confirmed gaps (build-or-retreat). If it finds a theorem I missed → my kernel, canceled.

## Coverage honesty (my null space, stated)
This covers the DEVICE-LEVEL and fence claims — the deltable surface. It does NOT exhaustively grade
every finite-count/shadow claim in all 30 chapters (those are NONE-by-construction, but I have not
line-verified each). Where the outside read grades a claim I did not cover, that gap in MY coverage is
itself a null-space signal — a claim my basis did not think worth checking. Compare on that too.

## Fair-comparison caveat (raise before sending)
The brief I wrote for the auditor pre-seeds it with some of MY conclusions (Bell=over-claim, capstone
built). That ANCHORS its read toward mine and weakens the independence Richardson needs. For a clean
second point, strip the conclusion-level content from the brief — keep the METHOD, RUBRIC, SCHEMA, and
the method-guards (enumerate-don't-sample; name-only≠over-claim), but REMOVE the specific delta findings
so it reads cold. Then its agreement with this list is signal, not echo.
