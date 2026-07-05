# Vol 2 Text-vs-Code Fidelity Audit — Brief for the Independent Auditor

*Hand this to the outside adversarial environment. It is self-contained. The briefing IS the ballgame:
the last audit failed not from a weak model but from excerpt-sampling (it missed all 582 theorems but
~14, and reported the capstone unbuilt when it is proved). Follow the METHOD exactly.*

## Mission
Produce an EXHAUSTIVE punch chart: every claim in the book
(`books/experimentation/latex/chapters/01.tex`–`30.tex`) checked against what the proof
(`device/Measurement/*.lean`) actually supports. One row per claim. Output in the exact schema below so
it imports cleanly.

## The stance you audit against (the rubric)
The book is "proof-backed prose." Every effect is graded onto exactly one FLOOR, and the discipline is
to claim that floor and never more:
1. **FINITE COUNT OBLIGATION** — a finite count/theorem, the world's.
2. **SMOOTH-SHADOW ANALOGY** — the continuum as a limit the count approaches, explicitly "ours to draw,"
   NOT the world's.
3. **NO-GO WALL** — an impossibility, the world's refusal.
4. **NAME-ONLY** — the physics is named; the model claims only the label; the mechanism outruns it.
Plus **PROVED / DERIVED** for device-level results the Lean code actually establishes.

## What is a DELTA — and what is NOT
A delta = the PROSE'S GRADE ≠ what the CODE SUPPORTS. Types:
- **OVER-CLAIM** — prose says PROVED/DERIVED but the code has no theorem, or only a weaker/qualitative
  one. THE DANGEROUS KIND.
- **LAG** — the code proves something the prose holds softer (name-only / conjectured / "not built").
  Often a DESIGNED FENCE (the book deliberately withholds a reveal). Flag it, but mark
  `designed-fence?` in the Note for adjudication — do not assume it is an error.
- **GRADE-MISMATCH** — both have it, different grades.
- **NONE** — aligned (still record it for the strong-grade claims, so we know it was checked).

**NOT a delta:** a NAME-ONLY or SMOOTH-SHADOW claim with no code theorem. These do not claim code
backing — they explicitly say the physics is named/shadowed. **Do not flag name-only/shadow as
over-claims.** This is the most common false positive; do not make it.

## METHOD — mandatory, in order (the last audit died skipping step 1)
1. **ENUMERATE ALL CODE THEOREMS.** Run `grep -rnE "^theorem |^lemma " device/Measurement/*.lean` —
   582 of them. Cross-check against the pre-generated ground truth:
   `books/experimentation/text_code_theorem_groundtruth.txt`. NEVER excerpt-sample the code.
2. **ENUMERATE ALL PROSE CLAIMS.** Read every chapter `01.tex`–`30.tex` end to end. For each claim,
   record its grading phrase VERBATIM (e.g. "proved," "the finite theorem," "a smooth shadow," "claims
   only the name," "inadmissible") and its line number.
3. **MATCH.** For each prose claim, find the code theorem that backs it (by name/statement) or record
   `NONE`. `NONE` for a PROVED-graded claim is the key finding.
4. **GRADE THE DELTA** per the rubric.

## Known ground truth — VERIFY, don't trust; these are the traps the last audit failed
- **The CAPSTONE IS BUILT** — `Capstone.lean`: `the_capstone`, `capstone_zeroth_is_tensor`,
  `capstone_first_is_frechet`, `capstone_two_terms_exhaust_the_count`. Do NOT report it unbuilt.
- **Einstein field equations PROVED** — `Episode75:215 threeRung_einstein_field_equations_hold`.
- **Electron = second variation PROVED** — `Episode75:192 threeRung_boundary_secondVariation_eq_electron`;
  **the naming** — `NamingClose:266 the_naming`; **two-electron bridge** —
  `ElectronBridge:51 two_electrons_are_one_particle`; **"at most three"** —
  `Episode83:163 apparatus_resolves_at_most_three`.
- **±1 holonomy** — `Episode83:139 baseline_relative_flip` (flat = −1, tilted = +1). The FIVE "proved
  loop residues" in the book (echo Ch05, Bragg Ch15, Dirac Ch17, Sagnac Ch20, positron Ch18) mostly READ
  this one mechanism. **Flag only if a chapter claims a SEPARATE proof it does not have.**
- **Navier–Stokes** — `Episode75:223 threeRung_navierStokes_balance` is a finite ACCOUNTING
  (forcing = transport + pressure + …), NOT a solution. The book's NS fence (unsolved) is therefore
  CORRECT — do not report it as solved.
- **Forcing** — named at `29.tex:138` (Cohen forcing); the body NEVER says "axiom of choice"
  (confirm this holds). The earlier "Ch22-23" mandate was a stale number; forcing lives at Ch29.
- **The one known OVER-CLAIM candidate** — **Ch14 Bell**: prose grades `|S| ≤ 2` as PROVED, but there
  is NO CHSH/Bell theorem in `Measurement/`; only `Experiments/TheBellAspectTests`, a QUALITATIVE
  locality no-go that explicitly disclaims "no CHSH bound, no expectation values." Confirm and grade.

## OUTPUT SCHEMA — produce EXACTLY this (for clean import)
One markdown table, one row per prose claim, every chapter covered:

| # | Ch (NN.tex) | Doc claim (short) | Doc grade phrase (verbatim) | Doc line | Code theorem (name) or NONE | Code file:line | Delta {OVER/LAG/MISMATCH/NONE} | Confidence {high/med/low} | Recommendation {fix-doc/fix-code/keep} | Note |

Include `NONE`-delta rows for every strong-grade (PROVED/DERIVED) claim you verified as backed — absence
of a row is indistinguishable from a skipped claim, and skipping is the failure mode.

## DO NOT
- Do not excerpt-sample the code — enumerate all 582.
- Do not grade NAME-ONLY or SMOOTH-SHADOW as over-claims.
- Do not treat a designed fence (a withheld reveal) as a defect — flag LAG + `designed-fence?`.
- Do not invent a backing theorem to make a claim "match" — `NONE` is a valid, important result.
- Do not trust the two prior agent ledgers — they under-reported by ~40×.

## After it returns (the import path — for our side, not the auditor's)
The schema above imports into `books/experimentation/text_code_punch_chart.md`. On import the beastmaster
adjudicates each row against the discipline (killing name-only false positives, confirming designed
fences), then routes: `fix-doc` rows → Kodo/Podo as gated body/coda edits; `fix-code` rows → the device
track; `keep` rows → closed. Three independent readings triangulated: the code (ground truth), the book
(this auditor), the discipline (beastmaster).
