# Text vs. Code — Punch Chart (Vol 2, fidelity audit)

*2026-07-05. Each row is a delta between what the book (`books/experimentation/latex/chapters/*.tex`)
claims and what the proof (`device/Measurement/*.lean`) supports. Decision per row: **fix code**
(build what the doc claims) or **fix doc** (grade to what the code holds) or **keep** (designed fence /
already aligned). Chapter numbers are `NN.tex` filenames (agent ledgers drifted; trust filenames).*

## Headline (the audit's real finding)
The book **under-claims** relative to the code — the code raced ahead and the doc's updates were staged
behind it. The prior "capstone unbuilt / Bell in the proved set" read was on **incomplete agent data**;
the code proves far more than reported. So most deltas are "fix doc to catch up," and there is exactly
**one genuine over-claim** (Ch14 Bell). Confidence: deltas below are VERIFIED against the theorem list +
statements; the "backed/no-delta" universe is high-confidence but not yet exhaustively cross-checked
(a complete row-per-claim pass is a bigger job — offered separately).

## The punch chart

| # | Ch | Document says | Code reality (verified) | Delta | Fix |
|---|----|---------------|--------------------------|-------|-----|
| 1 | **14** | Bell local bound `\|S\|≤2` graded **PROVED** ("counting no-go, the wall no local theory can pass — that much is proved") | **No CHSH/Bell theorem in `Measurement/`.** Only `Experiments/TheBellAspectTests` — a *qualitative* locality no-go exemplar that **explicitly disclaims** "no CHSH bound, no expectation values." | **OVER-CLAIM** (the only one): doc says a quantitative bound is proved; code proves a qualitative no-go shape, in the explanatory Experiments layer, not the proof spine. | **fix doc** — soften to "the *locality no-go* is proved; the `\|S\|≤2` number and its `2√2` violation are name-only / experimental." *(Or fix code: build a real CHSH theorem in `Measurement/` if you want the quantitative claim.)* |
| 2 | **~14–24** (esp. 21) | GR+QED unification **not claimed**; gravity **name-only** (Ch21) | `the_capstone` **PROVED** (`Capstone.lean`): universe tensor→valueBox, electronVariation→electronBox, exhaustive two terms; `threeRung_einstein_field_equations_hold` **PROVED** (`Episode75`) | **LAG** — the staged Vol 2 thread-rethread's precondition (a built capstone) is now met | **fix doc** — the rethread is due: Parts IV+V as the two leading terms of one operator; grade the "satisfies GR / Heisenberg" readings *interpretive*, never proved |
| 3 | **~19 / 30** | 3-up/3-down flavor count **conjectured / not claimed** | `apparatus_resolves_at_most_three` **PROVED** (`Episode83`): ¬∃ four pairwise-distinct tags | **LAG** — the "at most three" the doc holds as conjecture is proved | **fix doc** — can promote "resolves at most three" from conjectured → derived. **VERIFY** the scope first (is "at most three tags" the generation-count claim, or a narrower tag result?) |
| 4 | **17 / 18 / 30** | electron **"named, not built"**; spinor **coda-only** | `the_naming`, `threeRung_boundary_secondVariation_eq_electron`, `two_electrons_are_one_particle` **PROVED** | **LAG BY DESIGN** — the question/resolution fence deliberately withholds the built naming until the reveal | **keep doc** (intentional) — but confirm the **Ch29 reveal** can now land the *built* pigeonhole/naming rather than reach for it |
| 5 | **11 / 22** | Navier–Stokes **fenced as unsolved** | `threeRung_navierStokes_balance` = finite accounting (`forcing = transport + pressure + …`), **not a solution** | **NO DELTA** — code's NS is the finite-model balance, consistent with the fence | **keep both** — confirm the coda/prose never reads the balance as "we solved NS" |
| 6 | **05 / 15 / 17 / 20** | **five** "proved loop residues" (echo, Bragg, Dirac, Sagnac, positron) | **one** ±1-holonomy mechanism (`baseline_relative_flip`, `threeRung_boundaryCharge_one`) read across contexts | **SOFT** — five *readings* of ~1–2 theorems, not five independent proofs | **keep doc** if framed as readings of the one residue; **fix doc** only if any chapter asserts a *separate* proof it doesn't have |
| 7 | **18** | positron: coincidence **iff**, converses falsifiable, "not one inch more" | `detects_positron_over_tilt`, `no_positron_over_flat` **PROVED**; fence content matches | **NO DELTA** — backed, and the exemplar fence | **keep both** |
| 8 | **28 → 29** (forcing) | forcing named at the Cantor–Gödel–Cohen chapter | `29.tex:138` names Cohen forcing; body never says "axiom of choice"; `Episode61 cohen_cauchy_up_to_epsilon` is the finite analogue | **NO DELTA** (location reconciled: **Ch29**) | **keep** — the earlier "Ch22-23" was a stale carried number, corrected |

## What this means for the decisions
- **Only Row 1 (Bell) is an over-claim** → the single place the doc reaches past the code. One-line grade fix (my call), or build CHSH if you want it proved.
- **Rows 2–3 are "the doc owes the code"** → the code built the capstone and the "three"; the book should catch up (the rethread + the flavor promotion). These are *upgrades*, gated on the interpretive-grade discipline.
- **Row 4 is a designed fence** → keep, but the reveal can now be built, not reached-for.
- **Rows 5–8 are aligned** → confirm framing, no substantive change.

## Not yet covered (honest gap)
A complete row-per-claim chart (every chapter claim × every one of ~200 device theorems) is a larger
pass than the two quick agent maps, which under-reported. The rows above are the load-bearing deltas,
verified. If you want exhaustive coverage, that's a dedicated pass — worth doing once, given the agents
missed the capstone entirely.
