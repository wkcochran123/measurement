# Consolidation Map — PLAN_RFC Step 1 (for Kodo's gate, BEFORE any mass change)

*Graded off the build. Every claim below is from `lake build` / grep on the real tree, not prose.*

## Step 0 — FIX THE BREAK: DONE ✅ (verified off bare `lake build`)
- Bare `lake build` FAILED on `Measurement.lean:74 import Measurement.Episode93` → the file had been
  git-mv'd to `Measurement/attic/Episode93.lean` (my earlier trim), leaving a live import to a missing file.
- **Fix: restored `Episode93.lean` to its expected path.** Episode93 was the **ONLY** atticked-but-root-imported
  file (Kodo's guess re: Agent/Formalization checked and **disproved** — `CooperManual`/`AlphaProbe` are not
  root-imported; 0 other atticked files are imported).
- **Bare `lake build` GREEN, 101 jobs** (100 + the echo below).

## The shape of the space (the fact that dictates the strategy)
- 202 `.lean` (excl. attic): 71 `Meanwhile*`, 93 `Episode*` (1–93 contiguous), 38 other. Root imports 73 modules.
- **The import graph is a near-LINEAR CHAIN, not a tree** — only 4 leaves (`Meanwhile79`, `Episode93`, `Funge`,
  `TwoDescriptions`). Each Meanwhile imports the prior (`M50←M49`, `M79←M78`).
- **Sacred Ep1–15 import ZERO sprawl** — clean frozen base (Ep15←Ep14←…←Ep1).
- **Episode16 is the single JOIN**: `import Episode15, Meanwhile17, Calibration.EKGBounded`. The ENTIRE 16+ sprawl
  (Episodes 16–93 + Meanwhile 17–80) hangs off Episode16, on top of sacred Ep15.

## (a) Duplicate kill-list
- **No byte-identical files.**
- **64 multi-home decl names, but MOST are namespaced-legit** (`le`,`lt`,`zero`,`add`,`apply`,`identity`… each
  inside its own Episode/structure namespace — the build is green, they don't clash). **Blindly killing these
  breaks the build.**
- **Real structural duplicates:** `QPhase` (`Episode39` ≡ `Meanwhile22`, identical `{plus,minus}`); `Spin`
  (`CooperManual` + `Meanwhile52` + `TwoDescriptions`); the **α-study chain re-derives the running study**
  (`centerAlpha`/`InverseAlphaScaledAt18` repeated across `Meanwhile49,50,52,57,58,60,61,62,67,68,70,71,72,73,74,77,78`).
- **Under the prune strategy these are moot** — the whole 16+ sprawl leaves the build, so the "kill-list" collapses
  to "the 16+ chain, in bulk," not a decl-by-decl surgery.

## (b) Consolidation strategy — PRUNE, not a 93-episode rename (reconciling operator + Kodo)
Operator's steer: *"the algorithm and the equation should echo so that episodes 17- are unnecessary."* Combined with
the linear-chain-on-clean-sacred-base fact, the safe plan is:
1. Build the convergent target (echo ✅ + bound ⏳) **self-contained on sacred Ep1–15** (no dependency on 16+).
2. **Prune root `Measurement.lean`** to import only {`Episode15` (sacred top) + the convergent target file(s)}.
   → the entire 16+ chain (≈150 files) falls out of the build in ONE edit; bare `lake build` re-verified green,
   printing only the target.
3. **Attic/delete the now-unimported 16+ files** (reversible; nothing imports them once step 2 lands).
4. Result = sacred serial Ep1–15 + the convergent construction. No `Meanwhile` filenames; no gaps; no dup surgery.
- **Do NOT mass-rename 93 episodes** — a blind rename of a linear chain + 80 cross-refs is how everything breaks;
  the prune achieves "serial, no Meanwhile, no dups" without touching the sacred chain or renaming anything.

## (c) Where the target lives today + how it collapses
| Target piece | Lives today | Collapse |
|---|---|---|
| `electron_in_orbit` / `anti_cooper_pair` | substrate in `Meanwhile52` (`CooperPairChannel`, `antiCooperPairChannel`, `Spin`) | **DONE** — rebuilt self-contained in `TwoDescriptions.lean` |
| `two_descriptions := rfl` (§2) | did not exist | **DONE** — built; bare build green |
| `#print axioms` | — | got **`[]`** (cleaner than `[propext]`); ⚠ if `[propext]` is required, lift the equality through the sacred `Truth`/`Fact` Prop layer |
| α bound `a1 < α ≤ a2` (§1.2) | scaled-integer chain `Meanwhile49–78` (`centerInverseAlpha ≈ 137.011`, device-**derived**; CODATA fence holds — 0 root files carry `137036`) | ⏳ **REBUILD minimal on sacred** (the Dedekind/scaled-integer resolution) — the remaining construction |
| dead weight | `AlphaManual` (Float+CODATA), `CooperManual` — **not root-imported** | delete with the prune |

## The echo prototype (already built this turn, target (c))
`Measurement/TwoDescriptions.lean` — `two_descriptions : electron_in_orbit = anti_cooper_pair := rfl`, self-contained,
`#print axioms = []`, bare `lake build` green (101 jobs). Meaningful (not a hollow alias): `electron_in_orbit` =
one electron (matter/up) carried around its orbit, charge-conjugated on the return leg (the positron reading, §3),
two half-turns → computes to the anti-Cooper-pair.

## What I'm holding for the gate
- The **prune + delete** (step (b).2–3) is the high-stakes, hard-to-reverse move — **held for Kodo's gate**.
- Open decision: **`[]` vs `[propext]`** for the echo (keep the stronger `[]`, or route through `Truth` for `[propext]`).
- Next construction (independent of the gate): **rebuild the α bound self-contained on sacred**.
