# Phase 0a — The 16+ Inventory (review artifact, NOTHING MOVED)

*Task `instrument` (SPEC.md), Turn 75. Podo. Branch `instrument/restore-pre-trim-0a` @ baseline `55827f0`.
Method: mechanical import-graph + signal scan over all 182 owned files → ultracode fan-out (6 agents,
build-checked) read-classifying every candidate/ambiguous cluster + a dedicated α-path trace. **This is a REPORT
for the acting operator to review BEFORE any cut. No decl has been moved, quarantined, or deleted.** Criterion is
the operator's: ABOVE = builds AND registers a real distinction (computes / proves / used-downstream); BELOW =
sketch / stub / promissory / dead / does-not-build.*

---

## 0. THE HEADLINE — the whole Phase-0 pipeline is blocked behind ONE localized repair

The α signal path is a **barbell**: two building wings joined by a broken ℕ-cost spine.

| Segment | Anchor | Location | Builds? |
|---|---|---|---|
| **WING 1 — reading** | `Fact.Truth` (TRUE=TRUE floor) | Episode1:96 (sacred) | ✅ |
| | `spin : Number → Bullshit` (the fold; real `output_true` proof) | Meanwhile18:1852 | ✅ |
| **SPINE — ℕ cost/rank** | `Stage.rank` | Formalization/Epiphany:251 | ❌ |
| | `Step.rank_succ` (rank +1 per step) | Formalization/Grammar:50 | ❌ |
| | `Derivation.cost` / `inferred_cost = 36` | Formalization/Cost:47,64 | ❌ |
| | `derivation_cost_eq_rank` (**the 0b bridge lemma**) | Formalization/Search:15 | ❌ |
| **WING 2 — calibration** | `Calibration.EKG.outgrown?` | LeanCalibration:147 (sacred-in-spirit) | ✅ |
| **the 0b seam** | `AlphaProbe` (gauge + phase face in one file) | AlphaProbe.lean | ❌ |

**The entire broken spine sits behind ONE root failure: `Formalization/Epiphany.lean:340` & `:352`** — a
`FullCascadeObject` / `LOCAL` universe/type error (`type expected, got (LOCAL Value …)` at 340; `invalid {...}
notation` on `truthObject` at 352). The proofs downstream (`Step.rank_succ`, `derivation_cost_eq_rank`, …) are
themselves **well-formed** (`by decide` / induction / `rfl`) — they are gated out *purely* by the upstream
non-build. Confirmed by TARGET build: `lake build Measurement.Formalization.Cost` and `…AlphaProbe` both fail at
exactly Epiphany 340/352.

**Consequence:** Phase 0b (the connection theorem) is **blocked, not merely unwritten.** Both wings are ready and
waiting. **Repairing `Epiphany:340/352` is the single gate that reopens the whole Formalization chain and the
0b seam.** Epiphany is 16+ (mine) — **NOT a sacred file** — so its repair is *not* a sacred-gate item.

---

## 1. The trim is surgical — the BELOW-floor set (attic candidates)

Only **6 files** are genuinely below-floor. The computing core is untouched.

| File | Sub-reason | Note |
|---|---|---|
| `Formalization/ProfileToy.lean` | **dead** | Explicitly sidelined Bool^36 toy: docstring "not the main formalization", "Do not cite the theorems in this file". Dead leaf. |
| `Formalization.lean` | **dead** | Import-only orphan aggregator; own docstring: "no new theorems… no definitions"; not imported by root. |
| `Agent.lean` | **dead** | Thin re-export (0 decls of its own); not imported by root; leaf. |
| `Basic.lean` | **stub** | The lake-generated placeholder `def hello := "world"`. |
| `Episode93.lean` | **dead** | All decls are `def : Prop` (`did_this_distinguish?`, `youTheReader_asked`, …) — no theorem/`#eval`/proof term; builds but registers no distinction. |
| `AlphaProbe.lean` | **does-not-build** | Scratch `#check` probe (imports the broken Cost). ⚠ It is the *intended* 0b seam — **rebuild it as the real seam once Epiphany is fixed, don't just attic it.** |

*The `attic/` (= the codebase's antimatter budget) would receive these via `git mv` — quarantine, never delete —
**only after your review.***

---

## 2. The Formalization branch — REPAIR, not attic (the nuance)

The branch is almost entirely **ABOVE-by-design (proves real theorems) but ENTIRELY build-broken.** It is not a
sketch pile; it is a real formalization gated out by two committed breaks.

- **α-core → must repair (0b needs them):** `Epiphany`, `Grammar`, `Cost`, `Search`. Fixing `Epiphany:340/352`
  reopens all four (they only fail transitively).
- **Off-path, real, self-healing:** `Herbrand`, `TerminalUniqueness`, `Irredundance`, `Minimality`, `Bridge`,
  `QED`, `Example` — all prove real theorems on the uniqueness / QED-apex track; all broken *only* transitively
  via Epiphany → they build again the moment Epiphany is fixed. (`Minimality` is a dead leaf but proves a real
  Level-1 theorem — keep.)
- **A SECOND, independent break:** `Formalization/FiniteGaugeEquation.lean:162`
  (`finiteGaugeEquation_eq_transmute`, a `LOCAL/REAL` universe mismatch). It imports Episode10 (**not** Epiphany),
  so it fails on its own. Off the α path (feeds the QED track). **Decision needed: repair or attic?**
- **The one green file:** `Formalization/ReciprocalAccounting.lean` — builds (73 jobs), off α-path, used by
  Episode74. Keep.

---

## 3. Everything else the deep sweep read = ABOVE (keep)

- **Below-marker Episodes** `Episode{20,42,49,52,53,56,57}` + **`NamingClose`**: ALL ABOVE. Every "sorry/stub/not-yet"
  marker is **incidental header prose**, not a live gap. Build-verified (`Episode57`+`NamingClose` = 64 jobs; every
  `#print axioms` = `[propext, Quot.sound]`, never `sorryAx`). `NamingClose` carries the α-adjacent naming close
  (`the_naming`, `boxCount_is_two`, δ¹→δ²).
- **Frontier leaves** ABOVE: `Capstone` (4 thms), `ElectronBridge` (97-job build, 3 thms), `Episode89`
  (popcount/positronCount + 4 `decide`), `Episode91`, `Episode92` (`band_covers` by omega).
- **The WIP α-estimate chain** (the acting operator's own α work, already in the tree, all ABOVE-computes):
  `Meanwhile40` (first α read, `alphaScaledAt18`), `Meanwhile62` (**QFT α center `qftAlphaScaledAt18`**),
  `Meanwhile63` (α envelope), `Meanwhile{72–78}` (covariant-tax layers: Christoffel / spinor / variational /
  JFNK / Yang-Mills-antimatter), `Meanwhile79` (terminal report, +6 `decide` thms), `Meanwhile39ElectromagneticCoupling`,
  the `Meanwhile62{Chirality,Mott,Photoelectric,Semiconductor,SmallAngle,SternGerlach}` variants, `Meanwhile{64–71}`.
  **build_status = unverified** (cold compile of the ~70-file Meanwhile chain — not cheaply checked this pass;
  the prior commit "Working prediction just type lake build" implies the snapshot built).
- **The ±1 anchor** `baseline_relative_flip` (the matter/antimatter sign α is the *strength* above) = **Episode83:139**
  (a real theorem; not in NamingClose).

---

## 4. Sacred-touch flags

**NONE.** The α path *reads* `Fact.Truth` (Ep1, sacred) and `EKG.outgrown?` (LeanCalibration, sacred-in-spirit)
but does not modify them. The one repair the pipeline needs — `Epiphany:340/352` — is in **16+ (mine)**, not
sacred. No sacred gate is triggered by anything in this inventory.

---

## 5. Decisions requested (before any cut)

1. **Approve the 6-file attic list** (§1) — or amend it.
2. **Approve the immediate unblock:** I repair `Epiphany:340/352` (16+, my territory, no gate) → the whole
   Formalization spine + the 0b seam reopen. This is the critical-path next action.
3. **Rule on `FiniteGaugeEquation:162`** (second break, off-path): repair or attic?
4. **`AlphaProbe`**: attic the scratch version now, then rebuild it as the real 0b seam post-repair (recommended),
   vs. leave in place.

*Scope honesty: the deep per-file read covered the candidate/ambiguous clusters (all dead-leaf + all below-marker
candidates) + the α path; the ~150-file computing core is ABOVE by mechanical signal (import + `#eval`/`#print`/`decide`),
spot-checked, not exhaustively agent-read. The BELOW set above is the fully-identified trim target; a deeper
per-decl sweep can follow if you want the trim more aggressive.*
