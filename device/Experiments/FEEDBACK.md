# Feedback on the `device/Experiments/*/Experiment1.lean` unit tests

Reviewed all 136 `Experiment1.lean` files + `Common/Basic.lean`, deep-read a 14-effect
sample, and grep-verified the systemic claims. Net: **the harness design is good and the
honesty-tagging idea is genuinely clever, but as written these files test almost nothing.**
Prioritized below.

## 0. Decide first: what are these *for*? (This changes everything.)

Two possible goals; the suite is currently built for neither cleanly.

- **(A) Behavioral tests of the device** — then the suite **fails outright**: **0 of 136
  files import the actual device.** Every file imports only the toy `Experiments.Common`
  harness. If a real `Measurement.lean` theorem regressed or grew a `sorry`, all 136 still
  go green. Zero regression coverage of the thing they're named after.
- **(B) A machine-checked "honesty-ceiling registry"** (each file declares the max claim
  that effect is allowed to make) — then it's coherent, but **the ceiling is a sticker, not
  a fence**: `theorem ceiling : claim.tag = X := by rfl` only proves a label equals itself.
  Nothing ties the tag to a *bound on what the file actually proves*. A `finiteLedgerModel`-
  tagged file could prove anything (or nothing) and the tag still typechecks.

**Decide which goal you're targeting** — it reorders the whole fix list. The rest assumes a
blend of (B) with real per-effect content.

## 1. `claim_holds` is vacuous — it can only fail on an author typo

Every file (136/136) proves its claim by `decide` over **closed integer literals the author
typed in the same file**:

```lean
def defaultSetup := { recorded := 2, accessible := 2, required := 3 }
theorem claim_holds : claim.statement := by decide   -- reduces to 3 ≤ 2 + 2
```

Three stacking problems, all verifiable:
- **The claim discards its input:** `claim := fun _ => claim.statement` in all 136 files.
  The theorem says nothing about `run` as a function — only about one hard-coded output.
- **The integers are rigged:** only **6 distinct triples total**, each *determined by the
  ModelKind*. The author picks a ModelKind (which picks an inequality), then picks integers
  that satisfy it. The test verifies the author can satisfy their own inequality.
- **`labelsOnly` proves literally `True`:** `ModelKind.holds labelsOnly _ = True`
  (Basic.lean:158, output discarded). So all `physicalClaimLabelOnly` files (~26, e.g.
  Aharonov-Bohm, Bell-Aspect, Yang-Mills, Conservation of Energy) prove `True = True`.

→ **Fix:** make claims quantify over the setup —
`theorem claim_holds : ∀ s, P s → ModelKind.holds k (run s)` — so the proof depends on the
model's *behavior*, not three frozen literals. For the `blocks`/`inadmissibilityNoGo` tier,
prove a **universal impossibility** (`∀ s with property P, ¬ holds`), not one favorable
triple — a no-go shown by a single hand-picked instance is the weakest possible form of a
no-go.

## 2. The physics is 100% discarded; the matching harness structures sit unused

The `description.md` files are rich and specific, and `Common/Basic.lean` ships exactly the
right vocabulary — `Ledger`, `Channel`, `Boundary`, `Projection`, `Holonomy`, `Refinement`,
`CausalOrder` — and **135 of 136 files use none of it**, collapsing every effect to 3
integers. The mappings are nearly 1:1:

| Effect family | Description hands you | Harness structure to use |
|---|---|---|
| loop / phase / holonomy (Aharonov-Bohm, Yang-Mills, Sagnac) | `∮A·dx`, "curvature without force" | `Holonomy` — `residue ≠ 0` while a local `Projection` agrees |
| shadow / coarse-graining (Shadow Tomography, Butterfly, Gibbs) | "only a bounded shadow survives" | `Projection.sameShadow` + `Refinement` — two distinct fine states, same shadow |
| distinguishability bound (Heisenberg, Maxwell's Demon, Turing) | "refinement P_n → P_{n+1}" | `Refinement` + `pushLedger` |
| locality no-go (Bell-Aspect, Entanglement) | "no local factorization" | `Boundary.compatible` + a factorization-failure witness |
| conservation / balance (Conservation of Energy) | "what leaves here enters there" | `Ledger.count_append` (tailor-made for a continuity law) |

→ **Fix:** either use this vocabulary so each tag sits over a real model, or prune
`Basic.lean` to what you actually use. The harness's expressiveness currently implies far
more is proven than is — the most misleading part.

## 3. Three concrete bugs (fix regardless of goal A vs B)

- **`TheChaitinEffect` is mis-tagged and contradicts its own source.** Tagged
  `inadmissibilityNoGo` (a finite obstruction, `required > accessible`), but the description
  explicitly says *every* event is finite and **admissible** — there is no obstruction; what's
  absent is a predictive *law*. Tagging an uncomputability effect as a decidable finite no-go
  is a category error. → Retag `physicalClaimLabelOnly`, or model prefix-underdetermination
  (two continuations with `Projection.sameShadow` but a different next event).
- **`TheHeisenbergEffect` encodes the wrong direction.** `ModelKind.blocks` =
  `accessible < required` is an *upper-bound over-request*, but the description is about a
  *minimum/lower* refinement bound. Worse, the in-file comment says "lower-bound refinement
  version" while the code does the opposite. → Make model + comment agree with the description.
- **`CompactDiscEncoding` (your one good file) still asserts its headline by fiat.**
  `mergedCount = fineCount` is `rfl`-true because `run` defines *both* as
  `setup.fineLedger.count`, and `mergedLedger` is literally defined as `fineLedger` — the
  "merge" discards the coarse ledger instead of reconciling it. `merge_preserves_fine_count`
  is a contentless `rfl`. → Make the merge a real `Refinement.pushLedger` reconciliation and
  prove `coarseCount ≤ fineCount` as a theorem about the decode map, not hardcoded literals.

## 4. What "good" looks like — copy `CompactDiscEncoding`'s *shape*, fix its *vacuity*

It's the only file that does the right things: an effect-specific type
(`SurfaceMark : pit | land`), a threshold `Reader`, and a **genuinely falsifiable general
lemma** (`belowThresholdInvisible : separation < threshold → ¬ canRecord`, quantified over
reader/separation — it would break if the def were wrong). That's the template the other 135
should follow: a small domain type + at least one *quantified* lemma that constrains the
claim + a conjunctive `claimStatement` about the modeled object. Just don't let the central
`claim` reduce to `rfl`/`decide` on frozen literals.

Also add a harness lemma `tag_matches_modelKind` so a mis-paired file (high tier running the
`True` model, or vice versa) fails to compile — right now tag↔ModelKind consistency is
convention, not a theorem.

## Credit where due (balanced)
- **No `sorry`, `admit`, `native_decide`, or `axiom` anywhere** — clean.
- **The `ClaimTag` honesty discipline is a real, good idea**, and most tags are honest (they
  under-claim rather than over-claim; the disclaimer comments are candid). The two tag
  problems are Chaitin (over-claims a no-go) and Heisenberg (right family, wrong direction).
- `CompactDiscEncoding` proves the author *can* do it right — which is why the uniform
  template is a choice, not a necessity.

**One-line summary:** *Stop emitting the 44-line `CountSetup` template. Per effect,
import/exercise the real device (or, if these are honesty-registrations, prove the tag
actually bounds the content), pick the harness structure the description points at, and write
at least one `setup`-quantified lemma that could actually fail — model
`CompactDiscEncoding`'s shape, not its rigged merge.*
