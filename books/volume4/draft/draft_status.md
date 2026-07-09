# Volume 4 Draft Status

## Files Created Or Rewritten

- Rewritten: `books/volume4/draft/00-preface.md`
- Created: `books/volume4/draft/01-the-number-with-no-units.md`
- Created: `books/volume4/draft/02-the-loop-price.md`
- Created: `books/volume4/draft/03-the-needle-through-the-phase-face.md`
- Rewritten: `books/volume4/draft/draft_status.md`

## Files Removed

- Removed obsolete first-pass file: `books/volume4/draft/01-the-joke-that-survived-the-proofs.md`
- Removed obsolete first-pass file: `books/volume4/draft/02-charge-is-what-the-story-owes.md`

## Quick Acceptance-Check Results

- Owned-file scope: edits stayed under `books/volume4/draft/`.
- Corrected mandate: the preface states the device reading of alpha on the first page:
  `alpha = cost of one needle-through at the phase face / cost of closing the whole loop`.
- Proof fence: the preface explicitly says Volume 4 does not prove alpha and that alpha
  derivation/build status belongs to Volume 1.
- Ch01 notation fence: distinguishes `alpha` from `alpha^-1`; treats 137 as folklore,
  scale, and doorplate, not as success.
- Ch02 denominator discipline: treats loop cost as an independently specified whole
  closure before any division.
- Ch03 numerator discipline: treats needle-through cost as one independently motivated
  coupling at the phase face before any division.
- Ledger discipline: each prose file ends with `## Ledger` and exactly these labels:
  `Explanation:`, `Device-reading:`, `Build result:`, `Speculation:`.
- Positron discipline: positron material appears only as supporting color in Ch03 and
  does not drive the opening spine.
- Numerical discipline: the draft does not claim exact 137, does not celebrate 137 as
  a result, and does not claim Volume 4 derives alpha.

## Unresolved Risks For Beastmaster Review

- The phrase "cost" is reader-facing and visual; beastmaster should confirm whether
  any later batch needs a tighter bridge to the formal cost gauge vocabulary.
- The phase face image is intentionally flexible across detector plane, membrane, and
  polarizing sheet; beastmaster should decide whether one canonical visual should
  dominate before art direction begins.
- Ch01 mentions the empirical reciprocal as near 137.036; beastmaster should confirm
  whether Volume 4 wants that decimal early or prefers to defer precision to a sidebar.
- The first batch is alpha-first and deliberately cool on positron play; beastmaster
  should confirm whether the next batch can restore more of that tonal sparkle without
  bending the spine.

## Suggested Next Batch

- `04-divide-only-after-you-have-two-costs.md`
- `05-the-instrument-that-refuses-to-tune.md`
- `06-phase-makes-the-invisible-expensive.md`

The next batch should make anti-fitting visual, introduce the pre-registered
instrument/dial discipline, and then connect phase/interference plates to the
coupling ratio without upgrading explanation into build result.

Use `books/volume4/experiment_plate_atlas.md` before drafting the next batch.
For each batch, record at least one primary plate experiment, one sidebar or
caption experiment, and one cautionary/fence experiment. The whole
`device/Experiments/` corpus is available as inspiration, not only the obvious
phase and positron examples.

When an experiment supplies more than visual texture, consult its
`Experiment*.lean` files, and consult `device/Measurement/**/*.lean` for device
mechanics when needed. Record any code files read in this status file. Reading
code is allowed for nitty gritty accuracy; running Lean/builds or claiming a
new build result is not part of this pass.
