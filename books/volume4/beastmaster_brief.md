# Volume 4 First-Draft Brief

## Corrected Mandate

Volume 4 is the coffee-table science book.

Its center is the fine-structure constant explained in terms of the device: not a technical proof monograph,
not a code audit, and not primarily a positron joke. It should make a visually minded reader feel what the
device says alpha is: the price of one electromagnetic interaction as a fraction of the whole measurement
loop.

Working device reading:

```text
alpha = cost of one needle-through at the phase face / cost of closing the whole loop
alpha^-1 ~= 137
```

The book should explain this through images, spreads, captions, analogies, and short prose. The mathematical
claim discipline remains strict, but the reader-facing goal is explanatory: show how the device makes alpha
legible.

## Role Split

- Beastmaster: coordinates this run, reviews global drift, and keeps the active RYOT process untouched.
- Outline agent: owns `books/volume4/outline.md`.
- Text agent: owns files under `books/volume4/draft/` after the outline is available.

## Source Pack

Read these before writing:

- `RYOT.md` for process shape only, especially the outline-then-text pattern and beastmaster guardrails.
- `books/expository_monograph/alpha_target_and_acceptance.md`, especially the cost-ratio target and the
  "What migrates from Vol 4" note.
- `books/expository_monograph/outline.md` for Volume 1's device loop.
- `books/experimentation/outline.md` for Volume 2's applied-physics and effect-ceiling style.
- `books/the_compiler/outline.md` for Volume 3's proof/sketch ledger.
- `device/Experiments/**/description.md` as the full coffee-table inspiration corpus. In this checkout
  there are 137 experiment descriptions under `device/Experiments/`; use that as catalog metadata, not as
  evidence for alpha.
- `device/Experiments/**/Experiment*.lean` and `device/Measurement/**/*.lean` are always available for
  understanding the nitty gritty details behind a plate, caption, or device-reading claim. Read code when
  the prose needs mechanism. Do not turn the coffee-table book into code commentary.
- `books/volume4/experiment_plate_atlas.md` for routing experiments into plate families, captions,
  sidebars, and cautionary spreads.
- `books/expository_monograph/three_gauges.md` and `books/expository_monograph/_episodes_digest.md` as
  orientation sources for gauge, loop, electron/positron, residue, reader-process, and charge motifs.

## Priorities

- Make alpha central from page one.
- Write for a coffee-table science format: visual spreads, plate ideas, captionable metaphors, short vivid
  prose, concrete reader-facing explanations.
- Explain the device in plain language: loop, phase face, coupling, electron-photon interaction, cost,
  bootstrap, gauge, and reader.
- Treat `alpha^-1 ~= 137` as the famous empirical target and the device's interpretive challenge.
- Use any and all experiments in `device/Experiments/` as visual/scientific inspiration. Do not restrict
  Volume 4 to the obvious phase, positron, or QED examples; the whole corpus is available as a plate,
  sidebar, caption, texture, or caution source.
- Use the code as the detail layer. Descriptions supply the reader-facing scene; Lean files supply exact
  mechanisms, definitions, local theorems, and claim boundaries when the draft needs precision.
- Keep proof status explicit: the book can explain the target and the device reading without pretending that
  prose or art has proven the number.
- Keep the positron/playful material as supporting color, not the main spine.
- Do not use active RYOT inboxes, state files, prompt automations, or handoff turns for this work.
- Do not run Lean, builds, experiments, or code audits for this pass; reading source files for understanding
  is allowed and expected.
- Do not edit Vol 1, Vol 2, Vol 3, RYOT files, or device code.

## Outline Agent Deliverable

Rewrite `books/volume4/outline.md` with:

- a working title and two alternate titles;
- a one-breath thesis centered on alpha and the device;
- a coffee-table format section: visual grammar, recurring spread types, sidebars, captions;
- a claim-discipline section distinguishing explanation, device-reading, build result, and speculation;
- a proposed act or movement structure;
- chapter-by-chapter notes, each with visual spread ideas;
- a source/seed ledger;
- a drafting plan for the text agent.

## Text Agent Deliverable

After `outline.md` exists, create or rewrite the first prose batch under `books/volume4/draft/`:

- `00-preface.md`;
- `01-*.md` and `02-*.md` for the first two chapters selected by the revised outline;
- `draft_status.md` naming what remains and what risks need beastmaster review.

The opening batch should feel like a coffee-table science book in prose: plate notes, caption-ready
paragraphs, and a clear explanation of alpha in terms of the device.
