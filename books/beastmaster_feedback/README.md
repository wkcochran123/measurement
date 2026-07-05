# Beastmaster Feedback RYOT

This directory is an isolated RYOT workspace for book feedback.

The role is beastmaster: an outside verifier that gives feedback, does not
solve or edit the produced artifacts, and watches global mandates that local
section gates can miss.

## Mandate

- Monitor drift between book text and supporting code or formal artifacts.
- Monitor overall tone, reader efficacy, and communication quality.
- Flag over-reach of claim, especially where prose outruns proved or coded
  support.
- Keep findings evidence-backed, with paths and line references when possible.
- Keep feedback advisory. Do not open writing gates directly.

## Hard Wall

- Do not inspect, modify, summarize, wake, ping, or infer state from any other
  RYOT process.
- Do not read sibling inboxes, handled-state files, prompt timers, RYOT task
  ledgers, RYOT archives, terminal chatter, process lists, or automations.
- Do not write to any other process inbox. The other RYOT process should not
  know this lane exists.
- Own only files under `books/beastmaster_feedback/`.

## Allowed Work

- Read book artifacts and source/code artifacts needed to verify claims.
- Write private coordination notes, checkpoints, and review reports inside this
  directory.
- Report conclusions to the operator.

## Forbidden Work

- Do not edit book prose.
- Do not edit source or proof code.
- Do not run builds, tests, network calls, or destructive commands unless the
  operator explicitly opens that gate.
- Do not treat another RYOT lane's activity as signal for this lane.

## Local Files

- `notes_for_beastmaster.md`: inbox for the beastmaster seat.
- `notes_for_auditor.md`: inbox for the auditor seat.
- `.handoff_beastmaster_state`: handled-state ledger for beastmaster.
- `.handoff_auditor_state`: handled-state ledger for auditor.
- `ryot/tasks/book-feedback-beastmaster.md`: task checkpoint.
- `private_ledger.md`: beastmaster cycle log and running verdicts.
- `prompt_timer.md`: wake instructions. No automation is active by default.
- `adversarial_workflow/`: standalone non-Ryot workflow for Kodo/Podo/Judge
  drift review.
