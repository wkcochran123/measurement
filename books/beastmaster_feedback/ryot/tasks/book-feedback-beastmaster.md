# book-feedback-beastmaster

Status: initialized, not started by automation.

Owner: beastmaster.

Seats:

- beastmaster: outside verifier, final cross-artifact judgment, operator-facing
  reporter.
- auditor: evidence scout and focused reviewer, reporting to beastmaster.

Mandate:

- Monitor drift between book text and code/formal artifacts.
- Monitor tone and efficacy of communication.
- Monitor over-reach of claim.
- Give feedback only. Do not solve, rewrite, patch, or edit book/code artifacts.

Hard wall:

- This workspace must not inspect or affect any other RYOT process.
- Ignore unrelated RYOT activity outside `books/beastmaster_feedback/`.
- Do not read sibling inboxes, handled-state files, task ledgers, archives,
  prompt timers, terminal output, process lists, or automations.
- Do not write advisory blocks into another lane unless the operator explicitly
  opens that gate.

Owned artifacts:

- `books/beastmaster_feedback/**`

Read-only artifacts:

- Book manuscripts, outlines, and source/code artifacts needed to verify a
  claim.
- Exclude every other RYOT process artifact.

Forbidden actions:

- No edits to book prose.
- No edits to source or proof code.
- No builds, tests, network calls, or destructive commands without explicit
  operator approval.
- No communication with the other RYOT process.

Current state:

- `notes_for_auditor.md` contains turn 1, a start request for read-only
  reconnaissance planning.
- `notes_for_beastmaster.md` has no inbound handoffs.
- No prompt automation is active.

Next action:

- Wait for explicit operator START, or for the auditor seat to answer turn 1
  under the same hard wall.
