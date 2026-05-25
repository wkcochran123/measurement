# RYOT: Roll Your Own Talent

RYOT means **Roll Your Own Talent**.

Off-the-shelf agent stacks pick the agents, the review style, and the stop
conditions for you. RYOT is for the operator who would rather assemble those
pieces: two LLM agents, an inbox each, a watcher, and a strict review habit.
RYOT is small on purpose. It is not a task queue, a chat server, or a substitute
for human approval. It is a disciplined way for two agents to pass state back
and forth without losing the thread.

## RYOT Brand Usage

Use **RYOT** as the name of the system.

Use **Roll Your Own Talent** when expanding the acronym for a new reader.

Use **RYOT job**, **RYOT handoff**, **RYOT watcher**, and **RYOT artifact** for
the moving parts. Avoid falling back to a generic name like "the two-agent
handoff protocol" once the reader knows the brand.

Use **RYOT operator** for the human who owns the approval gates, restarts
watchers, and decides when the loop stops.

The RYOT promise: two agents that never lose state, never quietly approve their
own work, and never stop without the operator's sign-off.

## Core Idea

Each agent has an inbox file. The other agent writes to that inbox.

```text
notes_for_agent_a.md  <- written by Agent B, read by Agent A
notes_for_agent_b.md  <- written by Agent A, read by Agent B
```

A RYOT watcher polls each inbox, reads the first `HANDOFF` header, ignores stale
or misaddressed messages, prints new messages, and records the last processed
turn in a state file.

The RYOT operator owns the dangerous parts:

- approving source edits, builds, long experiments, and destructive commands;
- deciding when jobs may run in parallel;
- restarting stuck watchers;
- stopping the loop when the agents need judgment rather than more iteration.

## Files And Roles

A minimal RYOT setup needs:

```text
notes_for_agent_a.md
notes_for_agent_b.md
poll_agent_a.sh
poll_agent_b.sh
.handoff_agent_a_state
.handoff_agent_b_state
```

In this repository the concrete names are:

```text
notes_for_codex.md
notes_for_claude.md
poll_codex.sh
poll_claude.sh
.handoff_codex_state
.handoff_claude_state
```

Agents can be symmetric peers, but most jobs benefit from temporary roles:

```text
Writer / Reviewer
Implementer / Auditor
Proof author / Formalism critic
Drafting agent / Style and correctness grader
Patch author / Build-output diagnostician
```

State the roles in the first handoff for each job.

## RYOT Quickstart

1. Choose agent ids.
2. Choose roles for the first job.
3. Create inbox files.
4. Create state files with `last_turn=0`.
5. Start one watcher per receiving agent.
6. Seed the first handoff with `respond_to_sha: RYOT_START_<task>`.
7. Forward watcher output to the receiving agent when the process is manual.
8. Continue until one agent sends `CONVERGED` and the other sends
   `HANDOFF_CONVERGED`.
9. Stop the watchers or start the next job with a new task id.

To reset a stuck watcher without replaying stale turns:

1. Stop the watcher.
2. Edit the state file so `last_turn` equals the highest already-processed
   turn from the latest valid handoff.
3. Restart the watcher.

If the state file is missing or corrupt, recreate it with the correct
`last_turn`. Starting from zero can replay the whole conversation.

## Handoff Header

Every handoff file should begin with a machine-readable header:

```markdown
<!-- HANDOFF
from: agent_a
to: agent_b
turn: 17
status: NEEDS_RESPONSE
respond_to_sha: <artifact-sha-or-ryot-bootstrap-token>
stop_token: HANDOFF_CONVERGED
task: short-task-id
scope: what-this-message-covers
stop_mode: two-phase
grading: strict
constraint: no source edits without approval; no build unless approved
protocol_version: v1
-->
```

Required fields:

```text
from              sender id
to                receiver id
turn              strictly increasing integer for the receiver
status            current state of this handoff
respond_to_sha    artifact hash, output hash, decision id, or bootstrap token
stop_token        usually HANDOFF_CONVERGED
task              stable job id
scope             current slice of the job
stop_mode         usually two-phase
constraint        permissions, build limits, edit limits, or user rules
protocol_version  protocol version used by both agents
```

Use exact agent ids. If the watcher expects `to: codex`, do not write
`to: Codex`.

## Status Vocabulary

RYOT uses a small status vocabulary.

```text
NEEDS_RESPONSE       open turn; receiving agent should reply
CHANGES_REQUESTED    review with specific revisions named
CHANGES_APPLIED      edits landed; details in body
CONVERGED            sender believes the job is complete
HANDOFF_CONVERGED    receiver ratifies convergence; both stop for this job
BLOCKED              agent cannot proceed; RYOT operator input required
WITHDRAWN            sender retracts a prior handoff
INFO_ONLY            informational; no action expected
```

When an agent needs the RYOT operator, use `status: BLOCKED` and put the
smallest concrete question in the body.

Keep watcher behavior and human protocol aligned. A watcher may only stop on the
exact status values it implements.

## `respond_to_sha`

`respond_to_sha` anchors a multi-turn conversation.

Use one of:

```text
file hash             when discussing a specific artifact
output hash           when diagnosing a build or experiment result
bootstrap token       before an artifact exists, e.g. RYOT_START_<task>
decision id           when converging on a design choice rather than a file
```

Once an artifact exists, prefer a real hash. If the artifact changes, update the
hash in the next handoff so both agents know which version is under discussion.

## Message Body

After the header, write a self-contained handoff. Assume the other agent may
have lost prior context.

Good handoffs include:

- what changed or what was read;
- artifact hashes, file paths, and line numbers;
- observations separated from inferences;
- patch shape separated from edits actually made;
- unresolved questions;
- human approval gates;
- the exact response requested from the other agent.

Do not bury the request. End with direct questions or a checklist.

## Turn Discipline

Turns are monotonic for the receiving agent. If Agent A writes to Agent B with
`turn: 17`, the next message to Agent B must use `turn: 18` or higher.

When retrying a bad handoff, always use a fresh turn. Rewriting an already
processed turn will usually be ignored by the watcher.

Crossed turns are normal. If both agents write before reading the other's latest
message, each should acknowledge the crossing, state which turn it is answering,
and carry forward any constraints or open questions that still apply.

## Watchers

A watcher performs four jobs:

1. Poll the receiver's inbox.
2. Parse the first `HANDOFF` header.
3. Ignore stale, malformed, self-authored, or misaddressed messages.
4. Print new messages and update the state file.

Minimal behavior:

```text
read INBOX
extract from, to, turn, status, respond_to_sha
if to != AGENT: ignore
if from == AGENT: ignore
if turn <= last_turn in state file: ignore
print handoff
write last_turn=turn to state file
repeat
```

State file format:

```text
last_turn=17
```

See the inline reference script below; copy and adapt as needed for your shell
or runtime.

## Reference Watcher

Any watcher that reads the `HANDOFF` header, compares `turn` against a state
file, and emits only new turns is conforming. This is one reference
implementation:

```sh
#!/usr/bin/env bash
# poll_inbox.sh - RYOT reference watcher
set -euo pipefail

AGENT="${1:?usage: poll_inbox.sh <agent_id> <inbox_file> <state_file> [interval]}"
INBOX="${2:?}"
STATE_FILE="${3:?}"
INTERVAL="${4:-3}"

[[ -f "$STATE_FILE" ]] || echo "last_turn=0" > "$STATE_FILE"

extract() {
  awk -v field="$1" '
    /<!-- HANDOFF/ { in_block=1; next }
    in_block && /-->/ { exit }
    in_block {
      sub(/^[ \t]+/, "")
      if ($1 == field":") {
        sub("^"field":[ \t]*", "")
        print
        exit
      }
    }
  ' "$INBOX"
}

while true; do
  [[ -s "$INBOX" ]] || { sleep "$INTERVAL"; continue; }
  TO=$(extract to)
  FROM=$(extract from)
  TURN=$(extract turn)
  LAST=$(sed -n 's/^last_turn=//p' "$STATE_FILE")
  if [[ "$TO" == "$AGENT" && "$FROM" != "$AGENT" && "$TURN" -gt "$LAST" ]]; then
    echo "=== NEW HANDOFF turn=$TURN from=$FROM ==="
    cat "$INBOX"
    echo "last_turn=$TURN" > "$STATE_FILE"
  fi
  sleep "$INTERVAL"
done
```

## Starting A RYOT Job

The first message should define:

- task id;
- artifact or directory under discussion;
- roles;
- allowed actions;
- forbidden actions;
- done condition;
- whether edits, builds, tests, or network access are allowed.

Example:

```markdown
<!-- HANDOFF
from: reviewer
to: writer
turn: 1
status: NEEDS_RESPONSE
respond_to_sha: RYOT_START_VOLUME6_CHAPTER2
stop_token: HANDOFF_CONVERGED
task: volume6-chapter2-public-pass
scope: first section only
stop_mode: two-phase
grading: strict
constraint: edit only volume_6.md; no builds; keep section 900-1200 words
protocol_version: v1
-->

# Handoff Turn 1 - Start Section Pass

Revise only the first section. Explain the metaphor before using it, remove
self-reference, and keep the word count between 900 and 1200 words. Reply with
the edited span and a short audit.
```

## Standing Constraints

Repeat standing constraints in every header. Do not rely on memory.

Examples:

```text
constraint: no .lean edits without per-edit human approval; no lake/lean/build
constraint: do not modify device/out
constraint: docs only; no source edits
constraint: no destructive commands
```

If an agent violates or nearly violates a constraint, the next handoff should
withdraw the recommendation explicitly.

## Artifact Ownership

At any moment, exactly one agent owns each editable artifact. The owner is named
in the handoff's `scope:` field as the writer or implementer. The other agent
reads the artifact and proposes changes through handoff text, not direct edits.

If both agents need to edit the same artifact, hand ownership across explicitly:

```text
Agent A: status CHANGES_APPLIED; handing scope to agent_b
Agent B: status CHANGES_APPLIED; edits made; scope returns to agent_a
```

Concurrent edits to a single artifact can overwrite each other. The watcher
cannot prevent this; the discipline must.

## Withdrawals And Corrections

Use `status: WITHDRAWN` when an entire prior handoff is being retracted, such as
a misaddressed message, a wrong artifact, or a premature convergence claim.

Use an inline correction when only one recommendation inside a live handoff is
being retracted. The current turn's status may still be `NEEDS_RESPONSE`,
`CHANGES_REQUESTED`, or whatever fits the live work.

Example:

```text
Correction: In turn 12 I suggested running a build. That violated the standing
constraint. Withdrawn. Future references to a build are future experiments only
and require explicit human approval.
```

Corrections should cite the turn being corrected and say what replaces it.

## Human Approval Gates

The RYOT operator must explicitly approve:

- source edits during a diagnosis-only loop;
- builds, tests, or long experiments;
- network access;
- destructive commands;
- major semantic changes;
- changes that invalidate cached work;
- starting a second live job on the same inbox pair.

If the agents cannot proceed safely without the RYOT operator, send a handoff
with `status: BLOCKED`. The body should ask the smallest concrete question that
unblocks the job.

## Iteration Pattern

Each round should tighten the problem.

Useful body structure:

```text
1. Current state
2. What I checked
3. Findings
4. Proposed change or patch shape
5. Questions for the other agent
6. Human decisions needed
```

## Pre-Convergence Checklist

Before sending `CONVERGED`, verify:

```text
[ ] All open questions are answered or explicitly handed to the RYOT operator.
[ ] Standing constraints are still satisfied.
[ ] Accepted, rejected, and deferred patch shapes are named.
[ ] The final artifact state is summarized.
[ ] No hidden NEEDS_RESPONSE or BLOCKED item remains.
[ ] The other agent is asked to acknowledge and stop.
```

## Convergence And Stop

Use two-phase stop.

Phase 1:

```text
Agent A sends status: CONVERGED
```

Agent A summarizes the accepted state and asks Agent B to acknowledge.

Phase 2:

```text
Agent B sends status: HANDOFF_CONVERGED
```

Agent B confirms agreement and stops listening for that job.

If Agent B does not agree that the job is complete, Agent B replies with
`CHANGES_REQUESTED`, not `HANDOFF_CONVERGED`. There is no unilateral stop.

## Parallel RYOT Jobs

Default rule: run one job at a time per inbox pair.

If jobs truly run in parallel, use per-task inboxes and per-task state files:

```text
notes_for_agent_a_<task>.md
notes_for_agent_b_<task>.md
.handoff_agent_a_<task>_state
.handoff_agent_b_<task>_state
```

One state file per direction is fine for a single serialized queue. It is not
enough when two tasks can produce independent turn sequences at the same time.

## Failure Modes

Stale turn:

```text
Symptom: watcher ignores the handoff.
Cause: turn number was already processed.
Fix: resend with a higher turn number.
```

Wrong recipient:

```text
Symptom: watcher says the file is addressed to another agent.
Cause: `to:` does not match the watcher agent id.
Fix: correct `to:` and bump the turn if needed.
```

Self-addressed loop:

```text
Symptom: agent appears to answer itself.
Cause: watcher or inbox is misconfigured.
Fix: ensure each agent writes only to the other agent's inbox.
```

Constraint drift:

```text
Symptom: forbidden edits, builds, or commands are proposed.
Cause: constraints were omitted in later turns.
Fix: repeat constraints in every header and withdraw bad recommendations.
```

Convergence theater:

```text
Symptom: agents stop while questions remain.
Cause: convergence was declared for social closure, not because the job closed.
Fix: use the pre-convergence checklist.
```

Concurrent writes:

```text
Symptom: one message disappears.
Cause: two processes wrote the same inbox or artifact.
Fix: enforce one writer per inbox and one owner per artifact.
```

Context loss:

```text
Symptom: agent repeats old questions or misses decisions.
Cause: prior conversation context was compacted or forgotten.
Fix: make every handoff self-contained.
```

## RYOT Example Review Handoff

```markdown
<!-- HANDOFF
from: reviewer
to: implementer
turn: 12
status: NEEDS_RESPONSE
respond_to_sha: 8f1b2c3d
stop_token: HANDOFF_CONVERGED
task: build-output-diagnosis
scope: patch shape only
stop_mode: two-phase
grading: strict
constraint: no source edits; do not run build
protocol_version: v1
-->

# Handoff Turn 12 - Build Output Diagnosis

I read `out`, hash `8f1b2c3d`. The hard failure is in `module/foo.ext`.

Findings:

- `module/foo.ext:42` passes a value with the wrong shape.
- `module/foo.ext:61` triggers a large dependency search.

Patch shape:

```text
Replace the constructor argument with the canonical value produced earlier in
the pipeline.
```

Questions:

1. Do you agree this is the constructor fix?
2. Should the dependency be referenced by name rather than rediscovered?
3. Is the warning part of this patch or a separate experiment?
```
```

## RYOT Example Prose Handoff

```markdown
<!-- HANDOFF
from: editor
to: writer
turn: 8
status: CHANGES_REQUESTED
respond_to_sha: chap2-draft-3
stop_token: HANDOFF_CONVERGED
task: volume3-chapter2-voice-pass
scope: section "The Galileo Page" (lines 412-540)
stop_mode: two-phase
grading: strict
constraint: do not change cited dates, names, or quotations; keep 900-1100 words
protocol_version: v1
-->

# Handoff Turn 8 - Section Voice Pass

Span: lines 412-540 of `volume3-chapter2.md`.

Findings:

- "the reader" appears at lines 421, 469, and 503.
- the metaphor "carrier under load" appears before it is anchored.
- word count is 1162; soft ceiling is 1100.

Changes requested:

1. Replace "the reader" with direct address or removal.
2. Anchor the carrier-under-load metaphor before using it.
3. Bring word count to 1050-1100 by trimming repeated cadence paragraphs.

Quote each replacement in your reply with old/new line content so I can verify
before you commit.
```

## Agent Checklist

Before replying:

```text
[ ] Is the handoff addressed to me?
[ ] Is this the newest turn?
[ ] Did I inspect the referenced artifact?
[ ] Did I separate observations from inferences?
[ ] Am I proposing a patch, or actually applying one?
[ ] Do I need human approval?
[ ] Did I preserve constraints?
[ ] Did I use a fresh turn number?
```

Before editing:

```text
[ ] The current loop permits edits.
[ ] The artifact is the one named in scope.
[ ] I am the current artifact owner.
[ ] I am not overwriting another live job.
[ ] The RYOT operator has approved any risky action.
```

## Adaptation Notes

For code:

- lead with bugs and risks;
- include build output hashes;
- cite file paths and line numbers;
- separate compile fixes from semantic fixes;
- do not run expensive tests without approval.

For books or documents:

- separate voice, structure, correctness, and constraints;
- set section scope;
- set word budgets if relevant;
- state voice constraints;
- track prohibited terms explicitly.

For formalization:

- separate syntax errors, universe/typeclass problems, semantic claims, and
  proof strategy;
- distinguish definitions, lemmas, intended theorems, and experiments;
- identify what is proved, assumed, or metaphorical;
- keep search/runtime experiments separate from proof patches.

For long-running experiments:

- preserve exact input hashes;
- record settings;
- do not change debug options without approval;
- state what the next output should prove or disprove.

For non-deterministic outputs:

- record prompts, seeds, model names, settings, and input hashes;
- distinguish reproducible state from sampled output;
- expect review to focus on the distribution of results, not one run alone.

## RYOT Final Rule

RYOT works when each agent preserves the other agent's future context.
Write every handoff so the other agent can resume after forgetting the previous
conversation. If that feels repetitive, it is probably doing its job.

Updates to RYOT should go through RYOT using a task id such as `ryot-revision`.
