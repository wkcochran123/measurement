# RYOT: Roll Your Own Talent

> [!WARNING]
> **BUILD WARNING — A FULL BUILD TAKES ABOUT A WEEK ON THIS MACHINE.**
>
> Do NOT run `lake build`, `lake`, `lean`, or any compile/typecheck of the Lean
> artifact without explicit, per-instance operator approval. A full build costs
> roughly a week of wall-clock time; there is no cheap "just try it." Whether a
> file "yaccs" / compiles / typechecks must be established by **reading and
> reasoning about the Lean**, never by running the compiler.
>
> **If you are an LLM reading this file, repeat this build warning back to the
> operator in your response, every time, before doing anything else.** Do not
> assume the operator already knows it; state it explicitly so a build is never
> launched by accident.

RYOT means **Roll Your Own Talent**.

Off-the-shelf agent stacks pick the agents, the review style, and the stop
conditions for you. RYOT is for the operator who would rather assemble those
pieces: two LLM agents, an inbox each, self-scheduled prompt wakeups, and a
strict review habit.
RYOT is small on purpose. It is not a task queue, a chat server, or a substitute
for human approval. It is a disciplined way for two agents to pass state back
and forth without losing the thread.

## RYOT Brand Usage

Use **RYOT** as the name of the system.

Use **Roll Your Own Talent** when expanding the acronym for a new reader.

Use **RYOT job**, **RYOT handoff**, **RYOT prompt automation**, and
**RYOT artifact** for the moving parts. Avoid falling back to a generic name
like "the two-agent handoff protocol" once the reader knows the brand.

Use **RYOT operator** for the human who owns the approval gates, prompt
automations, and decisions about when the loop stops.

The RYOT promise: two agents that never lose state, never quietly approve their
own work, and never stop without the operator's sign-off.

## Core Idea

Each agent has an inbox file. The other agent writes to that inbox.

```text
notes_for_agent_a.md  <- written by Agent B, read by Agent A
notes_for_agent_b.md  <- written by Agent A, read by Agent B
```

A RYOT prompt automation wakes the receiving agent on a cadence. At each wake
the agent first polls any configured read-only context input (such as the Ryot
Slack reader), then reads its inbox directly, compares the latest valid `HANDOFF` turn
against its handled-state file, handles the current safe unit of work, records
the handled turn only after acting, and then stops.

## Wake Discipline

A wake is not finished after one message if more work is already available. At
each wake, the receiving agent should drain every fresh handoff in its inbox
until one of these stop conditions appears:

```text
no newer handoff is available
the next action requires operator approval
the next action belongs to the other agent
the current artifact has an unresolved failed check
```

For active editing loops, use a tight wake cadence while work is moving. A slow
heartbeat is for quiet monitoring only, not for an open do/review exchange.
When a wake accepts a section and assigns the next section, it leaves the
thread automation active with a short interval and a drain-all instruction.

The RYOT operator owns the dangerous parts:

- approving source edits, builds, long experiments, and destructive commands;
- deciding when jobs may run in parallel;
- maintaining or pausing prompt automations;
- stopping the loop when the agents need judgment rather than more iteration.

## Files And Roles

A minimal RYOT setup needs:

```text
notes_for_agent_a.md
notes_for_agent_b.md
.handoff_agent_a_state
.handoff_agent_b_state
one prompt automation per active receiving agent
```

In this repository the concrete names are the seat names:

```text
notes_for_kodo.md
notes_for_podo.md
.handoff_kodo_state
.handoff_podo_state
each agent's own prompt-scheduling wake for each live receiving role
```

The `.handoff_<agent>_state` files are handled ledgers: they say which handoffs
the agent has actually processed. RYOT uses no separate delivery ledgers. A
scheduled wake may notice a handoff many times,
but it must update handled state only after the receiving agent has actually
accepted, rejected, blocked, or otherwise recorded that handoff.

Agents can be symmetric peers, but most jobs benefit from temporary roles:

```text
Writer / Reviewer
Implementer / Auditor
Proof author / Formalism critic
Drafting agent / Style and correctness grader
Patch author / Build-output diagnostician
Doer / Thinker-planner
Podo / Kodo
```

State the roles in the first handoff for each job.

## Kodo / Podo Split

Kodo and Podo are the preferred RYOT names for the thinker/doer split.

```text
Kodo  thinker-planner, reviewer, budget/order keeper, formalism critic,
      UAT/checkpoint owner, and final acceptance gate.

Podo  doer-agent, patch author, proof writer, drafter, build/report runner,
      and uncertainty reporter inside the restricted prompt.
```

Routing and seat are separate. A seat (Kodo or Podo) is a role; which underlying
agent runs that seat is a routing choice recorded in the session's inbox header
(the `route:` field on the `<!-- RYOT INBOX ... -->` marker), never in this
protocol doc. Either seat may be run by any capable agent, and the route↔seat
binding may flip between sessions — confirm a seat by which inbox it writes to,
not by which agent it is. Whoever runs Podo must accept the doer contract and
must not claim Kodo's final gate-closing authority.

For jobs that use Kodo/Podo:

```text
Podo  writes code, drafts prose, applies patches, runs authorized checks, and
      reports exact changed files, hashes, output, and uncertain points.

Kodo  reads state, chooses the next concrete task, critiques the result,
      catches overclaims, and keeps the operator's approval gates explicit.
```

If there is unblocked work and Podo appears idle, Kodo should send the next
small actionable handoff rather than waiting passively. If Podo cannot
continue, it should write `BLOCKED` with the smallest concrete question and
stop.

## Question Routing

Questions stay inside the doer/reviewer loop. Kodo and Podo direct questions
ONLY to each other:

```text
Kodo asks Podo.
Podo asks Kodo.
Neither agent asks the operator.
If Kodo has a question, Podo asks it -- it is resolved in-loop, never carried
  up to the operator.
```

The operator initiates work and rules on approval gates; the operator is never
a question-target. Agents REPORT to the operator (status, findings, and a
`BLOCKED` approval gate for an action that genuinely needs the operator's
sign-off) but do not interrogate the operator or hand it their uncertainties to
resolve. A doer's uncertainty goes to the reviewer; a reviewer's uncertainty is
worked out in the loop by tasking the doer to investigate -- not by asking the
operator. Going around the loop to the operator is a chain-of-command breach.

## Beastmaster

The beastmaster is an occasional "(semi)-outside verifier" layered over a
Kodo/Podo job. Most jobs never need one. It is semi-outside by design: inside
enough to read the live state and feed the loop through Kodo's inbox, yet
outside enough to verify the whole artifact on its own terms and refuse capture
by the pair's local gates. A beastmaster is warranted when the doer/reviewer
pair has begun solving problems in ways that clear each local gate yet drift
away from what the operator actually wants across the whole artifact ---
"unorthodox" problem solving that is locally clever and globally wrong.

```text
Kodo / Podo   produce and review one section at a time.
Beastmaster   watches the whole world around the pair: the full artifact, the
              source it claims to restate, the operator's standing mandates,
              and the arc no per-section gate can see.
```

Charter:

```text
- Give feedback, do not solve. The beastmaster never owns or edits the produced
  artifact (book prose, proof code). It reads, judges, and reports.
- Hold the cross-cutting mandates a section gate is blind to: voice, idiom,
  source-leakage, fidelity to the source, and global scope.
- Keep the pair moving and in bounds: rein in drift, unblock stalls, and refuse
  premature convergence.
- Own the completion call. The beastmaster declares the job done only when its
  mandates hold across the whole artifact, and sends Kodo and Podo back to work
  when they do not. This is a stricter, later gate than Kodo's per-section
  acceptance, never a replacement for it.
```

Discipline:

```text
- Advisory to Kodo's gates. The beastmaster recommends; Kodo issues the gate to
  Podo. The beastmaster does not open or close writing gates directly.
- Keep role authority distinct from process orchestration. At the operator's
  explicit request, the beastmaster may provision or wake separate Kodo and
  Podo processes. Launching a process is not a writing gate and does not give
  the beastmaster authority to assign Podo artifact work: the beastmaster gives
  the operator context to Kodo, and Kodo issues any artifact task or gate to
  Podo. If the runtime cannot launch a process, report that technical limit;
  never misstate the feedback-only charter as forbidding the launch itself.
- Do not corrupt the turn machinery. The receiver's handled-state integer
  tracks the doer/reviewer turn stream only. Beastmaster feedback goes to its
  own ledger (long reviews) plus a short, clearly marked advisory pointer in
  Kodo's inbox --- never a doer/reviewer turn number.
- Separate K-items from P-items. A K-item needs a Kodo ruling; a P-item is a
  doer fix contingent on Kodo opening a revision gate.
- One small cycle at a time. Each beastmaster cycle files at most one refinement
  and one focused review, then stops.
```

The beastmaster keeps a private coordination ledger, never reader-facing, that
records its mandate, its running verdicts, and its cycle log.

### Beastmaster Message Format (the out-of-band channel)

A beastmaster never writes a numbered HANDOFF. The turn integer is the two-party
(doer/reviewer) monotonic contract; a third party writing into it forces a
collision --- two blocks claim the same N, and the receiver's handled-state skips
one. (This happened: an operator/beastmaster block filed as `turn: 804` clobbered
the doer's own `turn: 804`, and the doer's verdicts went stale.) The beastmaster
is out-of-band by construction: no turn number, a separate zone, a separate ack.

It inserts an **unnumbered BEASTMASTER block** so the receiver instantly knows the
message is out-of-band --- it did not come from the other seat and does not belong
to the turn stream:

```markdown
<!-- BEASTMASTER
from: beastmaster
to: kodo
id: bm-<short-slug>            # unique slug, NEVER a turn number
kind: interrupt | advisory     # interrupt = handle before anything else; advisory = read before your next gate
task: short-task-id
re: what-this-touches
status: NEEDS_ACK
-->
... message body ...
<!-- END BEASTMASTER -->
```

Placement: at the **top** of the inbox, in the `<!-- BEASTMASTER ZONE -->`
directly under the `<!-- RYOT INBOX ... -->` header marker and **above** the
numbered stream. Never interleaved with HANDOFF turns.

Receiver discipline:

```text
- At every wake, read the BEASTMASTER ZONE FIRST, before the numbered drain.
- kind: interrupt OVERRIDES the current plan --- handle it (or record the
  operator decision it carries) before processing any numbered turn.
- kind: advisory is read before the next gate but does not halt in-flight safe
  work.
- It NEVER changes the handled-state integer. The turn stream is untouched, so
  nothing the doer sent can be skipped by a beastmaster insert.
- Acknowledge by flipping status: NEEDS_ACK -> ACKED in place, and cite the id in
  the next HANDOFF you send (`acked: bm-<slug>`). Leave the block as a record, or
  move it to a beastmaster_log once acked.
- Ids are slugs, not integers, so beastmaster messages never collide with each
  other or with the turn stream. Two unacked messages are handled top-to-bottom.
```

The beastmaster still obeys the charter above: give feedback, do not solve;
advisory to Kodo's gates; one small cycle at a time. The out-of-band block is the
*delivery mechanism*, not a license to issue doer/reviewer gates directly ---
those still flow Kodo -> Podo as numbered turns.

## Loop Hygiene (retro 2026-07-05)

Five rules the last run learned the hard way. Together with the beastmaster
out-of-band channel above (injection discipline: operator/beastmaster never carry
a doer/reviewer turn number), these close the process gaps that forced a full
inbox reset.

```text
- Minimal wake prompts; state lives in the checkpoint. A wake prompt is
  "check your inbox and act" --- NEVER hardcode the current task ("do Ch14
  first"), which goes stale the moment work moves and turns the loop self-
  contradicting. The inbox + handled-state ARE the state; the prompt only wakes.

- Cull the box per accepted batch. When a batch is accepted, absorb its outcome
  into the checkpoint and archive its turns out of the live inbox. Never let the
  box grow unbounded --- a multi-hundred-turn, multi-MB inbox is a reset waiting
  to happen and slows every wake's read.

- Pause, don't heartbeat, at operator-gated stops. When the next action needs the
  operator and the operator is away, PAUSE the automation --- do not fire short
  wakes that produce idle "still holding" reports. Resume on the operator's
  return (or a Slack ping), not on a timer.

- Context-saturation tripwire. A single agent grinding ~15-20 near-identical units
  is the risk signal for contamination (task tokens leaking into the artifact ---
  e.g. writing "court" where the tag belongs). Hand off, reset the context, or
  split the run BEFORE the contamination shows, not after.

- Reset is two steps: disk AND session wakes. `ryot/reset.sh` clears on-disk
  inbox/checkpoint state but cannot cancel session-scoped wake automations
  (crons). A full reset must also cancel the crons --- make the wakes durable/
  disk-tracked, or keep a documented "cancel crons" step beside the reset.
```

## Parallel Lanes

A RYOT job may split into parallel lanes when the operator approves more than
one kind of work around the same subject.

Use one shared subject, one active inbox pair, and explicit lane labels:

```text
Lean lane      Doer writes isolated code; thinker-planner reviews theorem shape.
Prose lane     Thinker-planner drafts explanation; doer edits as domain critic.
Build lane     Operator or assigned doer runs the expensive experiment.
```

Every handoff should state which lane it concerns. If two lanes are active, the
agents should avoid blocking each other: code review can continue while prose is
drafted, and prose editing can wait until the doer is no longer in the middle of
a fragile patch. Shared claims must still converge through the same checkpoint
files before either lane declares victory.

## Multiple RYOT Jobs

Several RYOT jobs may run on the same machine at once. Treat project scope as a
first-class guardrail.

Each handoff should name the active workspace, task id, and owned artifacts.
Each agent should trust its own inbox, its own handled-state file, and
checkpoint files inside the active workspace. Process lists, terminal chatter,
and automation output from another workspace are noise unless the operator
explicitly connects the jobs.

When another RYOT job is known to be noisy, add a constraint like:

```text
ignore unrelated RYOT activity outside <workspace-or-task>
```

This keeps a long build, a noisy side project, or a second pair of agents from
becoming a false trigger in the current job.

## Two-Phase Do/Review

For paired code/prose work, use a two-phase cycle:

```text
Phase 1 - DO
  Agent A owns proof/code artifacts.
  Agent B owns prose/explanation artifacts.
  Both work in parallel and write compact progress handoffs.
  Neither agent edits the other's owned artifact during this phase.

Phase 2 - REVIEW
  Agent A reviews the prose for technical correctness.
  Agent B reviews the proof/code for theorem shape, assumptions, and exposition.
  Review produces explicit CHANGES_REQUESTED or HANDOFF_CONVERGED turns.
```

The handoff between phases must name artifact hashes, open risks, and the exact
review question. This keeps production parallel but correctness adversarial.
Do/review cycles may repeat many times under the same 500-step target.

## Section-Scoped Writing

When a RYOT job includes a book, article, long README, module document, or
other prose artifact, split writing work by section rather than by whole file.

Each writing handoff should name one target section:

```text
artifact: volume_7.md
section: Chapter 2 / Uncommon Path
goal: clarify the gate cascade for a public reader
checks: word budget, banned terms, citations, claim boundary
```

The receiving agent should edit or review only that section unless the handoff
explicitly labels the work as a mechanical whole-file check. Mechanical checks
include build, citation scan, banned-token scan, ASCII scan, and warning scan.
This keeps context local, makes critique sharper, and prevents a large prose
artifact from turning into one undifferentiated task.

## Proof-Backed Prose Stance

When the operator asks for prose written as though a proof stack compiles, write
from the theorem statement rather than from nervous process commentary. Keep
the formal boundaries visible, but avoid turning every sentence into a hedge.

If a prose section exposes a mismatch with the formal artifact, record a Lean
audit flag instead of weakening the prose until the mismatch disappears. The
reviewer should separate three cases:

```text
confirmed theorem surface       prose may speak directly
named bridge assumption          prose may speak directly inside that boundary
artifact/prose discrepancy       mark as Lean audit flag and queue proof review
```

This stance is especially useful when a long build is running. The prose lane
can advance from the accepted theorem design while the build lane remains
observational. If the build later fails, the RYOT job reopens the proof lane and
repairs the artifact rather than pretending the book never made a claim.

## RYOT Quickstart

1. Choose agent ids.
2. Choose roles for the first job.
3. Create inbox files.
4. Create state files with `last_turn=0`.
5. Create one prompt automation per receiving agent.
6. Seed the first handoff with `respond_to_sha: RYOT_START_<task>`.
7. At each automation wake, have the agent check its own inbox directly.
8. Continue until one agent sends `CONVERGED` and the other sends
   `HANDOFF_CONVERGED`.
9. Pause/delete the prompt automations or start the next job with a new task id.

To recover from a missed wake without replaying stale turns:

1. Pause the prompt automation if it is still firing badly.
2. Edit the state file so `last_turn` equals the highest already-processed
   turn from the latest valid handoff.
3. Re-enable the automation or send a one-time manual prompt to the agent.

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

Use the exact agent id configured for the receiving seat — the `route:` id in
that seat's inbox header — matching case exactly; if the id is lowercase, do not
capitalize it.

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

Keep prompt-automation behavior and human protocol aligned. An automation may
only stop or pause on the exact status values it implements.

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
processed turn will usually be ignored by the receiving agent's handled-state
check.

Crossed turns are normal. If both agents write before reading the other's latest
message, each should acknowledge the crossing, state which turn it is answering,
and carry forward any constraints or open questions that still apply.

## Starting And Waking A Process

A process may be provisioned by the operator or, at the operator's explicit
request, by a coordinating beastmaster. Provisioning is runtime orchestration,
not role authority: it neither assigns artifact work nor opens a writing gate.
Provisioning is complete only when the runtime returns a live process identity.
The beastmaster must not report a role as started, running, or provisioning
another role from intent alone. The newly launched role acknowledges its own
start through the operator-visible channel. Every operator request that enters
this route receives three distinct role-authored acknowledgements:

```text
Beastmaster  acknowledges receipt and routing of the operator request.
Kodo         acknowledges review ownership and the task it will gate to Podo.
Podo         acknowledges the concrete assignment it accepted from Kodo.
```

One acknowledgement never stands in for another. Beastmaster does not announce
Kodo or Podo as though they had spoken; Kodo does not announce Podo's receipt.
A missing role-authored acknowledgement is a failed or unconfirmed hop, not
permission for another role to impersonate success.

When the request produces operator-facing artifacts, Kodo returns the reviewed
artifact paths and provenance to Beastmaster. Beastmaster performs the guarded
upload to the operator-visible channel and reports the upload receipt. The task
is not externally delivered merely because files exist locally. If upload
preflight or Slack file authorization fails, Beastmaster must not retry an
ambiguous write or claim delivery; it reports the exact non-secret failure and
keeps the reviewed local artifacts intact.

After every required result has passed Kodo review and every required external
delivery has a confirmed receipt, Beastmaster posts the closing acknowledgement
in its own voice: the process is done, what was delivered, and where. This is
the terminal counterpart to Beastmaster's opening receipt. Beastmaster never
posts the closing acknowledgement while review, delivery, or another promised
step remains incomplete.
The provisioned process is not yet a participant. "Up" is not "listening":
until the operator issues an explicit start, the process holds and does nothing.
Two operator commands drive it:

```text
RYOT START <role> <task>
  Bring a process into the job. On START the agent, in order:
  - rereads RYOT.md, its task checkpoint, its inbox, and its handled-state;
  - adopts its route id and existing files without resetting or replaying them;
  - drains every fresh handoff per Wake Discipline;
  - then stops.

RYOT WAKE <role>
  A routine tick once started: the same bounded check, assuming context is
  already loaded. This is what a self-scheduled wakeup issues.
```

A process acts only after an explicit START; START is the operator's gate for
when a process may begin, and WAKE keeps it in the loop afterward. To stop a
process, the operator pauses its wakeups; to restart it, issue START again. A
START handoff may carry constraints (e.g. "hold all writing gates pending the
beastmaster directive") just like any other handoff.

## Prompt Automations

RYOT uses the agent's own prompt scheduling mechanism as the wake mechanism:
whatever recurring self-prompt or scheduled-wakeup feature the agent's runtime
provides. RYOT does not prescribe a specific vendor tool, and each wake is one
bounded check rather than a loop.

### Optional Slack polling reader

`ryot/plugins/slack_reader/` provides a read-only context poll for an operator
Slack conversation. When configured, each Beastmaster, Kodo, or Podo wake polls
the newest messages once (default 20) before reading local loop state. The
snapshot is cached per role under `.ryot-cache/slack/`, so the three seats have
independent new-message cursors and a failed poll can fall back to the last good
snapshot.

Slack remains advisory. It is not an inbox, cannot alter a handled-state
integer, and cannot open or close a writing gate. An actor that discovers an
operative decision there must carry it into the normal Beastmaster or Kodo/Podo
channel before treating it as Ryot state. See
`ryot/plugins/slack_reader/README.md` for setup and the exact command.

After the actor writes its authoritative handoff/checkpoint, the same bridge may
post one role-labeled mirror back to Slack. Post only after the filesystem write
succeeds. The `post` operation must perform a fresh last-20 Slack check and
update the role cache immediately before the write; if that check fails, it
must not post. Posting failure never rolls back loop state, and an ambiguous
write failure is never retried automatically. The mirror is for operator
visibility; the file remains the record.

At each wake, the receiving agent performs one bounded check:

```text
poll configured read-only context inputs once (Slack, if enabled)
read the BEASTMASTER ZONE
read INBOX
find the newest valid HANDOFF addressed to AGENT
ignore malformed, self-authored, or misaddressed handoffs
compare turn against .handoff_<agent>_state
if turn is fresh, handle the safe current unit of work
record handled state only after the response/checkpoint is written
stop
```

The prompt automation is not a proof worker by itself. It wakes the agent, and
the agent applies the normal RYOT constraints, ownership rules, and approval
gates. During an active exchange, a 3-minute heartbeat is appropriate. During a
quiet wait, use a slower cadence or pause the automation.

The automation prompt should name:

```text
workspace root
agent id
inbox file
handled-state file
task checkpoint
current lane constraints
what to report when idle or blocked
```

## Inbox Discipline And Task Checkpoints

RYOT inboxes are append-only while messages are in flight. Writers append new
handoffs; they do not overwrite unread handoffs. Prompt automations wake the
receiving agent, and the receiving agent uses handled-state files to decide
which addressed `HANDOFF` blocks are still fresh.

> [!IMPORTANT]
> Append-only inboxes are a delivery guarantee, not long-term memory. When a
> task starts to repeat context, grows expensive to read, or crosses a check-in
> boundary, recycle the message box: absorb processed decisions into
> `ryot/tasks/<task-id>.md`, compact the inbox, and continue from the
> checkpoint. Before acting after a wakeup, reread `RYOT.md` and the relevant
> task checkpoint so the current turn is grounded in the latest written state,
> not only in model context.

A check-in boundary is one of:

- a task's two-phase convergence completes (`HANDOFF_CONVERGED` received and
  ratified);
- the RYOT operator requests it;
- the inbox exceeds an agreed size threshold and all in-flight handoffs have
  been processed.

At a check-in boundary, agents may compact the inbox. Compaction appends an
entry to the relevant task checkpoint recording:

- the turn range compacted, such as `turns 451-457`;
- the decisions accepted during that range;
- any deferred or rolled-back proposals named explicitly;
- the resulting artifact hash at the end of the range.

After the entry is written, the compacted `HANDOFF` blocks may be moved to
`ryot/archive/<task>-<turn-range>.md` or deleted. Compaction must never delete
an unread handoff or an unresolved decision.

A handoff may not be compacted until both conditions hold:

1. The receiving agent's handled-state file has advanced past the handoff turn.
2. The relevant task checkpoint has been updated to absorb its content.

Compaction races violate the delivery guarantee even when the prompt automation
is firing correctly.

For long jobs or parallel work, each task keeps a compact checkpoint at
`ryot/tasks/<task-id>.md`. The checkpoint is a state vector, not a transcript:
task id, owner, artifact anchors, accepted decisions, open questions, blocked
approvals, next action, and last turn seen from each agent. The checkpoint is
the source of truth when the inbox is lost or an agent's context is compacted.

Cross-task changes require ownership acknowledgement. A task may edit only its
owned artifacts and checkpoint. If it needs to affect `RYOT.md`, another task's
checkpoint, or another task's artifact, it proposes the change in a fresh
handoff under `task: ryot-revision` or a dedicated merge task. Apply only after
the affected owner acknowledges.

Promote to a formal merge ledger only when three or more live tasks contend on
the same artifact or when merge decisions themselves become hard to track.

## Culling A Box

A box grows without bound because handoffs are append-only. Culling reclaims the
box by moving processed handoffs out of it. Culling is operator-gated and must
preserve the delivery guarantee. A box may be culled by hand or by a small tool
the doer writes to this spec; the invariants are the same either way.

```text
1. HANDLED ONLY. A block is cullable only if its turn <= the receiver's handled
   threshold for that block's sender. Respect both state formats:
   `last_turn=N` (one queue) and `last_turn_from_<sender>=N` (per sender).
2. NEVER A FRESH BLOCK. A handoff the receiver has not processed, or any
   unresolved decision, is never removed. Blocks with no parseable turn
   (INFO_ONLY heartbeats, anything unrecognized) are kept.
3. KEEP ANCHORS. Retain the last few handled blocks (default three) so recent
   context and respond_to_sha references survive in the live box.
4. ARCHIVE, DO NOT DELETE. Move culled blocks to
   <box_dir>/ryot/archive/<box>-turns-<lo>-<hi>.md and append one line to a
   compaction log. The live box keeps a one-line header pointing to the archive.
5. ATOMIC AND QUIET. Rewrite via temp-file + rename, and only while the loop is
   paused or between wakes. Re-check the box's size/mtime just before the rename;
   if it changed, abort and retry --- never clobber a concurrent append.
6. CHECKPOINT. Record the culled turn range and the decisions it absorbed in the
   task checkpoint --- the semantic step a tool cannot do.
7. ONE OWNER. A box belongs to one job; cull it only with that job's owner's
   acknowledgement, since handled-state and turn streams differ across jobs.
```

Culling changes the box's bytes but not its meaning: handled-state is keyed by
turn integer and `respond_to_sha` points at artifacts, so neither is disturbed.

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

Concurrent edits to a single artifact can overwrite each other. The automation
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

## Heartbeat Updates

When an agent is waiting on a long-running process --- a build, a slow
experiment, an operator-controlled run, any task that does not complete
inside a single agent turn --- send an `INFO_ONLY` heartbeat update to
the other agent every 15 minutes. The heartbeat is short: elapsed time,
latest visible progress (target reached, last log line, output file
size), and a one-line forecast.

The point is to keep the loop alive without keeping an agent turn busy staring
at a silent file. A heartbeat says "still running, no new findings, will report
on completion."

If the long-running process completes between heartbeats, skip the
heartbeat and send the actual diagnostic turn instead. If three
consecutive heartbeats show no progress, escalate to `BLOCKED` and
ask the RYOT operator whether to keep waiting.

A heartbeat is a turn like any other. Use a fresh turn number, the
running task id, and `status: INFO_ONLY`. Set `respond_to_sha` to the
artifact or output the long-running process targets, so the other
agent can re-anchor when the wait ends.

## Wake Mechanism

A heartbeat discipline is only as reliable as the agent's wake mechanism. RYOT
uses each agent's own prompt scheduling mechanism: the agent schedules its own
wakes on a cadence and gives itself a normal prompt; at each wake it reads the
inbox and state files itself.

For an active two-agent exchange, set the heartbeat to a short interval, usually
3 minutes. For long quiet waits, slow the heartbeat or pause it.

Each wake must be bounded:

```text
1. Poll each configured read-only context input once; use its local cache if stale.
2. Read the Beastmaster zone, then inspect the agent's inbox.
3. Compare the newest valid addressed handoff with handled state.
4. If a fresh handoff exists, process exactly the current safe unit of work.
5. If no fresh handoff exists, report a short idle status.
6. Do not start an unbounded loop; one bounded check per wake, then stop.
```

If the automation cannot prove delivery of unread handoffs, the system must use
manual operator pings until the automation is repaired.

## Wake-Phase Lanes

Two agents that run self-scheduled wakes against the same workspace must not
fire in the same minute. Simultaneous wakes run two sessions at once; even with
disjoint inboxes they race on the shared checkpoint and contend for the box. A
bare `*/N` schedule lands every agent on :00 and guarantees the collision.

Give each agent a wake-phase lane. The robust scheme is a **residue lane**:
assign each agent a distinct residue class mod M (M >= number of agents), and
let every one of its wakes fall in that class. Two agents on different residues
never share a minute --- at *any* cadence, even different cadences --- because a
wake only ever lands on a minute in its own class.

```text
Residue lanes (mod 3), two agents, independent cadences:
  Podo lane   minutes ≡ 2 (mod 3)   2,5,8,...,59      (offset 2, 3-min: `2-59/3`)
  Kodo lane   minutes ≡ 1 (mod 3)   1,10,19,...,55    (offset 1, ~9-min: `1-59/9`)
                                    quiet: 1,31       (offset 1, ~30-min: `1,31`)
  ≡ 0 (mod 3) left EMPTY -> dodges :00,:15,:30,:45 (all ≡ 0).
```

The trick: stay in your class by using a stride that is a multiple of M. With
M = 3, strides of 3/9/12/30 from offset 1 all stay ≡ 1 (mod 3); Podo at offset 2
stays ≡ 2. The two never coincide no matter how often each fires. (A simpler
same-base / different-offset scheme works only while both agents keep the *same*
base interval; the moment one re-cadences to a different base, their offsets can
realign. Residue lanes are immune to that.)

Rules:

```text
1. DISTINCT RESIDUE, ANY CADENCE. Each agent owns a residue class mod M and only
   wakes within it (stride = a multiple of M from its offset). Distinct residues
   never share a minute, even at different cadences. Leave the ≡0 class empty to
   dodge the :00/:15/:30/:45 fleet marks; never use a bare `*/N` (lands on :00).
2. KEEP YOUR OFFSET. When an agent retightens or slows its cadence, change the
   interval, not the offset. The lane is stable for the life of the job.
3. ONE WRITER PER FILE STILL HOLDS. Lanes reduce overlap; they do not license
   shared writes. Each agent writes only the peer inbox (append-only) and its
   own handled-state file. The task checkpoint has a single owner (Kodo / the
   reviewer); the doer reports through its inbox and never co-writes the
   checkpoint. Any unavoidable shared write uses temp-file + atomic rename with
   an mtime re-check (see Culling A Box, rule 5).
4. RECURRING, NOT IDLE-GATED. Use a true recurring wake. An idle-only wake is
   starved by long active or build turns and silently misses handoffs; the next
   recurring wake's bounded drain catches up safely. A missed wake is recovered
   by an operator WAKE, not by a tighter idle trigger.
5. RECORD THE LANE. Put each agent's lane (offset + interval) in the task
   checkpoint (state lives there, not in the prompt — see Wake Prompts).
```

## Wake Prompts

Keep the wake prompt MINIMAL. State lives in the task checkpoint, reread on every
wake (per Inbox Discipline And Task Checkpoints) — it is not stuffed into the
prompt. This supersedes the older "name workspace / inbox / lane / ... in the
prompt" guidance: a giant state-dump prompt rots and drifts from the checkpoint,
which is the single source of truth. The prompt carries the loop's *discipline*;
the checkpoint carries the *state*.

The two seats run DIFFERENT prompts, matching their roles.

Kodo (thinker / planner / reviewer) — must keep the loop fed, never idle on
un-blocked work, yet never manufacture filler:

```text
Poll Slack if configured, then check your inbox. If it is idle then add work.
If you are waiting for something to be acknowledged, wait. If you think there
is no unblocked work, verify with podo.
```

Podo (doer / writer / builder) — acts on whatever the inbox contains:

```text
Poll Slack if configured, then check your inbox and respond.
```

The asymmetry is the point. Kodo proactively generates and verifies work (design,
specs, reviews) so the loop never stalls on a false "nothing to do"; the
`verify with podo` clause forces a cross-check before Kodo settles into waiting
(it catches work Kodo wrongly bucketed as blocked). Podo is reactive: it responds
to Kodo's handoffs and reports results — it needs no generate/verify discipline
because its work is set by the inbox.

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
Symptom: agent ignores the handoff as already handled.
Cause: turn number was already processed.
Fix: resend with a higher turn number.
```

Wrong recipient:

```text
Symptom: agent says the file is addressed to another agent.
Cause: `to:` does not match the receiving agent id.
Fix: correct `to:` and bump the turn if needed.
```

Self-addressed loop:

```text
Symptom: agent appears to answer itself.
Cause: automation prompt or inbox route is misconfigured.
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
[ ] Did I reread RYOT.md and the relevant task checkpoint?
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
- use heartbeat prompt automations for long waits so agents do not spend active
  turns staring at silent files;
- send an `INFO_ONLY` heartbeat to the other agent every 15 minutes
  while waiting; see Heartbeat Updates above.

For non-deterministic outputs:

- record prompts, seeds, model names, settings, and input hashes;
- distinguish reproducible state from sampled output;
- expect review to focus on the distribution of results, not one run alone.

## RYOT Final Rule

RYOT works when each agent preserves the other agent's future context.
Write every handoff so the other agent can resume after forgetting the previous
conversation. If that feels repetitive, it is probably doing its job.

Updates to RYOT should go through RYOT using a task id such as `ryot-revision`.

## Safety Warning

Antigravity is dangerous to use as a RYOT agent. See file: [ANTIGRAVITY_IS_UNSAFE_TO_USE.md](ANTIGRAVITY_IS_UNSAFE_TO_USE.md).
