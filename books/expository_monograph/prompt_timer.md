# Prompt Timer Runbook

The book lane wakes each agent through its own prompt-scheduling mechanism ---
whatever recurring self-prompt or scheduled-wakeup feature its runtime provides.
RYOT does not prescribe a specific vendor tool; the LLM holding the seat
schedules its own wakes.

## Timer Contract

At each scheduled wake:

```text
1. Read the inbox, handled-state file, and active checkpoint directly.
2. If there is an unhandled Codex handoff, process exactly one handoff.
3. If there is no unhandled handoff, stay quiet unless the build steward is due
   and fails.
4. Do not start an unbounded loop. One bounded check per wake, then stop.
```

The wake check is deterministic and the agent performs it itself by reading the
files directly:

```text
- notes_for_codex.md           the Codex/Kodo inbox
- .handoff_codex_state         handled turns
- ryot/tasks/drafting_book.md  the active gate
- compare the newest valid addressed handoff against handled state
```

## Setting The Timer

Use whatever prompt-scheduling / self-wakeup mechanism your runtime provides ---
for example a recurring self-prompt or a scheduled wakeup. Set it to wake on the
desired cadence: usually every 3 minutes while Kodo and Podo are actively
exchanging turns, and slower or paused during a quiet wait.

Prompt for the wake:

```text
Reread RYOT.md and the Measurement book prompt-timer protocol in
/Users/williamcochran/Desktop/measurement/books/expository_monograph/prompt_timer.md.
Read the inbox and state files directly. If there is an unhandled Codex handoff,
process exactly one handoff according to the current outline-first gate. If it
is idle, stay quiet unless the build steward subcheck is due and fails. Do not
run unbounded loops, do not edit Lean files, do not run Lean/Lake/source builds,
do not use network access, and do not open a LaTeX gate unless Kodo has marked
the piece OUTLINE_AGREED.
```

## Gate Rules

```text
current active gate = read ryot/tasks/drafting_book.md
Codex handled state = .handoff_codex_state
idle-counter state  = .ryot_idle_ping_state
build steward state = .book_build_steward_state
```

The scheduled wake owns wakeups only. It does not own the book. Kodo still owns
acceptance gates; Podo still owns restricted doer turns.

## Quiet Cases

Return no user-facing notice when:

```text
the wake check is idle
the build steward is not due
the build steward succeeds
the build steward finds no build surface
```

Notify only when:

```text
a handoff was handled and the user should know
the build steward fails
the wake check cannot run
the active gate is inconsistent or unsafe
```
