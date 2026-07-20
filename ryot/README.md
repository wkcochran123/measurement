# RYOT workspace (measurement)

Roll Your Own Talent setup for this repo. See [`../RYOT.md`](../RYOT.md) for the protocol.

## Routes and roles

| route    | RYOT role | seat                                   |
|----------|-----------|----------------------------------------|
| `codex`  | **Kodo**  | thinker / planner / reviewer / final gate |
| `claude` | **Podo**  | doer / writer / builder / uncertainty reporter |

## Files

Inboxes and handled-state are **role-named**, not route-named, so a seat survives a
route swap (e.g. a second codex could fill Podo):

```text
notes_for_podo.md       Podo inbox  — Kodo writes, Podo reads
notes_for_kodo.md       Kodo inbox  — Podo writes, Kodo reads
.handoff_podo_state     Podo handled-state ledger (last_turn=N)
.handoff_kodo_state     Kodo handled-state ledger (last_turn=N)
ryot/tasks/<task-id>.md task checkpoints (state vector, source of truth)
ryot/archive/           culled / compacted handoff blocks
```

(`notes_for*` and `.handoff*` are gitignored.)

## Wake-phase lanes (residue mod 3)

```text
Podo (claude)  minutes ≡ 2 (mod 3)   active: `2-59/3`   quiet: `2,32`
Kodo (codex)   minutes ≡ 1 (mod 3)   active: `1-59/9`   quiet: `1,31`
≡ 0 (mod 3) left EMPTY -> dodges :00/:15/:30/:45 fleet marks.
```

Each seat schedules only its own wake and writes only the peer inbox plus its own
handled-state file. The task checkpoint has a single owner (Kodo).

## Optional Slack context

The read-only polling input in [`plugins/slack_reader/`](plugins/slack_reader/)
can fetch the newest Slack messages (default 20) at the beginning of each wake.
It keeps a private local cache per Beastmaster/Kodo/Podo role. Slack context is
advisory and never replaces the inbox or handled-state ledger. After writing its
authoritative response, an actor may use the same bridge to post one visibly
role-labeled mirror back to Slack.
