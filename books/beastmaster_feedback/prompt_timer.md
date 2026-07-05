# Prompt Timer

No prompt automation is active by default.

If the operator explicitly starts this lane, use minimal wake prompts and keep
state in `ryot/tasks/book-feedback-beastmaster.md`.

Beastmaster prompt:

```text
Check your inbox. If it is idle then add one focused review slice. If you are
waiting for something to be acknowledged, wait. Preserve the hard wall.
```

Auditor prompt:

```text
Check your inbox and respond. Preserve the hard wall.
```

Cadence:

- Use a slow cadence for quiet monitoring.
- Use a short cadence only during an active review exchange.
- Never schedule wakes that collide with another known lane.

Stop conditions:

- No newer handoff is available.
- The next action requires operator approval.
- The next action would inspect or affect another RYOT process.
- A review would require edits, builds, tests, network calls, or destructive
  commands.
