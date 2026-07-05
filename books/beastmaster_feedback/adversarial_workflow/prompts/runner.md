# Runner Prompt

Use this prompt in a normal Codex thread to run the adversarial workflow without
Ryot.

```
Set up and run the standalone adversarial book-code drift audit in
books/beastmaster_feedback/adversarial_workflow.

Rules:
- Do not use Ryot timers, inboxes, automations, process inspection, or any
  unrelated coordination state.
- Do not inspect or communicate with any other Ryot process.
- Do not edit book prose or Lean/source code.
- Do not run builds, tests, network calls, destructive commands, process
  inspection, prompt timers, or automations without explicit operator approval.
- Do not suggest fixes to device/Measurement/Episode1.lean through
  device/Measurement/Episode16.lean.

Run this as an adversarial review:
1. Give Kodo the prompt in
   books/beastmaster_feedback/adversarial_workflow/prompts/kodo.md.
2. Give Podo the prompt in
   books/beastmaster_feedback/adversarial_workflow/prompts/podo.md, plus
   Kodo's candidate ledger.
3. Run the judge pass using
   books/beastmaster_feedback/adversarial_workflow/prompts/judge.md.

The final product must follow
books/beastmaster_feedback/adversarial_workflow/ledger_template.md.

Treat every device/Measurement/Episode*.lean and
device/Measurement/Meanwhile*.lean file as part of the unfinished but necessary
proof surface. Audit outline documentation first, then manuscript prose.
```
