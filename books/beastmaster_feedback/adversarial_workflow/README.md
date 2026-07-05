# Adversarial Book-Code Drift Workflow

This workflow replaces Ryot mechanics with a standalone adversarial audit. It
can be run manually in one Codex thread, with ordinary subagents, or by copying
the role prompts into separate sessions. It does not depend on timers, inbox
polling, prompt state, or another process.

## Purpose

Produce a tight, evidence-backed accounting of drift between:

- book text and outline documentation;
- `device/Measurement/Episode*.lean`;
- `device/Measurement/Meanwhile*.lean`;
- direct Lean dependencies needed to understand a claim.

The product is a ledger, not a rewrite. The workflow monitors drift, tone,
reader efficacy, and over-reach of claim.

## Hard Wall

- Do not inspect, modify, summarize, wake, ping, infer from, or communicate
  with any other Ryot process.
- Own only `books/beastmaster_feedback/**`.
- Read book artifacts and Lean/source artifacts only as needed to verify
  claims.
- Do not edit book prose or Lean/source code.
- Do not run builds, tests, network calls, destructive commands, process
  inspection, prompt timers, or automations unless the operator explicitly
  opens that gate.

## Roles

Kodo is the affirmative case builder. Kodo extracts claims from docs and prose,
then proposes candidate drift rows with exact evidence.

Podo is the adversary. Podo tries to break, narrow, or reclassify every Kodo
row, and also hunts for drifts Kodo missed.

The judge pass resolves disputes. It accepts only rows with enough evidence,
assigns severity, and enforces the fix-boundary rule.

## Fix-Boundary Rule

No one may suggest fixes to:

- `device/Measurement/Episode1.lean`
- `device/Measurement/Episode2.lean`
- `device/Measurement/Episode3.lean`
- `device/Measurement/Episode4.lean`
- `device/Measurement/Episode5.lean`
- `device/Measurement/Episode6.lean`
- `device/Measurement/Episode7.lean`
- `device/Measurement/Episode8.lean`
- `device/Measurement/Episode9.lean`
- `device/Measurement/Episode10.lean`
- `device/Measurement/Episode11.lean`
- `device/Measurement/Episode12.lean`
- `device/Measurement/Episode13.lean`
- `device/Measurement/Episode14.lean`
- `device/Measurement/Episode15.lean`
- `device/Measurement/Episode16.lean`

If drift touches those files, the recommended target must be one of:

- prose or outline documentation;
- downstream proof work outside Episodes 1-16;
- Episode17+ or Meanwhile;
- judge ruling needed.

## Protocol

1. Scope Lock

   Read the source manifest and confirm the corpus. Treat the whole Lean proof
   as unfinished but necessary. Do not demote Episodes or Meanwhiles to notes.

2. Kodo Candidate Case

   Kodo extracts exact text claims and proposes candidate drift rows. Each row
   must include a prose/doc anchor, a Lean anchor, a status, and a rationale.

3. Podo Challenge

   Podo attacks each row. The challenge must ask whether the text really makes
   the claim, whether the Lean anchor is the narrowest correct support, whether
   the status is too strong or too weak, and whether the recommended target
   violates the fix-boundary rule.

4. Judge Resolution

   The judge accepts, narrows, rejects, or escalates each row. Accepted rows go
   into the final drift ledger.

5. Product Check

   The final ledger must be tight enough that the operator can hand it to
   writers or proof workers without extra excavation.

## Status Labels

- `proved`: supported by current Lean declarations/proofs.
- `conditional`: supported only under explicit assumptions, classes, axioms, or
  local hypotheses.
- `measured`: supported by concrete `#eval` or computation, not by a theorem.
- `interface`: names, structures, tokens, or bridges exist, but the claimed
  mathematical/physical conclusion is not proved there.
- `building`: plausible unfinished proof surface, but not integrated enough to
  support the text as written.
- `stale`: documentation describes an older code state.
- `overclaimed`: prose says more than the code establishes.
- `contradicted`: prose conflicts with code comments, honesty gates, or
  declarations.

## Severity

- `S0`: blocking contradiction or major overclaim in a core claim.
- `S1`: high-impact unsupported/stale claim likely to mislead readers.
- `S2`: medium drift, missing qualifier, conditional support, or sequencing
  mismatch.
- `S3`: local tone, wording, or reader-efficacy issue.

## Outputs

Use the templates in this directory:

- `source_manifest.md`: audit corpus and priority order.
- `ledger_template.md`: final row schema and examples.
- `prompts/kodo.md`: Kodo role prompt.
- `prompts/podo.md`: Podo adversarial prompt.
- `prompts/judge.md`: judge pass prompt.
- `prompts/runner.md`: one-shot orchestration prompt for a normal Codex thread.
- `work/`: output area for candidate, challenge, and final ledgers.
