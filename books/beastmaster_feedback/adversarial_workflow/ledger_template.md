# Drift Ledger Template

Use one row per claim. Keep rows narrow. If a prose paragraph makes three
claims, split it into three rows.

| ID | Severity | Text Anchor | Exact Claim | Lean Anchor | Status | Drift Type | Recommended Target | Rationale | Podo Challenge | Judge Ruling |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| D-001 | S1 | `path:line` | Exact words or tight paraphrase | `path:line` | stale | stale documentation | docs | Current code state no longer matches the document's description. | pending | pending |

## Required Fields

- `ID`: stable identifier like `D-001`.
- `Severity`: `S0`, `S1`, `S2`, or `S3`.
- `Text Anchor`: file and line for the prose/doc claim.
- `Exact Claim`: quote only the minimum needed words, or use a tight
  paraphrase if the claim is distributed.
- `Lean Anchor`: file and line for strongest current code support or conflict.
- `Status`: `proved`, `conditional`, `measured`, `interface`, `building`,
  `stale`, `overclaimed`, or `contradicted`.
- `Drift Type`: stale code state, claim expansion, honesty-gate conflict,
  import-closure mismatch, axiom-accounting mismatch, sequencing mismatch,
  tone/efficacy, or other.
- `Recommended Target`: docs, prose, Episode17+, Meanwhile, other, or judge.
- `Rationale`: one sentence.
- `Podo Challenge`: unresolved objection or "none".
- `Judge Ruling`: accept, narrow, reject, or escalate.

## Acceptance Criteria

- Every accepted row has both a text/doc anchor and a Lean anchor.
- Every accepted row states what kind of support the code currently gives.
- No accepted row suggests edits to Episodes 1-16.
- No finding relies on another Ryot process or process state.
- Rows distinguish "code has a name/interface" from "code proves the prose
  conclusion."
- Rows distinguish "proof surface is building" from "prose is false."
