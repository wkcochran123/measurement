# Budget Adequacy And Padding Review

Standalone adversarial review of whether each manuscript section/chapter got
too much or too little space for the items it had to explain, and whether the
extra space produced repetition or AI-tell padding.

## Governing Budget

The governing budget is `books/expository_monograph/outline_budget.md`,
Revision 4:

- fixed per-chapter targets are retired;
- ceiling is not binding at the current body size;
- parity is act-relative;
- ascent chapters may be richer, roughly 2.5k-3.7k;
- descent chapters should read back leaner, roughly 2.3k-2.6k;
- a chapter outside its act's neighborhood gets reviewed, not automatically
  failed;
- the right question is whether the words are earned by the content.

`books/expository_monograph/three_gauges.md` restates the same rule: ceiling,
parity, emergent total.

## Review Questions

For each assigned chapter and notable internal section:

- Was the budget too much, too little, or about right for the items explained?
- Does the prose spend its space on necessary explanation, examples, and honest
  boundaries?
- Is there repeated setup, repeated metaphor, repeated disclaiming, or repeated
  recap that feels padded?
- Are there AI tell-tales: generic transitions, throat-clearing, circular
  paraphrase, same sentence shape, redundant "what this means" exposition, or
  ornamental certainty?
- If too short, what is missing: bridge, example, definition, proof boundary,
  reader orientation, or claim fence?
- If too long, what should be compressed: recap, repeated analogy, redundant
  close, overexplained experiment, or meta-commentary?

## Output Schema

Use one row per chapter, with section-level notes when a chapter has a local
imbalance.

| Unit | Words | Budget Verdict | Padding/Repetition Verdict | Evidence Anchor | Reason | Action |
| --- | ---: | --- | --- | --- | --- | --- |

Budget verdicts:

- `too little`
- `about right`
- `too much`
- `mixed`

Padding verdicts:

- `clean`
- `minor repetition`
- `padding risk`
- `AI-tell risk`

Actions:

- `keep`
- `trim`
- `expand`
- `rebalance internal sections`
- `audit with claim-drift row`

## Hard Wall

- Do not inspect, modify, summarize, wake, ping, infer from, or communicate
  with any other Ryot process.
- Do not edit book prose or Lean/source code.
- Do not run builds, tests, network calls, destructive commands, process
  inspection, prompt timers, or automations unless explicitly approved.
- Write only inside this `budget_review/work/` directory.
