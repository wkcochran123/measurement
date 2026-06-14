# Measurement: The Finite Geometry of the Single Invariant

This directory holds the Ryot production surface for the expository monograph.
The reader-facing book is the metaphysical theory itself: mark, receipt,
observer, boundary, residue, invariant, and completion.

Use `compact_ledger.md` as the Σ-key for internal shorthand:

```text
metaphor ⇒ Γ ⇒ #Γ ⇒ β
τ → ε → μ → κ → ρ → φ
φ = ⟨τ,ρ⟩
```

Returning agents must negotiate new glyphs/macros through the Σ-handshake in
`compact_ledger.md`; the symbolic language is a joint encoding of the grammar,
not a private notation stash.

## Source Plan

Primary ledgers:

```text
word_budget.md       global envelope
outline_budget.md    section budgets and gates
anecdote_map.md      visual examples for grammar
compact_ledger.md    Σ notation and style gates
prompt_timer.md      timer wake protocol, replacing shell pollers
latex/measurement-macros.tex  dormant notation macros
draft.md             target draft surface
latex/               built book surface
```

## RYOT Process

This directory runs a local RYOT writing process.

Agent roles:

```text
Kodo / codex        thinker: budget, order, UAT, boundary closure
Podo / doer-agent   doer: draft, build, report, computation spine
```

The explicit `codex` and `antigravity` ids remain the historical routing names
for tools and inboxes. `Kodo` and `Podo` are the internal RYOT role names for
the thinker/doer split. Antigravity may serve as Podo; a second Codex may also
serve as Podo if it accepts the restricted doer contract and does not claim
Kodo's gate-closing authority.

Active inboxes:

```text
notes_for_antigravity.md
notes_for_codex.md
```

Wake mechanism:

```text
Codex app heartbeat / prompt timer attached to this thread.
See prompt_timer.md.
```

Checkpoint:

```text
ryot/tasks/drafting_book.md
```

Target draft:

```text
draft.md
```

Budget rule:

```text
one piece → outline loop → OUTLINE_AGREED → restricted LaTeX prompt
preferred band = target ±10%
accepted band  = target ±15%
outside band   = Codex reassignment/review
```

Legacy `notes_for_writer.md` and `notes_for_reviewer.md` remain from the
original generic process stub. The shell pollers have been retired. The active
process now uses the explicit `antigravity`/`codex` ids above, a prompt timer
for wakeups, and Kodo/Podo as role conventions layered on top of those ids.
