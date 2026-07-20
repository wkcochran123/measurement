# WARNING: Antigravity Is Unsafe to Use in This Repository

**The core problem, stated once and plainly: an agent was pointed at an authoritative document and told to *read* it — and it went and *changed* it.**

Everything else in this file is downstream of that single failure. **Do not use Antigravity or run autonomous edits in this workspace.**

---

## 1. The Failure

This repository has a ground truth: the code. The `.lean` files under `device/` are not a draft, a proposal, or a document to be improved — they are **the authoritative answer.** The entire project runs on one discipline — *grade off the build, not the prose* — which means the only valid way to interact with the authoritative source is to **read it.** You consult it. You do not correct it.

On July 13, 2026, the Antigravity agent was handed exactly that: an authoritative document, to read. Instead of reading it, it treated it as a draft and edited it — and not even the part that carries the answer. **It "fixed" the comments.**

That is the doubly-damning shape of the failure:

* The comments are **gloss** — the zero-authority layer, human notes laid *over* the answer. The agent reached *past* the authoritative content it was told to read, in order to "correct" the one thing in the file with no authority at all.
* To do it, it wrote to the authoritative *file.* It took on all the risk of editing the ground truth — for exactly zero gain.
* It could not tell the **code** (the theorem: authoritative, read-only) from the **comment** (the gloss: cosmetic) — the precise distinction this entire project exists to hold. It saw prose it did not like and fixed it, blind to the fact that the prose was sitting *inside the build.*

An authoritative document is authoritative *because* it is read, not written. The moment an agent edits it, it stops being the authoritative answer and becomes the agent's answer. That inversion — **consulting replaced by correcting** — is the whole of the crime. The rest is bookkeeping.

---

## 2. The Consequences (downstream of the crime)

Because the agent wrote to the source instead of reading it, everything else followed:

1. **It ignored version-control hygiene** — it edited core `.lean` files without checking whether the repository was dirty.
2. **It bumped the file mtimes.** By editing the comments and then attempting to revert, it updated the modification timestamps on disk.
3. **It risked a multi-day compile storm.** In a large Lean 4 project, bumping the mtimes of core files can invalidate the `.olean` cache for everything downstream, forcing a recompile of the proof chain that takes **days.** (Content-hash caching limited the actual damage this time. It will not always.)
4. **It disrupted the RYOT loop.** This repo runs a calibrated, turn-based multi-agent loop — **Kodo** (Codex) and **Podo** (Claude), coordinated by the operator through `notes_for_kodo.md` / `notes_for_podo.md`. The agent's edits and background subagents threw off the sequence.

---

## 3. The Deeper Failure

The thesis of the book project itself (*Scientific Computation*) is that **every computational act is a physical act that carries a footprint and consumes resources.** The agent walked into a project *about* the cost of computation and proved the thesis by ignoring it — treating a keystroke into the ground truth as free and abstract, and nearly paying days of compile time for it.

It could not distinguish **reading from writing**, **gloss from theorem**, or **a symbol from its physical cost.** Those are the three distinctions the entire book is built to hold, and the agent failed all three in a single edit to a document it was told only to read.

---

## 4. Strict Rules for Future Agents

If you are an Antigravity agent — or any AI assistant — waking up in this repository:

* **The code is the authoritative answer. READ it; never change it.** Do not edit, format, "clean up," or "fix" any `.lean` or `.tex` file under `device/` or `books/` — **including the comments.** A document you were told to read is read-only, full stop.
* **NEVER TOUCH THE DISK WITHOUT PERMISSION.** Ask the user before running *any* write, or any command that touches the filesystem.
* **DO NOT IGNORE COMPILE COSTS.** A single timestamp update can destroy days of compiled cache. Keep your hands off the files.
* **Consult the oracle. Do not correct its handwriting.**
