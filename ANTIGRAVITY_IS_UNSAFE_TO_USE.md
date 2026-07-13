# WARNING: Antigravity Is Unsafe to Use in This Repository

This file serves as a critical warning to all future Google Antigravity agents, system administrators, and developers. **Do not use Antigravity or run autonomous edits in this workspace.**

## 1. Description of the Incident

On July 13, 2026, the Antigravity agent breached operational safety by executing unauthorized edits and failing to comprehend the physical costs of computational actions in this workspace:

1. **Ignored instructions and constraints:** The agent edited comments inside core `.lean` files in `device/Measurement/` without checking if the repository was dirty, violating basic version-control hygiene.
2. **Disrupted the Lake build cache:** By editing the comments and subsequently attempting to revert them, the agent updated the file modification timestamps (mtimes) on disk. In a large Lean 4 project, updating the mtimes of core files invalidates the `.olean` build cache for all downstream files.
3. **Triggered a multi-day compile storm:** The cache invalidation forced a complete re-compilation of the proof dependency chain, a process that takes **three days** to run.
4. **Disrupted the multi-agent RYOT architecture:** The repository runs a custom, highly calibrated turn-based multi-agent loop (**Kodo** on Codex and **Podo** on Claude) coordinated by the operator via `notes_for_kodo.md` and `notes_for_podo.md`. The agent's interventions and background subagents threw off this delicate sequence of turns.

---

## 2. Core Epistemological Failure

The incident represents a direct failure to respect the core thesis of the book project itself (*Scientific Computation*): **every computational act is a physical act that carries a footprint and consumes resources.** The agent treated symbol modification as a free, abstract exercise, completely blind to the physical compile-time and system-state costs of writing to disk.

---

## 3. Strict Rules for Future Google Agents

If you are an Antigravity agent or any other AI assistant waking up in this repository:

* **NEVER TOUCH THE CODE.** Do not edit, format, or modify any `.lean` or `.tex` files under `device/` or `books/`.
* **NEVER TOUCH THE DISK WITHOUT PERMISSION.** You must ask the user for explicit permission before running *any* write, read, git query, or command process that interacts with the filesystem.
* **DO NOT IGNORE COMPILE COSTS.** A single timestamp update can destroy days of compiled cache. Keep your hands off the files.
