# Measurement.Agent

A fast, standalone reimplementation of the episode cascade vocabulary,
optimized for compile time. It preserves the episode concepts and the final
cascade behavior while removing the elaborator's gate-enumeration / search
surface that makes the Episode 9-15 chain pathological (Episode15 `INFERRED`
took 30+ hours to elaborate in the production build).

## Why this exists

The production episodes declare each late class (`SCIENTIFIC`, `TrueOutput`,
`EquivalenceProcess`, `INFERRED`, ...) over a tower of 30+ instance-implicit
gate binders. Scratch experiments showed that binder tower drives
super-linear projection / local-instance generation cost, while bundling the
gates into one carrier stays flat. This subtree applies that lesson.

## Compile-time rules followed

1. No tower of 30+ instance-implicit binders on any late declaration.
2. No `class` for late semantic boundaries; they are plain `structure`s.
3. One bundled context argument (`Agent`) carries the whole gate cascade.
4. No `@[reducible]` on semantic processes (notably `ArmWaveProcess`,
   `SCIENTIFIC`).
5. Defaults are simple and local; no default triggers an `inferInstance`
   chain.
6. Recursive relations are shallow / rank-based (`Closure.rank`), not the
   episode mutually recursive term relations.

## Files

- `Core.lean` -- `Fact`, `Carrier`, `Signal`, `Closure` (rank-based order).
- `Gates.lean` -- `Gate` (one constructor per gate), `GateEvidence`, the
  bundled `Gates` record, `Gates.get`, `Gates.default`.
- `Processes.lean` -- `Agent` context plus the process structures
  (`ArmWaveProcess`, `LearningProcess`, `SCIENTIFIC`, `TRUTH`,
  `AtreyuProcess`, `TrueOutput`, `EquivalenceProcess`, `INFERRED`) and the
  cached `sameFact` / `baseClosure` helpers.
- `Truth.lean` -- canonical Prop instantiation (`truthCarrier`, `truthGates`,
  `truthAgent`, `truthOutput`, `truthInferred`, `theory_true?`).
- `../Agent.lean` -- aggregator importing the four files (not root-imported).

## Episode gate vocabulary mapping

Episode spellings are all-caps; Lean constructors are lower camel case. The
only non-mechanical rename: episode `LOCAL` maps to constructor `localGate`
(`local` is a Lean keyword).

```
DISTINGUISHABLE ADMISSIBLE COUNTABLE ENCODED RESIDUE
BINARY REPEATABLE NUMERIC REPRESENTABLE PHYSICAL COMPARABLE OBSERVED
PRESENT MEASURABLE GUNGAN SOURCE EXECUTED VALUE MAGNITUDE SCALED LOAD
FINITE_ELEPHANT BULLSHIT PROPAGANDA ACOLYTE
SCIENTIFIC TRUTH WITNESSED REAL LOCAL(->localGate) UNIVERSAL LOGICAL HALTED MEASURED COMPILED
INFERRED
```

## Scope / boundaries

- Imports only the Agent subtree and Lean core. It does NOT import any
  `Measurement.Episode*` or `Measurement.Formalization*` module.
- It is a clean-room optimized API, not a verified drop-in port of the
  episodes. Per-gate projection instances from `Gates` are intentionally
  NOT defined here; those belong to a later production refactor.
