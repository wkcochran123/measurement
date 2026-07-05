# Source Manifest

## Lean Corpus

Required first-pass code reading:

- `device/Measurement/Episode*.lean`
- `device/Measurement/Meanwhile*.lean`

Read direct dependencies when needed to verify a claim, especially:

- `device/Measurement/Calibration/*.lean`
- `device/Measurement/ComputerProgram.lean`
- `device/Measurement/NamingClose.lean`
- `device/Measurement/Agent/*.lean`

Do not treat an imported dependency as outside the proof surface if a prose
claim depends on it. Do not treat unimported episodes as terminal proof for a
claim unless the prose itself is speaking at the book-arc level rather than a
single terminal file.

## Documentation Corpus

Audit outline and planning docs before chapter prose:

- `books/expository_monograph/outline.md`
- `books/expository_monograph/_conceptual_outline.md`
- `books/expository_monograph/_episodes_digest.md`
- `books/expository_monograph/_episodes_arc.txt`
- `books/expository_monograph/outline_budget.md`
- `books/expository_monograph/meanwhile17_study.md`
- `books/expository_monograph/three_gauges.md`

Then audit manuscript material in:

- `books/expository_monograph/**/*.tex`
- `books/expository_monograph/**/*.md`

Exclude `books/beastmaster_feedback/**` from the evidence corpus except for
workflow state.

## Seed Drifts To Verify

These are leads, not findings:

- Documentation appears to say `Meanwhile17.lean` still contains many `sorry`s;
  current code appears to contain none.
- A conceptual outline appears to use "baryon asymmetry" language; Episodes 82
  and 83 appear to disclaim baryogenesis, CP violation, Sakharov conditions,
  and Standard Model matter/antimatter asymmetry.
- A three-gauge document appears to describe a choice-free or limited-axiom
  story; this must be reconciled with `Episode19.lean` and early uses of
  `propext` and `Quot.sound`.
- Episode 92 appears to import no prior Measurement episode while its comments
  speak as if reading from the arc across Episodes 17-90.
- Episode 93 appears to import only Episode 15 while functioning as a
  reader-facing terminal question file.
- Pair production, boundary/Einstein/Navier-Stokes, reader band/whelm, and
  matter/antimatter claims need exact Lean anchors and status classification.
