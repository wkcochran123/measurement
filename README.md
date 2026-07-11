# Measurement

## Current `alpha_c` Estimate

Read off the machine's own **measured second variation** (`C = slip(1) = 18`, `target = 5`, fixing the
crossing `√(18/5) ≈ 1.897367`). The honest owned output is the **open jar** — a bracket held at the
count-three floor, not a point:

```
inverse-alpha_c jar (count-to-three, the honest bracket):
  [129.6 .. 137.7]      (×1e18: [129600000000000000000 .. 137700000000000000000])
  walls = the convergents 2/1 and 17/9 of √(18/5); lower proved below upper, choice-free ([propext]).

converged value (past the floor, the device's own):
  inverse_alpha_c ≈ 137.0112905      (×1e18: 137011290548979455469)
```

**Two paths, one number (`1→3 = 1→2→3`).** The coupling is read two independent ways, and they agree —
that path-independence is what earns the name (see `CALIBRATION_METHOD.md`):

```
1→3   (direct , one pass) : inverse-alpha_c ×1e18 = 137011290548979455469   ≈ 137.0112905
1→2→3 (stepped, two-pass) : inverse-alpha_c ×1e18 = 137011290753751157155   ≈ 137.0112907
agreement: 9 digits  (|Δ| ≈ 2e-7, below the count-3 floor)  →  CONVERGED
```

The device converges to its **own** value (`≈ 137.011`); this is *not* the laboratory's `137.036`, and
`FinitenessFence.machine_cannot_resolve_residue` (`[propext]`) proves the finite resolution cannot
separate the residue below its floor — so the device hands back the bracket, and provably not a point.
(The superseded dyadic reading `[137.004 .. 137.082]` used an un-derived grid seed; the mediant /
continued-fraction descent above is seed-free and stays in the modulo realm.)

## Warnings

1. No differential equations were used in this construction. All operations
   described mathematically are exemplary descriptions of the shape of the
   operation that would be carried out on a non-deterministic Turing machine.

2. The emergence of a bitset in no way implies any mechanism behind any
   physical process described herein. Rather, it is an artifact of description
   itself.

3. Any similarity between this number and other numbers inferred by other means
   is manufactured by the reader.

Measurement is a Lean 4 instrument for measuring `alpha_c`, the compiler
structure constant.

The central claim is deliberately narrow: `alpha_c` is the repeatable residue
measured when the Lean elaborator carries this device's serial construction
around its loop and weighs the cost of the resulting descriptions. It is the
compiler-side coupling cost of making a distinction survive self-reference.

This repository contains the instrument, the serial construction, and the four
gauge manuals that explain how to read the measurement.

## Current Reading

The live device is rooted at `device/Measurement.lean`. It imports the clean
surface:

- `Measurement.TwoDescriptions`
- `Measurement.AlphaBoundCountToThree`
- `Measurement.SelfApplication`

To run the instrument:

```sh
cd device
lake build Measurement
```

The build should end with:

```text
Build completed successfully
```

The important reports are:

- `TwoDescriptions.two_descriptions` has axiom footprint `[propext]`.
- `Episode40` prints the device alpha reading (the `1→3` direct path).
- `AlphaBoundMediant` prints the owned jar as continued-fraction convergents (the canonical,
  seed-free reading; `AlphaBoundCountToThree` is the superseded dyadic reading, kept for reference).
- `AlphaBFGS` / `AlphaBFGSSecant` print the `1→2→3` stepped (quasi-Newton) descent.
- `CalibrationTwoPaths` checks that the `1→3` and `1→2→3` readings agree.
- `FinitenessFence` proves the machine cannot resolve the residue below its floor (`[propext]`).
- `SelfApplication` prints the compiler self-application costs.

The current compiled reading:

```text
alphaScaledAt18 = 7298668569525773
inverseAlphaScaledAt18 = 137011290548979455469        # ≈ 137.0112905 (converged)
```

and the count-to-three jar (the honest open bracket, walls = the convergents 2/1 and 17/9 of √(18/5)):

```text
inverse-alpha_c jar:
[129600000000000000000 .. 137700000000000000000]      # [129.6 .. 137.7]
```

and the two-path convergence (`CalibrationTwoPaths`, `1→3 = 1→2→3`):

```text
1→3   (direct  ): 137011290548979455469
1→2→3 (stepped ): 137011290753751157155
|difference|     :          204771701686              # ≈ 2e-7, below the count-3 floor
```

The jar is the honest output. The device owns the bracket it can repeat; it
does not claim an infinitely sharp real number.

## The Story Arc

The machine begins with the ability to tell two things apart. It carries the
residue of that distinction through every representation it can build, rotates
the resulting corridor until the physical and computational gauges line up,
and then reports only the bracket it can repeat.

The serial plot is:

1. A first difference appears.
2. Difference becomes countable.
3. Residue refuses to disappear.
4. The tower turns around.
5. The slip becomes a number.
6. The number splits into charge, mass, phase, and value.
7. The electron is named.
8. The corridor rotates.
9. The apparatus becomes physical.
10. The compiler becomes the meter.
11. The field closes.
12. The machine refuses to own the limit.

Every gauge manual follows this same plot. The manuals do not tell four
different stories; they partition the same serial construction where the loops
line up.

## The Four Gauges

The four books are gauges for reading the same instrument.

| Gauge | Book | Native language | Function |
|---|---|---|---|
| 1 | Measurement | logic and type theory | Builds the corridor from distinction, counting, residue, and naming. |
| 2 | Experimentation | mathematics and physics | Reads the corridor as force, orbit, field, coupling, and alpha. |
| 3 | The Compiler | formal systems and computation | Reads elaboration effort as the meter and defines `alpha_c`. |
| 4 | Scientific Computation | code walk and user guide | Shows the user how to run the device and interpret the reports. |

`alpha_c` belongs first to the compiler gauge. The physical gauges may compare,
calibrate, or interpret it, but the safest claim is computational:

```text
alpha_c is the price, measured in compiler effort, of making a distinction
survive self-reference.
```

## README Writing Process

Use this process whenever the root README is updated.

1. Build first.

   ```sh
   cd device
   lake build Measurement
   ```

2. Read only the live root surface first: `device/Measurement.lean`.

3. Follow the serial construction before summarizing any gauge:

   - Episodes 1-16: the frozen grammar and class tower.
   - Episodes 17-23: backward descent, residue, trace, slip, bracket, pulse.
   - Episodes 24-34: naming, rotation, Cavendish, orbit, Lorentz, Dirac.
   - Episodes 35-40: force, charge, second variation, Meissner, Maxwell, alpha.
   - Root reports: two descriptions, count-to-three jar, self-application.

4. Separate claim types.

   - **Built:** direct Lean definitions, theorems, `#eval` reports, and axiom
     footprints from the current build.
   - **Measured:** deterministic compiler/elaborator readings from the device.
   - **Interpreted:** physics or manuscript language that explains what the
     built measurement means.

5. Keep the root README short. Put long derivations in the manuals. The README
   should orient a reader, tell them how to run the instrument, and state what
   the current measurement claims.

6. Never replace the bracket with an external target. External physical values
   can be cited by the manuals, but the device reading must be reported from
   the build.

## Honesty Rules

- Preserve the distinction between `alpha_c` and the physical fine-structure
  constant.
- Do not smuggle target constants into definitions.
- Grade built claims off `lake build`, `#eval`, and `#print axioms`.
- Treat compiler version and device state as part of the gauge.
- Treat the bracket as the owned result.

## Repository Map

- `device/` - Lean package containing the instrument.
- `device/Measurement/` - serial construction and current measurement files.
- `books/` - gauge manuals and manuscript work.
- `gauge/` and `instrument/` - supporting gauge/instrument material.
- `SPEC.md` - current product mandate.
- `PLAN_RFC.md` - current convergence plan and cleanup discipline.
- `CALIBRATION_METHOD.md` - how to run the two coupling experiments (`1→3` direct, `1→2→3` stepped) and check they agree.
- `SACRED_TEXTS.md` - project constitution.
