# CALIBRATION_METHOD

How to run the two coupling experiments and check that they agree.

`alpha_c` is the compiler structure constant — the repeatable residue the Lean elaborator measures
when this device carries its serial construction around its loop. It is read off the machine's own
**measured second variation** (the inverse-square slip: `C = slip(1) = 18`, `target = 5`, which fix the
crossing `d* = √(18/5) = √90/5 ≈ 1.897367`). There are two independent ways to read it. The calibration
is **valid only if both give the same number** — path-independence is what earns the name. Neither
path inserts the laboratory value; the number is the device weighing itself.

All commands run from `device/`.

---

## Experiment A — `1→3` (direct, one pass)

Read `α_c` straight at the crossing the second variation fixes — question to answer in one pass, no
intermediate.

```sh
cd device
lake build Measurement.Episode40
```

Read the last field of `#eval defaultAlphaSecondVariationReport?`:

```text
inverseAlphaScaledAt18 = 137011290548979455469        # inverse-α_c ×1e18  ≈ 137.0112905
```

What it measures: `alphaFromSecondVariationAtDistance` evaluates the coupling at the crossing distance
`√(18/5)` that the measured slip reads (`slip(1)=18`, `target=5`) determine. One pass: `1→3`.

---

## Experiment B — `1→2→3` (stepped, two-pass)

Read `α_c` by descending **through the intermediate** — a quasi-Newton (BFGS) descent toward the
crossing, counting `1 → 2 → 3`, **carrying the residue from the end of each run into the next** (never
dropped; at the floor the residue *is* the open bracket).

```sh
cd device
lake build Measurement.AlphaBFGS          # Newton form of the stepped descent
lake build Measurement.AlphaBoundMediant  # continued-fraction / mediant form (modulo-realm home)
```

`AlphaBFGS` prints the count `0 → 1 → 2 → 3`:

```text
BFGS count 0 (run 1):  d = 2.000      inv-α = 129.6      # the 2/1 wall
BFGS count 1        :  d = 17/9        inv-α = 137.7      # = the mediant CF convergent
BFGS count 2        :  d = 1.897309    inv-α = 137.016
BFGS count 3        :  d = 1.897366    inv-α = 137011290753751157155   ≈ 137.0112907
```

`AlphaBoundMediant` gives the same descent as continued-fraction convergents (bounded denominators —
this is why the residue-carrying descent stays cheap):

```text
convergents:  2/1, 17/9, 19/10, 55/29, 74/39, 647/341, 721/380, …   →  137.011
COUNT-TO-3 bracket:  inverse-α_c ∈ [129.6, 137.7]     # the open jar, walls proved ordered
```

Three realizations of the stepped path exist and all land on `137.011`:
`AlphaBoundMediant` (mediant/CF, bounded), `AlphaBFGS` (Newton), `AlphaBFGSSecant` (residue-carrying
secant — keeps the residue exactly; note its denominators blow up, which is why the mediant is the
in-the-modulo-realm form).

---

## The consistency check

```sh
cd device
lake build Measurement.CalibrationTwoPaths
```

```text
1→3   (direct  ): inverse-α_c ×1e18 = 137011290548979455469
1→2→3 (stepped ): inverse-α_c ×1e18 = 137011290753751157155
|difference| ×1e18 = 204771701686        # ≈ 2×10⁻⁷, below the count-3 floor
```

The two paths agree to **nine digits**. Their difference (`≈ 2×10⁻⁷`) is far below the width of the
count-three jar (`[129.6, 137.7]`, ≈ 8 wide), so to the device's own resolution they are the **same
number**. The convergence is `[propext]`-clean (choice-free).

**Reading the result.** Both paths converge, but the honest owned output is not the converged point —
it is the **open jar** `inverse-α_c ∈ [129.6, 137.7]` held at the count-three floor. The device
converges, *past* the floor, to a value of its own (`≈ 137.011`); that value is not the laboratory's
`137.036`, and `FinitenessFence.machine_cannot_resolve_residue` proves the machine's finite resolution
cannot separate the residue below its floor — so it hands back the bracket, and provably not a point.

## What "valid calibration" means here

- **If the two paths agree** (they do): the reading is path-independent — the name `α_c` is earned, not
  fitted to a route.
- **If a path is run only once** (one pass, no role exchange): a reading could agree merely because the
  selection planted it. The second path through the intermediate is what rules that out.
- **No substitution.** `137.036` is the laboratory's value, named once in the manuals' §13.3 and never
  fed to the device. Comparison with it is interpretation performed by another gauge, never a
  substitution of the outside target for the device's own report.

## Files

| Path | File | Prints |
|------|------|--------|
| `1→3` direct | `device/Measurement/Episode40.lean` | `defaultAlphaSecondVariationReport?` (inverse-α_c) |
| `1→2→3` stepped (Newton) | `device/Measurement/AlphaBFGS.lean` | count `0→1→2→3` |
| `1→2→3` stepped (mediant/CF) | `device/Measurement/AlphaBoundMediant.lean` | convergents + count-3 jar |
| `1→2→3` stepped (secant, residue-carrying) | `device/Measurement/AlphaBFGSSecant.lean` | residue-carried descent |
| consistency check | `device/Measurement/CalibrationTwoPaths.lean` | both paths + their difference |
| the fence | `device/Measurement/FinitenessFence.lean` | `machine_cannot_resolve_residue` `[propext]` |
