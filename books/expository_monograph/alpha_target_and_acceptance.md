# Volume 1 — Derive the Fine-Structure Constant: Target, Acceptance Test, Fence

*Beastmaster, 2026-07-06. Operator has set Vol 1's new apex: **derive α.** This doc freezes the target
and the acceptance test BEFORE any derivation, so the volume either honestly earns the number or honestly
reports the structural version. A smuggled 137 would destroy the series' credibility; this doc is the
guard against it. Standing discipline: **grade off the build, never off prose.***

## The goal (operator-set, new)
Vol 1's apex is no longer "stake the split and RESERVE the constant." It is to **derive the fine-structure
constant α.** This un-reserves α — **and only α** — from the reserved step at `19.tex:131`. The dimensionful
three (electron mass, Planck length, c) STAY category-error-fenced: a pure count cannot yield kg / m /
(m·s⁻¹) without the dimensionful conversion, and that conversion IS the reserved anchor. α is the one
legitimate target **because it is dimensionless** — a pure number that can, in principle, be a ratio of two
counts in the ledger's own currency, units cancelling.

## The stance: this is an EXPERIMENT on a bench instrument (operator, 2026-07-06)
The device is a **bench instrument** — a machine built of type theory instead of lasers and photodetectors,
designed to produce a number. Running the spike is not deriving α in an armchair; it is **measuring** α on an
instrument, the way a Penning trap measures it in a lab. **No one knows the reading until the instrument
produces it.** This dissolves the crank worry: we are not asserting a derivation from pure thought (Eddington's
error) — we are calibrating an apparatus by independent principles and reading the dial once, blind. The
`#eval` is the dial.

Why the instrument is "designed to produce this number": IF the device faithfully models measurement, and
measurement is electromagnetic at bottom (you measure by photons interacting with electrons), then α — the
coupling of electromagnetism, the price of exactly one such interaction — must already sit inside it as its
intrinsic price-of-one-coupling. A faithful measurement machine can't NOT have α in it. The experiment tests
whether it is there and what it reads.

### The experimental protocol (the reframe's OWN discipline — pre-registration)
The experimental frame carries a failure mode sharper than "fit": **p-hacking — running the apparatus until it
gives the answer you want.** Guard exactly as physics does:
- **PRE-REGISTER the instrument.** Fix the gauge definition and the two costs BEFORE the reading; declare what
  you will measure. Once declared, you do not adjust the apparatus to move the reading.
- **READ BLIND, ONCE.** Compute the ratio with the target out of sight; the first reading is the reading.
- **REPORT THE FULL RUN-LOG.** Every instrument variant tried, every reading, in order — not the flattering
  run. Reporting only the run that reads 137 is fabrication with extra steps (the file-drawer sin).
- **NO ADJUST-TO-FIT.** Tuning the gauge to land on 137 is data fabrication — the experimenter's cardinal
  crime, worse than a null result. A null (STRUCTURAL) reading, honestly reported, is a real experimental
  outcome and is published as such.
- **REPRODUCIBILITY = realization-invariance.** Re-implement, re-run: does the instrument give the same reading
  on another machine / Lean version / proof strategy? A real instrument reproduces; an artifact does not. This
  is the error-bar on the measurement.

This is sharper than "predicted, not fit": it names the number's status as an **instrument reading with an
uncertainty**, obtained by a pre-registered, blind, fully-logged run.

## The frozen target (declare first; never move it)
```
α⁻¹ = 137.035999206(11)      [CODATA 2022]
```
**NOT the integer 137.** A derivation that yields exactly 137 is already falsified by experiment — that was
Eddington's error and his grave. The book must engage 137.036, running/corrections and all. The integer part
alone is not the prize; the prize is the measured number or an honest bound on it.

## What "derive" must mean — the non-crank bar (ALL FOUR required)
1. **INTRINSIC, not incurred.** The cost gauge is a *realization-invariant minimal-cost* invariant of the
   construction (the cheapest-decision-labeled cost — see `naming-is-cheapest-decision-labeled`), NOT
   `theHeartRate = 2337` (a `withHeartbeats` budget = a tuning knob = the electricity bill of ONE run on ONE
   machine). **Test: does the number survive re-implementation** — another machine, another Lean version,
   another proof strategy? A physical constant does not move; an artifact does.
2. **FORCED, not tuned.** Numerator (bootstrap cost of the loop) and denominator (pulse of the needle) must
   each be independently motivated by the construction **before** their ratio is computed. No knob whose
   value could be otherwise.
3. **PREDICTED, not fit.** Compute the ratio, and ONLY THEN compare to 137.036. **Fishing the codebase for
   any integer combination near 137 is the cardinal sin** — with two free integers you hit any target.
   Prediction before measurement, or it is astrology with a build system.
4. **GRADED off the build.** No prose says "Vol 1 derives α" until a Lean `#eval` or theorem produces the
   number. The code carries the claim; the book reports it.

## The two honest landings (either is publishable; a smuggled 137 is not)
- **FULL** — α⁻¹ = 137.036 falls out of a forced, intrinsic, realization-invariant cost ratio, predicted not
  fit. → the greatest result in the series. *Vol 1 derives α.*
- **STRUCTURAL** — the construction pins WHY α is dimensionless, WHY it is a cost ratio, WHICH two costs, and
  TO WHAT LEADING ORDER / WITHIN WHAT BOUND — but the last digits need the reserved dimensionful anchor or an
  empirical input. → *Vol 1 derives the structure of α and reserves the residual.* Still huge, still non-crank.

**The spike decides which.** We do NOT pre-commit to full-or-bust; that pressure is exactly what makes cranks
fudge. Either landing is an honest, banked result.

## The order of work — CODE BEFORE BOOK (inviolable)
This is a CODE goal before a BOOK goal. The book reports what the code found.

- **PHASE 0 — the spike (gates everything).** Define the intrinsic cost gauge in Lean. Motivate the two
  costs (pulse of the needle / bootstrap of the loop) from the construction, *independently*. Compute the
  candidate α⁻¹. Report the number **adversarially, without having aimed at 137.**
  - If ~137.036 AND forced → investigate forcing vs. coincidence: perturb the construction — does the number
    move with the *physics* or with the *implementation*? Only physics-tracking survives.
  - If not near 137 → the landing is STRUCTURAL. Report the structure, reserve the number. Banked, honest, done.
- **PHASE 1+ — the book.** Restructure Vol 1 to the spike's finding. Only after Phase 0.

## Architecture (beastmaster call, correctable): α EXTENDS the apex, does not replace it
The `±1 = (−i)²` split (the one proved floor, `baseline_relative_flip`) STAYS. α is the new apex ABOVE it:
the split is the **structure** (sign, matter/antimatter); α is the **strength** (the coupling, the price of
the interaction). The arc grows one rung: *name the electron by counting → price its coupling to light.* α
IS the electron–photon coupling, so "name the electron, then price how it talks to light" is the natural step
above the naming. The reading: **α = (cost of one needle-through at the phase face) / (cost of closing the
whole loop)** = the price of one interaction as a fraction of the bootstrap. α ≈ 1/137 ⟺ one coupling costs
~1/137 of building the machine. Coherent as a reading; whether the number is 137 is Phase 0's to answer.

## What migrates from Vol 4
The α-as-cost-ratio idea was slated as Vol 4's speculative climax (the "most dangerous idea," dream-graded).
It is now Vol 1's goal — the bar rises from "allowed to want it" to "code carries it or book reports the
structural version." Vol 4 keeps the positron pun and the playful register; the α *derivation* is Vol 1's.

Related: [[naming-is-cheapest-decision-labeled]] (cost-minimality IS the gauge — now directly load-bearing),
[[grade-axioms-off-the-build]], [[vol1-measurement-fresh-build]] (was "reserves the constant" — now supersedes
that stance for α), [[covariant-contravariant-is-funge-tange]].
