# ep17-loop — the mapping table + the capstone (Phase M deliverable)

The double-read at macro scale: the **Meanwhile loop NAMES backward** (M17→M24), the
**Episodes PROVE forward** (Ep17→52), and the two bands meet at the electron — the loop
names it (M24, box 1 = second variation), the episodes prove it (Ep31, Ep52), and D2
bridges the two electron representations.

Legend: ■ = confirmed off the real theorems · □→split/flag = the sketch row did not hold
as stated; the honest form is given.

## The theorem ↔ step table

| Episode (proves forward) | Loop step (names backward) | Verdict |
|---|---|---|
| Ep17 Stationary Reader (`stationaryAt`/`admits`/`flatAt`) | δ¹ vanishes — M24 `delta1_vanished` box 0; naming step 3 | ■ (Phase-2 wiring: `admits_reads_value_box`, `reader_tower_closes`) |
| Ep18 Fréchet approximation | `transmute` gateaux→frechet — M17 UNIVERSAL_LOCAL_backward; M24 `boxOf` | ■ |
| Ep19 Euler–Lagrange residue closure | the residue seam — M18 | ■ |
| **Ep27–33** approximation/energy tower (Weierstrass residual, energySq, nullspace, **Ep31 second variation = single invariant**, proof-middle) | ~~class trace (M19)~~ | **□→FLAG.** Not a class-trace descent; it is a **Weierstrass-approximation + energy-squared + second-variation** tower. Ep31 IS the naming meeting point (second variation = the coupled-cubic remainder, the Galerkin Hessian invariant). Honest row: **Ep27–33 ↔ the finite/Galerkin realization + the second-variation naming**, not M19. |
| **Ep34–40** operator (Ep37 `threeRungCompiled`, coercivity), universe kernel (Ep39 `UniverseKernel`/`QPhase`/`invariant_zero_detects`), grounding (Ep40 `rung3Inferred`) | ~~class trace (M19)~~ | **□→FLAG.** These are **operator + universe-kernel + grounding** theorems, not class-trace steps. Honest row: **Ep39 UniverseKernel (the tensor/0th term, fixed-point energy) ↔ M24 `fixed_point_pins_zeroth`** (the capstone's GR side); **Ep40 grounding ↔ M19 class trace** (the realizability descent) — the M19 tie is Ep40, not the whole Ep27–40 block. |
| Ep41 apparatus / `fungeBit` | the slip test — M20 | ■ (+ Phase-0 split: the funge/crank primitives factored to `Funge.lean`) |
| **Ep42–46** records (witness/certificate pairs), the integrator (gauge-EL residue reading) | ~~number in [charge,curvature], three trips, mass at f₂ (M21)~~ | **□→FLAG.** Records are **apparatus-realizability** (physical vs metaphysical, the anchor boundary), a different step from the bracketed number. Honest row: **Ep42–46 ↔ M20/apparatus realizability** (the slip test's realizability half), not M21. |
| **Ep47–51** pigeonhole (`finite_entries_miss_a_slip`, `iterOne_injective`), three holes (`tag_lt_three` = Fin 3), mass at f₂ | number in [charge,curvature], **three trips**, mass at f₂ (M21) | **■ CONFIRMED.** The finite pigeonhole → the three tag-holes (three trips) → mass at the second-derivative node. Lands M21. |
| Ep52 pair production (−1) + Ep53–55 QED gauge (phase) | the four faces charge/mass/phase — M22 | ■ |
| Ep31 "second variation = single invariant" + Ep52 electron | **the naming — M24** (the meeting point) | ■ (built + **D2-bridged**: `ElectronBridge.two_electrons_are_one_particle`) |
| ★ **CAPSTONE** (post-Ep52) | M24 fixed point + gateaux→frechet | ★ **BUILT** — `Capstone.the_capstone` |

## The capstone (M3) — `device/Measurement/Capstone.lean`

`universal = universe_tensor (⊨ GR)  ⊕  Fréchet (⊨ Heisenberg)`

The operator's `CalculusProcess.derivative` (`BigRedDogProcess`) carries exactly two
fields — `universal_observer : UniverseTensor` (the 0th term) and `differential_equation
: Variation` (the 1st term). The capstone names them as the operator's decomposition and
lands them in the naming's finite representation:

- **0th term** — `capstone_zeroth_is_tensor : boxOfTensor .universe = valueBox` (box 0).
  Reading: the tensor ⊨ GR (Einstein, U(x*) = x*).
- **1st term** — `capstone_first_is_frechet : boxOf electronVariation = electronBox`
  (box 1; `electronVariation` = the stack's promotion of `differential_equation` to its
  second variation, Ep52). Reading: the Fréchet ⊨ Heisenberg (the produced electron, −1).
- **the decomposition** — `the_capstone : … ∧ valueBox ≠ electronBox` — two DISTINCT
  terms; `capstone_two_terms_exhaust_the_count` — they exhaust the finite count.

Built as the **cheapest-decision-labeled move**: ask the cheapest decision (`rfl`/`decide`
— the finite representation's own verdict, the same shape as the compiler's `lake_build
:= the_compiler.converged = d.fact`), and inscribe the verdict as the operator's label.

**Grade:** the decomposition is DERIVED (`[propext, Quot.sound]`, no Classical); the two
⊨ readings are INTERPRETIVE on code-carriers — never a proved unification.

## The cycle closes (M4)

Ep93 "You the Reader" (`AtreyuProcess`) asks `did_this_distinguish? := d.different?
d.symbol` — `DISTINGUISHABLE.different?`, the very class (Ep1) the loop began from and the
one the naming (M24 / NamingClose) boxes. The cycle closes at the DISTINGUISHABLE. (The
tie is definitional; `AtreyuProcess` is the assembled 34-instance tower — heavy by
construction — so it is documented, not re-proved.)
