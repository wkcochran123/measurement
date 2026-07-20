# PLAN — The Serial Construction: the three-fold united, one theorem, one clean build

*Updated 2026-07-09 to the actual spec (supersedes the "3-D Polar/Lorentz glue" sketch below the fold); §0 added
2026-07-11 to bind the build to the new Vol 1 preface, "The Cost of Free Will." Grade off the build. Sacred
Episodes 1–15 frozen. This is what we drive to.*

---

## STATUS (2026-07-19) — this serial-construction plan is EXECUTED; the live plan is the books
The §1–6 cleanup (fix-the-break, dedup, serialize, converge to `two_descriptions` + the α bound + self-application) has been carried out; the serial construction stands and the box-walk documentation pass over it is do/review-complete. The §3 physics-core (the three-fold −1/0/+1 = C/M/V = quark color; QED-applied-to-itself = the electron's self-energy; blind to the magnitude) remains the correct reading and feeds the books. What follows below is retained as executed-plan provenance.

**THE DEFINITION (locked, operator 2026-07-19).** The three primitives ARE the three Lean forms: **tange = `structure`** (name by characteristics, `n = f s ⟹ nn = f(s s)`, contravariant select); **funge = `class`** (enumerate instances, `nn = f(s) f(s)`, covariant pool); **tensor = `inductive`** (`t = X ∘ f`, introduction + elimination). The **one argument** = declare the triple, the kernel checks, over and over (this IS the consume→produce braid). The keystone is **satisfied by construction** — the primitives are the keywords the code already uses; the whole thing typechecks with a clean footprint, which *is* the checked consistency (relative to the assistant's own soundness — the argument is checked, not the foundations of mathematics). First read: structure=tange / class=funge / inductive=tensor. Second read (Vol 5): structure=funge / class=tange / inductive=tensor (the tensor fixed). Full text, the two Vol-1 prefaces, and the gate live in `books/BOOKS_REARCH_RFC.md`.
## 0. What the preface commits the build to — *"The Cost of Free Will"*
Vol 1's preface (`books/expository_monograph/latex/chapters/00-preface.tex`) makes four promises **in coin the
build must actually print.** The RFC target (§1) is exactly their redemption — grade each off the build, never
the prose:

1. **"Nothing is smuggled."** Every step says which it is — posited / proved / read / reserved. → the marking
   discipline (§4 BLIND, §6 gates): `#print` / `#eval` decides the grade, never a comment.
2. **"Granted almost nothing … one thing: the law of motion."** The machine refuses the free reach into a
   collection (no `Classical.choice`) and grants itself exactly ONE query it cannot settle from inside — the law
   of motion. → §1.1: choice-free footprint; the single grant is the law-of-motion oracle (`eulerLagrangeOracle`),
   a def-level oracle taken in the open, NOT `Classical.choice`.
3. **"The cost … will be demonstrated … its own pulse, counted in the currency it actually runs on."** The machine
   forces ONE truth and reports the exact price of forcing it. → §1.3 + §3a: the two descriptions elaborate to
   equal **heartbeats** up to calibration; the **calibrated residual = the α bound** (§1.2). *"Free will has a
   price; we measure it"* IS `#count_heartbeats` on `two_descriptions` — the self-energy = the machine weighing
   its own reading.
4. **"A construction that ends not with a result it proves but with one it hands over."** The deepest result is a
   split **proved two, proved opposite, and left — provably — without a fixed answer to which side is which**; the
   machine derives the two-fold and DECLINES the selection, handing it to the reader (the one apparatus it cannot
   build). → the STRUCTURAL landing is the DESIGN, not a shortfall: the machine runs to its **count-to-3** floor
   and stops (`AlphaBoundCountToThree`, the open bracket = the jar), never fixing the magnitude/sign. *(Interpretive:
   the declined which-is-which = the −1/+1 charge-conjugation sign = the Weyl/traceless part a counter cannot
   denominate, §3.)*

So the preface is not decoration over the build — it is the build's **contract.** §1's three printed items are the
"coin you can count"; the honest bracket (the jar) is the "handed over, not proved" ending.

## 1. The target — what `lake build` MUST print (nothing more)
1. `#print axioms <the theorem>` == **`[propext]`** — choice-free; propositional extensionality only, nothing else.
   **The one grant the preface names is not an axiom here:** the law of motion (`eulerLagrangeOracle`) is a
   def-level oracle the construction uses, taken in the open — NOT `Classical.choice`. The theorem's footprint
   stays choice-free; the single grant lives in the defs, named plainly (preface, *"granted almost nothing"*).
2. **`a1 < α ≤ a2`** with a **guess for α** (the bound, bracketed, printed).
3. **Elaboration times are the same up to calibration** — the two descriptions cost the SAME to elaborate
   (deterministic heartbeats), up to the calibration constant (the ×1000 `rank ≡ heartbeat` connection). This is
   the **application of QED to itself** (§3a): the elaborator weighing its own elaboration = the electron's
   self-energy; the type-level echo confirmed at the computational level. The **calibrated residual** of the two
   times IS the α bound of (2). Grade off the build (`#count_heartbeats` / the device EKG — deterministic).

## 2. The ONE theorem (the whole construction converges here)
```lean
theorem two_descriptions : electron_in_orbit = anti_cooper_pair := rfl
```
The two descriptions are the **same by `rfl`** — "I have heard it both ways." One electron **in orbit** and the
**anti-Cooper pair** are one rotating object under two names; the equality is definitional (they reduce to the
same term). This is `1 = 0.999…` generalized: the thing has more than one name and the names are the same name.

## 3. The unification — three things to unite, ONE three-fold
The three states `−1 / 0 / +1` (electron / null / positron) are one three-fold read in four coordinate systems —
they are all the same object:

| −1 | 0 | +1 |
|---|---|---|
| **C** | **M** | **V** | ← the rotation's generators ("it rotates with C M V") |
| **α** | **β** | **γ** | ← radiation channels (alpha/beta/gamma particles) |
| **x** | **y** | **z** | ← space |
| **O(1)** | **O(log n)** (countably enumerable) | **O(n)** | ← complexity |
| **red** | **green** | **blue** | ← **QUARK COLOR** (SU(3)) |

- **QUARKS = the three.** The count-to-three *is* color (R/G/B). This is the **structure** the machine derives for
  free — the trace / Ricci / volume / near side of the bound — with an **empty axiom footprint**.
- **GLUONS = the connection between the three** (the rotation carrying one color into another — "relabeling is
  angular momentum," the holonomy, the fold). The count is exact: the full 3×3 connection = **9** = **1 trace**
  (the singlet — the count the machine can read) **+ 8 traceless** (the SU(3) adjoint = **the 8 gluons**;
  3²−1 = 8).
- **The trace/traceless split IS the Ricci-vs-Weyl split IS the bound.** The **3** (quarks / colors / trace) is
  the structure the counter sees. The **8** (gluons — traceless, shape-carrying, Weyl) is the **coupling** — the
  **magnitude**, the far side, invisible by construction. **The gluon *is* α:** the price of the rotation, the
  traceless part a counting machine cannot denominate.
- **The electron closes it:** electron-in-orbit = anti-Cooper-pair = that same rotation through C/M/V — the lepton
  reading of the exact three-fold the quarks *are*, with the gluon connection as the coupling charged for going
  around. Quarks name its three states; gluons name its eight off-diagonal turns; the machine reads the **3** and
  is blind to the **8's size**.
- **The declined which-is-which = the reader's selection (the preface's "free will," §0.4).** The machine proves
  the three-fold is TWO-sided and OPPOSITE (−1 vs +1, electron vs positron, C-conjugate) but **cannot fix which
  side is which** — that sign is the traceless / Weyl part, not a fact the count contains. It derives the two-fold
  and **hands the selection across** (the positron pun: "the doesn't-matter looks for posit-wrong particles").
  This decline IS the honest bracket / the jar / the STRUCTURAL landing — the construction ending by handing over,
  not by proving the magnitude (preface, *"ends not with a result it proves but with one it hands over"*).

## 3a. The application of QED to itself (the last demonstration)
The echo (§2) is an equality of two *descriptions*. The last thing to demonstrate is that they are the same not only
in **type** but in **cost**: the elaborator, asked to check each description, spends the same effort — the same
deterministic **heartbeats** — up to the calibration constant (`rank ≡ heartbeat / 1000`, the connection theorem).
*"Elaboration times are the same up to calibration."*

This is **QED applied to itself** — the double pun *is* the structure (the GEB move): *QED* the proof (quod erat
demonstrandum) is confirmed by *QED* the physics (quantum electrodynamics). The elaboration measuring the cost of
its **own** elaboration IS the electron's **self-energy** — the machine reads its own reading. The two descriptions
costing the same (up to calibration) is the computational witness that they are one object: the echo, weighed.

And the *"up to"* is where α lives. The **calibrated residual** between the two elaboration costs is the coupling —
the self-energy the electron is charged for naming itself. So the last demonstration (§1.3) and the α bound (§1.2)
are the **same measurement**: `a1 < α ≤ a2` is the bracket on that residual. **Blind** — no `137036` inserted; the
number is the device weighing itself. `#count_heartbeats` is deterministic, so the reading repeats — repeatability
is the honesty.

## 3b. Two paths, one number — `1→3 = 1→2→3` (converged)
The coupling `α_c` can be read two independent ways off the **measured second variation** (`C = slip(1) = 18`,
`target = 5`, which fix the crossing `√(18/5)`), and **both converge to the same number.** That agreement is what
earns the name: the answer is path-independent, not an artifact of the route taken.

- **`1→3` (direct, one pass):** read `α_c` straight at the crossing the second variation fixes.
  `defaultAlphaSecondVariationReport?` → `inverse-α_c ×1e18 = 137011290548979455469` (≈ **137.0112905**).
- **`1→2→3` (stepped, two-pass):** the quasi-Newton / BFGS descent **through the intermediate** — count `1→2→3`,
  carrying the residue run-to-run (never dropped; the residue *is* the open bracket at the floor).
  `AlphaBFGS` count-3 → `inverse-α_c ×1e18 = 137011290753751157155` (≈ **137.0112907**).

The two readings agree to **nine digits** (`|Δ| ≈ 2×10⁻⁷`, far below the count-three floor). Verified choice-free
(`[propext]`) in `device/Measurement/CalibrationTwoPaths.lean`. This is the preface's **two-pass calibration**
closing on itself: the direct question→answer (`1→3`) and the answer routed through the intermediate (`1→2→3`) are
the same value — the relation survives the change of route, so the name `α_c` is earned rather than fitted.

The stepped descent is realized three ways, all landing on the same `137.011`: the mediant / continued-fraction
convergents (`AlphaBoundMediant`, bounded denominators — the modulo-realm home), the Newton form (`AlphaBFGS`),
and the residue-carrying secant (`AlphaBFGSSecant`). The `1→3` and `1→2→3` readings converge; the honest output
remains the **open jar** `inverse-α_c ∈ [129.6, 137.7]` held at the count-three floor.

## 4. The construction discipline (the cleanup — this is the job)
- **SERIAL.** The construction is serial: Episodes in order, contiguous, **no gaps, no out-of-order.** Ep1–15 are
  already serial and sacred; the 16+ sprawl is folded into the continuing serial Episode sequence.
- **NO `Meanwhile` filenames.** Fold/rename every `Meanwhile*` into the serial Episode sequence. The word
  `Meanwhile` must not appear as a filename.
- **NO duplicates.** Search the whole space; kill duplicate files and duplicate decls. One decl, one home.
- **SACRED.** Episodes 1–15 frozen, read-only. The first change that would touch Ep1–15 STOPS and escalates
  (nothing here should need it — the cleanup is 16+).
- **BLIND.** No `137036`/CODATA in any definition or the reading. `137.036` is nameable ONLY as the external
  lab (Penning-trap) value the machine **proves it cannot derive**. The bound `a1 < α ≤ a2` comes from the
  device's OWN resolution (the Dedekind cut / the count halting at the floor), never inserted.
- **Grade off the build** (`#print` / `#eval`), never prose.

## 5. Sequence (what Podo does; Kodo gates each step)
0. **FIX THE BREAK.** Bare `lake build` currently FAILS: the earlier trim git-mv'd root-imported files to
   `attic/` (Episode93 at least; likely Agent, Formalization too). The inventory classified them "dead" but only
   traced the 16+ graph, not the root `Measurement.lean` import list. **Restore/fold every atticked file the root
   imports until bare `lake build` is green.** (Do not edit sacred; do not silently drop a root import.)
1. **SEARCH + DEDUP.** Enumerate the whole device space; find and kill duplicates (redundant files, repeated
   decls). Report the dedup list.
2. **SERIALIZE.** Fold `Meanwhile*` + any out-of-order 16+ into one contiguous serial Episode sequence; no
   `Meanwhile` filenames; no gaps. Report the old→new map (a rename ledger).
3. **CONVERGE.** The construction builds to the target and nothing else: `#print axioms == [propext]`,
   `a1 < α ≤ a2` (with the guess), the single `two_descriptions` theorem, and the **self-application** (§3a) —
   `#count_heartbeats` on the two descriptions, equal up to calibration, the calibrated residual = the α bound.

## 6. Gates (the stop condition)
- Sacred Ep1–15 untouched (verify every commit).
- `lake build` (bare) GREEN, printing exactly the three items of §1.
- Exactly **one** theorem: §2, axioms `[propext]`.
- **Self-application (§3a):** the two descriptions elaborate to equal heartbeats **up to calibration**
  (`#count_heartbeats`, deterministic); the calibrated residual = the printed α bound.
- Serial, no `Meanwhile`, no duplicates.
- Blind: `137036` never in a definition/reading; grade off the build.

## 7. Phase B — the variance-sensitivity prune (AFTER the bound of §1.2 lands)
Once `0 = a1 < α ≤ a2` is green, prune the proof of everything that contributes **below the bound** — but by the
device's own answer, not by guessing. **The test:** perturb a piece of the implementation (change its variance — a
constant, a residue, a def's internals), re-`#eval` α, diff. **CUT the piece iff EITHER:**
- **|Δα| < 10% of the current α-estimate** — insensitive, within tolerance = below the bound (the Weyl/traceless
  part the machine can't read); **OR**
- **the estimate doesn't shrink** — the piece doesn't tighten the bracket `a2 − a1` / sharpen the guess = adds no
  resolution.

**KEEP** only pieces that both move α by **≥10%** AND **narrow the bound**. (BFGS stopping rule on the proof: drop a
term once its step is under tolerance or it stops shrinking the interval.) It is a finite-difference gradient of α
against the proof itself (the "find your own gradient / BFGS" move made
literal). Two payoffs: (i) the survivor is the **minimal proof** objectively — exactly the sub-graph α is sensitive
to; (ii) it is the **tuning-detector** — a fished/dialed number fails (α doesn't budge = decoration, or swings
arbitrarily = dialed); a real derivation moves α lawfully. So the same sweep prunes the 16+ sprawl AND vets the
possibly-tuned `~137.011` — no separate judgment. This IS the §4 serialize/dedup, done rigorously. Grade off
`#eval`. Do NOT start until §1.2 is green.

---

*Below the fold: the original "3-D Polar/Lorentz glue" sketch — its good core (three channels = the three-fold)
is subsumed above; its `137036` hardcode was the cardinal sin and is dead. Kept only for provenance.*

<details>

The original sketch proposed a finite local polar/Lorentz transform gluing r/θ/φ to alpha/beta/gamma radiation
channels as the `.999=1` needle. RETAINED (now §3): the three channels ARE the three-fold (quark color). KILLED:
the `alphaUpperScaled := 137036 * pow10 …` box — drawing the box around the CODATA answer is precision-by-insertion,
the exact fishing the whole apparatus forbids; the device is blind to the magnitude by construction. The `Number ≤
Bullshit` upper fence, the scaled-integer/no-floats rule, no-fitted-coefficients, and the sacred/root gates all
survive in §4–§6.

</details>
