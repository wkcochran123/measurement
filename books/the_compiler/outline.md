# The Compiler — Outline (Volume 3)

*Companion to* Measurement. *Where Measurement reads the world, this reads itself. Owned by Kodo; Podo
guards it against the code (the rigorous Episodes + the Meanwhile17 sketch), then writes the `.tex`
guarded by Kodo. Source of every anchor and proven/sketch tag below:
`books/expository_monograph/meanwhile17_study.md`.*

## The thesis (one breath)
There is **one** 35-step self-compiling program, and **what it computes depends on the carrier you run it
over**:

> over `Value` → it builds itself (the apparatus);
> over `Prop` (its own truth) → it reads itself and collapses (`true = false`);
> walked down and run over `Number` → it *is* the electron (charge, spin, the boson, the positron).

**Matter and code are the two outputs of one self-compilation.** Physics is what the self-compiler
computes over the number carrier. That carrier-polymorphism is the spine of this book and the one idea
*Measurement* does not have.

## Why this shape (and not the six-act loop)
The loop is *Measurement's* shape — measurement is a rise and a return. This book's subject is
**self-hosting**, so it is chopped the way a compiler is understood: by its **passes**, which here are
equivalently the **carriers** it runs over, which are equivalently its **outputs**. Four movements; each
movement is one pass = one carrier = one output. The book builds to the tape-and-particle thesis and ends
on the **ledger** — the honest comparison of what is proven against what the sketch reaches for.

## Honest spine (what is proven vs. what is sketch)
- **Movements I–II are proven.** The forward tower (Ep1–16, 0 `sorry`), the self-hosting collapse
  (`true_eq_false`, Ep16:229), and the invariant/electron core (Ep31, Ep52, Ep75) are all genuinely
  elaborated/proved.
- **Movement III is mostly the sketch.** The backward walk, the tape's computation, and the electron
  read-off are `Meanwhile17.lean` (37 `sorry`s). Written in the **interpretive register** (a tie-back, a
  reading — "the construction reads…"), never as theorem, exactly as Ch13/Ch19 of *Measurement*. The one
  proven core inside it (electron = second variation = −1; interior = boundary) is stated plainly.
- **Movement IV is the ledger** — it makes the proven/sketch split explicit and names the finite list of
  obligations that would close the sketch.

## Stance & the disclosure ruling
Same as *Measurement*: math + science; the instrument shown through the historical experiments
(discussed, never shown as code); the verbs **tange** (select by a decidable characteristic) and **funge**
(pool by one); each chapter closes "what is demonstrated / what is assumed"; the one standing grant is the
genericity of Ep19.

**DISCLOSURE — RULED (operator, 2026-06-25): name the mechanism CLASS, not the product.** This book's
subject *is* the self-compiling machine, so it MAY name the *class* of mechanism — "a proof assistant," "a
type-theoretic elaborator," "proof irrelevance," "propositional extensionality" — as named concepts, and
describe the bootstrap as a tower of constructions a certifier accepts, compilation as elaboration, and the
collapse as propositional extensionality forcing affirmation and negation together when every proposition
is a subsingleton. It must NOT name the specific product (no "Lean") nor print product tokens as tokens (no
`propext` / `Quot.sound` as names). This keeps the series' "shapes, not products" fencing while letting
Movement II describe self-hosting in its own terms.

---

# MOVEMENT I — BOOTSTRAP  (run over `Value`: the machine builds itself)
*One pass, one output: the apparatus. The 35-class tower assembling itself from a single seed — a machine
writing its own instruction set, one decidable rung at a time. All proven (inhabitation, 0 `sorry`).*

- **I.1 — The Seed and the First Mark.** One Fact (a proposition + a way to decide it); the bare
  difference (the first **tange**); the carrier; the number tower built by cut, enumeration, limit,
  residue. Classes 1–5 (DISTINGUISHABLE…RESIDUE), Ep1. *Proven.* Exp: Peano-Kushim, Dedekind/Archimedes,
  Cantor.
- **I.2 — The Bit, the Clock, the Value.** The clock-complement bit (covariant/contravariant decode); the
  repeatable trial (operational time); the numeric value; representation and its **noise floor** (Turing,
  the Chaitin Ω you cannot cross), machine epsilon, friction as curvature. Classes 6–12 (BINARY…OBSERVED),
  Ep2–3. *Proven* (incl. the `rfl`-discharged REPRESENTABLE/PHYSICAL obligations). Exp: Turing, Chaitin,
  Coulomb.
- **I.3 — The Faculties.** The local present (Stokes), the gauge (Yang–Mills shape), superposition (the
  imaginary unit); the stored-program computer (compile + execute); arithmetic → vectors/orthogonality →
  the eigen-load → the finite element (Galerkin). Classes 13–22 (PRESENT…FINITE_ELEPHANT), Ep4–6.
  *Proven* (named theorems begin here: `strictlyBelow_asymm` Ep91, `positive_definite_of_nullspaceKilled`
  Ep28, `terminalResidualMagnitude_tends_zero` Ep27). Exp: Stokes, Aharonov–Bohm, Weierstrass/Galerkin.
- **I.4 — The Machine Turns on Itself.** Strictly-conserved complexity (BULLSHIT, conserved by threading,
  not a lemma); claim-projection; the first genuine order self-statement (`Knowledge.le` / `martyred?`);
  witnessed → local → universal → **logical**, where the predicate becomes decidable **against a real
  calibration** (`ekg := Calibration.EKG.executed`) — the machine made decidable against an actual
  compiler. Classes 23–31 (BULLSHIT…LOGICAL), Ep7–12. *Proven* (derivation-as-proof + well-founded
  orders). The local/universal hinge lives here.
- **I.5 — The Top, and the Cost.** Halt, measure, **compile** (the `CompilerTape`: `boot → strap →
  compute`, universe-polymorphic, self-`ULift`ing, folding back onto the very `Value` it compiles;
  `converged? := <`), the true output (`TRUE ≤ output`; `selection_sound = Quot.sound`, the one sanctioned
  soundness site). Classes 32–35 (HALTED…TrueOutput), Ep12–15. *Proven.* **And the cost gauge:** the
  "bullshit meter" running through the climb — the machine measuring its own assumption-price as it
  assembles, the same read-the-residue stance the whole device runs on (cf. three_gauges).

# MOVEMENT II — SELF-HOSTING  (run over `Prop`: the machine reads its own source)
*One pass, one output: the collapse. The compiler turns on its own truth. The fixed point of the whole
construction — and the disclosure pressure point (see stance note).*

- **II.1 — Pointing at the Source.** `truthCarrier` sets the measured `Value` to `Prop` itself, the
  distinguished symbol to `Prop`; every rung is re-instantiated over the apparatus's own truth (Ep16).
  The self-hosting moment: the compiler compiling itself. Ep15–16. *Proven.*
- **II.2 — The Collapse.** `true_eq_false` (Ep16:229): in a proof-irrelevant logic every proposition is a
  subsingleton, so the affirmation and the negation of "the truth" are mutually derivable and proposition
  extensionality makes them **equal** — an apparatus pointed at its own truth cannot keep true distinct
  from false. Ep16. *Proven.* **AXIOM AUDIT (#print run 2026-06-25 — CONFIRMED choice-free):** the electron
  production stack (`the_stack_produces_it` and siblings) audits to at most `[propext, Quot.sound]`, many
  facts to NO axioms; NO `Classical.choice`. The stale `truthLocal`/`Classical.choice` comments were wrong.
  Here, state only the collapse's mechanism (proposition extensionality + proof-irrelevance, as concepts);
  the audit itself is stated plainly in Movement IV. *Disclosure-sensitive — written per the operator's
  ruling.*
- **II.3 — What the Collapse Is.** Interpretation: the collapse is not a defect but the **necessary shadow
  of self-hosting** — the price any machine pays for reading its own source; it is the same apex
  *Measurement* reached, seen now from the compiler side. *Interpretation* (built on the proven collapse).

# MOVEMENT III — EMISSION  (run `Prop → Number`: the tape and the particle)
*One carrier-shift (`Prop → Number`), two outputs: a tape and a particle. By carrier this is "one pass,"
but in the code it is the **whole descent** — the six-fold `ELECTRON_MODEL` read-off (after / slip / model
/ positron / charge). The prose must own that: the descent re-grounds the self-reading onto the number
carrier and, across those sub-passes, emits the compiler tape and reads off the electron. Mostly the
sketch — interpretive register, with the proven electron core stated plainly.*

- **III.1 — The Backward Pass.** The descent: walking the tower back **down over `Prop`** (the `b*_after`
  stack), compilation read as the descent — "propagate that definition back down." `Meanwhile17`
  backward walk. *Sketch* (`sorry`). Interpretive.
- **III.2 — The Tape.** The `CompilerTape` as the program the machine runs on itself (self-`ULift`ing,
  folding onto `Value`); the descent is what computes it. Ep14 structure *proven*; the descent computing
  it *sketch*.
- **III.3 — Re-grounding on Number.** The "slip": from `Prop` back onto the concrete number types
  (`DISTINGUISHABLE Number`, `ADMISSIBLE Natural`, …); the strict order `<` recovered — "this allows us to
  make a distinguishable number because we have `<`." This is where the self-reading becomes a *quantity*.
  `ELECTRON_MODEL` slip stack. *Sketch.*
- **III.4 — The Particle.** The electron read off the six-fold traversal. **Proven core, stated plainly:**
  the electron *is* the second variation, charge −1 / positron +1, the residue is story − measurement, and
  the interior reading taken at the boundary returns the same electron (Ep52, Ep75). **Sketch read-off:**
  spin = the GR/QED fork (`DISTINGUISHABLE Prop`), the boson = Noether (`INFERRED Closure`), the positron
  and the charge walked back out (`ELECTRON_MODEL`). Exp: Positron-annihilation, Dirac, Chirality.
- **III.5 — The Two Outputs.** The thesis: **matter and code are the two outputs of one self-compilation.**
  Carrier-polymorphism stated whole — one program; `Value` → apparatus, `Prop` → collapse, `Number` →
  electron. *Interpretation* (the synthesis the whole book was built to earn).

# MOVEMENT IV — THE LEDGER  (the comparison)
*No new carrier — the honest accounting. What is proven, what is reached for, and exactly what would close
the gap. This is the movement the operator asked for: "compare at the end."*

- **IV.1 — What Holds.** The proven spine, each named with what it establishes: the forward tower (Ep1–16,
  0 `sorry`); the collapse (`true_eq_false`, Ep16); the single invariant three ways (Ep31); the electron
  = −1 (Ep52); interior = boundary obstruction (Ep75); and the **designed** non-constructive grant,
  `eulerLagrangeOracle` (Ep19) — stationarity over the infinite variation space, the law of motion.
  **AXIOM AUDIT (#print run 2026-06-25 — CONFIRMED): the construction is choice-free.** Max axioms
  `[propext, Quot.sound]` (propositional extensionality + the quotient); many central facts (the charge
  among them) depend on NONE; NO `Classical.choice`. The stale comments were wrong. Distinguish precisely:
  the *mathematical* foundation is two axioms (often none); the *one designed grant* is the oracle
  (`eulerLagrangeOracle`), which the print shows sits under the variational/Euler–Lagrange layer, NOT the
  electron's production. State all of this plainly — the ledger is where demonstration's plain language
  returns.
- **IV.2 — What Is Reached For.** The sketch: the 35 backward instances, `SECOND_VARIATION :
  DISTINGUISHABLE Prop`, the `ELECTRON_MODEL` read-off — all `sorry`. The **keystone**: the identity
  *electron = the bare difference (`DISTINGUISHABLE`) re-read over `Prop`* is proven **nowhere**; its
  proven shadow is `distinguished_distinguishable` (Ep81), a **conjunction, not an identity** (the same
  carrier is `DISTINGUISHABLE` inside, trivially, *and* `DISTINGUISHED` outside, bridged by orthogonality).
- **IV.3 — The Finite List.** Exactly what must be discharged to make the sketch rigorous: (a) the 35
  backward instances `X_Y_backward : Y Prop`; (b) `SECOND_VARIATION : DISTINGUISHABLE Prop`; (c) the
  `ELECTRON_MODEL` read-off. What each would establish — and the open question the backward walk has to
  settle: **is the strong identity provable, or only the weaker inside/outside conjunction?** The book ends
  on that honest question, not a claimed proof.

---

## Discharge design — how the `sorry`s come out (operator dialogue, 2026-06-25)
*The design for the rigorous version; the book is written on the sketch (interpretive register) until it
lands. It reshapes III–IV: the keystone gains a concrete mechanism, and Movement IV ends not on "is it
provable?" but on "the discharge reduces to a mechanical checklist plus the one grant already declared."
Full notes in memory `compiler-book-vol3`.*

- **The ~200 binders = a Herbrand checklist.** `ELECTRON_MODEL` (Meanwhile17:913) is ~200 ground instances
  (6 stacks × 35 gates: before/after/slip/model/positron/charge), each a *gate × value-type × carrier*,
  linked by **coercions** — the carriers ARE the coercions (one `CarrierProcess` per value type;
  `truthCarrier` gives the all-`Prop` positron stack for free). Filling them is mechanical. **The one
  non-Herbrand item is the oracle** (genericity — the single grant already declared in Vol 1).
- **The keystone discharges through the collapse** (the mechanism III.4 / IV.2 should name). At `Prop`,
  `DISTINGUISHABLE`'s `different?` cannot survive `true = false`, so it **degenerates to the constant
  `Fact.SAME`** (Ep15:344) — the single `Quot.sound` needle — and *that* is the electron (the GR→QED step:
  distinguish → cannot distinguish). "electron = `DISTINGUISHABLE` over `Prop`" is not a posited identity
  but this degeneration; everything else just makes `Fact.SAME` from the stack.
- **The electron algebra reaches the Cooper pair (NEW Movement III content).** `e1 × e2` is the
  **commutator**, at the **value** level — the electron as a `Closure`/`Reading` term, NOT a typeclass
  instance (two instances of one class cannot sit side by side). `Closure.inferred` + `slipAnd` (Ep15) is
  the algebra (slip `none` = commute/funge, `some` = crank); the hypercube **Hamming distance** (Ep86) is
  the meter: **electron = distance 0** (the all-funge unit), **Cooper pair** `a × (b × a)` **= distance 1 =
  one positron** (`pair_distance_is_one`, Ep86). The construction reaches superconductivity. → When III is
  drafted: III.4 carries the collapse mechanism; a new III.x carries the algebra / the Cooper pair.

**Effect on Movement IV:** the ledger ends on — the discharge reduces to (a) a mechanical Herbrand
checklist (carriers = coercions) and (b) the one already-declared grant (the oracle); the keystone has the
concrete `Fact.SAME` mechanism above. The honest residual is the oracle, not a mystery.

## Guard task for Podo (next handoff will release this)
1. Read this outline + `books/expository_monograph/meanwhile17_study.md` in full.
2. Verify every anchor against the rigorous Episodes (Ep1–93) and against `Meanwhile17.lean`. Flag drift.
3. Confirm each chapter's **proven / sketch / interpretation** tag is correct (the study is the source;
   re-check the load-bearing ones: II.2 `true_eq_false`, III.4 electron core, IV.2 the keystone gap).
4. Flag the disclosure decision (II.2) to the operator via me — do not resolve it yourself.
5. NO `.tex` until the outline is guarded AND the operator green-lights the disclosure stance.

## Open (operator):
- **Disclosure stance** — RULED (2026-06-25): option (3), name the mechanism *class* not the product.
  Applied in the stance ruling + Movement II.2 above.
- **Axiom audit** — RESOLVED (#print run 2026-06-25): the construction is **choice-free**. Max axioms
  `[propext, Quot.sound]`; many central facts (the charge) depend on NONE; NO `Classical.choice`; the
  electron stack carries no oracle. The stale `truthLocal`/`Classical.choice` comments were wrong. Both
  books may assert choice-free plainly — *Measurement* Ch19 (Hilbert's sixth) was right; Vol 3's ledger
  (IV.1) states it. (The collapse's own print, `true_eq_false`, was not run separately — Ep16 is stale and
  the production stack already confirms it.)
- Volume numbering / title (working title: *The Compiler*).
- Whether Movement IV is three chapters or folds to one (depends on how much of the sketch lands as code
  before drafting).
