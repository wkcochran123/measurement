# Compact Ledger Σ

Purpose: shared shorthand for outline, prompt, and UAT work. These symbols are
internal working notation unless a later coinage pass promotes them into the
reader-facing book.

## Core Chain

```text
metaphor ⇒ Γ ⇒ #Γ ⇒ β
```

| Symbol | Reading | Use |
|---|---|---|
| `τ` | truth-condition | What may hold; wider than any record. |
| `ε` | event | Admissible boundary crossing. Use `event`, not `move`, in Measurement prose. |
| `μ` | mark / outcome | Durable finite difference left by `ε`. |
| `κ` | reckon | Encode `μ` into partial numeric order: countable, comparable, orderable, passable. |
| `ρ` | receipt, `κ(μ)` | Reckoned outcome carried forward as witness. |
| `φ` | fact, `⟨τ,ρ⟩` | A truth-condition admitted with a receipt. |
| `α` | calibration | Baseline that makes later receipts comparable. |
| `β` | boundary | Admissibility surface: what may enter the record. |
| `σ` | sample | Finite held surface presented to an observer. |
| `ω` | observer | Orientation partner, not an omniscient owner. |
| `δ` | residue | What remains as pressure after admissible reckoning. |
| `λ` | limit-promise | Finite promise that a completion is being approached, not possessed. |
| `Γ` | grammar | BNF-like metaphysical rule for allowed events. |
| `#Γ` | count | Finite stages, refusals, compatibilities, or residuals made inspectable. |

## Doctrine

```text
τ may be true without becoming φ.
μ may persist without becoming ρ.
ρ witnesses; it does not exhaust τ.
φ = claim + admissible receipt.
```

Galileo/Hooke form: the moons or cells can be real before the instrument, but
they become facts for the ledger only when a boundary produces repeatable
reckoned receipts.

## Grounding Contract

```text
private Lean episodes ground the logic
public prose never names or points at them
```

Kodo/Podo handoffs may use private episode anchors, declarations, and line
spans to keep the argument honest. Reader-facing LaTeX must translate those
anchors into metaphysical grammar. A public claim should expose what the
private anchor does, not where it lives.

Translation test:

```text
private anchor asks: which episode/declaration supports this?
public prose asks: which boundary, event, mark, reckoning, receipt, fact,
                   residue, invariant, or completion door makes this necessary?
```

Failure modes:

```text
"Episode 17 shows..."       -> forbidden
"the Lean construction..."  -> forbidden
"the source defines..."     -> forbidden
"the private proof..."      -> forbidden
```

## Expository Naming

Non-satirical exposition may translate source names into public metaphysical
names. The public name should preserve:

```text
grammar role
count effect
boundary protected
relation to τ, ε, μ, κ, ρ, φ, α, β, σ, ω, δ, λ, Γ, or #Γ
```

It does not need to preserve:

```text
satirical naming
implementation-shaped naming
private class/structure/field names
source-order phrasing
```

Rule of thumb: keep the role, rename the costume. If the old name carries
satire, source scaffolding, or code-shaped residue, Kodo may choose a cleaner
reader-facing term and ledger the private anchor separately.

## Tange / Funge

| Term | Working verb | Meaning |
|---|---|---|
| tangible | `tange` | Force an abstract claim into holdable, inspectable, passable structure. |
| fungible | `funge` | Let a tangible witness circulate through compatible events without dragging the whole origin story. |

Trust bridge:

```text
tange ≈ parabolic pressure: time-directed settling under resistance.
funge ≈ elliptic pressure: boundary compatibility that preserves guardrails.
```

This is an internal analogy, not yet a theorem. Use PDE/FEM citations only when
a later outline budgets them. Candidate trust anchors: `evans2010`,
`brenner2008`, `ciarlet1978`, `strang1973`, `lions1968`, `courant1953`,
`courant1943`.

## Public Grammar Template

```text
1. image: finite metaphor
2. Γ: BNF-like metaphysical grammar
3. #Γ: countable stages/refusals/checks/residuals
4. β: boundary / shortcut forbidden
5. citation: optional trust anchor, never the source of authority
```

## Glyphs And Macros

Glyphs are available in the working ledgers. TeX macro names stay ASCII so the
book can build predictably; the printed symbols may be expressive.

LaTeX registry: `latex/measurement-macros.tex`

| Ledger glyph | LaTeX macro | Printed meaning |
|---|---|---|
| `τ` | `\Truth` | truth-condition |
| `ε` | `\Event` | event |
| `μ` | `\Mark` | mark / outcome |
| `κ` | `\Reckon` | reckon |
| `ρ` | `\Receipt` | receipt |
| `φ` | `\Fact` | fact |
| `α` | `\Calibration` | calibration |
| `β` | `\Boundary` | boundary |
| `σ` | `\Sample` | sample |
| `ω` | `\Observer` | observer |
| `δ` | `\Residue` | residue |
| `λ` | `\LimitPromise` | limit-promise |
| `Γ` | `\Grammar` | grammar |
| `#Γ` | `\GrammarCount` | finite grammar count |

Convenience macros:

```text
\measurementchain  = τ → ε → μ → κ → ρ → φ
\grammarcountchain = metaphor ⇒ Γ ⇒ #Γ ⇒ β
\factpair          = φ = ⟨τ,ρ⟩
\factof{τ}{ρ}      = ⟨τ,ρ⟩
\reckonsof{μ}      = κ(μ)
\tange, \funge     = internal operators unless promoted later
```

## Σ Negotiation Protocol

Kodo and any returning Podo/agent must negotiate symbols as a shared language,
not as private decoration. The goal is to let the agents jointly build a
symbolic encoding of the grammar.

No new durable glyph or macro is accepted until it has a Σ-handshake:

```text
glyph/macro:
  proposed mark:
  spoken name:
  arity:
  grammar role:
  count effect:
  boundary it protects:
  public status: internal | dormant-latex | reader-facing
  collision check:
  example:
  owner of next action:
```

Rules:

```text
1. Extend, do not fork, the Σ ledger.
2. Prefer one glyph per metaphysical role.
3. A glyph must say what it counts or what boundary it protects.
4. A macro must point back to the ledger glyph.
5. Podo may propose symbols; Kodo ratifies or asks for reconciliation.
6. Conflicts are resolved by comparing ledgers, not by silently overwriting.
7. Reader-facing promotion requires a separate prose/notation pass.
```

Minimal acceptance test:

```text
Can this symbol encode an allowed event, receipt, refusal, compatibility, or
residue more clearly than prose alone?
```

## Style Gates

```text
public book = metaphysical theory itself
private anchors = coordination only
reader-facing leakage = 0
tedium throttle = keep guardrails in Σ/UAT; prose shows mechanism
voice gate = active voice only in reader-facing prose
```

Forbidden in final LaTeX unless Codex grants a narrow exception:

```text
source code, codebase, source file, compiler, proof assistant, theorem prover,
build command, import, file path, declaration name, verbatim code, \texttt{...},
"the code says", "the compiler accepts", "the file proves"
```

## Active Voice Gate

Reader-facing prose must use active voice for events. A passive event-sentence
blocks acceptance unless Kodo grants a local exception for a named reason.
Copular definition sentences may use `is/are` when they define, classify, or
coin a term rather than hide an actor.

Rewrite pattern:

```text
bad:  The receipt is carried by the apparatus.
good: The apparatus carries the receipt.

bad:  A fact is produced when a mark is reckoned.
good: Reckoning turns a mark into a fact-bearing receipt.
```

UAT check:

```text
1. Find forms of be/get + participle.
2. If the sentence defines or classifies, route it through the Definition Template.
3. Otherwise ask who acts.
4. Put that actor before the verb.
5. If no actor belongs in the sentence, recast around the event itself.
6. Leave no passive event-sentence in final LaTeX without an explicit Kodo exception.
```

## Definition And Coining Template

Coinages and definitions must make `is` do visible work. A definition may use
a copula; it may not smuggle a passive event into the prose.

Template:

```text
term:
status: internal | trial-public | reader-facing
part of speech:
spoken form:
need:
genus:
differentia:
definition sentence:
active event sentence:
Σ role:
grammar rule:
count effect:
boundary protected:
near words:
collision check:
example:
non-example:
promotion test:
```

Definition sentence pattern:

```text
<term> is <genus> that <differentia>.
```

Active event sentence pattern:

```text
<actor/event> <verb> <object> <result>.
```

Example:

```text
term: receipt
definition sentence: A receipt is a reckoned outcome carried as witness.
active event sentence: Reckoning turns an outcome into a receipt.
Σ role: ρ = κ(μ)
count effect: makes the outcome passable and comparable.
boundary protected: receipt does not exhaust truth.
```

## Kodo / Podo

```text
Kodo = Codex thinker: budgets, order, UAT, claim-boundary closure.
Podo = doer-agent: draft/build/report inside restricted prompts.
Operator = source authority and final editorial owner.
```

Routing ids remain `codex` and `antigravity`; Kodo/Podo are internal Ryot role
names unless the operator opens an attribution pass. Antigravity may serve as
Podo; a second Codex may serve as Podo if it accepts the doer contract and
leaves Kodo's final acceptance gate intact.

## Anecdote Form

```text
before β: distinction unavailable/blurry
β imposed: instrument/apparatus sets the admissible surface
ε occurs: boundary crossing
μ remains: durable outcome
κ reckons: partial numeric order
ρ circulates: witness
φ enters: claim + receipt
limit: fact, not total reality
```

## Fixed Glossary (operator ruling 2026-06-13: trim hard)

Operator ruling: trim the reader-facing vocabulary HARD to a small fixed set
(funge/tange + the core grammar) and rename everything else to standard
mathematics. The book uses standard math freely (USE-MATH); only the SANCTIONED
coinages below are non-standard, and every other invented term is renamed.

PROPOSED - awaiting operator ratification before mass application. Until ratified,
do not mass-rename in the chapters.

### Sanctioned reader-facing set (everything else renames to standard math)

```text
Core chain (already in this ledger): truth-condition, event, mark, reckon /
  reckoning, receipt, fact, calibration, boundary, sample, observer, residue,
  limit-promise, count.
Structural terms kept (load-bearing in the ladder): vessel (the localized arena;
  "carrier" renames TO "vessel" for one word), distinction / distinguish,
  admissible / admissibility, sequence, route.
Sanctioned coined verbs: tange, funge (now reader-facing - entries below).
```

Anything not on this list that is an invented/idiosyncratic term is a defect:
rename it to the standard mathematical term (or to a sanctioned term above).
Genuine standard math terms are always allowed and are NOT coinages (e.g. "finite
support" is the standard notion of support; keep it).

### tange / funge - reader-facing Σ entries

```text
term: tange
status: reader-facing (operator ruling 2026-06-13)
part of speech: transitive verb
spoken form: "tange" (rhymes with range)
need: name the measuring act - fixing a circulating claim into a held form
genus: a measuring act
differentia: takes a funged (circulating) record and fixes it as a concrete,
  held, inspectable mark/receipt
definition sentence: To tange a record is to take a funged record and fix it as a
  held, inspectable mark.
active event sentence: An instrument takes a funged record and tanges it.
Σ role: tange : (circulating record) |-> ρ (held receipt); measurement IS tanging.
count effect: yields one held, countable receipt from a circulating input.
boundary protected: a tanged receipt is held/inspectable but does not exhaust τ.
collision check: coined; no standard-math collision.
example: the clock face tanges the held receipt.
non-example: asserting a claim without holding it is not tanging.

term: funge
status: reader-facing (operator ruling 2026-06-13)
part of speech: verb (intransitive, also transitive "funge X")
spoken form: "funge" (rhymes with plunge)
need: name circulation - letting a held witness pass between compatible events
genus: a circulation act
differentia: lets a tangible witness pass between compatible events without
  dragging its whole origin story, costs still attached
definition sentence: To funge a record is to let a tangible witness circulate
  between compatible events without dragging its whole origin.
active event sentence: The closed report funges: it circulates between later
  witnesses with its costs attached.
Σ role: funge : ρ (held receipt) |-> (circulating witness); circulation IS funging.
count effect: preserves the receipt's count while extending its reach.
boundary protected: a funged witness keeps its refusal/residue attached; it does
  not shed constraints.
collision check: coined; no standard-math collision.
example: the pair funges the difference token so it can circulate.
non-example: copying a receipt while dropping its refusal is not funging.

CANON: "An instrument takes a funged record and tanges it." Measurement IS
tanging; circulation IS funging. A witness chain alternates tange -> funge ->
tange. Introduce + define both at first reader use in Chapter 1 (K-FT ruling);
reinforce at C02-S01 (which already uses tangible/fungible). The \tange and
\funge macros are now reader-facing, not internal-only.
```

### Rename map (coinage -> standard math / sanctioned term)

```text
NAMED collisions (mandate, confident):
  forcing / tangible forcing      -> drive / advance
  (relative) variance             -> relative difference / discrepancy
  covariant / contravariant order -> same-orientation / opposite-orientation
  parity / trivial / truth parity -> reflexive equality (a = a)
  pseudo-rational                 -> finite fraction
  halting (K-HALT)                -> stop / arrest / termination
  gauge / gauge event (K-GAUGE)   -> recalibration / update step
                                     (RESERVE "gauge" for Ch13+ gauge theory)

Novel coinages -> standard (confident):
  braided count                   -> ordered pair / joined pair
  itinerary                       -> route / finite path  (use sanctioned "route")
  slip (free middle coordinate)   -> the free intermediate point; its variation
  unresolved place                -> unresolved point
  admissible physicality          -> admissibility (sanctioned "admissible")
  tally                           -> count (sanctioned)
  number-facing handle            -> the exposed value
  convergence machinery / residue
    interface / structural limit  -> drop "machinery/interface" dressing; use
                                     "residue" (sanctioned) + standard limit /
                                     convergence
  "stimulus/expectation fixtures" -> stimulus and expectation (drop "fixtures")

Standard words used in non-standard senses (signpost once, keep standard sense):
  value, magnitude, scale, load   -> standard senses; "scale"/"magnitude" must
                                     NOT bleed into the later technical gauge-scale

Vague coinages needing per-section judgment (propose at gate time):
  narrative amplification, recruited account, adoption order,
  institutional bearer (C04-S04 overhead cluster), direction-request (C03-S04)
                                  -> rename to the plain standard concept per
                                     section; flag any that resist a clean term.
```
