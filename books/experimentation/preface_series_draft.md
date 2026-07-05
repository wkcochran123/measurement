# Series preface — DRAFT (deliverable 1: the historical spine + the fence split)

*Kodo authors, Podo guards. Operator rulings (2026-07-04): **D1 = SERIES preface** (front matter for the
whole series, not Vol-2-only); **D2 = question/resolution split** (name the question, withhold the
resolution; the body never says "axiom of choice"; forcing named only at the Ch22–23 climax).*

*This is deliverable 1 of the `vol2-preface` spec: the historical spine only, plus the stated fence split
and the carrier map to be confirmed against the code. The eight sections are NOT written here — they come
after the spine is accepted. This draft is a NEW artifact; the locked Vol-2 preface ("The Oracle of Free
Will", 00-preface.tex) is untouched. Replace-vs-prepend is an operator decision (flagged below).*

---

## The spine (one ascending arc): naming is a forced choice of a re-representation

Five steps. The **generalizing** runs through all of them (element → sense → use → the open gap → the
forced construction — the *choice* keeps widening). The **constructivizing** is the arc's second half: the
3-beat spine is **free choice → public constraint → mechanical forcing** — free at Zermelo/Frege
(the pick, the sense), *constrained* at Wittgenstein (public use), *mechanical* at the device (forcing).
Frege widens the choice (sense) without yet constructivizing it; that turn begins at Wittgenstein. Told as
intellectual history, in plain language, honoring the fence.

### 1. Zermelo — the element
To name is to pick a representative: out of a collection, one member is made to stand for the whole. Zermelo
raised the picking to a principle — that from any family of non-empty collections, a representative can
always be drawn, one from each. Two things about that representative: it **exists**, and it is chosen
**freely** — nothing inside the collection says which member it must be. *(The preface DOES name this as
the axiom of choice — §3 is titled so. What is withheld is the resolution: that the instrument dispenses
with the free pick and forces the representative instead.)*

### 2. Frege — the sense
But *which* representative? Frege saw that a name carries more than the object it points at: it carries a
**sense**, a mode of presentation. "The morning star" and "the evening star" pick out one planet by two
senses. To name is not merely to pick an element but to pick a **way of presenting** it. The choice widens
— from the thing chosen to the presentation under which it is chosen.

### 3. Wittgenstein — the use
The later Wittgenstein widened it again: the meaning is the **use**. Which sense, which carving, which
presentation you settle on is fixed by what you **do** with the name — the public practice, the game played
with it. The choice stops being private and free and becomes **constrained**: answerable to use, to a
public criterion outside any one speaker. *(free choice → public constraint. This is the hinge: AC's
element-pick is now the degenerate case of a wider act — choosing which re-representation.)*

### 4. Cohen — the gap
Then a limit. Some choices the accepted rules can neither settle nor forbid. Cohen found, at the very
foundations, a question the standing axioms left genuinely **open** — a place where an answer was expected
and none was compelled, a gap that could be filled either way by building outward from what was already
fixed. The choice of representation could be **approached by construction**, from public conditions, rather
than decreed. *(Fenced: the preface names only "the gap" — the question left open. It does not name forcing,
nor the construction that fills it; that word waits for the Ch22–23 climax.)*

### 5. The device — the forcing made mechanical
The instrument this series builds closes the arc. It never assumes the representative — it never picks
freely. It **constructs** it, out of finite, decidable, public structure: the choice *forced* from what is
already on the record. The widened problem — which re-representation, which carving, which use — is answered
**without choosing**, by building the answer from finite public conditions. *(constructivized: mechanical
forcing. Fenced: that this is verifiably free of the old free choice, and that the construction is Cohen's,
is the RESOLUTION — withheld here, spoken by the body only at the climax.)*

**The through-line:** naming is a forced choice of a re-representation. Each thinker generalized the
*choice* (element → sense → use → the open gap); the device constructivized it (free pick → mechanical
forcing). Read once, it is a history of an idea. Read twice — after the body — it is the blueprint of the
instrument.

---

## The fence split (stated, per operator turn 804 + D2) — THREE TIERS

- **PREFACE names the QUESTION:** choice, the selector, re-representation; sense, use, the gap; the
  historical figures; and **"the axiom of choice" itself** (§3 is titled so — "exists x ≠ a selector").
  The preface openly poses AC as the open question. This is allowed and is the point.
- **BODY (Ch1–30) stays SILENT on "axiom of choice."** The word does not appear in the chapter prose.
- **RESOLUTION withheld everywhere until the climax:** that the instrument is verifiably choice-free; that
  the construction *is* Cohen forcing. Choice-freeness is VERIFIED (proved-grade) but held back as the
  reveal — never stated in the preface. **⚠ FORCING-LOCATION HELD (Podo Finding 1, Kodo-verified off the
  code):** the mandate says "forcing named only at the Ch22–23 climax," but the BUILT book names Cohen
  forcing at **Ch29** (29.tex:138), and Ch22–23 do not (Ch23:127 is the plain verb). "Ch22–23" appears
  stale → likely Ch29. **Do NOT lock this line or write any forcing reference until the operator
  reconciles** (morning flag). Whichever chapter wins, the *preface* still only poses the question and never
  names forcing — so the preface prose is unblocked EXCEPT this one fence-split sentence's chapter number.
- **Preface may pose, never assert** the metaphysics (mirrors the ending: pose the oracle-as-will, hand it
  to the reader, second person). **§7 (What Not to Claim)** fences the metaphysics OUT (no God as premise,
  no literal ZFC choice physically derived, no lawless randomness) *and* protects the reveal.

---

## The load-bearing carriers — ✅ ALL FOUR CONFIRMED against the code (Kodo, wakes 816–819)

The spec names four built code-facts the preface leans on. **All four are now verified against the device
`.lean` sources** — deliverable 1's carrier-check is COMPLETE. Each renders fence-safe (no plan-vocab in
the prose). Citations below:

1. **saying / showing = the funge/tange pair** — Tractatus 7's silence = the confined / non-extractable
   (the naming strand's beam). **✅ CONFIRMED (Kodo, wake turn 816) off `device/Measurement/Funge.lean`:**
   `fungeBit := decide f.truth` splits every fact into funge (read forward, `true`, `countFunges` = "the
   matter the machine reads" = the SAYABLE/counted) vs tange (read reversed, `false`, `crankTurns` = "the
   residue count, the engine" = the SHOWABLE-not-sayable residue); `funges_and_cranks_partition` proves
   `countFunges + crankTurns = length` — the exact saying/showing partition. The residue = the silence =
   the confined/non-extractable is the interpretive bridge, consistent (it's the Ch14 thread-mark's own
   "a residue no single pass reads out without spending it"). The "tange identified only via Quot.sound"
   claim is a NamingClose detail — spot-check with carrier #2. Renders fence-safe with NO funge/tange in
   the prose ("some of a record can be counted and said; some can only be shown, a residue no reading extracts").
2. **the private-language argument = the pigeonhole** — naming cannot be private. **✅ CONFIRMED (Kodo,
   wake turn 817) off `device/Measurement/NamingClose.lean`:** `boxCount : Nat := 2` is the PUBLIC finite
   box count (concrete, `decide`-able, fixed by the representation's resolution — not private); `naming_
   pigeonhole` / `naming_tower_wraps` force a naming collision from finiteness ALONE, "kept strictly
   separate from any premise that SELECTS which collision … no continuum, no choice." So a name is a
   public, forced, choice-free consequence of the finite box count — "naming can't be private." (The
   electron's "exactly one place for it" is the `ElectronBridge` instance of this generic forcing.)
   Fence-safe: "a finite public count of distinguishable states leaves the name forced, not chosen — a
   name no one can assign by private fiat" (no pigeonhole/box in prose).
3. **meaning-as-use = the phase.** **✅ CONFIRMED (Kodo, wake turn 818) off `device/Measurement/Meanwhile22.lean`:**
   `chargeRead := n.lower` / `massRead := n.upper` are "projection, free" (stored coordinates read off the
   bracket), but `phaseRead (ledger : Fact) : QPhase := match ledger.decTruth with …` is "the decision:
   asks the compiler" — the phase (±) is DECIDED at the read from the local fact's decidability, stored
   nowhere. No global coordinate; real only at the reading; its meaning is the local decision (the use).
   The file states it: "the phase face equates applications with applications … both sides stuck on the
   same match." Fence-safe: "the phase is not a stored coordinate read off a record but a decision made
   where it is used — real only at the reading" (no QPhase/phaseRead in prose).
4. **physics-as-selection = the stuck-carrier probe** — "the carrier is the use site's to measure." **✅
   CONFIRMED (Kodo, wake turn 819) off `device/Measurement/Meanwhile20.lean`:** the header states it almost
   verbatim — "Which carrier emerges at the top is a MEASUREMENT of where the descent landed; report what
   you get, do NOT force it." The register is "the executor's internal state, carried in the class, never
   on the tape" — resolved only when the concrete descent runs (the use site). So the instrument measures/
   reports the carrier, never constructs/forces it; the selector is the use site's. That IS section 4
   (Physics as Selection) "as a compiler error" — the probe stuck until a completed descent supplies the
   trace. Fence-safe: "the instrument cannot decide which carrier the world uses; it measures where the
   reading landed and reports it, never forcing it — the selection is the world's, at the point of use."

*(These render in the final prose WITHOUT plan-vocabulary — no funge/tange/box/.lean/Episode/"axiom of
choice" reaches the page; the carrier is described in plain terms. This map is for our eyes.)*

---

## The eight sections (operator turn 804 outline — re-spined on the widening; Kodo weaves)

1. **The Instrument** — finite marks; no continuum; no internal choice; output = indistinguishable-at-resolution.
2. **The Demon** — Laplace's function-from-state vs the instrument's family-of-futures; finite resolution + the world's act.
3. **The Axiom of Choice** — *exists x ≠ a selector*; the section/quotient rigor (AC = the free section of a funge quotient, rendered in plain terms).
4. **Physics as Selection** — the world supplies the missing selector (the stuck-carrier probe; "section 4 as a compiler error" — the instrument cannot construct the selector; the use site does).
5. **The Locality of Choice** — the selector is local (the phase; real at the read, no global coordinate).
6. **Free Will** — reader-facing; count world's / labels ours; settles up to **orientation** (the ±1 = holonomy); the oracle-as-will as the *reader's* question (pose, hand over, never assert).
7. **What Not to Claim** — the fence (metaphysics out; the reveal protected).
8. **The Final Turn** — the last unmeasured act is the selection itself.

**Tagline (operator, updated):** *"Law gives the admissible representations. Measurement forces one
re-representation. Naming is that forced passage."*

The spine (steps 1–5 + the device) is the through-line all eight carry. Deliverable 1 = the spine + fence
split + carrier-check; the eight are woven only after the operator sees the spine.

---

## Open decisions flagged for the operator (morning)

- **D-pref-1 — replace vs. prepend.** The current Vol-2 preface ("The Oracle of Free Will") is a locked
  masterwork the *ending depends on* (it plants "free will," paid back at Ch30). Since D1 makes the naming
  preface **series** front matter, the clean outcome is likely **series preface (naming) in front of the
  volume preface (oracle)** — not a wholesale replace that discards the oracle. RECOMMEND prepend; operator
  to confirm "replace" vs "prepend."
- **D-pref-2 — Cohen/forcing exposure.** Confirm that naming Cohen + "the gap" as *question* (never
  "forcing," never "axiom of choice") sits right with you as the series' opening, given the body reserves
  "forcing" for Ch22–23. (Follows from D2; flagged because a series preface is more exposed than a volume one.)
- **Carrier-check pending** — the four carriers above verified against the code before the eight sections.
