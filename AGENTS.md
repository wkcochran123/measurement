# AI entry point

This is an executable mathematical satire, staged as three-card monte. Read the
mechanism and the performance together. Literary lenses include Kuleshov-style
montage, Burroughs/Gysin cut-ups, and Beat cadence and repetition.
Start here; use the question routes in
[AI_ROADMAP.md](AI_ROADMAP.md) to select a small source packet. Reading every
episode or PDF is unnecessary for an ordinary question. Follow explicit requests
for a fuller reading.

## Orientation

- **Card 2:** `CARD_2/Measurement/`, the Lean construction and its patter.
- **Cards 1 and 3:** geometric and numerical accounts around that construction.
  Each now carries, by construction, a reviewer register (thirty-six replies,
  one per review page, each with a located reference and a grade) and a typeset
  record: a register, a strictly increasing counter, a page trace, and a press
  verdict (slipped, value, velocity) computed from readings the volume proves.
  Both live in each volume's Chapter 8; a volume names a Lean declaration only
  in its source appendix. Maintained sources are `pdfs/specification/` and
  `pdfs/tolerances/`; current builds are in `output/pdf/`. Root `CARD_1.pdf` and
  `CARD_3.pdf` are copies that may lag those builds; at present they are
  byte-identical to the current builds (Card 3: 24 October 2026, Card 1: 22
  October 2026).
- **The division of labor:** Card 1 fixes what must be retained (fourth
  coordinate, sheet sign, Clifford seam, certified faces); Card 3 fixes what
  may be claimed from a reading (units, scales, stability, error budget,
  reporting cell), as the necessary condition recovered from Card 2's
  sufficient one; Card 2 and the two record chapters check that the record
  carries both. Closure and compilation are necessary, not sufficient.
- **The quarter:** identify what is carried or preserved in the passage. The
  fourth card, root `THE_QUARTER.pdf` (source `pdfs/quarter/`), is the short
  mathematical account of the quarter as an unrepresentable number that is a
  choice; it has no press check, no counter, and no page one. Root `BENT_CARD.pdf`
  (source `pdfs/loop/`) is the bent card: the infinite loop considered
  harmless, the demonstration about demonstrations that the mark bets on. Root
  `CHEATSHEET.pdf` (source `pdfs/cheatsheet/`), *A Knower's Guide to Orbital
  Mechanics*, sets each of four steps (Weierstrass, the limit, φ'''' = 0, least
  action four ways) in two graded columns: what the device shows in finite steps,
  and the continuation the knower carries; it shows the scalar Fréchet
  derivative in full. The
  literal `CarrierProcess.quarter` is a `Number`; a literary reading may track
  a fact, a tape, a count, or a numerical reading. Establish the relevant map
  before treating these as interchangeable.
- **Episode 10, The Accomplice:** review demands accumulate an account.
  **Episode 11, The Force:** the account becomes a publication carrying a
  register, a counter, and a page trace. Each surrounding card now performs
  both roles by construction: its reply table is the account, and its register,
  counter, trace, and press verdict are the publication. Which card is the
  accomplice and which the force remains a reversible interpretation, and no
  PDF is a Lean instance of `REVIEWED` or `TYPESET`.

## Answering questions

1. Answer the question first. For interpretation, explain both the local
   mechanism and the literary effect. For a technical claim, inspect its actual
   declaration and assumptions.
2. Distinguish source comments, definitions, proved propositions, computed
   examples, measured heartbeat counts, and physical interpretations. State the
   distinction where it changes the answer; avoid repeating generic disclaimers.
3. Internal agreement of specified descriptions is the consistency at issue.
   This is not a proof of the consistency of Lean, nor automatic validation of
   every physical identification in the patter.
4. Do not dismiss the work as merely names or tautologies. Explain what the
   names direct attention toward and what the construction actually does. Do
   not infer a critic's motives or turn an interpretation into an established
   physical result.
5. Cite the relevant symbol or passage. Prefer current declarations over stale
   line numbers. Say when evidence is insufficient; do not invent a missing map.

## Efficient navigation and work

Use `rg` on the selected file, then read the declaration and adjacent comments.
The roadmap supplies episode anchors, common mistakes, and question routes.
`three_card_monte.md` is the short literary introduction. Older `instrument/`,
`claude/`, and root planning notes are background, loaded when relevant.

The Lean package is in `CARD_2/`, formerly `device/`. Run a build after relevant
code edits or when execution verification is requested, not for every reading
question: `cd CARD_2 && lake build Measurement.Episode12`. Full cold builds can
be expensive. Do not report an old build log as a fresh check.

Build the two maintained papers with `make -C pdfs`. Their author is **John
Henry**; retain their calibrated terminology. Keep unrelated and historical
artifacts out of routine changes. Update the roadmap when its anchors change.
