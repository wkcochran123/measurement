# Volume 2 — The Math
## Outline v0.1 (to Kodo's section gates + Beastmaster's whole-book gate)

Assignment (operator, 2026-07-25 13:18–13:27Z): fresh volume, old vol2 retired.
"The construction of differential geometry from topology and linear algebra
through the lens of physical descriptions." Outline first, then the PDF.

## 0. The laws this volume is built under (the charter — gates read this first)

1. **THE CITATION LAW** (operator, verbatim intent): *no original idea appears
   in this book.* Only cited ideas. Every mathematical claim on any page traces
   to a name and a date in the back matter. The gate test per claim: "off which
   source was this read?" The failure mode to hunt: the un-citable sentence.
   If a physicist has to remodel anything in their head, we wrote an original
   idea by accident.
2. **THE LENS LAW**: the device is the LENS, never the originator. The book
   shows how cited mathematics already describes the electron. The apparatus is
   cited once, as apparatus; carried device structures may ILLUSTRATE a
   construction (fenced as illustration), never carry a claim.
3. **FACE GRADES** (from the 2026-07-25 receipts, held throughout): topology =
   CARRIED (structure); geometry = carried (the bracket walk); algebra =
   carried (exact rationals); numerics = carried (measured computation);
   Navier–Stokes = OWED (sacred seed, fluid body not load-bearing) — named
   only as debt. Physics-face NAMES are the founding program's words, marked
   promise-or-carried, never asserted identities.
4. **Vol 1's own laws carry over**: §0 honesty (assert only what the
   construction shows; fence in flight, never after), NO Lean identifiers in
   prose, step-not-move, bracket-not-point where readings appear, pdflatex
   only, the public copy a separate decision held for the operator's word.
5. **The organizing physical axis** (named at the origin, sacred seed): the
   two transformation laws — covariant and contravariant — are the axis the
   whole construction climbs. The physicist knows them as index placement;
   the book never renames what they know (citation law), it constructs what
   sits beneath the indices.

## The arc in one sentence

The physicist already speaks differential geometry in indices; this book
builds, from cited topology and cited linear algebra, the objects under the
words they already use — one construction step per chapter, each step entered
through a physical description the reader already holds — so that at the end
the full apparatus of manifolds, tensors, connections, and curvature stands
assembled with nothing new to believe and nothing old to remodel.

## Chapters (each lists: the physical description that opens it → the cited
construction → its citation roster → the fenced lens exhibit, if any)

### Ch 1 — The Local (topology as "valid here")
- OPENS WITH: every lab statement is local — a reading valid in a neighborhood
  of the bench, not everywhere. The physicist already reasons this way.
- CONSTRUCTS: topological space via neighborhoods; open sets; continuity as
  preservation of nearness; limits WITHOUT a norm (the neighborhood definition
  — no ruler needed); separation as distinguishability (T0/T1/Hausdorff);
  quotient by indistinguishability (the Kolmogorov quotient, cited as the
  standard T0 identification).
- CITES: Hausdorff 1914 (Grundzüge der Mengenlehre — neighborhood axioms);
  Kuratowski 1922 (closure); Kelley 1955 (General Topology); Kolmogorov's T0
  axiom via the standard texts (Alexandroff–Hopf 1935).
- LENS (fenced, illustration only): an instrument that quotients its state
  space by "the reading cannot tell these apart" is performing the T0
  identification — the apparatus does exactly this (cited once, as apparatus).

### Ch 2 — The Chart (manifolds as the observer's coordinates)
- OPENS WITH: an observer lays down coordinates; a second observer lays down
  different ones; physics is what survives the change. Already how the reader
  works.
- CONSTRUCTS: locally-Euclidean spaces; charts and atlases; transition maps as
  changes of observer; smooth structure = the demand that changes of observer
  be differentiable; why "the manifold" is the coordinate-free residue of all
  charts.
- CITES: Riemann 1854 (the Habilitation lecture — told as story, at Cavendish
  grade); Whitney 1936 (differentiable manifolds made precise); Lee, Smooth
  Manifolds (the modern standard statement).

### Ch 3 — The Direction (linear algebra at a point)
- OPENS WITH: velocity. At one instant, at one place, the electron has a
  velocity — an arrow that exists before any coordinates do.
- CONSTRUCTS: the tangent space (velocities of curves); the dual space
  (covectors = the linear read-outs — a measuring device is a covector);
  the TWO transformation laws derived, not decreed: components of vectors
  transform one way under change of chart, components of read-outs the other —
  contravariant and covariant, exactly the indices the physicist already
  writes. Bra/ket duality cited as the same structure.
- CITES: Grassmann 1844 (extension theory); Ricci & Levi-Civita 1901 (the
  absolute differential calculus — the covariant/contravariant calculus
  itself); Dirac 1930 (Principles — duality in the physicist's own house).

### Ch 4 — The Machine (tensors and forms)
- OPENS WITH: the machine-with-slots description, cited verbatim in spirit:
  a tensor is a linear machine — insert vectors and covectors, read out a
  number (Misner–Thorne–Wheeler's pedagogy, which the reader may already own).
- CONSTRUCTS: multilinear maps; tensor fields; the original physical tensor —
  Cauchy's stress tensor (1822) — as the reason the word exists; antisymmetry
  and differential forms; the exterior derivative; the generalized Stokes
  theorem as "the boundary reads the interior."
- CITES: MTW 1973 (Gravitation — machines with slots); Cauchy 1822 (stress);
  Cartan 1899 (forms, exterior derivative); the Stokes lineage as standardly
  attributed (Kelvin–Stokes; Poincaré; Cartan's general form).
- SEED, marked as DEBT: the stress tensor is Navier–Stokes' native object —
  named here as the owed face, one sentence, fenced (the founding text's own
  promise; the fluid construction is NOT performed in this volume).

### Ch 5 — The Comparison (connections)
- OPENS WITH: two neighboring labs each hold an arrow; are they holding "the
  same" arrow? On curved ground there is no free answer — a RULE must be
  chosen for carrying arrows from bench to bench.
- CONSTRUCTS: parallel transport as the chosen rule; the covariant derivative;
  Christoffel symbols as the rule's coordinates; why the rule is extra
  structure (not derivable from the manifold alone).
- CITES: Christoffel 1869 (the symbols); Levi-Civita 1917 (parallel
  transport); Cartan 1923 (connections in general); Koszul via the standard
  texts.

### Ch 6 — The Loop That Fails to Close (curvature)
- OPENS WITH: carry the arrow around a small loop under the chosen rule; on
  curved ground it comes back TURNED. The turning per unit loop is a tensor.
- CONSTRUCTS: holonomy; the Riemann curvature tensor as the commutator of
  covariant derivatives; its symmetries; contractions (Ricci, scalar).
- CITES: Riemann 1854/1861; the commutator formulation via Ricci &
  Levi-Civita 1901; MTW's loop pedagogy (cited as the physical description).
- LENS (fenced, illustration only): an instrument whose repeated
  self-description leaves a residue that refuses to vanish exhibits the same
  SHAPE — a loop with a nonzero return. Illustration, not identity; one
  sentence; the apparatus already cited.

### Ch 7 — The Ruler (the metric)
- OPENS WITH: until now, no lengths — the whole construction stood without a
  ruler (the reader should feel the shock: curvature needed no metric).
  Now add the ruler: an inner product smoothly chosen at each point.
- CONSTRUCTS: Riemannian (and Lorentzian, one paragraph) metrics; the
  fundamental theorem — exactly one torsion-free rule of comparison is
  compatible with the ruler (the Levi-Civita connection); geodesics;
  distance as infimum; how the metric turns topology's neighborhoods into
  geometry's balls.
- CITES: Riemann 1854; Levi-Civita 1917 + the fundamental theorem via the
  standard texts (do Carmo; Lee, Riemannian Manifolds).

### Ch 8 — The Two Faces at the Boundary (the assembled apparatus reads physics)
- OPENS WITH: the constructed language now READS the two great descriptions:
  Einstein 1915 written in the covariant face (curvature = stress-energy),
  Dirac 1930 written in the contravariant face (states and their duals).
- SHOWS (all cited, no originals): the field equation as a sentence in the
  Ch 1–7 language; the quantum state-space as a sentence in the Ch 3 language;
  Madelung 1927 — the Schrödinger equation rewritten exactly as fluid
  equations — as the cited bridge standing nearest the owed face.
- FENCES (the founding program, named as promise): the sacred text's own
  sentence — the covariance of the one description and the contravariance of
  the other do not settle at the boundary — is stated AS the founding
  program's promise, with its own self-fence (zero-energy case), NOT as a
  theorem this or any volume has proved. Navier–Stokes marked owed. The
  boundary is the door to the later volumes; the book ends at the door.
- CITES: Einstein 1915; Dirac 1930; Madelung 1927; the founding text cited
  once as apparatus.

### Ch 9 — The Ledgers (back matter)
- The citation ledger: EVERY claim's name-and-date, chapter by chapter — the
  spine of the volume (Kodo's second eyes accepted here).
- The physical-descriptions ledger: the descriptions borrowed as openings
  (velocity, stress, machines-with-slots, loops, rulers) each credited to its
  source tradition.
- The face-grade ledger: the four math faces with their honest grades and the
  one owed physics face, as graded 2026-07-25 — carried / carried / carried /
  carried / owed.

## Build plan (per the operator's "build the outline, then build the pdf")

1. This outline → Kodo's gate (structure + citation-law conformance) →
   Beastmaster's architecture pass (whole-arc + the fences).
2. On outline convergence: chapters drafted in order, one Kodo gate per
   chapter (the per-claim citation test applied at gate time).
3. Whole-book pass by Beastmaster; pdflatex build; the PDF is the deliverable.
   The public copy is a SEPARATE decision held for the operator's word.

## Open questions for the gates (flag now, not later)

- Chapter count 9 mirrors Vol 1; if the gates prefer the construction split
  differently (e.g., forms and Stokes as their own chapter), the arc bends
  without breaking.
- Whether Ch 8's Lorentzian paragraph stays (it is one cited paragraph; the
  volume's spine is Riemannian) — gates' call.
- The two LENS exhibits (Ch 1, Ch 6) are the only device appearances beyond
  the single apparatus citation — confirm that count is the right dose.
