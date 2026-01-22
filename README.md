# Measurement

Version 0.1.1
[Latest pdf build.](https://drive.google.com/file/d/1t8qZYaYHa_-4-A0Hfjk-5ZqHwnuflh8H/view?usp=drive_link)


This repository contains a developing axiomatic framework for measurement,
events, and refinement, together with a Lean 4 formalization of the early
chapters.

The project is intentionally split between two modes:

1. **Human-readable mathematical exposition**, and
2. **Machine-verified formal statements** in Lean.

Up through **Chapter 2**, these two views coincide. From that point onward,
the manuscript emphasizes the *shape* and consequences of the argument rather
than full formal rigor.


## Current status

- **Chapter 1**  
  Human-readable and accompanied by working Lean code.  Pretty big
  refactor, but the types are now ready to scale.

- **Chapter 2**
  Mostly readable.  Substantial work left on the Lean.

- **Chapter 3 and beyond**  
  The text gives more of a shape of the argument as the prose and rigor lack
  formality.  Read past chapter 2 at your own peril.  Chapter 3 is currently
  under development.

---

## Lean Code Organization

The Lean formalization mirrors the structure of the manuscript as closely as
possible, with an emphasis on traceability between the text and the code.

### Definitions

Each definition introduced in the book appears **once and in order** in a
corresponding `Definitions.lean` file. This enforces a single source of truth
for concepts and preserves the narrative dependency structure of the text.
Later chapters may *use* these definitions, but never redefine them.

### Axioms and ZFC

Axioms are separated from definitions to make the logical commitments explicit.

- `Chapter2/ZFC.lean` contains axioms inherited from or aligned with ZFC-style
  foundations.
- `Chapter2/Axioms.lean` contains the additional axioms of measurement
  introduced by the book.

This separation makes it clear which assumptions are foundational and which are
specific to the measurement framework, and allows the latter to be varied or
examined independently.

### Constructions

Each chapter may introduce *constructions*: derived objects, operators, or
interfaces built from concepts defined in earlier chapters. These live in
`Constructions.lean` files and contain no new axioms. Constructions exist to
make later arguments expressible, not to extend the theory.

### Propositions

The propositions stated in each chapter of the book are formalized and proved
in the corresponding `Propositions.lean` file. These proofs depend only on:

- earlier definitions,
- stated axioms,
- and constructions already introduced.

This organization ensures that every proposition can be traced directly back
to its assumptions, and that the Lean code follows the same logical progression
as the manuscript.

