/-
# Ep3Implicits — Computation and ChaitinsNumberSequence, proved out (batch 3)

(operator-gated, 2026-08-13: "finish proving out … implicits from episode1 ->
(but not including) Abstraction. DO NOT IMPLEMENT ABSTRACTION for JAR.")

Batch 3 of the pre-Abstraction implicits. Stratum fence held by the
elaborator: imports `Measurement.Episode3` and nothing else — Abstraction
(Ep5:359) unreachable, sacred text untouched, Jar unreferenced. Proofs are
rfl / trivial / Iff.rfl / nomatch; expected census: every theorem axiom-free.

THE LAWS (and this rung's two inversions):

COMPUTATION:
* FACT-BLIND at the program rung: program/program compares the carried
  Studies only — the head Facts are never consulted.
* Program is covariant with compute ("comes after"): a program sits below
  any compute, unconditionally.
* THE REVERSE-ENGINEERING WALL: a compute NEVER sits below a program — the
  arm is literally `true = false`. Decomposition is contravariant;
  "reverse engineering is hard" is now a theorem.
* HEAD-BLIND at the compute rung — the inversion: compute/compute reads
  ONLY the recursive tails (`le c₁ c₂`); the head payloads (fact and both
  Studies) are never consulted. Every other carrier on the ladder is
  tail-blind; Computation's top arm is exactly the opposite — "Recurse!
  Eventually we will find a computation that has completed."

CHAITINSNUMBERSEQUENCE — the heavyweight:
* halting/halting and nonhalting/nonhalting both compare the carried
  Computations (fact-blind again).
* Halting sits below nonhalting, unconditionally.
* THE NONHALTING WALL: a nonhalting NEVER sits below any halting — the arm
  is the Bool `false`. Once past the halting boundary, nothing brings a
  record back beneath a halted one: the order itself encodes
  halting-status dominance.
* OPTION-BLIND: the nonhalting arm never consults its `Option` tail.
* And the law that is an ABSENCE: this is the one carrier on the ladder
  with NO `lt` — the source: "Can't compute lt. Against the rules." The
  order exists; strictness does not. You can bound Chaitin's number ever
  closer by spending TIME; you can never strictly separate — the
  Berry/Chaitin fence written into the order's own signature. (An absence
  cannot be a theorem in this file; it is recorded here and checkable by
  grep: `Measurement.ChaitinsNumberSequence.lt` does not exist.)
-/
import Measurement.Episode3

namespace Measurement.Ep3Implicits

open Measurement

-- ═════════════════════════ COMPUTATION ════════════════════════════

/-- FACT-BLIND: program/program compares the carried Studies only; the head
Facts never enter the comparison. -/
theorem computation_program_fork (f₁ f₂ : Fact) (s₁ s₂ : Study) :
    Computation.le (.program f₁ s₁) (.program f₂ s₂) ↔ s₁ ≤ s₂ := Iff.rfl

/-- Program is covariant with compute: a program sits below any compute,
unconditionally ("comes after"). -/
theorem computation_program_below_compute (f : Fact) (s : Study) (g : Fact)
    (a b : Study) (c : Computation) :
    Computation.le (.program f s) (.compute g a b c) := rfl

/-- THE REVERSE-ENGINEERING WALL: a compute never sits below a program —
the arm is literally `true = false`. Decomposition is contravariant. -/
theorem computation_reverse_engineering_wall (g : Fact) (a b : Study)
    (c : Computation) (f : Fact) (s : Study) :
    ¬ Computation.le (.compute g a b c) (.program f s) := fun h => nomatch h

/-- HEAD-BLIND — the ladder's inversion: compute/compute reads ONLY the
recursive tails; the head fact and both Study payloads are never consulted.
(Every other carrier is tail-blind; this arm is the opposite.) -/
theorem computation_compute_head_blind (f₁ f₂ : Fact) (a₁ a₂ b₁ b₂ : Study)
    (c₁ c₂ : Computation) :
    Computation.le (.compute f₁ a₁ b₁ c₁) (.compute f₂ a₂ b₂ c₂)
      ↔ Computation.le c₁ c₂ := Iff.rfl

/-- The same law read as invariance: swap every head payload on both sides
and the comparison is untouched. -/
theorem computation_head_swap_invariant (f₁ f₂ g₁ g₂ : Fact)
    (a₁ a₂ b₁ b₂ x₁ x₂ y₁ y₂ : Study) (c₁ c₂ : Computation) :
    Computation.le (.compute f₁ a₁ b₁ c₁) (.compute f₂ a₂ b₂ c₂)
      ↔ Computation.le (.compute g₁ x₁ y₁ c₁) (.compute g₂ x₂ y₂ c₂) := Iff.rfl

-- ═════════════════ CHAITINSNUMBERSEQUENCE ═════════════════════════

/-- Halting/halting compares the carried Computations (fact-blind). -/
theorem chaitin_halting_fork (f₁ f₂ : Fact) (c₁ c₂ : Computation) :
    ChaitinsNumberSequence.le (.halting f₁ c₁) (.halting f₂ c₂) ↔ c₁ ≤ c₂ :=
  Iff.rfl

/-- Halting sits below nonhalting, unconditionally. -/
theorem chaitin_halting_below_nonhalting (f : Fact) (c : Computation) (g : Fact)
    (d : Computation) (o : Option ChaitinsNumberSequence) :
    ChaitinsNumberSequence.le (.halting f c) (.nonhalting g d o) := rfl

/-- THE NONHALTING WALL: a nonhalting never sits below any halting — the
arm is the Bool `false`. Past the halting boundary, nothing comes back
beneath a halted record: halting-status dominance, in the order itself. -/
theorem chaitin_nonhalting_wall (f : Fact) (c : Computation)
    (o : Option ChaitinsNumberSequence) (g : Fact) (d : Computation) :
    ¬ ChaitinsNumberSequence.le (.nonhalting f c o) (.halting g d) :=
  fun h => nomatch h

/-- Nonhalting/nonhalting compares the carried Computations. -/
theorem chaitin_nonhalting_fork (f₁ f₂ : Fact) (c₁ c₂ : Computation)
    (o₁ o₂ : Option ChaitinsNumberSequence) :
    ChaitinsNumberSequence.le (.nonhalting f₁ c₁ o₁) (.nonhalting f₂ c₂ o₂)
      ↔ c₁ ≤ c₂ := Iff.rfl

/-- OPTION-BLIND: the nonhalting comparison never consults its Option tail. -/
theorem chaitin_option_blind (f₁ f₂ : Fact) (c₁ c₂ : Computation)
    (o₁ o₂ p₁ p₂ : Option ChaitinsNumberSequence) :
    ChaitinsNumberSequence.le (.nonhalting f₁ c₁ o₁) (.nonhalting f₂ c₂ o₂)
      ↔ ChaitinsNumberSequence.le (.nonhalting f₁ c₁ p₁) (.nonhalting f₂ c₂ p₂) :=
  Iff.rfl

end Measurement.Ep3Implicits
