/-
A language of readers, for the review of Episode 13's recovery theorem.

This file is not part of the device.  It is imported by nothing in `Measurement`, it is built apart
(`lake build Experiments.ReaderLanguage`), and its one inductive is in the namespace `Review`, so the census
the device takes of its own inductives does not see it.  The specification is a reviewer's (GPT, 18 November
2026): write down exactly what a reader of the retained evidence may do, and show that every such reader
returns the same on the two decisions.
-/
import Measurement.Episode13

namespace Review
open Measurement

/-- A reader expression: what is handed in, and what is returned.  It is handed one value of the evidence and
nothing else: no decision, no parity, no left-out part of the root, no name of a declaration, no clock. -/
inductive Reader : Type → Type → Type 1
  /-- Return what was handed in. -/
  | input {Evidence : Type} : Reader Evidence Evidence
  /-- Return a fixed thing.  A convention may sit here; it is the same on every case. -/
  | constant {Evidence Returned : Type} (fixed : Returned) : Reader Evidence Returned
  /-- Apply a fixed total function to what another reader returns.  Any function, computable or not. -/
  | apply {Evidence Middle Returned : Type} (function : Middle → Returned) (reader : Reader Evidence Middle) :
      Reader Evidence Returned
  /-- Return what two readers return, together. -/
  | pair {Evidence First Second : Type} (first : Reader Evidence First) (second : Reader Evidence Second) :
      Reader Evidence (First × Second)
  /-- Read a coin, then return what the reader it selects returns. -/
  | branch {Evidence Returned : Type} (coin : Reader Evidence Bool) (on_true on_false : Reader Evidence Returned) :
      Reader Evidence Returned
  /-- Read a count, read a start, and take a step that many times; the step is handed the evidence and the state. -/
  | iterate {Evidence Returned : Type} (count : Reader Evidence Nat) (start : Reader Evidence Returned)
      (step : Reader (Evidence × Returned) Returned) : Reader Evidence Returned

/-- A step taken a number of times. -/
def taken (step : Returned → Returned) : Nat → Returned → Returned
  | 0, state => state
  | times + 1, state => taken step times (step state)

/-- What a reader returns on what it is handed. -/
def Reader.returns : {Evidence Returned : Type} → Reader Evidence Returned → Evidence → Returned
  | _, _, .input, evidence => evidence
  | _, _, .constant fixed, _ => fixed
  | _, _, .apply function reader, evidence => function (reader.returns evidence)
  | _, _, .pair first second, evidence => (first.returns evidence, second.returns evidence)
  | _, _, .branch coin on_true on_false, evidence =>
      if coin.returns evidence then on_true.returns evidence else on_false.returns evidence
  | _, _, .iterate count start step, evidence =>
      taken (fun state => step.returns (evidence, state)) (count.returns evidence) (start.returns evidence)

/-- Handed the same, a reader returns the same.  No induction is needed for this: a reader's return is a
function of what it is handed, and a function takes equals to equals.  The language adds nothing to the
obstruction; it says what the readers are. -/
theorem handed_the_same_a_reader_returns_the_same {Evidence Returned : Type} (reader : Reader Evidence Returned)
    (this that : Evidence) (the_same : this = that) : reader.returns this = reader.returns that := by
  subst the_same; rfl

/-- The same, case by case through the language, as the review asked: each constructor is taken in turn, and
the iteration by induction on its count.  It proves no more than the theorem above. -/
theorem handed_the_same_step_by_step :
    ∀ {Evidence Returned : Type} (reader : Reader Evidence Returned) (this that : Evidence),
      this = that → reader.returns this = reader.returns that
  | _, _, .input, _, _, same => same
  | _, _, .constant _, _, _, _ => rfl
  | _, _, .apply function reader, this, that, same =>
      congrArg function (handed_the_same_step_by_step reader this that same)
  | _, _, .pair first second, this, that, same => by
      show (first.returns this, second.returns this) = (first.returns that, second.returns that)
      rw [handed_the_same_step_by_step first this that same, handed_the_same_step_by_step second this that same]
  | _, _, .branch coin on_true on_false, this, that, same => by
      show (if coin.returns this then on_true.returns this else on_false.returns this)
          = (if coin.returns that then on_true.returns that else on_false.returns that)
      rw [handed_the_same_step_by_step coin this that same, handed_the_same_step_by_step on_true this that same,
        handed_the_same_step_by_step on_false this that same]
  | _, _, .iterate count start step, this, that, same => by
      show taken (fun state => step.returns (this, state)) (count.returns this) (start.returns this)
          = taken (fun state => step.returns (that, state)) (count.returns that) (start.returns that)
      have steps_agree : (fun state => step.returns (this, state)) = (fun state => step.returns (that, state)) :=
        funext fun state => handed_the_same_step_by_step step (this, state) (that, state) (by rw [same])
      rw [handed_the_same_step_by_step count this that same, handed_the_same_step_by_step start this that same,
        steps_agree]

/-- The language is exactly the functions of what is handed in: every function is a reader, and every reader is
a function.  So it describes the readers of this evidence.  It does not show that this evidence is all that an
account of the device may look at. -/
theorem every_function_of_the_evidence_is_a_reader {Evidence Returned : Type} (function : Evidence → Returned) :
    ∃ reader : Reader Evidence Returned, ∀ evidence, reader.returns evidence = function evidence :=
  ⟨.apply function .input, fun _ => rfl⟩

/-- On the two decisions.  Every reader of what is kept of a decision returns the same for the one decision as
for the other. -/
theorem every_reader_returns_the_same_on_the_two_decisions {Returned : Type}
    (reader : Reader (Basis × Bool × (Int × Int) × Int) Returned) :
    reader.returns (what_is_kept_of_a_decision true) = reader.returns (what_is_kept_of_a_decision false) :=
  handed_the_same_a_reader_returns_the_same reader _ _ the_same_is_kept_of_both_decisions

/-- So no reader that returns a coin returns the decision in both cases. -/
theorem no_reader_returns_the_decision :
    ¬ ∃ reader : Reader (Basis × Bool × (Int × Int) × Int) Bool,
        reader.returns (what_is_kept_of_a_decision true) = true
          ∧ reader.returns (what_is_kept_of_a_decision false) = false := by
  intro ⟨reader, on_true, on_false⟩
  have same := every_reader_returns_the_same_on_the_two_decisions reader
  rw [on_true, on_false] at same
  exact Bool.noConfusion same

end Review

#print axioms Review.handed_the_same_a_reader_returns_the_same
#print axioms Review.handed_the_same_step_by_step
#print axioms Review.every_function_of_the_evidence_is_a_reader
#print axioms Review.every_reader_returns_the_same_on_the_two_decisions
#print axioms Review.no_reader_returns_the_decision
