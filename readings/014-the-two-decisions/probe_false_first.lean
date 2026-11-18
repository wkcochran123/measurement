import Measurement.Episode12
open Lean Elab Term Meta Measurement readers_experience readers_interpretation_of_the_experience
-- Experiment 014, the two decisions.  The timer is in the code.  One evaluation: the device's root for a decision,
-- `you_re_a_daisy_if_you_do (bitFACT decision)`, elaborated and reduced to weak head normal form.  First one evaluation
-- of a blank, read and set aside; then the decision false, once and a thousand times; then the decision true, once and
-- a thousand times.  All in one compile.
def evaluated (term : TSyntax `term) (times : Nat) : TermElabM (Nat × Nat) := do
  let before ← IO.monoNanosNow
  let (_, beats) ← withHeartbeats do
    for _ in [0:times] do
      let e ← elabTerm term none; let _ ← whnf e; pure ()
  let after ← IO.monoNanosNow
  pure (beats, after - before)
elab "the_two_decisions" : command => do
  Command.liftTermElabM do
    let (beats, nanoseconds) ← evaluated (← `(you_re_a_daisy_if_you_do FACT.Truth)) 1
    logInfo m!"READ order=false_first decision=blank evaluations=1 beats={beats} nanoseconds={nanoseconds}"
    for (name, term) in [("false", ← `(you_re_a_daisy_if_you_do (bitFACT false))), ("true", ← `(you_re_a_daisy_if_you_do (bitFACT true)))] do
      for times in [1, 1000] do
        let (beats, nanoseconds) ← evaluated term times
        logInfo m!"READ order=false_first decision={name} evaluations={times} beats={beats} nanoseconds={nanoseconds}"
the_two_decisions
