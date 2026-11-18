import Measurement.Episode08
open Lean Elab Term Meta Measurement readers_experience
-- Experiment 011, the throw.  the bent card thrown: Quot.sound, on one statement of Episode 8's box.  Read twice in one process, each beside its blank.
elab "read_the_meter" : command => do
  Command.liftTermElabM do
    let mut out := ""
    let (_, hb) ← withHeartbeats (pure ())
    out := out ++ s!"BLANK 0 {hb}\n"
    let (beat, blank) ← the_ekg_reads (← `((Quot.sound (r := the_rational_idea_of_relativity) (Nat.le_refl (1 * 1)) : (Quot.mk the_rational_idea_of_relativity ((1 : Nat), (1 : Nat)) : Quot the_rational_idea_of_relativity) = Quot.mk the_rational_idea_of_relativity ((1 : Nat), (1 : Nat)))))
    out := out ++ s!"READ 1 sound {beat} {blank}\n"
    let (beat, blank) ← the_ekg_reads (← `((Quot.sound (r := the_rational_idea_of_relativity) (Nat.le_refl (1 * 1)) : (Quot.mk the_rational_idea_of_relativity ((1 : Nat), (1 : Nat)) : Quot the_rational_idea_of_relativity) = Quot.mk the_rational_idea_of_relativity ((1 : Nat), (1 : Nat)))))
    out := out ++ s!"READ 2 sound {beat} {blank}\n"
    logInfo out
read_the_meter
