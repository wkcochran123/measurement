import Measurement.Episode08
open Lean Elab Term Meta Measurement
-- Experiment 009c, the clock and the quarter.  Eight ticks: a true that is not the device's truth, a false, turn about.
def the_true_built_plainly : FACT := { truth := True, click := .isTrue trivial }
def the_false_built_plainly : FACT := { truth := False, click := .isFalse id }
-- What is under a card: the fact its quarter stands on.
def what_is_under (card : CarrierProcess FACT) : FACT :=
  match card.quarter with
  | .zero fact  => fact
  | .one fact _ => fact
-- Three cards.  Every one shows the same face.  The quarter is under one.
def card_a : CarrierProcess FACT := { symbol := the_true_built_plainly, quarter := Number.zero the_false_built_plainly }
def card_b : CarrierProcess FACT := { symbol := the_true_built_plainly, quarter := Number.zero FACT.Truth }
def card_c : CarrierProcess FACT := { symbol := the_true_built_plainly, quarter := Number.zero the_true_built_plainly }
elab "read_the_meter" : command => do
  Command.liftTermElabM do
    let mut out := ""
    let (_, hb) ← withHeartbeats (pure ())
    out := out ++ s!"BLANK 0 {hb}\n"
    let (beat, blank) ← the_ekg_reads (← `((the_true_built_plainly).click))
    out := out ++ s!"READ 0 T1 {beat} {blank}\n"
    let (beat, blank) ← the_ekg_reads (← `((the_false_built_plainly).click))
    out := out ++ s!"READ 1 F0 {beat} {blank}\n"
    let (beat, blank) ← the_ekg_reads (← `((the_true_built_plainly).click))
    out := out ++ s!"READ 2 T1 {beat} {blank}\n"
    let (beat, blank) ← the_ekg_reads (← `((the_false_built_plainly).click))
    out := out ++ s!"READ 3 F0 {beat} {blank}\n"
    let (beat, blank) ← the_ekg_reads (← `((the_true_built_plainly).click))
    out := out ++ s!"READ 4 T1 {beat} {blank}\n"
    let (beat, blank) ← the_ekg_reads (← `((the_false_built_plainly).click))
    out := out ++ s!"READ 5 F0 {beat} {blank}\n"
    let (beat, blank) ← the_ekg_reads (← `((the_true_built_plainly).click))
    out := out ++ s!"READ 6 T1 {beat} {blank}\n"
    let (beat, blank) ← the_ekg_reads (← `((the_false_built_plainly).click))
    out := out ++ s!"READ 7 F0 {beat} {blank}\n"
    logInfo out
read_the_meter
