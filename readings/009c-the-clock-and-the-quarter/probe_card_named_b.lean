import Measurement.Episode08
open Lean Elab Term Meta Measurement
-- Experiment 009c, the clock and the quarter.  The card b, written out in the term so that what is under it is named: read twice.
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
    let (beat, blank) ← the_ekg_reads (← `((what_is_under ({ symbol := the_true_built_plainly, quarter := Number.zero FACT.Truth } : CarrierProcess FACT)).click))
    out := out ++ s!"READ 1 b {beat} {blank}\n"
    let (beat, blank) ← the_ekg_reads (← `((what_is_under ({ symbol := the_true_built_plainly, quarter := Number.zero FACT.Truth } : CarrierProcess FACT)).click))
    out := out ++ s!"READ 2 b {beat} {blank}\n"
    logInfo out
read_the_meter
