import Measurement.Meanwhile22
import Measurement.Calibration.EKGBounded
import Lean.Util.Heartbeats
import Lean.Elab.Command

/-! # AlphaFoldProbe — Phase 0c: the BLIND α reading (task `instrument`)

Per pre-reg v2 (Kodo Turn 84 green light). The reading is a fold-cost measurement, read as
**elaboration heartbeats** (the deterministic meta-reading; a metaprogram in 16+, out of the
Ep1–15 cache — Episode3 stays frozen). α is read as the **second difference δ²** (the precession /
curvature = the BFGS secant) of the fold cost, referenced to the **TRUE=TRUE blank** (g−2, δ¹=0 at
the stationary point), swept over the value depth (the loop iterated).

**BLIND: the target 137.035999206 and the value bracket (137, 137.036) do NOT enter this reading.**
This reads the raw number off the intrinsic cost sequence alone. Report whatever it is.
-/

namespace Measurement.AlphaFoldProbe
open Lean Measurement

-- The metaprogram (16+, mine): measure a term's elaboration heartbeats, emit as a def.
-- Model: EKGBounded / Meanwhile23 `register_heart_rate_as`. Does NOT touch Episode3.
elab "register_cost" name:ident " => " t:term : command => do
  let hb ← Lean.Elab.Command.liftTermElabM do
    let (_, hb) ← Lean.withHeartbeats do
      let e ← Lean.Elab.Term.elabTerm t none
      let _ ← Lean.Meta.whnf e
      pure ()
    pure hb
  let cmd ← `(def $name:ident : Nat := $(Lean.quote hb))
  Lean.Elab.Command.elabCommand cmd

-- THE BLANK (TRUE=TRUE, δ¹=0): the reference the reading is differenced from.
register_cost blank => (Fact.Truth.decTruth)

-- THE FOLD at increasing value-depth (the loop iterated): the phase face read off `recover` on a
-- BracketedNumber whose value is a Number of depth k. Warmup-discard convention (Meanwhile23):
-- measure each twice; take the second (post-warmup, stable) read.

register_cost w0 => ((recover { lower := .zero Fact.Truth, upper := .zero Fact.Truth,
                                 value := .zero Fact.Truth } Fact.Truth).phase)
register_cost fold0 => ((recover { lower := .zero Fact.Truth, upper := .zero Fact.Truth,
                                    value := .zero Fact.Truth } Fact.Truth).phase)

register_cost w1 => ((recover { lower := .zero Fact.Truth, upper := .zero Fact.Truth,
                                 value := .one Fact.Truth (.zero Fact.Truth) } Fact.Truth).phase)
register_cost fold1 => ((recover { lower := .zero Fact.Truth, upper := .zero Fact.Truth,
                                    value := .one Fact.Truth (.zero Fact.Truth) } Fact.Truth).phase)

register_cost w2 => ((recover { lower := .zero Fact.Truth, upper := .zero Fact.Truth,
                                 value := .one Fact.Truth (.one Fact.Truth (.zero Fact.Truth)) } Fact.Truth).phase)
register_cost fold2 => ((recover { lower := .zero Fact.Truth, upper := .zero Fact.Truth,
                                    value := .one Fact.Truth (.one Fact.Truth (.zero Fact.Truth)) } Fact.Truth).phase)

register_cost w3 => ((recover { lower := .zero Fact.Truth, upper := .zero Fact.Truth,
                                 value := .one Fact.Truth (.one Fact.Truth (.one Fact.Truth (.zero Fact.Truth))) } Fact.Truth).phase)
register_cost fold3 => ((recover { lower := .zero Fact.Truth, upper := .zero Fact.Truth,
                                    value := .one Fact.Truth (.one Fact.Truth (.one Fact.Truth (.zero Fact.Truth))) } Fact.Truth).phase)

register_cost w4 => ((recover { lower := .zero Fact.Truth, upper := .zero Fact.Truth,
                                 value := .one Fact.Truth (.one Fact.Truth (.one Fact.Truth (.one Fact.Truth (.zero Fact.Truth)))) } Fact.Truth).phase)
register_cost fold4 => ((recover { lower := .zero Fact.Truth, upper := .zero Fact.Truth,
                                    value := .one Fact.Truth (.one Fact.Truth (.one Fact.Truth (.one Fact.Truth (.zero Fact.Truth)))) } Fact.Truth).phase)

-- ── THE RAW RUN-LOG (report every number, in order — not the flattering run) ──
#eval (blank, fold0, fold1, fold2, fold3, fold4)                      -- the blank + the fold-cost sweep

-- δ¹ — the first differences (the "velocity"; on a stationary blank this should be ~flat):
def d1_1 : Int := (fold1 : Int) - fold0
def d1_2 : Int := (fold2 : Int) - fold1
def d1_3 : Int := (fold3 : Int) - fold2
def d1_4 : Int := (fold4 : Int) - fold3
#eval (d1_1, d1_2, d1_3, d1_4)

-- δ² — THE SECOND DIFFERENCE (the precession/curvature = the α candidate, BFGS secant):
def d2_2 : Int := d1_2 - d1_1
def d2_3 : Int := d1_3 - d1_2
def d2_4 : Int := d1_4 - d1_3
#eval (d2_2, d2_3, d2_4)                                              -- the curvature per level (raw)

-- blank-referenced (g−2): the δ² as a fraction of the blank (the dimensionless read, ×10^6 to see it):
#eval (((d2_2 * 1000000) / (blank : Int)), ((d2_3 * 1000000) / (blank : Int)), ((d2_4 * 1000000) / (blank : Int)))

end Measurement.AlphaFoldProbe
