import Measurement.Meanwhile22
import Lean.Util.Heartbeats
import Lean.Elab.Command

/- MEANWHILE 23 -- PREDICT THE PULSE. Meanwhile22 REPORTS the heart rate; this
file PREDICTS it from parts and names the residual the binding energy. Everything
here is MEASURED, never proved: raw heartbeat reads off the elaborator's own
counter. THE PROTOCOL (operator-amended Gate 0): a pulse is measured three times
in the same file as three separate commands; the first read is a one-time warmup
and is DISCARDED; the pulse is the second read, verified stable against the third
(within one heartbeat). Cross-command warmup was found empirically ([1618,1602,1602,1602,
1603], 5x driver.phase): the first measurement forces a shared subterm the rest
reuse, and the intrinsic cost is the stable post-warmup value. -/

namespace Measurement

-- The parametric generalization of Meanwhile22's register_heart_rate: measure any
-- term's whnf cost and emit it as a def. Same liftTermElabM / withHeartbeats /
-- elabTerm+whnf / quote-emit shape; name and term are arguments.
elab "register_heart_rate_as" name:ident term:term : command => do
  let hb ← Lean.Elab.Command.liftTermElabM do
    let (_, hb) ← Lean.withHeartbeats do
      let e ← Lean.Elab.Term.elabTerm term none
      let _ ← Lean.Meta.whnf e
      pure ()
    pure hb
  let cmd ← `(def $name:ident : Nat := $(Lean.quote hb))
  Lean.Elab.Command.elabCommand cmd

-- ---------------------------------------------------------------------------
-- GATE 0-AMENDED -- the null control, warmup-discard + stability.
-- Three reads of the SAME needle (driver.phase, the M22 concrete driver);
-- discard read 1 (warmup), take read 2, verify read2 == read3 (+/-1).
-- ---------------------------------------------------------------------------
register_heart_rate_as g0_warmup (driver.phase)
register_heart_rate_as g0_r2 (driver.phase)
register_heart_rate_as g0_r3 (driver.phase)

#eval g0_warmup                                                    -- discarded warmup
#eval g0_r2                                                        -- the pulse
#eval g0_r3                                                        -- stability check
-- the regime verdict: read2 and read3 agree within +/-1
#eval (decide (g0_r2 = g0_r3 ∨ g0_r2 + 1 = g0_r3 ∨ g0_r3 + 1 = g0_r2) : Bool)

-- ---------------------------------------------------------------------------
-- GATE 1 -- the ladder of needles, over bracket B1 (operator turn 750).
-- Four pulses, each warmup-discarded; telescopic DIFFERENCES, not sums.
-- ---------------------------------------------------------------------------
def B1 : BracketedNumber :=
  { lower := .one Fact.Truth (.one Fact.Truth (.zero Fact.Truth))
    upper := .zero Fact.Truth
    value := .one Fact.Truth (.zero Fact.Truth) }

-- basePulse: the bare literal
register_heart_rate_as base_warmup (QPhase.plus)
register_heart_rate_as base_r2 (QPhase.plus)
register_heart_rate_as base_r3 (QPhase.plus)

-- projectionPulse: the record projection (faces assembled, then .phase read)
register_heart_rate_as proj_warmup (({ charge := .one Fact.Truth (.one Fact.Truth (.zero Fact.Truth)), mass := .zero Fact.Truth, phase := QPhase.plus } : RecoveredObservables).phase)
register_heart_rate_as proj_r2 (({ charge := .one Fact.Truth (.one Fact.Truth (.zero Fact.Truth)), mass := .zero Fact.Truth, phase := QPhase.plus } : RecoveredObservables).phase)
register_heart_rate_as proj_r3 (({ charge := .one Fact.Truth (.one Fact.Truth (.zero Fact.Truth)), mass := .zero Fact.Truth, phase := QPhase.plus } : RecoveredObservables).phase)

-- recoverPulse: the full recover, then .phase
register_heart_rate_as recov_warmup ((recover B1 Fact.Truth).phase)
register_heart_rate_as recov_r2 ((recover B1 Fact.Truth).phase)
register_heart_rate_as recov_r3 ((recover B1 Fact.Truth).phase)

-- phaseDecisionPulse: the isolated decision
register_heart_rate_as dec_warmup (phaseRead Fact.Truth)
register_heart_rate_as dec_r2 (phaseRead Fact.Truth)
register_heart_rate_as dec_r3 (phaseRead Fact.Truth)

-- raw triples (report all)
#eval (base_warmup, base_r2, base_r3)
#eval (proj_warmup, proj_r2, proj_r3)
#eval (recov_warmup, recov_r2, recov_r3)
#eval (dec_warmup, dec_r2, dec_r3)

-- taken values (read 2), lifted to Int for signed deltas
def basePulse          : Int := (base_r2  : Int)
def projectionPulse    : Int := (proj_r2  : Int)
def recoverPulse       : Int := (recov_r2 : Int)
def phaseDecisionPulse : Int := (dec_r2   : Int)

-- telescopic deltas (differences, never sums-of-absolutes)
def projectionDelta : Int := projectionPulse - basePulse
def recoverDelta    : Int := recoverPulse - projectionPulse
def decisionDelta   : Int := phaseDecisionPulse - basePulse

def predictedHeartRate : Int := basePulse + projectionDelta + recoverDelta + decisionDelta

#eval basePulse
#eval projectionDelta
#eval recoverDelta
#eval decisionDelta
#eval predictedHeartRate

-- ---------------------------------------------------------------------------
-- GATE 2 -- CALIBRATE-B1, PREDICT B2 (the anti-cheat). The B1 deltas above
-- never saw B2, so predictedHeartRate cannot encode B2's answer. Two targets.
-- ---------------------------------------------------------------------------
def B2 : BracketedNumber :=
  { lower := .one Fact.Truth (.zero Fact.Truth)
    upper := .one Fact.Truth (.zero Fact.Truth)
    value := .zero Fact.Truth }

register_heart_rate_as tB2_warmup ((recover B2 Fact.Truth).phase)
register_heart_rate_as tB2_r2 ((recover B2 Fact.Truth).phase)
register_heart_rate_as tB2_r3 ((recover B2 Fact.Truth).phase)

register_heart_rate_as tDrv_warmup ((recover B1 Fact.Truth).phase)
register_heart_rate_as tDrv_r2 ((recover B1 Fact.Truth).phase)
register_heart_rate_as tDrv_r3 ((recover B1 Fact.Truth).phase)

register_heart_rate_as tDef_warmup (driver.phase)
register_heart_rate_as tDef_r2 (driver.phase)
register_heart_rate_as tDef_r3 (driver.phase)

#eval (tB2_warmup, tB2_r2, tB2_r3)
#eval (tDrv_warmup, tDrv_r2, tDrv_r3)
#eval (tDef_warmup, tDef_r2, tDef_r3)

def targetB2        : Int := (tB2_r2  : Int)
def targetDriver    : Int := (tDrv_r2 : Int)
def targetDriverDef : Int := (tDef_r2 : Int)

-- ---------------------------------------------------------------------------
-- GATE 3 -- THE BINDING ENERGY. The residual between a measured target and the
-- prediction assembled from parts. Nonzero = the elaboration's binding energy:
-- the assembled pulse lighter than its measured-apart parts (shared cached
-- subterms), a mass defect -- nucleus lighter than its nucleons. The counter
-- rules; the sign names it.
-- ---------------------------------------------------------------------------
def elabBindingEnergyB2        : Int := targetB2        - predictedHeartRate
def elabBindingEnergyDriver    : Int := targetDriver    - predictedHeartRate
def elabBindingEnergyDriverDef : Int := targetDriverDef - predictedHeartRate

#eval elabBindingEnergyB2
#eval elabBindingEnergyDriver
#eval elabBindingEnergyDriverDef

/- THE RESULT -- a NEGATIVE binding energy. The measured pulse is LIGHTER than
the prediction assembled from separately-measured parts (predicted 3231 vs
measured ~2165 for the recover targets, ~1603 for the def target): assembled,
the faces share the cached phase-decision subterm that measuring them apart
double-counts. The whole costs less than the sum of its parts -- the nucleus
lighter than its nucleons, a mass defect read off the elaborator's own
heartbeat. The anti-cheat holds: B2 was never seen by the B1 deltas, yet its
residual is the same negative binding energy. -/

end Measurement
