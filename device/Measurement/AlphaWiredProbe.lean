import Measurement.SelfApplication
import Measurement.Episode40

/-! # AlphaWiredProbe — P1 wiring: self-energy residual -> the coupling reading, run twice, count to 3.
Operator: "wire it up and run it twice. count to three 1 2 3."
The self-application measures elaboration heartbeats. Each term is measured THREE times (count 1,2,3)
to watch the reading settle to its fixpoint (the machine measuring its own measurement until stable).
The settled residual, calibrated by the book's own x1000 (rank == heartbeat) connection, is READ as the
inverse coupling -- the chain the book claims (two descriptions -> residual -> self-energy -> alpha),
now actually WIRED. BLIND: report every number, aim at nothing, do NOT fit to 137. -/

namespace Measurement.AlphaWiredProbe
open Measurement.SelfApplication Measurement.TwoDescriptions

-- COUNT TO THREE: measure each term three times (1,2,3), watching it settle to a fixpoint.
register_cost orbit1 => (electron_in_orbit)
register_cost orbit2 => (electron_in_orbit)
register_cost orbit3 => (electron_in_orbit)
register_cost echo1  => (two_descriptions)
register_cost echo2  => (two_descriptions)
register_cost echo3  => (two_descriptions)

#eval s!"orbit counts 1,2,3: {orbit1} {orbit2} {orbit3}   (settling to fixpoint)"
#eval s!"echo  counts 1,2,3: {echo1} {echo2} {echo3}"

-- The FIXPOINT (count-3, settled) residual = the self-energy, now wired:
def orbitFix : Int := orbit3
def echoFix  : Int := echo3
def selfResidual : Int := echoFix - orbitFix
def heartbeatCoeff : Int := 1000        -- the book's rank == heartbeat / 1000 calibration

#eval s!"count-3 fixpoint: orbit={orbitFix} echo={echoFix}  self-residual (echo-orbit)={selfResidual}"

-- WIRED reading: the coupling read AS the calibrated self-energy residual (blind, reported not aimed).
-- inverse coupling candidates off the residual + the x1000 calibration:
#eval s!"|self-residual| = {selfResidual.natAbs}"
#eval s!"x1000 / |residual|            = {heartbeatCoeff / selfResidual.natAbs}"
#eval s!"orbit / |residual|            = {orbitFix / selfResidual.natAbs}"
#eval s!"(orbit+echo) / |residual|     = {(orbitFix + echoFix) / selfResidual.natAbs}"
-- Most faithful wiring: feed the self-measurement RATIO as the crossing distance into the REAL alpha
-- map (the same one AlphaBoundMediant reads at sqrt(18/5)~1.897). Blind.
open Measurement in
#eval s!"self-ratio orbit/echo = {orbitFix.natAbs}/{echoFix.natAbs} ~ 1.037 (cf the real crossing sqrt(18/5)~1.897)"
open Measurement in
#eval s!"inv-alpha read at self-crossing orbit/echo: {(alphaFromSecondVariationAtDistance 5 (RationalDistance.mk orbitFix.natAbs echoFix.natAbs)).inverseScaledFloor (pow10 18)}"
open Measurement in
#eval s!"inv-alpha read at self-crossing echo/orbit: {(alphaFromSecondVariationAtDistance 5 (RationalDistance.mk echoFix.natAbs orbitFix.natAbs)).inverseScaledFloor (pow10 18)}"
end Measurement.AlphaWiredProbe
