import Measurement.TwoDescriptions
import Lean.Util.Heartbeats
import Lean.Elab.Command

/-! # SelfApplication — PLAN_RFC §3a: the application of QED to itself (BLIND probe)

The echo (`two_descriptions`) says the two descriptions are the same in TYPE.  This weighs them
in COST: the deterministic elaboration heartbeats the checker spends on each.  "Elaboration times
are the same up to calibration" (the ×1000 `rank ≡ heartbeat` connection).  The elaborator weighing
its own elaboration = the electron's self-energy; the calibrated residual is where α lives.

BLIND: no target, no 137, no bracket enters this reading.  Measure, report the raw numbers, aim at
nothing.  Model: `AlphaFoldProbe.register_cost` (16+, mine; out of the Ep1–15 cache).
-/

namespace Measurement.SelfApplication
open Lean Measurement.TwoDescriptions

/-- The ×1000 calibration constant (the `rank ≡ heartbeat / 1000` connection, 0b). Restated locally
so this file stays self-contained on sacred. -/
def heartbeatCoefficient : Nat := 1000

/-- Measure a term's elaboration heartbeats, emit as a `Nat` def (model: `AlphaFoldProbe`). -/
elab "register_cost" name:ident " => " t:term : command => do
  let hb ← Lean.Elab.Command.liftTermElabM do
    let (_, hb) ← Lean.withHeartbeats do
      let e ← Lean.Elab.Term.elabTerm t none
      let _ ← Lean.Meta.whnf e
      pure ()
    pure hb
  let cmd ← `(def $name:ident : Nat := $(Lean.quote hb))
  Lean.Elab.Command.elabCommand cmd

-- Warmup-discard (Episode23 convention): measure each twice, take the second (post-warmup, stable).
register_cost orbit_w => (electron_in_orbit)
register_cost orbit   => (electron_in_orbit)
register_cost pair_w  => (anti_cooper_pair)
register_cost pair    => (anti_cooper_pair)
register_cost echo_w  => (two_descriptions)
register_cost echo    => (two_descriptions)

-- ── RAW run-log (report every number, blind) ──
#eval (orbit, pair, echo)

-- The two DESCRIPTIONS, weighed: do they cost the same? (the echo, at the level of cost)
def descriptions_residual : Int := (orbit : Int) - pair
#eval descriptions_residual

-- The SELF-APPLICATION residual: the proof (QED applied to itself) over the description it proves.
def self_residual : Int := (echo : Int) - orbit
#eval self_residual

-- Calibrated (÷1000, the connection) — the reading in rank units:
#eval ((descriptions_residual / heartbeatCoefficient), (self_residual / heartbeatCoefficient))

end Measurement.SelfApplication
