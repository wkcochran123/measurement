/-
Measurement.Calibration.EKGBounded

Elaboration-time EKG: a local bounded-attempt circuit breaker, kept in its OWN
module so that importing it does not invalidate the Episode 1-15 build cache
(LeanCalibration is upstream of the whole episode chain; this is not).

`Calibration.EKG.outgrown?` (in LeanCalibration) is the term-level reading.
`tryBounded?` / `ekg_probe` here are its elaboration-time analog, modeled on
`Lean.Meta.Tactic.Grind.Canon.isDefEqBounded`.

The paradigm is Embarrassingly Serial Subjunctive Metaprogramming: the device
walks a serial grammar, asks a subjunctive question of each clause (the `?`
predicates), and MEASURES whether the bounded evaluation closes. The EKG bounds
one such step. Budget for one clause: 9 (cost to do a Fact) * 8 (the 2^3
assignments of a 3SAT clause) * 10 (safety) = 720 user-heartbeats, i.e.
720000 internal compiler heartbeats.
-/
import Lean.Util.Heartbeats
import Lean.Elab.Command

namespace Measurement
namespace Calibration
namespace EKG

open Lean

/-- Run `probe` under a fresh local heartbeat origin and a LOCAL heartbeat
budget of `budget` user-heartbeats (`budget * 1000` internal). If the probe
outgrows that budget or raises any runtime exception (heartbeat / maxRecDepth /
stack), the EKG records the outgrowth and returns `none`; the caller falls back
and the module keeps building. Ordinary (non-runtime, semantic) errors are
rethrown. For probes that mutate metavariable / elaborator state, the call site
should wrap the probe with `withoutModifyingState` / `commitWhenSome?`. -/
def tryBounded? {α : Type} (budget : Nat) (label : String)
    (probe : CoreM α) : CoreM (Option α) :=
  withCurrHeartbeats do
    tryCatchRuntimeEx
      (do
        let a ← withTheReader Core.Context
          (fun ctx => { ctx with maxHeartbeats := budget * 1000 }) probe
        return some a)
      (fun ex => do
        if ex.isRuntime then
          logInfo m!"EKG outgrown at {label}: bounded elaboration exceeded {budget} user-heartbeats; returning fallback"
          return none
        else
          throw ex)

end EKG
end Calibration
end Measurement

/-
`ekg_probe N => term` MEASURES THE EVALUATION OF A PROPOSITION, and that is all.
It elaborates `term` under a local EKG heartbeat budget of `N` user-heartbeats
and reports whether the evaluation finished within bound. It binds NO top-level
declaration, so a universe-incomplete probe term cannot leak into a required
signature (the "contains universe level metavariables" check fires only when a
declaration is added). It NEVER fails the module: on runtime outgrowth it logs
the EKG event and continues. The real elaboration happens INSIDE the budget.
-/
open Lean Lean.Elab Lean.Elab.Command Lean.Elab.Term in
elab "ekg_probe" n:num "=>" t:term : command => do
  let budget := n.getNat
  liftTermElabM do
    withCurrHeartbeats do
      tryCatchRuntimeEx
        (withTheReader Core.Context (fun ctx => { ctx with maxHeartbeats := budget * 1000 }) do
          -- CAPTURE the elaboration heartbeat count -- the EKG reading -- bounded by
          -- the budget. Model: Episode32 `register_timed_probe` (`Lean.withHeartbeats`).
          -- We do NOT `whnf`/force the term: a term over the heavy `noncomputable`
          -- truth instances is cheap to ELABORATE (projecting a built constant) but
          -- ruinous to EVALUATE, so capturing the elaboration cost is the correct,
          -- bounded signal; the local `maxHeartbeats` is the circuit-breaker only.
          let (_, hb) ← Lean.withHeartbeats do
            let _ ← Term.elabTerm t none
            pure ()
          logInfo m!"EKG probe within budget ({budget} user-heartbeats): elaboration consumed {hb} internal heartbeats")
        (fun ex => do
          if ex.isRuntime then
            logInfo m!"EKG outgrown ({budget} user-heartbeats): elaboration exceeded budget -- diagnostic only"
          else
            throw ex)
