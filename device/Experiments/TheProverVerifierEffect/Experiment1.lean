import Experiments.Common
import Measurement.AffineConstant

/-!
# The Prover–Verifier Effect — the device is a verifier, not a prover

The informational theory is not complete in isolation: it requires the world of admissible models
as its PROVER, and serves only as their VERIFIER. It takes a claimed value and checks it, returning
whether the residual falls below its own count-3 resolution floor — it never derives the value.

That is exactly the device's own `Measurement.AffineConstant.verify (claimed) → {verified, residual}`:
a claim that matches the read (residual 0) is verified; a claim one tick past the floor is rejected.
The device symbols sit inside `claim_holds`, so a regression in `verify` / `count3Floor` /
`affineInvAlpha` breaks THIS build. That is the coupling (it replaces the old generic `CountSetup`).

Claim ceiling (unchanged): `finiteLedgerModel`.
-/

namespace Experiments.TheProverVerifierEffect

open Measurement.AffineConstant

/-- The reading distance the prover's claim is checked against (the math register's own reading). -/
def checkDist := mathReg.reading

/-- The device's read at that distance (the verifier's own figure). -/
def readValue : Nat := affineInvAlpha checkDist

/-- The prover proposes a claimed value; `Setup` carries it. -/
structure Setup where
  claimed : Nat
deriving DecidableEq, Repr

def defaultSetup : Setup := { claimed := readValue }

/-- The verifier's verdict on a proposed claim. -/
def verdict (s : Setup) : VerifyResult := verify "prover" s.claimed checkDist

/-- Exported per-setup predicate: the verifier ACCEPTS the prover's claim. -/
def accepted (s : Setup) : Prop := (verdict s).verified = true

instance (s : Setup) : Decidable (accepted s) := by
  unfold accepted; infer_instance

/-- Content claim: the verifier ACCEPTS the matching claim (residual within the floor) and REJECTS
one a tick past the floor. Both read the device's `verify` / `count3Floor` / `affineInvAlpha`. -/
def claimStatement : Prop :=
  (verify "prover" readValue checkDist).verified = true
    ∧ (verify "prover" (readValue + count3Floor + 1) checkDist).verified = false

def claim : Experiments.Common.Claim :=
  { tag := Experiments.Common.ClaimTag.finiteLedgerModel
    statement := claimStatement }

theorem claim_holds : claim.statement := by
  refine ⟨?_, ?_⟩ <;> native_decide

theorem ceiling :
    claim.tag = Experiments.Common.ClaimTag.finiteLedgerModel := rfl

def run (s : Setup) : Bool := decide (accepted s)

def experiment : Experiments.Common.Experiment Setup Bool :=
  { tag := claim.tag
    run := run
    claim := fun s => accepted s }

theorem run_iff_claim (s : Setup) :
    run s = true ↔ experiment.claim s := by
  show decide (accepted s) = true ↔ accepted s
  exact decide_eq_true_iff

/-- Bring a minimal device next to this experiment: it records whether the exported claim fires. -/
def deviceNear (setup : Setup) : Bool :=
  decide (accepted setup)

theorem deviceNear_detects_claim (setup : Setup) :
    deviceNear setup = true ↔ experiment.claim setup := by
  show decide (accepted setup) = true ↔ accepted setup
  exact decide_eq_true_iff

def triangulation : Experiments.Common.Triangulation Setup Bool :=
  { experiment := experiment
    device := deviceNear
    detects := deviceNear_detects_claim }

#eval s!"prover claims {readValue} (= the read) -> verified? {(verdict defaultSetup).verified}  residual {(verdict defaultSetup).residual}"
#eval s!"prover claims read+floor+1 -> verified? {(verdict { claimed := readValue + count3Floor + 1 }).verified}  (rejected past the count-3 floor)"

end Experiments.TheProverVerifierEffect
