import Experiments.Common
import Measurement.FinitenessFence

/-!
# The Wittgenstein Effect — whereof one cannot speak, thereof one must be silent

The machine names through a finite box-resolution (`boxCount = 2`). With more distinctions to name
than boxes, some must share a box — and what shares a box the machine cannot separate or name. The
residue between the first variation and the second falls below that resolution: for ANY reading the
machine computes off its boxes, the two read the SAME. That residue is what the machine must pass
over in silence — the limit of its language.

Both halves are the device's own theorems — `Measurement.boxCount_is_two` and
`Measurement.FinitenessFence.machine_cannot_resolve_residue`; a rename / sign / `sorry` regression in
either breaks THIS build. That is the coupling (it replaces the old generic `CountSetup`).

Claim ceiling (unchanged): `finiteLedgerModel`.
-/

namespace Experiments.TheWittgensteinEffect

/-- A naming attempt: how many distinctions the machine tries to name. -/
structure Setup where
  names : Nat
deriving DecidableEq, Repr

/-- The default attempt names more distinctions (3) than the box-resolution (2) holds. -/
def defaultSetup : Setup := { names := 3 }

/-- Exported per-setup predicate: the attempt names MORE distinctions than the finite box-resolution,
so two must share a box — a residue the machine cannot separate or name. -/
def outrunsResolution (s : Setup) : Prop := s.names > Measurement.boxCount

instance (s : Setup) : Decidable (outrunsResolution s) := by
  unfold outrunsResolution; infer_instance

/-- Content claim: the box-resolution is exactly 2, and for ANY reading the machine computes off its
boxes, the first variation and the second read the SAME — the residue between them is un-nameable
("whereof one cannot speak, thereof one must be silent"). Both are the device's own theorems. -/
def claimStatement : Prop :=
  Measurement.boxCount = 2
    ∧ ∀ {M : Type} (read : Fin Measurement.boxCount → M)
        (g : Measurement.Gospel) (a b c : Prop) (v1 v2 tail : Measurement.Variation),
        read (Measurement.boxOf (Measurement.Variation.gateaux g a b tail))
          = read (Measurement.boxOf (Measurement.Variation.frechet g a b c v1 v2))

def claim : Experiments.Common.Claim :=
  { tag := Experiments.Common.ClaimTag.finiteLedgerModel
    statement := claimStatement }

theorem claim_holds : claim.statement := by
  refine ⟨Measurement.boxCount_is_two, ?_⟩
  intro M read g a b c v1 v2 tail
  exact Measurement.FinitenessFence.machine_cannot_resolve_residue read g a b c v1 v2 tail

theorem ceiling :
    claim.tag = Experiments.Common.ClaimTag.finiteLedgerModel := rfl

def run (s : Setup) : Bool := decide (outrunsResolution s)

def experiment : Experiments.Common.Experiment Setup Bool :=
  { tag := claim.tag
    run := run
    claim := fun s => outrunsResolution s }

theorem run_iff_claim (s : Setup) :
    run s = true ↔ experiment.claim s := by
  show decide (outrunsResolution s) = true ↔ outrunsResolution s
  exact decide_eq_true_iff

/-- Bring a minimal device next to this experiment: it records whether the exported claim fires. -/
def deviceNear (setup : Setup) : Bool :=
  decide (outrunsResolution setup)

theorem deviceNear_detects_claim (setup : Setup) :
    deviceNear setup = true ↔ experiment.claim setup := by
  show decide (outrunsResolution setup) = true ↔ outrunsResolution setup
  exact decide_eq_true_iff

def triangulation : Experiments.Common.Triangulation Setup Bool :=
  { experiment := experiment
    device := deviceNear
    detects := deviceNear_detects_claim }

#eval s!"box-resolution boxCount = {Measurement.boxCount}  (finite: the limits of the machine's language)"
#eval s!"naming {defaultSetup.names} distinctions outruns {Measurement.boxCount} boxes? {decide (outrunsResolution defaultSetup)}  -> two collide; the residue between them is un-nameable"

end Experiments.TheWittgensteinEffect
