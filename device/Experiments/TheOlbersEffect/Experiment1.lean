import Experiments.Common
import Measurement.NamingClose

/-!
# The Olbers Effect — a finite ledger bounds its luminous events

An endlessly refined ledger would admit endlessly many distinguishable luminous events, and the
night would blaze in every direction. The device's ledger is NOT endless: its box-resolution is
finite (`boxCount = 2`), so the distinguishable events it can record are bounded, however finely the
sky is refined. The dark sky is the finiteness of the record, read from inside.

⚠ FENCE (electron-scope + no-name-bridge): Olbers's paradox is COSMOLOGICAL. This couples ONLY the
device's own FINITENESS FACT (`Measurement.boxCount_is_two` — the electron-model's ledger is finite),
as a structural LENS on Olbers's finite-record; it makes NO claim that the device's electron-mesh IS
the universe. The resemblance is the finiteness shape, not a shared object; the cosmological reach is
DECLINED. What is coupled is the device finiteness fact (a regression in `boxCount` breaks this build);
the "bounded events" step is a local harness model, not a device theorem.

Claim ceiling (unchanged): `finiteLedgerModel`.
-/

namespace Experiments.TheOlbersEffect

/-- A refinement attempt: how finely the mesh of the sky is refined. -/
structure Setup where
  refinements : Nat
deriving DecidableEq, Repr

def defaultSetup : Setup := { refinements := 100 }

/-- The distinguishable luminous events a FINITE ledger can record: at most `boxCount`, however finely
the sky is refined. (A finite mesh cannot hold infinitely many distinct events.) -/
def luminousEvents (s : Setup) : Nat := min s.refinements Measurement.boxCount

/-- Exported per-setup predicate: the events are BOUNDED by the finite box-resolution — the sky
cannot blaze without end. -/
def eventsBounded (s : Setup) : Prop := luminousEvents s ≤ Measurement.boxCount

instance (s : Setup) : Decidable (eventsBounded s) := by
  unfold eventsBounded luminousEvents; infer_instance

/-- Content claim: the ledger's resolution is finite (`boxCount = 2`) — the device's own theorem —
and so the luminous events it records are bounded, however finely the sky is refined. The dark sky is
the record's finiteness. -/
def claimStatement : Prop :=
  Measurement.boxCount = 2 ∧ ∀ s : Setup, luminousEvents s ≤ Measurement.boxCount

def claim : Experiments.Common.Claim :=
  { tag := Experiments.Common.ClaimTag.finiteLedgerModel
    statement := claimStatement }

theorem claim_holds : claim.statement := by
  refine ⟨Measurement.boxCount_is_two, ?_⟩
  intro s
  unfold luminousEvents
  exact Nat.min_le_right _ _

theorem ceiling :
    claim.tag = Experiments.Common.ClaimTag.finiteLedgerModel := rfl

def run (s : Setup) : Bool := decide (eventsBounded s)

def experiment : Experiments.Common.Experiment Setup Bool :=
  { tag := claim.tag
    run := run
    claim := fun s => eventsBounded s }

theorem run_iff_claim (s : Setup) :
    run s = true ↔ experiment.claim s := by
  show decide (eventsBounded s) = true ↔ eventsBounded s
  exact decide_eq_true_iff

/-- Bring a minimal device next to this experiment: it records whether the exported claim fires. -/
def deviceNear (setup : Setup) : Bool :=
  decide (eventsBounded setup)

theorem deviceNear_detects_claim (setup : Setup) :
    deviceNear setup = true ↔ experiment.claim setup := by
  show decide (eventsBounded setup) = true ↔ eventsBounded setup
  exact decide_eq_true_iff

def triangulation : Experiments.Common.Triangulation Setup Bool :=
  { experiment := experiment
    device := deviceNear
    detects := deviceNear_detects_claim }

#eval s!"box-resolution (finite ledger) = {Measurement.boxCount}"
#eval s!"refine the sky {defaultSetup.refinements}x -> distinguishable luminous events = {luminousEvents defaultSetup} (bounded by the finite mesh; the sky stays dark)"

end Experiments.TheOlbersEffect
