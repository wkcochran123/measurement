import Measurement.SupportingMeasurements.ComputerProgram
import Lean.Util.Heartbeats
import Lean.Elab.Command

namespace Measurement
namespace Calibration

/-!
Calibration lives outside the instrument.  The raw Lean heartbeat counter is
only the reference substrate; the public surface is the ephemeral proposition
that one reading is embigger than another.
-/

-- ------------------------------------------------------------
-- Noise floor: heartbeats consumed by forcing `Fact.Truth.decTruth`.
-- Probe and tolerance are the same act, by the de Broglie identity.
-- Result is in Lean's internal heartbeat units (× 1000 user-facing).
-- ------------------------------------------------------------

elab "register_noise_floor" : command => do
  let hb ← Lean.Elab.Command.liftTermElabM do
    let stx ← `(Fact.Truth.decTruth)
    let (_, hb) ← Lean.withHeartbeats do
      let e ← Lean.Elab.Term.elabTerm stx none
      let _ ← Lean.Meta.whnf e
      pure ()
    pure hb
  let measuredFloorId := Lean.mkIdent `measuredFloor
  let cmd ← `(def $measuredFloorId:ident : Nat := $(Lean.quote hb))
  Lean.Elab.Command.elabCommand cmd

register_noise_floor

-- ------------------------------------------------------------
-- Gauge map between the paper (Bullshit / Number) and the metal (EKG /
-- Lean heartbeats).  One paper work unit corresponds to 1000 internal
-- heartbeats; that is the same coefficient Lean uses between user-facing
-- `maxHeartbeats` and `Lean.withHeartbeats` (see `Lean.CoreM.getMaxHeartbeats`).
-- `busyBeaverBudget` is BB(4) -- the structural complexity bound the
-- calibration tolerates per EKG-reference unit.
-- ------------------------------------------------------------
private def heartbeatCoefficient : Nat := 1000
private def busyBeaverBudget : Nat := 4

private structure Reading where
  heartbeats : Nat

private def observeHeartbeats {α : Type} {m : Type → Type}
    [Monad m] [MonadLiftT BaseIO m] (x : m α) : m Reading := do
  let (_, heartbeats) ← Lean.withHeartbeats x
  pure { heartbeats }

private def Reading.embigger? (before after : Reading) : Prop :=
  before.heartbeats <= after.heartbeats

private def Reading.next (reading : Reading) : Reading :=
  { heartbeats := reading.heartbeats + heartbeatCoefficient }

private def Reading.outgrows? (reading reference : Reading) : Prop :=
  reference.heartbeats < reading.heartbeats

private def Reading.scale (reading : Reading) (n : Nat) : Reading :=
  { heartbeats := reading.heartbeats * n }

@[reducible]
private def Reading.outgrowsWithNoise? (reading reference : Reading) : Prop :=
  reference.heartbeats + measuredFloor < reading.heartbeats

private def loadConstructor : Reading :=
  { heartbeats := heartbeatCoefficient }

private def booleanConstructor : Reading :=
  loadConstructor.next.next

private def explicitElaboration : ComputerProgram → Reading
  | .load _ _ => loadConstructor
  | .transform _ _ _ _ program => (explicitElaboration program).next
  | .boolean _ _ _ _ _ _ program => (explicitElaboration program).next

private def programName? : ComputerProgram → Prop
  | .load p _ => p
  | .transform p1 p2 _ _ program => p1 ∧ p2 ∧ programName? program
  | .boolean p1 p2 p3 _ _ _ program => p1 ∧ p2 ∧ p3 ∧ programName? program

private def compareHeartbeats? {α β : Type} {m : Type → Type}
    [Monad m] [MonadLiftT BaseIO m] (before : m α) (after : m β) : m Prop := do
  let beforeReading ← observeHeartbeats before
  let afterReading ← observeHeartbeats after
  pure (beforeReading.embigger? afterReading)

structure EKG where
  private reference : Reading
  embigger? : Prop → Prop → Prop

namespace EKG

def raw : EKG where
  reference := booleanConstructor
  embigger? := fun before after => before → after

def executed : EKG where
  reference := loadConstructor
  embigger? := fun before after => before → after

def booleanLength? (ekg : EKG)
    (a1 a2 a3 b1 b2 b3 : Prop) : Prop :=
  ekg.embigger? a1 b1 ∧
  ekg.embigger? a2 b2 ∧
  ekg.embigger? a3 b3

def booleanProgram? (ekg : EKG) (before after : ComputerProgram) : Prop :=
  ekg.reference.embigger? (explicitElaboration before) ∧
  (explicitElaboration before).embigger? (explicitElaboration after) ∧
  ekg.embigger? (programName? before) (programName? after)

def transformBoolean? (ekg : EKG) (before after : ComputerProgram) : Prop :=
  match before, after with
  | .transform _ _ _ _ _, .boolean _ _ _ _ _ _ _ =>
    ¬ ((explicitElaboration before).outgrows? ekg.reference)
  | _, _ => False

private def covariantBooleanTransform? (_ekg : EKG) (before after : ComputerProgram) : Prop :=
  match before, after with
  | .boolean _ _ _ _ _ _ _, .transform _ _ _ _ _ => False
  | _, _ => False

def booleanTransform? (ekg : EKG) (before after : ComputerProgram) : Prop :=
  match before, after with
  | .boolean _ _ _ _ _ _ _, .transform _ _ _ _ _ =>
    ¬ (covariantBooleanTransform? ekg before after) ∧
    ¬ (ekg.transformBoolean? after before)
  | _, _ => False

-- ------------------------------------------------------------
-- outgrown? compares the structural reading of `program` (coefficient-
-- scaled) against `busyBeaverBudget * ekg.reference + measuredFloor`,
-- where `measuredFloor` is the calibrated noise-tolerance deadband.  This
-- is the device's principled best from inside its own locality.
--
-- The live counter reading via `Lean.withHeartbeats` cannot be lifted
-- into this pure function without making the whole carrier ladder
-- monadic, and even then the probe would consume the very heartbeats it
-- is trying to count -- probe and tolerance, the same act, per the
-- noise-floor comment above.  The live reading lives outside the device
-- by necessity, not by oversight.
-- ------------------------------------------------------------
def outgrown? (ekg : EKG) (program : ComputerProgram) : Bool :=
  decide <|
    (explicitElaboration program).outgrowsWithNoise?
      (ekg.reference.scale busyBeaverBudget)

end EKG

end Calibration
end Measurement
