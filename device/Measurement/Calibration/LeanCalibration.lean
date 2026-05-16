import Measurement.ComputerProgram
import Lean.Util.Heartbeats

namespace Measurement
namespace Calibration

/-!
Calibration lives outside the instrument.  The raw Lean heartbeat counter is
only the reference substrate; the public surface is the ephemeral proposition
that one reading is embigger than another.
-/

private structure Reading where
  heartbeats : Nat

private def observeHeartbeats {α : Type} {m : Type → Type}
    [Monad m] [MonadLiftT BaseIO m] (x : m α) : m Reading := do
  let (_, heartbeats) ← Lean.withHeartbeats x
  pure { heartbeats }

private def Reading.embigger? (before after : Reading) : Prop :=
  before.heartbeats <= after.heartbeats

private def Reading.next (reading : Reading) : Reading :=
  { heartbeats := reading.heartbeats + 1 }

private def Reading.outgrows? (reading reference : Reading) : Prop :=
  reference.heartbeats < reading.heartbeats

private def loadConstructor : Reading :=
  { heartbeats := 1 }

private def booleanConstructor : Reading :=
  loadConstructor.next.next

private def explicitElaboration : ComputerProgram → Reading
  | .load _ _ _ => loadConstructor
  | .transform _ _ _ _ _ _ program => (explicitElaboration program).next
  | .boolean _ _ _ _ _ _ _ _ _ program => (explicitElaboration program).next

private def programName? : ComputerProgram → Prop
  | .load _ p _ => p
  | .transform _ _ p1 p2 _ _ program => p1 ∧ p2 ∧ programName? program
  | .boolean _ _ _ p1 p2 p3 _ _ _ program => p1 ∧ p2 ∧ p3 ∧ programName? program

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
  | .transform _ _ _ _ _ _ _, .boolean _ _ _ _ _ _ _ _ _ _ =>
    ¬ ((explicitElaboration before).outgrows? ekg.reference)
  | _, _ => False

private def covariantBooleanTransform? (_ekg : EKG) (before after : ComputerProgram) : Prop :=
  match before, after with
  | .boolean _ _ _ _ _ _ _ _ _ _, .transform _ _ _ _ _ _ _ => False
  | _, _ => False

def booleanTransform? (ekg : EKG) (before after : ComputerProgram) : Prop :=
  match before, after with
  | .boolean _ _ _ _ _ _ _ _ _ _, .transform _ _ _ _ _ _ _ =>
    ¬ (covariantBooleanTransform? ekg before after) ∧
    ¬ (ekg.transformBoolean? after before)
  | _, _ => False

end EKG

end Calibration
end Measurement
