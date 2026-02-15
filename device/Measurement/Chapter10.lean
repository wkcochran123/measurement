import Measurement.Chapter9

namespace Measurement

namespace Ledger

def ulift {X : Type u} (L : Ledger X) : Ledger (ULift X) :=
{ head := ULift.up L.head
  tail := Enumeration.map ULift.up L.tail }

end Ledger

namespace Decomposition

def uliftRight {α : Type u} {β : Type v} (D : Decomposition α β) :
    Decomposition α (ULift β) :=
{ pairs := Enumeration.map (fun p : (α × β) => (p.1, ULift.up p.2)) D.pairs }

def uliftLeft {α : Type u} {β : Type v} (D : Decomposition α β) :
    Decomposition (ULift α) β :=
{ pairs := Enumeration.map (fun p : (α × β) => (ULift.up p.1, p.2)) D.pairs }

end Decomposition

namespace Instrument

/-- Lift the instrument's *state/ledger* universe. -/
def uliftState {S : Type u} {σ : Type v} (I : Instrument S σ) :
    Instrument (ULift S) σ :=
{ alphabet := I.alphabet
  ledger   := Ledger.ulift I.ledger }

end Instrument

namespace Device

/-- Lift a device along the ledger/state side (the `σ` of `Instrument σ τ`). -/
def uliftState {σ : Type u} {τ : Type v} (D : Device σ τ) :
    Device (ULift σ) τ :=
{ instrument     := Instrument.uliftState D.instrument
  decomposition  := Decomposition.uliftRight D.decomposition }

/-- Promote, but first lift the ledger/state universe. -/
def getCarrierUliftState {σ : Type u} {τ : Type v} (D : Device σ τ) :
    Carrier (ULift σ) τ :=
  (D.uliftState).getCarrier

end Device



universe u v

structure Gauge (σ : Type u) (τ : Type (u+1)) where
  state : Surface σ τ
  sequence : Commutator σ τ

structure Frame (σ : Type u) (τ : Type (u+1)) where
  measurement: Observer σ τ
  units: Surface σ τ


-- Strictly positive reals
abbrev Rpos : Type := { r : Real // 0 < r }

structure PhysicalLaw (σ : Type u) (τ : Type (u+1)) where
  finiteGauge: Ledger (Gauge σ τ)
  observer: Frame σ τ

namespace PhysicalLaw

noncomputable def f
  {σ : Type u} {τ : Type (u+1)}
  [DecidableEq σ] [DecidableEq τ]
  (PL : PhysicalLaw σ τ) (s : ℝ) : Option τ :=
  (PL.observer.measurement.experiment.getInstrument.getDevice.getCarrier).recv? (Event σ).value (s)

end PhysicalLaw
/--
f(t) = t (!)
f:Rpos -> R
-/
abbrev TrivialPhysicalLaw := PhysicalLaw ℚ (ULift ℚ)

end Measurement
