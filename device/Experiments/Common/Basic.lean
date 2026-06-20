namespace Experiments.Common

universe u v w

/-- The ceiling on what an experiment file is allowed to claim. -/
inductive ClaimTag where
  | finiteLedgerModel
  | smoothShadowAnalogy
  | standardMathlibTheorem
  | physicalClaimLabelOnly
  | inadmissibilityNoGo
deriving DecidableEq, Repr

/-- A tagged proposition: the proposition is the Lean artifact, the tag is its claim ceiling. -/
structure Claim where
  tag : ClaimTag
  statement : Prop

/-- A finite ledger of recorded events. -/
structure Ledger (Event : Type u) where
  events : List Event
deriving Repr

namespace Ledger

variable {Event : Type u}

def count (ledger : Ledger Event) : Nat :=
  ledger.events.length

def empty : Ledger Event :=
  { events := [] }

def append (left right : Ledger Event) : Ledger Event :=
  { events := left.events ++ right.events }

def map {Other : Type v} (decode : Event -> Other) (ledger : Ledger Event) : Ledger Other :=
  { events := ledger.events.map decode }

theorem count_empty : (empty : Ledger Event).count = 0 := by
  rfl

theorem count_append (left right : Ledger Event) :
    (append left right).count = left.count + right.count := by
  simp [append, count]

theorem count_map {Other : Type v} (decode : Event -> Other) (ledger : Ledger Event) :
    (map decode ledger).count = ledger.count := by
  simp [map, count]

end Ledger

/-- A relation used when an experiment needs only causal order, not geometry. -/
structure CausalOrder (Event : Type u) where
  precedes : Event -> Event -> Prop

/-- A refinement decodes fine events into coarse events. -/
structure Refinement (Coarse : Type u) (Fine : Type v) where
  decode : Fine -> Coarse

namespace Refinement

def pushLedger {Coarse : Type u} {Fine : Type v}
    (refinement : Refinement Coarse Fine) (ledger : Ledger Fine) : Ledger Coarse :=
  ledger.map refinement.decode

end Refinement

/-- A channel has the two maps needed to discuss encoded and decoded records. -/
structure Channel (Input : Type u) (Output : Type v) where
  encode : Input -> Output
  decode : Output -> Input

/-- A boundary is whatever part of a state remains visible to a neighboring ledger. -/
structure Boundary (State : Type u) (BoundaryState : Type v) where
  restrict : State -> BoundaryState

namespace Boundary

def compatible {State : Type u} {BoundaryState : Type v}
    [DecidableEq BoundaryState] (boundary : Boundary State BoundaryState)
    (left right : State) : Prop :=
  boundary.restrict left = boundary.restrict right

end Boundary

/-- A projection records the shadow of a state seen by a restricted test family. -/
structure Projection (State : Type u) (Shadow : Type v) where
  project : State -> Shadow

namespace Projection

def sameShadow {State : Type u} {Shadow : Type v}
    (projection : Projection State Shadow) (left right : State) : Prop :=
  projection.project left = projection.project right

end Projection

/-- A holonomy witness records transport around a loop and the resulting residue. -/
structure Holonomy (State : Type u) (Loop : Type v) (Residue : Type w) where
  transportAround : State -> Loop -> State
  residue : State -> Loop -> Residue

namespace Counting

def boundedBy {Event : Type u} (ledger : Ledger Event) (bound : Nat) : Prop :=
  ledger.count <= bound

theorem boundedBy_self {Event : Type u} (ledger : Ledger Event) :
    boundedBy ledger ledger.count := by
  exact Nat.le_refl ledger.count

theorem boundedBy_of_eq {Event : Type u} {ledger : Ledger Event} {bound : Nat}
    (h : ledger.count = bound) : boundedBy ledger bound := by
  simp [boundedBy, h]

end Counting

/-- The small finite pattern used by first-pass experiment simulations. -/
inductive ModelKind where
  | preserves
  | blocks
  | projects
  | transports
  | labelsOnly
deriving DecidableEq, Repr

namespace ClaimTag

def allowsModelKind : ClaimTag -> ModelKind -> Bool
  | finiteLedgerModel, ModelKind.preserves => true
  | finiteLedgerModel, ModelKind.projects => true
  | finiteLedgerModel, ModelKind.transports => true
  | smoothShadowAnalogy, ModelKind.projects => true
  | smoothShadowAnalogy, ModelKind.transports => true
  | standardMathlibTheorem, ModelKind.preserves => true
  | physicalClaimLabelOnly, ModelKind.labelsOnly => true
  | inadmissibilityNoGo, ModelKind.blocks => true
  | _, _ => false

end ClaimTag

/--
A dimensionless count setup. The names are deliberately generic: individual
experiments explain in comments what each count represents.
-/
structure CountSetup where
  recorded : Nat
  accessible : Nat
  required : Nat
deriving Repr

structure CountOutput where
  recorded : Nat
  accessible : Nat
  required : Nat
  slack : Nat
deriving Repr

def runCount (setup : CountSetup) : CountOutput :=
  { recorded := setup.recorded
    accessible := setup.accessible
    required := setup.required
    slack := setup.accessible - setup.required }

namespace ModelKind

def holds : ModelKind -> CountOutput -> Prop
  | preserves, output => output.required <= output.accessible
  | blocks, output => output.accessible < output.required
  | projects, output => output.recorded <= output.accessible
  | transports, output => output.required <= output.recorded + output.accessible
  | labelsOnly, _ => True

end ModelKind

/-- The common shape for executable experiments. -/
structure Experiment (Setup : Type u) (Output : Type v) where
  tag : ClaimTag
  run : Setup -> Output
  claim : Setup -> Prop

/--
A local triangulation brings a boolean device/probe next to an experiment and
records exactly what the device detects.  The device is intentionally allowed
to be smaller than the experiment output: it only has to detect the exported
claim for the setup under test.
-/
structure Triangulation (Setup : Type u) (Output : Type v) where
  experiment : Experiment Setup Output
  device : Setup -> Bool
  detects : forall setup, device setup = true ↔ experiment.claim setup

end Experiments.Common
