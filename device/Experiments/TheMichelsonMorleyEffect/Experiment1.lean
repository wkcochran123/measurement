import Experiments.Common
import Measurement.Apparatus

/-!
# The Michelson–Morley Effect — the null result as frame-relative detection

Read as a purely informational NULL RESULT: the same loop, read in two frames (the two
interferometer arms / two frame choices), returns holonomy signs that are NEGATIVES of each
other — so no absolute frame is singled out. The frame-dependent part (the "ether-wind" sign)
is a pure relativity artifact; what survives is the frame-independent structure, not the route.

That the two frames read opposite signs is the device's own theorem
`Measurement.detection_is_frame_relative`; a sign / rename / `sorry` regression there breaks
THIS build — the device symbol sits inside `claim_holds`. That is the coupling (it replaces the
old generic `CountSetup` harness).

Claim ceiling (unchanged): `finiteLedgerModel` — a finite shadow of the no-preferred-frame
null, whose content is the device's frame-relativity theorem.
-/

namespace Experiments.TheMichelsonMorleyEffect

/-- The charged loop the two arms trace (node1 → node2). -/
def loopPair : Measurement.CubicGaugeVariation0 :=
  Measurement.CubicGaugeVariation.pairVariation Measurement.node1 Measurement.node2

/-- An arm choice: `charged = true` traces the charged loop; `false` the trivial reverse pair. -/
structure Setup where
  charged : Bool
deriving DecidableEq, Repr

def defaultSetup : Setup := { charged := true }

def armPair (s : Setup) : Measurement.CubicGaugeVariation0 :=
  if s.charged then loopPair
  else Measurement.CubicGaugeVariation.pairVariation Measurement.node2 Measurement.node1

/-- The two frame-readings of the arm's holonomy (the "ether-wind" sign in each frame). -/
def flatReading  (s : Setup) : Int := Measurement.holonomy Measurement.flatPath  (armPair s)
def tiltedReading (s : Setup) : Int := Measurement.holonomy Measurement.tiltedPath (armPair s)

/-- The exported per-setup predicate: the two frames read OPPOSITE signs — frame-relative
detection, no absolute frame. -/
def framesRelative (s : Setup) : Prop := flatReading s = - tiltedReading s

instance (s : Setup) : Decidable (framesRelative s) := by
  unfold framesRelative flatReading tiltedReading; infer_instance

/-- Content claim: on the charged loop, the same holonomy reads opposite signs in the two frames.
This is exactly `Measurement.detection_is_frame_relative`, so the device symbol is load-bearing. -/
def claimStatement : Prop :=
  Measurement.holonomy Measurement.flatPath loopPair
    = - Measurement.holonomy Measurement.tiltedPath loopPair

def claim : Experiments.Common.Claim :=
  { tag := Experiments.Common.ClaimTag.finiteLedgerModel
    statement := claimStatement }

theorem claim_holds : claim.statement := Measurement.detection_is_frame_relative

theorem ceiling :
    claim.tag = Experiments.Common.ClaimTag.finiteLedgerModel := rfl

def run (s : Setup) : Bool := decide (framesRelative s)

def experiment : Experiments.Common.Experiment Setup Bool :=
  { tag := claim.tag
    run := run
    claim := fun s => framesRelative s }

theorem run_iff_claim (s : Setup) :
    run s = true ↔ experiment.claim s := by
  show decide (framesRelative s) = true ↔ framesRelative s
  exact decide_eq_true_iff

/-- Bring a minimal device next to this experiment: it records whether the exported claim fires. -/
def deviceNear (setup : Setup) : Bool :=
  decide (framesRelative setup)

theorem deviceNear_detects_claim (setup : Setup) :
    deviceNear setup = true ↔ experiment.claim setup := by
  show decide (framesRelative setup) = true ↔ framesRelative setup
  exact decide_eq_true_iff

def triangulation : Experiments.Common.Triangulation Setup Bool :=
  { experiment := experiment
    device := deviceNear
    detects := deviceNear_detects_claim }

#eval s!"flat-frame reading = {flatReading defaultSetup}   tilted-frame reading = {tiltedReading defaultSetup}  (opposite signs: no absolute frame)"
#eval s!"framesRelative (charged loop)? {decide (framesRelative defaultSetup)}   coupling = Measurement.detection_is_frame_relative"

end Experiments.TheMichelsonMorleyEffect
