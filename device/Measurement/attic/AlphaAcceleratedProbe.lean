import Measurement.Meanwhile22
import Measurement.Calibration.EKGBounded
import Lean.Util.Heartbeats
import Lean.Elab.Command

/-! # AlphaAcceleratedProbe — Phase 0c: the ACCELERATED-FRAME residual reading (blind)

Operator: **"the bounds for α is the residual of their difference, the constant-acceleration frame."** The residual
of `1 − 0.999…` closes to null in the INERTIAL frame (why i1/i2 read flat, α=0). This reads it in the
CONSTANT-ACCELERATION (Rindler) frame: the residual is the fold cost's **second difference** — which IS the strain
= `mass = 2nd difference = acceleration` (Meanwhile21) — referenced to the Unruh floor (`measuredFloor`, ∝ accel).
The bounds = the range this accelerated residual takes; Richardson-swept over levels (ρ≈½).

**Gibbs/Weyl acceptance test (operator):** the device is BLIND to Weyl (shape), and Gibbs is a shape artifact, so
a true Ricci reading is **Gibbs-free** — no ~9% overshoot. If the residual RINGS (a ~9% overshoot that only
narrows), that's the tell I've drifted into the invisible Weyl frame → REJECT. A clean reading is monotone/smooth.

**BLIND: target absent; refuse coincidences; CODATA never; read whatever comes.** -/

namespace Measurement.AlphaAcceleratedProbe
open Lean Measurement

elab "register_cost" name:ident " => " t:term : command => do
  let hb ← Lean.Elab.Command.liftTermElabM do
    let (_, hb) ← Lean.withHeartbeats do
      let e ← Lean.Elab.Term.elabTerm t none
      let _ ← Lean.Meta.whnf e
      pure ()
    pure hb
  let cmd ← `(def $name:ident : Nat := $(Lean.quote hb))
  Lean.Elab.Command.elabCommand cmd

-- THE FLOOR (the Unruh floor ∝ acceleration; the blank).
register_cost floor => (Fact.Truth.decTruth)

-- THE FOLD COST at increasing depth (warmup-discarded: measure twice, take the 2nd, post-warmup stable read).
-- The value being folded is a Number of depth k (the loop iterated); the residual of the fold = its 2nd difference.
private def bk (k : Nat) : Number := Nat.rec (.zero Fact.Truth) (fun _ ih => .one Fact.Truth ih) k
register_cost w0 => ((recover { lower := .zero Fact.Truth, upper := .zero Fact.Truth, value := bk 0 } Fact.Truth).phase)
register_cost f0 => ((recover { lower := .zero Fact.Truth, upper := .zero Fact.Truth, value := bk 0 } Fact.Truth).phase)
register_cost w1 => ((recover { lower := .zero Fact.Truth, upper := .zero Fact.Truth, value := bk 1 } Fact.Truth).phase)
register_cost f1 => ((recover { lower := .zero Fact.Truth, upper := .zero Fact.Truth, value := bk 1 } Fact.Truth).phase)
register_cost w2 => ((recover { lower := .zero Fact.Truth, upper := .zero Fact.Truth, value := bk 2 } Fact.Truth).phase)
register_cost f2 => ((recover { lower := .zero Fact.Truth, upper := .zero Fact.Truth, value := bk 2 } Fact.Truth).phase)
register_cost w3 => ((recover { lower := .zero Fact.Truth, upper := .zero Fact.Truth, value := bk 3 } Fact.Truth).phase)
register_cost f3 => ((recover { lower := .zero Fact.Truth, upper := .zero Fact.Truth, value := bk 3 } Fact.Truth).phase)
register_cost w4 => ((recover { lower := .zero Fact.Truth, upper := .zero Fact.Truth, value := bk 4 } Fact.Truth).phase)
register_cost f4 => ((recover { lower := .zero Fact.Truth, upper := .zero Fact.Truth, value := bk 4 } Fact.Truth).phase)
register_cost w5 => ((recover { lower := .zero Fact.Truth, upper := .zero Fact.Truth, value := bk 5 } Fact.Truth).phase)
register_cost f5 => ((recover { lower := .zero Fact.Truth, upper := .zero Fact.Truth, value := bk 5 } Fact.Truth).phase)

-- ── THE RAW RUN-LOG (full, in order) ──
#eval (floor, f0, f1, f2, f3, f4, f5)
-- δ¹ (the "velocity"):
def d1 (a b : Nat) : Int := (b:Int) - a
#eval (d1 f0 f1, d1 f1 f2, d1 f2 f3, d1 f3 f4, d1 f4 f5)
-- δ² = THE STRAIN = the residual in the ACCELERATED frame (mass = 2nd difference, Meanwhile21):
def strain2 : Int := d1 f1 f2 - d1 f0 f1
def strain3 : Int := d1 f2 f3 - d1 f1 f2
def strain4 : Int := d1 f3 f4 - d1 f2 f3
def strain5 : Int := d1 f4 f5 - d1 f3 f4
#eval (strain2, strain3, strain4, strain5)                       -- the accelerated residual (raw), per level
-- referenced to the Unruh floor (the dimensionless accelerated read, ppm):
#eval ((strain2*1000000)/(floor:Int), (strain3*1000000)/(floor:Int), (strain4*1000000)/(floor:Int), (strain5*1000000)/(floor:Int))
-- GIBBS TEST: does the accelerated residual RING (a persistent ~9% overshoot) or settle smoothly? report the
-- successive ratios — a ringing (alternating, ~const magnitude) = Weyl frame → reject; settling = clean Ricci.
#eval (strain3 - strain2, strain4 - strain3, strain5 - strain4)  -- third differences: settling → 0, ringing → alternating

end Measurement.AlphaAcceleratedProbe
