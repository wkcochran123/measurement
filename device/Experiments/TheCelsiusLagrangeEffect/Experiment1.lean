import Experiments.Common

/-!
# The Celsius–Lagrange Effect — a finite-anchor interpolation shadow

Source: `instrument/chapters/02.tex:1758`, `phenom`, label `ph:interpolation`.

The phenomenon: discrete reference points (Celsius' freezing/boiling of water) are embedded
in a continuous representational scheme to support *interpolation*, without asserting that the
underlying phenomenon is continuous. The scale is **arbitrary in its symbols but stable in its
relations**. The governing *Constraint* (description.md): "Interpolation must be **recoverable**
from the chosen reference points. No intermediate value may be treated as factual unless it can
be reconstructed from the finite data that define the scale."

This file models that finitely and falsifiably:

* the domain is an effect-specific `Scale` (two anchors: a low/high reading paired with a
  low/high degree), NOT `Experiments.Common.CountSetup`;
* the interpolant `interp` is integer linear interpolation between the two anchors;
* a **falsifiable** ∀-lemma (`interp_recovers_anchor`) pins the Constraint: AT an anchor the
  interpolant reproduces the anchor's recorded degree exactly — drop the "at an anchor"
  hypothesis and it is false (the `#eval` at the bottom witnesses a non-anchor point where the
  interpolated degree ≠ the low anchor degree);
* the **recoverability** half of the claim is discharged through the harness'
  `Experiments.Common.Projection.sameShadow`: the smooth curve and the discrete anchor record
  cast the *same shadow* at an anchor (the projection = "read the degree at this reading"). That
  is the smooth-shadow content, load-bearing in `claim_holds`.

## NOT claimed
That temperature is *actually* continuous; that any real thermometer interpolates linearly
(Lagrange interpolation of >2 anchors is generally a higher-degree polynomial — not modelled);
that the chosen symbols (0, 100) are anything but convention; any physics of heat. The model
asserts only: a finite anchor set determines an interpolation rule that **reconstructs its own
anchors**, and the off-anchor values are representational scaffolding, never facts.
**Claim ceiling:** a finite stand-in (`smoothShadowAnalogy`) for a continuous scale.
-/

namespace Experiments.TheCelsiusLagrangeEffect

/-- A two-anchor scale: at reading `loRead` the recorded degree is `loDeg`; at `hiRead` it is
`hiDeg`. (Celsius: `loRead`/`hiRead` are the freezing/boiling readings, `loDeg=0`, `hiDeg=100`.)
Symbols are arbitrary; only the relation between the two anchors is fixed. -/
structure Scale where
  loRead : Int
  hiRead : Int
  loDeg : Int
  hiDeg : Int
deriving DecidableEq, Repr

/-- The canonical Celsius scale: freeze at raw reading 0 → 0°, boil at raw reading 1000 → 100°.
(The raw readings are an arbitrary instrument coordinate; the degrees are the convention.) -/
def celsius : Scale := { loRead := 0, hiRead := 1000, loDeg := 0, hiDeg := 100 }

namespace Scale

/-- Integer linear interpolation: the degree the smooth curve assigns to a raw reading `x`.
`loDeg + (hiDeg - loDeg) * (x - loRead) / (hiRead - loRead)`. This is the "continuity introduced
as a representational convenience" — a rule relating the symbols as if on a continuum. -/
def interp (s : Scale) (x : Int) : Int :=
  s.loDeg + (s.hiDeg - s.loDeg) * (x - s.loRead) / (s.hiRead - s.loRead)

/-- `x` is one of the two reference readings (an anchor). The Constraint privileges these:
only at anchors is a value guaranteed factual. -/
def isAnchor (s : Scale) (x : Int) : Prop :=
  x = s.loRead ∨ x = s.hiRead

/-- The recorded (factual) degree at an anchor reading. Undefined off-anchor (we return the low
degree as a placeholder — the model never treats that as a fact). -/
def recorded (s : Scale) (x : Int) : Int :=
  if x = s.hiRead then s.hiDeg else s.loDeg

instance (s : Scale) (x : Int) : Decidable (s.isAnchor x) := by
  unfold isAnchor; exact inferInstance

end Scale

-- ---------------------------------------------------------------------------
-- FALSIFIABLE lemma: the Constraint. At an anchor the interpolant reproduces the recorded
-- degree. The "at an anchor" hypothesis is load-bearing — see the `#eval` at the bottom, which
-- evaluates the predicate at a NON-anchor reading and prints `false`.
-- ---------------------------------------------------------------------------

/-- The interpolant reconstructs the recorded degree **at every anchor**, for the canonical
scale. (Quantified over `x`; the hypothesis `isAnchor` is necessary and is dropped at the
falsifying `#eval`.) -/
theorem interp_recovers_anchor (x : Int) (h : celsius.isAnchor x) :
    celsius.interp x = celsius.recorded x := by
  rcases h with h | h <;> subst h <;> rfl

/-- A relations-not-symbols witness: the *interval* between the two anchors is what the scale
fixes. The full span maps to exactly `hiDeg - loDeg = 100` degrees. -/
theorem span_is_one_hundred :
    celsius.interp celsius.hiRead - celsius.interp celsius.loRead = 100 := by
  decide

-- ---------------------------------------------------------------------------
-- HARNESS COUPLING: recoverability as a SHADOW. The smooth curve (`interp`) and the discrete
-- anchor record (`recorded`) cast the SAME shadow at an anchor, where "shadow" = the degree read
-- at that reading. This is `Experiments.Common.Projection.sameShadow`, so a rename/regression in
-- the harness `Projection` breaks THIS build. (`smoothShadowAnalogy`, literally.)
-- ---------------------------------------------------------------------------

/-- The projection that reads the interpolated degree at a given reading. A pair `(scale, reading)`
projects to the curve's degree there. -/
def degreeShadow (x : Int) : Experiments.Common.Projection Scale Int :=
  { project := fun s => s.interp x }

/-- At the low anchor, the canonical scale and a scale whose *high* anchor has been moved cast the
SAME shadow (both still read `loDeg` at `loRead`): the off-anchor data is scaffolding and does not
change the anchor fact. Coupled through the harness `Projection.sameShadow`. -/
theorem anchor_shadow_agrees :
    Experiments.Common.Projection.sameShadow (degreeShadow celsius.loRead)
      celsius { celsius with hiRead := 2000 } := by
  unfold Experiments.Common.Projection.sameShadow degreeShadow Scale.interp
  decide

-- ---------------------------------------------------------------------------
-- THE CLAIM (content-bearing conjunction):
--   (recovery)  the interpolant reconstructs the recorded degree at the high anchor;
--   (relations) the anchor-to-anchor span is exactly 100 degrees; and
--   (shadow)    moving the off-anchor data leaves the low-anchor shadow invariant
--               (`Projection.sameShadow`, the harness coupling).
-- ---------------------------------------------------------------------------

def claimStatement : Prop :=
  celsius.interp celsius.hiRead = celsius.recorded celsius.hiRead ∧
    (celsius.interp celsius.hiRead - celsius.interp celsius.loRead = 100) ∧
    Experiments.Common.Projection.sameShadow (degreeShadow celsius.loRead)
      celsius { celsius with hiRead := 2000 }

def claim : Experiments.Common.Claim :=
  { tag := Experiments.Common.ClaimTag.smoothShadowAnalogy
    statement := claimStatement }

theorem claim_holds : claim.statement :=
  ⟨interp_recovers_anchor celsius.hiRead (Or.inr rfl),
    span_is_one_hundred,
    anchor_shadow_agrees⟩

theorem ceiling :
    claim.tag = Experiments.Common.ClaimTag.smoothShadowAnalogy := rfl

-- ---------------------------------------------------------------------------
-- A computable run + a non-vacuous exported experiment, with a proved bridge.
-- ---------------------------------------------------------------------------

structure Setup where
  scale : Scale
  reading : Int

/-- The run computes whether the chosen reading is an anchor (only there is the value factual). -/
def run (s : Setup) : Bool := decide (s.scale.isAnchor s.reading)

def experiment : Experiments.Common.Experiment Setup Bool :=
  { tag := claim.tag
    run := run
    claim := fun s => s.scale.isAnchor s.reading }

theorem run_iff_claim (s : Setup) :
    run s = true ↔ experiment.claim s := by
  simp only [run, experiment, decide_eq_true_iff]

def anchorSetup : Setup := { scale := celsius, reading := celsius.hiRead }

#eval run anchorSetup                                           -- expect: true  (an anchor)
#eval run { anchorSetup with reading := 500 }                   -- expect: false (off-anchor)
-- The falsifiable lemma is LOAD-BEARING: at a NON-anchor reading the interpolant disagrees with
-- the low-anchor record, so the unhypothesized version would be FALSE:
#eval decide (celsius.interp 500 = celsius.recorded 500)        -- expect: false
#print axioms claim_holds                                       -- ambient [propext, Quot.sound]

/-- Bring a minimal device next to this experiment: it records whether the exported claim fires. -/
def deviceNear (setup : Setup) : Bool :=
  decide (setup.scale.isAnchor setup.reading)

theorem deviceNear_detects_claim (setup : Setup) :
    deviceNear setup = true ↔ experiment.claim setup := by
  simp only [deviceNear, experiment, decide_eq_true_iff]

def triangulation : Experiments.Common.Triangulation Setup Bool :=
  { experiment := experiment
    device := deviceNear
    detects := deviceNear_detects_claim }

end Experiments.TheCelsiusLagrangeEffect
